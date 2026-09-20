#!/usr/bin/env python3
"""
MK formed alert - cloud version (Python port of the TradingView / MT5 logic).

What it does on every run:
  1. downloads the last ~500 candles for each symbol / timeframe (Twelve Data)
  2. replays the same state machine as the Pine / MQL5 versions:
       CHOCH + exhaustion move -> MK zone -> 1-2 weak candles inside MK
       -> first reversal candle closes  => "MK formed" alert
  3. sends a Telegram message for new setups only (no trading, alerts only)

Secrets are read from environment variables (GitHub Actions secrets):
  TWELVE_DATA_KEY, TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID

Options:  --test     send a test message and check that data download works
          --force    ignore the "only fetch right after a candle closes" rule
          --history  send the MK setups found in the last N days (env HISTORY_DAYS, default 5)
          --cases    replay the known setups from CASES below and explain why each one
                     was found / missed (sent to Telegram)
          --debug    same explanation for one time window
                     (env DEBUG_SYMBOL, DEBUG_TF, DEBUG_TIME "YYYY-MM-DD HH:MM" UTC+3:30, DEBUG_HOURS)
"""
import json
import os
import sys
import time
from datetime import datetime, timedelta, timezone

import requests

# ───────────────────────── Settings ─────────────────────────
# (display name, Twelve Data symbol, market kind, price digits)
SYMBOLS = [
    ("XAUUSD", "XAU/USD", "forex", 2),
    ("GBPUSD", "GBP/USD", "forex", 5),
    # ("BTCUSD", "BTC/USD", "crypto", 2),   # remove the # to add bitcoin (24/7)
]
# (Twelve Data interval, minutes)
TIMEFRAMES = [("5min", 5), ("15min", 15)]
INTERVALS = {5: "5min", 15: "15min", 30: "30min"}

# Detector settings
PIV_LEN = 5          # swing pivot length
ATR_LEN = 14         # ATR length
TREND_HOURS = 10     # how far back to look for the strong trend (impulse) before the CHOCH
LEG_MULT = 4.0       # the impulse before the CHOCH must be at least this many ATR
BIG_MULT = 1.0       # exhaustion move in 1-2 candles (x ATR)
BASE_N = 2           # origin candles used for the MK zone (1-4)
MAX_ZONE = 3.0       # max MK zone height (x ATR)
WEAK_MULT = 0.8      # weak (hopeless) candle max body (x ATR)
MAX_WEAK_BY_TF = {5: 6, 15: 3, 30: 3}   # max weak candles inside MK per timeframe
STRICT_CLOSE = True  # reversal candle must close beyond the weak candles' extreme
INV_TOL = 0.1        # invalidation tolerance beyond MK (x ATR)
EXPIRE_HOURS = 48    # an MK zone stays valid this long (unless price closes beyond it)
MAX_ZONES = 8        # max simultaneous MK zones kept in memory

HISTORY = 500        # candles downloaded per request (normal runs)
HISTORY_BIG = 2000   # candles downloaded in --history mode
HISTORY_DEBUG = 5000 # candles downloaded in --debug / --cases mode
LOOKBACK_BARS = 3    # only alert for setups that completed in the last N closed candles
STATE_FILE = "state.json"
LOCAL_TZ = timezone(timedelta(hours=3, minutes=30))  # shown in messages (UTC+3:30)

# Known setups read from the user's TradingView screenshots (times are UTC+3:30, zones approximate).
# (label, symbol, timeframe minutes, time you looked at it, hours of context before it,
#  expected direction 1=SELL / -1=BUY, approx zone low, approx zone high)
CASES = [
    ("A", "XAUUSD", 5,  "2026-09-15 17:00", 12,  1, 4287.5, 4292.7),
    ("B", "XAUUSD", 15, "2026-09-15 18:00", 14,  1, 4287.5, 4292.7),
    ("C", "XAUUSD", 5,  "2026-09-17 23:30", 8,   1, 4349.2, 4352.3),
    ("D", "XAUUSD", 15, "2026-09-09 18:30", 30,  1, 4418.0, 4428.0),
    ("E", "XAUUSD", 5,  "2026-09-07 15:30", 8,  -1, 4384.0, 4390.0),
]


# ───────────────────────── Detector ─────────────────────────
def _p(x):
    return f"{x:.6g}"


def detect(candles, tf_min, trace=None):
    """candles: list of dicts (t, o, h, l, c), oldest -> newest, closed candles only.
    Returns a list of 'MK formed' events found in the whole window.
    If trace is a list, human readable diagnostics are appended to it.

    Logic (same idea as the Pine / MQL5 versions, but MK zones now live on their own):
      1. strong impulse in the last TREND_HOURS (leg >= LEG_MULT x ATR)
      2. close breaks the pullback swing that formed after the impulse (CHOCH)
         with 1-2 strong candles (>= BIG_MULT x ATR)
      3. MK zone = origin candles before that move; it stays valid until price closes beyond it
      4. price returns into MK, 1..N weak candles form inside it
      5. first reversal candle closes -> alert
    """
    n = len(candles)
    L = PIV_LEN
    W = max(20, int(TREND_HOURS * 60 / tf_min))
    expire = int(EXPIRE_HOURS * 60 / tf_min)
    max_weak = MAX_WEAK_BY_TF.get(tf_min, 3)
    start = 2 * L + 25
    if n <= start + 2:
        return []

    o = [x["o"] for x in candles]
    h = [x["h"] for x in candles]
    lo = [x["l"] for x in candles]
    cl = [x["c"] for x in candles]

    def note(t, kind, msg):
        if trace is not None:
            trace.append({"t": t, "kind": kind, "msg": msg})

    atr = None
    sw_h = sw_l = None
    sw_h_i = sw_l_i = -1
    zones = []
    out = []
    used_l = used_h = -1   # swing pivots that already produced a CHOCH

    for i in range(1, n):
        # ATR (Wilder / RMA)
        tr = max(h[i] - lo[i], abs(h[i] - cl[i - 1]), abs(lo[i] - cl[i - 1]))
        atr = tr if atr is None else (atr * (ATR_LEN - 1) + tr) / ATR_LEN

        # swing pivots, confirmed L bars later
        if i >= 2 * L:
            pi = i - L
            is_ph = all(h[pi] > h[pi - k] for k in range(1, L + 1)) and \
                    all(h[pi] >= h[pi + k] for k in range(1, L + 1))
            is_pl = all(lo[pi] < lo[pi - k] for k in range(1, L + 1)) and \
                    all(lo[pi] <= lo[pi + k] for k in range(1, L + 1))
            if is_ph:
                sw_h, sw_h_i = h[pi], pi
                note(candles[pi]["t"], "pivot", f"swing HIGH {_p(h[pi])}")
            if is_pl:
                sw_l, sw_l_i = lo[pi], pi
                note(candles[pi]["t"], "pivot", f"swing LOW {_p(lo[pi])}")

        if i < start:
            continue

        # ---- 1) update the MK zones that already exist ----
        alive = []
        for z in zones:
            z["waited"] += 1
            d = z["dir"]
            if d == 1:
                touch = h[i] >= z["lo"]
                inv = cl[i] > z["hi"] + INV_TOL * atr
            else:
                touch = lo[i] <= z["hi"]
                inv = cl[i] < z["lo"] - INV_TOL * atr
            body = abs(cl[i] - o[i])
            is_weak = touch and not inv and body <= WEAK_MULT * atr

            trig = False
            if z["weak"] >= 1 and not inv and z["wext"] is not None:
                if d == 1:
                    trig = cl[i] < o[i] and (not STRICT_CLOSE or cl[i] < z["wext"])
                else:
                    trig = cl[i] > o[i] and (not STRICT_CLOSE or cl[i] > z["wext"])

            tag = f"[{'SELL' if d == 1 else 'BUY'} MK {_p(z['lo'])}-{_p(z['hi'])}]"
            keep = True
            if touch:
                note(candles[i]["t"], "touch",
                     f"{tag} price in MK: close {_p(cl[i])}, body {body / atr:.2f} ATR "
                     f"({'weak' if is_weak else 'not weak, limit ' + str(WEAK_MULT)})")
            if inv:
                keep = False
                note(candles[i]["t"], "cancel", f"{tag} CANCELLED: closed beyond MK ({_p(cl[i])})")
            elif trig:
                sweep = False
                if z["ret"] is not None:
                    sweep = z["ret"] > z["ref"] if d == 1 else z["ret"] < z["ref"]
                out.append({"i": i, "t": candles[i]["t"], "dir": d,
                            "zlo": z["lo"], "zhi": z["hi"], "sweep": sweep})
                keep = False
                note(candles[i]["t"], "trigger", f"{tag} MK FORMED -> alert")
            elif is_weak:
                z["weak"] += 1
                if d == 1:
                    z["wext"] = lo[i] if z["wext"] is None else min(z["wext"], lo[i])
                else:
                    z["wext"] = h[i] if z["wext"] is None else max(z["wext"], h[i])
                if z["weak"] > max_weak:
                    keep = False
                    note(candles[i]["t"], "cancel", f"{tag} CANCELLED: more than {max_weak} weak candles inside MK")
            else:
                z["weak"] = 0
                z["wext"] = None
            if keep and z["waited"] > expire:
                keep = False
                note(candles[i]["t"], "cancel", f"{tag} expired after {EXPIRE_HOURS}h")
            if keep:
                if d == 1:
                    z["ret"] = h[i] if z["ret"] is None else max(z["ret"], h[i])
                else:
                    z["ret"] = lo[i] if z["ret"] is None else min(z["ret"], lo[i])
                alive.append(z)
        zones = alive

        # ---- 2) look for a new CHOCH ----
        s0 = max(0, i - W)
        new = None  # (dir, ref level, leg size)

        if sw_l is not None and sw_l_i != used_l and cl[i] < sw_l and \
                max(o[i], o[i - 1]) >= sw_l - 0.5 * atr:
            pk = max(range(s0, i), key=lambda j: (h[j], j))
            tro = min(lo[s0:pk + 1])
            leg = h[pk] - tro
            leg_ok = leg >= LEG_MULT * atr
            low_ok = sw_l > tro and sw_l_i > pk
            disp = max(o[i], o[i - 1]) - cl[i]
            disp_ok = disp >= BIG_MULT * atr
            if leg_ok and low_ok and disp_ok:
                new = (1, h[pk], leg)
                used_l = sw_l_i
            elif cl[i - 1] >= sw_l:
                why = []
                if not leg_ok:
                    why.append(f"no strong up-trend before it (impulse {leg / atr:.1f} ATR < {LEG_MULT})")
                if not low_ok:
                    why.append("broken low is not the pullback low after the impulse top")
                if not disp_ok:
                    why.append(f"break move {disp / atr:.1f} ATR < {BIG_MULT}")
                note(candles[i]["t"], "cross",
                     f"close broke below swing low {_p(sw_l)} but NOT a CHOCH: " + "; ".join(why))

        if new is None and sw_h is not None and sw_h_i != used_h and cl[i] > sw_h and \
                min(o[i], o[i - 1]) <= sw_h + 0.5 * atr:
            bt = min(range(s0, i), key=lambda j: (lo[j], -j))
            top = max(h[s0:bt + 1])
            leg = top - lo[bt]
            leg_ok = leg >= LEG_MULT * atr
            high_ok = sw_h < top and sw_h_i > bt
            disp = cl[i] - min(o[i], o[i - 1])
            disp_ok = disp >= BIG_MULT * atr
            if leg_ok and high_ok and disp_ok:
                new = (-1, lo[bt], leg)
                used_h = sw_h_i
            elif cl[i - 1] <= sw_h:
                why = []
                if not leg_ok:
                    why.append(f"no strong down-trend before it (impulse {leg / atr:.1f} ATR < {LEG_MULT})")
                if not high_ok:
                    why.append("broken high is not the pullback high after the impulse bottom")
                if not disp_ok:
                    why.append(f"break move {disp / atr:.1f} ATR < {BIG_MULT}")
                note(candles[i]["t"], "cross",
                     f"close broke above swing high {_p(sw_h)} but NOT a CHOCH: " + "; ".join(why))

        if new is not None:
            dirn, ref, leg = new
            if dirn == 1:
                off = 2 if (cl[i - 1] < o[i - 1] and (o[i - 1] - cl[i - 1]) >= 0.5 * BIG_MULT * atr) else 1
            else:
                off = 2 if (cl[i - 1] > o[i - 1] and (cl[i - 1] - o[i - 1]) >= 0.5 * BIG_MULT * atr) else 1
            idx = [i - k for k in range(off, off + BASE_N)]
            hi_w = max(h[j] for j in idx)
            lo_w = min(lo[j] for j in idx)
            b_hi = max(max(o[j], cl[j]) for j in idx)
            b_lo = min(min(o[j], cl[j]) for j in idx)
            if dirn == 1:
                z_hi, z_lo = hi_w, b_lo
                if z_hi - z_lo > MAX_ZONE * atr:
                    z_lo = z_hi - MAX_ZONE * atr
            else:
                z_lo, z_hi = lo_w, b_hi
                if z_hi - z_lo > MAX_ZONE * atr:
                    z_hi = z_lo + MAX_ZONE * atr
            # a fresh CHOCH replaces an untouched zone of the same direction that overlaps it
            zones = [e for e in zones
                     if not (e["dir"] == dirn and e["lo"] <= z_hi and e["hi"] >= z_lo and e["weak"] == 0)]
            zones.append({"dir": dirn, "lo": z_lo, "hi": z_hi, "ref": ref, "ret": None,
                          "wext": None, "weak": 0, "waited": 0})
            if len(zones) > MAX_ZONES:
                zones = zones[-MAX_ZONES:]
            note(candles[i]["t"], "setup",
                 f"CHOCH ok -> {'SELL' if dirn == 1 else 'BUY'} MK zone {_p(z_lo)} - {_p(z_hi)} "
                 f"(impulse {leg / atr:.1f} ATR, ATR {_p(atr)})")

    for z in zones:
        note(candles[-1]["t"], "info",
             f"[{'SELL' if z['dir'] == 1 else 'BUY'} MK {_p(z['lo'])}-{_p(z['hi'])}] still open, waiting")
    return out


# ───────────────────────── Data / Telegram ─────────────────────────
def fetch(td_symbol, interval, tf_min, api_key, now, size=HISTORY):
    r = requests.get(
        "https://api.twelvedata.com/time_series",
        params={
            "symbol": td_symbol,
            "interval": interval,
            "outputsize": size,
            "timezone": "UTC",
            "apikey": api_key,
        },
        timeout=60,
    )
    data = r.json()
    if "values" not in data:
        raise RuntimeError(str(data.get("message", data))[:200])
    rows = []
    for v in data["values"]:
        fmt = "%Y-%m-%d %H:%M:%S" if " " in v["datetime"] else "%Y-%m-%d"
        t = datetime.strptime(v["datetime"], fmt).replace(tzinfo=timezone.utc)
        rows.append({
            "t": t,
            "o": float(v["open"]),
            "h": float(v["high"]),
            "l": float(v["low"]),
            "c": float(v["close"]),
        })
    rows.sort(key=lambda x: x["t"])
    # drop the candle that is still forming
    return [x for x in rows if x["t"] + timedelta(minutes=tf_min) <= now]


def send_telegram(token, chat_id, text):
    if not token or not chat_id:
        print("Telegram token or chat id is missing, message not sent:", text)
        return
    try:
        r = requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={"chat_id": chat_id, "text": text},
            timeout=20,
        )
        if r.status_code != 200:
            print("Telegram error", r.status_code, r.text[:200])
    except Exception as e:  # never print the token
        print("Telegram request failed:", type(e).__name__)


def send_long(token, chat_id, lines, limit=3500):
    """Send many lines as several Telegram messages."""
    buf = ""
    for ln in lines:
        if len(buf) + len(ln) + 1 > limit:
            send_telegram(token, chat_id, buf)
            buf = ""
        buf += ln + "\n"
    if buf.strip():
        send_telegram(token, chat_id, buf)


def market_open(kind, now):
    """Rough forex/gold opening hours in UTC (closed Fri 22:00 -> Sun 22:00)."""
    if kind == "crypto":
        return True
    wd = now.weekday()  # Mon=0 ... Sun=6
    if wd == 5:
        return False
    if wd == 4 and now.hour >= 22:
        return False
    if wd == 6 and now.hour < 22:
        return False
    return True


def load_state():
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_state(state):
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=1, sort_keys=True)


def fmt_local(t):
    return t.astimezone(LOCAL_TZ).strftime("%m-%d %H:%M")


# ───────────────────────── History mode ─────────────────────────
def run_history(api_key, token, chat_id, now):
    """Sends the MK setups found in the last N days (no state is saved, nothing is marked as sent).
    Use it to compare with the same period on your TradingView chart."""
    days = int(os.environ.get("HISTORY_DAYS", "5"))
    cutoff = now - timedelta(days=days)
    for name, td_symbol, kind, digits in SYMBOLS:
        for interval, tf_min in TIMEFRAMES:
            try:
                candles = fetch(td_symbol, interval, tf_min, api_key, now, size=HISTORY_BIG)
            except Exception as e:
                text = f"MK history {name} {tf_min}m: FAILED ({str(e)[:80]})"
                print(text)
                send_telegram(token, chat_id, text)
                time.sleep(1)
                continue
            time.sleep(1)
            if not candles:
                continue
            events = [ev for ev in detect(candles, tf_min) if ev["t"] >= cutoff]
            first = fmt_local(candles[0]["t"])
            lines = [f"MK history | {name} {tf_min}m | last {days} days | {len(events)} setups | data from {first} (UTC+3:30)"]
            for k, ev in enumerate(events, 1):
                side = "SELL" if ev["dir"] == 1 else "BUY"
                close_t = fmt_local(ev["t"] + timedelta(minutes=tf_min))
                lines.append(
                    f"{k}) {side} {close_t} | zone {ev['zlo']:.{digits}f} - {ev['zhi']:.{digits}f}"
                    f"{' + sweep' if ev['sweep'] else ''}"
                )
            text = "\n".join(lines)
            print(text)
            send_telegram(token, chat_id, text)


# ───────────────────────── Debug / known cases ─────────────────────────
def explain_case(candles, label, name, tf_min, when, hours, exp_dir, exp_lo, exp_hi):
    """Returns text lines explaining what the detector did around `when`."""
    w0 = when - timedelta(hours=hours)
    w1 = when + timedelta(hours=2)
    lines = []
    side_txt = "any" if exp_dir is None else ("SELL" if exp_dir == 1 else "BUY")
    head = f"CASE {label} | {name} {tf_min}m | around {fmt_local(when)} (UTC+3:30) | expected {side_txt}"
    if exp_lo is not None:
        head += f" zone ~{exp_lo:g}-{exp_hi:g}"
    lines.append(head)
    if not candles:
        lines.append("no data")
        return lines
    lines.append(f"data covers {fmt_local(candles[0]['t'])} -> {fmt_local(candles[-1]['t'])}")
    if when < candles[0]["t"]:
        lines.append("this time is older than the downloaded data, use a higher timeframe")
        return lines

    trace = []
    events = detect(candles, tf_min, trace)

    # pass / fail
    found = [ev for ev in events
             if when - timedelta(hours=4) <= ev["t"] <= when + timedelta(hours=1)
             and (exp_dir is None or ev["dir"] == exp_dir)]
    if found:
        for ev in found:
            side = "SELL" if ev["dir"] == 1 else "BUY"
            lines.append(f"RESULT: FOUND {side} at {fmt_local(ev['t'] + timedelta(minutes=tf_min))} "
                         f"zone {_p(ev['zlo'])} - {_p(ev['zhi'])}")
    else:
        lines.append("RESULT: NOT FOUND")

    # context: last swings before the window, then everything inside the window
    before = [e for e in trace if e["kind"] == "pivot" and e["t"] < w0][-4:]
    inside = sorted((e for e in trace if w0 <= e["t"] <= w1), key=lambda e: e["t"])
    if before:
        lines.append("swings just before the window:")
        for e in before:
            lines.append(f"  {fmt_local(e['t'])} {e['msg']}")
    lines.append(f"what the detector saw ({fmt_local(w0)} -> {fmt_local(w1)}):")
    shown = 0
    for e in inside:
        if e["kind"] == "touch" and shown > 40:
            continue
        lines.append(f"  {fmt_local(e['t'])} {e['msg']}")
        shown += 1
    if not inside:
        lines.append("  nothing (no swing, no break, no setup)")
    return lines


def run_cases(api_key, token, chat_id, now):
    cache = {}
    for label, name, tf_min, when_s, hours, exp_dir, exp_lo, exp_hi in CASES:
        sym = next((s for s in SYMBOLS if s[0] == name), None)
        if sym is None or tf_min not in INTERVALS:
            continue
        key = (name, tf_min)
        if key not in cache:
            try:
                cache[key] = fetch(sym[1], INTERVALS[tf_min], tf_min, api_key, now, size=HISTORY_DEBUG)
            except Exception as e:
                cache[key] = None
                print(f"{name} {tf_min}m download failed: {e}")
            time.sleep(1)
        candles = cache[key]
        if candles is None:
            send_telegram(token, chat_id, f"CASE {label}: data download failed")
            continue
        when = datetime.strptime(when_s, "%Y-%m-%d %H:%M").replace(tzinfo=LOCAL_TZ)
        lines = explain_case(candles, label, name, tf_min, when, hours, exp_dir, exp_lo, exp_hi)
        print("\n".join(lines))
        send_long(token, chat_id, lines)


def run_debug(api_key, token, chat_id, now):
    name = os.environ.get("DEBUG_SYMBOL", "XAUUSD").strip().upper()
    tf_min = int(os.environ.get("DEBUG_TF", "5") or 5)
    when_s = os.environ.get("DEBUG_TIME", "").strip()
    hours = float(os.environ.get("DEBUG_HOURS", "12") or 12)
    sym = next((s for s in SYMBOLS if s[0] == name), None)
    if sym is None or tf_min not in INTERVALS or not when_s:
        send_telegram(token, chat_id, "debug: set DEBUG_SYMBOL (XAUUSD/GBPUSD), DEBUG_TF (5/15/30) and DEBUG_TIME (YYYY-MM-DD HH:MM)")
        return
    when = datetime.strptime(when_s, "%Y-%m-%d %H:%M").replace(tzinfo=LOCAL_TZ)
    candles = fetch(sym[1], INTERVALS[tf_min], tf_min, api_key, now, size=HISTORY_DEBUG)
    lines = explain_case(candles, "manual", name, tf_min, when, hours, None, None, None)
    print("\n".join(lines))
    send_long(token, chat_id, lines)


# ───────────────────────── Main ─────────────────────────
def main():
    args = sys.argv[1:]
    test = "--test" in args
    force = "--force" in args
    history = "--history" in args
    cases = "--cases" in args
    debug = "--debug" in args

    api_key = os.environ.get("TWELVE_DATA_KEY", "")
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "")
    if not api_key:
        print("TWELVE_DATA_KEY is missing.")
        sys.exit(1)

    now = datetime.now(timezone.utc)
    if history:
        run_history(api_key, token, chat_id, now)
        return
    if cases:
        run_cases(api_key, token, chat_id, now)
        return
    if debug:
        run_debug(api_key, token, chat_id, now)
        return

    state = load_state()
    changed = not os.path.exists(STATE_FILE)
    test_lines = []

    for name, td_symbol, kind, digits in SYMBOLS:
        if not test and not market_open(kind, now):
            print(f"{name}: market closed, skipped")
            continue
        for interval, tf_min in TIMEFRAMES:
            if not (test or force or now.minute % tf_min < 5):
                continue
            try:
                candles = fetch(td_symbol, interval, tf_min, api_key, now)
            except Exception as e:
                print(f"{name} {interval}: download failed: {e}")
                test_lines.append(f"{name} {tf_min}m: FAILED ({str(e)[:80]})")
                time.sleep(1)
                continue
            time.sleep(1)

            n = len(candles)
            if test:
                last = fmt_local(candles[-1]["t"]) if n else "-"
                test_lines.append(f"{name} {tf_min}m: OK, {n} candles, last open {last}")
            key = f"{name}|{tf_min}"
            last_sent = state.get(key)
            for ev in detect(candles, tf_min):
                if ev["i"] < n - LOOKBACK_BARS:
                    continue
                ts = ev["t"].isoformat()
                if last_sent is not None and ts <= last_sent:
                    continue
                side = "SELL" if ev["dir"] == 1 else "BUY"
                close_t = (ev["t"] + timedelta(minutes=tf_min)).astimezone(LOCAL_TZ).strftime("%H:%M")
                text = (
                    f"MK formed {side} | {name} {tf_min}m | "
                    f"zone {ev['zlo']:.{digits}f} - {ev['zhi']:.{digits}f}"
                    f"{' + liquidity sweep' if ev['sweep'] else ''}"
                    f" | candle closed {close_t} (UTC+3:30)"
                )
                print(text)
                send_telegram(token, chat_id, text)
                state[key] = ts
                last_sent = ts
                changed = True

    if test:
        send_telegram(token, chat_id, "MK alert test OK\n" + "\n".join(test_lines))
        print("\n".join(test_lines))

    if changed:
        save_state(state)


if __name__ == "__main__":
    main()
