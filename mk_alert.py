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

Options:  --test   send a test message and check that data download works
          --force  ignore the "only fetch right after a candle closes" rule
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

# Same meaning as the inputs in the Pine / MQL5 versions
PIV_LEN = 5          # swing pivot length
ATR_LEN = 14         # ATR length
LEG_MULT = 3.0       # prior leg min size (x ATR)
BIG_MULT = 1.5       # exhaustion move in 1-2 candles (x ATR)
USE_WEAK = False     # require weakening before the break
BASE_N = 2           # origin candles used for the MK zone (1-4)
MAX_ZONE = 3.0       # max MK zone height (x ATR)
WEAK_MULT = 0.8      # weak candle max body (x ATR)
MAX_WEAK = 2         # max weak candles inside MK
STRICT_CLOSE = True  # reversal candle must close beyond the weak candles' extreme
INV_TOL = 0.1        # invalidation tolerance beyond MK (x ATR)
MAX_WAIT = 60        # max bars to wait after CHOCH

HISTORY = 500        # candles downloaded per request
LOOKBACK_BARS = 3    # only alert for setups that completed in the last N closed candles
STATE_FILE = "state.json"
LOCAL_TZ = timezone(timedelta(hours=3, minutes=30))  # shown in messages (UTC+3:30)


# ───────────────────────── Detector ─────────────────────────
def detect(candles):
    """candles: list of dicts (t, o, h, l, c), oldest -> newest, closed candles only.
    Returns a list of 'MK formed' events found in the whole window."""
    n = len(candles)
    L = PIV_LEN
    start = 2 * L + 25
    if n <= start + 2:
        return []

    o = [x["o"] for x in candles]
    h = [x["h"] for x in candles]
    lo = [x["l"] for x in candles]
    cl = [x["c"] for x in candles]

    atr = None
    sw_h = prev_sw_h = sw_l = prev_sw_l = None
    state = 0
    dirn = 0
    z_hi = z_lo = leg_ref = ret_ext = w_ext = None
    weak_cnt = 0
    waited = 0
    out = []

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
                prev_sw_h, sw_h = sw_h, h[pi]
            if is_pl:
                prev_sw_l, sw_l = sw_l, lo[pi]

        if i < start:
            continue

        weak_ok = True
        if USE_WEAK:
            rec = sum(abs(cl[i - k] - o[i - k]) for k in range(2, 7)) / 5.0
            old = sum(abs(cl[i - k] - o[i - k]) for k in range(7, 22)) / 15.0
            weak_ok = rec < old

        # CHOCH + exhaustion move
        bear = bull = False
        if None not in (sw_h, prev_sw_h, sw_l, prev_sw_l):
            up = sw_h > prev_sw_h and sw_l > prev_sw_l
            leg_up = (sw_h - prev_sw_l) >= LEG_MULT * atr
            disp_bear = (max(o[i], o[i - 1]) - cl[i]) >= BIG_MULT * atr
            cross_dn = cl[i] < sw_l and cl[i - 1] >= sw_l
            bear = up and leg_up and weak_ok and disp_bear and cross_dn

            dn = sw_h < prev_sw_h and sw_l < prev_sw_l
            leg_dn = (prev_sw_h - sw_l) >= LEG_MULT * atr
            disp_bull = (cl[i] - min(o[i], o[i - 1])) >= BIG_MULT * atr
            cross_up = cl[i] > sw_h and cl[i - 1] <= sw_h
            bull = dn and leg_dn and weak_ok and disp_bull and cross_up

        if bear or bull:
            if bear:
                off = 2 if (cl[i - 1] < o[i - 1] and (o[i - 1] - cl[i - 1]) >= 0.5 * BIG_MULT * atr) else 1
            else:
                off = 2 if (cl[i - 1] > o[i - 1] and (cl[i - 1] - o[i - 1]) >= 0.5 * BIG_MULT * atr) else 1
            idx = [i - k for k in range(off, off + BASE_N)]
            hi_w = max(h[j] for j in idx)
            lo_w = min(lo[j] for j in idx)
            b_hi = max(max(o[j], cl[j]) for j in idx)
            b_lo = min(min(o[j], cl[j]) for j in idx)

            if bear:
                dirn = 1
                z_hi, z_lo = hi_w, b_lo
                if z_hi - z_lo > MAX_ZONE * atr:
                    z_lo = z_hi - MAX_ZONE * atr
                leg_ref = sw_h
            else:
                dirn = -1
                z_lo, z_hi = lo_w, b_hi
                if z_hi - z_lo > MAX_ZONE * atr:
                    z_hi = z_lo + MAX_ZONE * atr
                leg_ref = sw_l
            ret_ext = None
            w_ext = None
            weak_cnt = 0
            waited = 0
            state = 1
            continue

        if state == 0:
            continue

        # waiting for MK to form
        waited += 1
        cancel = False
        if dirn == 1:
            touch = h[i] >= z_lo
            inv = cl[i] > z_hi + INV_TOL * atr
        else:
            touch = lo[i] <= z_hi
            inv = cl[i] < z_lo - INV_TOL * atr
        body = abs(cl[i] - o[i])
        is_weak = touch and not inv and body <= WEAK_MULT * atr

        trig = False
        if weak_cnt >= 1 and not inv and w_ext is not None:
            if dirn == 1:
                trig = cl[i] < o[i] and (not STRICT_CLOSE or cl[i] < w_ext)
            else:
                trig = cl[i] > o[i] and (not STRICT_CLOSE or cl[i] > w_ext)

        if inv:
            cancel = True
        elif trig:
            sweep = False
            if ret_ext is not None:
                sweep = ret_ext > leg_ref if dirn == 1 else ret_ext < leg_ref
            out.append({
                "i": i,
                "t": candles[i]["t"],
                "dir": dirn,
                "zlo": z_lo,
                "zhi": z_hi,
                "sweep": sweep,
            })
            state = 0
        elif is_weak:
            weak_cnt += 1
            if dirn == 1:
                w_ext = lo[i] if w_ext is None else min(w_ext, lo[i])
            else:
                w_ext = h[i] if w_ext is None else max(w_ext, h[i])
            if weak_cnt > MAX_WEAK:
                cancel = True
        else:
            weak_cnt = 0
            w_ext = None

        if state != 0 and waited > MAX_WAIT:
            cancel = True

        if state != 0:
            if dirn == 1:
                ret_ext = h[i] if ret_ext is None else max(ret_ext, h[i])
            else:
                ret_ext = lo[i] if ret_ext is None else min(ret_ext, lo[i])

        if cancel:
            state = 0

    return out


# ───────────────────────── Data / Telegram ─────────────────────────
def fetch(td_symbol, interval, tf_min, api_key, now):
    r = requests.get(
        "https://api.twelvedata.com/time_series",
        params={
            "symbol": td_symbol,
            "interval": interval,
            "outputsize": HISTORY,
            "timezone": "UTC",
            "apikey": api_key,
        },
        timeout=30,
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


# ───────────────────────── Main ─────────────────────────
def main():
    args = sys.argv[1:]
    test = "--test" in args
    force = "--force" in args

    api_key = os.environ.get("TWELVE_DATA_KEY", "")
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID", "")
    if not api_key:
        print("TWELVE_DATA_KEY is missing.")
        sys.exit(1)

    now = datetime.now(timezone.utc)
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
                last = candles[-1]["t"].astimezone(LOCAL_TZ).strftime("%m-%d %H:%M") if n else "-"
                test_lines.append(f"{name} {tf_min}m: OK, {n} candles, last open {last}")
            key = f"{name}|{tf_min}"
            last_sent = state.get(key)
            for ev in detect(candles):
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
