"""
================================================================================
 AIGCL T20 GPL  ·  Presented by Alobha Technologies
 VIP ENTRY PASS  —  issuance portal + hardware gate authentication
================================================================================
 Two systems in one file.

 ISSUANCE (public tab)
   Attendee submits Name / Organisation / WhatsApp -> the backend allocates the
   first free pass in strict sequence (Pass-1 .. Pass-200) -> locks it in Google
   Sheets -> draws a high-resolution JPEG pass with Pillow, auto-downloads it,
   and shows it inline. No PDF libraries anywhere.

 GATE (admin tab)
   A hardware QR scanner types the ticket payload and presses Enter. The form
   is clear_on_submit so scanning is continuous — no mouse, no tapping.
   Three and only three verdicts:
       INVALID        payload fails the HMAC, or the pass was never issued
       DUPLICATE      checkin_time already stamped — someone used this pass
       AUTHENTICATED checkin_time written, guest walks in

 SECURITY MODEL — read this before deploying
   The QR carries  VALIDATE|Pass-42|<10-hex>  where the hex is a truncated
   HMAC-SHA256 over "EVENT|seat" keyed with `security_salt` from st.secrets.
   * The salt NEVER leaves the server, so a guest holding a real pass cannot
     compute a signature for any other pass number.
   * Truncated to 10 hex chars = 40 bits. Brute-forcing one valid signature
     offline is trivial for a computer but the attacker has no oracle — they
     would have to present forged QRs at a physical gate to test, so the real
     defence is that a wrong guess is a public rejection.
   * If you leave the default salt in place the scheme is worthless. The admin
     panel screams about it until you set a real one.
   * The pass is NOT anti-copy. Two phones showing the same valid QR is exactly
     the case DUPLICATE detection exists to catch — first scan wins.

 CONCURRENCY — read this too
   Google Sheets has no row-level locking. `update()` rewrites the whole
   worksheet. Run gate check-in from ONE device. Two scanners writing in the
   same second will silently clobber each other's stamps.

 TYPE SYSTEM
   Playfair Display (high-contrast serif) for the marquee — championship
   titling. Inter (neutral grotesque) for every label, value and numeral —
   boarding-pass data. An editorial display face against a technical UI face is
   what separates a premiere invitation from a form print-out.

 Run:   streamlit run app.py

 .streamlit/secrets.toml
     [connections.gsheets]
     spreadsheet = "https://docs.google.com/spreadsheets/d/..."
     type = "service_account"
     ...service account keys...

     [app]
     admin_password = "..."
     security_salt  = "long-random-string-keep-private"
     event_time     = "1:00 AM"
     maps_url       = "https://maps.app.goo.gl/..."

 Assets next to app.py:
     header.png            edge-bleed artwork on the ticket + web hero
     footer.png            web page footer
     sponsor1.png          sponsor logo 1 (rendered at bottom)
     sponsor2.png          sponsor logo 2
     sponsor3.png          sponsor logo 3
     sponsor4.png          sponsor logo 4
     sponsor5.png          sponsor logo 5
     sponsor6.png          sponsor logo 6
     sponsor7.png          sponsor logo 7
     sponsor8.png          sponsor logo 8
     assets/*.ttf          OPTIONAL. Fetched once on first run if absent.
================================================================================
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import io
import re
import time
import urllib.request
from datetime import datetime
from functools import lru_cache
from pathlib import Path
from typing import Any, Final
from zoneinfo import ZoneInfo

import pandas as pd
import qrcode
import streamlit as st
from PIL import Image, ImageDraw, ImageFilter, ImageFont
from streamlit.components.v1 import html as components_html
from streamlit_gsheets import GSheetsConnection

# =============================================================================
# 1. CONFIGURATION
# =============================================================================

TOTAL_PASSES: Final[int] = 200
PASS_PREFIX: Final[str] = "Pass-"
SEAT_ORDER: Final[list[str]] = [f"{PASS_PREFIX}{n}" for n in range(1, TOTAL_PASSES + 1)]
SEAT_RANK: Final[dict[str, int]] = {seat: i for i, seat in enumerate(SEAT_ORDER)}
TOTAL_SEATS: Final[int] = len(SEAT_ORDER)

WORKSHEET: Final[str] = "passes"
SCHEMA: Final[list[str]] = [
    "seat_id", "status", "name", "organisation", "phone", "booked_at",
    "checkin_time",
]
AVAILABLE: Final[str] = "Available"
BOOKED: Final[str] = "Booked"
IST: Final[ZoneInfo] = ZoneInfo("Asia/Kolkata")

STATS_TTL: Final[int] = 10
ALLOC_ATTEMPTS: Final[int] = 4
ONE_PASS_PER_PHONE: Final[bool] = True

BASE_DIR: Final[Path] = Path(__file__).parent
HEADER_IMG: Final[Path] = BASE_DIR / "header.png"
FOOTER_IMG: Final[Path] = BASE_DIR / "footer.png"
ASSET_DIR: Final[Path] = BASE_DIR / "assets"


def cfg(key: str, default: Any = "") -> Any:
    """Secrets lookup that never explodes when secrets.toml is absent."""
    try:
        return st.secrets.get("app", {}).get(key, default)
    except Exception:  # noqa: BLE001 — missing secrets file must not kill the app
        return default


EVENT_NAME: Final[str] = cfg("event_name", "AIGCL T20 GPL")
EVENT_SUBTITLE: Final[str] = cfg("event_subtitle", "Presented by Alobha Technologies")
VENUE: Final[str] = cfg("venue", "Hotel Radisson Blu, Paschim Vihar, New Delhi")
EVENT_DATE: Final[str] = cfg("event_date", "13 September 2026")
EVENT_TIME: Final[str] = cfg("event_time", "1:00 PM")
MAPS_URL: Final[str] = cfg("maps_url", "")
TICKET_VALUE: Final[str] = str(cfg("ticket_value", "By Invitation Only"))
FETCH_FONTS: Final[bool] = bool(cfg("fetch_fonts", True))

# --- Gate security -----------------------------------------------------------
DEFAULT_SALT: Final[str] = "aigcl-gpl-CHANGE-THIS-SALT"
SECURITY_SALT: Final[str] = str(cfg("security_salt", DEFAULT_SALT))
SALT_IS_DEFAULT: Final[bool] = SECURITY_SALT == DEFAULT_SALT
HASH_LEN: Final[int] = 10
SCAN_RE: Final[re.Pattern[str]] = re.compile(
    r"^\s*VALIDATE\s*\|\s*([A-Za-z]*[\s\-_]*\d{1,4})\s*\|\s*([A-Fa-f0-9]{%d})\s*$"
    % HASH_LEN
)
SEAT_RE: Final[re.Pattern[str]] = re.compile(r"^\s*(?:pass)?[\s\-_]*(\d{1,4})\s*$", re.I)

SPLASH_HOLD: Final[float] = 0.85
SPLASH_FADE: Final[float] = 0.65
REVEAL_BASE: Final[float] = 0.72

# --- Palette -----------------------------------------------------------------
# Championship gold for structure, pitch emerald and Alobha royal blue as
# ambient light only. The metals are identical in CSS and in Pillow so the web
# portal and the printed pass are the same object.
GOLD_STOPS: Final[tuple[str, ...]] = (
    "#BF953F", "#FCF6BA", "#B38728", "#FBF5B7", "#AA771C",
)
GOLD_CSS: Final[str] = "linear-gradient(135deg," + ",".join(GOLD_STOPS) + ")"
GOLD: Final[str] = "#D4AF37"
GOLD_SOFT: Final[str] = "#E8CC6B"
OBSIDIAN: Final[str] = "#090B10"
EMERALD: Final[str] = "#1FBF75"
ROYAL: Final[str] = "#2F6BFF"
ALERT: Final[str] = "#FF4D5E"
AMBER: Final[str] = "#FFB020"

RGB_GOLD_STOPS: Final[tuple[tuple[int, int, int], ...]] = tuple(
    (int(h[1:3], 16), int(h[3:5], 16), int(h[5:7], 16)) for h in GOLD_STOPS
)
RGB_GOLD: Final[tuple[int, int, int]] = (212, 175, 55)
RGB_EMERALD: Final[tuple[int, int, int]] = (31, 191, 117)
RGB_ROYAL: Final[tuple[int, int, int]] = (47, 107, 255)
RGB_INK: Final[tuple[int, int, int]] = (10, 11, 14)
RGB_MUTED: Final[tuple[int, int, int]] = (143, 149, 160)
RGB_TEXT: Final[tuple[int, int, int]] = (246, 243, 236)
RGB_SILVER: Final[tuple[int, int, int]] = (226, 231, 240)

# --- Ticket canvas -----------------------------------------------------------
TICKET_W: Final[int] = 1600          # design grid
TICKET_H: Final[int] = 600
SS: Final[int] = 2                   # supersample factor
OUT_SCALE: Final[float] = 1.5        # final JPEG = 2400 x 900
STUB_X: Final[int] = 1058
QR_PX: Final[int] = 230
JPEG_QUALITY: Final[int] = 94


def seat_number(seat_id: str) -> str:
    """'Pass-127' -> '127'. The stub hero is the numeral alone."""
    return str(seat_id).split("-")[-1].strip() or str(seat_id)


def normalise_seat(raw: str) -> str | None:
    """Accept 'Pass-12', 'pass 12', 'PASS_12', '12' -> 'Pass-12'. Else None."""
    match = SEAT_RE.match(str(raw))
    if not match:
        return None
    number = int(match.group(1))
    if not 1 <= number <= TOTAL_PASSES:
        return None
    return f"{PASS_PREFIX}{number}"


# =============================================================================
# 2. FONT SYSTEM
# =============================================================================
# Pillow's built-in default is a bitmap face that looks like a receipt printer,
# so a real TTF is non-negotiable. Two further traps:
#   * The Rupee sign (U+20B9) is NOT in every TTF. DejaVu has it, Liberation
#     does not (verified by rendering). A silent font swap turns a price badge
#     into a tofu box, so the resolved face is probed at runtime.
#   * Google's OFL faces ship as VARIABLE fonts. FreeType loads the default
#     instance, which is Regular — asking for "Bold" and silently getting
#     Regular is why programmatic tickets look limp. set_variation_by_name()
#     pulls the real weight.

FONT_SOURCES: Final[dict[str, str]] = {
    "Inter.ttf":
        "https://raw.githubusercontent.com/google/fonts/main/ofl/inter/"
        "Inter%5Bopsz%2Cwght%5D.ttf",
    "PlayfairDisplay.ttf":
        "https://raw.githubusercontent.com/google/fonts/main/ofl/playfairdisplay/"
        "PlayfairDisplay%5Bwght%5D.ttf",
}

SYSTEM_SANS: Final[tuple[str, ...]] = (
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/local/lib/python3.12/dist-packages/matplotlib/mpl-data/fonts/ttf/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
    "/Library/Fonts/Arial Bold.ttf",
    "C:/Windows/Fonts/arialbd.ttf",
)
SYSTEM_SERIF: Final[tuple[str, ...]] = (
    "/usr/share/fonts/truetype/dejavu/DejaVuSerif-Bold.ttf",
    "/usr/local/lib/python3.12/dist-packages/matplotlib/mpl-data/fonts/ttf/DejaVuSerif-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSerif-Bold.ttf",
    "/System/Library/Fonts/Supplemental/Georgia Bold.ttf",
    "C:/Windows/Fonts/georgiab.ttf",
)


def _fetch_font(name: str) -> Path | None:
    """
    One-time download into assets/. Wrapped tight: a 12s timeout, any failure
    is swallowed, and the app falls through to system fonts. A ticketing portal
    must never fail to issue a pass because a CDN was slow.
    """
    target = ASSET_DIR / name
    if target.exists():
        return target
    if not FETCH_FONTS or name not in FONT_SOURCES:
        return None
    try:
        ASSET_DIR.mkdir(parents=True, exist_ok=True)
        with urllib.request.urlopen(FONT_SOURCES[name], timeout=12) as response:
            payload = response.read()
        if len(payload) < 20_000:          # obviously not a font
            return None
        tmp = target.with_suffix(".part")
        tmp.write_bytes(payload)
        ImageFont.truetype(str(tmp), 24)   # prove it parses before publishing
        tmp.replace(target)
        return target
    except Exception:                       # noqa: BLE001 — never fatal
        return None


@lru_cache(maxsize=8)
def _face(role: str) -> tuple[str | None, str | None]:
    """Return (path, forced_variation_name) for a type role."""
    if role == "serif":
        local = _fetch_font("PlayfairDisplay.ttf")
        if local:
            return str(local), "Bold"
        for candidate in SYSTEM_SERIF:
            if Path(candidate).exists():
                return candidate, None
        role = "sans"                        # no serif anywhere — fall through
    local = _fetch_font("Inter.ttf")
    if local:
        return str(local), None
    for candidate in SYSTEM_SANS:
        if Path(candidate).exists():
            return candidate, None
    return None, None


# role -> (face, variable-axis weight)
ROLES: Final[dict[str, tuple[str, str | None]]] = {
    "title":    ("serif", "Black"),
    "subtitle": ("serif", "Medium"),
    "hero":     ("sans", "Black"),      # the pass numeral
    "strong":   ("sans", "Bold"),
    "label":    ("sans", "Medium"),
}


@lru_cache(maxsize=256)
def font(role: str, size: int) -> Any:
    face, default_weight = ROLES.get(role, ("sans", "Bold"))
    path, forced = _face(face)
    if not path:
        try:
            return ImageFont.load_default(size=size)
        except TypeError:
            return ImageFont.load_default()
    fnt = ImageFont.truetype(path, size)
    weight = forced or default_weight
    if weight:
        try:
            fnt.set_variation_by_name(weight)
        except Exception:                    # noqa: BLE001 — static face, fine
            pass
    return fnt


@lru_cache(maxsize=16)
def font_has_glyph(role: str, char: str) -> bool:
    """
    Render the character beside a guaranteed-unmapped codepoint. Identical
    bitmaps mean the font is drawing .notdef — a tofu box — so the glyph is
    missing and we must substitute.
    """
    probe = font(role, 48)

    def stamp(text: str) -> bytes:
        img = Image.new("L", (96, 96), 0)
        ImageDraw.Draw(img).text((6, 6), text, font=probe, fill=255)
        return img.tobytes()

    target = stamp(char)
    return target != stamp("\uFFFE") and target != stamp(" ")


def fonts_ready() -> bool:
    return _face("sans")[0] is not None


@lru_cache(maxsize=2)
def rupee() -> str:
    return "\u20B9" if font_has_glyph("strong", "\u20B9") else "Rs. "


@lru_cache(maxsize=2)
def ellipsis() -> str:
    return "\u2026" if font_has_glyph("strong", "\u2026") else "..."


# =============================================================================
# 3. DRAWING PRIMITIVES
# =============================================================================


def money_text(value: Any) -> str:
    """A stray secrets value must never crash ticket generation."""
    try:
        return f"{float(str(value).replace(',', '').strip()):,.0f}"
    except (TypeError, ValueError):
        return str(value)


def value_is_numeric() -> bool:
    return bool(re.fullmatch(r"[\d,]+(\.\d+)?", str(TICKET_VALUE).strip()))


def value_label() -> str:
    """`ticket_value` may be a number OR a phrase like 'By Invitation Only'."""
    if value_is_numeric():
        return f"{rupee()}{money_text(TICKET_VALUE)} VALUE"
    return str(TICKET_VALUE).strip().upper()


def now_ist() -> str:
    return datetime.now(IST).strftime("%d-%m-%Y %H:%M:%S")


def clock_ist() -> str:
    return datetime.now(IST).strftime("%H:%M:%S")


# --- OpenType figures -------------------------------------------------------
# Playfair Display defaults to OLD-STYLE figures: the 2 and the 0 drop below
# cap height, so "T20" renders as "T2o" and "2026" looks like a footnote. On a
# T20 league pass that is not a stylistic quibble, it is a misprint. `lnum`
# forces lining figures; `tnum` makes them tabular, which is what you want for
# phone numbers and dates anyway. Inter is already lining, so both are no-ops
# there and can be applied globally.
#
# Applying features needs libraqm. Pillow's manylinux wheels bundle it, but a
# source build may not, and passing `features=` without it raises. Probe once,
# then every text call degrades silently to plain layout.
OT_FEATURES: Final[list[str]] = ["lnum", "tnum"]


def _raqm_available() -> bool:
    try:
        from PIL import features as pil_features
        if not pil_features.check("raqm"):
            return False
        probe = Image.new("L", (8, 8), 0)
        ImageDraw.Draw(probe).text((0, 0), "0", font=font("label", 8), fill=255,
                                   features=OT_FEATURES)
        return True
    except Exception:                        # noqa: BLE001 — no Raqm, no features
        return False


@lru_cache(maxsize=1)
def features_ok() -> bool:
    return _raqm_available()


def ot_len(draw: ImageDraw.ImageDraw, text: str, fnt: Any) -> float:
    """Measure with the SAME features used to draw, or fit_text mis-measures."""
    if features_ok():
        try:
            return draw.textlength(text, font=fnt, features=OT_FEATURES)
        except Exception:                    # noqa: BLE001
            pass
    return draw.textlength(text, font=fnt)


def ot_text(draw: ImageDraw.ImageDraw, xy: tuple[float, float], text: str,
            fnt: Any, fill: Any, anchor: str = "la") -> None:
    """`fill` is an RGB tuple on the canvas and a plain int on an L mask."""
    if features_ok():
        try:
            draw.text(xy, text, font=fnt, fill=fill, anchor=anchor,
                      features=OT_FEATURES)
            return
        except Exception:                    # noqa: BLE001
            pass
    draw.text(xy, text, font=fnt, fill=fill, anchor=anchor)


def text_w(draw: ImageDraw.ImageDraw, text: str, fnt: Any, tracking: float = 0) -> float:
    return ot_len(draw, text, fnt) + tracking * max(len(text) - 1, 0)


def draw_tracked(
    draw: ImageDraw.ImageDraw, xy: tuple[float, float], text: str, fnt: Any,
    fill: tuple[int, int, int], tracking: float = 0, anchor: str = "la",
) -> None:
    """
    Pillow has no letter-spacing. Wide tracking on small uppercase labels is the
    single strongest "premium print" signal, so glyphs are advanced by hand.
    """
    x, y = xy
    if tracking <= 0:
        ot_text(draw, (x, y), text, fnt, fill, anchor=anchor)
        return
    total = text_w(draw, text, fnt, tracking)
    if anchor[0] == "m":
        x -= total / 2
    elif anchor[0] == "r":
        x -= total
    vertical = anchor[1] if len(anchor) > 1 else "a"
    for ch in text:
        ot_text(draw, (x, y), ch, fnt, fill, anchor="l" + vertical)
        x += ot_len(draw, ch, fnt) + tracking


def fit_font(draw: ImageDraw.ImageDraw, text: str, role: str, max_w: float,
             start: int, minimum: int) -> Any:
    size = start
    while size > minimum and ot_len(draw, text, font(role, size)) > max_w:
        size -= 2
    return font(role, size)


def fit_text(draw: ImageDraw.ImageDraw, text: str, role: str, max_w: float,
             start: int, minimum: int) -> tuple[Any, str]:
    """
    Shrink to fit, then TRUNCATE if it still overflows at the size floor.
    Shrinking alone bottoms out and lets a 60-character organisation name run
    through the next column and into the stub.
    """
    fnt = fit_font(draw, text, role, max_w, start, minimum)
    if ot_len(draw, text, fnt) <= max_w:
        return fnt, text
    clipped = text
    while clipped and ot_len(draw, clipped + ellipsis(), fnt) > max_w:
        clipped = clipped[:-1]
    return fnt, (clipped.rstrip() + ellipsis()) if clipped else text[:1]


def fit_tracked(draw: ImageDraw.ImageDraw, text: str, role: str, max_w: float,
                start: int, minimum: int, tracking: float) -> tuple[Any, str]:
    """fit_text, but accounting for hand-applied tracking in the width budget."""
    size = start
    while size > minimum and text_w(draw, text, font(role, size), tracking) > max_w:
        size -= 1
    fnt = font(role, size)
    if text_w(draw, text, fnt, tracking) <= max_w:
        return fnt, text
    clipped = text
    while clipped and text_w(draw, clipped + ellipsis(), fnt, tracking) > max_w:
        clipped = clipped[:-1]
    return fnt, (clipped.rstrip() + ellipsis()) if clipped else text[:1]


@lru_cache(maxsize=4)
def gold_ramp(size: tuple[int, int]) -> Image.Image:
    """The five-stop metal, as a vertical ramp. Flat gold reads like clip art."""
    w, h = size
    ramp = Image.new("RGB", (1, max(h, 2)))
    px = ramp.load()
    stops = RGB_GOLD_STOPS
    span = len(stops) - 1
    for y in range(ramp.height):
        t = y / max(ramp.height - 1, 1) * span
        i = min(int(t), span - 1)
        k = t - i
        c0, c1 = stops[i], stops[i + 1]
        px[0, y] = tuple(round(c0[j] + (c1[j] - c0[j]) * k) for j in range(3))
    return ramp.resize((max(w, 1), max(h, 1)), Image.BILINEAR)


def _text_mask(size: tuple[int, int], xy: tuple[float, float], text: str,
               fnt: Any, tracking: float, anchor: str) -> Image.Image:
    mask = Image.new("L", size, 0)
    draw_tracked(ImageDraw.Draw(mask), xy, text, fnt, 255,
                 tracking=tracking, anchor=anchor)
    return mask


def draw_embossed(
    canvas: Image.Image, xy: tuple[float, float], text: str, fnt: Any,
    anchor: str = "la", tracking: float = 0, glow: int = 0, emboss: int = 0,
) -> None:
    """
    Foil-stamp in three passes: dark shadow down-right, metallic ramp, pale
    highlight up-left. Separate masks rather than ImageChops.offset, which wraps
    at the canvas edge and would smear a glyph onto the opposite side.
    """
    size = canvas.size
    x, y = xy
    mask = _text_mask(size, (x, y), text, fnt, tracking, anchor)

    if glow:
        halo = mask.filter(ImageFilter.GaussianBlur(glow))
        canvas.paste(Image.new("RGB", size, RGB_GOLD), (0, 0),
                     halo.point(lambda v: int(v * 0.46)))
    if emboss:
        shadow = _text_mask(size, (x + emboss, y + emboss), text, fnt, tracking, anchor)
        canvas.paste(Image.new("RGB", size, (0, 0, 0)), (0, 0),
                     shadow.point(lambda v: int(v * 0.82)))
        hi = _text_mask(size, (x - emboss * 0.5, y - emboss * 0.5), text,
                        fnt, tracking, anchor)
        canvas.paste(Image.new("RGB", size, (255, 250, 226)), (0, 0),
                     hi.point(lambda v: int(v * 0.30)))
    canvas.paste(gold_ramp(size), (0, 0), mask)


def vertical_mask(size: tuple[int, int], stops: list[tuple[float, float]]) -> Image.Image:
    """
    L mask from (position 0..1, alpha 0..1) stops. This is what keeps the header
    artwork OFF the text: alpha drops to exactly zero across the detail block,
    so contrast there is guaranteed rather than hoped for.
    """
    w, h = size
    strip = Image.new("L", (1, max(h, 2)), 0)
    px = strip.load()
    ordered = sorted(stops)
    for y in range(strip.height):
        t = y / max(strip.height - 1, 1)
        val = ordered[-1][1]
        for i in range(len(ordered) - 1):
            t0, a0 = ordered[i]
            t1, a1 = ordered[i + 1]
            if t0 <= t <= t1:
                val = a0 + (a1 - a0) * (t - t0) / max(t1 - t0, 1e-6)
                break
        px[0, y] = max(0, min(255, int(val * 255)))
    return strip.resize((max(w, 1), max(h, 1)), Image.BILINEAR)


def radial_glow(size: tuple[int, int], centre: tuple[float, float],
                radius: float, strength: float) -> Image.Image:
    w, h = size
    small = 96
    mask = Image.new("L", (small, small), 0)
    md = ImageDraw.Draw(mask)
    cx, cy = centre[0] / w * small, centre[1] / h * small
    steps = 26
    for i in range(steps, 0, -1):
        r = radius / max(w, h) * small * (i / steps)
        md.ellipse([cx - r, cy - r, cx + r, cy + r],
                   fill=int(255 * strength * (1 - i / steps) ** 1.7))
    return mask.resize((w, h), Image.BILINEAR)


def cover_fit(img: Image.Image, size: tuple[int, int]) -> Image.Image:
    """Scale-and-crop to fill, preserving aspect ratio (never squashed)."""
    tw, th = size
    sw, sh = img.size
    scale = max(tw / sw, th / sh)
    resized = img.resize((max(1, round(sw * scale)), max(1, round(sh * scale))),
                         Image.LANCZOS)
    left, top = (resized.width - tw) // 2, (resized.height - th) // 2
    return resized.crop((left, top, left + tw, top + th))


@st.cache_data(show_spinner=False)
def load_flat_rgb(path_str: str, _mtime: float) -> bytes | None:
    """
    Flatten any PNG onto the ticket ground as RGB. JPEG has no alpha, and a
    palette PNG carrying transparency composites unpredictably — flattening once
    up front kills a whole class of "why is my banner a black rectangle" bugs.
    """
    try:
        with Image.open(path_str) as src:
            src.load()
            rgba = src.convert("RGBA")
            flat = Image.new("RGB", rgba.size, RGB_INK)
            flat.paste(rgba, (0, 0), rgba)
    except (OSError, ValueError):
        return None
    buf = io.BytesIO()
    flat.save(buf, "PNG")
    return buf.getvalue()


def header_art() -> Image.Image | None:
    if not HEADER_IMG.exists():
        return None
    raw = load_flat_rgb(str(HEADER_IMG), HEADER_IMG.stat().st_mtime)
    return Image.open(io.BytesIO(raw)).convert("RGB") if raw else None


# =============================================================================
# 4. GATE SECURITY  (HMAC payload + abstract security print)
# =============================================================================


def security_hash(seat_id: str) -> str:
    """
    Truncated HMAC-SHA256 over "EVENT|seat", keyed with the private salt.
    HMAC rather than a bare sha256(salt + msg) — correct construction, same
    cost, and it keeps the key handling honest.
    """
    return hmac.new(
        SECURITY_SALT.encode("utf-8"),
        f"{EVENT_NAME}|{seat_id}".encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()[:HASH_LEN].upper()


def gate_payload(seat_id: str) -> str:
    """Deliberately short — a sparse QR is a QR that scans on the first try."""
    return f"VALIDATE|{seat_id}|{security_hash(seat_id)}"


def verify_payload(raw: str) -> str | None:
    """Full payload -> canonical seat_id, or None if the signature is wrong."""
    match = SCAN_RE.match(str(raw))
    if not match:
        return None
    seat = normalise_seat(match.group(1))
    if seat is None:
        return None
    if not hmac.compare_digest(security_hash(seat), match.group(2).upper()):
        return None
    return seat


def qr_image(payload: str, edge_px: int) -> Image.Image:
    """
    ERROR_CORRECT_L keeps the grid sparse — higher levels add redundancy
    modules, shrinking each module at a fixed print size, the opposite of what
    a hand-held scan needs. NEAREST resize keeps module edges razor sharp;
    LANCZOS would blur them into grey mush.
    """
    # border=4 is the spec minimum quiet zone. It was 3, which decodes fine on
    # a flat scan but leaves nothing to spare when an operator fills the
    # viewfinder edge-to-edge and the camera clips the white margin — the
    # decoder then cannot locate the finder patterns at all.
    qr = qrcode.QRCode(version=None, box_size=10, border=4,
                       error_correction=qrcode.constants.ERROR_CORRECT_L)
    qr.add_data(payload)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white").convert("RGB")
    return img.resize((edge_px, edge_px), Image.NEAREST)


def qr_px_per_module(payload: str, edge_px: int = round(QR_PX * OUT_SCALE)) -> float:
    probe = qrcode.QRCode(version=None, box_size=1, border=4,
                          error_correction=qrcode.constants.ERROR_CORRECT_L)
    probe.add_data(payload)
    probe.make(fit=True)
    total = probe.modules_count + 8
    return edge_px / total if total else 0.0


def ticket_digest(row: pd.Series) -> str:
    """Stable per pass — the bars MUST look identical every regeneration."""
    seed = f"{EVENT_NAME}|{row['seat_id']}|{row['phone']}|{row['booked_at']}"
    return hashlib.sha256(seed.encode("utf-8")).hexdigest()


def draw_security_bars(draw: ImageDraw.ImageDraw, x: float, y: float,
                       w: float, h: float, digest: str, s: int) -> None:
    """
    Abstract security-print bars — the visual language premiere passes use to
    signal "official document".

    NOT machine-readable, by design and by honesty: it encodes nothing and no
    scanner will read it. It IS deterministic (hashed from seat + phone + time)
    so the same pass always renders identically; a random pattern would change
    on every regeneration, which is exactly what a forgery looks like.
    Everything the gate actually reads lives in the QR.
    """
    raw = bytes.fromhex(digest)
    cx, i = x, 0
    while cx < x + w and i < 512:
        b = raw[i % len(raw)]
        bar = (1 + (b % 4)) * s
        gap = (1 + ((b >> 3) % 3)) * s
        if cx + bar > x + w:
            break
        tall = h if (b & 0x40) else h * 0.66
        colour = RGB_GOLD if (b & 0x08) else RGB_SILVER
        draw.rectangle([cx, y + (h - tall), cx + bar, y + h], fill=colour)
        cx += bar + gap
        i += 1


# =============================================================================
# 5. THE TICKET
# =============================================================================


def _draw_background(canvas: Image.Image, s: int) -> None:
    """
    Pitch black ground lit from four corners: championship gold top-left,
    Alobha royal blue top-right, pitch emerald along the bottom. Header artwork
    bleeds in at the TOP and BOTTOM edges only and is masked to zero across the
    middle band, so guest details always sit on pure black. A full-canvas
    watermark is precisely what makes the type look muddy.
    """
    w, h = canvas.size
    art = header_art()
    if art is not None:
        bed = cover_fit(art, (w, h))
        bed = bed.filter(ImageFilter.GaussianBlur(5 * s)).point(lambda v: int(v * 0.48))
        canvas.paste(bed, (0, 0), vertical_mask(
            (w, h),
            [(0.00, 0.52), (0.13, 0.26), (0.25, 0.00),
             (0.78, 0.00), (0.91, 0.20), (1.00, 0.38)],
        ))

    def glow(rgb: tuple[int, int, int], centre: tuple[float, float],
             radius: float, strength: float) -> None:
        canvas.paste(Image.new("RGB", (w, h), rgb), (0, 0),
                     radial_glow((w, h), centre, radius, strength))

    glow(RGB_GOLD, (w * 0.03, -h * 0.18), w * 0.55, 0.22)
    glow(RGB_ROYAL, (w * 1.00, -h * 0.10), w * 0.40, 0.17)
    glow(RGB_EMERALD, (w * 0.22, h * 1.18), w * 0.50, 0.16)
    glow(RGB_GOLD, (w * 0.90, h * 1.14), w * 0.34, 0.12)

    vign = Image.new("RGB", (w, h), (0, 0, 0))
    edge = Image.new("L", (w, h), 255)
    ImageDraw.Draw(edge).rounded_rectangle(
        [w * 0.026, h * 0.05, w * 0.974, h * 0.95],
        radius=int(h * 0.10), fill=0)
    canvas.paste(vign, (0, 0),
                 edge.filter(ImageFilter.GaussianBlur(int(h * 0.07)))
                     .point(lambda v: int(v * 0.9)))


def _draw_gold_rule(canvas: Image.Image, box: tuple[float, float, float, float],
                    radius: int, width: int) -> None:
    """A rounded rect stroked with the real metal ramp, not a flat colour."""
    mask = Image.new("L", canvas.size, 0)
    ImageDraw.Draw(mask).rounded_rectangle(box, radius=radius,
                                           outline=255, width=width)
    canvas.paste(gold_ramp(canvas.size), (0, 0), mask)


def _draw_frame(canvas: Image.Image, w: int, h: int, s: int) -> None:
    inset, radius = 15 * s, 26 * s
    _draw_gold_rule(canvas, (inset, inset, w - inset, h - inset), radius, max(1, 2 * s))
    draw = ImageDraw.Draw(canvas)
    draw.rounded_rectangle(
        [inset + 7 * s, inset + 7 * s, w - inset - 7 * s, h - inset - 7 * s],
        radius=radius - 5 * s, outline=(122, 100, 24), width=max(1, s))
    arm = 26 * s
    for cx, cy, dx, dy in (
        (inset + 22 * s, inset + 22 * s, 1, 1),
        (w - inset - 22 * s, inset + 22 * s, -1, 1),
        (inset + 22 * s, h - inset - 22 * s, 1, -1),
        (w - inset - 22 * s, h - inset - 22 * s, -1, -1),
    ):
        draw.line([cx, cy, cx + arm * dx, cy], fill=RGB_GOLD, width=max(1, 2 * s))
        draw.line([cx, cy, cx, cy + arm * dy], fill=RGB_GOLD, width=max(1, 2 * s))


def _draw_seam(draw: ImageDraw.ImageDraw, x0: float, x1: float, y: float,
               s: int) -> None:
    """
    The signature detail: the divider under the marquee is a cricket-ball seam.
    A dim gold hairline the full width, with six angled stitches worked over the
    centre. It is the only literal cricket reference on the pass — everything
    else stays black-tie, which is what keeps it from reading as merchandise.
    """
    draw.line([x0, y, x1, y], fill=(118, 96, 26), width=max(1, s))
    mid = (x0 + x1) / 2
    span, step, rise = 96 * s, 19 * s, 6 * s
    cx = mid - span / 2
    while cx <= mid + span / 2 + 1:
        draw.line([cx, y + rise, cx + 7 * s, y - rise],
                  fill=RGB_GOLD, width=max(1, s))
        cx += step


def build_ticket_jpeg(row: pd.Series) -> bytes:
    s = SS
    w, h = TICKET_W * s, TICKET_H * s
    canvas = Image.new("RGB", (w, h), RGB_INK)
    _draw_background(canvas, s)
    _draw_frame(canvas, w, h, s)
    draw = ImageDraw.Draw(canvas)

    stub_x = STUB_X * s
    digest = ticket_digest(row)
    seat_id = str(row["seat_id"])

    # ------------------------------------------------ perforation / tear line
    dash, gap = 13 * s, 11 * s
    y = 44 * s
    while y < h - 44 * s:
        draw.line([stub_x, y, stub_x, min(y + dash, h - 44 * s)],
                  fill=RGB_GOLD, width=max(1, 2 * s))
        y += dash + gap
    r = 15 * s
    for cy in (15 * s, h - 15 * s):
        draw.ellipse([stub_x - r, cy - r, stub_x + r, cy + r],
                     fill=RGB_INK, outline=RGB_GOLD, width=max(1, 2 * s))

    # ---------------------------------------------------- LEFT: the marquee
    lx = 62 * s
    right_edge = stub_x - 52 * s
    avail = right_edge - lx

    draw_tracked(draw, (lx, 46 * s), "OFFICIAL LEAGUE LAUNCH  ·  VIP ENTRY PASS",
                 font("label", 15 * s), RGB_GOLD, tracking=4.6 * s)

    title_font, title_text = fit_text(draw, EVENT_NAME, "title", avail,
                                      76 * s, 34 * s)
    draw_embossed(canvas, (lx, 76 * s), title_text, title_font,
                  glow=9 * s, emboss=3 * s)
    draw = ImageDraw.Draw(canvas)

    sub_font, sub_text = fit_text(draw, EVENT_SUBTITLE, "subtitle", avail,
                                  26 * s, 14 * s)
    draw_tracked(draw, (lx, 166 * s), sub_text, sub_font,
                 (206, 178, 106), tracking=1.5 * s)

    venue_font, venue_text = fit_tracked(draw, VENUE.upper(), "label", avail,
                                         17 * s, 10 * s, 2.2 * s)
    draw_tracked(draw, (lx, 208 * s), venue_text, venue_font, RGB_MUTED,
                 tracking=2.2 * s)

    when = f"{EVENT_DATE.upper()}   ·   {EVENT_TIME.upper()}   ·   GATES OPEN 60 MIN PRIOR"
    when_font, when_text = fit_tracked(draw, when, "label", avail,
                                       16 * s, 10 * s, 2.2 * s)
    draw_tracked(draw, (lx, 234 * s), when_text, when_font, (196, 170, 104),
                 tracking=2.2 * s)

    _draw_seam(draw, lx, right_edge, 268 * s, s)

    col_w = (avail - 40 * s) / 2
    col2 = lx + col_w + 40 * s

    def field(x: float, y_top: float, label: str, value: str, max_w: float) -> None:
        draw_tracked(draw, (x, y_top), label, font("label", 13 * s),
                     RGB_MUTED, tracking=3.4 * s)
        vf, shown = fit_text(draw, value or "—", "strong", max_w, 34 * s, 16 * s)
        ot_text(draw, (x, y_top + 25 * s), shown, vf, RGB_TEXT)

    field(lx, 296 * s, "GUEST NAME", str(row["name"]), col_w)
    field(col2, 296 * s, "ORGANISATION", str(row["organisation"]), col_w)
    field(lx, 380 * s, "WHATSAPP", str(row["phone"]), col_w)
    field(col2, 380 * s, "ISSUED ON",
          str(row["booked_at"] or now_ist()).split(" ")[0], col_w)

    # ---------------------------------------------------- admission badge
    badge = f"COMPLIMENTARY ADMISSION  ·  {value_label()}"
    bf = font("strong", 18 * s)
    bw = text_w(draw, badge, bf, 3.0 * s) + 52 * s
    by, bh = 462 * s, 52 * s
    _draw_gold_rule(canvas, (lx, by, lx + bw, by + bh), bh // 2, max(1, 2 * s))
    draw = ImageDraw.Draw(canvas)
    draw_tracked(draw, (lx + bw / 2, by + bh / 2), badge, bf, (252, 246, 186),
                 tracking=3.0 * s, anchor="mm")

    serial = f"REF {digest[:12].upper()}"
    if lx + bw + 30 * s + text_w(draw, serial, font("label", 13 * s), 3.0 * s) < right_edge:
        draw_tracked(draw, (lx + bw + 30 * s, by + bh / 2), serial,
                     font("label", 13 * s), RGB_MUTED, tracking=3.0 * s, anchor="lm")

    # ---------------------------------------------------- RIGHT: the stub
    sx = stub_x + (w - 15 * s - stub_x) / 2
    stub_w = w - 15 * s - stub_x

    draw_tracked(draw, (sx, 46 * s), "ENTRY PASS", font("label", 16 * s),
                 RGB_MUTED, tracking=7 * s, anchor="ma")

    numeral = seat_number(seat_id)
    hero_font = fit_font(draw, numeral, "hero", stub_w - 74 * s, 118 * s, 52 * s)
    draw_embossed(canvas, (sx, 68 * s), numeral, hero_font, anchor="ma",
                  glow=13 * s, emboss=4 * s)
    draw = ImageDraw.Draw(canvas)

    plate = 250 * s
    py = 200 * s
    _draw_gold_rule(canvas, (sx - plate / 2, py, sx + plate / 2, py + plate),
                    14 * s, max(1, 2 * s))
    draw = ImageDraw.Draw(canvas)
    pad = 8 * s
    draw.rounded_rectangle(
        [sx - plate / 2 + pad, py + pad, sx + plate / 2 - pad, py + plate - pad],
        radius=9 * s, fill=(255, 255, 255))

    bar_w = plate - 16 * s
    draw_security_bars(draw, sx - bar_w / 2, 470 * s, bar_w, 28 * s, digest, s)

    draw_tracked(draw, (sx, 510 * s), "SCAN AT GATE", font("label", 15 * s),
                 RGB_GOLD, tracking=5.4 * s, anchor="ma")
    draw_tracked(draw, (sx, 534 * s), f"{seat_id.upper()}  ·  NON-TRANSFERABLE",
                 font("label", 11 * s), (120, 126, 136), tracking=2.2 * s,
                 anchor="ma")

    # ---------------------------------------------------- render out
    out_w, out_h = round(TICKET_W * OUT_SCALE), round(TICKET_H * OUT_SCALE)
    final = canvas.resize((out_w, out_h), Image.LANCZOS)

    # QR goes on AFTER the downsample at its exact output size. Resampling a QR
    # is what turns crisp modules into grey mush.
    qr_out = round(QR_PX * OUT_SCALE)
    qr = qr_image(gate_payload(seat_id), qr_out)
    cx = sx / s * OUT_SCALE
    cy = (py / s + plate / s / 2) * OUT_SCALE
    final.paste(qr, (round(cx - qr_out / 2), round(cy - qr_out / 2)))

    buf = io.BytesIO()
    # subsampling=0 (4:4:4). JPEG's default 4:2:0 chroma subsampling visibly
    # smears fine gold type and QR edges against a dark ground.
    final.save(buf, "JPEG", quality=JPEG_QUALITY, subsampling=0, optimize=True)
    return buf.getvalue()


def cached_ticket(row: pd.Series) -> bytes:
    store: dict[str, bytes] = st.session_state.setdefault("tickets", {})
    seat = str(row["seat_id"])
    if seat not in store:
        store[seat] = build_ticket_jpeg(row)
    return store[seat]


# =============================================================================
# 6. DATA LAYER  (Google Sheets)
# =============================================================================


def get_conn() -> GSheetsConnection:
    return st.connection("gsheets", type=GSheetsConnection)


def _normalise(df: pd.DataFrame) -> pd.DataFrame:
    """Sheets round-trips are lossy: blanks -> NaN, phones -> '9876543210.0'."""
    df = df.reindex(columns=SCHEMA)
    df = df.astype(object).where(pd.notna(df), "")
    for col in SCHEMA:
        df[col] = (df[col].astype(str).str.strip()
                   .replace({"nan": "", "None": "", "NaT": "", "<NA>": ""}))
    df["phone"] = df["phone"].str.replace(r"\.0$", "", regex=True)
    df = df[df["seat_id"] != ""]
    df["status"] = df["status"].where(df["status"] == BOOKED, AVAILABLE)
    return df.reset_index(drop=True)


def load_seats(*, fresh: bool = False) -> pd.DataFrame:
    raw = get_conn().read(worksheet=WORKSHEET, ttl=0 if fresh else STATS_TTL)
    return _normalise(pd.DataFrame(raw))


def save_seats(df: pd.DataFrame) -> None:
    get_conn().update(worksheet=WORKSHEET, data=df[SCHEMA])
    st.cache_data.clear()


def blank_layout() -> pd.DataFrame:
    return pd.DataFrame([
        {"seat_id": s, "status": AVAILABLE, "name": "", "organisation": "",
         "phone": "", "booked_at": "", "checkin_time": ""}
        for s in SEAT_ORDER
    ])


# =============================================================================
# 7. ALLOCATION ENGINE
# =============================================================================
# Sheets has no transactions, and blind allocation is worse than a seat grid:
# every concurrent user computes the SAME next pass.
#   read(ttl=0) -> write -> read back and confirm OUR phone holds the pass ->
#   retry the next pass if someone beat us.
# Compare-and-verify, not compare-and-swap. Shrinks the window; cannot close it.


def next_free_seat(df: pd.DataFrame) -> str | None:
    free = df[df["status"] == AVAILABLE].copy()
    if free.empty:
        return None
    free["rank"] = free["seat_id"].map(SEAT_RANK)
    free = free.dropna(subset=["rank"]).sort_values("rank")
    return None if free.empty else str(free.iloc[0]["seat_id"])


def existing_pass(df: pd.DataFrame, phone: str) -> pd.Series | None:
    if not ONE_PASS_PER_PHONE:
        return None
    hit = df[(df["phone"] == phone) & (df["status"] == BOOKED)]
    return None if hit.empty else hit.iloc[0]


def allocate_seat(name: str, organisation: str, phone: str
                  ) -> tuple[bool, pd.Series | None, str]:
    for _ in range(ALLOC_ATTEMPTS):
        df = load_seats(fresh=True)
        if df.empty:
            return False, None, "Pass database is empty. Ask the organiser to initialise it."

        already = existing_pass(df, phone)
        if already is not None:
            return True, already, f"This number already holds {already['seat_id']}."

        seat = next_free_seat(df)
        if seat is None:
            return False, None, "All 200 entry passes have been claimed."

        idx = df.index[df["seat_id"] == seat][0]
        df.loc[idx, ["status", "name", "organisation", "phone", "booked_at"]] = [
            BOOKED, name, organisation, phone, now_ist()
        ]
        save_seats(df)

        confirm = load_seats(fresh=True)
        row = confirm[confirm["seat_id"] == seat]
        if not row.empty and row.iloc[0]["phone"] == phone:
            return True, row.iloc[0], f"{seat} confirmed."

    return False, None, (
        "High demand right now — that pass was taken mid-booking. Please submit again."
    )


# =============================================================================
# 8. GATE AUTHENTICATION ENGINE
# =============================================================================
# Verdicts are deliberately few and blunt. A gate operator glancing at a phone
# in the dark needs colour + icon, not prose.

GRANTED: Final[str] = "GRANTED"
DUPLICATE: Final[str] = "DUPLICATE"
NOT_ISSUED: Final[str] = "NOT_ISSUED"
INVALID: Final[str] = "INVALID"
FAILED: Final[str] = "FAILED"


def resolve_scan(raw: str, allow_manual: bool) -> tuple[str | None, str]:
    """
    Returns (seat_id, mode). mode is 'qr', 'manual' or 'bad'.
    A signed payload always wins. A bare number is only honoured when the
    operator has explicitly switched manual entry on — otherwise anybody who
    can guess "Pass-7" walks in.
    """
    seat = verify_payload(raw)
    if seat:
        return seat, "qr"
    if str(raw).strip().upper().startswith("VALIDATE"):
        return None, "bad"                    # looked like a pass, failed HMAC
    if allow_manual:
        manual = normalise_seat(raw)
        if manual:
            return manual, "manual"
    return None, "bad"


def mark_checkin(seat_id: str) -> tuple[str, dict[str, Any]]:
    """
    Stamp checkin_time, or explain why not. Read fresh -> branch -> write ->
    read back and confirm. One Sheets round-trip pair per scan; budget 2-4s.
    """
    try:
        df = load_seats(fresh=True)
    except Exception as exc:                   # noqa: BLE001 — surface at the gate
        return FAILED, {"seat_id": seat_id, "note": f"Sheet unreachable: {exc}"}

    hit = df[df["seat_id"] == seat_id]
    if hit.empty:
        return INVALID, {"seat_id": seat_id, "note": "Pass number is not in the database."}

    row = hit.iloc[0]
    info: dict[str, Any] = {
        "seat_id": seat_id,
        "name": row["name"],
        "organisation": row["organisation"],
        "phone": row["phone"],
        "checkin_time": row["checkin_time"],
        "note": "",
    }

    if row["status"] != BOOKED:
        info["note"] = "Signature is valid but this pass was never issued to a guest."
        return NOT_ISSUED, info

    if str(row["checkin_time"]).strip():
        info["note"] = f"First scanned at {row['checkin_time']}."
        return DUPLICATE, info

    stamp = now_ist()
    idx = hit.index[0]
    df.loc[idx, "checkin_time"] = stamp
    try:
        save_seats(df)
        confirm = load_seats(fresh=True)
        back = confirm[confirm["seat_id"] == seat_id]
        if back.empty or not str(back.iloc[0]["checkin_time"]).strip():
            info["note"] = "Write did not stick. Scan again."
            return FAILED, info
    except Exception as exc:                   # noqa: BLE001
        info["note"] = f"Could not write check-in: {exc}"
        return FAILED, info

    info["checkin_time"] = stamp
    return GRANTED, info


def undo_checkin(seat_id: str) -> tuple[bool, str]:
    """Mis-scans happen. Without this, a wrongly-scanned guest is locked out."""
    try:
        df = load_seats(fresh=True)
        hit = df[df["seat_id"] == seat_id]
        if hit.empty:
            return False, f"{seat_id} not found."
        df.loc[hit.index[0], "checkin_time"] = ""
        save_seats(df)
        return True, f"Check-in cleared for {seat_id}. The guest can scan again."
    except Exception as exc:                   # noqa: BLE001
        return False, f"Could not clear check-in: {exc}"


# =============================================================================
# 9. HTML / CSS INJECTION
# =============================================================================


def _html(markup: str) -> None:
    """
    The ONLY sanctioned injection path.

    Not st.html(): it sanitizes its input and, depending on the Streamlit build,
    drops a <style> block entirely. Nothing errors — the page just renders with
    stock styling, and the #FF4B4B primary button is the tell.

    Three markdown traps this also defuses:
      * a line indented 4+ spaces becomes a CODE BLOCK, printing the stylesheet
        onto the page as literal text;
      * a blank line inside HTML becomes a paragraph break, injecting <p> tags
        into the middle of the markup;
      * a line starting '#' or '-' can parse as a heading or list item.
    Joining with SPACES into one physical line makes all three impossible.
    """
    cleaned = " ".join(line.strip() for line in markup.splitlines() if line.strip())
    st.markdown(cleaned, unsafe_allow_html=True)


def esc(text: Any) -> str:
    """Guest-supplied strings land inside injected HTML. Neutralise them."""
    return (str(text).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))


def inject_theme(intro: bool = False) -> None:
    """
    `intro=True` only on the FIRST script run of a session.

    Streamlit re-executes the whole script on every interaction, so
    unconditional entrance CSS would replay the blackout and the slide-up on
    every keystroke rerun and every form submit. The app would feel broken —
    and at the gate it would blackout the screen on every single scan.
    """
    hold, fade = SPLASH_HOLD, SPLASH_FADE

    if intro:
        stagger = "".join(
            f'[data-testid="stVerticalBlock"] > *:nth-child({i}) '
            f"{{ animation-delay:{REVEAL_BASE + 0.05 * (i - 1):.2f}s; }} "
            for i in range(1, 11)
        )
        reveal = (
            '[data-testid="stVerticalBlock"] > [data-testid="stElementContainer"],'
            '[data-testid="stVerticalBlock"] > .stElementContainer {'
            "animation:vipRise .55s cubic-bezier(.22,1,.36,1) both;"
            f"animation-delay:{REVEAL_BASE:.2f}s; }} " + stagger
        )
    else:
        reveal = ""

    _html(f"""
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;800;900&family=Playfair+Display:wght@500;700;900&display=swap');

    /* ============ GROUND ============ */
    /* Gold from the top-left, Alobha royal blue from the top-right, pitch
       emerald rising from the floor. Three lights, one black room. */
    .stApp, [data-testid="stAppViewContainer"], section.main,
    [data-testid="stMain"] {{ background-color:{OBSIDIAN} !important; }}
    .stApp {{
        background-image:
          radial-gradient(1200px 700px at 4% -14%, rgba(212,175,55,.17), transparent 60%),
          radial-gradient(900px 620px at 99% 2%, rgba(47,107,255,.14), transparent 62%),
          radial-gradient(1100px 620px at 46% 112%, rgba(31,191,117,.12), transparent 64%) !important;
        color:#ECE7DA !important;
    }}
    [data-testid="stHeader"], header[data-testid="stHeader"] {{
        background:transparent !important; }}
    .block-container {{ padding-top:1.2rem; padding-bottom:3.5rem; max-width:880px; }}
    html, body, [class*="css"] {{ font-family:Inter, system-ui, sans-serif; }}
    ::selection {{ background:rgba(212,175,55,.32); }}

    /* ============ GLASS CARDS ============ */
    /* The metal edge is a masked ::before ring, not a border-image. A gradient
       painted via background-clip:border-box bleeds through a translucent
       fill and tints the whole card gold. */
    .glass {{
        position:relative;
        background:rgba(255,255,255,0.03);
        border-radius:22px; padding:1.7rem 1.9rem; margin-bottom:1rem;
        box-shadow:0 24px 60px rgba(0,0,0,.66),
                   inset 0 1px 0 rgba(255,255,255,.07);
        backdrop-filter:blur(18px) saturate(150%);
        -webkit-backdrop-filter:blur(18px) saturate(150%);
    }}
    .glass::before {{
        content:""; position:absolute; inset:0; border-radius:inherit;
        padding:1px; background:{GOLD_CSS}; opacity:.55;
        -webkit-mask:linear-gradient(#000 0 0) content-box, linear-gradient(#000 0 0);
        -webkit-mask-composite:xor; mask:linear-gradient(#000 0 0) content-box,
                                          linear-gradient(#000 0 0);
        mask-composite:exclude; pointer-events:none;
    }}
    .glass--hero::before {{ opacity:.9; animation:vipBreathe 5.6s ease-in-out infinite; }}
    .glass--hero {{ box-shadow:0 24px 60px rgba(0,0,0,.66),
                    inset 0 1px 0 rgba(255,255,255,.07),
                    0 0 46px rgba(212,175,55,.10); }}

    /* ============ TYPE ============ */
    .pill {{
        display:inline-block; padding:.46rem 1.2rem; border-radius:999px;
        font-size:.63rem; font-weight:900; letter-spacing:.3em; color:#12141A;
        background:{GOLD_CSS}; background-size:200% 200%;
        animation:pillsheen 6s ease-in-out infinite, pillglow 3.2s ease-in-out infinite;
    }}
    @keyframes pillsheen {{ 0%,100%{{background-position:0% 50%}}
                            50%{{background-position:100% 50%}} }}
    @keyframes pillglow {{
        0%,100%{{box-shadow:0 0 14px rgba(212,175,55,.38),0 0 32px rgba(212,175,55,.14)}}
        50%    {{box-shadow:0 0 28px rgba(212,175,55,.70),0 0 62px rgba(212,175,55,.28)}}
    }}
    .show-title {{
        font-family:'Playfair Display', Georgia, serif;
        font-size:clamp(2.2rem, 7.6vw, 3.4rem); font-weight:900; line-height:1.02;
        margin:1rem 0 .3rem; letter-spacing:.005em;
        background:{GOLD_CSS};
        -webkit-background-clip:text; background-clip:text;
        -webkit-text-fill-color:transparent;
        filter:drop-shadow(0 6px 26px rgba(212,175,55,.26));
    }}
    .show-sub {{
        font-family:'Playfair Display', Georgia, serif;
        font-size:1.02rem; font-weight:500; font-style:italic;
        letter-spacing:.04em; color:rgba(232,204,107,.9); margin-bottom:.2rem;
    }}
    .micro {{ font-size:.74rem; font-weight:300; letter-spacing:.13em;
              line-height:1.75; color:rgba(236,231,218,.46); }}
    .eyebrow {{ font-size:.58rem; font-weight:800; letter-spacing:.32em;
                text-transform:uppercase; color:rgba(236,231,218,.4); }}

    /* ============ META CHIPS ============ */
    .chips {{ display:flex; flex-wrap:wrap; gap:.5rem; margin-top:1.1rem; }}
    .chip {{
        display:inline-flex; align-items:baseline; gap:.55rem;
        padding:.5rem 1rem; border-radius:12px; font-size:.76rem;
        font-weight:500; letter-spacing:.02em; color:#EFE8D8;
        border:1px solid rgba(212,175,55,.24); background:rgba(212,175,55,.06);
        transition:border-color .2s ease, background .2s ease, transform .12s ease;
    }}
    .chip:hover {{ border-color:rgba(212,175,55,.55);
                   background:rgba(212,175,55,.12); transform:translateY(-1px); }}
    .chip b {{ font-size:.58rem; font-weight:900; letter-spacing:.2em;
               color:{GOLD_SOFT}; text-transform:uppercase; }}
    .chip--map {{ border-color:rgba(47,107,255,.55);
                  background:rgba(47,107,255,.13); }}
    .chip--map b {{ color:#9DB9FF; }}
    a.chip, a.chip:link, a.chip:visited, a.chip:hover {{
        text-decoration:none !important; color:#EFE8D8 !important; }}

    /* ============ ADMISSION ============ */
    .price {{ display:flex; flex-wrap:wrap; gap:2.2rem; align-items:flex-end; }}
    .price-old {{ font-size:1.4rem; font-weight:700; color:{GOLD_SOFT};
                  text-decoration:line-through; opacity:.6;
                  font-variant-numeric:tabular-nums; }}
    .price-new {{ font-size:2.35rem; font-weight:900; color:{EMERALD};
                  text-shadow:0 0 28px rgba(31,191,117,.34);
                  font-variant-numeric:tabular-nums; line-height:1; }}
    .price-tag {{ font-size:.6rem; font-weight:900; letter-spacing:.2em;
                  color:{EMERALD}; }}
    .price-word {{ font-size:1.5rem; font-weight:900; color:{GOLD_SOFT};
                   letter-spacing:.04em; line-height:1.1; }}

    /* ============ TRACKER ============ */
    .trk-rail {{ height:10px; border-radius:999px; overflow:hidden;
                 background:rgba(255,255,255,.05);
                 border:1px solid rgba(212,175,55,.16); }}
    .trk-fill {{ height:100%; border-radius:999px; background:{GOLD_CSS};
                 background-size:220% 100%;
                 box-shadow:0 0 18px rgba(212,175,55,.62); }}
    @keyframes shimmer {{0%{{background-position:0 0}}100%{{background-position:220% 0}}}}
    .num {{ color:{GOLD_SOFT}; font-weight:900;
            font-variant-numeric:tabular-nums; }}

    /* ============ GATE VERDICT ============ */
    /* The one screen that has to read across a dark lobby in half a second.
       Colour first, icon second, words third. */
    .verdict {{ position:relative; border-radius:26px; text-align:center;
                padding:2.1rem 1.3rem 1.8rem; margin:.2rem 0 1rem;
                overflow:hidden; }}
    .verdict__icon {{ font-size:clamp(3rem,13vw,4.6rem); line-height:1;
                      display:block; margin-bottom:.5rem; }}
    .verdict__title {{ font-size:clamp(1.45rem,6.4vw,2.5rem); font-weight:900;
                       letter-spacing:.14em; line-height:1.1; margin:0; }}
    .verdict__seat {{ font-family:'Playfair Display', Georgia, serif;
                      font-size:clamp(2.6rem,12vw,4.2rem); font-weight:900;
                      line-height:1; margin:.6rem 0 .1rem;
                      background:{GOLD_CSS}; -webkit-background-clip:text;
                      background-clip:text; -webkit-text-fill-color:transparent; }}
    .verdict__who {{ font-size:1.02rem; font-weight:700; letter-spacing:.05em;
                     color:#F3EEE0; margin-top:.25rem; }}
    .verdict__meta {{ font-size:.72rem; font-weight:500; letter-spacing:.16em;
                      text-transform:uppercase; color:rgba(236,231,218,.55);
                      margin-top:.5rem; }}
    .verdict--ok {{ border:1px solid rgba(31,191,117,.55);
        background:linear-gradient(180deg, rgba(31,191,117,.16), rgba(31,191,117,.03));
        box-shadow:0 0 60px rgba(31,191,117,.22), inset 0 1px 0 rgba(255,255,255,.08);
        animation:okFlash .5s ease-out both; }}
    .verdict--ok .verdict__title {{ color:{EMERALD}; }}
    .verdict--dupe {{ border:1px solid rgba(255,176,32,.6);
        background:linear-gradient(180deg, rgba(255,176,32,.17), rgba(255,176,32,.03));
        box-shadow:0 0 60px rgba(255,176,32,.24), inset 0 1px 0 rgba(255,255,255,.08);
        animation:dupePulse 1.1s ease-in-out 3; }}
    .verdict--dupe .verdict__title {{ color:{AMBER}; }}
    .verdict--bad {{ border:1px solid rgba(255,77,94,.65);
        background:linear-gradient(180deg, rgba(255,77,94,.18), rgba(255,77,94,.03));
        box-shadow:0 0 60px rgba(255,77,94,.26), inset 0 1px 0 rgba(255,255,255,.08);
        animation:badShake .42s cubic-bezier(.36,.07,.19,.97) both; }}
    .verdict--bad .verdict__title {{ color:{ALERT}; }}
    @keyframes okFlash {{ from {{ transform:scale(.965); opacity:0; }}
                          to {{ transform:none; opacity:1; }} }}
    @keyframes dupePulse {{ 0%,100%{{ box-shadow:0 0 34px rgba(255,176,32,.18) }}
                            50%{{ box-shadow:0 0 78px rgba(255,176,32,.52) }} }}
    @keyframes badShake {{ 10%,90%{{transform:translateX(-3px)}}
                           20%,80%{{transform:translateX(6px)}}
                           30%,50%,70%{{transform:translateX(-10px)}}
                           40%,60%{{transform:translateX(10px)}} }}
    .scanlog {{ font-family:Inter, system-ui, sans-serif; font-size:.76rem;
                letter-spacing:.04em; line-height:2.05; }}
    .scanlog span.t {{ color:rgba(236,231,218,.4);
                       font-variant-numeric:tabular-nums; }}
    .scanlog b.ok {{ color:{EMERALD}; }}
    .scanlog b.dupe {{ color:{AMBER}; }}
    .scanlog b.bad {{ color:{ALERT}; }}

    /* ============ INPUTS ============ */
    /* BaseWeb wraps the <input> in its own bordered container, so the CONTAINER
       must lose its border — styling the <input> alone leaves the grey box
       visible underneath. Every DOM generation is covered. */
    .stTextInput label, .stTextInput label p,
    .stTextInput label div, .stTextInput label span {{
        font-size:0.92rem !important; font-weight:800 !important;
        letter-spacing:.14em !important; text-transform:uppercase !important;
        color:#FFF8E7 !important; opacity:1 !important;
        margin-bottom:.55rem !important;
        text-shadow:0 1px 12px rgba(212,175,55,.35) !important; }}

    .stTextInput > div > div,
    .stTextInput [data-baseweb="input"],
    .stTextInput [data-baseweb="base-input"],
    [data-testid="stTextInputRootElement"] {{
        background-color:rgba(255,255,255,0.08) !important;
        background-image:none !important;
        border:1px solid rgba(212,175,55,.30) !important;
        border-bottom:2px solid rgba(212,175,55,.55) !important;
        border-radius:16px 16px 6px 6px !important;
        box-shadow:inset 0 1px 0 rgba(255,255,255,.12),
                   0 6px 20px -10px rgba(0,0,0,.8) !important;
        backdrop-filter:blur(10px); -webkit-backdrop-filter:blur(10px);
        transition:border-color .2s ease, box-shadow .26s ease,
                   background-color .2s ease;
        overflow:hidden; }}
    .stTextInput > div > div:hover,
    .stTextInput [data-baseweb="input"]:hover {{
        background-color:rgba(255,255,255,0.11) !important;
        border-bottom-color:rgba(212,175,55,.85) !important; }}
    .stTextInput > div > div:focus-within,
    .stTextInput [data-baseweb="input"]:focus-within,
    [data-testid="stTextInputRootElement"]:focus-within {{
        background-color:rgba(255,255,255,0.12) !important;
        border-color:rgba(212,175,55,.5) !important;
        border-bottom-color:{GOLD} !important;
        box-shadow:0 14px 40px -12px rgba(212,175,55,.95),
                   0 3px 0 -1px rgba(212,175,55,.7),
                   inset 0 1px 0 rgba(255,255,255,.18) !important; }}

    .stTextInput input, .stTextInput input[type="text"],
    .stTextInput input[type="password"] {{
        height:78px !important; font-size:1.4rem !important;
        font-weight:600 !important; letter-spacing:.015em !important;
        padding:0 1.45rem !important;
        background:transparent !important; background-color:transparent !important;
        border:none !important; outline:none !important; box-shadow:none !important;
        color:#FFFFFF !important; caret-color:{GOLD} !important;
        -webkit-text-fill-color:#FFFFFF !important; }}
    /* At 1.4rem a faint placeholder reads as a rendering fault, so it is lifted
       to stay clearly legible without competing with real input. */
    .stTextInput input::placeholder {{
        color:rgba(245,240,228,.46) !important; font-weight:400 !important;
        font-size:1.02rem !important; letter-spacing:.04em !important;
        -webkit-text-fill-color:rgba(245,240,228,.46) !important; }}
    .stTextInput [data-baseweb="input"] > div {{ background:transparent !important; }}

    /* ============ CAMERA RELAY ============ */
    /* The camera's landing pad. Pulled off-screen rather than display:none —
       a clipped element still accepts programmatic input events and clicks,
       and Streamlit still commits the form. display:none is riskier: some
       builds skip layout for it and the click never registers. No
       pointer-events:none either; .click() ignores it, but why risk it. */
    .st-key-{RELAY_KEY} {{
        position:absolute !important; left:-10000px !important; top:0 !important;
        width:1px !important; height:1px !important;
        overflow:hidden !important; opacity:0 !important; }}

    /* The viewfinder iframe sits flush; its own gold frame lives inside. */
    .stElementContainer:has(> iframe[title="st.iframe"]) {{ line-height:0; }}
    iframe[title="st.iframe"] {{ border:none !important; background:transparent !important;
        color-scheme:normal; }}

    /* The scanner field is emerald, not gold — the operator must never confuse
       the gate input with a guest form. */
    .st-key-gate_field .stTextInput > div > div,
    .st-key-gate_field [data-baseweb="input"],
    .st-key-gate_field [data-testid="stTextInputRootElement"] {{
        border-color:rgba(31,191,117,.45) !important;
        border-bottom-color:{EMERALD} !important; }}
    .st-key-gate_field input {{ font-family:'Inter', monospace !important;
        letter-spacing:.08em !important; }}

    /* ============ BUTTONS ============ */
    /* Streamlit renames its button hooks between releases and its default
       primary is #FF4B4B, so every generation of selector is covered and
       background-color is nuked explicitly — the `background` shorthand alone
       loses to a later background-color rule in some builds. */
    .stButton > button, .stButton button,
    .stFormSubmitButton > button, .stFormSubmitButton button,
    .stDownloadButton > button, .stDownloadButton button,
    button[kind="primary"], button[kind="secondary"],
    button[kind="primaryFormSubmit"], button[kind="secondaryFormSubmit"],
    [data-testid^="stBaseButton"] {{
        border:1px solid rgba(212,175,55,.42) !important; border-radius:14px !important;
        background-color:rgba(212,175,55,.09) !important; background-image:none !important;
        color:#F2EBD9 !important; font-weight:800 !important;
        letter-spacing:.1em !important; min-height:54px !important;
        box-shadow:none !important;
        transition:transform .1s ease, box-shadow .24s ease,
                   background-color .24s ease; }}

    .stFormSubmitButton > button, .stFormSubmitButton button,
    .stFormSubmitButton button[kind="primaryFormSubmit"],
    .stFormSubmitButton [data-testid^="stBaseButton"] {{
        width:100% !important; min-height:88px !important;
        font-size:1.14rem !important; font-weight:900 !important;
        letter-spacing:.22em !important; border-radius:20px !important;
        border:none !important; color:#12100C !important;
        background-color:{GOLD} !important;
        background-image:{GOLD_CSS} !important; background-size:200% 200%;
        position:relative; overflow:hidden;
        animation:ctapulse 2.6s ease-in-out infinite,
                  ctashift 7s ease-in-out infinite; }}
    .stFormSubmitButton button * {{ color:#12100C !important;
        font-weight:900 !important; letter-spacing:.22em !important; }}
    @keyframes ctashift {{ 0%,100%{{background-position:0% 50%}}
                           50%{{background-position:100% 50%}} }}
    @keyframes ctapulse {{
        0%,100% {{ box-shadow:0 16px 40px -10px rgba(212,175,55,.6),
                              0 0 0 0 rgba(212,175,55,.44),
                              inset 0 1px 0 rgba(255,255,255,.7); }}
        50%     {{ box-shadow:0 20px 54px -8px rgba(212,175,55,.85),
                              0 0 0 18px rgba(212,175,55,0),
                              inset 0 1px 0 rgba(255,255,255,.7); }} }}
    .stFormSubmitButton button::after {{
        content:""; position:absolute; top:0; left:-60%; width:36%; height:100%;
        background:linear-gradient(105deg, transparent,
                                   rgba(255,255,255,.6), transparent);
        transform:skewX(-18deg); animation:sheen 4.4s ease-in-out infinite; }}
    @keyframes sheen {{ 0%{{left:-60%}} 55%{{left:132%}} 100%{{left:132%}} }}
    .stFormSubmitButton button:hover {{ transform:translateY(-2px);
        box-shadow:0 26px 62px -10px rgba(212,175,55,.95) !important; }}
    .stFormSubmitButton button:active {{ transform:translateY(0); }}

    /* The gate submit is a quiet emerald bar. It is pressed by a barcode gun,
       not a person, so it must not throb for gold attention all evening. */
    .st-key-gate_form .stFormSubmitButton button {{
        min-height:62px !important; font-size:.86rem !important;
        letter-spacing:.26em !important; border-radius:16px !important;
        color:#04140C !important;
        background-color:{EMERALD} !important;
        background-image:linear-gradient(135deg,#2FE08D,#0F9B5C) !important;
        animation:none !important;
        box-shadow:0 14px 34px -14px rgba(31,191,117,.9) !important; }}
    .st-key-gate_form .stFormSubmitButton button * {{
        color:#04140C !important; letter-spacing:.26em !important; }}
    .st-key-gate_form .stFormSubmitButton button::after {{ display:none !important; }}

    .stDownloadButton > button, .stDownloadButton button {{
        width:100% !important; min-height:74px !important;
        font-size:1rem !important; font-weight:900 !important;
        letter-spacing:.18em !important; border-radius:18px !important;
        border:1px solid rgba(212,175,55,.5) !important; color:#F7F0DE !important;
        background-color:rgba(212,175,55,.12) !important;
        background-image:linear-gradient(135deg, rgba(212,175,55,.2),
                                         rgba(212,175,55,.04)) !important; }}
    .stDownloadButton button:hover {{ background-image:{GOLD_CSS} !important;
        color:#12100C !important; border-color:transparent !important;
        box-shadow:0 20px 50px -12px rgba(212,175,55,.85) !important; }}
    .stDownloadButton button:hover * {{ color:#12100C !important; }}
    .st-key-reset_db button {{ background-color:#C7222A !important;
        background-image:linear-gradient(135deg,#F0616B,#B91C1C) !important;
        color:#FFF !important; border:none !important; }}
    .st-key-undo_checkin button {{
        background-color:rgba(255,176,32,.12) !important;
        border-color:rgba(255,176,32,.5) !important; color:#FFD98A !important;
        min-height:46px !important; }}

    /* ============ CHROME ============ */
    [data-baseweb="tab-list"] {{ gap:.45rem;
        border-bottom:1px solid rgba(212,175,55,.14) !important; }}
    [data-baseweb="tab"] {{ font-weight:900 !important;
        letter-spacing:.16em !important; font-size:.72rem !important; }}
    [data-baseweb="tab-highlight"] {{ background:{GOLD} !important; height:2px; }}
    [data-testid="stImage"] img {{ border-radius:18px;
        box-shadow:0 30px 80px rgba(0,0,0,.75), 0 0 46px rgba(212,175,55,.14); }}
    [data-testid="stMetricValue"] {{ color:{GOLD_SOFT} !important;
        font-weight:900 !important; font-variant-numeric:tabular-nums; }}
    [data-testid="stMetricLabel"] {{ letter-spacing:.18em !important;
        text-transform:uppercase !important; font-size:.6rem !important; }}
    [data-testid="stDataFrame"] {{ border:1px solid rgba(212,175,55,.22);
        border-radius:14px; overflow:hidden; }}
    hr {{ border-color:rgba(212,175,55,.14) !important; }}

    /* ============ CINEMATIC INTRO ============ */
    /* Simple two-stop keyframes. The hold is expressed as an animation-DELAY
       rather than as percentage stops inside the keyframe — same result, far
       less for the compositor to interpolate, and no mid-timeline jumps. */
    @keyframes vipVeil {{ from {{ opacity:1; }}
                          to   {{ opacity:0; visibility:hidden; }} }}
    @keyframes vipMarkIn {{ from {{ opacity:0; transform:translateY(14px) scale(.972); }}
                            to   {{ opacity:1; transform:none; }} }}
    @keyframes vipRuleIn {{ from {{ width:0; opacity:0; }}
                            to   {{ width:210px; opacity:1; }} }}
    @keyframes vipRise {{ from {{ opacity:0; transform:translateY(16px); }}
                          to   {{ opacity:1; transform:none; }} }}
    @keyframes vipBreathe {{ 0%,100%{{opacity:.5}} 50%{{opacity:1}} }}

    /* THE GLITCH FIX.
       A `position:fixed` element is trapped by ANY ancestor carrying a
       transform, filter or backdrop-filter — that ancestor becomes its
       containing block. The veil is injected inside a Streamlit element
       container, and the reveal animation puts translateY() on those very
       containers, so the veil was being dragged around mid-fade and could sit
       over live controls. Its own container is therefore pinned static. */
    [data-testid="stElementContainer"]:has(.vip-veil),
    .stElementContainer:has(.vip-veil) {{
        animation:none !important; transform:none !important;
        filter:none !important; opacity:1 !important;
        position:static !important; contain:none !important; }}

    /* pointer-events is none on the veil AND every descendant, from the first
       frame — not switched at the end of the animation. An opaque full-screen
       layer that failed to fade would otherwise lock every click in the app. */
    .vip-veil, .vip-veil * {{ pointer-events:none !important; }}
    .vip-veil {{
        position:fixed !important; inset:0; z-index:2147483000;
        display:flex; flex-direction:column; align-items:center;
        justify-content:center; will-change:opacity;
        background:radial-gradient(1000px 640px at 50% 44%,
                    #12161C 0%, #05060B 62%, #000 100%);
        animation:vipVeil {fade:.2f}s cubic-bezier(.4,0,.2,1) {hold:.2f}s forwards; }}
    .vip-veil__mark {{
        font-family:'Playfair Display', Georgia, serif;
        font-size:clamp(1.6rem, 6.4vw, 3.1rem); font-weight:900;
        letter-spacing:.16em; text-align:center; padding:0 1.4rem;
        background:{GOLD_CSS};
        -webkit-background-clip:text; background-clip:text;
        -webkit-text-fill-color:transparent;
        filter:drop-shadow(0 0 30px rgba(212,175,55,.6));
        animation:vipMarkIn .5s cubic-bezier(.22,1,.36,1) both; }}
    .vip-veil__rule {{ height:1px; margin:1.25rem 0 .95rem;
        background:linear-gradient(90deg,transparent,{GOLD},transparent);
        animation:vipRuleIn .6s cubic-bezier(.22,1,.36,1) .08s both; }}
    .vip-veil__sub {{
        font-family:Inter, system-ui, sans-serif; font-size:.58rem;
        font-weight:800; letter-spacing:.44em; color:rgba(232,204,107,.72);
        text-align:center; text-transform:uppercase; padding:0 1.2rem;
        animation:vipMarkIn .5s cubic-bezier(.22,1,.36,1) .12s both; }}
    {reveal}
    /* Accessibility + failsafe. If motion is suppressed nothing may be left at
       opacity:0 — that would render the app permanently blank. */
    @media (prefers-reduced-motion: reduce) {{
        .vip-veil {{ display:none !important; }}
        [data-testid="stVerticalBlock"] > [data-testid="stElementContainer"],
        [data-testid="stVerticalBlock"] > .stElementContainer,
        .glass, .glass--hero, .glass--hero::before, .pill, .trk-live,
        .verdict, .verdict--ok, .verdict--dupe, .verdict--bad,
        .stFormSubmitButton button, .stFormSubmitButton button::after {{
            animation:none !important; opacity:1 !important;
            transform:none !important; }} }}
    @media (max-width: 640px) {{
        .block-container {{ padding-left:.9rem; padding-right:.9rem; }}
        .glass {{ padding:1.25rem 1.1rem; border-radius:18px; }}
        .price {{ gap:1.3rem; }}
        .verdict {{ padding:1.6rem 1rem 1.4rem; }}
    }}
    </style>
    """)


def splash_overlay() -> None:
    """Cinematic veil. Injected ONCE per session — see inject_theme()."""
    _html(f"""
    <div class="vip-veil">
      <div class="vip-veil__mark">{esc(EVENT_NAME.upper())}</div>
      <div class="vip-veil__rule"></div>
      <div class="vip-veil__sub">{esc(EVENT_SUBTITLE)}</div>
    </div>
    """)


def banner(path: Path, fallback: str) -> None:
    if path.exists():
        st.image(str(path), width="stretch")
    else:
        _html(f"<div class='glass' style='text-align:center;letter-spacing:.3em;"
              f"font-weight:900;color:{GOLD_SOFT};'>{esc(fallback)}</div>")


def render_top_branding() -> None:
    """Renders the custom headline & subheadline above the header image."""
    _html(f"""
    <div style="text-align: center; margin-bottom: 1rem; margin-top: 0.5rem;">
        <div class="show-title" style="font-size:clamp(1.8rem, 6vw, 3rem); margin-bottom: 0.2rem; filter:drop-shadow(0 4px 15px rgba(212,175,55,.3));">
            All India gramin Cricket league
        </div>
        <div style="color:{EMERALD}; font-weight: 900; font-size: clamp(1rem, 3vw, 1.4rem); letter-spacing: 0.2em; text-transform: uppercase; text-shadow: 0 0 20px rgba(31,191,117,0.4);">
            Khelo gramin
        </div>
    </div>
    """)


def render_sponsors() -> None:
    """Renders 8 sponsor images in a responsive flex grid."""
    sponsor_paths = [BASE_DIR / f"sponsor{i}.png" for i in range(1, 9)]
    valid_paths = [p for p in sponsor_paths if p.exists()]
    
    if not valid_paths:
        return
        
    _html('<div style="text-align:center; margin-top: 1.5rem; margin-bottom: 1rem;"><span class="eyebrow">OUR SPONSORS</span></div>')
    
    img_tags = []
    for path in valid_paths:
        try:
            with open(path, "rb") as f:
                encoded = base64.b64encode(f.read()).decode("utf-8")
            img_tags.append(
                f'<img src="data:image/png;base64,{encoded}" '
                f'style="flex: 1 1 20%; max-width: 80px; min-width: 50px; object-fit: contain; border-radius: 8px;">'
            )
        except OSError:
            continue
            
    if img_tags:
        _html(f'<div style="display: flex; flex-wrap: wrap; justify-content: center; align-items: center; gap: 10px; width: 100%;">'
              f'{"".join(img_tags)}</div>')


def render_footer_credits() -> None:
    """Renders the final rights reserved statement and contact email."""
    _html(f"""
    <div style="text-align: center; margin-top: 2.5rem; padding-bottom: 1rem;">
        <div style="color:rgba(236,231,218,.4); font-size: .65rem; letter-spacing: .15em; text-transform: uppercase;">
            &copy; {datetime.now(IST).year} All Rights Reserved
        </div>
        <div style="margin-top: 0.4rem;">
            <a href="mailto:mioghub@gmail.com" style="color:{GOLD_SOFT}; font-size: .75rem; text-decoration: none; letter-spacing: .05em; font-weight: 600;">mioghub@gmail.com</a>
        </div>
    </div>
    """)


def hero() -> None:
    # A real anchor, target=_blank, rel=noopener — it must actually open Maps.
    maps_chip = (
        f'<a class="chip chip--map" href="{esc(MAPS_URL)}" target="_blank" '
        f'rel="noopener noreferrer"><b>Map</b><span>Directions &#8599;</span></a>'
        if MAPS_URL else ""
    )
    _html(f"""
    <div class="glass glass--hero">
      <span class="pill">OFFICIAL LEAGUE LAUNCH</span>
      <div class="show-title">{esc(EVENT_NAME)}</div>
      <div class="show-sub">{esc(EVENT_SUBTITLE)}</div>
      <div class="micro">An evening for the league, its teams and its partners
        &middot; strictly by invitation</div>
      <div class="chips">
        <span class="chip"><b>Venue</b><span>{esc(VENUE)}</span></span>
        <span class="chip"><b>Date</b><span>{esc(EVENT_DATE)}</span></span>
        <span class="chip"><b>Time</b><span>{esc(EVENT_TIME)}</span></span>
        {maps_chip}
      </div>
    </div>
    """)


def admission_banner() -> None:
    if value_is_numeric():
        left = (f'<span class="eyebrow">Ticket Value</span><br>'
                f'<span class="price-old">&#8377;{money_text(TICKET_VALUE)}</span>')
    else:
        left = (f'<span class="eyebrow">Admission</span><br>'
                f'<span class="price-word">{esc(str(TICKET_VALUE).upper())}</span>')
    _html(f"""
    <div class="glass" style="padding:1.3rem 1.7rem;">
      <div class="price">
        <div>{left}</div>
        <div><span class="eyebrow">Amount Payable</span><br>
             <span class="price-new">&#8377;0</span>
             &nbsp;<span class="price-tag">COMPLIMENTARY</span></div>
        <div><span class="eyebrow">Gate</span><br>
             <span style="font-weight:900;color:{GOLD_SOFT};font-size:.92rem;
                   letter-spacing:.12em;">QR VERIFIED &middot; ONE ENTRY</span></div>
      </div>
    </div>
    """)


def tracker(booked: int, total: int) -> None:
    pct = (booked / total * 100) if total else 0.0
    _html(f"""
    <style>
    @keyframes fillbar {{ from {{width:0%}} to {{width:{pct:.2f}%}} }}
    .trk-live {{ animation:fillbar 1.2s cubic-bezier(.22,1,.36,1) both,
                           shimmer 2.8s linear infinite; }}
    </style>
    <div class="glass" style="padding:1.3rem 1.6rem;">
      <div style="display:flex;justify-content:space-between;margin-bottom:.75rem;">
        <span class="eyebrow">Live pass tracker</span>
        <span class="eyebrow">{pct:.0f}% claimed</span>
      </div>
      <div class="trk-rail"><div class="trk-fill trk-live"
           style="width:{pct:.2f}%"></div></div>
      <div class="micro" style="margin-top:.75rem;">
        <span class="num">{booked}</span> of <span class="num">{total}</span>
        claimed &nbsp;&middot;&nbsp;
        <span class="num">{max(total - booked, 0)}</span> remaining
      </div>
    </div>
    """)


# =============================================================================
# 10. BROWSER SIDE-EFFECTS  (auto-download, scanner focus, gate tones)
# =============================================================================


def auto_download(jpeg: bytes, filename: str, fire_key: str) -> None:
    """
    Best-effort automatic save. Fired ONCE per issued pass — an ungated version
    would re-trigger on every Streamlit rerun and spam the user's downloads.

    Honest about the limits. Programmatic downloads are actively restricted:
      * st.markdown strips <script>, so this MUST go through components.html,
        which renders in a sandboxed iframe;
      * Chrome blocks downloads from sandboxed iframes lacking allow-downloads,
        so the script first tries window.parent.document to step outside it;
      * browsers require a recent user gesture, and the form submit's gesture
        has usually expired by the time this component mounts;
      * iOS Safari largely ignores the `download` attribute and will open the
        image in a tab instead.
    Net effect: reliable on desktop Chrome/Edge/Firefox, unreliable on mobile
    Safari. The inline image and the download button below it are therefore the
    real delivery path on phones, not a fallback.
    """
    if st.session_state.get("_auto_dl") == fire_key:
        return
    st.session_state["_auto_dl"] = fire_key
    payload = base64.b64encode(jpeg).decode("ascii")
    components_html(
        f"""<script>
(function(){{
  var b64 = "{payload}";
  function bytes() {{
    var s = atob(b64), a = new Uint8Array(s.length);
    for (var i = 0; i < s.length; i++) a[i] = s.charCodeAt(i);
    return a;
  }}
  function save(doc, win) {{
    try {{
      var url = win.URL.createObjectURL(new Blob([bytes()], {{type: "image/jpeg"}}));
      var a = doc.createElement("a");
      a.href = url; a.download = "{filename}"; a.rel = "noopener";
      a.style.display = "none";
      doc.body.appendChild(a); a.click();
      setTimeout(function(){{ doc.body.removeChild(a); win.URL.revokeObjectURL(url); }}, 5000);
      return true;
    }} catch (e) {{ return false; }}
  }}
  var ok = false;
  try {{ ok = save(window.parent.document, window.parent); }} catch (e) {{ ok = false; }}
  if (!ok) save(document, window);
}})();
</script>""",
        height=0,
    )


GATE_TONES: Final[dict[str, str]] = {
    # [frequency Hz, seconds, waveform]
    GRANTED:    '[[880,0.10,"sine"],[1320,0.16,"sine"]]',
    DUPLICATE:  '[[520,0.22,"square"],[400,0.30,"square"]]',
    INVALID:    '[[190,0.42,"sawtooth"]]',
    NOT_ISSUED: '[[190,0.42,"sawtooth"]]',
    FAILED:     '[[300,0.30,"square"]]',
}


def gate_side_effects(verdict: str | None, beep: bool, nonce: str,
                      focus: bool = True) -> None:
    """
    Two gate-only browser tricks in a single iframe:
      1. Re-focus the manual field after a rerun. A hardware gun types into
         whatever has focus; without this the operator must tap the box after
         each scan, which destroys the point of clear_on_submit. Suppressed
         while the camera is live — focusing a text field on a phone throws the
         on-screen keyboard over the viewfinder.
      2. Play a verdict tone. Distinct sounds mean the operator can wave people
         through without looking at the screen.
    Both are best-effort: the iframe may be cross-origin, and browsers gate
    AudioContext behind a user gesture. Silent failure, never an exception.
    """
    tones = GATE_TONES.get(verdict or "", "[]") if beep and verdict else "[]"
    want_focus = "1" if focus else "0"
    components_html(
        f"""<script>
/* nonce {nonce} */
(function(){{
  try {{
    if ("{want_focus}" === "1") {{
      var d = window.parent.document;
      var el = d.querySelector('input[aria-label="SCAN PASS"]')
            || d.querySelector('.st-key-gate_field input');
      if (el) {{ el.focus(); if (el.select) el.select(); }}
    }}
  }} catch (e) {{}}
  try {{
    var seq = {tones};
    if (!seq.length) return;
    var Ctx = window.AudioContext || window.webkitAudioContext;
    if (!Ctx) return;
    var ctx = new Ctx(), t = ctx.currentTime + 0.02;
    seq.forEach(function(n) {{
      var o = ctx.createOscillator(), g = ctx.createGain();
      o.type = n[2] || "sine"; o.frequency.value = n[0];
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(0.30, t + 0.012);
      g.gain.exponentialRampToValueAtTime(0.0001, t + n[1]);
      o.connect(g); g.connect(ctx.destination);
      o.start(t); o.stop(t + n[1] + 0.03);
      t += n[1] + 0.03;
    }});
    setTimeout(function(){{ try {{ ctx.close(); }} catch (e) {{}} }}, 2500);
  }} catch (e) {{}}
}})();
</script>""",
        height=0,
    )


# =============================================================================
# 10b. LIVE CAMERA SCANNER
# =============================================================================
# Three hard browser facts drive this design. None are optional.
#
# 1. getUserMedia needs a SECURE CONTEXT — https:// or localhost, full stop.
#    Opening the app on a phone at http://192.168.x.x:8501 gives a permanently
#    dead camera and a misleading "permission denied". Deploy over https.
#
# 2. components.v1.html renders inside an IFRAME, and an iframe only gets the
#    camera if the parent tags it `allow="camera"`. Streamlit does not. The
#    iframe is same-origin though (its sandbox includes allow-same-origin —
#    the same fact the auto-download hack already relies on), so the document
#    reaches up, writes the attribute onto its OWN iframe element, and
#    re-assigns srcdoc to force one silent reload. A data-attribute guard on
#    the parent element survives that reload and prevents a loop.
#
# 3. components.v1.html is NOT bi-directional. `Streamlit.setComponentValue`
#    exists only for components built with declare_component, which needs a
#    compiled JS bundle — impossible in a single-file app. So the payload is
#    relayed by writing into a real (off-screen) Streamlit text_input using
#    React's native value setter, firing an input event, then clicking that
#    form's submit. Assigning .value directly does nothing: React tracks the
#    internal value node and silently discards the change.
#
# Plus one design fact: a camera re-reads the SAME QR ten times a second.
# Unsuppressed, one guest produces one GRANTED and twenty DUPLICATE alarms —
# which would make the duplicate detection useless exactly when it matters. So
# the scanner freezes the frame on a hit and holds a per-payload cooldown, and
# Python independently ignores a repeat of the same raw string.

CAM_COOLDOWN_MS: Final[int] = 4000
SCAN_COOLDOWN_S: Final[float] = 3.5
RELAY_KEY: Final[str] = "gate_relay"

_CAMERA_HTML = """
<style>
  *{box-sizing:border-box;}
  html,body{margin:0;padding:0;background:transparent;
    font-family:Inter,system-ui,-apple-system,"Segoe UI",sans-serif;
    -webkit-font-smoothing:antialiased;}
  #wrap{display:flex;flex-direction:column;align-items:center;gap:.65rem;}

  /* ---- viewfinder ---- */
  .shell{position:relative;width:100%;max-width:320px;aspect-ratio:1/1;
    border-radius:24px;overflow:hidden;background:#05060B;
    border:1px solid rgba(212,175,55,.45);
    box-shadow:0 22px 54px rgba(0,0,0,.72),inset 0 1px 0 rgba(255,255,255,.06),
               0 0 42px rgba(212,175,55,.12);}
  #reader{position:absolute;inset:0;width:100%;height:100%;}
  #reader video{width:100%!important;height:100%!important;
    object-fit:cover!important;display:block;}
  #reader img{display:none!important;}
  #reader__dashboard{display:none!important;}
  #reader__scan_region{height:100%!important;display:flex!important;
    align-items:center!important;justify-content:center!important;}
  /* html5-qrcode paints its own white scan box — we draw a better one */
  #qr-shaded-region{border:none!important;background:transparent!important;}
  #qr-shaded-region div{background:rgba(0,0,0,.34)!important;}

  /* ---- gold corner reticle ---- */
  .ret{position:absolute;inset:0;pointer-events:none;}
  .ret i{position:absolute;width:36px;height:36px;border:2px solid %%GOLD%%;
    filter:drop-shadow(0 0 6px rgba(212,175,55,.7));}
  .ret i:nth-child(1){top:7%;left:7%;border-right:0;border-bottom:0;
    border-radius:10px 0 0 0;}
  .ret i:nth-child(2){top:7%;right:7%;border-left:0;border-bottom:0;
    border-radius:0 10px 0 0;}
  .ret i:nth-child(3){bottom:7%;left:7%;border-right:0;border-top:0;
    border-radius:0 0 0 10px;}
  .ret i:nth-child(4){bottom:7%;right:7%;border-left:0;border-top:0;
    border-radius:0 0 10px 0;}
  .line{position:absolute;left:9%;right:9%;height:2px;border-radius:2px;
    background:linear-gradient(90deg,transparent,%%EMERALD%%,transparent);
    box-shadow:0 0 14px %%EMERALD%%;animation:sweep 2.4s ease-in-out infinite;}
  @keyframes sweep{0%,100%{top:10%;opacity:.15}50%{top:88%;opacity:1}}
  #shot{display:none;}

  /* ---- status chip ---- */
  .badge{position:absolute;left:50%;bottom:12px;transform:translateX(-50%);
    max-width:88%;padding:.42rem .95rem;border-radius:999px;font-size:.66rem;
    font-weight:800;letter-spacing:.14em;text-transform:uppercase;
    white-space:nowrap;overflow:hidden;text-overflow:ellipsis;
    background:rgba(5,6,11,.86);border:1px solid rgba(212,175,55,.4);
    color:rgba(236,231,218,.82);backdrop-filter:blur(8px);}
  .badge.ok{border-color:%%EMERALD%%;color:%%EMERALD%%;
    box-shadow:0 0 22px rgba(31,191,117,.4);}
  .badge.bad{border-color:%%ALERT%%;color:%%ALERT%%;
    box-shadow:0 0 22px rgba(255,77,94,.34);}
  .badge.warn{border-color:%%AMBER%%;color:%%AMBER%%;}

  /* capture flash */
  .flash{position:absolute;inset:0;background:%%EMERALD%%;opacity:0;
    pointer-events:none;}
  .flash.go{animation:pop .42s ease-out;}
  @keyframes pop{0%{opacity:.55}100%{opacity:0}}

  /* ---- controls ---- */
  .bar{display:flex;gap:.45rem;flex-wrap:wrap;justify-content:center;
    width:100%;max-width:320px;}
  .bar button{flex:1 1 0;min-width:66px;min-height:42px;padding:0 .5rem;
    border-radius:13px;cursor:pointer;font-size:.63rem;font-weight:900;
    letter-spacing:.16em;text-transform:uppercase;
    color:#F2EBD9;background:rgba(212,175,55,.10);
    border:1px solid rgba(212,175,55,.42);
    transition:background .2s ease,border-color .2s ease,transform .1s ease;}
  .bar button:hover{background:rgba(212,175,55,.2);
    border-color:rgba(212,175,55,.75);}
  .bar button:active{transform:translateY(1px);}
  .bar button[disabled]{opacity:.34;cursor:not-allowed;}
  .bar button.live{background:linear-gradient(135deg,#2FE08D,#0F9B5C);
    color:#04140C;border-color:transparent;}
  /* the fallback that always works, so it must not look like an afterthought */
  #b-shot{border-color:rgba(212,175,55,.85);background:rgba(212,175,55,.2);
    color:%%GOLD_SOFT%%;}
  .note{font-size:.6rem;letter-spacing:.1em;line-height:1.6;text-align:center;
    color:rgba(236,231,218,.42);max-width:320px;padding:0 .4rem;}
  .note b{color:%%GOLD_SOFT%%;font-weight:700;}
  .diag{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;
    font-size:.55rem;letter-spacing:.06em;color:rgba(212,175,55,.5);
    text-align:center;max-width:320px;word-break:break-all;}
  @media (prefers-reduced-motion:reduce){.line{animation:none;top:49%;}}
</style>

<div id="wrap">
  <div class="shell">
    <div id="reader"></div>
    <div class="ret"><i></i><i></i><i></i><i></i><div class="line"></div></div>
    <div class="flash" id="flash"></div>
    <div class="badge" id="badge">Preparing camera</div>
  </div>
  <div class="bar">
    <button id="b-start">Start</button>
    <button id="b-flip" disabled>Flip</button>
    <button id="b-torch" disabled>Torch</button>
    <button id="b-shot">Photo</button>
  </div>
  <input type="file" accept="image/*" capture="environment" id="shot">
  <div class="note" id="note">Hold the pass steady inside the frame.</div>
  <div class="diag" id="diag">relay: idle</div>
</div>

<script>
(function () {
  var COOLDOWN = %%COOLDOWN%%;
  var RELAY = "%%RELAY%%";
  var CDNS = [
    "https://unpkg.com/html5-qrcode@2.3.8/html5-qrcode.min.js",
    "https://cdn.jsdelivr.net/npm/html5-qrcode@2.3.8/html5-qrcode.min.js"
  ];

  var badge = document.getElementById("badge");
  var note = document.getElementById("note");
  var flash = document.getElementById("flash");
  var bStart = document.getElementById("b-start");
  var bFlip = document.getElementById("b-flip");
  var bTorch = document.getElementById("b-torch");
  var bShot = document.getElementById("b-shot");

  var qr = null, live = false, facing = "environment";
  var torchOn = false, lastText = "", lastAt = 0;

  function say(text, cls) {
    badge.textContent = text;
    badge.className = "badge " + (cls || "");
  }
  function tell(html) { note.innerHTML = html; }
  /* Names the exact stage that failed. A scanner that silently does nothing is
     undebuggable at a venue; a scanner that says "relay field not found" is a
     two-minute fix. */
  function diag(text) {
    var el = document.getElementById("diag");
    if (el) el.textContent = "relay: " + text;
  }

  /* ---------- 1. give our own iframe the camera permission policy ---------- */
  function ownFrame() {
    try {
      var list = window.parent.document.getElementsByTagName("iframe");
      for (var i = 0; i < list.length; i++) {
        try { if (list[i].contentWindow === window) return list[i]; } catch (e) {}
      }
    } catch (e) {}
    return null;
  }

  function policyReady() {
    var f = ownFrame();
    if (!f) return true;                       /* cross-origin: try regardless */
    var allow = f.getAttribute("allow") || "";
    if (allow.indexOf("camera") !== -1) return true;
    if (f.getAttribute("data-gpl-cam") === "1") return true;   /* patched once */
    f.setAttribute("data-gpl-cam", "1");
    f.setAttribute("allow", "camera;microphone;fullscreen");
    /* the attribute only binds on navigation, so re-run this document once */
    var sd = f.getAttribute("srcdoc");
    if (sd !== null) { f.setAttribute("srcdoc", sd); }
    else { f.setAttribute("src", f.getAttribute("src") || ""); }
    return false;
  }

  /* ---------- 2. hand the payload to Streamlit ----------
     THE SUBTLE PART, and the reason a naive version scans but never verifies.

     Streamlit's text_input inside a form does NOT push each keystroke to its
     widget manager. onChange only marks the component "dirty" and parks the
     text in local React state; the value is committed on blur, on Enter, or
     when the focused field loses focus to the submit button. A programmatic
     .click() blurs nothing — the field was never focused — so submitForm ships
     the PREVIOUS committed value, i.e. the empty string. The scan then arrives
     server-side as "", process_scan() drops it, and the page reruns with no
     verdict at all. Camera fine, decode fine, nothing on screen.

     So the value has to be committed explicitly, three independent ways,
     because which one a given Streamlit build honours varies:
       focus -> native setter -> input/change -> Enter -> blur -> click.
     Any one of those committing is enough; the rest are harmless no-ops. */

  function relayTargets() {
    var W = window.parent, D = W.document;
    return {
      W: W, D: D,
      box: D.querySelector(".st-key-" + RELAY + "_field input")
        || D.querySelector(".st-key-" + RELAY + " input"),
      btn: D.querySelector(".st-key-" + RELAY + " button")
    };
  }

  function writeInto(t, box, payload) {
    var proto = (t.W.HTMLInputElement || HTMLInputElement).prototype;
    var setter = Object.getOwnPropertyDescriptor(proto, "value").set;
    var Ev = t.W.Event || Event;
    var KEv = t.W.KeyboardEvent || KeyboardEvent;

    try { box.focus(); } catch (e) {}
    setter.call(box, payload);
    box.dispatchEvent(new Ev("input", { bubbles: true }));
    box.dispatchEvent(new Ev("change", { bubbles: true }));

    /* Enter commits the value AND submits the form in one go */
    ["keydown", "keypress", "keyup"].forEach(function (type) {
      try {
        box.dispatchEvent(new KEv(type, {
          key: "Enter", code: "Enter", keyCode: 13, which: 13, bubbles: true
        }));
      } catch (e) {}
    });
    /* blur commits on builds that ignore synthetic key events */
    try { box.blur(); } catch (e) {}
  }

  function relay(payload) {
    var t;
    try { t = relayTargets(); }
    catch (e) { diag("parent blocked (cross-origin)"); return false; }

    if (!t.box) { diag("relay field not found"); return false; }
    writeInto(t, t.box, payload);
    diag("committed \\u2192 waiting for Streamlit");

    /* and finally the button, in case neither Enter nor blur committed */
    setTimeout(function () {
      try {
        var again = relayTargets();
        if (again.btn) again.btn.click();
      } catch (e) {}
    }, 110);

    /* Did it land? clear_on_submit empties the field on a successful rerun,
       so an unchanged field means Streamlit never took it. Fall back to the
       visible manual box, which is a completely different DOM path. */
    setTimeout(function () { confirm(payload, 0); }, 900);
    return true;
  }

  function confirm(payload, tries) {
    var t;
    try { t = relayTargets(); } catch (e) { return; }
    if (!t.box || t.box.value !== payload) { diag("delivered"); return; }
    if (tries < 2) {
      writeInto(t, t.box, payload);
      setTimeout(function () {
        try { var a = relayTargets(); if (a.btn) a.btn.click(); } catch (e) {}
      }, 110);
      setTimeout(function () { confirm(payload, tries + 1); }, 900);
      return;
    }
    /* last resort: drive the visible manual override field instead */
    try {
      var D = window.parent.document;
      var mbox = D.querySelector(".st-key-gate_field input");
      var mbtn = D.querySelector(".st-key-gate_form button");
      if (mbox) {
        writeInto({ W: window.parent, D: D }, mbox, payload);
        setTimeout(function () { if (mbtn) mbtn.click(); }, 120);
        diag("used manual field fallback");
        return;
      }
    } catch (e) {}
    diag("Streamlit did not accept the value");
    say("Relay blocked", "bad");
    tell("The scan decoded but the page would not take it. "
       + "Use <b>Manual override</b> and tell the developer: relay-no-commit.");
  }

  /* ---------- 3. a hit ---------- */
  function onHit(text) {
    var now = Date.now();
    if (text === lastText && now - lastAt < COOLDOWN) return;
    lastText = text; lastAt = now;

    flash.classList.remove("go");
    void flash.offsetWidth;
    flash.classList.add("go");

    try { qr.pause(true); } catch (e) {}
    var short = text.length > 30 ? text.slice(0, 30) + "\\u2026" : text;

    if (relay(text)) {
      say("Captured \\u00b7 " + short, "ok");
    } else {
      say("Could not reach the form", "bad");
      tell("The page did not accept the scan. Use <b>Manual override</b> below.");
    }
    setTimeout(function () {
      try { qr.resume(); } catch (e) {}
      if (live) say("Ready \\u00b7 point at a pass", "");
    }, 2200);
  }

  /* ---------- 4. torch ---------- */
  function torchable() {
    try {
      var caps = qr.getRunningTrackCapabilities();
      return !!(caps && "torch" in caps);
    } catch (e) { return false; }
  }
  function setTorch(on) {
    try {
      qr.applyVideoConstraints({ advanced: [{ torch: !!on }] });
      torchOn = !!on;
      bTorch.classList.toggle("live", torchOn);
      return true;
    } catch (e) { return false; }
  }

  /* ---------- 5. start / stop ---------- */
  var frames = 0, lastTick = 0;

  /* html5-qrcode calls this on EVERY frame that contains no code. That makes
     it the proof-of-life for the decode loop: a climbing count means the
     camera and the scanner are both fine and it is purely a framing problem,
     while a stuck count means the loop itself died. Without this the operator
     just sees "relay: idle" forever and has no idea which half is broken. */
  function onScanFail() {
    frames++;
    var now = Date.now();
    if (now - lastTick > 1000) {
      lastTick = now;
      diag("scanning \\u00b7 " + frames + " frames \\u00b7 no code yet");
    }
    /* ~6 seconds of clean frames with nothing decoded is almost always the
       operator holding the pass too close, so the white quiet zone around the
       QR is cropped by the frame edge and the finder patterns cannot be
       located. Coach it rather than sit there silently saying READY. */
    if (frames === 60) {
      tell("Not reading. Move the phone <b>back</b> until the whole QR and its "
         + "white border are inside the view \\u2014 or just tap <b>PHOTO</b>.");
    }
  }

  function start() {
    if (live) return;
    if (!window.isSecureContext) {
      say("HTTPS required", "bad");
      tell("Browsers only allow the camera over <b>https</b> or localhost. "
         + "Open the deployed https link on this phone, or use manual override.");
      return;
    }
    if (!window.Html5Qrcode) { say("Scanner failed to load", "bad"); return; }
    say("Starting camera", "");
    bStart.disabled = true;

    /* NO qrbox — and that is the whole point.
       html5-qrcode CROPS each frame down to qrbox before it even tries to
       decode. A centred 72% box sounds helpful and is actively harmful: hold a
       pass close enough to be sharp and the QR overflows the box, hold it far
       enough to fit and the modules are too small to resolve. Either way the
       decoder never sees a complete code and the scanner appears dead while
       the video looks perfect. Omitting qrbox scans the entire frame, so
       whatever the operator can see is what gets decoded. */
    var cfg = { fps: 10, disableFlip: false,
                useBarCodeDetectorIfSupported: true };
    try {
      qr = new Html5Qrcode("reader", { verbose: false });
    } catch (e) {
      say("Scanner failed to init", "bad"); bStart.disabled = false; return;
    }

    qr.start({ facingMode: facing }, cfg, onHit, onScanFail)
      .then(function () {
        live = true;
        frames = 0;
        bStart.textContent = "Stop";
        bStart.classList.add("live");
        bStart.disabled = false;
        bFlip.disabled = false;
        say("Ready \\u00b7 point at a pass", "");
        tell("Fill about <b>half the frame</b> \\u2014 the whole QR plus a little "
           + "white margin must be visible. If it will not read, tap "
           + "<b>PHOTO</b>.");
        diag("scanning \\u00b7 waiting for a code");
        /* A sharper, larger feed decodes a printed pass from much further out,
           and continuous focus is what makes close-up scans resolve at all.
           Both are best-effort: iOS ignores focusMode, older Android ignores
           the resolution hint, and neither failing matters. */
        try {
          qr.applyVideoConstraints({
            width: { ideal: 1280 }, height: { ideal: 720 },
            advanced: [{ focusMode: "continuous" }]
          });
        } catch (e) {}
        setTimeout(function () {
          if (torchable()) { bTorch.disabled = false; }
        }, 700);
      })
      .catch(function (err) {
        bStart.disabled = false;
        var name = (err && (err.name || err.message)) || "";
        if (/NotAllowed|Permission/i.test(name)) {
          say("Permission denied", "bad");
          tell("Camera access was blocked. Allow it for this site from the "
             + "address bar, then press <b>Start</b>.");
        } else if (/NotFound|Overconstrained|DevicesNotFound/i.test(name)) {
          if (facing === "environment") { facing = "user"; start(); return; }
          say("No camera found", "bad");
          tell("This device reports no usable camera. Use <b>Manual override</b>.");
        } else if (/NotReadable|TrackStart/i.test(name)) {
          say("Camera is busy", "bad");
          tell("Another app is holding the camera. Close it, then press <b>Start</b>.");
        } else {
          say("Camera unavailable", "bad");
          tell("Could not open the camera (" + String(name).slice(0, 60)
             + "). Use <b>Manual override</b>.");
        }
      });
  }

  function stop(cb) {
    if (!qr || !live) { if (cb) cb(); return; }
    live = false;
    if (torchOn) { setTorch(false); }
    qr.stop().then(function () {
      try { qr.clear(); } catch (e) {}
      bStart.textContent = "Start";
      bStart.classList.remove("live");
      bTorch.disabled = true;
      bFlip.disabled = true;
      say("Camera stopped", "warn");
      if (cb) cb();
    }).catch(function () { if (cb) cb(); });
  }

  /* Bind defensively. Every listener below lives in one IIFE, so a single null
     element — a renamed id, a trimmed control — would throw and take the whole
     scanner down with it, camera included. A dead Photo button is survivable;
     a dead scanner at the gate is not. */
  function on(el, ev, fn) {
    if (el && el.addEventListener) { el.addEventListener(ev, fn); }
  }

  on(bStart, "click", function () { live ? stop() : start(); });
  on(bFlip, "click", function () {
    facing = (facing === "environment") ? "user" : "environment";
    stop(function () { setTimeout(start, 220); });
  });
  on(bTorch, "click", function () { setTorch(!torchOn); });

  /* ---------- 5b. photo fallback ----------
     A still photo is captured at the sensor's full resolution rather than the
     downscaled preview stream, and it is sharp rather than motion-blurred, so
     it decodes passes the live loop cannot — a glossy print under a spotlight,
     a dim lobby, a screen with moire. It is the guaranteed path: if this fails
     the QR genuinely is unreadable, and the operator falls back to typing. */
  var shot = document.getElementById("shot");
  on(bShot, "click", function () { if (shot) shot.click(); });
  on(shot, "change", function () {
    var file = shot.files && shot.files[0];
    shot.value = "";
    if (!file) return;
    if (!window.Html5Qrcode) { say("Scanner not loaded", "bad"); return; }
    say("Reading photo", "");
    diag("decoding still image");

    function decode() {
      var inst = qr || new Html5Qrcode("reader", { verbose: false });
      inst.scanFile(file, false)
        .then(function (text) { lastText = ""; onHit(text); })
        .catch(function () {
          say("No QR in that photo", "bad");
          tell("Nothing readable found. Get closer, hold steady, and avoid "
             + "glare on the pass.");
          diag("still image: no code");
        });
    }
    if (live) { stop(decode); } else { decode(); }
  });

  /* release the camera if the tab is hidden or the frame is torn down */
  on(document, "visibilitychange", function () {
    if (document.hidden && live) { stop(); }
  });
  window.addEventListener("pagehide", function () { try { stop(); } catch (e) {} });

  /* ---------- 6. boot ---------- */
  function loadLib(i) {
    if (i >= CDNS.length) {
      say("Scanner failed to load", "bad");
      tell("The scanner library could not be fetched. Check the network, "
         + "or use <b>Manual override</b> below.");
      return;
    }
    var s = document.createElement("script");
    s.src = CDNS[i];
    s.onload = function () { say("Tap Start", ""); start(); };
    s.onerror = function () { loadLib(i + 1); };
    document.head.appendChild(s);
  }

  if (!policyReady()) { say("Preparing camera", ""); return; }
  loadLib(0);
})();
</script>
"""


@lru_cache(maxsize=1)
def camera_html() -> str:
    """
    Byte-identical on every rerun, deliberately. Streamlit only rebuilds a
    components.html iframe when its markup changes — hand it the same string
    and React keeps the existing element, so the camera survives the check-in
    rerun instead of restarting (and re-prompting) after every single guest.
    That is also why nothing dynamic may ever be interpolated in here.
    """
    return (_CAMERA_HTML
            .replace("%%GOLD%%", GOLD)
            .replace("%%GOLD_SOFT%%", GOLD_SOFT)
            .replace("%%EMERALD%%", EMERALD)
            .replace("%%ALERT%%", ALERT)
            .replace("%%AMBER%%", AMBER)
            .replace("%%COOLDOWN%%", str(CAM_COOLDOWN_MS))
            .replace("%%RELAY%%", RELAY_KEY))


CAMERA_OFF_HTML: Final[str] = """
<style>
  html,body{margin:0;padding:0;background:transparent;
    font-family:Inter,system-ui,sans-serif;}
  .off{display:flex;flex-direction:column;align-items:center;
    justify-content:center;height:150px;border-radius:22px;
    border:1px dashed rgba(212,175,55,.34);background:rgba(255,255,255,.02);
    color:rgba(236,231,218,.44);font-size:.64rem;font-weight:800;
    letter-spacing:.2em;text-transform:uppercase;}
  .off span{font-size:1.7rem;margin-bottom:.5rem;filter:grayscale(1);opacity:.6;}
</style>
<div class="off"><span>&#128247;</span>Camera off &middot; manual entry active</div>
"""


# =============================================================================
# 11. CLAIM PAGE
# =============================================================================

NAME_MIN: Final[int] = 3
ORG_MIN: Final[int] = 2
PHONE_RE: Final[re.Pattern[str]] = re.compile(r"^[6-9]\d{9}$")
ISSUED_KEY: Final[str] = "issued_pass"


def validate(name: str, organisation: str, phone: str) -> list[str]:
    errors: list[str] = []
    if len(name) < NAME_MIN:
        errors.append(f"Full name needs at least {NAME_MIN} characters.")
    if len(organisation) < ORG_MIN:
        errors.append(f"Organisation needs at least {ORG_MIN} characters.")
    if not PHONE_RE.match(phone):
        errors.append("WhatsApp number must be exactly 10 digits starting with 6–9.")
    return errors


def render_issued_pass() -> None:
    """
    Confirmation. Auto-save fires once, the pass renders inline for
    long-press-to-save, and a styled download button backs it up.
    Intentionally NO 'claim another pass' action — one pass per number.
    """
    issued = st.session_state.get(ISSUED_KEY)
    if not issued:
        return
    row = pd.Series(issued)
    jpeg = cached_ticket(row)
    seat_id = str(row["seat_id"])
    filename = f"AIGCL_GPL_{seat_id.replace('-', '_')}.jpeg"

    auto_download(jpeg, filename, fire_key=seat_id)

    _html(f"""
    <div class="glass glass--hero" style="text-align:center;">
      <span class="pill">PASS CONFIRMED</span>
      <div class="show-title" style="font-size:clamp(3rem,14vw,4.6rem);
           margin:1.1rem 0 .2rem;">{esc(seat_id)}</div>
      <div class="show-sub">{esc(EVENT_SUBTITLE)}</div>
      <div class="micro">{esc(row['name'])} &nbsp;&middot;&nbsp;
           {esc(row['organisation'])} &nbsp;&middot;&nbsp; {esc(row['phone'])}</div>
    </div>
    """)

    st.image(jpeg, width="stretch")
    _html("""
    <div class="micro" style="text-align:center;margin:-.1rem 0 1rem;">
      Saving automatically. If nothing downloaded, long-press the pass to save it
      to your gallery, or use the button below. Bring the QR to the gate — it is
      scanned once and one entry only.
    </div>
    """)
    st.download_button(
        f"DOWNLOAD ENTRY PASS  ·  {seat_id.upper()}",
        data=jpeg, file_name=filename, mime="image/jpeg",
        width="stretch", key=f"dl_{seat_id}",
    )

    if not fonts_ready():
        st.warning(
            "No TrueType font was available, so the pass used a bitmap face and "
            "will look coarse. Drop a .ttf into `assets/`.", icon="🔤")
    ppm = qr_px_per_module(gate_payload(seat_id))
    if ppm < 4.0:
        st.warning(
            f"QR is dense ({ppm:.1f}px per module) and may not scan reliably.",
            icon="📷")


def render_claim(df: pd.DataFrame) -> None:
    booked = int((df["status"] == BOOKED).sum())
    remaining = max(TOTAL_SEATS - booked, 0)

    hero()
    admission_banner()
    tracker(booked, TOTAL_SEATS)

    if st.session_state.get(ISSUED_KEY):
        render_issued_pass()
        return

    if remaining == 0:
        st.error("All 200 entry passes have been claimed.", icon="🏏")
        return

    _html("""
    <div class="glass" style="padding-bottom:.7rem;">
      <span class="pill">CLAIM YOUR PASS</span>
      <div class="micro" style="margin-top:1.05rem;">
        Three fields. Your pass number is allocated automatically from the front
        of the block &mdash; one pass per WhatsApp number.
      </div>
    </div>
    """)

    with st.form("claim_pass", border=False):
        name = st.text_input("Full Name", max_chars=60,
                             placeholder="Exactly as printed on your ID")
        organisation = st.text_input("Organisation / Team", max_chars=60,
                                     placeholder="Company, franchise or club")
        phone = st.text_input("WhatsApp Number", max_chars=10,
                              placeholder="10 digits, starting 6–9")
        submitted = st.form_submit_button("CLAIM ENTRY PASS", type="primary")

    if not submitted:
        return

    name, organisation, phone = name.strip(), organisation.strip(), phone.strip()
    errors = validate(name, organisation, phone)
    if errors:
        for message in errors:
            st.error(message, icon="⚠️")
        return

    with st.spinner("Allocating your pass and pressing the ticket…"):
        ok, row, message = allocate_seat(name, organisation, phone)

    if not ok or row is None:
        st.error(message, icon="🚫")
        return

    st.session_state[ISSUED_KEY] = row.to_dict()
    st.balloons()
    st.rerun()


# =============================================================================
# 12. ADMIN  —  gate scanner, guest list, database
# =============================================================================

SCAN_RESULT: Final[str] = "gate_result"
SCAN_LOG: Final[str] = "gate_log"
LAST_GRANTED: Final[str] = "gate_last_granted"


def admin_login() -> bool:
    if st.session_state.get("is_admin"):
        return True
    _html("""
    <div class="glass"><span class="pill">RESTRICTED</span>
      <div class="micro" style="margin-top:1.05rem;">Organiser and gate staff only.</div>
    </div>
    """)
    with st.form("admin_login", border=False):
        pwd = st.text_input("Admin password", type="password")
        if st.form_submit_button("UNLOCK", type="primary"):
            secret = str(cfg("admin_password", ""))
            if pwd and secret and hmac.compare_digest(pwd, secret):
                st.session_state["is_admin"] = True
                st.rerun()
            else:
                st.error("Incorrect password.", icon="🔒")
    return False


VERDICT_SKIN: Final[dict[str, tuple[str, str, str]]] = {
    #                 css-modifier, icon, headline
    GRANTED:    ("ok",   "✅", "AUTHENTICATED &middot; ENTRY GRANTED"),
    DUPLICATE:  ("dupe", "❌", "DUPLICATE ENTRY &middot; ALREADY SCANNED"),
    NOT_ISSUED: ("bad",  "🚫", "PASS NOT ISSUED"),
    INVALID:    ("bad",  "🚫", "INVALID PASS"),
    FAILED:     ("bad",  "⚠️", "CHECK-IN FAILED"),
}


def render_verdict(result: dict[str, Any]) -> None:
    verdict = result.get("verdict", INVALID)
    skin, icon, headline = VERDICT_SKIN.get(verdict, VERDICT_SKIN[INVALID])
    seat = result.get("seat_id") or ""
    name = result.get("name") or ""
    org = result.get("organisation") or ""
    note = result.get("note") or ""
    stamp = result.get("checkin_time") or ""

    seat_block = f'<div class="verdict__seat">{esc(seat)}</div>' if seat else ""
    who = ""
    if name:
        who = f'<div class="verdict__who">{esc(name)}'
        if org:
            who += f' &middot; <span style="font-weight:500;opacity:.75;">{esc(org)}</span>'
        who += "</div>"

    meta_bits = []
    if verdict == GRANTED and stamp:
        meta_bits.append(f"Checked in {esc(stamp)}")
    if note:
        meta_bits.append(esc(note))
    if result.get("mode") == "manual":
        meta_bits.append("Manual entry — QR not verified")
    meta = (f'<div class="verdict__meta">{" &nbsp;·&nbsp; ".join(meta_bits)}</div>'
            if meta_bits else "")

    _html(f"""
    <div class="verdict verdict--{skin}">
      <span class="verdict__icon">{icon}</span>
      <div class="verdict__title">{headline}</div>
      {seat_block}{who}{meta}
    </div>
    """)


def push_log(verdict: str, seat: str, name: str) -> None:
    log: list[dict[str, str]] = st.session_state.setdefault(SCAN_LOG, [])
    skin = VERDICT_SKIN.get(verdict, VERDICT_SKIN[INVALID])[0]
    log.insert(0, {"t": clock_ist(), "skin": skin, "verdict": verdict,
                   "seat": seat or "—", "name": name or ""})
    del log[24:]


def render_log() -> None:
    log: list[dict[str, str]] = st.session_state.get(SCAN_LOG, [])
    if not log:
        return
    label = {GRANTED: "IN", DUPLICATE: "DUPE", NOT_ISSUED: "UNISSUED",
             INVALID: "INVALID", FAILED: "ERROR"}
    rows = "".join(
        f'<div><span class="t">{esc(e["t"])}</span> &nbsp; '
        f'<b class="{e["skin"]}">{label.get(e["verdict"], "?")}</b> &nbsp; '
        f'{esc(e["seat"])}'
        + (f' &nbsp;<span class="t">{esc(e["name"])}</span>' if e["name"] else "")
        + "</div>"
        for e in log[:12]
    )
    _html(f"""
    <div class="glass" style="padding:1.1rem 1.5rem;">
      <span class="eyebrow">Recent scans &middot; this device</span>
      <div class="scanlog" style="margin-top:.6rem;">{rows}</div>
    </div>
    """)


def salt_fingerprint() -> str:
    """
    A short, non-reversible tag for the active salt. Never reveals the salt, but
    lets you tell at a glance whether it changed since the passes were printed —
    which is the other way a perfectly good QR reads INVALID at the gate.
    """
    return hashlib.sha256(("fingerprint|" + SECURITY_SALT).encode("utf-8")
                          ).hexdigest()[:8].upper()


def explain_payload(raw: str) -> list[tuple[str, bool, str]]:
    """
    Step-by-step account of why a scanned string was accepted or rejected.
    Returns (step, passed, detail). This exists because "invalid pass" on its
    own is useless at 6pm with a queue building — the operator needs to know
    whether it is a fake, a smudged scan, or a salt that changed after printing.
    """
    steps: list[tuple[str, bool, str]] = []
    raw = (raw or "").strip()

    steps.append(("Something arrived at the server", bool(raw),
                  f"{len(raw)} characters"))
    if not raw:
        steps.append(("Diagnosis", False,
                      "The field reached the server empty. The camera decoded "
                      "but the value was not committed — a relay problem, not "
                      "a pass problem."))
        return steps

    match = SCAN_RE.match(raw)
    steps.append(("Matches VALIDATE|pass|signature", bool(match),
                  "" if match else "Not a payload this app prints."))
    if not match:
        bare = normalise_seat(raw)
        steps.append(("Looks like a bare pass number", bare is not None,
                      bare or "no"))
        steps.append(("Diagnosis", False,
                      "Accepted only with 'Manual no.' switched on, since "
                      "nothing about a bare number can be verified."
                      if bare else
                      "This QR was not produced by this system."))
        return steps

    seat = normalise_seat(match.group(1))
    steps.append((f"Pass number within 1–{TOTAL_PASSES}", seat is not None,
                  seat or match.group(1)))
    if seat is None:
        return steps

    expected = security_hash(seat)
    carried = match.group(2).upper()
    ok = hmac.compare_digest(expected, carried)
    steps.append(("Signature matches the current security_salt", ok,
                  f"pass carries {carried} · this salt produces {expected}"))
    if not ok:
        steps.append(("Diagnosis", False,
                      "The pass is well-formed but signed with a DIFFERENT "
                      "salt. Almost always this means `security_salt` was "
                      "changed after these passes were issued. Restore the "
                      "old salt, or reset the database and re-issue."))
    else:
        steps.append(("Diagnosis", True,
                      "Signature is valid. Any rejection now comes from the "
                      "sheet: unissued pass, or already checked in."))
    return steps


LAST_SEEN: Final[str] = "gate_last_seen"


def note_arrival(raw: str, source: str) -> None:
    """Record what actually reached the server, empty strings included."""
    st.session_state[LAST_SEEN] = {
        "raw": raw or "", "source": source, "at": clock_ist(),
    }


def reload_seats(fallback: pd.DataFrame) -> pd.DataFrame:
    """
    Re-read after the gate may have written.

    main() loads the sheet once, at the top, and hands that frame to every tab.
    But the gate tab renders FIRST and writes a check-in during that same run,
    so the guest list and the counters further down were rendering data from
    before the write — a check-in that had genuinely been saved still showed as
    "not arrived" until the next interaction. Reads are cached for STATS_TTL and
    save_seats() clears that cache, so this is free when nothing changed and
    correct when something did.
    """
    try:
        return load_seats()
    except Exception:                        # noqa: BLE001 — keep the tab alive
        return fallback


LAST_RAW: Final[str] = "gate_last_raw"


def process_scan(raw: str, allow_manual: bool, source: str) -> str | None:
    """
    Single authentication path. The camera and the manual box both land here,
    so a payload cannot take a shortcut around the signature check.

    Returns the verdict for the audio cue, or None when the scan was swallowed
    as a repeat. Burst suppression is the important bit: a camera re-reads the
    same QR many times a second, and without this the operator would get one
    GRANTED followed by a wall of DUPLICATE alarms for a guest who did nothing
    wrong. Suppressing here also spares Google Sheets a write per frame.
    """
    raw = (raw or "").strip()
    if not raw:
        return None

    previous = st.session_state.get(LAST_RAW)
    now = time.monotonic()
    if previous and previous[0] == raw and now - previous[1] < SCAN_COOLDOWN_S:
        st.session_state[LAST_RAW] = (raw, now)
        return None                      # same code, still on screen — ignore
    st.session_state[LAST_RAW] = (raw, now)

    # A camera decodes QR codes; it cannot produce a bare "42". Enforcing that
    # here rather than trusting the caller's flag means a future edit to the
    # gate UI cannot accidentally turn the viewfinder into an unsigned-entry
    # path — the invariant lives with the check, not with the convention.
    if source == "camera":
        allow_manual = False

    seat, mode = resolve_scan(raw, allow_manual)
    if seat is None:
        result: dict[str, Any] = {
            "verdict": INVALID, "seat_id": "", "mode": mode, "source": source,
            "note": "Signature did not verify. This is not a pass issued by "
                    "this system.",
        }
        push_log(INVALID, "", "")
    else:
        with st.spinner(f"Verifying {seat}…"):
            verdict, info = mark_checkin(seat)
        result = {"verdict": verdict, "mode": mode, "source": source, **info}
        push_log(verdict, seat, str(info.get("name", "")))
        if verdict == GRANTED:
            st.session_state[LAST_GRANTED] = seat

    st.session_state[SCAN_RESULT] = result
    return str(result["verdict"])


def render_gate(df: pd.DataFrame) -> None:
    # Counters are deliberately NOT computed here. A check-in written further
    # down this function would make them stale on the very run that mattered,
    # so they are read fresh in step 8 instead.

    # ELEMENT ORDER MATTERS ABOVE THE CAMERA.
    # Streamlit reconciles components by position. If the number of elements
    # before the camera iframe changed between runs, React would rebuild the
    # iframe and the camera would restart after every guest. So positions 1-2
    # are unconditional, and every conditional block lives further down.

    # -- 1. header (always rendered) ------------------------------------------
    _html(f"""
    <div class="glass" style="padding:1.2rem 1.5rem;">
      <span class="pill">GATE SCANNER</span>
      <div class="micro" style="margin-top:1rem;">
        Point the phone at a guest's QR &mdash; check-in is automatic, no button
        to press. Run the gate from <b style="color:{GOLD_SOFT};">one device
        only</b>: Google Sheets has no row locking, so two phones writing in the
        same second will overwrite each other.
      </div>
    </div>
    """)

    # -- 2. controls (always rendered, so the camera's index never moves) -----
    opt_a, opt_b, opt_c = st.columns(3)
    camera_on = opt_a.toggle("Camera", value=True, key="gate_camera",
                             help="Live rear-camera scanning. Turn off to save "
                                  "battery or when using a hardware gun.")
    beep = opt_b.toggle("Sound", value=True, key="gate_beep",
                        help="Distinct tone per verdict. Browsers may block "
                             "audio until you tap the page once.")
    allow_manual = opt_c.toggle("Manual no.", value=False, key="gate_manual",
                                help="Lets you type '42' when a QR is damaged. "
                                     "No signature is checked, so keep it off "
                                     "unless you need it.")

    # -- 3. the camera -------------------------------------------------------
    if camera_on:
        components_html(camera_html(), height=520, scrolling=False)
    else:
        components_html(CAMERA_OFF_HTML, height=170, scrolling=False)

    # -- 4. relay: where the camera drops its payload ------------------------
    # Off-screen, not display:none — a clipped element still takes programmatic
    # input events and clicks, and Streamlit still commits the form.
    with st.container(key=RELAY_KEY):
        with st.form("gate_relay_form", clear_on_submit=True, border=False):
            cam_raw = st.text_input("Camera relay", key=f"{RELAY_KEY}_field",
                                    label_visibility="collapsed")
            cam_submitted = st.form_submit_button("relay")

    # -- 5. manual override --------------------------------------------------
    with st.container(key="gate_form"):
        with st.form("gate_scan", clear_on_submit=True, border=False):
            raw = st.text_input(
                "SCAN PASS", key="gate_field",
                placeholder="VALIDATE|Pass-1|A1B2C3D4E5",
                help="Backup path: paste a payload, type a pass number with "
                     "manual mode on, or fire a hardware scanner into it.",
            )
            scanned = st.form_submit_button("CHECK IN MANUALLY", type="primary")

    # -- 6. authenticate -----------------------------------------------------
    verdict_for_tone: str | None = None
    if cam_submitted:
        note_arrival(cam_raw, "camera")
        # A camera only ever produces a signed payload, so manual bare numbers
        # are never honoured on this path regardless of the toggle.
        verdict_for_tone = process_scan(cam_raw, False, "camera")
    elif scanned:
        note_arrival(raw, "manual")
        if not (raw or "").strip():
            st.session_state[SCAN_RESULT] = None
        else:
            verdict_for_tone = process_scan(raw, allow_manual, "manual")

    # -- 7. verdict ----------------------------------------------------------
    result = st.session_state.get(SCAN_RESULT)
    if result:
        render_verdict(result)
        if result.get("verdict") == GRANTED and \
                st.session_state.get(LAST_GRANTED) == result.get("seat_id"):
            if st.button(f"Undo check-in for {result['seat_id']}",
                         key="undo_checkin", width="stretch"):
                ok, message = undo_checkin(str(result["seat_id"]))
                st.session_state[SCAN_RESULT] = None
                st.session_state.pop(LAST_GRANTED, None)
                st.session_state.pop(LAST_RAW, None)
                (st.success if ok else st.error)(message)
                st.rerun()
    else:
        _html("""
        <div class="glass" style="text-align:center;padding:2rem 1.4rem;">
          <div style="font-size:2.6rem;line-height:1;">🎟️</div>
          <div class="micro" style="margin-top:.8rem;">
            Ready. The verdict appears here and stays until the next pass.
          </div>
        </div>
        """)

    # -- 8. counters, warnings, log (conditional blocks live below the camera)
    # Re-read: a check-in was very likely just written a few lines above, and
    # the frame main() handed us predates it.
    df = reload_seats(df)
    issued = int((df["status"] == BOOKED).sum())
    arrived = int(((df["status"] == BOOKED) &
                   (df["checkin_time"].astype(str).str.strip() != "")).sum())

    a, b, c = st.columns(3)
    a.metric("Passes issued", issued)
    b.metric("Checked in", arrived)
    c.metric("Yet to arrive", max(issued - arrived, 0))

    if SALT_IS_DEFAULT:
        st.error(
            "`security_salt` is still the default value in the code. Every QR "
            "signature on every pass is forgeable by anyone who has read this "
            "repository. Set a long random `security_salt` under `[app]` in "
            "secrets.toml, then re-issue passes before the event.", icon="🔓")

    render_log()

    # -- 9. diagnostics ------------------------------------------------------
    # Turns "it scans but nothing happens" into a one-line answer: either
    # nothing reached the server (relay problem) or something did and the
    # signature failed (salt problem).
    with st.expander("Scan diagnostics"):
        seen = st.session_state.get(LAST_SEEN)
        if not seen:
            st.caption(
                "Nothing has reached the server yet. If the viewfinder shows "
                "CAPTURED but this stays empty, the payload is not being "
                "committed — check the small `relay:` line under the camera."
            )
        else:
            st.caption(f"Last value received · {seen['at']} · via {seen['source']}")
            st.code(seen["raw"] or "(empty string)", language="text")
            for step, ok, detail in explain_payload(seen["raw"]):
                st.markdown(f"{'✅' if ok else '❌'} **{step}**"
                            + (f" — {detail}" if detail else ""))
        st.caption(f"Active salt fingerprint: `{salt_fingerprint()}` — if this "
                   "changed since the passes were printed, every QR will read "
                   "as invalid.")

    # Focusing the manual box pops the on-screen keyboard over the viewfinder,
    # so it is only done when the camera is off.
    gate_side_effects(
        verdict_for_tone, beep, focus=not camera_on,
        nonce=f"{clock_ist()}-{len(st.session_state.get(SCAN_LOG, []))}",
    )


def guest_table(df: pd.DataFrame) -> pd.DataFrame:
    booked = df[df["status"] == BOOKED].copy()
    if booked.empty:
        return booked
    booked["rank"] = booked["seat_id"].map(SEAT_RANK)
    booked = booked.sort_values("rank", na_position="last")
    booked["arrived"] = booked["checkin_time"].astype(str).str.strip().ne("").map(
        {True: "✅ In", False: "—"})
    return booked[["seat_id", "name", "organisation", "phone", "booked_at",
                   "arrived", "checkin_time"]].rename(
        columns={"seat_id": "Pass", "name": "Name",
                 "organisation": "Organisation", "phone": "Phone",
                 "booked_at": "Issued", "arrived": "Status",
                 "checkin_time": "Checked in"})


def render_guest_list(df: pd.DataFrame) -> None:
    issued = int((df["status"] == BOOKED).sum())
    arrived = int(((df["status"] == BOOKED) &
                   (df["checkin_time"].astype(str).str.strip() != "")).sum())
    a, b, c, d = st.columns(4)
    a.metric("Passes in sheet", len(df))
    b.metric("Issued", issued)
    c.metric("Checked in", arrived)
    d.metric("Unclaimed", max(len(df) - issued, 0))

    _html('<div class="glass" style="padding:1rem 1.4rem;">'
          '<span class="pill">GUEST LIST</span></div>')

    table = guest_table(df)
    if table.empty:
        st.info("No passes claimed yet.", icon="🎫")
        return

    view = st.radio("Filter", ["All", "Checked in", "Not arrived"],
                    horizontal=True, label_visibility="collapsed")
    if view == "Checked in":
        table = table[table["Status"] != "—"]
    elif view == "Not arrived":
        table = table[table["Status"] == "—"]

    st.caption(f"{len(table)} shown · allocation order "
               f"({SEAT_ORDER[0]} → {SEAT_ORDER[-1]}). "
               "Use the table toolbar to search or export CSV.")
    st.dataframe(table, hide_index=True, width="stretch")


def render_database(df: pd.DataFrame) -> None:
    _html(f"""
    <div class="glass" style="padding:1.2rem 1.5rem;">
      <span class="pill">DATABASE</span>
      <div class="micro" style="margin-top:1rem;">
        Worksheet <b style="color:{GOLD_SOFT};">{esc(WORKSHEET)}</b> &middot;
        columns: {esc(", ".join(SCHEMA))}
      </div>
    </div>
    """)

    st.subheader("Clear a check-in", divider=False)
    st.caption("For mis-scans. Clearing lets that guest scan again.")
    fix_a, fix_b = st.columns([3, 2])
    target = fix_a.text_input("Pass number", placeholder="e.g. 42 or Pass-42",
                              key="fix_seat", label_visibility="collapsed")
    if fix_b.button("CLEAR CHECK-IN", width="stretch"):
        seat = normalise_seat(target or "")
        if seat is None:
            st.error(f"Enter a pass number between 1 and {TOTAL_PASSES}.", icon="⚠️")
        else:
            ok, message = undo_checkin(seat)
            (st.success if ok else st.error)(message)
            st.rerun()

    st.divider()
    st.warning(
        f"Resetting wipes every issued pass AND every check-in, then re-seeds "
        f"all {TOTAL_PASSES} passes ({SEAT_ORDER[0]} → {SEAT_ORDER[-1]}) as "
        f"Available.\n\nNot reversible.", icon="⚠️")
    confirmed = st.checkbox("I understand this deletes all existing passes and check-ins")
    if st.button(f"RESET DATABASE  ·  {TOTAL_PASSES} PASSES",
                 key="reset_db", disabled=not confirmed, width="stretch"):
        with st.spinner("Re-seeding the sheet…"):
            save_seats(blank_layout())
        for key in ("tickets", ISSUED_KEY, "_auto_dl", SCAN_RESULT,
                    SCAN_LOG, LAST_GRANTED):
            st.session_state.pop(key, None)
        st.success(f"Database reset. {TOTAL_PASSES} passes initialised.", icon="✅")
        st.rerun()

    st.divider()
    st.subheader("Scan doctor", divider=False)
    st.caption("Paste any scanned payload to see exactly why it passes or fails. "
               "Use it to test the scanner before doors open.")
    probe = st.text_input("Payload", key="doctor_payload",
                          placeholder="VALIDATE|Pass-1|A1B2C3D4E5",
                          label_visibility="collapsed")
    if probe.strip():
        for step, ok, detail in explain_payload(probe):
            st.markdown(f"{'✅' if ok else '❌'} **{step}**"
                        + (f" — {detail}" if detail else ""))

    st.divider()
    st.caption("Signature self-test — these are the exact payloads encoded into "
               "the first three QRs. Scan a real pass and compare.")
    st.code("\n".join(gate_payload(s) for s in SEAT_ORDER[:3]), language="text")
    st.caption(f"Active salt fingerprint: `{salt_fingerprint()}`")


def render_admin(df: pd.DataFrame) -> None:
    gate_tab, list_tab, db_tab = st.tabs(
        ["🎟️ GATE SCANNER", "📋 GUEST LIST", "⚙️ DATABASE"])
    with gate_tab:
        render_gate(df)
    with list_tab:
        # The gate tab rendered first and may have just written a check-in.
        render_guest_list(reload_seats(df))
    with db_tab:
        render_database(reload_seats(df))


# =============================================================================
# 13. ENTRY POINT
# =============================================================================


def main() -> None:
    st.set_page_config(page_title=f"{EVENT_NAME} — VIP Entry Pass",
                       page_icon="🏏", layout="centered")

    # First script run of this browser session only. Streamlit re-executes the
    # whole script on every interaction, so an ungated intro would blackout the
    # screen again on every form submit — including every single gate scan.
    intro = not st.session_state.get("_intro_played", False)
    st.session_state["_intro_played"] = True

    inject_theme(intro=intro)
    if intro:
        splash_overlay()

    render_top_branding()
    banner(HEADER_IMG, EVENT_NAME.upper())

    try:
        df = load_seats()
    except Exception as exc:  # noqa: BLE001 — surface config errors to the operator
        st.error(f"Could not read the Google Sheet: {exc}", icon="🔌")
        banner(FOOTER_IMG, VENUE.upper())
        st.stop()
        return

    if df.empty:
        st.warning("Pass database is empty. Open Admin → Database and reset it "
                   f"to seed {TOTAL_PASSES} passes.", icon="🗄️")

    claim_tab, admin_tab = st.tabs(["CLAIM ENTRY PASS", "ADMIN"])
    with claim_tab:
        render_claim(df)
    with admin_tab:
        if admin_login():
            render_admin(df)

    st.divider()
    banner(FOOTER_IMG, VENUE.upper())
    render_sponsors()
    render_footer_credits()


if __name__ == "__main__":
    main()
