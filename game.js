// ============================================================
// POLAR BATTLESHIP - Canvas/JS port
// ============================================================

// ---------- Angles ----------
// Generate all special angles: multiples of pi/6, pi/4, pi/3, pi/2 in [0, 2pi)
function gcd(a, b) { return b ? gcd(b, a % b) : a; }
function makeFraction(num, den) {
  const g = gcd(Math.abs(num), den);
  return { num: num / g, den: den / g };
}
function fracEqual(a, b) { return a.num === b.num && a.den === b.den; }
function fracKey(f) { return `${f.num}/${f.den}`; }
function fracValue(f) { return f.num / f.den; }

const angleFractionMap = new Map();
[6, 4, 3, 2].forEach(denom => {
  for (let k = 0; k < 2 * denom; k++) {
    const f = makeFraction(k, denom);
    angleFractionMap.set(fracKey(f), f);
  }
});
const angleFractions = [...angleFractionMap.values()].sort(
  (a, b) => fracValue(a) - fracValue(b)
);
const specialAngles = angleFractions.map(f => fracValue(f) * Math.PI);
const N_ANG = specialAngles.length;

function piLabel(frac) {
  if (frac.num === 0) return '0';
  const numStr = frac.num === 1 ? 'π' : `${frac.num}π`;
  return frac.den === 1 ? numStr : `${numStr}/${frac.den}`;
}

// ---------- Constants ----------
const R_MAX = 5;
const R_MIN = 0;
const SHIP_SIZES = [2, 3, 4];
const SHIP_NAMES = ['DESTROYER', 'BATTLESHIP', 'CARRIER'];
const SHIP_COLORS = ['#5dffc4', '#ffb84d', '#7ec8ff'];  // phosphor green, amber, sonar blue
const NUM_SHIPS = SHIP_SIZES.length;

// ---------- Adjacency / placement helpers ----------
function canonicalCell(point) {
  const [ai, r] = point;
  return r === 0 ? [-1, 0] : [ai, r];
}
function cellKey(point) {
  const c = canonicalCell(point);
  return `${c[0]},${c[1]}`;
}
function isAdjacent(p, q) {
  const [aiP, rP] = p;
  const [aiQ, rQ] = q;
  if (rP === 0 && rQ === 1) return true;
  if (rQ === 0 && rP === 1) return true;
  if (rP === 0 && rQ === 0) return false;
  const sameAngle = (aiP === aiQ) && (Math.abs(rP - rQ) === 1);
  const angDiff = Math.min(
    ((aiP - aiQ) % N_ANG + N_ANG) % N_ANG,
    ((aiQ - aiP) % N_ANG + N_ANG) % N_ANG
  );
  const sameRadius = (rP === rQ) && (angDiff === 1);
  return sameAngle || sameRadius;
}
function neighborsCanonical(canon) {
  const [ai, r] = canon;
  const out = [];
  if (r === 0) {
    for (let a = 0; a < N_ANG; a++) out.push([a, 1]);
  } else {
    if (r - 1 === 0) out.push([-1, 0]);
    else if (r - 1 >= 1) out.push([ai, r - 1]);
    if (r + 1 <= R_MAX) out.push([ai, r + 1]);
    out.push([((ai - 1) % N_ANG + N_ANG) % N_ANG, r]);
    out.push([(ai + 1) % N_ANG, r]);
  }
  return out;
}

// ---------- Random ship placement (for CPU) ----------
function placeOne(size, usedKeys, attempts = 400) {
  for (let t = 0; t < attempts; t++) {
    const orient = Math.random() < 0.5 ? 'arc' : 'radial';
    let ship;
    if (orient === 'arc') {
      const r = 1 + Math.floor(Math.random() * R_MAX);
      const startAi = Math.floor(Math.random() * N_ANG);
      const dir = Math.random() < 0.5 ? 1 : -1;
      ship = [];
      for (let k = 0; k < size; k++) {
        ship.push([((startAi + dir * k) % N_ANG + N_ANG) % N_ANG, r]);
      }
    } else {
      const ai = Math.floor(Math.random() * N_ANG);
      if (size > (R_MAX - R_MIN + 1)) continue;
      const dir = Math.random() < 0.5 ? 1 : -1;
      let startR;
      if (dir === 1) startR = R_MIN + Math.floor(Math.random() * (R_MAX - size + 2));
      else           startR = R_MIN + size - 1 + Math.floor(Math.random() * (R_MAX - size + 2));
      ship = [];
      let bad = false;
      for (let k = 0; k < size; k++) {
        const rr = startR + dir * k;
        if (rr < R_MIN || rr > R_MAX) { bad = true; break; }
        ship.push([ai, rr]);
      }
      if (bad) continue;
    }
    const keys = ship.map(cellKey);
    if (keys.some(k => usedKeys.has(k))) continue;
    if (new Set(keys).size !== size) continue;
    return ship;
  }
  return null;
}
function randomPlaceShips(sizes, maxAttempts = 2000) {
  for (let t = 0; t < maxAttempts; t++) {
    const used = new Set();
    const placements = [];
    let ok = true;
    for (const size of sizes) {
      const s = placeOne(size, used);
      if (!s) { ok = false; break; }
      placements.push(s);
      s.forEach(c => used.add(cellKey(c)));
    }
    if (ok) return placements;
  }
  throw new Error('Could not place CPU ships');
}

// ---------- Game state ----------
const state = {
  phase: 'place',  // 'place' | 'guess' | 'done'
  shipsPlayer: [[], [], []],
  currentShip: 0,
  shipsCpu: [],
  cpuHits: new Set(),       // keys of cells player has hit on CPU board
  cpuMisses: new Set(),
  cpuHitPoints: [],         // raw [ai, r] for drawing
  cpuMissPoints: [],
  playerHits: new Set(),    // keys where CPU has hit player ships
  playerMisses: new Set(),
  playerHitPoints: [],
  playerMissPoints: [],
  cpuTargetsQueue: [],
  cpuHitStreak: [],
  selectedRadius: 1,
  selectedAngleIdx: 0,
  sonarAngleDeg: 0,
  prevSonarAngleDeg: 0,    // last frame's sweep angle, for crossing detection
  pings: [],               // active hit-pings: { ai, r, t } where t is elapsed seconds
  place: {                 // ship-placement UI state
    anchor: null,          // chosen start berth [ai, r], or null
    hover: null,           // berth under the pointer
    dragging: false,
    msg: '',               // transient warning shown in the banner
    msgTimer: null,
  },
};

// ---------- Canvas setup ----------
const playerCanvas = document.getElementById('player-canvas');
const cpuCanvas = document.getElementById('cpu-canvas');
const pctx = playerCanvas.getContext('2d');
const cctx = cpuCanvas.getContext('2d');

// Ensure a canvas's backing store matches its current displayed CSS size.
// Safe to call every frame: it only does work when the size actually changed
// (e.g. after the placement->guessing layout switch, or a window resize).
// Returns the CSS-pixel size to draw with.
function syncCanvas(canvas, ctx) {
  const dpr = window.devicePixelRatio || 1;
  const cssSize = canvas.clientWidth;
  if (cssSize === 0) return 0;            // not laid out yet; skip this frame
  const wantW = Math.round(cssSize * dpr);
  if (canvas.width !== wantW) {
    // Setting canvas.width resets the context transform to identity.
    canvas.width = wantW;
    canvas.height = wantW;
  }
  // Re-apply the dpr transform every call so drawing uses CSS-pixel coords.
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return cssSize;
}

let CANVAS_SIZE = syncCanvas(playerCanvas, pctx);
syncCanvas(cpuCanvas, cctx);
window.addEventListener('resize', () => {
  CANVAS_SIZE = syncCanvas(playerCanvas, pctx);
  syncCanvas(cpuCanvas, cctx);
  redrawAll();
});

function polarToXY(ai, r, size) {
  // We rotate so theta=0 points right, going counter-clockwise (standard math)
  const cx = size / 2;
  const cy = size / 2;
  const maxR = (size / 2) - 30; // padding for labels
  const theta = specialAngles[ai];
  const rr = (r / R_MAX) * maxR;
  return {
    x: cx + rr * Math.cos(theta),
    y: cy - rr * Math.sin(theta),
    cx, cy, maxR
  };
}

// ---------- Helpers ----------
function hexToRgba(hex, a) {
  const n = parseInt(hex.slice(1), 16);
  return `rgba(${(n >> 16) & 255}, ${(n >> 8) & 255}, ${n & 255}, ${a})`;
}
// Drawing scale: 1.0 at the original 560px board, never smaller than 0.75 so
// berths and hulls stay readable on small phone screens.
function uScale(size) { return Math.max(0.75, size / 560); }

// ---------- Grid drawing ----------
function drawGrid(ctx, size, isCpu) {
  const u = uScale(size);
  const cx = size / 2, cy = size / 2;
  const maxR = (size / 2) - 30;
  const tint = isCpu ? '125, 200, 255' : '93, 255, 196';

  // Water depth: each ring adds a translucent layer, so the centre reads as deepest
  ctx.fillStyle = isCpu ? 'rgba(30, 70, 120, 0.055)' : 'rgba(20, 90, 100, 0.055)';
  for (let r = R_MAX; r >= 1; r--) {
    ctx.beginPath();
    ctx.arc(cx, cy, (r / R_MAX) * maxR, 0, Math.PI * 2);
    ctx.fill();
  }

  // Radial circles
  ctx.strokeStyle = 'rgba(70, 130, 150, 0.5)';
  ctx.lineWidth = 1;
  for (let r = 1; r <= R_MAX; r++) {
    ctx.beginPath();
    ctx.arc(cx, cy, (r / R_MAX) * maxR, 0, Math.PI * 2);
    ctx.stroke();
  }
  // Outer bezel
  ctx.strokeStyle = `rgba(${tint}, 0.4)`;
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.arc(cx, cy, maxR + 5 * u, 0, Math.PI * 2);
  ctx.stroke();

  // Angular spokes (axes a little brighter)
  for (let i = 0; i < N_ANG; i++) {
    const theta = specialAngles[i];
    const axis = i % 4 === 0 && Math.abs(Math.sin(theta * 2)) < 1e-9;
    ctx.strokeStyle = axis ? 'rgba(70, 130, 150, 0.55)' : 'rgba(55, 105, 125, 0.32)';
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    ctx.lineTo(cx + maxR * Math.cos(theta), cy - maxR * Math.sin(theta));
    ctx.stroke();
  }

  // Degree ticks just inside the bezel (every 5 degrees, longer every 15)
  ctx.strokeStyle = `rgba(${tint}, 0.35)`;
  ctx.lineWidth = 1;
  for (let d = 0; d < 360; d += 5) {
    const a = d * Math.PI / 180;
    const len = (d % 15 === 0 ? 7 : 4) * u;
    ctx.beginPath();
    ctx.moveTo(cx + (maxR - len) * Math.cos(a), cy - (maxR - len) * Math.sin(a));
    ctx.lineTo(cx + maxR * Math.cos(a), cy - maxR * Math.sin(a));
    ctx.stroke();
  }

  // Angle labels
  ctx.fillStyle = '#9ad6bf';
  ctx.font = `bold ${Math.round(12 * Math.max(1, u * 0.95))}px "Share Tech Mono"`;
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.shadowColor = 'rgba(93, 255, 196, 0.4)';
  ctx.shadowBlur = 4;
  for (let i = 0; i < N_ANG; i++) {
    const theta = specialAngles[i];
    const lblR = maxR + 17;
    const lx = cx + lblR * Math.cos(theta);
    const ly = cy - lblR * Math.sin(theta);
    ctx.fillText(piLabel(angleFractions[i]), lx, ly);
  }
  ctx.shadowBlur = 0;

  // Radius labels (along theta=0 axis)
  ctx.fillStyle = '#4f7584';
  ctx.font = `${Math.round(10 * Math.max(1, u * 0.95))}px "Share Tech Mono"`;
  ctx.textAlign = 'left';
  for (let r = 1; r <= R_MAX; r++) {
    ctx.fillText(r.toString(), cx + (r / R_MAX) * maxR + 4, cy - 8);
  }

  // Berths: every intersection is a visible slot a ship can occupy
  for (let i = 0; i < N_ANG; i++) {
    for (let r = 1; r <= R_MAX; r++) {
      const { x, y } = polarToXY(i, r, size);
      ctx.strokeStyle = `rgba(${tint}, 0.5)`;
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.arc(x, y, 3.6 * u, 0, Math.PI * 2);
      ctx.stroke();
      ctx.fillStyle = `rgba(${tint}, 0.55)`;
      ctx.beginPath();
      ctx.arc(x, y, 1.3 * u, 0, Math.PI * 2);
      ctx.fill();
    }
  }
  // Origin berth: bigger, with a crosshair
  ctx.strokeStyle = `rgba(${tint}, 0.7)`;
  ctx.lineWidth = 1.2;
  ctx.beginPath();
  ctx.arc(cx, cy, 5.5 * u, 0, Math.PI * 2);
  ctx.moveTo(cx - 9 * u, cy); ctx.lineTo(cx + 9 * u, cy);
  ctx.moveTo(cx, cy - 9 * u); ctx.lineTo(cx, cy + 9 * u);
  ctx.stroke();
  ctx.fillStyle = `rgba(${tint}, 0.7)`;
  ctx.beginPath();
  ctx.arc(cx, cy, 1.6 * u, 0, Math.PI * 2);
  ctx.fill();
}

// ---------- Sonar sweep ----------
function drawSonarSweep(ctx, size) {
  const cx = size / 2, cy = size / 2;
  const maxR = (size / 2) - 30;

  // Faint blue overlay disc
  ctx.fillStyle = 'rgba(125, 200, 255, 0.05)';
  ctx.beginPath();
  ctx.arc(cx, cy, maxR, 0, Math.PI * 2);
  ctx.fill();

  // Rotating wedge with fading tail
  const leadDeg = state.sonarAngleDeg;
  const widthDeg = 30;
  const nBands = 14;
  const bandDeg = widthDeg / nBands;

  for (let i = 0; i < nBands; i++) {
    // Canvas angles go clockwise from 3 o'clock; we want CCW from 3 o'clock.
    // So negate the degrees.
    const aLead = -(leadDeg - i * bandDeg) * Math.PI / 180;
    const aTrail = -(leadDeg - (i + 1) * bandDeg) * Math.PI / 180;
    const alpha = 0.45 * (1 - i / nBands) + 0.04;
    ctx.fillStyle = `rgba(125, 200, 255, ${alpha})`;
    ctx.beginPath();
    ctx.moveTo(cx, cy);
    // arc goes from aLead to aTrail (note negation flips direction)
    ctx.arc(cx, cy, maxR, Math.min(aLead, aTrail), Math.max(aLead, aTrail));
    ctx.closePath();
    ctx.fill();
  }

  // Bright leading edge line
  const aLeadRad = -leadDeg * Math.PI / 180;
  ctx.strokeStyle = 'rgba(207, 232, 255, 0.85)';
  ctx.lineWidth = 1.5;
  ctx.shadowColor = '#7ec8ff';
  ctx.shadowBlur = 8;
  ctx.beginPath();
  ctx.moveTo(cx, cy);
  ctx.lineTo(cx + maxR * Math.cos(aLeadRad), cy + maxR * Math.sin(aLeadRad));
  ctx.stroke();
  ctx.shadowBlur = 0;
}

// ---------- Hit-target sonar pings ----------
const PING_DURATION = 0.9;  // seconds for a ping to expand and fade

// True if the sweep's leading edge moved across `targetDeg` this frame.
// All values are degrees in [0, 360), sweep advances by a positive step.
function sweepCrossed(prevDeg, curDeg, targetDeg) {
  // Normalize so we measure forward travel from prevDeg.
  const span = ((curDeg - prevDeg) % 360 + 360) % 360;
  const offset = ((targetDeg - prevDeg) % 360 + 360) % 360;
  return offset <= span;
}

// Each frame: if the sweep crossed the bearing of an already-hit CPU cell,
// start a fresh ping there.
function updatePings(dt) {
  // Advance / retire existing pings
  for (const p of state.pings) p.t += dt;
  state.pings = state.pings.filter(p => p.t < PING_DURATION);

  // Detect new crossings over hit cells
  for (const [ai, r] of state.cpuHitPoints) {
    const bearingDeg = (specialAngles[ai] * 180 / Math.PI) % 360;
    if (sweepCrossed(state.prevSonarAngleDeg, state.sonarAngleDeg, bearingDeg)) {
      // Refresh the ping for this cell (replace any in-flight one)
      state.pings = state.pings.filter(p => !(p.ai === ai && p.r === r));
      state.pings.push({ ai, r, t: 0 });
    }
  }
}

function drawPings(ctx, size) {
  for (const p of state.pings) {
    const { x, y } = polarToXY(p.ai, p.r, size);
    const prog = p.t / PING_DURATION;          // 0 -> 1
    const ringR = 6 + prog * 26;               // expanding radius
    const alpha = (1 - prog) * 0.85;           // fading out

    // Expanding ring
    ctx.strokeStyle = `rgba(255, 77, 94, ${alpha})`;
    ctx.lineWidth = 2.5 * (1 - prog) + 0.5;
    ctx.shadowColor = '#ff4d5e';
    ctx.shadowBlur = 16 * (1 - prog);
    ctx.beginPath();
    ctx.arc(x, y, ringR, 0, Math.PI * 2);
    ctx.stroke();

    // Bright core flare, strongest at the start of the ping
    const coreAlpha = (1 - prog) * (1 - prog) * 0.9;
    ctx.fillStyle = `rgba(255, 200, 205, ${coreAlpha})`;
    ctx.beginPath();
    ctx.arc(x, y, 4 + (1 - prog) * 5, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.shadowBlur = 0;
}

// ---------- Ship drawing ----------
// A ship is an ordered list of berths (stern -> bow). Its hull follows the
// ring (arc ships) or the spoke (radial ships) through those berths.

// Centreline of a ship in canvas pixels, extended `pad` px past each end.
// Returns { at(s) -> {x, y, ang}, total } where s is distance along the hull.
function shipPath(cells, size, pad) {
  const pts = cells.map(([ai, r]) => polarToXY(ai, r, size));
  const out = [];
  const STEPS = 14;
  for (let k = 0; k < cells.length - 1; k++) {
    const [a1, r1] = cells[k];
    const [a2, r2] = cells[k + 1];
    const P = pts[k], Q = pts[k + 1];
    for (let s = 0; s < STEPS; s++) {
      const f = s / STEPS;
      if (r1 === r2 && r1 > 0) {
        // Arc segment: sweep the shorter way around the ring
        const th1 = specialAngles[a1];
        let d = specialAngles[a2] - th1;
        while (d > Math.PI) d -= 2 * Math.PI;
        while (d <= -Math.PI) d += 2 * Math.PI;
        const th = th1 + d * f;
        const rr = (r1 / R_MAX) * P.maxR;
        out.push({ x: P.cx + rr * Math.cos(th), y: P.cy - rr * Math.sin(th) });
      } else {
        // Radial segment (including through the origin)
        out.push({ x: P.x + (Q.x - P.x) * f, y: P.y + (Q.y - P.y) * f });
      }
    }
  }
  const last = pts[pts.length - 1];
  out.push({ x: last.x, y: last.y });

  const ext = (a, b) => {
    const dx = a.x - b.x, dy = a.y - b.y;
    const L = Math.hypot(dx, dy) || 1;
    return { x: a.x + dx / L * pad, y: a.y + dy / L * pad };
  };
  out.unshift(ext(out[0], out[1]));
  out.push(ext(out[out.length - 1], out[out.length - 2]));

  const cum = [0];
  for (let i = 1; i < out.length; i++) {
    cum.push(cum[i - 1] + Math.hypot(out[i].x - out[i - 1].x, out[i].y - out[i - 1].y));
  }
  const total = cum[cum.length - 1];
  const at = (s) => {
    s = Math.max(0, Math.min(total, s));
    let i = 1;
    while (i < cum.length - 1 && cum[i] < s) i++;
    const seg = (cum[i] - cum[i - 1]) || 1;
    const f = (s - cum[i - 1]) / seg;
    const A = out[i - 1], B = out[i];
    return {
      x: A.x + (B.x - A.x) * f,
      y: A.y + (B.y - A.y) * f,
      ang: Math.atan2(B.y - A.y, B.x - A.x)
    };
  };
  return { at, total };
}

// opts: alpha, glow, details (deck gear), markers (per-berth portholes), wreck
function drawHull(ctx, size, cells, idx, color, opts = {}) {
  if (!cells || cells.length < 2) return;
  const u = uScale(size);
  const alpha = opts.alpha ?? 1;
  const wreck = !!opts.wreck;
  const details = opts.details !== false && !wreck;
  const markers = opts.markers !== false;
  const glow = opts.glow ?? 12;
  const W = (idx === 2 ? 12 : idx === 1 ? 10.5 : 9) * u;   // half-beam by ship class
  const { at, total } = shipPath(cells, size, 12 * u);

  // Hull profile: blunt transom at the stern, pointed bow
  const prof = (t) => {
    if (t > 0.70) return 1 - Math.pow((t - 0.70) / 0.30, 1.7);
    if (t < 0.07) return 0.62 + 0.38 * Math.sin((t / 0.07) * Math.PI / 2);
    return 1;
  };
  const outline = (t0, t1, scale, n) => {
    const L = [], R = [];
    for (let i = 0; i <= n; i++) {
      const t = t0 + (t1 - t0) * (i / n);
      const p = at(t * total);
      const w = W * scale * prof(t);
      const nx = Math.cos(p.ang + Math.PI / 2), ny = Math.sin(p.ang + Math.PI / 2);
      L.push({ x: p.x + nx * w, y: p.y + ny * w });
      R.push({ x: p.x - nx * w, y: p.y - ny * w });
    }
    return { L, R };
  };
  const trace = ({ L, R }) => {
    ctx.beginPath();
    ctx.moveTo(L[0].x, L[0].y);
    for (const q of L) ctx.lineTo(q.x, q.y);
    for (let i = R.length - 1; i >= 0; i--) ctx.lineTo(R[i].x, R[i].y);
    ctx.closePath();
  };

  ctx.save();
  ctx.globalAlpha = alpha;
  ctx.lineJoin = 'round';

  // Hull
  const hull = outline(0, 1, 1, 44);
  trace(hull);
  ctx.fillStyle = wreck ? 'rgba(38, 16, 22, 0.8)' : hexToRgba(color, 0.2);
  ctx.shadowColor = color;
  ctx.shadowBlur = wreck ? 0 : glow;
  ctx.fill();
  ctx.lineWidth = 2 * u;
  ctx.strokeStyle = color;
  if (wreck) ctx.setLineDash([6 * u, 4 * u]);
  ctx.stroke();
  ctx.setLineDash([]);
  ctx.shadowBlur = 0;

  // Deck inset
  if (!wreck) {
    trace(outline(0.09, 0.88, 0.55, 30));
    ctx.fillStyle = hexToRgba(color, 0.14);
    ctx.fill();
    ctx.lineWidth = 1;
    ctx.strokeStyle = hexToRgba(color, 0.45);
    ctx.stroke();
  }

  // Deck gear that makes each class recognisable: dark shapes with a bright
  // outline so they stand out against the lit hull
  if (details) {
    const local = (t, fn) => {
      const p = at(t * total);
      ctx.save();
      ctx.translate(p.x, p.y);
      ctx.rotate(p.ang);
      fn();
      ctx.restore();
    };
    const GEAR = 'rgba(3, 12, 16, 0.85)';
    ctx.lineWidth = 1.4 * u;
    ctx.strokeStyle = color;
    const block = (w, h, dy = 0) => {
      ctx.fillStyle = GEAR;
      ctx.fillRect(-w / 2 * u, (dy - h / 2) * u, w * u, h * u);
      ctx.strokeRect(-w / 2 * u, (dy - h / 2) * u, w * u, h * u);
    };
    const gun = (barrels) => {
      ctx.beginPath();
      for (const by of barrels) { ctx.moveTo(0, by * u); ctx.lineTo(9 * u, by * u); }
      ctx.stroke();
      ctx.fillStyle = GEAR;
      ctx.beginPath(); ctx.arc(0, 0, 3.4 * u, 0, Math.PI * 2); ctx.fill(); ctx.stroke();
    };
    if (idx === 0) {            // destroyer: bridge + single gun
      local(0.40, () => block(9, 7));
      local(0.70, () => gun([0]));
    } else if (idx === 1) {     // battleship: twin turrets + central tower
      local(0.28, () => gun([-1.5, 1.5]));
      local(0.72, () => gun([-1.5, 1.5]));
      local(0.50, () => block(11, 8));
    } else {                    // carrier: flight-deck stripe + island on the beam
      ctx.save();
      ctx.setLineDash([6 * u, 4 * u]);
      ctx.strokeStyle = color;
      ctx.lineWidth = 1.6 * u;
      ctx.beginPath();
      for (let i = 0; i <= 24; i++) {
        const p = at((0.13 + 0.74 * (i / 24)) * total);
        if (i === 0) ctx.moveTo(p.x, p.y); else ctx.lineTo(p.x, p.y);
      }
      ctx.stroke();
      ctx.restore();
      local(0.60, () => block(10, 5.5, W / u * 0.5));
    }
  }

  // One bright berth lamp per space the ship occupies, so its length is obvious
  // (deck gear above is dark, so only the lit dots count as spaces)
  if (markers) {
    for (const [ai, r] of cells) {
      const { x, y } = polarToXY(ai, r, size);
      ctx.beginPath();
      ctx.arc(x, y, 3.9 * u, 0, Math.PI * 2);
      ctx.fillStyle = wreck ? 'rgba(255, 120, 130, 0.9)' : '#f2fffa';
      ctx.fill();
      ctx.lineWidth = 1.6 * u;
      ctx.strokeStyle = 'rgba(3, 10, 14, 0.9)';
      ctx.stroke();
    }
  }
  ctx.restore();
}

// ---------- Hit/miss markers ----------
function drawHitsMisses(ctx, size, hits, misses) {
  // Misses: dim X
  ctx.strokeStyle = '#6a8a98';
  ctx.lineWidth = 2;
  for (const [ai, r] of misses) {
    const { x, y } = polarToXY(ai, r, size);
    ctx.beginPath();
    ctx.moveTo(x - 7, y - 7); ctx.lineTo(x + 7, y + 7);
    ctx.moveTo(x + 7, y - 7); ctx.lineTo(x - 7, y + 7);
    ctx.stroke();
  }
  // Hits: red glowing star
  ctx.fillStyle = '#ff4d5e';
  ctx.shadowColor = '#ff4d5e';
  ctx.shadowBlur = 14;
  for (const [ai, r] of hits) {
    const { x, y } = polarToXY(ai, r, size);
    drawStar(ctx, x, y, 5, 9, 4);
    ctx.fill();
  }
  ctx.shadowBlur = 0;
}
function drawStar(ctx, cx, cy, spikes, outerR, innerR) {
  ctx.beginPath();
  let rot = -Math.PI / 2;
  const step = Math.PI / spikes;
  ctx.moveTo(cx, cy - outerR);
  for (let i = 0; i < spikes; i++) {
    let x = cx + Math.cos(rot) * outerR;
    let y = cy + Math.sin(rot) * outerR;
    ctx.lineTo(x, y);
    rot += step;
    x = cx + Math.cos(rot) * innerR;
    y = cy + Math.sin(rot) * innerR;
    ctx.lineTo(x, y);
    rot += step;
  }
  ctx.lineTo(cx, cy - outerR);
  ctx.closePath();
}

// ---------- Redraw ----------
function isSunk(ship, hits, idx) {
  return ship.length === SHIP_SIZES[idx] && ship.every(c => hits.has(cellKey(c)));
}
function redrawPlayer() {
  const size = syncCanvas(playerCanvas, pctx);
  if (size === 0) return;            // not laid out yet
  pctx.clearRect(0, 0, size, size);
  drawGrid(pctx, size, false);
  state.shipsPlayer.forEach((ship, idx) => {
    if (ship.length < 2) return;
    const sunk = isSunk(ship, state.playerHits, idx);
    drawHull(pctx, size, ship, idx, sunk ? '#ff4d5e' : SHIP_COLORS[idx],
             sunk ? { wreck: true, alpha: 0.85 } : {});
  });
  if (state.phase === 'place') drawPlacementOverlay(pctx, size);
  drawHitsMisses(pctx, size, state.playerHitPoints, state.playerMissPoints);
}
function redrawCpu() {
  const size = syncCanvas(cpuCanvas, cctx);
  if (size === 0) return;            // not laid out yet (e.g. hidden in placement)
  cctx.clearRect(0, 0, size, size);
  drawGrid(cctx, size, true);
  // A hostile ship stays hidden until it is sunk, then its wreck is revealed
  state.shipsCpu.forEach((ship, idx) => {
    if (isSunk(ship, state.cpuHits, idx)) {
      drawHull(cctx, size, ship, idx, '#ff4d5e', { wreck: true, alpha: 0.8 });
    }
  });
  drawSonarSweep(cctx, size);
  drawHitsMisses(cctx, size, state.cpuHitPoints, state.cpuMissPoints);
  drawPings(cctx, size);
}
function redrawAll() { redrawPlayer(); redrawCpu(); }

// ---------- Sonar animation loop ----------
let lastFrame = performance.now();
const SONAR_DEG_PER_SEC = 36; // one rev per 10 seconds
function animate(now) {
  // Clamp dt: the very first frame (or a backgrounded tab) can produce a
  // huge gap since lastFrame was set at load time. An unclamped dt makes the
  // sweep angle jump hundreds of degrees and land at a bogus value.
  let dt = (now - lastFrame) / 1000;
  if (dt > 0.1 || dt < 0) dt = 0.016;   // cap at ~one frame
  lastFrame = now;
  state.prevSonarAngleDeg = state.sonarAngleDeg;
  // Positive modulo: JS '%' keeps the dividend's sign, which can yield a
  // negative angle. ((x % 360) + 360) % 360 forces [0, 360).
  const raw = state.sonarAngleDeg + SONAR_DEG_PER_SEC * dt;
  state.sonarAngleDeg = ((raw % 360) + 360) % 360;
  updatePings(dt);
  redrawCpu();
  if (state.phase === 'place') redrawPlayer();   // pulsing beacons + hover ghosts
  requestAnimationFrame(animate);
}
requestAnimationFrame(animate);

// ---------- Status bar / banner ----------
function setStatus(msg) {
  document.getElementById('status-text').textContent = msg;
}
function showBanner(text, variant, durationMs = 2200) {
  const el = document.getElementById('banner');
  el.className = `banner ${variant}`;
  el.innerHTML = `<span class="banner-text">${text}</span>`;
  if (durationMs > 0) {
    setTimeout(() => { el.className = 'banner hidden'; }, durationMs);
  }
}
function showEndBanner(text, variant) {
  const el = document.getElementById('banner');
  el.className = `banner ${variant}`;
  el.innerHTML = `
    <span class="banner-text">${text}</span>
    <button class="play-again-btn" id="play-again-btn">
      <span class="play-again-label">PLAY AGAIN</span>
    </button>
  `;
  document.getElementById('play-again-btn').addEventListener('click', resetGame);
}

// ---------- Fleet status display ----------
function renderFleets() {
  const playerEl = document.getElementById('player-fleet');
  const cpuEl = document.getElementById('cpu-fleet');
  playerEl.innerHTML = '';
  cpuEl.innerHTML = '';

  const placing = state.phase === 'place';
  for (let i = 0; i < NUM_SHIPS; i++) {
    const ship = state.shipsPlayer[i];
    const sunk = ship.length === SHIP_SIZES[i] &&
      ship.every(c => state.playerHits.has(cellKey(c)));
    const div = document.createElement('div');
    if (placing) {
      const st = i < state.currentShip ? 'placed' : (i === state.currentShip ? 'active' : 'pending');
      div.className = `fleet-item ${st}`;
      div.style.setProperty('--ship-color', SHIP_COLORS[i]);
    } else {
      div.className = `fleet-item ${sunk ? 'sunk' : 'alive'}`;
    }
    div.innerHTML = `<span class="fleet-name">${SHIP_NAMES[i]}</span><span class="fleet-size">${SHIP_SIZES[i]} PTS</span>`;
    playerEl.appendChild(div);
  }
  for (let i = 0; i < NUM_SHIPS; i++) {
    const sunk = state.shipsCpu[i] && state.shipsCpu[i].every(c => state.cpuHits.has(cellKey(c)));
    const div = document.createElement('div');
    div.className = `fleet-item ${sunk ? 'sunk' : 'alive'}`;
    div.innerHTML = `<span class="fleet-name">${SHIP_NAMES[i]}</span><span class="fleet-size">${SHIP_SIZES[i]} PTS</span>`;
    cpuEl.appendChild(div);
  }
}

// ---------- Placement ----------
// Two steps, no guessing:
//   1. Click a berth where the ship starts.
//   2. Click (or drag to) one of the glowing berths to aim it.
// Every legal ship is a straight line along a ring, or along a spoke (a spoke
// may run through the origin and out the opposite bearing).

const HALF_TURN = N_ANG / 2;   // index offset that adds pi to an angle
const modAng = (n) => ((n % N_ANG) + N_ANG) % N_ANG;
const sameCell = (p, q) => cellKey(p) === cellKey(q);

function usedKeysPlayer() {
  return new Set(state.shipsPlayer.flat().map(cellKey));
}

// All legal ships of `size` that start at `anchor`, as ordered stern->bow lists
function candidatesFrom(anchor, size) {
  const used = usedKeysPlayer();
  const [ai, r] = anchor;
  const out = [];
  const tryPush = (cells) => {
    if (cells.length !== size) return;
    const keys = cells.map(cellKey);
    if (new Set(keys).size !== size) return;
    if (keys.some(k => used.has(k))) return;
    out.push(cells);
  };

  if (r === 0) {
    // From the origin a ship can run out along any of the 16 bearings
    for (let a = 0; a < N_ANG; a++) {
      const cells = [[0, 0]];
      for (let k = 1; k < size && k <= R_MAX; k++) cells.push([a, k]);
      tryPush(cells);
    }
    return out;
  }
  // Along the ring, both directions
  for (const dir of [1, -1]) {
    const cells = [];
    for (let k = 0; k < size; k++) cells.push([modAng(ai + dir * k), r]);
    tryPush(cells);
  }
  // Outward along the spoke
  {
    const cells = [];
    for (let k = 0; k < size && r + k <= R_MAX; k++) cells.push([ai, r + k]);
    tryPush(cells);
  }
  // Inward along the spoke, through the origin and out the opposite bearing
  {
    const cells = [];
    for (let k = 0; k < size; k++) {
      const rr = r - k;
      if (rr >= 1) cells.push([ai, rr]);
      else if (rr === 0) cells.push([0, 0]);
      else if (-rr <= R_MAX) cells.push([modAng(ai + HALF_TURN), -rr]);
      else break;
    }
    tryPush(cells);
  }
  return out;
}

// The candidate (if any) that a given berth belongs to
function candidateFor(cell, cands) {
  return cands.find(c => c.slice(1).some(x => sameCell(x, cell))) || null;
}

// Every berth on the board, for hit-testing
const ALL_BERTHS = [[0, 0]];
for (let ai = 0; ai < N_ANG; ai++) {
  for (let r = 1; r <= R_MAX; r++) ALL_BERTHS.push([ai, r]);
}

// Nearest berth to the pointer, or null if the pointer is out in open water
function berthAt(evt) {
  const rect = playerCanvas.getBoundingClientRect();
  const size = playerCanvas.clientWidth;
  if (!size) return null;
  const x = evt.clientX - rect.left, y = evt.clientY - rect.top;
  let best = null, bestD = Infinity;
  for (const cell of ALL_BERTHS) {
    const p = polarToXY(cell[0], cell[1], size);
    const d = Math.hypot(p.x - x, p.y - y);
    if (d < bestD) { bestD = d; best = cell; }
  }
  return bestD <= 34 * uScale(size) ? best : null;
}

function cellLabel(cell) {
  return cell[1] === 0
    ? 'ORIGIN  r = 0'
    : `θ = ${piLabel(angleFractions[cell[0]])}   r = ${cell[1]}`;
}

// ----- Ship icon for the banner -----
function shipIconSVG(idx, color) {
  const n = SHIP_SIZES[idx];
  const w = 44 + n * 26;
  const bowBase = w - 30;
  const portholes = Array.from({ length: n }, (_, i) =>
    `<circle cx="${22 + i * 26}" cy="18" r="4.6" fill="#03080b" stroke="${color}" stroke-width="1.6"/>`
  ).join('');
  return `<svg class="pb-icon" viewBox="0 0 ${w} 36" aria-hidden="true">` +
    `<path d="M4 6 H${bowBase} L${w - 4} 18 L${bowBase} 30 H4 Z" fill="${hexToRgba(color, 0.2)}" ` +
    `stroke="${color}" stroke-width="2" stroke-linejoin="round"/>${portholes}</svg>`;
}

// ----- Banner / status text -----
function placeStatusLine() {
  const i = Math.min(state.currentShip, NUM_SHIPS - 1);
  return state.place.anchor
    ? `STEP 2 — CLICK A GLOWING SPOT TO AIM YOUR ${SHIP_NAMES[i]}.`
    : `PLACE YOUR ${SHIP_NAMES[i]} (${SHIP_SIZES[i]} SPACES). CLICK A START SPOT ON THE FRIENDLY GRID.`;
}

function updatePlaceBanner(flash) {
  const banner = document.getElementById('place-banner');
  if (!banner) return;
  const idx = Math.min(state.currentShip, NUM_SHIPS - 1);
  const color = SHIP_COLORS[idx];
  const name = SHIP_NAMES[idx].toLowerCase();
  banner.style.setProperty('--ship-color', color);
  banner.style.setProperty('--ship-glow', hexToRgba(color, 0.5));
  document.getElementById('pb-kicker').textContent = `DEPLOYMENT // SHIP ${idx + 1} OF ${NUM_SHIPS}`;
  document.getElementById('pb-ship').textContent = SHIP_NAMES[idx];
  document.getElementById('pb-size').innerHTML =
    shipIconSVG(idx, color) + `<span class="pb-spaces">${SHIP_SIZES[idx]} SPACES</span>`;

  const hint = document.getElementById('pb-hint');
  if (state.place.msg) {
    hint.className = 'pb-hint warn';
    hint.textContent = state.place.msg;
  } else if (state.place.anchor) {
    hint.className = 'pb-hint';
    hint.innerHTML = `<b>STEP 2</b> Click a glowing spot to aim your ${name} <span class="pb-esc">(ESC cancels)</span>`;
  } else {
    hint.className = 'pb-hint';
    hint.innerHTML = `<b>STEP 1</b> Click a spot on the grid to start your ${name}`;
  }
  document.getElementById('pb-pips').innerHTML = SHIP_NAMES.map((n, i) =>
    `<span class="pip ${i < state.currentShip ? 'done' : (i === state.currentShip ? 'active' : '')}" title="${n}"></span>`
  ).join('');

  document.getElementById('undo-btn').disabled = state.currentShip === 0;
  document.getElementById('reset-btn').disabled = state.currentShip === 0 && !state.place.anchor;

  if (flash) {
    banner.classList.remove('flash');
    void banner.offsetWidth;          // restart the CSS animation
    banner.classList.add('flash');
  }
}

function flashHint(msg) {
  state.place.msg = msg;
  clearTimeout(state.place.msgTimer);
  state.place.msgTimer = setTimeout(() => {
    state.place.msg = '';
    updatePlaceBanner();
  }, 2000);
  setStatus(msg);
  updatePlaceBanner();
}

// ----- Placement overlay (ghost hulls, beacons, hover) -----
function drawPlacementOverlay(ctx, size) {
  const idx = state.currentShip;
  if (idx >= NUM_SHIPS) return;
  const u = uScale(size);
  const color = SHIP_COLORS[idx];
  const sz = SHIP_SIZES[idx];
  const pulse = 0.5 + 0.5 * Math.sin(performance.now() / 1000 * 5);
  const pl = state.place;

  const ring = (cell, rad, col, a, lw) => {
    const { x, y } = polarToXY(cell[0], cell[1], size);
    ctx.strokeStyle = hexToRgba(col, a);
    ctx.lineWidth = lw * u;
    ctx.beginPath();
    ctx.arc(x, y, rad * u, 0, Math.PI * 2);
    ctx.stroke();
  };
  const cross = (cell, col) => {
    const { x, y } = polarToXY(cell[0], cell[1], size);
    ctx.strokeStyle = hexToRgba(col, 0.95);
    ctx.lineWidth = 2.2 * u;
    ctx.beginPath();
    ctx.moveTo(x - 6 * u, y - 6 * u); ctx.lineTo(x + 6 * u, y + 6 * u);
    ctx.moveTo(x + 6 * u, y - 6 * u); ctx.lineTo(x - 6 * u, y + 6 * u);
    ctx.stroke();
  };
  const ghost = (c, a) => drawHull(ctx, size, c, idx, color,
    { alpha: a, details: false, markers: false, glow: 0 });

  if (pl.anchor) {
    const cands = candidatesFrom(pl.anchor, sz);
    const hot = pl.hover ? candidateFor(pl.hover, cands) : null;
    cands.forEach(c => { if (c !== hot) ghost(c, 0.3); });
    if (hot) drawHull(ctx, size, hot, idx, color, { alpha: 0.95, glow: 18 });
    // Beacon on the far end of every option
    cands.forEach(c => {
      ring(c[c.length - 1], 9 + 4 * pulse, color, c === hot ? 1 : 0.5 + 0.4 * pulse, 2.2);
    });
    // Anchor
    ring(pl.anchor, 8 + 2 * pulse, '#ffffff', 0.95, 2.4);
    ring(pl.anchor, 14, color, 0.6, 1.5);
  } else if (pl.hover) {
    if (usedKeysPlayer().has(cellKey(pl.hover))) {
      ring(pl.hover, 9, '#ff4d5e', 0.9, 2);
      cross(pl.hover, '#ff4d5e');
    } else {
      const cands = candidatesFrom(pl.hover, sz);
      if (cands.length === 0) {
        ring(pl.hover, 9, '#ff4d5e', 0.9, 2);
        cross(pl.hover, '#ff4d5e');
      } else {
        cands.forEach(c => ghost(c, 0.22));
        ring(pl.hover, 9 + 2 * pulse, color, 1, 2.4);
      }
    }
  }
}

// ----- Actions -----
function cancelAnchor() {
  if (!state.place.anchor) return;
  state.place.anchor = null;
  state.place.dragging = false;
  setStatus(placeStatusLine());
  updatePlaceBanner();
}

function startFrom(cell, evt) {
  const idx = state.currentShip;
  if (usedKeysPlayer().has(cellKey(cell))) {
    flashHint('THAT SPOT IS ALREADY TAKEN');
    return;
  }
  if (candidatesFrom(cell, SHIP_SIZES[idx]).length === 0) {
    flashHint(`NO ROOM FOR A ${SHIP_NAMES[idx]} STARTING THERE — TRY ANOTHER SPOT`);
    return;
  }
  state.place.anchor = cell.slice();
  state.place.dragging = true;
  if (evt && evt.pointerId !== undefined && playerCanvas.setPointerCapture) {
    try { playerCanvas.setPointerCapture(evt.pointerId); } catch (e) { /* ignore */ }
  }
  setStatus(placeStatusLine());
  updatePlaceBanner();
}

function commitShip(cells) {
  const idx = state.currentShip;
  state.shipsPlayer[idx] = cells.map(c => c.slice());   // stern -> bow
  state.currentShip++;
  state.place.anchor = null;
  state.place.dragging = false;
  if (state.currentShip >= NUM_SHIPS) {
    finishDeployment();
  } else {
    const ni = state.currentShip;
    setStatus(`${SHIP_NAMES[idx]} DEPLOYED. NOW PLACE YOUR ${SHIP_NAMES[ni]} (${SHIP_SIZES[ni]} SPACES).`);
    updatePlaceBanner(true);
  }
  renderFleets();
  redrawPlayer();
}

function finishDeployment() {
  generateCpuShips();
  startGuessingPhase();
  showBanner('FLEET DEPLOYED', 'sunk-hostile', 1400);
}

function undoShip() {
  if (state.phase !== 'place' || state.currentShip === 0) return;
  state.currentShip--;
  state.shipsPlayer[state.currentShip] = [];
  state.place.anchor = null;
  state.place.dragging = false;
  setStatus(`UNDONE. PLACE YOUR ${SHIP_NAMES[state.currentShip]} AGAIN.`);
  updatePlaceBanner(true);
  renderFleets();
  redrawPlayer();
}

function resetPlacement() {
  if (state.phase !== 'place') return;
  state.shipsPlayer = [[], [], []];
  state.currentShip = 0;
  state.place.anchor = null;
  state.place.dragging = false;
  setStatus(placeStatusLine());
  updatePlaceBanner(true);
  renderFleets();
  redrawPlayer();
}

// Drop whatever hasn't been placed yet at random, then start the battle
function autoDeploy() {
  if (state.phase !== 'place') return;
  for (let attempt = 0; attempt < 500; attempt++) {
    const used = new Set(state.shipsPlayer.flat().map(cellKey));
    const placed = [];
    let ok = true;
    for (let i = state.currentShip; i < NUM_SHIPS; i++) {
      const s = placeOne(SHIP_SIZES[i], used);
      if (!s) { ok = false; break; }
      placed.push(s);
      s.forEach(c => used.add(cellKey(c)));
    }
    if (ok) {
      placed.forEach((s, k) => { state.shipsPlayer[state.currentShip + k] = s; });
      state.currentShip = NUM_SHIPS;
      break;
    }
  }
  if (state.currentShip >= NUM_SHIPS) {
    state.place.anchor = null;
    renderFleets();
    finishDeployment();
  }
}

// ----- Input -----
function cursorFor(cell) {
  if (!cell) return 'crosshair';
  if (state.place.anchor) {
    const cands = candidatesFrom(state.place.anchor, SHIP_SIZES[state.currentShip]);
    if (candidateFor(cell, cands)) return 'pointer';
  }
  return usedKeysPlayer().has(cellKey(cell)) ? 'not-allowed' : 'pointer';
}

playerCanvas.addEventListener('pointermove', (evt) => {
  if (state.phase !== 'place') return;
  const cell = berthAt(evt);
  state.place.hover = cell;
  document.getElementById('pb-readout').textContent = cell ? `CURSOR  ${cellLabel(cell)}` : 'CURSOR  —';
  playerCanvas.style.cursor = cursorFor(cell);
});
playerCanvas.addEventListener('pointerleave', () => {
  state.place.hover = null;
  const ro = document.getElementById('pb-readout');
  if (ro) ro.textContent = 'CURSOR  —';
});

playerCanvas.addEventListener('pointerdown', (evt) => {
  if (state.phase !== 'place' || state.currentShip >= NUM_SHIPS) return;
  if (evt.button !== undefined && evt.button !== 0) return;
  const pl = state.place;
  pl.dragging = false;
  const cell = berthAt(evt);
  pl.hover = cell;
  if (!cell) { cancelAnchor(); return; }          // click in open water cancels
  if (pl.anchor) {
    const hit = candidateFor(cell, candidatesFrom(pl.anchor, SHIP_SIZES[state.currentShip]));
    if (hit) { commitShip(hit); return; }
    if (sameCell(cell, pl.anchor)) { cancelAnchor(); return; }
  }
  startFrom(cell, evt);
});

// Drag support: press on the start, release on a glowing spot
playerCanvas.addEventListener('pointerup', (evt) => {
  const pl = state.place;
  if (!pl.dragging) return;
  pl.dragging = false;
  if (state.phase !== 'place' || !pl.anchor) return;
  const cell = berthAt(evt);
  if (!cell || sameCell(cell, pl.anchor)) return;
  const hit = candidateFor(cell, candidatesFrom(pl.anchor, SHIP_SIZES[state.currentShip]));
  if (hit) commitShip(hit);
});
playerCanvas.addEventListener('pointercancel', () => { state.place.dragging = false; });

playerCanvas.addEventListener('contextmenu', (evt) => {
  if (state.phase !== 'place') return;
  evt.preventDefault();
  cancelAnchor();
});

document.addEventListener('keydown', (evt) => {
  if (state.phase !== 'place') return;
  if (evt.key === 'Escape') cancelAnchor();
  if ((evt.ctrlKey || evt.metaKey) && evt.key.toLowerCase() === 'z') {
    evt.preventDefault();
    undoShip();
  }
});

document.getElementById('undo-btn').addEventListener('click', undoShip);
document.getElementById('reset-btn').addEventListener('click', resetPlacement);
document.getElementById('auto-btn').addEventListener('click', autoDeploy);

// ---------- CPU ships ----------
function generateCpuShips() {
  state.shipsCpu = randomPlaceShips(SHIP_SIZES);
}

// ---------- Guessing phase ----------
function startGuessingPhase() {
  state.phase = 'guess';
  state.place.anchor = null;
  state.place.hover = null;
  state.place.dragging = false;
  document.body.classList.remove('phase-place');
  document.getElementById('controls').hidden = false;
  buildRadiusButtons();
  buildAngleButtons();
  setStatus('SONAR ACTIVE. SELECT RADIUS AND BEARING, THEN FIRE.');
  // The animation loop's redrawCpu() self-syncs the canvas size every frame,
  // so the layout change is picked up automatically once it reflows.
  redrawPlayer();
}

function buildRadiusButtons() {
  const wrap = document.getElementById('radius-buttons');
  wrap.innerHTML = '';
  for (let r = R_MIN; r <= R_MAX; r++) {
    const b = document.createElement('button');
    b.className = 'radius-btn' + (r === state.selectedRadius ? ' active' : '');
    b.textContent = r;
    b.addEventListener('click', () => {
      state.selectedRadius = r;
      [...wrap.children].forEach((c, i) => c.classList.toggle('active', (R_MIN + i) === r));
    });
    wrap.appendChild(b);
  }
}

function buildAngleButtons() {
  const wrap = document.getElementById('angle-grid');
  wrap.innerHTML = '';
  for (let i = 0; i < N_ANG; i++) {
    const b = document.createElement('button');
    b.className = 'angle-btn' + (i === state.selectedAngleIdx ? ' active' : '');
    b.textContent = piLabel(angleFractions[i]);
    b.addEventListener('click', () => {
      state.selectedAngleIdx = i;
      [...wrap.children].forEach((c, idx) => c.classList.toggle('active', idx === i));
    });
    wrap.appendChild(b);
  }
}

// ---------- Firing ----------
document.getElementById('fire-btn').addEventListener('click', () => fire());

function fire() {
  if (state.phase !== 'guess') return;
  const r = state.selectedRadius;
  const ai = state.selectedAngleIdx;
  const point = [ai, r];
  const k = cellKey(point);
  const aLbl = r !== 0 ? piLabel(angleFractions[ai]) : '—';

  if (state.cpuHits.has(k) || state.cpuMisses.has(k)) {
    setStatus(`(θ=${aLbl}, r=${r}) — ALREADY CALLED`);
    return;
  }

  // Find hit ship
  let hitShipIdx = -1;
  for (let i = 0; i < state.shipsCpu.length; i++) {
    if (state.shipsCpu[i].some(c => cellKey(c) === k)) { hitShipIdx = i; break; }
  }

  if (hitShipIdx >= 0) {
    state.cpuHits.add(k);
    state.cpuHitPoints.push(point);
    const ship = state.shipsCpu[hitShipIdx];
    const sunk = ship.every(c => state.cpuHits.has(cellKey(c)));
    if (sunk) {
      setStatus(`TARGET SUNK: ${SHIP_NAMES[hitShipIdx]}. FIRE AGAIN.`);
      showBanner(`HOSTILE ${SHIP_NAMES[hitShipIdx]} DESTROYED`, 'sunk-hostile');
    } else {
      setStatus(`DIRECT HIT AT (θ=${aLbl}, r=${r}). FIRE AGAIN.`);
    }
    // Victory check
    const allCpuCells = state.shipsCpu.flat().map(cellKey);
    if (allCpuCells.every(ck => state.cpuHits.has(ck))) {
      setStatus('ALL HOSTILES NEUTRALIZED. VICTORY.');
      state.phase = 'done';
      showEndBanner('VICTORY', 'victory');
    }
    redrawCpu();
    renderFleets();
  } else {
    state.cpuMisses.add(k);
    state.cpuMissPoints.push(point);
    setStatus(`MISS AT (θ=${aLbl}, r=${r}). HOSTILE TURN...`);
    redrawCpu();
    setTimeout(computerTurn, 900);
  }
}

// ---------- CPU AI (ported from Python) ----------
function streakOrientation() {
  if (state.cpuHitStreak.length < 2) return [null, null];
  const radii = new Set(state.cpuHitStreak.map(([_, r]) => r));
  if (radii.size === 1 && !radii.has(0)) return ['arc', [...radii][0]];
  const nonOrigin = state.cpuHitStreak.filter(([_, r]) => r !== 0);
  if (nonOrigin.length > 0) {
    const angles = new Set(nonOrigin.map(([a]) => a));
    if (angles.size === 1) return ['radial', [...angles][0]];
  }
  return [null, null];
}

function canonToPoint(canon) {
  const [ai, r] = canon;
  return r === 0 ? [0, 0] : [ai, r];
}

function allPlayerCellsCanonical() {
  const cells = [[-1, 0]];
  for (let ai = 0; ai < N_ANG; ai++) {
    for (let r = 1; r <= R_MAX; r++) cells.push([ai, r]);
  }
  return cells;
}

function pickCpuTarget() {
  const tried = new Set([...state.playerHits, ...state.playerMisses]);

  const [orient, value] = streakOrientation();
  if (orient === 'arc') {
    const r = value;
    const angIndices = state.cpuHitStreak.map(([a]) => a).sort((a, b) => a - b);
    const lo = angIndices[0], hi = angIndices[angIndices.length - 1];
    const candidates = [
      [((lo - 1) % N_ANG + N_ANG) % N_ANG, r],
      [(hi + 1) % N_ANG, r]
    ];
    shuffle(candidates);
    for (const c of candidates) {
      if (!tried.has(cellKey(c))) return c;
    }
  } else if (orient === 'radial') {
    const ai = value;
    const radiiInStreak = state.cpuHitStreak.map(([_, r]) => r).sort((a, b) => a - b);
    const ends = [];
    if (radiiInStreak[0] - 1 >= R_MIN) {
      const rLow = radiiInStreak[0] - 1;
      ends.push(rLow === 0 ? [-1, 0] : [ai, rLow]);
    }
    if (radiiInStreak[radiiInStreak.length - 1] + 1 <= R_MAX) {
      ends.push([ai, radiiInStreak[radiiInStreak.length - 1] + 1]);
    }
    shuffle(ends);
    for (const c of ends) {
      if (!tried.has(cellKey(c))) return canonToPoint(c);
    }
  }

  // Single-hit neighbor probing
  while (state.cpuTargetsQueue.length > 0) {
    const c = state.cpuTargetsQueue.shift();
    if (!tried.has(cellKey(c))) return canonToPoint(c);
  }

  // Hunt mode: random
  const all = allPlayerCellsCanonical().filter(c => !tried.has(cellKey(c)));
  if (all.length === 0) return null;
  return canonToPoint(all[Math.floor(Math.random() * all.length)]);
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}

function expandNeighbors(target) {
  const tried = new Set([...state.playerHits, ...state.playerMisses]);
  const canon = canonicalCell(target);
  const [orient, value] = streakOrientation();
  let candidates = neighborsCanonical(canon);
  if (orient === 'arc') {
    candidates = candidates.filter(c => c[1] === value);
  } else if (orient === 'radial') {
    candidates = candidates.filter(c => c[0] === value || (c[0] === -1 && c[1] === 0));
  }
  const queueKeys = new Set(state.cpuTargetsQueue.map(cellKey));
  for (const n of candidates) {
    const nk = cellKey(n);
    if (!tried.has(nk) && !queueKeys.has(nk)) {
      state.cpuTargetsQueue.push(n);
      queueKeys.add(nk);
    }
  }
}

function purgeQueueOffLine() {
  const [orient, value] = streakOrientation();
  if (orient === 'arc') {
    state.cpuTargetsQueue = state.cpuTargetsQueue.filter(c => c[1] === value);
  } else if (orient === 'radial') {
    state.cpuTargetsQueue = state.cpuTargetsQueue.filter(
      c => c[0] === value || (c[0] === -1 && c[1] === 0)
    );
  }
}

function shipContaining(point, ships) {
  const k = cellKey(point);
  return ships.find(s => s.some(c => cellKey(c) === k)) || null;
}

function computerTurn() {
  if (state.phase === 'done') return;
  const target = pickCpuTarget();
  if (!target) {
    setStatus('HOSTILE HAS NO TARGETS REMAINING');
    return;
  }
  const [ai, r] = target;
  const aLbl = r !== 0 ? piLabel(angleFractions[ai]) : '—';
  const ship = shipContaining(target, state.shipsPlayer);

  if (ship) {
    state.playerHits.add(cellKey(target));
    state.playerHitPoints.push(target);
    const sunk = ship.every(c => state.playerHits.has(cellKey(c)));
    let sunkShipIdx = -1;
    for (let i = 0; i < state.shipsPlayer.length; i++) {
      if (state.shipsPlayer[i] === ship) { sunkShipIdx = i; break; }
    }

    if (sunk) {
      setStatus(`HOSTILE SUNK YOUR ${SHIP_NAMES[sunkShipIdx]}. FIRING AGAIN...`);
      showBanner(`FRIENDLY ${SHIP_NAMES[sunkShipIdx]} LOST`, 'sunk-friendly');
      // Clear streak/queue for this ship
      const shipKeys = new Set(ship.map(cellKey));
      state.cpuHitStreak = state.cpuHitStreak.filter(c => !shipKeys.has(cellKey(c)));
      state.cpuTargetsQueue = state.cpuTargetsQueue.filter(c => !shipKeys.has(cellKey(c)));
    } else {
      state.cpuHitStreak.push(target);
      expandNeighbors(target);
      purgeQueueOffLine();
      setStatus(`HOSTILE HIT AT (θ=${aLbl}, r=${r}). FIRING AGAIN...`);
    }

    // Defeat check
    const allPlayerCells = state.shipsPlayer.flat().map(cellKey);
    if (allPlayerCells.every(ck => state.playerHits.has(ck))) {
      setStatus('ALL FRIENDLIES DESTROYED. DEFEAT.');
      state.phase = 'done';
      showEndBanner('DEFEAT', 'defeat');
      redrawPlayer();
      renderFleets();
      return;
    }

    redrawPlayer();
    renderFleets();

    if (state.phase !== 'done') {
      setTimeout(computerTurn, 1000);
    }
  } else {
    state.playerMisses.add(cellKey(target));
    state.playerMissPoints.push(target);
    setStatus(`HOSTILE MISS AT (θ=${aLbl}, r=${r}). YOUR TURN — FIRE.`);
    redrawPlayer();
  }
}

// ---------- Clock ----------
function tickClock() {
  const d = new Date();
  const hh = String(d.getHours()).padStart(2, '0');
  const mm = String(d.getMinutes()).padStart(2, '0');
  const ss = String(d.getSeconds()).padStart(2, '0');
  document.getElementById('clock').textContent = `${hh}:${mm}:${ss}`;
}
setInterval(tickClock, 1000);
tickClock();

// ---------- Reset ----------
function resetGame() {
  // Wipe state in place so existing references stay valid
  state.phase = 'place';
  state.shipsPlayer = [[], [], []];
  state.currentShip = 0;
  state.shipsCpu = [];
  state.cpuHits.clear();
  state.cpuMisses.clear();
  state.cpuHitPoints.length = 0;
  state.cpuMissPoints.length = 0;
  state.playerHits.clear();
  state.playerMisses.clear();
  state.playerHitPoints.length = 0;
  state.playerMissPoints.length = 0;
  state.cpuTargetsQueue.length = 0;
  state.cpuHitStreak.length = 0;
  state.selectedRadius = 1;
  state.selectedAngleIdx = 0;
  state.pings.length = 0;

  // Hide banner + controls
  document.getElementById('banner').className = 'banner hidden';
  document.getElementById('controls').hidden = true;
  document.body.classList.add('phase-place');

  state.place.anchor = null;
  state.place.hover = null;
  state.place.dragging = false;
  state.place.msg = '';
  setStatus(placeStatusLine());
  updatePlaceBanner(true);
  renderFleets();
  // redrawCpu()/redrawPlayer() self-sync the canvas size each call, so the
  // layout change is handled automatically.
  redrawPlayer();
}

// ---------- Init ----------
setStatus(placeStatusLine());
updatePlaceBanner(true);
renderFleets();
redrawAll();
