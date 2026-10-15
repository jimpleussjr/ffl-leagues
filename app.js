"use strict";

/* ------------------------------------------------------------------ *
 *  Pleuss Family Fantasy Football - season summary
 *  Pulls live data from ESPN's (undocumented) fantasy football API.
 * ------------------------------------------------------------------ */

const SEASON = 2026;
const WEEKS = 5; // analyze the first five weeks of the season
const BASE = `https://lm-api-reads.fantasy.espn.com/apis/v3/games/ffl/seasons/${SEASON}`;
const NEG = 1e9; // sentinel cost for "player is not eligible for this slot"

const LEAGUES = [
  { id: 847888, fallbackName: "League A" },
  { id: 1453712872, fallbackName: "League B" },
];

/* ----------------------------- fetching --------------------------- */

async function getJson(url) {
  const res = await fetch(url);
  if (!res.ok) throw new Error(`ESPN request failed (${res.status})`);
  return res.json();
}

function leagueUrl(id, params) {
  return `${BASE}/segments/0/leagues/${id}?${params}`;
}

async function loadLeague(cfg) {
  const meta = await getJson(
    leagueUrl(cfg.id, "view=mTeam&view=mSettings&view=mStandings")
  );

  const members = {};
  (meta.members || []).forEach((m) => {
    members[m.id] = m.displayName;
  });

  const teams = {};
  (meta.teams || []).forEach((t) => {
    const ov = (t.record && t.record.overall) || {};
    teams[t.id] = {
      id: t.id,
      name: t.name,
      abbrev: t.abbrev,
      owners: (t.owners || []).map((o) => members[o]).filter(Boolean),
      wins: ov.wins || 0,
      losses: ov.losses || 0,
      ties: ov.ties || 0,
      pf: ov.pointsFor || 0,
      pa: ov.pointsAgainst || 0,
    };
  });

  // Which starting slots exist (skip bench = 20 and IR = 21).
  const counts = (meta.settings.rosterSettings || {}).lineupSlotCounts || {};
  const startSlots = [];
  Object.keys(counts).forEach((k) => {
    const slot = Number(k);
    if (slot === 20 || slot === 21) return;
    const n = counts[k] || 0;
    for (let i = 0; i < n; i++) startSlots.push(slot);
  });

  // Per-week box scores (player points, actual & optimal lineup totals).
  const weeks = [];
  for (let w = 1; w <= WEEKS; w++) {
    const box = await getJson(
      leagueUrl(cfg.id, `view=mBoxscore&scoringPeriodId=${w}`)
    );
    const week = {};
    (box.schedule || []).forEach((matchup) => {
      [matchup.home, matchup.away].forEach((side) => {
        if (!side) return;
        const rsp = side.rosterForCurrentScoringPeriod;
        const entries = (rsp && rsp.entries) || [];
        if (entries.length === 0) return;

        const players = entries.map((e) => {
          const pe = e.playerPoolEntry || {};
          const p = pe.player || {};
          return {
            id: e.playerId,
            name: p.fullName || `Player ${e.playerId}`,
            slot: e.lineupSlotId,
            points: pe.appliedStatTotal != null ? pe.appliedStatTotal : 0,
            eligible: p.eligibleSlots || [],
          };
        });

        const actual = players
          .filter((pl) => pl.slot !== 20 && pl.slot !== 21)
          .reduce((sum, pl) => sum + pl.points, 0);

        week[side.teamId] = {
          actual,
          optimal: optimalLineup(players, startSlots),
          players,
        };
      });
    });
    weeks.push(week);
  }

  // Roster activity: players added / dropped over weeks 1..WEEKS.
  const seenTx = {};
  for (let w = 1; w <= WEEKS; w++) {
    const tx = await getJson(
      leagueUrl(cfg.id, `view=mTransactions2&scoringPeriodId=${w}`)
    );
    (tx.transactions || []).forEach((t) => {
      seenTx[t.id] = t; // dedupe across weeks by transaction id
    });
  }
  const activity = {};
  Object.keys(teams).forEach((id) => {
    activity[id] = { adds: 0, drops: 0 };
  });
  Object.keys(seenTx).forEach((id) => {
    const t = seenTx[id];
    (t.items || []).forEach((it) => {
      if (it.type === "ADD" && it.toTeamId && activity[it.toTeamId]) {
        activity[it.toTeamId].adds += 1;
      } else if (it.type === "DROP" && it.fromTeamId && activity[it.fromTeamId]) {
        activity[it.fromTeamId].drops += 1;
      }
    });
  });

  return {
    id: cfg.id,
    name: (meta.settings && meta.settings.name) || cfg.fallbackName,
    teams,
    startSlots,
    weeks,
    activity,
  };
}

/* ------------------- optimal lineup (max assignment) -------------- *
 * Brute-force optimal is exponential, so we solve it as a maximum
 * weight bipartite matching (Hungarian algorithm). Each starting slot
 * instance is a row; each rostered player is a column. A player may
 * only fill a slot if the slot id is in the player's eligibleSlots.   */

function hungarianMin(a, n) {
  const INF = Infinity;
  const u = new Array(n + 1).fill(0);
  const v = new Array(n + 1).fill(0);
  const p = new Array(n + 1).fill(0);
  const way = new Array(n + 1).fill(0);

  for (let i = 1; i <= n; i++) {
    p[0] = i;
    let j0 = 0;
    const minv = new Array(n + 1).fill(INF);
    const used = new Array(n + 1).fill(false);

    do {
      used[j0] = true;
      const i0 = p[j0];
      let delta = INF;
      let j1 = 0;
      for (let j = 1; j <= n; j++) {
        if (used[j]) continue;
        const cur = a[i0][j] - u[i0] - v[j];
        if (cur < minv[j]) {
          minv[j] = cur;
          way[j] = j0;
        }
        if (minv[j] < delta) {
          delta = minv[j];
          j1 = j;
        }
      }
      for (let j = 0; j <= n; j++) {
        if (used[j]) {
          u[p[j]] += delta;
          v[j] -= delta;
        } else {
          minv[j] -= delta;
        }
      }
      j0 = j1;
    } while (p[j0] !== 0);

    do {
      const j1 = way[j0];
      p[j0] = p[j1];
      j0 = j1;
    } while (j0);
  }

  const colForRow = new Array(n + 1).fill(0);
  for (let j = 1; j <= n; j++) colForRow[p[j]] = j;
  return colForRow;
}

function optimalLineup(players, startSlots) {
  const rows = startSlots.length;
  const cols = players.length;
  if (rows === 0 || cols === 0) return 0;

  const n = Math.max(rows, cols);
  const a = [];
  for (let i = 0; i <= n; i++) a.push(new Array(n + 1).fill(0));

  for (let i = 1; i <= n; i++) {
    for (let j = 1; j <= n; j++) {
      let cost = 0;
      if (i <= rows && j <= cols) {
        const slot = startSlots[i - 1];
        const pl = players[j - 1];
        const eligible = (pl.eligible || []).indexOf(slot) !== -1;
        cost = eligible ? pl.points : -NEG;
      }
      a[i][j] = -cost; // Hungarian minimizes, so negate to maximize
    }
  }

  const colForRow = hungarianMin(a, n);

  let total = 0;
  for (let i = 1; i <= rows; i++) {
    const j = colForRow[i];
    if (j <= cols) {
      const slot = startSlots[i - 1];
      const pl = players[j - 1];
      if ((pl.eligible || []).indexOf(slot) !== -1) total += pl.points;
    }
  }
  return total;
}

/* ----------------------------- analysis --------------------------- */

function analyze(league) {
  const ids = Object.keys(league.teams).map(Number);
  const n = ids.length;

  const perTeam = {};
  ids.forEach((id) => (perTeam[id] = { scores: [], actual: 0, optimal: 0 }));

  for (let w = 0; w < WEEKS; w++) {
    ids.forEach((id) => {
      const e = league.weeks[w][id];
      perTeam[id].scores.push(e ? e.actual : null);
      if (e) {
        perTeam[id].actual += e.actual;
        perTeam[id].optimal += e.optimal;
      }
    });
  }

  // Standings: win% then points-for.
  const standings = ids
    .map((id) => {
      const t = league.teams[id];
      const games = t.wins + t.losses + t.ties;
      return {
        ...t,
        games,
        winPct: games ? (t.wins + 0.5 * t.ties) / games : 0,
      };
    })
    .sort((a, b) => b.winPct - a.winPct || b.pf - a.pf);

  // Highest / lowest single-week team score.
  let high = null;
  let low = null;
  for (let w = 0; w < WEEKS; w++) {
    ids.forEach((id) => {
      const s = perTeam[id].scores[w];
      if (s == null) return;
      if (!high || s > high.score) high = { teamId: id, week: w + 1, score: s };
      if (!low || s < low.score) low = { teamId: id, week: w + 1, score: s };
    });
  }

  // Trophy (weekly high) / plunger (weekly low) counts.
  const trophies = {};
  const plungers = {};
  ids.forEach((id) => {
    trophies[id] = 0;
    plungers[id] = 0;
  });
  for (let w = 0; w < WEEKS; w++) {
    let hi = -Infinity;
    let lo = Infinity;
    let hiIds = [];
    let loIds = [];
    ids.forEach((id) => {
      const s = perTeam[id].scores[w];
      if (s == null) return;
      if (s > hi) { hi = s; hiIds = [id]; }
      else if (s === hi) hiIds.push(id);
      if (s < lo) { lo = s; loIds = [id]; }
      else if (s === lo) loIds.push(id);
    });
    hiIds.forEach((id) => (trophies[id] += 1 / hiIds.length));
    loIds.forEach((id) => (plungers[id] += 1 / loIds.length));
  }

  // Manager quality: points left on the bench vs. the optimal lineup.
  const managers = ids
    .map((id) => {
      const t = league.teams[id];
      const actual = perTeam[id].actual;
      const optimal = perTeam[id].optimal;
      return {
        id,
        name: t.name,
        owner: t.owners.join(" & "),
        actual,
        optimal,
        regret: optimal - actual,
        eff: optimal > 0 ? actual / optimal : 0,
      };
    })
    .sort((a, b) => a.regret - b.regret); // best (least regret) first

  // Luck: actual record vs. all-play record (facing every team every week).
  const allPlayGames = WEEKS * (n - 1);
  const luck = ids
    .map((id) => {
      const t = league.teams[id];
      let expWins = 0;
      for (let w = 0; w < WEEKS; w++) {
        const mine = perTeam[id].scores[w];
        if (mine == null) continue;
        ids.forEach((o) => {
          if (o === id) return;
          const other = perTeam[o].scores[w];
          if (other == null) return;
          if (mine > other) expWins += 1;
          else if (mine === other) expWins += 0.5;
        });
      }
      const games = t.wins + t.losses + t.ties;
      const allPlayPct = allPlayGames ? expWins / allPlayGames : 0;
      const expectedWins = allPlayPct * games;
      const actualWins = t.wins + 0.5 * t.ties;
      return {
        id,
        name: t.name,
        owner: t.owners.join(" & "),
        actualWins,
        expectedWins,
        allPlayPct,
        luck: actualWins - expectedWins,
      };
    })
    .sort((a, b) => b.luck - a.luck);

  // Roster activity: total adds + drops per team, most active first.
  const activity = ids
    .map((id) => {
      const act = (league.activity && league.activity[id]) || { adds: 0, drops: 0 };
      return {
        id,
        name: league.teams[id].name,
        owner: league.teams[id].owners.join(" & "),
        adds: act.adds,
        drops: act.drops,
        total: act.adds + act.drops,
      };
    })
    .sort((a, b) => b.total - a.total || b.adds - a.adds);

  return { n, standings, high, low, trophies, plungers, managers, luck, activity };
}

/* ----------------------------- rendering -------------------------- */

const CHART = {
  color: "#e8eef6",
  grid: "rgba(255,255,255,.08)",
  accent: "#3ea6ff",
  green: "#37c26b",
  red: "#ff5c72",
  gold: "#ffcf4d",
  plunger: "#8a6bff",
  muted: "#9db0c6",
};

function esc(s) {
  return String(s).replace(/[&<>"]/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c])
  );
}

function fmt(n, d = 1) {
  return Number(n).toFixed(d);
}

function standingsTable(league, a) {
  const rows = a.standings
    .map((t, i) => {
      const owner = esc(t.owners.join(" & "));
      return `<tr>
        <td class="rank">${i + 1}</td>
        <td>
          <div class="team-name">${esc(t.name)}</div>
          ${owner ? `<div class="owner">${owner}</div>` : ""}
        </td>
        <td class="num">${t.wins}-${t.losses}${t.ties ? "-" + t.ties : ""}</td>
        <td class="num">${fmt(t.pf)}</td>
        <td class="num">${fmt(t.pa)}</td>
        <td class="num">${t.games ? fmt(t.winPct * 100, 0) + "%" : "\u2013"}</td>
      </tr>`;
    })
    .join("");
  return `<table>
    <thead><tr>
      <th class="rank">#</th><th>Team</th><th class="num">W-L</th>
      <th class="num">PF</th><th class="num">PA</th><th class="num">Win%</th>
    </tr></thead>
    <tbody>${rows}</tbody>
  </table>`;
}

function leaguePanel(league, a) {
  const teamName = (id) => esc(league.teams[id].name);

  const high = a.high
    ? `${teamName(a.high.teamId)}<br><small>Week ${a.high.week}</small>`
    : "\u2013";
  const low = a.low
    ? `${teamName(a.low.teamId)}<br><small>Week ${a.low.week}</small>`
    : "\u2013";

  const bestMgr = a.managers[0];
  const worstMgr = a.managers[a.managers.length - 1];
  const luckiest = a.luck[0];
  const unluckiest = a.luck[a.luck.length - 1];

  return `
    <div class="league-head">
      <h2>${esc(league.name)}</h2>
      <span class="meta">${a.n} teams &middot; Weeks 1\u2013${WEEKS} of ${SEASON}</span>
    </div>

    <div class="grid cards">
      <div class="card high">
        <div class="label">Highest scoring week</div>
        <div class="value">${a.high ? fmt(a.high.score) + " <small>pts</small>" : "\u2013"}</div>
        <div class="owner">${high}</div>
      </div>
      <div class="card low">
        <div class="label">Lowest scoring week</div>
        <div class="value">${a.low ? fmt(a.low.score) + " <small>pts</small>" : "\u2013"}</div>
        <div class="owner">${low}</div>
      </div>
      <div class="card">
        <div class="label">Best manager (least bench regret)</div>
        <div class="value">${esc(bestMgr.name)}</div>
        <div class="owner">left ${fmt(bestMgr.regret)} pts on the bench</div>
      </div>
      <div class="card">
        <div class="label">Worst manager (most bench regret)</div>
        <div class="value">${esc(worstMgr.name)}</div>
        <div class="owner">left ${fmt(worstMgr.regret)} pts on the bench</div>
      </div>
      <div class="card">
        <div class="label">Luckiest record</div>
        <div class="value">${esc(luckiest.name)}</div>
        <div class="owner">${fmt(luckiest.luck)} wins above expectation</div>
      </div>
      <div class="card">
        <div class="label">Unluckiest record</div>
        <div class="value">${esc(unluckiest.name)}</div>
        <div class="owner">${fmt(unluckiest.luck)} wins below expectation</div>
      </div>
    </div>

    <div class="panel" style="margin-top:18px">
      <h3>Standings</h3>
      <p class="hint">Through Week ${WEEKS}. Sorted by win%, then points for.</p>
      ${standingsTable(league, a)}
    </div>

    <div class="two-col" style="margin-top:18px">
      <div class="panel">
        <h3>Trophy &amp; plunger count</h3>
        <p class="hint">Weeks a team posted the league's high score (trophy) or low score (plunger).</p>
        <div class="chart-box"><canvas id="tp-${league.id}"></canvas></div>
      </div>
      <div class="panel">
        <h3>Manager quality &mdash; points left on the bench</h3>
        <p class="hint">Total gap between each team's optimal lineup and what they actually started (Weeks 1&ndash;${WEEKS}). Lower is better.</p>
        <div class="chart-box tall"><canvas id="mgr-${league.id}"></canvas></div>
      </div>
    </div>

    <div class="two-col" style="margin-top:18px">
      <div class="panel">
        <h3>Luck &mdash; record vs. all-play record</h3>
        <p class="hint">
          Expected wins come from how each team's weekly score would fare against every other
          team that week (the "all-play" record), scaled to a ${a.standings[0].games}-game schedule.
          Bars above expectation are lucky; below are unlucky.
        </p>
        <div class="chart-box"><canvas id="luck-${league.id}"></canvas></div>
      </div>
      <div class="panel">
        <h3>Most active &mdash; roster moves</h3>
        <p class="hint">Players added and dropped (free agency &amp; waivers) over Weeks 1&ndash;${WEEKS}. Most active at top.</p>
        <div class="chart-box"><canvas id="act-${league.id}"></canvas></div>
      </div>
    </div>
  `;
}

function drawCharts(league, a) {
  const labels = a.standings.map((t) => t.name);
  Chart.defaults.color = CHART.color;
  Chart.defaults.font.family = '"Segoe UI", system-ui, sans-serif';

  // Trophy / plunger grouped bars.
  new Chart(document.getElementById(`tp-${league.id}`), {
    type: "bar",
    data: {
      labels,
      datasets: [
        {
          label: "Trophies (weekly high)",
          data: a.standings.map((t) => a.trophies[t.id]),
          backgroundColor: CHART.gold,
          borderRadius: 5,
        },
        {
          label: "Plungers (weekly low)",
          data: a.standings.map((t) => a.plungers[t.id]),
          backgroundColor: CHART.plunger,
          borderRadius: 5,
        },
      ],
    },
    options: {
      responsive: true,
      maintainAspectRatio: false,
      scales: {
        x: {
          grid: { display: false },
          ticks: { maxRotation: 90, minRotation: 90, autoSkip: false },
        },
        y: { beginAtZero: true, ticks: { stepSize: 1 }, grid: { color: CHART.grid } },
      },
      plugins: { legend: { position: "bottom" } },
    },
  });

  // Manager regret horizontal bars (sorted best -> worst).
  const mgrSorted = [...a.managers].sort((x, y) => y.regret - x.regret); // worst at top for y-axis
  const mgrColors = mgrSorted.map((m, i) => {
    if (i === mgrSorted.length - 1) return CHART.green; // best (lowest regret) at bottom
    if (i === 0) return CHART.red; // worst at top
    return "rgba(62,166,255,.65)";
  });
  new Chart(document.getElementById(`mgr-${league.id}`), {
    type: "bar",
    data: {
      labels: mgrSorted.map((m) => m.name),
      datasets: [
        {
          label: "Points left on bench",
          data: mgrSorted.map((m) => m.regret),
          backgroundColor: mgrColors,
          borderRadius: 5,
        },
      ],
    },
    options: {
      indexAxis: "y",
      responsive: true,
      maintainAspectRatio: false,
      scales: {
        x: { beginAtZero: true, grid: { color: CHART.grid } },
        y: { grid: { display: false } },
      },
      plugins: {
        legend: { display: false },
        tooltip: {
          callbacks: {
            afterLabel: (ctx) => {
              const m = mgrSorted[ctx.dataIndex];
              return `Efficiency: ${fmt(m.eff * 100, 1)}%`;
            },
          },
        },
      },
    },
  });

  // Luck: actual vs expected wins.
  const luckSorted = [...a.luck].sort((x, y) => x.actualWins - y.actualWins);
  new Chart(document.getElementById(`luck-${league.id}`), {
    type: "bar",
    data: {
      labels: luckSorted.map((l) => l.name),
      datasets: [
        {
          label: "Actual wins",
          data: luckSorted.map((l) => l.actualWins),
          backgroundColor: CHART.accent,
          borderRadius: 5,
        },
        {
          label: "Expected wins (all-play)",
          data: luckSorted.map((l) => l.expectedWins),
          backgroundColor: "rgba(255,255,255,.28)",
          borderRadius: 5,
        },
      ],
    },
    options: {
      indexAxis: "y",
      responsive: true,
      maintainAspectRatio: false,
      scales: {
        x: { beginAtZero: true, grid: { color: CHART.grid }, ticks: { stepSize: 1 }, title: { display: true, text: "Wins" } },
        y: { grid: { display: false } },
      },
      plugins: {
        legend: { position: "bottom" },
        tooltip: {
          callbacks: {
            afterBody: (items) => {
              const l = luckSorted[items[0].dataIndex];
              const sign = l.luck >= 0 ? "+" : "";
              return `Luck: ${sign}${fmt(l.luck)} wins  |  All-play: ${fmt(l.allPlayPct * 100, 0)}%`;
            },
          },
        },
      },
    },
  });

  // Roster activity: stacked horizontal bars (most active at top).
  const act = [...a.activity].sort((x, y) => x.total - y.total || x.adds - y.adds);
  new Chart(document.getElementById(`act-${league.id}`), {
    type: "bar",
    data: {
      labels: act.map((x) => x.name),
      datasets: [
        {
          label: "Players added",
          data: act.map((x) => x.adds),
          backgroundColor: CHART.green,
          borderRadius: 5,
          stack: "moves",
        },
        {
          label: "Players dropped",
          data: act.map((x) => x.drops),
          backgroundColor: CHART.red,
          borderRadius: 5,
          stack: "moves",
        },
      ],
    },
    options: {
      indexAxis: "y",
      responsive: true,
      maintainAspectRatio: false,
      scales: {
        x: {
          stacked: true,
          beginAtZero: true,
          grid: { color: CHART.grid },
          ticks: { stepSize: 1 },
          title: { display: true, text: "Roster moves" },
        },
        y: { stacked: true, grid: { display: false } },
      },
      plugins: {
        legend: { position: "bottom" },
        tooltip: {
          callbacks: {
            afterBody: (items) => `Total moves: ${act[items[0].dataIndex].total}`,
          },
        },
      },
    },
  });
}

/* ------------------------------- wiring --------------------------- */

function showOnly(activeId, loaded) {
  document.querySelectorAll(".tab").forEach((b) => {
    b.classList.toggle("active", Number(b.dataset.id) === activeId);
  });
  loaded.forEach(({ id, node }) => {
    node.style.display = id === activeId ? "" : "none";
  });
}

async function main() {
  const tabsEl = document.getElementById("tabs");
  const contentEl = document.getElementById("content");
  contentEl.innerHTML = '<p class="loading">Loading league data from ESPN&hellip;</p>';

  try {
    const loaded = await Promise.all(
      LEAGUES.map(async (cfg) => {
        const league = await loadLeague(cfg);
        const analysis = analyze(league);
        const node = document.createElement("section");
        node.innerHTML = leaguePanel(league, analysis);
        return { id: cfg.id, league, analysis, node };
      })
    );

    contentEl.innerHTML = "";
    loaded.forEach((entry) => contentEl.appendChild(entry.node));

    tabsEl.innerHTML = "";
    loaded.forEach((entry, i) => {
      const btn = document.createElement("button");
      btn.className = "tab";
      btn.dataset.id = entry.id;
      btn.textContent = entry.league.name;
      btn.addEventListener("click", () => showOnly(entry.id, loaded));
      tabsEl.appendChild(btn);
    });

    loaded.forEach((entry) => drawCharts(entry.league, entry.analysis));
    showOnly(loaded[0].id, loaded);
  } catch (err) {
    console.error(err);
    contentEl.innerHTML = `<p class="error">Could not load ESPN data: ${esc(err.message)}. Check your connection and refresh.</p>`;
  }
}

document.addEventListener("DOMContentLoaded", main);
