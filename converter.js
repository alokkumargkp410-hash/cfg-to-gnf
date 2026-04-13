/* =====================================================
   CFG → CNF / GNF Converter Logic  |  converter.js
   ===================================================== */

// ─── State ───────────────────────────────────────────
let currentTarget = 'CNF';
let newVarCounter = 0;

// ─── Sample grammars ─────────────────────────────────
const SAMPLES = {
  cnf1: {
    start: 'S', vars: 'S, A, B', terms: 'a, b',
    prods: 'S → AB | ε\nA → aA | a\nB → bB | b'
  },
  cnf2: {
    start: 'S', vars: 'S, A, B, C', terms: 'a, b, c',
    prods: 'S → ABC | A\nA → aA | ε\nB → bB | b\nC → cC | c'
  },
  gnf1: {
    start: 'S', vars: 'S, A, B', terms: 'a, b',
    prods: 'S → AA | a\nA → SS | b'
  }
};

function loadSample(name) {
  const s = SAMPLES[name];
  document.getElementById('startSymbol').value = s.start;
  document.getElementById('variables').value = s.vars;
  document.getElementById('terminals').value = s.terms;
  document.getElementById('productionInput').value = s.prods;
}

// ─── Target selection ─────────────────────────────────
function selectTarget(t) {
  currentTarget = t;
  document.getElementById('btnCNF').classList.toggle('active', t === 'CNF');
  document.getElementById('btnGNF').classList.toggle('active', t === 'GNF');
}

// ─── Parser ──────────────────────────────────────────
function parseGrammar() {
  const start = document.getElementById('startSymbol').value.trim();
  const vars = document.getElementById('variables').value.split(',').map(v => v.trim()).filter(Boolean);
  const terms = document.getElementById('terminals').value.split(',').map(t => t.trim()).filter(Boolean);
  const rawProds = document.getElementById('productionInput').value.trim();

  const productions = {}; // { LHS: [ [sym, sym, ...], ... ] }
  vars.forEach(v => productions[v] = []);

  for (const line of rawProds.split('\n')) {
    if (!line.trim()) continue;
    const parts = line.split(/→|->/).map(p => p.trim());
    if (parts.length < 2) continue;
    const lhs = parts[0].trim();
    if (!productions[lhs]) productions[lhs] = [];
    const rhs = parts[1].split('|').map(alt => {
      const syms = alt.trim().split(/\s+/).filter(s => s.length > 0);
      return syms.length === 0 ? ['ε'] : syms;
    });
    productions[lhs].push(...rhs);
  }

  return { start, vars: [...vars], terms: [...terms], productions };
}

// ─── Deep clone grammar ───────────────────────────────
function cloneGrammar(g) {
  return {
    start: g.start,
    vars: [...g.vars],
    terms: [...g.terms],
    productions: Object.fromEntries(
      Object.entries(g.productions).map(([k, v]) => [k, v.map(alt => [...alt])])
    )
  };
}

function prodStr(g) {
  return Object.entries(g.productions).map(([lhs, rhs]) =>
    lhs + ' → ' + rhs.map(a => a.join(' ')).join(' | ')
  ).join('\n');
}

// ─── Helpers ──────────────────────────────────────────
function freshVar(existing, prefix = 'X') {
  let i = 1;
  while (existing.has(`${prefix}${i}`)) i++;
  return `${prefix}${i}`;
}
function allVars(g) { return new Set(g.vars); }
function isVar(sym, g) { return g.vars.includes(sym); }
function isTerminal(sym, g) { return g.terms.includes(sym); }
function isEpsilon(sym) { return sym === 'ε' || sym === 'eps' || sym === ''; }

// ─── STEP: Remove Useless Symbols ─────────────────────
function removeUseless(g) {
  const log = [];

  // 1. Find generating symbols (can derive a terminal string)
  const generating = new Set();
  let changed = true;
  // terminals are "generating"
  g.terms.forEach(t => generating.add(t));
  generating.add('ε');

  while (changed) {
    changed = false;
    for (const [A, prods] of Object.entries(g.productions)) {
      if (generating.has(A)) continue;
      for (const alt of prods) {
        if (alt.every(sym => generating.has(sym))) {
          generating.add(A);
          changed = true;
          break;
        }
      }
    }
  }

  const uselessNonGen = g.vars.filter(v => !generating.has(v));

  // Remove non-generating
  const ng = cloneGrammar(g);
  if (uselessNonGen.length) {
    uselessNonGen.forEach(v => {
      delete ng.productions[v];
      ng.vars = ng.vars.filter(x => x !== v);
    });
    // Remove productions containing non-generating symbols
    for (const A of ng.vars) {
      ng.productions[A] = ng.productions[A].filter(alt =>
        alt.every(sym => generating.has(sym) || ng.vars.includes(sym))
      );
    }
    log.push({ type: 'removed', text: `Non-generating: ${uselessNonGen.join(', ')}` });
  }

  // 2. Find reachable symbols
  const reachable = new Set([ng.start]);
  changed = true;
  while (changed) {
    changed = false;
    for (const A of [...reachable]) {
      for (const alt of (ng.productions[A] || [])) {
        for (const sym of alt) {
          if (!reachable.has(sym)) { reachable.add(sym); changed = true; }
        }
      }
    }
  }

  const unreachable = ng.vars.filter(v => !reachable.has(v));
  if (unreachable.length) {
    unreachable.forEach(v => {
      delete ng.productions[v];
      ng.vars = ng.vars.filter(x => x !== v);
    });
    ng.terms = ng.terms.filter(t => reachable.has(t));
    log.push({ type: 'removed', text: `Unreachable: ${unreachable.join(', ')}` });
  }

  if (!log.length) log.push({ type: 'info', text: 'No useless symbols found' });

  return { grammar: ng, log };
}

// ─── STEP: Remove ε-Productions ───────────────────────
function removeEpsilon(g) {
  const log = [];

  // Find nullable variables
  const nullable = new Set();
  let changed = true;
  // directly nullable
  for (const [A, prods] of Object.entries(g.productions)) {
    if (prods.some(alt => alt.length === 1 && isEpsilon(alt[0]))) nullable.add(A);
  }
  while (changed) {
    changed = false;
    for (const [A, prods] of Object.entries(g.productions)) {
      if (nullable.has(A)) continue;
      if (prods.some(alt => alt.every(s => nullable.has(s)))) {
        nullable.add(A); changed = true;
      }
    }
  }

  if (!nullable.size) {
    log.push({ type: 'info', text: 'No ε-productions found' });
    return { grammar: cloneGrammar(g), log };
  }

  log.push({ type: 'info', text: `Nullable: { ${[...nullable].join(', ')} }` });

  const ng = cloneGrammar(g);
  const startWasNullable = nullable.has(g.start);

  // For each production, generate combinations without nullable vars
  for (const A of ng.vars) {
    const newProds = new Set();
    for (const alt of ng.productions[A]) {
      // find positions of nullable symbols
      const nullablePos = alt.map((s, i) => nullable.has(s) ? i : -1).filter(i => i >= 0);
      const combos = Math.pow(2, nullablePos.length);
      for (let mask = 0; mask < combos; mask++) {
        const newAlt = alt.filter((s, i) => {
          const nIdx = nullablePos.indexOf(i);
          if (nIdx === -1) return true;
          return !((mask >> nIdx) & 1);
        });
        if (newAlt.length > 0) newProds.add(newAlt.join(' '));
      }
    }
    ng.productions[A] = [...newProds].map(s => s.split(' '));
  }

  // Remove ε from all productions (except if start was nullable — add special rule)
  for (const A of ng.vars) {
    ng.productions[A] = ng.productions[A].filter(alt => !(alt.length === 1 && isEpsilon(alt[0])));
  }

  if (startWasNullable) {
    // Create new start symbol
    const S0 = g.start + '0';
    ng.vars = [S0, ...ng.vars];
    ng.productions[S0] = [[g.start], ['ε']];
    ng.start = S0;
    log.push({ type: 'added', text: `New start: ${S0} → ${g.start} | ε (language includes ε)` });
  }

  log.push({ type: 'removed', text: `Removed ε-productions from all variables` });

  return { grammar: ng, log };
}

// ─── STEP: Remove Unit Productions ───────────────────
function removeUnit(g) {
  const log = [];
  const ng = cloneGrammar(g);
  let anyRemoved = false;

  for (const A of ng.vars) {
    // Find unit closure of A
    const unitClosure = new Set([A]);
    let changed = true;
    while (changed) {
      changed = false;
      for (const B of [...unitClosure]) {
        for (const alt of (ng.productions[B] || [])) {
          if (alt.length === 1 && isVar(alt[0], ng) && !unitClosure.has(alt[0])) {
            unitClosure.add(alt[0]); changed = true;
          }
        }
      }
    }
    unitClosure.delete(A);

    if (unitClosure.size) {
      anyRemoved = true;
      log.push({ type: 'info', text: `Unit closure of ${A}: {${[...unitClosure].join(', ')}}` });
    }

    // Add non-unit productions from closure
    for (const B of unitClosure) {
      for (const alt of (ng.productions[B] || [])) {
        if (!(alt.length === 1 && isVar(alt[0], ng))) {
          const key = alt.join(' ');
          if (!ng.productions[A].some(p => p.join(' ') === key)) {
            ng.productions[A].push([...alt]);
            log.push({ type: 'added', text: `Added ${A} → ${alt.join(' ')} (from ${B})` });
          }
        }
      }
    }
  }

  // Remove all unit productions
  for (const A of ng.vars) {
    ng.productions[A] = ng.productions[A].filter(alt =>
      !(alt.length === 1 && isVar(alt[0], ng))
    );
  }

  if (!anyRemoved) log.push({ type: 'info', text: 'No unit productions found' });
  else log.push({ type: 'removed', text: 'All unit productions removed' });

  return { grammar: ng, log };
}

// ─── STEP CNF: Break Long Productions ─────────────────
function breakLong(g) {
  const log = [];
  const ng = cloneGrammar(g);
  const existing = allVars(ng);
  let anyBroke = false;

  // Map from sequence → new variable (to reuse)
  const seqMap = {};

  const getOrCreate = (seq) => {
    const key = seq.join(' ');
    if (seqMap[key]) return seqMap[key];
    const v = freshVar(existing, 'B');
    existing.add(v);
    ng.vars.push(v);
    ng.productions[v] = [seq];
    seqMap[key] = v;
    log.push({ type: 'added', text: `New: ${v} → ${seq.join(' ')}` });
    return v;
  };

  for (const A of [...ng.vars]) {
    const newProds = [];
    for (const alt of ng.productions[A]) {
      if (alt.length <= 2) { newProds.push(alt); continue; }
      anyBroke = true;
      // Break: A → X1 X2 ... Xn  becomes A → X1 V1, V1 → X2 V2, ...
      let cur = alt;
      let lhs = A;
      const chain = [];
      while (cur.length > 2) {
        const rest = cur.slice(1);
        const v = getOrCreate(rest);
        chain.push([cur[0], v]);
        cur = rest;
      }
      newProds.push(chain[0]);
    }
    ng.productions[A] = newProds;
  }

  if (!anyBroke) log.push({ type: 'info', text: 'No productions of length > 2 found' });
  else log.push({ type: 'removed', text: 'All long productions broken into binary rules' });

  return { grammar: ng, log };
}

// ─── STEP CNF: Replace Terminals in Binary+ Rules ─────
function replaceTerminals(g) {
  const log = [];
  const ng = cloneGrammar(g);
  const existing = allVars(ng);
  const termMap = {};

  const getTermVar = (t) => {
    if (termMap[t]) return termMap[t];
    const v = freshVar(existing, 'T');
    existing.add(v);
    ng.vars.push(v);
    ng.productions[v] = [[t]];
    termMap[t] = v;
    log.push({ type: 'added', text: `New: ${v} → ${t}` });
    return v;
  };

  let anyReplaced = false;
  for (const A of [...ng.vars]) {
    ng.productions[A] = ng.productions[A].map(alt => {
      if (alt.length < 2) return alt;
      return alt.map(sym => {
        if (isTerminal(sym, ng)) { anyReplaced = true; return getTermVar(sym); }
        return sym;
      });
    });
  }

  if (!anyReplaced) log.push({ type: 'info', text: 'No terminal replacements needed' });
  else log.push({ type: 'info', text: 'Terminals in binary rules replaced with new variables' });

  return { grammar: ng, log };
}

// ─── STEP GNF: Remove Left Recursion ──────────────────
function removeLeftRecursion(g) {
  const log = [];
  const ng = cloneGrammar(g);
  const existing = allVars(ng);
  let anyFound = false;

  // Order variables
  const vars = [...ng.vars];

  for (let i = 0; i < vars.length; i++) {
    const Ai = vars[i];
    // Substitute Aj (j < i) at the front
    for (let j = 0; j < i; j++) {
      const Aj = vars[j];
      const newProds = [];
      for (const alt of ng.productions[Ai]) {
        if (alt[0] === Aj) {
          for (const ajAlt of ng.productions[Aj]) {
            newProds.push([...ajAlt, ...alt.slice(1)]);
          }
          log.push({ type: 'info', text: `Substituted ${Aj} in ${Ai} → ${alt.join(' ')}` });
        } else {
          newProds.push(alt);
        }
      }
      ng.productions[Ai] = newProds;
    }

    // Now remove direct left recursion from Ai
    const recursive = ng.productions[Ai].filter(alt => alt[0] === Ai);
    const nonRecursive = ng.productions[Ai].filter(alt => alt[0] !== Ai);

    if (recursive.length) {
      anyFound = true;
      const Ai1 = freshVar(existing, Ai + "'");
      existing.add(Ai1);
      vars.push(Ai1);
      ng.vars.push(Ai1);

      // Ai → β Ai' for each non-recursive β
      ng.productions[Ai] = nonRecursive.map(alt => [...alt, Ai1]);
      // Ai' → α Ai' | ε for each recursive α
      ng.productions[Ai1] = [
        ...recursive.map(alt => [...alt.slice(1), Ai1]),
        ['ε']
      ];
      log.push({ type: 'added', text: `Eliminated left recursion from ${Ai}, added ${Ai1}` });
    }
  }

  if (!anyFound) log.push({ type: 'info', text: 'No left recursion found' });

  return { grammar: ng, log };
}

// ─── STEP GNF: Substitute to ensure GNF ───────────────
function substituteForGNF(g) {
  const log = [];
  const ng = cloneGrammar(g);
  const existing = allVars(ng);
  const termMap = {};
  let iterations = 0;
  const MAX_ITER = 20;

  const getTermVar = (t) => {
    if (termMap[t]) return termMap[t];
    const v = freshVar(existing, 'T');
    existing.add(v);
    ng.vars.push(v);
    ng.productions[v] = [[t]];
    termMap[t] = v;
    log.push({ type: 'added', text: `New: ${v} → ${t}` });
    return v;
  };

  let changed = true;
  while (changed && iterations < MAX_ITER) {
    changed = false; iterations++;
    for (const A of [...ng.vars]) {
      const newProds = [];
      for (const alt of ng.productions[A]) {
        if (alt.length === 0) { newProds.push(alt); continue; }
        const first = alt[0];
        if (isTerminal(first, ng) || isEpsilon(first)) {
          newProds.push(alt);
        } else if (isVar(first, ng) && ng.productions[first]) {
          // Substitute
          for (const sub of ng.productions[first]) {
            newProds.push([...sub, ...alt.slice(1)]);
          }
          changed = true;
          log.push({ type: 'info', text: `Substituted ${first} in ${A} → ${alt.join(' ')}` });
        } else {
          newProds.push(alt);
        }
      }
      // Deduplicate
      const seen = new Set();
      ng.productions[A] = newProds.filter(p => {
        const k = p.join(' ');
        if (seen.has(k)) return false;
        seen.add(k); return true;
      });
    }
  }

  if (!log.length) log.push({ type: 'info', text: 'Grammar already starts with terminals' });
  log.push({ type: 'added', text: 'All productions now begin with a terminal' });

  return { grammar: ng, log };
}

// ─── Render grammar ───────────────────────────────────
function renderGrammar(g, highlightNew = [], highlightRemoved = []) {
  let html = '<div class="grammar-display">';
  for (const [lhs, prods] of Object.entries(g.productions)) {
    if (!prods.length) continue;
    const rhsStr = prods.map(alt => {
      return alt.map(sym => {
        let cls = '';
        if (g.terms.includes(sym)) cls = 'terminal';
        return `<span class="${cls}">${sym}</span>`;
      }).join(' ');
    }).join(' <span class="prod-arrow">|</span> ');
    const lhsCls = highlightNew.includes(lhs) ? 'prod-new' : '';
    html += `<div><span class="prod-lhs ${lhsCls}">${lhs}</span><span class="prod-arrow"> → </span><span class="prod-rhs">${rhsStr}</span></div>`;
  }
  html += '</div>';
  return html;
}

// ─── Render step card ─────────────────────────────────
function renderStep(num, title, subtitle, desc, changes, grammar, isGNF = false, open = false) {
  const numClass = isGNF ? 'gnf' : '';
  const highlightClass = isGNF ? 'gnf-highlighted' : 'highlighted';
  const openClass = open ? 'open' : '';

  const changeHtml = changes.map(c =>
    `<div class="change-tag ${c.type}"><div class="change-dot"></div>${c.text}</div>`
  ).join('');

  return `
    <div class="step-card ${openClass}" id="step-${num}">
      <div class="step-header" onclick="toggleStep('step-${num}', '${highlightClass}')">
        <div class="step-num ${numClass}">${num}</div>
        <div style="flex:1">
          <div class="step-title">${title}</div>
          <div class="step-subtitle">${subtitle}</div>
        </div>
        <div class="step-toggle">▶</div>
      </div>
      <div class="step-body">
        <p class="step-description">${desc}</p>
        <div class="changes-list">${changeHtml}</div>
        <div class="card-label" style="margin-bottom:0.5rem;font-size:0.62rem">RESULTING GRAMMAR</div>
        ${renderGrammar(grammar)}
      </div>
    </div>
  `;
}

function toggleStep(id, highlightClass) {
  const el = document.getElementById(id);
  el.classList.toggle('open');
  el.classList.toggle(highlightClass, el.classList.contains('open'));
}

// ─── Build pipeline HTML ─────────────────────────────
function buildPipeline(steps, isGNF) {
  const cls = isGNF ? 'gnf-active' : 'active';
  return steps.map((s, i) =>
    `<div class="pipe-step">
      <div class="pipe-label ${cls}" onclick="document.getElementById('step-${i+1}').scrollIntoView({behavior:'smooth'})">${s}</div>
      ${i < steps.length - 1 ? '<div class="pipe-arrow">→</div>' : ''}
    </div>`
  ).join('');
}

// ─── Main conversion runner ───────────────────────────
function runConversion() {
  newVarCounter = 0;
  let g;
  try {
    g = parseGrammar();
    if (!g.vars.length || !g.start) throw new Error('Please fill in all grammar fields.');
  } catch (e) {
    showError(e.message); return;
  }

  const isGNF = currentTarget === 'GNF';
  const stepsSection = document.getElementById('stepsSection');
  const stepsContent = document.getElementById('stepsContent');
  const finalResult = document.getElementById('finalResult');
  const pipeline = document.getElementById('pipeline');
  document.getElementById('stepsLabel').textContent = `CFG → ${currentTarget} CONVERSION`;

  let steps = [];
  let stepsHtml = '';

  if (!isGNF) {
    // CNF pipeline
    const pipeNames = ['Useless', 'ε-Removal', 'Unit', 'Break', 'Replace'];
    pipeline.innerHTML = buildPipeline(pipeNames, false);

    const r1 = removeUseless(g);
    const r2 = removeEpsilon(r1.grammar);
    const r3 = removeUnit(r2.grammar);
    const r4 = breakLong(r3.grammar);
    const r5 = replaceTerminals(r4.grammar);

    stepsHtml += renderStep(1, 'Remove Useless Symbols', 'Eliminate non-generating & unreachable',
      'Remove variables that cannot derive any terminal string (non-generating), and variables that cannot be reached from the start symbol (unreachable).',
      r1.log, r1.grammar, false, true);
    stepsHtml += renderStep(2, 'Remove ε-Productions', 'Eliminate nullable variables',
      'Find all nullable variables (those that can derive ε), then generate new productions that omit each nullable variable in every possible combination.',
      r2.log, r2.grammar);
    stepsHtml += renderStep(3, 'Remove Unit Productions', 'Eliminate A → B rules',
      'Find unit closure for each variable, then replace unit productions with the actual productions they ultimately derive, forming no A → B single-variable rules.',
      r3.log, r3.grammar);
    stepsHtml += renderStep(4, 'Break Long Productions', 'Ensure all RHS have ≤ 2 symbols',
      'For every production with 3 or more symbols on the right-hand side, introduce new variables to break it into a chain of binary productions.',
      r4.log, r4.grammar);
    stepsHtml += renderStep(5, 'Replace Terminals in Binary Rules', 'Ensure binary rules have only variables',
      'For every terminal that appears in a production alongside another symbol, introduce a new unit production variable Tₓ → x and replace the terminal.',
      r5.log, r5.grammar);

    finalResult.className = 'final-result';
    finalResult.innerHTML = `
      <div class="final-badge">CNF COMPLETE</div>
      <div class="final-title">Chomsky Normal Form</div>
      <div class="final-subtitle">Every production is either A → BC (two variables) or A → a (single terminal)</div>
      ${renderGrammar(r5.grammar)}
    `;
  } else {
    // GNF pipeline
    const pipeNames = ['Useless', 'ε-Removal', 'Unit', 'Left Rec', 'Substitute'];
    pipeline.innerHTML = buildPipeline(pipeNames, true);

    const r1 = removeUseless(g);
    const r2 = removeEpsilon(r1.grammar);
    const r3 = removeUnit(r2.grammar);
    const r4 = removeLeftRecursion(r3.grammar);
    const r5 = substituteForGNF(r4.grammar);

    stepsHtml += renderStep(1, 'Remove Useless Symbols', 'Eliminate non-generating & unreachable',
      'Remove variables that cannot derive any terminal string (non-generating), and variables that cannot be reached from the start symbol (unreachable).',
      r1.log, r1.grammar, true, true);
    stepsHtml += renderStep(2, 'Remove ε-Productions', 'Eliminate nullable variables',
      'Find all nullable variables and eliminate all ε-productions by generating all possible combinations without the nullable variable.',
      r2.log, r2.grammar, true);
    stepsHtml += renderStep(3, 'Remove Unit Productions', 'Eliminate A → B rules',
      'Compute unit closure for each variable and add all non-unit productions reachable via unit chains, then remove unit rules.',
      r3.log, r3.grammar, true);
    stepsHtml += renderStep(4, 'Eliminate Left Recursion', 'Remove A → Aα rules',
      'For each variable with left recursion A → Aα, introduce a new variable A\' and rewrite as A → βA\' and A\' → αA\' | ε to eliminate the recursion.',
      r4.log, r4.grammar, true);
    stepsHtml += renderStep(5, 'Substitute to GNF Form', 'Ensure all RHS begin with terminal',
      'Substitute productions so every right-hand side starts with a terminal symbol, followed only by variables. This achieves full Greibach Normal Form.',
      r5.log, r5.grammar, true);

    finalResult.className = 'final-result gnf-final';
    finalResult.innerHTML = `
      <div class="final-badge">GNF COMPLETE</div>
      <div class="final-title">Greibach Normal Form</div>
      <div class="final-subtitle">Every production is A → aα where a is a terminal and α is a (possibly empty) string of variables</div>
      ${renderGrammar(r5.grammar)}
    `;
  }

  stepsContent.innerHTML = stepsHtml;
  stepsSection.style.display = 'flex';
  setTimeout(() => stepsSection.scrollIntoView({ behavior: 'smooth', block: 'start' }), 100);
}

function showError(msg) {
  const sec = document.getElementById('stepsSection');
  sec.style.display = 'flex';
  document.getElementById('stepsContent').innerHTML = `<div class="error-box">⚠ ${msg}</div>`;
  document.getElementById('finalResult').innerHTML = '';
  document.getElementById('pipeline').innerHTML = '';
}

// ─── Load default sample ──────────────────────────────
loadSample('cnf1');
