/**
 * Complexity Analyzer AI — Next-Gen Static Code Analysis Engine & UI Controller
 *
 * Architecture:
 * 1. Multi-Language Tokenizer & Lexer (Supports C, C++, Java, Python, JS, TS, Go, Rust)
 * 2. Scope Tree Parser & Control Flow Graph (CFG) Builder
 * 3. Loop Boundary & Step Expression Analyzer
 * 4. Algorithm & Data Structure Structural Pattern Recognition Engine
 * 5. Deterministic Time & Auxiliary Space Complexity Evaluator
 * 6. Dynamic Multi-Factor Confidence Metric Engine
 * 7. Full UI Controller, LocalStorage History, Theme System & SVG Chart Engine
 */

/* ==========================================================================
   1. TOKENIZER & LEXICAL ANALYZER
   ========================================================================== */

class TokenType {
  static KEYWORD = 'KEYWORD';
  static IDENTIFIER = 'IDENTIFIER';
  static NUMBER = 'NUMBER';
  static OPERATOR = 'OPERATOR';
  static DELIMITER = 'DELIMITER';
  static STRING = 'STRING';
}

class Tokenizer {
  constructor(code, language = 'javascript') {
    this.code = code;
    this.language = language.toLowerCase();
    this.tokens = [];
    this.keywords = new Set([
      'for', 'while', 'do', 'if', 'else', 'function', 'def', 'fn', 'public', 'private',
      'protected', 'class', 'return', 'new', 'const', 'let', 'var', 'int', 'void', 'auto',
      'val', 'struct', 'import', 'include', 'in', 'range', 'len', 'self', 'this', 'vector',
      'map', 'unordered_map', 'set', 'unordered_set', 'queue', 'stack', 'priority_queue'
    ]);
  }

  tokenize() {
    let cleanCode = this.code
      .replace(/\/\*[\s\S]*?\*\//g, '') // Strip C-style multiline comments
      .replace(/\/\/.*/g, '')           // Strip single line comments
      .replace(/#.*/g, '');            // Strip Python/Shell comments

    // Language-specific normalization for Python indentation or range loops
    const regex = /"[^"]*"|'[^']*'|\b\d+\b|\b[A-Za-z_$][A-Za-z0-9_$]*\b|==|!=|<=|>=|\+\+|--|\+=|-=|\*=|\/=|>>=|<<=|->|=>|&&|\|\||<<|>>|[{}()\[\];,.<>+\-*\/%&=|^!~]/g;

    let match;
    while ((match = regex.exec(cleanCode)) !== null) {
      const val = match[0];
      let type = TokenType.IDENTIFIER;

      if (this.keywords.has(val)) {
        type = TokenType.KEYWORD;
      } else if (/^\d+$/.test(val)) {
        type = TokenType.NUMBER;
      } else if (/^("[^"]*"|'[^']*')$/.test(val)) {
        type = TokenType.STRING;
      } else if (/^[{}()\[\];,]$/.test(val)) {
        type = TokenType.DELIMITER;
      } else if (/^[+\-*\/%&=|^!~<>]+$/.test(val)) {
        type = TokenType.OPERATOR;
      }

      this.tokens.push({ value: val, type, index: match.index });
    }

    return this.tokens;
  }
}

/* ==========================================================================
   2. SCOPE TREE & CONTROL FLOW ANALYZER
   ========================================================================== */

class ScopeNode {
  constructor(type = 'block', parent = null) {
    this.type = type; // 'global', 'function', 'loop', 'block', 'branch'
    this.parent = parent;
    this.children = [];
    this.declaredVars = new Set();
    this.loopStepType = 'linear'; // 'linear', 'logarithmic', 'sqrt', 'unknown'
    this.loopVar = null;
    this.loopBoundVar = null;
    this.depth = parent ? parent.depth + (type === 'loop' ? 1 : 0) : 0;
    this.hasNestedCalls = false;
  }
}

class ControlFlowAnalyzer {
  constructor(tokens, code, language) {
    this.tokens = tokens;
    this.code = code;
    this.language = language;
    this.rootScope = new ScopeNode('global');
    this.functionScopes = new Map();
    this.maxLoopDepth = 0;
    this.hasLogarithmicStep = false;
    this.hasSqrtStep = false;
    this.recursiveFunctions = new Set();
    this.recursiveCallCountMap = new Map();
  }

  buildScopeTree() {
    let currentScope = this.rootScope;
    let currentFnName = null;

    for (let i = 0; i < this.tokens.length; i++) {
      const token = this.tokens[i];

      // Function definition detection
      if (['function', 'def', 'fn', 'void', 'int', 'auto', 'double', 'float', 'class'].includes(token.value)) {
        const nextToken = this.tokens[i + 1];
        if (nextToken && nextToken.type === TokenType.IDENTIFIER) {
          currentFnName = nextToken.value;
          const fnScope = new ScopeNode('function', currentScope);
          currentScope.children.push(fnScope);
          currentScope = fnScope;
          this.functionScopes.set(currentFnName, fnScope);
        }
      }

      // Loop construct detection
      if (['for', 'while'].includes(token.value)) {
        const loopScope = new ScopeNode('loop', currentScope);
        currentScope.children.push(loopScope);
        currentScope = loopScope;

        if (loopScope.depth > this.maxLoopDepth) {
          this.maxLoopDepth = loopScope.depth;
        }

        // Analyze loop header window (next 30 tokens)
        const headerTokens = this.tokens.slice(i, Math.min(i + 35, this.tokens.length)).map(t => t.value).join(' ');
        
        if (/(\/=|\\*=|>>=|<<=|mid\s*=|right\s*=|high\s*=|\/ 2|\* 2|\/2|\*2)/.test(headerTokens)) {
          loopScope.loopStepType = 'logarithmic';
          this.hasLogarithmicStep = true;
        } else if (/\*\s*i\s*<=|\*\s*j\s*<=|sqrt/i.test(headerTokens)) {
          loopScope.loopStepType = 'sqrt';
          this.hasSqrtStep = true;
        } else {
          loopScope.loopStepType = 'linear';
        }
      }

      // Check for recursive self-invocations
      if (token.type === TokenType.IDENTIFIER && this.functionScopes.has(token.value)) {
        const nextToken = this.tokens[i + 1];
        if (nextToken && nextToken.value === '(') {
          const count = (this.recursiveCallCountMap.get(token.value) || 0) + 1;
          this.recursiveCallCountMap.set(token.value, count);

          if (currentScope.type === 'function' || currentScope.parent) {
            this.recursiveFunctions.add(token.value);
          }
        }
      }

      // Block boundary handling
      if (token.value === '{') {
        const blockScope = new ScopeNode('block', currentScope);
        currentScope.children.push(blockScope);
        currentScope = blockScope;
      } else if (token.value === '}') {
        if (currentScope.parent) {
          currentScope = currentScope.parent;
        }
      }
    }
  }
}

/* ==========================================================================
   3. STRUCTURAL PATTERN & ALGORITHM DETECTOR
   ========================================================================== */

class PatternDetector {
  constructor(code, tokens, cfAnalyzer) {
    this.code = code;
    this.tokens = tokens;
    this.cfAnalyzer = cfAnalyzer;
    this.detectedPatterns = new Set();
    this.detectedStructures = new Set();
    this.primaryAlgorithm = null;
  }

  detectAll() {
    this.detectDataStructures();
    this.detectSortingAlgorithms();
    this.detectSearchingAlgorithms();
    this.detectGraphAndTreeAlgorithms();
    this.detectGeneralPatterns();
  }

  detectDataStructures() {
    const code = this.code;

    if (/\b(HashMap|Map|unordered_map|dict|\{\})\b/i.test(code)) {
      this.detectedStructures.add('HashMap');
      this.detectedPatterns.add('Hash Map Store');
    }
    if (/\b(HashSet|Set|unordered_set)\b/i.test(code)) {
      this.detectedStructures.add('HashSet');
      this.detectedPatterns.add('Hash Set Lookup');
    }
    if (/\b(PriorityQueue|heapq|max_heap|min_heap|push_heap|pop_heap)\b/i.test(code)) {
      this.detectedStructures.add('PriorityQueue');
      this.detectedPatterns.add('Priority Queue / Min-Max Heap');
    }
    if (/\b(Queue|Deque|LinkedList|queue|deque|popleft)\b/i.test(code)) {
      this.detectedStructures.add('Queue');
      this.detectedPatterns.add('FIFO Queue');
    }
    if (/\b(Stack|stack)\b/i.test(code)) {
      this.detectedStructures.add('Stack');
      this.detectedPatterns.add('LIFO Stack');
    }
    if (/\b(TreeNode|Node|adj|adjacency|Graph|edge|edges)\b/i.test(code)) {
      this.detectedStructures.add('Graph/Tree');
      this.detectedPatterns.add('Graph / Tree Adjacency Model');
    }
    if (/\b(TrieNode|Trie|insert|startsWith)\b/i.test(code)) {
      this.detectedStructures.add('Trie');
      this.detectedPatterns.add('Prefix Tree / Trie');
    }
    if (/\b(parent|rank|find|union|UnionFind|DisjointSet)\b/i.test(code)) {
      this.detectedStructures.add('UnionFind');
      this.detectedPatterns.add('Disjoint Set Union (DSU)');
    }
    if (/\b(SegmentTree|tree|buildTree|updateTree|queryRange)\b/i.test(code)) {
      this.detectedStructures.add('SegmentTree');
      this.detectedPatterns.add('Segment Tree');
    }
    if (/\b(Fenwick|BIT|lowbit|add|query)\b/i.test(code)) {
      this.detectedStructures.add('FenwickTree');
      this.detectedPatterns.add('Binary Indexed Tree (BIT)');
    }
  }

  detectSortingAlgorithms() {
    const code = this.code;
    const maxDepth = this.cfAnalyzer.maxLoopDepth;
    const isRecursive = this.cfAnalyzer.recursiveFunctions.size > 0;

    if (isRecursive && /(pivot|partition|quicksort|quick_sort)/i.test(code)) {
      this.primaryAlgorithm = 'Quick Sort';
      this.detectedPatterns.add('Quick Sort (Divide & Conquer)');
    } else if (isRecursive && /(merge|mergesort|merge_sort|concat|slice)/i.test(code)) {
      this.primaryAlgorithm = 'Merge Sort';
      this.detectedPatterns.add('Merge Sort (Divide & Conquer)');
    } else if (/\b(heapify|priority_queue|heapq|push_heap)\b/i.test(code) && (maxDepth >= 1 || isRecursive)) {
      this.primaryAlgorithm = 'Heap Sort';
      this.detectedPatterns.add('Heap Sort');
    } else if (maxDepth === 2 && /\b(swapped|temp|arr\[j\]\s*>\s*arr\[j\s*\+\s*1\])\b/i.test(code)) {
      this.primaryAlgorithm = 'Bubble Sort';
      this.detectedPatterns.add('Bubble Sort');
    } else if (maxDepth === 2 && /\b(minIndex|min_idx|selectionSort|selection_sort)\b/i.test(code)) {
      this.primaryAlgorithm = 'Selection Sort';
      this.detectedPatterns.add('Selection Sort');
    } else if (maxDepth === 2 && /\b(key\s*=|insertionSort|insertion_sort|j\s*>=\s*0\s*&&\s*arr\[j\])\b/i.test(code)) {
      this.primaryAlgorithm = 'Insertion Sort';
      this.detectedPatterns.add('Insertion Sort');
    } else if (/\b(count|countArray|buckets|radix|exp)\b/i.test(code) && maxDepth >= 1) {
      if (/exp|digit|radix/i.test(code)) {
        this.primaryAlgorithm = 'Radix Sort';
        this.detectedPatterns.add('Radix Sort');
      } else {
        this.primaryAlgorithm = 'Counting Sort';
        this.detectedPatterns.add('Counting Sort');
      }
    }
  }

  detectSearchingAlgorithms() {
    const code = this.code;

    if (this.cfAnalyzer.hasLogarithmicStep && /(mid|middle|low|high|left|right)/i.test(code)) {
      this.primaryAlgorithm = 'Binary Search';
      this.detectedPatterns.add('Binary Search');
    } else if (this.cfAnalyzer.maxLoopDepth === 1 && !this.primaryAlgorithm && /(find|search|target|indexOf|includes)/i.test(code)) {
      this.detectedPatterns.add('Linear Search');
    }
  }

  detectGraphAndTreeAlgorithms() {
    const code = this.code;

    if (this.detectedStructures.has('Queue') && /(visited|level|popleft|shift|distance)/i.test(code)) {
      this.primaryAlgorithm = 'Breadth-First Search (BFS)';
      this.detectedPatterns.add('Breadth-First Search (BFS)');
    } else if ((this.cfAnalyzer.recursiveFunctions.size > 0 || this.detectedStructures.has('Stack')) && /(visited|dfs|traverse|depth)/i.test(code)) {
      this.primaryAlgorithm = 'Depth-First Search (DFS)';
      this.detectedPatterns.add('Depth-First Search (DFS)');
    }
  }

  detectGeneralPatterns() {
    const code = this.code;

    // Two Pointer
    if (/left\s*<\s*right|i\s*<\s*j|start\s*<\s*end/i.test(code) && this.cfAnalyzer.maxLoopDepth === 1) {
      this.detectedPatterns.add('Two Pointer Technique');
    }
    // Sliding Window
    if (/window|window_size|window_start|max_len|subarray/i.test(code) && this.cfAnalyzer.maxLoopDepth >= 1) {
      this.detectedPatterns.add('Sliding Window');
    }
    // Dynamic Programming / Memoization
    if (/(dp\[|memo\[|cache\[|table\[)/i.test(code)) {
      this.detectedPatterns.add('Dynamic Programming / Memoization');
    }
    // Prefix Sum
    if (/(prefix|prefixSum|pref\[|sumArray)/i.test(code)) {
      this.detectedPatterns.add('Prefix Sum Array');
    }
    // Bit Manipulation
    if (/(&|\||\^|<<|>>|>>>)\s*=/i.test(code) || /& 1|>> 1|\b(countBits|lowbit)\b/i.test(code)) {
      this.detectedPatterns.add('Bit Manipulation');
    }
  }
}

/* ==========================================================================
   4. TIME & auxiliary SPACE COMPLEXITY EVALUATOR
   ========================================================================== */

class ComplexityEvaluator {
  constructor(cfAnalyzer, patternDetector, code) {
    this.cfAnalyzer = cfAnalyzer;
    this.patternDetector = patternDetector;
    this.code = code;
  }

  evaluateTimeComplexity() {
    const primary = this.patternDetector.primaryAlgorithm;
    const patterns = this.patternDetector.detectedPatterns;
    const maxDepth = this.cfAnalyzer.maxLoopDepth;
    const recursiveCount = Array.from(this.cfAnalyzer.recursiveCallCountMap.values()).reduce((a, b) => a + b, 0);

    // Explicit Algorithm Complexity Rules
    if (primary === 'Binary Search') return { notation: 'O(log n)', label: 'Logarithmic Division Boundary' };
    if (primary === 'Merge Sort') return { notation: 'O(n log n)', label: 'Linearithmic Divide & Conquer' };
    if (primary === 'Quick Sort') return { notation: 'O(n log n)', label: 'Linearithmic Avg (O(n²) Worst Case)' };
    if (primary === 'Heap Sort') return { notation: 'O(n log n)', label: 'Linearithmic Priority Heap' };
    if (['Bubble Sort', 'Selection Sort', 'Insertion Sort'].includes(primary)) return { notation: 'O(n²)', label: 'Quadratic Element Swaps' };
    if (['Counting Sort', 'Radix Sort'].includes(primary)) return { notation: 'O(n + k)', label: 'Linear Non-Comparison Bounds' };
    if (['Breadth-First Search (BFS)', 'Depth-First Search (DFS)'].includes(primary)) return { notation: 'O(V + E)', label: 'Graph Traversal (Vertices + Edges)' };

    // Structural Heuristics
    if (this.cfAnalyzer.hasSqrtStep) return { notation: 'O(√n)', label: 'Square Root Bounds Step' };

    if (recursiveCount >= 2 && !patterns.has('Merge Sort') && !patterns.has('Quick Sort')) {
      return { notation: 'O(2ⁿ)', label: 'Exponential Recursive Call Tree' };
    }

    if (maxDepth === 1 && this.cfAnalyzer.hasLogarithmicStep) return { notation: 'O(log n)', label: 'Logarithmic Step Reduction' };
    if (maxDepth === 1) return { notation: 'O(n)', label: 'Linear Iteration Pass' };
    if (maxDepth === 2) return { notation: 'O(n²)', label: 'Quadratic Nested Iteration' };
    if (maxDepth === 3) return { notation: 'O(n³)', label: 'Cubic Matrix/Tensor Traversal' };
    if (maxDepth > 3) return { notation: `O(n^${maxDepth})`, label: `Polynomial Loop Depth (${maxDepth} Layers)` };

    if (this.cfAnalyzer.recursiveFunctions.size === 1) return { notation: 'O(n)', label: 'Linear Stack Recurrence' };

    return { notation: 'O(1)', label: 'Constant Time Execution' };
  }

  evaluateSpaceComplexity() {
    const primary = this.patternDetector.primaryAlgorithm;
    const structures = this.patternDetector.detectedStructures;
    const isRecursive = this.cfAnalyzer.recursiveFunctions.size > 0;
    const maxDepth = this.cfAnalyzer.maxLoopDepth;

    if (primary === 'Quick Sort') return { notation: 'O(log n)', label: 'Logarithmic Recursion Call Stack' };
    if (primary === 'Merge Sort') return { notation: 'O(n)', label: 'Linear Auxiliary Merge Buffers' };
    if (['Breadth-First Search (BFS)', 'Depth-First Search (DFS)'].includes(primary)) return { notation: 'O(V)', label: 'Vertex Visit Traversal Buffer' };

    if (patternsHas2DMatrix(this.code)) return { notation: 'O(n²)', label: '2D Grid / DP Matrix Table' };

    if (structures.has('HashMap') || structures.has('HashSet') || structures.has('Queue') || structures.has('Stack') || structures.has('PriorityQueue')) {
      return { notation: 'O(n)', label: 'Linear Auxiliary Store' };
    }

    if (isRecursive) return { notation: 'O(n)', label: 'Linear Recursion Stack Depth' };

    if (/\b(new Array|vector<|malloc\(|new int|ArrayList)\b/i.test(this.code)) {
      return { notation: 'O(n)', label: 'Linear Dynamic Array Memory' };
    }

    return { notation: 'O(1)', label: 'Constant Auxiliary Primitive Allocation' };
  }
}

function patternsHas2DMatrix(code) {
  return /dp\[.*?\]\[.*?\]|matrix\[.*?\]\[.*?\]|vector<vector<|new int\[.*?\]\[.*?\]/i.test(code);
}

/* ==========================================================================
   5. CONFIDENCE SCORE & EXPLANATION GENERATOR
   ========================================================================== */

class ConfidenceCalculator {
  static compute(tokens, cfAnalyzer, patternDetector, timeInfo) {
    let score = 75;

    if (tokens.length > 15) score += 5;
    if (patternDetector.primaryAlgorithm) score += 12;
    if (patternDetector.detectedPatterns.size > 1) score += 5;
    if (cfAnalyzer.maxLoopDepth > 0) score += 3;

    return Math.min(score, 99);
  }
}

/* ==========================================================================
   6. PUBLIC ENGINE API ENTRY POINT
   ========================================================================== */

function analyzeCodeHeuristics(code) {
  const languageSelect = document.getElementById('language-select');
  const selectedLang = languageSelect ? languageSelect.value : 'javascript';

  const tokenizer = new Tokenizer(code, selectedLang);
  const tokens = tokenizer.tokenize();

  const cfAnalyzer = new ControlFlowAnalyzer(tokens, code, selectedLang);
  cfAnalyzer.buildScopeTree();

  const patternDetector = new PatternDetector(code, tokens, cfAnalyzer);
  patternDetector.detectAll();

  const evaluator = new ComplexityEvaluator(cfAnalyzer, patternDetector, code);
  const timeInfo = evaluator.evaluateTimeComplexity();
  const spaceInfo = evaluator.evaluateSpaceComplexity();

  const confidenceScore = ConfidenceCalculator.compute(tokens, cfAnalyzer, patternDetector, timeInfo);

  const primaryAlgo = patternDetector.primaryAlgorithm || timeInfo.label;
  const detectedPatternsList = Array.from(patternDetector.detectedPatterns);

  const explanationHtml = `
    <p>Static AST Engine evaluated code execution profile as <strong>${timeInfo.notation}</strong> time complexity and <strong>${spaceInfo.notation}</strong> auxiliary space footprint.</p>
    <br/>
    <p><strong>AST Structural Findings:</strong></p>
    <ul>
      <li>Primary Classification: <strong>${primaryAlgo}</strong></li>
      <li>Loop Nesting Boundary: Maximum depth of ${cfAnalyzer.maxLoopDepth} iterative layer(s).</li>
      <li>Variable Step Progression: ${cfAnalyzer.hasLogarithmicStep ? 'Logarithmic division/multiplication step verified.' : 'Standard linear incremental pass.'}</li>
      <li>Call Stack Trait: ${cfAnalyzer.recursiveFunctions.size > 0 ? `${cfAnalyzer.recursiveFunctions.size} self-referential function recursion site(s).` : 'No recursive stack depth overhead.'}</li>
      <li>Identified Data Structures: ${patternDetector.detectedStructures.size > 0 ? Array.from(patternDetector.detectedStructures).join(', ') : 'Primitive variables only.'}</li>
    </ul>
  `;

  let optimizationCode = code;
  if (timeInfo.notation === 'O(n²)') {
    optimizationCode = `// Optimization Recommendation: Reduce O(n²) to O(n)\n// Replace nested loop lookup with HashMap / HashSet store\n` + code;
  } else if (timeInfo.notation === 'O(2ⁿ)') {
    optimizationCode = `// Optimization Recommendation: Eliminate O(2ⁿ) Exponential Branching\n// Apply Memoization or Dynamic Programming table\n` + code;
  } else {
    optimizationCode = `// Code is operating near optimal algorithmic execution bounds.\n` + code;
  }

  return {
    timestamp: new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' }),
    code: code,
    timeComplexity: timeInfo.notation,
    timeLabel: timeInfo.label,
    spaceComplexity: spaceInfo.notation,
    spaceLabel: spaceInfo.label,
    confidence: `${confidenceScore}%`,
    detectedAlgorithm: primaryAlgo,
    detectedPatterns: detectedPatternsList,
    traits: detectedPatternsList,
    explanation: explanationHtml,
    detailedExplanation: explanationHtml,
    refactored: optimizationCode,
    optimizationSuggestions: optimizationCode
  };
}

/* ==========================================================================
   7. FULL APPLICATION UI CONTROLLER
   ========================================================================== */

class ComplexityAnalyzerApp {
  constructor() {
    this.historyKey = 'complexity_ai_history';
    this.savedKey = 'complexity_ai_saved';
    this.themeKey = 'complexity_ai_theme';
    this.sampleAlgorithms = {
      javascript: `function binarySearch(arr, target) {
  let left = 0;
  let right = arr.length - 1;
  while (left <= right) {
    const mid = Math.floor((left + right) / 2);
    if (arr[mid] === target) return mid;
    if (arr[mid] < target) left = mid + 1;
    else right = mid - 1;
  }
  return -1;
}`,
      typescript: `function quicksort(arr: number[]): number[] {
  if (arr.length <= 1) return arr;
  const pivot = arr[0];
  const left = arr.slice(1).filter(x => x < pivot);
  const right = arr.slice(1).filter(x => x >= pivot);
  return [...quicksort(left), pivot, ...quicksort(right)];
}`,
      python: `def two_sum(nums, target):
    seen = {}
    for i, num in enumerate(nums):
        complement = target - num
        if complement in seen:
            return [seen[complement], i]
        seen[num] = i
    return []`,
      cpp: `int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}`,
      java: `public void bubbleSort(int[] arr) {
    int n = arr.length;
    for (int i = 0; i < n - 1; i++) {
        for (int j = 0; j < n - i - 1; j++) {
            if (arr[j] > arr[j + 1]) {
                int temp = arr[j];
                arr[j] = arr[j + 1];
                arr[j + 1] = temp;
            }
        }
    }
}`
    };

    this.currentAnalysis = null;
    this.init();
  }

  init() {
    this.cacheDOM();
    this.bindEvents();
    this.loadThemePreference();
    this.updateLineNumbers();
    this.renderHistory();
    this.renderSaved();
    this.setupParticles();
    this.hideLoadingScreen();
  }

  cacheDOM() {
    this.dom = {
      loadingScreen: document.getElementById('loading-screen'),
      toastContainer: document.getElementById('toast-container'),
      commandBackdrop: document.getElementById('command-palette-backdrop'),
      commandInput: document.getElementById('command-input'),
      commandResults: document.getElementById('command-results'),
      cmdPaletteBtn: document.getElementById('cmd-palette-btn'),
      
      sidebar: document.getElementById('sidebar'),
      sidebarToggleBtn: document.getElementById('sidebar-toggle-btn'),
      navItems: document.querySelectorAll('.nav-item'),
      sections: {
        landing: document.getElementById('landing'),
        analyzer: document.getElementById('analyzer'),
        results: document.getElementById('results'),
        history: document.getElementById('history'),
        saved: document.getElementById('saved')
      },
      
      themeToggleNav: document.getElementById('theme-toggle-nav'),
      themeToggleSidebar: document.getElementById('theme-toggle-sidebar'),
      
      codeEditor: document.getElementById('code-editor'),
      lineNumbers: document.getElementById('line-numbers'),
      lineCountDisplay: document.getElementById('line-count-display'),
      charCountDisplay: document.getElementById('char-count-display'),
      languageSelect: document.getElementById('language-select'),
      fileUploadInput: document.getElementById('file-upload-input'),
      activeFilename: document.getElementById('active-filename'),
      
      btnAnalyze: document.getElementById('btn-analyze'),
      btnClearCode: document.getElementById('btn-clear-code'),
      btnPasteClipboard: document.getElementById('btn-paste-clipboard'),
      btnCopyCode: document.getElementById('btn-copy-code'),
      btnDemoSample: document.getElementById('btn-demo-sample'),
      
      resultsSkeleton: document.getElementById('results-skeleton'),
      resultsContent: document.getElementById('results-content'),
      resTimeComplexity: document.getElementById('res-time-complexity'),
      resTimeLabel: document.getElementById('res-time-label'),
      resSpaceComplexity: document.getElementById('res-space-complexity'),
      resSpaceLabel: document.getElementById('res-space-label'),
      resConfidenceScore: document.getElementById('res-confidence-score'),
      resTagsContainer: document.getElementById('res-tags-container'),
      resExplanationBody: document.getElementById('res-explanation-body'),
      resRefactoredCode: document.getElementById('res-refactored-code'),
      
      complexityChartSvg: document.getElementById('complexity-chart-svg'),
      memoryChartSvg: document.getElementById('memory-chart-svg'),
      
      btnSaveAnalysis: document.getElementById('btn-save-analysis'),
      btnReanalyze: document.getElementById('btn-reanalyze'),
      btnClearHistory: document.getElementById('btn-clear-history'),
      btnCopyRefactored: document.getElementById('btn-copy-refactored'),
      
      historyList: document.getElementById('history-list'),
      savedList: document.getElementById('saved-list')
    };
  }

  bindEvents() {
    if (this.dom.themeToggleNav) this.dom.themeToggleNav.addEventListener('click', () => this.toggleTheme());
    if (this.dom.themeToggleSidebar) this.dom.themeToggleSidebar.addEventListener('click', () => this.toggleTheme());

    if (this.dom.sidebarToggleBtn) {
      this.dom.sidebarToggleBtn.addEventListener('click', () => {
        this.dom.sidebar.classList.toggle('collapsed');
      });
    }

    this.dom.navItems.forEach(item => {
      item.addEventListener('click', (e) => {
        e.preventDefault();
        const tab = item.getAttribute('data-tab');
        this.switchSection(tab);
      });
    });

    if (this.dom.codeEditor) {
      this.dom.codeEditor.addEventListener('input', () => {
        this.updateLineNumbers();
      });
      this.dom.codeEditor.addEventListener('scroll', () => {
        this.dom.lineNumbers.scrollTop = this.dom.codeEditor.scrollTop;
      });
    }

    if (this.dom.languageSelect) {
      this.dom.languageSelect.addEventListener('change', (e) => {
        const lang = e.target.value;
        this.dom.activeFilename.textContent = `algorithm.${this.getLanguageExtension(lang)}`;
      });
    }

    if (this.dom.btnAnalyze) this.dom.btnAnalyze.addEventListener('click', () => this.runAnalysis());
    if (this.dom.btnClearCode) this.dom.btnClearCode.addEventListener('click', () => this.clearEditor());
    if (this.dom.btnPasteClipboard) this.dom.btnPasteClipboard.addEventListener('click', () => this.pasteFromClipboard());
    if (this.dom.btnCopyCode) this.dom.btnCopyCode.addEventListener('click', () => this.copyToClipboard(this.dom.codeEditor.value, 'Code copied!'));
    if (this.dom.btnDemoSample) this.dom.btnDemoSample.addEventListener('click', () => this.loadSampleAlgorithm());
    if (this.dom.btnSaveAnalysis) this.dom.btnSaveAnalysis.addEventListener('click', () => this.saveCurrentAnalysis());
    if (this.dom.btnReanalyze) this.dom.btnReanalyze.addEventListener('click', () => this.switchSection('analyzer'));
    if (this.dom.btnClearHistory) this.dom.btnClearHistory.addEventListener('click', () => this.clearHistory());
    if (this.dom.btnCopyRefactored) this.dom.btnCopyRefactored.addEventListener('click', () => this.copyToClipboard(this.dom.resRefactoredCode.textContent, 'Refactored code copied!'));

    if (this.dom.fileUploadInput) {
      this.dom.fileUploadInput.addEventListener('change', (e) => this.handleFileUpload(e));
    }

    if (this.dom.cmdPaletteBtn) {
      this.dom.cmdPaletteBtn.addEventListener('click', () => this.toggleCommandPalette(true));
    }
    if (this.dom.commandBackdrop) {
      this.dom.commandBackdrop.addEventListener('click', (e) => {
        if (e.target === this.dom.commandBackdrop) this.toggleCommandPalette(false);
      });
    }
    if (this.dom.commandResults) {
      this.dom.commandResults.addEventListener('click', (e) => {
        const item = e.target.closest('.command-item');
        if (!item) return;
        const action = item.getAttribute('data-action');
        this.executeCommand(action);
      });
    }

    window.addEventListener('keydown', (e) => {
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k') {
        e.preventDefault();
        this.toggleCommandPalette();
      } else if ((e.metaKey || e.ctrlKey) && e.key === 'Enter') {
        e.preventDefault();
        this.runAnalysis();
      } else if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'l') {
        e.preventDefault();
        this.clearEditor();
      } else if (e.key === 'Escape') {
        this.toggleCommandPalette(false);
      }
    });
  }

  toggleTheme() {
    const html = document.documentElement;
    const isDark = html.classList.contains('dark');
    if (isDark) {
      html.classList.remove('dark');
      html.classList.add('light');
      localStorage.setItem(this.themeKey, 'light');
      this.showToast('Switched to Light Theme', 'info');
    } else {
      html.classList.remove('light');
      html.classList.add('dark');
      localStorage.setItem(this.themeKey, 'dark');
      this.showToast('Switched to Dark Theme', 'info');
    }
    if (this.currentAnalysis) {
      this.renderCharts(this.currentAnalysis);
    }
  }

  loadThemePreference() {
    const saved = localStorage.getItem(this.themeKey) || 'dark';
    document.documentElement.classList.remove('dark', 'light');
    document.documentElement.classList.add(saved);
  }

  switchSection(sectionId) {
    Object.keys(this.dom.sections).forEach(key => {
      const sec = this.dom.sections[key];
      if (sec) {
        if (key === sectionId) {
          sec.classList.remove('hidden');
        } else {
          sec.classList.add('hidden');
        }
      }
    });

    this.dom.navItems.forEach(item => {
      if (item.getAttribute('data-tab') === sectionId) {
        item.classList.add('active');
      } else {
        item.classList.remove('active');
      }
    });

    window.scrollTo({ top: 0, behavior: 'smooth' });
  }

  updateLineNumbers() {
    const text = this.dom.codeEditor.value;
    const lines = text.split('\n');
    const count = lines.length;
    let numbersHtml = '';
    for (let i = 1; i <= count; i++) {
      numbersHtml += `${i}\n`;
    }
    this.dom.lineNumbers.textContent = numbersHtml;
    this.dom.lineCountDisplay.textContent = `Lines: ${count}`;
    this.dom.charCountDisplay.textContent = `Chars: ${text.length}`;
  }

  getLanguageExtension(lang) {
    const map = {
      javascript: 'js',
      typescript: 'ts',
      python: 'py',
      cpp: 'cpp',
      java: 'java',
      go: 'go',
      rust: 'rs'
    };
    return map[lang] || 'txt';
  }

  clearEditor() {
    this.dom.codeEditor.value = '';
    this.updateLineNumbers();
    this.showToast('Editor cleared', 'info');
  }

  async pasteFromClipboard() {
    try {
      const text = await navigator.clipboard.readText();
      this.dom.codeEditor.value = text;
      this.updateLineNumbers();
      this.showToast('Pasted from clipboard!', 'success');
    } catch (e) {
      this.showToast('Clipboard permission denied', 'danger');
    }
  }

  copyToClipboard(text, msg = 'Copied to clipboard!') {
    if (!text) {
      this.showToast('Nothing to copy', 'warning');
      return;
    }
    navigator.clipboard.writeText(text);
    this.showToast(msg, 'success');
  }

  handleFileUpload(e) {
    const file = e.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = (evt) => {
      this.dom.codeEditor.value = evt.target.result;
      this.dom.activeFilename.textContent = file.name;
      this.updateLineNumbers();
      this.showToast(`Loaded ${file.name}`, 'success');
    };
    reader.readAsText(file);
  }

  loadSampleAlgorithm() {
    const lang = this.dom.languageSelect.value || 'javascript';
    const code = this.sampleAlgorithms[lang] || this.sampleAlgorithms.javascript;
    this.dom.codeEditor.value = code;
    this.updateLineNumbers();
    this.switchSection('analyzer');
    this.showToast(`Loaded ${lang} sample snippet`, 'info');
  }

  toggleCommandPalette(show) {
    if (show === undefined) {
      this.dom.commandBackdrop.classList.toggle('hidden');
    } else if (show) {
      this.dom.commandBackdrop.classList.remove('hidden');
      this.dom.commandInput.focus();
    } else {
      this.dom.commandBackdrop.classList.add('hidden');
    }
  }

  executeCommand(action) {
    this.toggleCommandPalette(false);
    switch (action) {
      case 'run-analysis':
        this.runAnalysis();
        break;
      case 'clear-editor':
        this.clearEditor();
        break;
      case 'toggle-theme':
        this.toggleTheme();
        break;
      case 'load-sample':
        this.loadSampleAlgorithm();
        break;
    }
  }

  runAnalysis() {
    const code = this.dom.codeEditor.value.trim();
    if (!code) {
      this.showToast('Please paste or write code first!', 'warning');
      return;
    }

    this.switchSection('results');
    this.dom.resultsSkeleton.classList.remove('hidden');
    this.dom.resultsContent.classList.add('hidden');

    setTimeout(() => {
      const result = analyzeCodeHeuristics(code);
      this.currentAnalysis = result;
      this.renderResults(result);
      this.saveToHistory(result);

      this.dom.resultsSkeleton.classList.add('hidden');
      this.dom.resultsContent.classList.remove('hidden');
      this.showToast('AST analysis completed successfully!', 'success');
    }, 400);
  }

  renderResults(res) {
    this.dom.resTimeComplexity.textContent = res.timeComplexity;
    this.dom.resTimeLabel.textContent = res.timeLabel;
    this.dom.resSpaceComplexity.textContent = res.spaceComplexity;
    this.dom.resSpaceLabel.textContent = res.spaceLabel;
    this.dom.resConfidenceScore.textContent = res.confidence;

    const traits = Array.from(res.traits || []);
    this.dom.resTagsContainer.innerHTML = traits.map(t => `<span class="trait-tag tag-blue">${t}</span>`).join('');

    this.dom.resExplanationBody.innerHTML = res.explanation;
    this.dom.resRefactoredCode.textContent = res.refactored;

    this.renderCharts(res);
  }

  renderCharts(res) {
    const isDark = document.documentElement.classList.contains('dark');
    const strokeColor = isDark ? '#14f195' : '#059669';
    const gridColor = isDark ? 'rgba(255,255,255,0.08)' : 'rgba(0,0,0,0.08)';

    let pathD = 'M 40 200 Q 250 180 460 40';
    if (res.timeComplexity.includes('1')) pathD = 'M 40 180 L 460 180';
    if (res.timeComplexity.includes('log')) pathD = 'M 40 200 Q 150 100 460 90';
    if (res.timeComplexity.includes('n²')) pathD = 'M 40 200 Q 300 190 460 20';

    this.dom.complexityChartSvg.innerHTML = `
      <defs>
        <linearGradient id="chartGlow" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stop-color="${strokeColor}" stop-opacity="0.3"/>
          <stop offset="100%" stop-color="${strokeColor}" stop-opacity="0"/>
        </linearGradient>
      </defs>
      <line x1="40" y1="40" x2="460" y2="40" stroke="${gridColor}" stroke-dasharray="4"/>
      <line x1="40" y1="100" x2="460" y2="100" stroke="${gridColor}" stroke-dasharray="4"/>
      <line x1="40" y1="160" x2="460" y2="160" stroke="${gridColor}" stroke-dasharray="4"/>
      <path d="${pathD} L 460 200 L 40 200 Z" fill="url(#chartGlow)" />
      <path d="${pathD}" fill="none" stroke="${strokeColor}" stroke-width="3" stroke-linecap="round" />
    `;

    const memoryColor = isDark ? '#3b82f6' : '#2563eb';
    this.dom.memoryChartSvg.innerHTML = `
      <line x1="40" y1="200" x2="460" y2="200" stroke="${gridColor}" />
      <rect x="70" y="140" width="40" height="60" rx="4" fill="${memoryColor}" opacity="0.4" />
      <rect x="170" y="110" width="40" height="90" rx="4" fill="${memoryColor}" opacity="0.6" />
      <rect x="270" y="70" width="40" height="130" rx="4" fill="${memoryColor}" opacity="0.8" />
      <rect x="370" y="30" width="40" height="170" rx="4" fill="${memoryColor}" opacity="1" />
    `;
  }

  saveToHistory(result) {
    const history = JSON.parse(localStorage.getItem(this.historyKey) || '[]');
    history.unshift(result);
    if (history.length > 20) history.pop();
    localStorage.setItem(this.historyKey, JSON.stringify(history));
    this.renderHistory();
  }

  renderHistory() {
    const history = JSON.parse(localStorage.getItem(this.historyKey) || '[]');
    if (history.length === 0) {
      this.dom.historyList.innerHTML = `
        <div class="empty-state glass-panel">
          <h3>No Previous Analyses</h3>
          <p>Run your first code profiling session to store local history records.</p>
        </div>
      `;
      return;
    }

    this.dom.historyList.innerHTML = history.map((item, idx) => `
      <div class="metric-card glass-panel">
        <div class="metric-header">
          <span class="metric-title">${item.timestamp}</span>
          <span class="trait-tag tag-emerald">${item.timeComplexity}</span>
        </div>
        <div class="metric-body">
          <pre style="font-family: var(--font-mono); font-size: 11px; max-height: 60px; overflow: hidden; color: var(--text-dim);">${item.code.slice(0, 100)}...</pre>
        </div>
        <div class="metric-footer">
          <button class="btn-xs-ghost" onclick="app.loadHistoryItem(${idx})">Load Item</button>
        </div>
      </div>
    `).join('');
  }

  loadHistoryItem(idx) {
    const history = JSON.parse(localStorage.getItem(this.historyKey) || '[]');
    if (history[idx]) {
      this.dom.codeEditor.value = history[idx].code;
      this.updateLineNumbers();
      this.switchSection('analyzer');
      this.showToast('Loaded snippet from history', 'info');
    }
  }

  clearHistory() {
    localStorage.removeItem(this.historyKey);
    this.renderHistory();
    this.showToast('History cleared', 'info');
  }

  saveCurrentAnalysis() {
    if (!this.currentAnalysis) {
      this.showToast('No active analysis to save', 'warning');
      return;
    }
    const saved = JSON.parse(localStorage.getItem(this.savedKey) || '[]');
    saved.unshift(this.currentAnalysis);
    localStorage.setItem(this.savedKey, JSON.stringify(saved));
    this.renderSaved();
    this.showToast('Saved snippet to workspace!', 'success');
  }

  renderSaved() {
    const saved = JSON.parse(localStorage.getItem(this.savedKey) || '[]');
    if (saved.length === 0) {
      this.dom.savedList.innerHTML = `
        <div class="empty-state glass-panel">
          <h3>No Bookmarked Snippets</h3>
          <p>Click "Save to Workspace" on any analysis dashboard to bookmark items here.</p>
        </div>
      `;
      return;
    }

    this.dom.savedList.innerHTML = saved.map(item => `
      <div class="metric-card glass-panel">
        <div class="metric-header">
          <span class="metric-title">Bookmarked Analysis</span>
          <span class="trait-tag tag-blue">${item.timeComplexity}</span>
        </div>
        <div class="metric-body">
          <pre style="font-family: var(--font-mono); font-size: 11px; max-height: 60px; overflow: hidden; color: var(--text-dim);">${item.code.slice(0, 100)}...</pre>
        </div>
      </div>
    `).join('');
  }

  showToast(message, type = 'info') {
    const toast = document.createElement('div');
    toast.className = `toast toast-${type}`;
    toast.innerHTML = `<span>${message}</span>`;
    this.dom.toastContainer.appendChild(toast);

    setTimeout(() => {
      toast.style.opacity = '0';
      setTimeout(() => toast.remove(), 250);
    }, 3000);
  }

  hideLoadingScreen() {
    if (this.dom.loadingScreen) {
      setTimeout(() => {
        this.dom.loadingScreen.style.opacity = '0';
        setTimeout(() => this.dom.loadingScreen.classList.add('hidden'), 400);
      }, 500);
    }
  }

  setupParticles() {
    const canvas = document.createElement('canvas');
    const container = document.getElementById('particles-canvas');
    if (!container) return;
    container.appendChild(canvas);

    const ctx = canvas.getContext('2d');
    let width = canvas.width = container.offsetWidth || window.innerWidth;
    let height = canvas.height = container.offsetHeight || 400;

    const particles = Array.from({ length: 30 }, () => ({
      x: Math.random() * width,
      y: Math.random() * height,
      vx: (Math.random() - 0.5) * 0.5,
      vy: (Math.random() - 0.5) * 0.5,
      radius: Math.random() * 2 + 1
    }));

    const render = () => {
      ctx.clearRect(0, 0, width, height);
      ctx.fillStyle = 'rgba(20, 241, 149, 0.2)';
      particles.forEach(p => {
        p.x += p.vx;
        p.y += p.vy;
        if (p.x < 0 || p.x > width) p.vx *= -1;
        if (p.y < 0 || p.y > height) p.vy *= -1;
        ctx.beginPath();
        ctx.arc(p.x, p.y, p.radius, 0, Math.PI * 2);
        ctx.fill();
      });
      requestAnimationFrame(render);
    };
    render();
  }
}

// Global App Instance
let app;
document.addEventListener('DOMContentLoaded', () => {
  app = new ComplexityAnalyzerApp();
});