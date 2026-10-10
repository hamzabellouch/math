import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15104 : Integer.Sparse Key := [(key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2554, 2), (key2554, 2), (key2538, 2), (key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2522, 2), (key2503, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2563, -1), (key2554, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2543, -1), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2482, -1)]

theorem rawRowCheck15104 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form10 = rawRow15104 := by decide +kernel

def row15104 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

theorem rowCheck15104 : row15104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15104 := by decide +kernel

theorem rowEval15104 (x : Key → ℝ) : Integer.Sparse.eval row15104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15104, Integer.Sparse.eval_collectBalanced, rawRowCheck15104]

def rawRow15105 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2378, 2), (key2392, 2), (key2406, 2), (key2440, 2), (key2543, 2), (key2554, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1), (key2392, 2), (key2482, 2), (key2522, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2440, -1), (key2482, -1), (key2506, -1)]

theorem rawRowCheck15105 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form10 = rawRow15105 := by decide +kernel

def row15105 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15105 : row15105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15105 := by decide +kernel

theorem rowEval15105 (x : Key → ℝ) : Integer.Sparse.eval row15105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15105, Integer.Sparse.eval_collectBalanced, rawRowCheck15105]

def rawRow15106 : Integer.Sparse Key := [(key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2392, 2), (key2378, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2543, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1), (key2392, 2), (key2522, 2), (key2482, 2), (key2392, -1), (key2381, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2482, -1)]

theorem rawRowCheck15106 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form10 = rawRow15106 := by decide +kernel

def row15106 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15106 : row15106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15106 := by decide +kernel

theorem rowEval15106 (x : Key → ℝ) : Integer.Sparse.eval row15106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15106, Integer.Sparse.eval_collectBalanced, rawRowCheck15106]

def rawRow15107 : Integer.Sparse Key := [(key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2406, 2), (key2543, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2482, 2), (key2392, 2), (key2522, 2), (key2409, -1), (key2482, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2440, -1)]

theorem rawRowCheck15107 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form10 = rawRow15107 := by decide +kernel

def row15107 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15107 : row15107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15107 := by decide +kernel

theorem rowEval15107 (x : Key → ℝ) : Integer.Sparse.eval row15107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15107, Integer.Sparse.eval_collectBalanced, rawRowCheck15107]

def rawRow15108 : Integer.Sparse Key := [(key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2543, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2440, 2), (key2392, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1), (key2482, 2), (key2522, 2), (key2392, 2), (key2482, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2440, -1), (key2392, -1)]

theorem rawRowCheck15108 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form10 = rawRow15108 := by decide +kernel

def row15108 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15108 : row15108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15108 := by decide +kernel

theorem rowEval15108 (x : Key → ℝ) : Integer.Sparse.eval row15108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form10) x := by
  rw [rowCheck15108, Integer.Sparse.eval_collectBalanced, rawRowCheck15108]

def rawRow15109 : Integer.Sparse Key := [(key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2440, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2378, 2), (key2406, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1), (key2522, 2), (key2392, 2), (key2482, 2), (key2440, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2381, -1), (key2409, -1)]

theorem rawRowCheck15109 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form10 = rawRow15109 := by decide +kernel

def row15109 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15109 : row15109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15109 := by decide +kernel

theorem rowEval15109 (x : Key → ℝ) : Integer.Sparse.eval row15109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15109, Integer.Sparse.eval_collectBalanced, rawRowCheck15109]

def rawRow15110 : Integer.Sparse Key := [(key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2554, 2), (key2440, 2), (key2543, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2522, 2), (key2482, 2), (key2392, 2), (key2506, -1), (key2440, -1), (key2482, -1), (key2392, -1), (key2409, -1), (key2381, -1)]

theorem rawRowCheck15110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form10 = rawRow15110 := by decide +kernel

def row15110 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15110 : row15110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15110 := by decide +kernel

theorem rowEval15110 (x : Key → ℝ) : Integer.Sparse.eval row15110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form10) x := by
  rw [rowCheck15110, Integer.Sparse.eval_collectBalanced, rawRowCheck15110]

def rawRow15111 : Integer.Sparse Key := [(key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2543, 2), (key2543, 2), (key2563, 2), (key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2472, 2), (key2482, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2506, 2), (key2538, -1), (key2543, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2554, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1)]

theorem rawRowCheck15111 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form10 = rawRow15111 := by decide +kernel

def row15111 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck15111 : row15111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15111 := by decide +kernel

theorem rowEval15111 (x : Key → ℝ) : Integer.Sparse.eval row15111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15111, Integer.Sparse.eval_collectBalanced, rawRowCheck15111]

def rawRow15112 : Integer.Sparse Key := [(key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2543, 2), (key2563, 2), (key2543, 2), (key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2482, 2), (key2472, 2), (key2506, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2543, -1), (key2538, -1), (key2554, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1)]

theorem rawRowCheck15112 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form10 = rawRow15112 := by decide +kernel

def row15112 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck15112 : row15112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15112 := by decide +kernel

theorem rowEval15112 (x : Key → ℝ) : Integer.Sparse.eval row15112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15112, Integer.Sparse.eval_collectBalanced, rawRowCheck15112]

def rawRow15113 : Integer.Sparse Key := [(key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2563, 2), (key2543, 2), (key2543, 2), (key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2506, 2), (key2506, 2), (key2482, 2), (key2482, 2), (key2472, 2), (key2472, 2), (key2554, -1), (key2554, -1), (key2543, -1), (key2543, -1), (key2538, -1), (key2538, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1)]

theorem rawRowCheck15113 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form10 = rawRow15113 := by decide +kernel

def row15113 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck15113 : row15113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15113 := by decide +kernel

theorem rowEval15113 (x : Key → ℝ) : Integer.Sparse.eval row15113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15113, Integer.Sparse.eval_collectBalanced, rawRowCheck15113]

def rawRow15114 : Integer.Sparse Key := [(key2390, -1), (key2392, -1), (key2480, -1), (key2522, -1), (key2543, -1), (key2563, -1), (key2392, 2), (key2482, 2), (key2522, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2506, -1), (key2538, -1), (key2554, -1), (key2378, 2), (key2392, 2), (key2406, 2), (key2440, 2), (key2543, 2), (key2554, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2440, -1), (key2482, -1), (key2506, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1)]

theorem rawRowCheck15114 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form10 = rawRow15114 := by decide +kernel

def row15114 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15114 : row15114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15114 := by decide +kernel

theorem rowEval15114 (x : Key → ℝ) : Integer.Sparse.eval row15114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15114, Integer.Sparse.eval_collectBalanced, rawRowCheck15114]

def rawRow15115 : Integer.Sparse Key := [(key2392, -1), (key2390, -1), (key2522, -1), (key2480, -1), (key2563, -1), (key2543, -1), (key2392, 2), (key2522, 2), (key2482, 2), (key2381, -1), (key2378, -1), (key2506, -1), (key2472, -1), (key2554, -1), (key2538, -1), (key2392, 2), (key2378, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2543, 2), (key2392, -1), (key2381, -1), (key2440, -1), (key2409, -1), (key2506, -1), (key2482, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1)]

theorem rawRowCheck15115 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form10 = rawRow15115 := by decide +kernel

def row15115 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15115 : row15115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15115 := by decide +kernel

theorem rowEval15115 (x : Key → ℝ) : Integer.Sparse.eval row15115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15115, Integer.Sparse.eval_collectBalanced, rawRowCheck15115]

def rawRow15116 : Integer.Sparse Key := [(key2480, -1), (key2543, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2482, 2), (key2392, 2), (key2522, 2), (key2472, -1), (key2538, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2406, 2), (key2543, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2409, -1), (key2482, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2440, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1)]

theorem rawRowCheck15116 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form10 = rawRow15116 := by decide +kernel

def row15116 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15116 : row15116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15116 := by decide +kernel

theorem rowEval15116 (x : Key → ℝ) : Integer.Sparse.eval row15116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15116, Integer.Sparse.eval_collectBalanced, rawRowCheck15116]

def rawRow15117 : Integer.Sparse Key := [(key2543, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2522, -1), (key2392, -1), (key2482, 2), (key2522, 2), (key2392, 2), (key2538, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2506, -1), (key2381, -1), (key2543, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2440, 2), (key2392, 2), (key2482, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2440, -1), (key2392, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1)]

theorem rawRowCheck15117 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form10 = rawRow15117 := by decide +kernel

def row15117 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15117 : row15117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15117 := by decide +kernel

theorem rowEval15117 (x : Key → ℝ) : Integer.Sparse.eval row15117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form10) x := by
  rw [rowCheck15117, Integer.Sparse.eval_collectBalanced, rawRowCheck15117]

def rawRow15118 : Integer.Sparse Key := [(key2522, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2390, -1), (key2480, -1), (key2522, 2), (key2392, 2), (key2482, 2), (key2506, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2378, -1), (key2472, -1), (key2440, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2378, 2), (key2406, 2), (key2440, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2381, -1), (key2409, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1)]

theorem rawRowCheck15118 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form10 = rawRow15118 := by decide +kernel

def row15118 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15118 : row15118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15118 := by decide +kernel

theorem rowEval15118 (x : Key → ℝ) : Integer.Sparse.eval row15118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15118, Integer.Sparse.eval_collectBalanced, rawRowCheck15118]

def rawRow15119 : Integer.Sparse Key := [(key2563, -1), (key2522, -1), (key2543, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2522, 2), (key2482, 2), (key2392, 2), (key2554, -1), (key2506, -1), (key2538, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2554, 2), (key2440, 2), (key2543, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2506, -1), (key2440, -1), (key2482, -1), (key2392, -1), (key2409, -1), (key2381, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1)]

theorem rawRowCheck15119 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form10 = rawRow15119 := by decide +kernel

def row15119 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2472, 1), (key2480, -2), (key2482, 1), (key2503, 1), (key2506, -2), (key2522, 1), (key2538, -1), (key2543, 1), (key2554, 1), (key2563, -1)]

theorem rowCheck15119 : row15119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15119 := by decide +kernel

theorem rowEval15119 (x : Key → ℝ) : Integer.Sparse.eval row15119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form10) x := by
  rw [rowCheck15119, Integer.Sparse.eval_collectBalanced, rawRowCheck15119]

def rawRow15120 : Integer.Sparse Key := [(key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2543, -1), (key2543, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2543, -1), (key2543, -1), (key2381, 2), (key2381, 2), (key2409, 2), (key2409, 2), (key2538, 2), (key2538, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1)]

theorem rawRowCheck15120 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form10 = rawRow15120 := by decide +kernel

def row15120 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

theorem rowCheck15120 : row15120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15120 := by decide +kernel

theorem rowEval15120 (x : Key → ℝ) : Integer.Sparse.eval row15120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15120, Integer.Sparse.eval_collectBalanced, rawRowCheck15120]

def rawRow15121 : Integer.Sparse Key := [(key2482, -1), (key2543, -1), (key2392, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2482, -1), (key2543, -1), (key2392, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2409, 2), (key2538, 2), (key2381, 2), (key2538, 2), (key2381, 2), (key2409, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1)]

theorem rawRowCheck15121 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form10 = rawRow15121 := by decide +kernel

def row15121 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

theorem rowCheck15121 : row15121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15121 := by decide +kernel

theorem rowEval15121 (x : Key → ℝ) : Integer.Sparse.eval row15121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15121, Integer.Sparse.eval_collectBalanced, rawRowCheck15121]

def rawRow15122 : Integer.Sparse Key := [(key2543, -1), (key2482, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2543, -1), (key2482, -1), (key2543, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2538, 2), (key2409, 2), (key2538, 2), (key2381, 2), (key2409, 2), (key2381, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1)]

theorem rawRowCheck15122 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form10 = rawRow15122 := by decide +kernel

def row15122 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, -4), (key2409, 4), (key2472, -4), (key2480, 8), (key2482, -4), (key2538, 4), (key2543, -4)]

theorem rowCheck15122 : row15122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15122 := by decide +kernel

theorem rowEval15122 (x : Key → ℝ) : Integer.Sparse.eval row15122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form10) x := by
  rw [rowCheck15122, Integer.Sparse.eval_collectBalanced, rawRowCheck15122]

def rawRow15123 : Integer.Sparse Key := [(key1277, -2), (key1277, -2), (key1283, -2), (key1283, 6), (key1700, -2), (key1700, -2), (key1706, -2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1855, 2), (key1855, 2), (key1706, -2), (key1855, -2), (key1855, -2), (key1756, 6), (key1756, -2), (key1886, -2), (key1886, -2)]

theorem rawRowCheck15123 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form11 = rawRow15123 := by decide +kernel

def row15123 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

theorem rowCheck15123 : row15123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15123 := by decide +kernel

theorem rowEval15123 (x : Key → ℝ) : Integer.Sparse.eval row15123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15123, Integer.Sparse.eval_collectBalanced, rawRowCheck15123]

def rawRow15124 : Integer.Sparse Key := [(key1277, -2), (key1283, -2), (key1277, -2), (key1283, 6), (key1700, -2), (key1706, -2), (key1700, -2), (key1851, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1855, -2), (key1706, -2), (key1855, -2), (key1756, 6), (key1886, -2), (key1756, -2), (key1886, -2)]

theorem rawRowCheck15124 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form11 = rawRow15124 := by decide +kernel

def row15124 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

theorem rowCheck15124 : row15124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15124 := by decide +kernel

theorem rowEval15124 (x : Key → ℝ) : Integer.Sparse.eval row15124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15124, Integer.Sparse.eval_collectBalanced, rawRowCheck15124]

def rawRow15125 : Integer.Sparse Key := [(key1283, -2), (key1277, -2), (key1277, -2), (key1283, 6), (key1706, -2), (key1700, -2), (key1700, -2), (key1855, 2), (key1851, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1700, 2), (key1855, -2), (key1855, -2), (key1706, -2), (key1756, 6), (key1886, -2), (key1886, -2), (key1756, -2)]

theorem rawRowCheck15125 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form11 = rawRow15125 := by decide +kernel

def row15125 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

theorem rowCheck15125 : row15125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15125 := by decide +kernel

theorem rowEval15125 (x : Key → ℝ) : Integer.Sparse.eval row15125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15125, Integer.Sparse.eval_collectBalanced, rawRowCheck15125]

def rawRow15126 : Integer.Sparse Key := [(key1277, -2), (key1283, -2), (key1283, -2), (key1277, 6), (key1851, -2), (key1855, -2), (key1855, -2), (key1700, 2), (key1706, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1855, 2), (key1700, -2), (key1700, -2), (key1851, -2), (key1886, 6), (key1756, -2), (key1756, -2), (key1886, -2)]

theorem rawRowCheck15126 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form11 = rawRow15126 := by decide +kernel

def row15126 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

theorem rowCheck15126 : row15126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15126 := by decide +kernel

theorem rowEval15126 (x : Key → ℝ) : Integer.Sparse.eval row15126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15126, Integer.Sparse.eval_collectBalanced, rawRowCheck15126]

def rawRow15127 : Integer.Sparse Key := [(key1283, -2), (key1277, -2), (key1283, -2), (key1277, 6), (key1855, -2), (key1851, -2), (key1855, -2), (key1706, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1700, -2), (key1851, -2), (key1700, -2), (key1886, 6), (key1756, -2), (key1886, -2), (key1756, -2)]

theorem rawRowCheck15127 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form11 = rawRow15127 := by decide +kernel

def row15127 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

theorem rowCheck15127 : row15127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15127 := by decide +kernel

theorem rowEval15127 (x : Key → ℝ) : Integer.Sparse.eval row15127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15127, Integer.Sparse.eval_collectBalanced, rawRowCheck15127]

def rawRow15128 : Integer.Sparse Key := [(key1283, -2), (key1283, -2), (key1277, -2), (key1277, 6), (key1855, -2), (key1855, -2), (key1851, -2), (key1855, 2), (key1855, 2), (key1706, 2), (key1706, 2), (key1700, 2), (key1700, 2), (key1851, -2), (key1700, -2), (key1700, -2), (key1886, 6), (key1886, -2), (key1756, -2), (key1756, -2)]

theorem rawRowCheck15128 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form11 = rawRow15128 := by decide +kernel

def row15128 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

theorem rowCheck15128 : row15128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15128 := by decide +kernel

theorem rowEval15128 (x : Key → ℝ) : Integer.Sparse.eval row15128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15128, Integer.Sparse.eval_collectBalanced, rawRowCheck15128]

def rawRow15129 : Integer.Sparse Key := [(key1700, -2), (key1700, -2), (key1706, -2), (key1756, 6), (key1277, -2), (key1277, -2), (key1283, -2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1855, 2), (key1855, 2), (key1756, -2), (key1886, -2), (key1886, -2), (key1283, 6), (key1706, -2), (key1855, -2), (key1855, -2)]

theorem rawRowCheck15129 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form11 = rawRow15129 := by decide +kernel

def row15129 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

theorem rowCheck15129 : row15129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15129 := by decide +kernel

theorem rowEval15129 (x : Key → ℝ) : Integer.Sparse.eval row15129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15129, Integer.Sparse.eval_collectBalanced, rawRowCheck15129]

def rawRow15130 : Integer.Sparse Key := [(key1700, -2), (key1706, -2), (key1700, -2), (key1756, 6), (key1277, -2), (key1283, -2), (key1277, -2), (key1851, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1886, -2), (key1756, -2), (key1886, -2), (key1283, 6), (key1855, -2), (key1706, -2), (key1855, -2)]

theorem rawRowCheck15130 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form11 = rawRow15130 := by decide +kernel

def row15130 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

theorem rowCheck15130 : row15130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15130 := by decide +kernel

theorem rowEval15130 (x : Key → ℝ) : Integer.Sparse.eval row15130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15130, Integer.Sparse.eval_collectBalanced, rawRowCheck15130]

def rawRow15131 : Integer.Sparse Key := [(key1706, -2), (key1700, -2), (key1700, -2), (key1756, 6), (key1283, -2), (key1277, -2), (key1277, -2), (key1855, 2), (key1851, 2), (key1855, 2), (key1700, 2), (key1851, 2), (key1700, 2), (key1886, -2), (key1886, -2), (key1756, -2), (key1283, 6), (key1855, -2), (key1855, -2), (key1706, -2)]

theorem rawRowCheck15131 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form11 = rawRow15131 := by decide +kernel

def row15131 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1706, -4), (key1756, 4), (key1851, 4), (key1886, -4)]

theorem rowCheck15131 : row15131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15131 := by decide +kernel

theorem rowEval15131 (x : Key → ℝ) : Integer.Sparse.eval row15131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15131, Integer.Sparse.eval_collectBalanced, rawRowCheck15131]

def rawRow15132 : Integer.Sparse Key := [(key1700, -2), (key1706, -2), (key1756, -2), (key1700, 6), (key1851, -2), (key1855, -2), (key1886, -2), (key1277, 2), (key1283, 2), (key1700, 2), (key1855, 2), (key1756, 2), (key1886, 2), (key1277, -2), (key1700, -2), (key1851, -2), (key1855, 6), (key1283, -2), (key1706, -2), (key1855, -2)]

theorem rawRowCheck15132 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form11 = rawRow15132 := by decide +kernel

def row15132 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15132 : row15132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15132 := by decide +kernel

theorem rowEval15132 (x : Key → ℝ) : Integer.Sparse.eval row15132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15132, Integer.Sparse.eval_collectBalanced, rawRowCheck15132]

def rawRow15133 : Integer.Sparse Key := [(key1706, -2), (key1700, -2), (key1756, -2), (key1700, 6), (key1855, -2), (key1851, -2), (key1886, -2), (key1283, 2), (key1277, 2), (key1855, 2), (key1700, 2), (key1886, 2), (key1756, 2), (key1277, -2), (key1851, -2), (key1700, -2), (key1855, 6), (key1283, -2), (key1855, -2), (key1706, -2)]

theorem rawRowCheck15133 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form11 = rawRow15133 := by decide +kernel

def row15133 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15133 : row15133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15133 := by decide +kernel

theorem rowEval15133 (x : Key → ℝ) : Integer.Sparse.eval row15133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15133, Integer.Sparse.eval_collectBalanced, rawRowCheck15133]

def rawRow15134 : Integer.Sparse Key := [(key1700, -2), (key1756, -2), (key1706, -2), (key1700, 6), (key1851, -2), (key1886, -2), (key1855, -2), (key1700, 2), (key1756, 2), (key1277, 2), (key1886, 2), (key1283, 2), (key1855, 2), (key1700, -2), (key1277, -2), (key1851, -2), (key1855, 6), (key1706, -2), (key1283, -2), (key1855, -2)]

theorem rawRowCheck15134 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form11 = rawRow15134 := by decide +kernel

def row15134 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15134 : row15134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15134 := by decide +kernel

theorem rowEval15134 (x : Key → ℝ) : Integer.Sparse.eval row15134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15134, Integer.Sparse.eval_collectBalanced, rawRowCheck15134]

def rawRow15135 : Integer.Sparse Key := [(key1756, -2), (key1700, -2), (key1706, -2), (key1700, 6), (key1886, -2), (key1851, -2), (key1855, -2), (key1756, 2), (key1700, 2), (key1886, 2), (key1277, 2), (key1855, 2), (key1283, 2), (key1700, -2), (key1851, -2), (key1277, -2), (key1855, 6), (key1706, -2), (key1855, -2), (key1283, -2)]

theorem rawRowCheck15135 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form11 = rawRow15135 := by decide +kernel

def row15135 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15135 : row15135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15135 := by decide +kernel

theorem rowEval15135 (x : Key → ℝ) : Integer.Sparse.eval row15135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form11) x := by
  rw [rowCheck15135, Integer.Sparse.eval_collectBalanced, rawRowCheck15135]

def rawRow15136 : Integer.Sparse Key := [(key1706, -2), (key1756, -2), (key1700, -2), (key1700, 6), (key1855, -2), (key1886, -2), (key1851, -2), (key1855, 2), (key1886, 2), (key1283, 2), (key1756, 2), (key1277, 2), (key1700, 2), (key1851, -2), (key1277, -2), (key1700, -2), (key1855, 6), (key1855, -2), (key1283, -2), (key1706, -2)]

theorem rawRowCheck15136 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form11 = rawRow15136 := by decide +kernel

def row15136 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15136 : row15136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15136 := by decide +kernel

theorem rowEval15136 (x : Key → ℝ) : Integer.Sparse.eval row15136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15136, Integer.Sparse.eval_collectBalanced, rawRowCheck15136]

def rawRow15137 : Integer.Sparse Key := [(key1756, -2), (key1706, -2), (key1700, -2), (key1700, 6), (key1886, -2), (key1855, -2), (key1851, -2), (key1886, 2), (key1855, 2), (key1756, 2), (key1283, 2), (key1700, 2), (key1277, 2), (key1851, -2), (key1700, -2), (key1277, -2), (key1855, 6), (key1855, -2), (key1706, -2), (key1283, -2)]

theorem rawRowCheck15137 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form11 = rawRow15137 := by decide +kernel

def row15137 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15137 : row15137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15137 := by decide +kernel

theorem rowEval15137 (x : Key → ℝ) : Integer.Sparse.eval row15137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form11) x := by
  rw [rowCheck15137, Integer.Sparse.eval_collectBalanced, rawRowCheck15137]

def rawRow15138 : Integer.Sparse Key := [(key1851, -2), (key1855, -2), (key1855, -2), (key1886, 6), (key1277, -2), (key1283, -2), (key1283, -2), (key1700, 2), (key1706, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1855, 2), (key1756, -2), (key1756, -2), (key1886, -2), (key1277, 6), (key1700, -2), (key1700, -2), (key1851, -2)]

theorem rawRowCheck15138 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form11 = rawRow15138 := by decide +kernel

def row15138 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

theorem rowCheck15138 : row15138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15138 := by decide +kernel

theorem rowEval15138 (x : Key → ℝ) : Integer.Sparse.eval row15138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15138, Integer.Sparse.eval_collectBalanced, rawRowCheck15138]

def rawRow15139 : Integer.Sparse Key := [(key1855, -2), (key1851, -2), (key1855, -2), (key1886, 6), (key1283, -2), (key1277, -2), (key1283, -2), (key1706, 2), (key1700, 2), (key1855, 2), (key1700, 2), (key1855, 2), (key1706, 2), (key1756, -2), (key1886, -2), (key1756, -2), (key1277, 6), (key1700, -2), (key1851, -2), (key1700, -2)]

theorem rawRowCheck15139 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form11 = rawRow15139 := by decide +kernel

def row15139 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

theorem rowCheck15139 : row15139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15139 := by decide +kernel

theorem rowEval15139 (x : Key → ℝ) : Integer.Sparse.eval row15139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15139, Integer.Sparse.eval_collectBalanced, rawRowCheck15139]

def rawRow15140 : Integer.Sparse Key := [(key1855, -2), (key1855, -2), (key1851, -2), (key1886, 6), (key1283, -2), (key1283, -2), (key1277, -2), (key1855, 2), (key1855, 2), (key1706, 2), (key1706, 2), (key1700, 2), (key1700, 2), (key1886, -2), (key1756, -2), (key1756, -2), (key1277, 6), (key1851, -2), (key1700, -2), (key1700, -2)]

theorem rawRowCheck15140 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form11 = rawRow15140 := by decide +kernel

def row15140 : Integer.Sparse Key := [(key1277, 4), (key1283, -4), (key1706, 4), (key1756, -4), (key1851, -4), (key1886, 4)]

theorem rowCheck15140 : row15140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15140 := by decide +kernel

theorem rowEval15140 (x : Key → ℝ) : Integer.Sparse.eval row15140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15140, Integer.Sparse.eval_collectBalanced, rawRowCheck15140]

def rawRow15141 : Integer.Sparse Key := [(key1851, -2), (key1855, -2), (key1886, -2), (key1855, 6), (key1700, -2), (key1706, -2), (key1756, -2), (key1277, 2), (key1283, 2), (key1700, 2), (key1855, 2), (key1756, 2), (key1886, 2), (key1283, -2), (key1706, -2), (key1855, -2), (key1700, 6), (key1277, -2), (key1700, -2), (key1851, -2)]

theorem rawRowCheck15141 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form11 = rawRow15141 := by decide +kernel

def row15141 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15141 : row15141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15141 := by decide +kernel

theorem rowEval15141 (x : Key → ℝ) : Integer.Sparse.eval row15141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15141, Integer.Sparse.eval_collectBalanced, rawRowCheck15141]

def rawRow15142 : Integer.Sparse Key := [(key1855, -2), (key1851, -2), (key1886, -2), (key1855, 6), (key1706, -2), (key1700, -2), (key1756, -2), (key1283, 2), (key1277, 2), (key1855, 2), (key1700, 2), (key1886, 2), (key1756, 2), (key1283, -2), (key1855, -2), (key1706, -2), (key1700, 6), (key1277, -2), (key1851, -2), (key1700, -2)]

theorem rawRowCheck15142 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form11 = rawRow15142 := by decide +kernel

def row15142 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15142 : row15142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15142 := by decide +kernel

theorem rowEval15142 (x : Key → ℝ) : Integer.Sparse.eval row15142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15142, Integer.Sparse.eval_collectBalanced, rawRowCheck15142]

def rawRow15143 : Integer.Sparse Key := [(key1851, -2), (key1886, -2), (key1855, -2), (key1855, 6), (key1700, -2), (key1756, -2), (key1706, -2), (key1700, 2), (key1756, 2), (key1277, 2), (key1886, 2), (key1283, 2), (key1855, 2), (key1706, -2), (key1283, -2), (key1855, -2), (key1700, 6), (key1700, -2), (key1277, -2), (key1851, -2)]

theorem rawRowCheck15143 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form11 = rawRow15143 := by decide +kernel

def row15143 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15143 : row15143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15143 := by decide +kernel

theorem rowEval15143 (x : Key → ℝ) : Integer.Sparse.eval row15143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15143, Integer.Sparse.eval_collectBalanced, rawRowCheck15143]

def rawRow15144 : Integer.Sparse Key := [(key1886, -2), (key1851, -2), (key1855, -2), (key1855, 6), (key1756, -2), (key1700, -2), (key1706, -2), (key1756, 2), (key1700, 2), (key1886, 2), (key1277, 2), (key1855, 2), (key1283, 2), (key1706, -2), (key1855, -2), (key1283, -2), (key1700, 6), (key1700, -2), (key1851, -2), (key1277, -2)]

theorem rawRowCheck15144 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form11 = rawRow15144 := by decide +kernel

def row15144 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15144 : row15144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15144 := by decide +kernel

theorem rowEval15144 (x : Key → ℝ) : Integer.Sparse.eval row15144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form11) x := by
  rw [rowCheck15144, Integer.Sparse.eval_collectBalanced, rawRowCheck15144]

def rawRow15145 : Integer.Sparse Key := [(key1855, -2), (key1886, -2), (key1851, -2), (key1855, 6), (key1706, -2), (key1756, -2), (key1700, -2), (key1855, 2), (key1886, 2), (key1283, 2), (key1756, 2), (key1277, 2), (key1700, 2), (key1855, -2), (key1283, -2), (key1706, -2), (key1700, 6), (key1851, -2), (key1277, -2), (key1700, -2)]

theorem rawRowCheck15145 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form11 = rawRow15145 := by decide +kernel

def row15145 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15145 : row15145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15145 := by decide +kernel

theorem rowEval15145 (x : Key → ℝ) : Integer.Sparse.eval row15145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15145, Integer.Sparse.eval_collectBalanced, rawRowCheck15145]

def rawRow15146 : Integer.Sparse Key := [(key1886, -2), (key1855, -2), (key1851, -2), (key1855, 6), (key1756, -2), (key1706, -2), (key1700, -2), (key1886, 2), (key1855, 2), (key1756, 2), (key1283, 2), (key1700, 2), (key1277, 2), (key1855, -2), (key1706, -2), (key1283, -2), (key1700, 6), (key1851, -2), (key1700, -2), (key1277, -2)]

theorem rawRowCheck15146 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form11 = rawRow15146 := by decide +kernel

def row15146 : Integer.Sparse Key := [(key1700, 4), (key1706, -4), (key1851, -4), (key1855, 4)]

theorem rowCheck15146 : row15146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15146 := by decide +kernel

theorem rowEval15146 (x : Key → ℝ) : Integer.Sparse.eval row15146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form11) x := by
  rw [rowCheck15146, Integer.Sparse.eval_collectBalanced, rawRowCheck15146]

def rawRow15147 : Integer.Sparse Key := [(key1855, -2), (key1855, -2), (key1886, -2), (key1851, 6), (key1855, -2), (key1855, -2), (key1886, -2), (key1283, 2), (key1283, 2), (key1706, 2), (key1706, 2), (key1756, 2), (key1756, 2), (key1277, -2), (key1700, -2), (key1700, -2), (key1851, 6), (key1277, -2), (key1700, -2), (key1700, -2)]

theorem rawRowCheck15147 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form11 = rawRow15147 := by decide +kernel

def row15147 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

theorem rowCheck15147 : row15147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15147 := by decide +kernel

theorem rowEval15147 (x : Key → ℝ) : Integer.Sparse.eval row15147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15147, Integer.Sparse.eval_collectBalanced, rawRowCheck15147]

def rawRow15148 : Integer.Sparse Key := [(key1855, -2), (key1886, -2), (key1855, -2), (key1851, 6), (key1855, -2), (key1886, -2), (key1855, -2), (key1706, 2), (key1756, 2), (key1283, 2), (key1756, 2), (key1283, 2), (key1706, 2), (key1700, -2), (key1277, -2), (key1700, -2), (key1851, 6), (key1700, -2), (key1277, -2), (key1700, -2)]

theorem rawRowCheck15148 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form11 = rawRow15148 := by decide +kernel

def row15148 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

theorem rowCheck15148 : row15148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15148 := by decide +kernel

theorem rowEval15148 (x : Key → ℝ) : Integer.Sparse.eval row15148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15148, Integer.Sparse.eval_collectBalanced, rawRowCheck15148]

def rawRow15149 : Integer.Sparse Key := [(key1886, -2), (key1855, -2), (key1855, -2), (key1851, 6), (key1886, -2), (key1855, -2), (key1855, -2), (key1756, 2), (key1706, 2), (key1756, 2), (key1283, 2), (key1706, 2), (key1283, 2), (key1700, -2), (key1700, -2), (key1277, -2), (key1851, 6), (key1700, -2), (key1700, -2), (key1277, -2)]

theorem rawRowCheck15149 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form11 = rawRow15149 := by decide +kernel

def row15149 : Integer.Sparse Key := [(key1277, -4), (key1283, 4), (key1700, -8), (key1706, 4), (key1756, 4), (key1851, 12), (key1855, -8), (key1886, -4)]

theorem rowCheck15149 : row15149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15149 := by decide +kernel

theorem rowEval15149 (x : Key → ℝ) : Integer.Sparse.eval row15149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form11) x := by
  rw [rowCheck15149, Integer.Sparse.eval_collectBalanced, rawRowCheck15149]

def rawRow15150 : Integer.Sparse Key := [(key2362, 2), (key2365, 2), (key2365, 2), (key2365, -2), (key2365, -2), (key2367, -2), (key2457, 2), (key2460, 2), (key2460, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2533, 4), (key2564, 4), (key2564, 4)]

theorem rawRowCheck15150 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form12 = rawRow15150 := by decide +kernel

def row15150 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

theorem rowCheck15150 : row15150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15150 := by decide +kernel

theorem rowEval15150 (x : Key → ℝ) : Integer.Sparse.eval row15150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15150, Integer.Sparse.eval_collectBalanced, rawRowCheck15150]

def rawRow15151 : Integer.Sparse Key := [(key2365, 2), (key2362, 2), (key2365, 2), (key2365, -2), (key2367, -2), (key2365, -2), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2564, 4), (key2533, 4), (key2564, 4)]

theorem rawRowCheck15151 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form12 = rawRow15151 := by decide +kernel

def row15151 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

theorem rowCheck15151 : row15151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15151 := by decide +kernel

theorem rowEval15151 (x : Key → ℝ) : Integer.Sparse.eval row15151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15151, Integer.Sparse.eval_collectBalanced, rawRowCheck15151]

def rawRow15152 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2362, 2), (key2367, -2), (key2365, -2), (key2365, -2), (key2460, 2), (key2460, 2), (key2457, 2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2564, 4), (key2564, 4), (key2533, 4)]

theorem rawRowCheck15152 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form12 = rawRow15152 := by decide +kernel

def row15152 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2532, -6), (key2533, 2), (key2562, -2), (key2564, 6)]

theorem rowCheck15152 : row15152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15152 := by decide +kernel

theorem rowEval15152 (x : Key → ℝ) : Integer.Sparse.eval row15152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15152, Integer.Sparse.eval_collectBalanced, rawRowCheck15152]

def rawRow15153 : Integer.Sparse Key := [(key2365, 2), (key2365, 2), (key2367, 2), (key2362, -2), (key2365, -2), (key2365, -2), (key2521, 2), (key2521, 2), (key2525, 2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, -1), (key2533, -1), (key2532, -1), (key2564, -1), (key2533, -1), (key2564, -1), (key2532, 4), (key2532, 4), (key2562, 4)]

theorem rawRowCheck15153 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form12 = rawRow15153 := by decide +kernel

def row15153 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

theorem rowCheck15153 : row15153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15153 := by decide +kernel

theorem rowEval15153 (x : Key → ℝ) : Integer.Sparse.eval row15153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15153, Integer.Sparse.eval_collectBalanced, rawRowCheck15153]

def rawRow15154 : Integer.Sparse Key := [(key2365, 2), (key2367, 2), (key2365, 2), (key2365, -2), (key2362, -2), (key2365, -2), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2533, -1), (key2532, 4), (key2562, 4), (key2532, 4)]

theorem rawRowCheck15154 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form12 = rawRow15154 := by decide +kernel

def row15154 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

theorem rowCheck15154 : row15154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15154 := by decide +kernel

theorem rowEval15154 (x : Key → ℝ) : Integer.Sparse.eval row15154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15154, Integer.Sparse.eval_collectBalanced, rawRowCheck15154]

def rawRow15155 : Integer.Sparse Key := [(key2367, 2), (key2365, 2), (key2365, 2), (key2365, -2), (key2365, -2), (key2362, -2), (key2525, 2), (key2521, 2), (key2521, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, -1), (key2564, -1), (key2533, -1), (key2533, -1), (key2532, -1), (key2532, -1), (key2562, 4), (key2532, 4), (key2532, 4)]

theorem rawRowCheck15155 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form12 = rawRow15155 := by decide +kernel

def row15155 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2532, 6), (key2533, -2), (key2562, 2), (key2564, -6)]

theorem rowCheck15155 : row15155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15155 := by decide +kernel

theorem rowEval15155 (x : Key → ℝ) : Integer.Sparse.eval row15155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15155, Integer.Sparse.eval_collectBalanced, rawRowCheck15155]

def rawRow15156 : Integer.Sparse Key := [(key2457, 2), (key2460, 2), (key2460, 2), (key2521, -2), (key2521, -2), (key2525, -2), (key2362, 2), (key2365, 2), (key2365, 2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2533, 4), (key2564, 4), (key2564, 4)]

theorem rawRowCheck15156 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form12 = rawRow15156 := by decide +kernel

def row15156 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

theorem rowCheck15156 : row15156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15156 := by decide +kernel

theorem rowEval15156 (x : Key → ℝ) : Integer.Sparse.eval row15156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15156, Integer.Sparse.eval_collectBalanced, rawRowCheck15156]

def rawRow15157 : Integer.Sparse Key := [(key2460, 2), (key2457, 2), (key2460, 2), (key2521, -2), (key2525, -2), (key2521, -2), (key2365, 2), (key2362, 2), (key2365, 2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2564, 4), (key2533, 4), (key2564, 4)]

theorem rawRowCheck15157 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form12 = rawRow15157 := by decide +kernel

def row15157 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

theorem rowCheck15157 : row15157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15157 := by decide +kernel

theorem rowEval15157 (x : Key → ℝ) : Integer.Sparse.eval row15157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15157, Integer.Sparse.eval_collectBalanced, rawRowCheck15157]

def rawRow15158 : Integer.Sparse Key := [(key2460, 2), (key2460, 2), (key2457, 2), (key2525, -2), (key2521, -2), (key2521, -2), (key2365, 2), (key2365, 2), (key2362, 2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2564, 4), (key2564, 4), (key2533, 4)]

theorem rawRowCheck15158 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form12 = rawRow15158 := by decide +kernel

def row15158 : Integer.Sparse Key := [(key2362, 2), (key2367, -2), (key2457, 2), (key2460, 2), (key2521, -6), (key2525, -4), (key2532, -2), (key2533, 4), (key2562, -2), (key2564, 6)]

theorem rowCheck15158 : row15158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15158 := by decide +kernel

theorem rowEval15158 (x : Key → ℝ) : Integer.Sparse.eval row15158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15158, Integer.Sparse.eval_collectBalanced, rawRowCheck15158]

def rawRow15159 : Integer.Sparse Key := [(key2460, 2), (key2521, 2), (key2525, 2), (key2457, -2), (key2460, -2), (key2521, -2), (key2532, 2), (key2562, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, -1), (key2367, -1), (key2460, -1), (key2525, -1), (key2533, -1), (key2564, -1), (key2365, 4), (key2460, 4), (key2521, 4)]

theorem rawRowCheck15159 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form12 = rawRow15159 := by decide +kernel

def row15159 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck15159 : row15159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15159 := by decide +kernel

theorem rowEval15159 (x : Key → ℝ) : Integer.Sparse.eval row15159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15159, Integer.Sparse.eval_collectBalanced, rawRowCheck15159]

def rawRow15160 : Integer.Sparse Key := [(key2460, 2), (key2525, 2), (key2521, 2), (key2460, -2), (key2457, -2), (key2521, -2), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, -1), (key2365, -1), (key2525, -1), (key2460, -1), (key2564, -1), (key2533, -1), (key2365, 4), (key2521, 4), (key2460, 4)]

theorem rawRowCheck15160 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form12 = rawRow15160 := by decide +kernel

def row15160 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck15160 : row15160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15160 := by decide +kernel

theorem rowEval15160 (x : Key → ℝ) : Integer.Sparse.eval row15160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15160, Integer.Sparse.eval_collectBalanced, rawRowCheck15160]

def rawRow15161 : Integer.Sparse Key := [(key2521, 2), (key2460, 2), (key2525, 2), (key2457, -2), (key2521, -2), (key2460, -2), (key2562, 2), (key2532, 2), (key2564, 2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, -1), (key2533, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2460, 4), (key2365, 4), (key2521, 4)]

theorem rawRowCheck15161 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form12 = rawRow15161 := by decide +kernel

def row15161 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2525, -1), (key2532, 2), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck15161 : row15161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15161 := by decide +kernel

theorem rowEval15161 (x : Key → ℝ) : Integer.Sparse.eval row15161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15161, Integer.Sparse.eval_collectBalanced, rawRowCheck15161]

def rawRow15162 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2460, 2), (key2521, -2), (key2457, -2), (key2460, -2), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2525, -1), (key2367, -1), (key2460, 4), (key2521, 4), (key2365, 4)]

theorem rawRowCheck15162 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form12 = rawRow15162 := by decide +kernel

def row15162 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2525, -1), (key2532, 2), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck15162 : row15162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15162 := by decide +kernel

theorem rowEval15162 (x : Key → ℝ) : Integer.Sparse.eval row15162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form12) x := by
  rw [rowCheck15162, Integer.Sparse.eval_collectBalanced, rawRowCheck15162]

def rawRow15163 : Integer.Sparse Key := [(key2525, 2), (key2460, 2), (key2521, 2), (key2460, -2), (key2521, -2), (key2457, -2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2365, -1), (key2460, -1), (key2521, 4), (key2365, 4), (key2460, 4)]

theorem rawRowCheck15163 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form12 = rawRow15163 := by decide +kernel

def row15163 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck15163 : row15163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15163 := by decide +kernel

theorem rowEval15163 (x : Key → ℝ) : Integer.Sparse.eval row15163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15163, Integer.Sparse.eval_collectBalanced, rawRowCheck15163]

def rawRow15164 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2460, 2), (key2521, -2), (key2460, -2), (key2457, -2), (key2564, 2), (key2562, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, -1), (key2525, -1), (key2533, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, 4), (key2460, 4), (key2365, 4)]

theorem rawRowCheck15164 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form12 = rawRow15164 := by decide +kernel

def row15164 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 1), (key2525, -1), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck15164 : row15164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15164 := by decide +kernel

theorem rowEval15164 (x : Key → ℝ) : Integer.Sparse.eval row15164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form12) x := by
  rw [rowCheck15164, Integer.Sparse.eval_collectBalanced, rawRowCheck15164]

def rawRow15165 : Integer.Sparse Key := [(key2532, 2), (key2532, 2), (key2533, 2), (key2562, -2), (key2564, -2), (key2564, -2), (key2365, 2), (key2365, 2), (key2367, 2), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2564, -1), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2532, 4), (key2532, 4), (key2562, 4)]

theorem rawRowCheck15165 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form12 = rawRow15165 := by decide +kernel

def row15165 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

theorem rowCheck15165 : row15165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15165 := by decide +kernel

theorem rowEval15165 (x : Key → ℝ) : Integer.Sparse.eval row15165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15165, Integer.Sparse.eval_collectBalanced, rawRowCheck15165]

def rawRow15166 : Integer.Sparse Key := [(key2532, 2), (key2533, 2), (key2532, 2), (key2564, -2), (key2562, -2), (key2564, -2), (key2365, 2), (key2367, 2), (key2365, 2), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2532, 4), (key2562, 4), (key2532, 4)]

theorem rawRowCheck15166 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form12 = rawRow15166 := by decide +kernel

def row15166 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

theorem rowCheck15166 : row15166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15166 := by decide +kernel

theorem rowEval15166 (x : Key → ℝ) : Integer.Sparse.eval row15166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15166, Integer.Sparse.eval_collectBalanced, rawRowCheck15166]

def rawRow15167 : Integer.Sparse Key := [(key2533, 2), (key2532, 2), (key2532, 2), (key2564, -2), (key2564, -2), (key2562, -2), (key2367, 2), (key2365, 2), (key2365, 2), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, -1), (key2521, -1), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2562, 4), (key2532, 4), (key2532, 4)]

theorem rawRowCheck15167 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form12 = rawRow15167 := by decide +kernel

def row15167 : Integer.Sparse Key := [(key2362, -2), (key2367, 2), (key2457, -2), (key2460, -2), (key2521, -4), (key2525, -2), (key2532, 12), (key2533, 2), (key2562, 2), (key2564, -6)]

theorem rowCheck15167 : row15167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15167 := by decide +kernel

theorem rowEval15167 (x : Key → ℝ) : Integer.Sparse.eval row15167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15167, Integer.Sparse.eval_collectBalanced, rawRowCheck15167]

def rawRow15168 : Integer.Sparse Key := [(key2532, 2), (key2562, 2), (key2564, 2), (key2532, -2), (key2533, -2), (key2564, -2), (key2460, 2), (key2521, 2), (key2525, 2), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, -1), (key2564, -1), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2365, 4), (key2460, 4), (key2521, 4)]

theorem rawRowCheck15168 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form12 = rawRow15168 := by decide +kernel

def row15168 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

theorem rowCheck15168 : row15168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15168 := by decide +kernel

theorem rowEval15168 (x : Key → ℝ) : Integer.Sparse.eval row15168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15168, Integer.Sparse.eval_collectBalanced, rawRowCheck15168]

def rawRow15169 : Integer.Sparse Key := [(key2532, 2), (key2564, 2), (key2562, 2), (key2533, -2), (key2532, -2), (key2564, -2), (key2460, 2), (key2525, 2), (key2521, 2), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, -1), (key2525, -1), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2365, 4), (key2521, 4), (key2460, 4)]

theorem rawRowCheck15169 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form12 = rawRow15169 := by decide +kernel

def row15169 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

theorem rowCheck15169 : row15169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15169 := by decide +kernel

theorem rowEval15169 (x : Key → ℝ) : Integer.Sparse.eval row15169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15169, Integer.Sparse.eval_collectBalanced, rawRowCheck15169]

def rawRow15170 : Integer.Sparse Key := [(key2562, 2), (key2532, 2), (key2564, 2), (key2532, -2), (key2564, -2), (key2533, -2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2460, 4), (key2365, 4), (key2521, 4)]

theorem rawRowCheck15170 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form12 = rawRow15170 := by decide +kernel

def row15170 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 2), (key2525, 1), (key2533, -3), (key2562, 1), (key2564, -1)]

theorem rowCheck15170 : row15170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15170 := by decide +kernel

theorem rowEval15170 (x : Key → ℝ) : Integer.Sparse.eval row15170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15170, Integer.Sparse.eval_collectBalanced, rawRowCheck15170]

def rawRow15171 : Integer.Sparse Key := [(key2562, 2), (key2564, 2), (key2532, 2), (key2564, -2), (key2532, -2), (key2533, -2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, -1), (key2367, -1), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2460, 4), (key2521, 4), (key2365, 4)]

theorem rawRowCheck15171 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form12 = rawRow15171 := by decide +kernel

def row15171 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 2), (key2525, 1), (key2533, -3), (key2562, 1), (key2564, -1)]

theorem rowCheck15171 : row15171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15171 := by decide +kernel

theorem rowEval15171 (x : Key → ℝ) : Integer.Sparse.eval row15171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form12) x := by
  rw [rowCheck15171, Integer.Sparse.eval_collectBalanced, rawRowCheck15171]

def rawRow15172 : Integer.Sparse Key := [(key2564, 2), (key2532, 2), (key2562, 2), (key2533, -2), (key2564, -2), (key2532, -2), (key2525, 2), (key2460, 2), (key2521, 2), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, -1), (key2460, -1), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2521, 4), (key2365, 4), (key2460, 4)]

theorem rawRowCheck15172 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form12 = rawRow15172 := by decide +kernel

def row15172 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

theorem rowCheck15172 : row15172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15172 := by decide +kernel

theorem rowEval15172 (x : Key → ℝ) : Integer.Sparse.eval row15172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15172, Integer.Sparse.eval_collectBalanced, rawRowCheck15172]

def rawRow15173 : Integer.Sparse Key := [(key2564, 2), (key2562, 2), (key2532, 2), (key2564, -2), (key2533, -2), (key2532, -2), (key2525, 2), (key2521, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2521, 4), (key2460, 4), (key2365, 4)]

theorem rawRowCheck15173 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form12 = rawRow15173 := by decide +kernel

def row15173 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, -3), (key2460, 3), (key2521, 3), (key2525, 1), (key2532, -1), (key2533, -3), (key2562, 1), (key2564, -1)]

theorem rowCheck15173 : row15173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15173 := by decide +kernel

theorem rowEval15173 (x : Key → ℝ) : Integer.Sparse.eval row15173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form12) x := by
  rw [rowCheck15173, Integer.Sparse.eval_collectBalanced, rawRowCheck15173]

def rawRow15174 : Integer.Sparse Key := [(key2533, 2), (key2564, 2), (key2564, 2), (key2532, -2), (key2532, -2), (key2562, -2), (key2533, 2), (key2564, 2), (key2564, 2), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2532, -2), (key2532, -2), (key2562, -2), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2362, 4), (key2457, 4), (key2457, 4)]

theorem rawRowCheck15174 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form12 = rawRow15174 := by decide +kernel

def row15174 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

theorem rowCheck15174 : row15174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15174 := by decide +kernel

theorem rowEval15174 (x : Key → ℝ) : Integer.Sparse.eval row15174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15174, Integer.Sparse.eval_collectBalanced, rawRowCheck15174]

def rawRow15175 : Integer.Sparse Key := [(key2564, 2), (key2533, 2), (key2564, 2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, 2), (key2533, 2), (key2564, 2), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2532, -2), (key2562, -2), (key2532, -2), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2457, 4), (key2362, 4), (key2457, 4)]

theorem rawRowCheck15175 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form12 = rawRow15175 := by decide +kernel

def row15175 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

theorem rowCheck15175 : row15175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15175 := by decide +kernel

theorem rowEval15175 (x : Key → ℝ) : Integer.Sparse.eval row15175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15175, Integer.Sparse.eval_collectBalanced, rawRowCheck15175]

def rawRow15176 : Integer.Sparse Key := [(key2564, 2), (key2564, 2), (key2533, 2), (key2562, -2), (key2532, -2), (key2532, -2), (key2564, 2), (key2564, 2), (key2533, 2), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2365, -1), (key2562, -2), (key2532, -2), (key2532, -2), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, -1), (key2365, -1), (key2457, 4), (key2457, 4), (key2362, 4)]

theorem rawRowCheck15176 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form12 = rawRow15176 := by decide +kernel

def row15176 : Integer.Sparse Key := [(key2362, 4), (key2365, -4), (key2457, 8), (key2460, -4), (key2521, -4), (key2532, -8), (key2533, 4), (key2562, -4), (key2564, 8)]

theorem rowCheck15176 : row15176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15176 := by decide +kernel

theorem rowEval15176 (x : Key → ℝ) : Integer.Sparse.eval row15176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form12) x := by
  rw [rowCheck15176, Integer.Sparse.eval_collectBalanced, rawRowCheck15176]

def rawRow15177 : Integer.Sparse Key := [(key2843, 4), (key2843, 4), (key2880, 4), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2995, 4), (key2995, 4), (key3002, 4)]

theorem rawRowCheck15177 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form0 = rawRow15177 := by decide +kernel

def row15177 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

theorem rowCheck15177 : row15177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15177 := by decide +kernel

theorem rowEval15177 (x : Key → ℝ) : Integer.Sparse.eval row15177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck15177, Integer.Sparse.eval_collectBalanced, rawRowCheck15177]

def rawRow15178 : Integer.Sparse Key := [(key2843, 4), (key2880, 4), (key2843, 4), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2995, 4), (key3002, 4), (key2995, 4)]

theorem rawRowCheck15178 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form0 = rawRow15178 := by decide +kernel

def row15178 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

theorem rowCheck15178 : row15178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15178 := by decide +kernel

theorem rowEval15178 (x : Key → ℝ) : Integer.Sparse.eval row15178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15178, Integer.Sparse.eval_collectBalanced, rawRowCheck15178]

def rawRow15179 : Integer.Sparse Key := [(key2880, 4), (key2843, 4), (key2843, 4), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key3002, 4), (key2995, 4), (key2995, 4)]

theorem rawRowCheck15179 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form0 = rawRow15179 := by decide +kernel

def row15179 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

theorem rowCheck15179 : row15179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15179 := by decide +kernel

theorem rowEval15179 (x : Key → ℝ) : Integer.Sparse.eval row15179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15179, Integer.Sparse.eval_collectBalanced, rawRowCheck15179]

def rawRow15180 : Integer.Sparse Key := [(key2766, 4), (key2887, 4), (key2910, 4), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2931, 4), (key2968, 4), (key2989, 4)]

theorem rawRowCheck15180 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form0 = rawRow15180 := by decide +kernel

def row15180 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15180 : row15180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15180 := by decide +kernel

theorem rowEval15180 (x : Key → ℝ) : Integer.Sparse.eval row15180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck15180, Integer.Sparse.eval_collectBalanced, rawRowCheck15180]

def rawRow15181 : Integer.Sparse Key := [(key2766, 4), (key2910, 4), (key2887, 4), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2931, 4), (key2989, 4), (key2968, 4)]

theorem rawRowCheck15181 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form0 = rawRow15181 := by decide +kernel

def row15181 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15181 : row15181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15181 := by decide +kernel

theorem rowEval15181 (x : Key → ℝ) : Integer.Sparse.eval row15181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15181, Integer.Sparse.eval_collectBalanced, rawRowCheck15181]

def rawRow15182 : Integer.Sparse Key := [(key2887, 4), (key2766, 4), (key2910, 4), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2968, 4), (key2931, 4), (key2989, 4)]

theorem rawRowCheck15182 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form0 = rawRow15182 := by decide +kernel

def row15182 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15182 : row15182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15182 := by decide +kernel

theorem rowEval15182 (x : Key → ℝ) : Integer.Sparse.eval row15182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck15182, Integer.Sparse.eval_collectBalanced, rawRowCheck15182]

def rawRow15183 : Integer.Sparse Key := [(key2887, 4), (key2910, 4), (key2766, 4), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2968, 4), (key2989, 4), (key2931, 4)]

theorem rawRowCheck15183 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form0 = rawRow15183 := by decide +kernel

def row15183 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15183 : row15183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15183 := by decide +kernel

theorem rowEval15183 (x : Key → ℝ) : Integer.Sparse.eval row15183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15183, Integer.Sparse.eval_collectBalanced, rawRowCheck15183]

def rawRow15184 : Integer.Sparse Key := [(key2910, 4), (key2766, 4), (key2887, 4), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2989, 4), (key2931, 4), (key2968, 4)]

theorem rawRowCheck15184 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form0 = rawRow15184 := by decide +kernel

def row15184 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15184 : row15184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15184 := by decide +kernel

theorem rowEval15184 (x : Key → ℝ) : Integer.Sparse.eval row15184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15184, Integer.Sparse.eval_collectBalanced, rawRowCheck15184]

def rawRow15185 : Integer.Sparse Key := [(key2910, 4), (key2887, 4), (key2766, 4), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2989, 4), (key2968, 4), (key2931, 4)]

theorem rawRowCheck15185 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form0 = rawRow15185 := by decide +kernel

def row15185 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15185 : row15185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15185 := by decide +kernel

theorem rowEval15185 (x : Key → ℝ) : Integer.Sparse.eval row15185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15185, Integer.Sparse.eval_collectBalanced, rawRowCheck15185]

def rawRow15186 : Integer.Sparse Key := [(key2843, 4), (key2843, 4), (key2880, 4), (key2966, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2989, -2), (key2887, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2910, -2), (key2995, 4), (key2995, 4), (key3002, 4)]

theorem rawRowCheck15186 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form0 = rawRow15186 := by decide +kernel

def row15186 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

theorem rowCheck15186 : row15186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15186 := by decide +kernel

theorem rowEval15186 (x : Key → ℝ) : Integer.Sparse.eval row15186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck15186, Integer.Sparse.eval_collectBalanced, rawRowCheck15186]

def rawRow15187 : Integer.Sparse Key := [(key2843, 4), (key2880, 4), (key2843, 4), (key2968, -2), (key2966, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2995, 4), (key3002, 4), (key2995, 4)]

theorem rawRowCheck15187 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form0 = rawRow15187 := by decide +kernel

def row15187 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

theorem rowCheck15187 : row15187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15187 := by decide +kernel

theorem rowEval15187 (x : Key → ℝ) : Integer.Sparse.eval row15187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15187, Integer.Sparse.eval_collectBalanced, rawRowCheck15187]

def rawRow15188 : Integer.Sparse Key := [(key2880, 4), (key2843, 4), (key2843, 4), (key2989, -2), (key2989, -2), (key2968, -2), (key2968, -2), (key2966, -2), (key2966, -2), (key2910, -2), (key2910, -2), (key2889, -2), (key2889, -2), (key2887, -2), (key2887, -2), (key3002, 4), (key2995, 4), (key2995, 4)]

theorem rawRowCheck15188 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form0 = rawRow15188 := by decide +kernel

def row15188 : Integer.Sparse Key := [(key2843, 8), (key2880, 4), (key2887, -4), (key2889, -4), (key2910, -4), (key2966, -4), (key2968, -4), (key2989, -4), (key2995, 8), (key3002, 4)]

theorem rowCheck15188 : row15188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15188 := by decide +kernel

theorem rowEval15188 (x : Key → ℝ) : Integer.Sparse.eval row15188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15188, Integer.Sparse.eval_collectBalanced, rawRowCheck15188]

def rawRow15189 : Integer.Sparse Key := [(key2766, 4), (key2887, 4), (key2910, 4), (key2929, -2), (key2931, -2), (key2966, -2), (key2989, -2), (key2995, -2), (key3002, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2880, -2), (key2889, -2), (key2910, -2), (key2931, 4), (key2968, 4), (key2989, 4)]

theorem rawRowCheck15189 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form0 = rawRow15189 := by decide +kernel

def row15189 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15189 : row15189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15189 := by decide +kernel

theorem rowEval15189 (x : Key → ℝ) : Integer.Sparse.eval row15189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck15189, Integer.Sparse.eval_collectBalanced, rawRowCheck15189]

def rawRow15190 : Integer.Sparse Key := [(key2766, 4), (key2910, 4), (key2887, 4), (key2931, -2), (key2929, -2), (key2989, -2), (key2966, -2), (key3002, -2), (key2995, -2), (key2772, -2), (key2766, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2889, -2), (key2931, 4), (key2989, 4), (key2968, 4)]

theorem rawRowCheck15190 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form0 = rawRow15190 := by decide +kernel

def row15190 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15190 : row15190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15190 := by decide +kernel

theorem rowEval15190 (x : Key → ℝ) : Integer.Sparse.eval row15190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15190, Integer.Sparse.eval_collectBalanced, rawRowCheck15190]

def rawRow15191 : Integer.Sparse Key := [(key2887, 4), (key2766, 4), (key2910, 4), (key2966, -2), (key2995, -2), (key2929, -2), (key3002, -2), (key2931, -2), (key2989, -2), (key2843, -2), (key2889, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2968, 4), (key2931, 4), (key2989, 4)]

theorem rawRowCheck15191 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form0 = rawRow15191 := by decide +kernel

def row15191 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15191 : row15191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15191 := by decide +kernel

theorem rowEval15191 (x : Key → ℝ) : Integer.Sparse.eval row15191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck15191, Integer.Sparse.eval_collectBalanced, rawRowCheck15191]

def rawRow15192 : Integer.Sparse Key := [(key2887, 4), (key2910, 4), (key2766, 4), (key2995, -2), (key2966, -2), (key3002, -2), (key2929, -2), (key2989, -2), (key2931, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2880, -2), (key2772, -2), (key2968, 4), (key2989, 4), (key2931, 4)]

theorem rawRowCheck15192 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form0 = rawRow15192 := by decide +kernel

def row15192 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15192 : row15192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15192 := by decide +kernel

theorem rowEval15192 (x : Key → ℝ) : Integer.Sparse.eval row15192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15192, Integer.Sparse.eval_collectBalanced, rawRowCheck15192]

def rawRow15193 : Integer.Sparse Key := [(key2910, 4), (key2766, 4), (key2887, 4), (key2989, -2), (key3002, -2), (key2931, -2), (key2995, -2), (key2929, -2), (key2966, -2), (key2880, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2766, -2), (key2843, -2), (key2989, 4), (key2931, 4), (key2968, 4)]

theorem rawRowCheck15193 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form0 = rawRow15193 := by decide +kernel

def row15193 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15193 : row15193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15193 := by decide +kernel

theorem rowEval15193 (x : Key → ℝ) : Integer.Sparse.eval row15193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15193, Integer.Sparse.eval_collectBalanced, rawRowCheck15193]

def rawRow15194 : Integer.Sparse Key := [(key2910, 4), (key2887, 4), (key2766, 4), (key3002, -2), (key2989, -2), (key2995, -2), (key2931, -2), (key2966, -2), (key2929, -2), (key2910, -2), (key2880, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2989, 4), (key2968, 4), (key2931, 4)]

theorem rawRowCheck15194 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form0 = rawRow15194 := by decide +kernel

def row15194 : Integer.Sparse Key := [(key2766, 2), (key2772, -2), (key2843, -2), (key2880, -2), (key2887, 4), (key2889, -2), (key2910, 2), (key2929, -2), (key2931, 2), (key2966, -2), (key2968, 4), (key2989, 2), (key2995, -2), (key3002, -2)]

theorem rowCheck15194 : row15194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15194 := by decide +kernel

theorem rowEval15194 (x : Key → ℝ) : Integer.Sparse.eval row15194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15194, Integer.Sparse.eval_collectBalanced, rawRowCheck15194]

def rawRow15195 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1001, -2), (key1015, 6), (key1028, -2), (key1036, -2), (key1036, -2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1123, -2), (key1123, -2), (key1235, -2), (key1071, 6), (key1150, -2), (key1150, -2), (key1242, -2)]

theorem rawRowCheck15195 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form1 = rawRow15195 := by decide +kernel

def row15195 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck15195 : row15195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15195 := by decide +kernel

theorem rowEval15195 (x : Key → ℝ) : Integer.Sparse.eval row15195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck15195, Integer.Sparse.eval_collectBalanced, rawRowCheck15195]

def rawRow15196 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1001, -2), (key1015, 6), (key1036, -2), (key1028, -2), (key1036, -2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1123, -2), (key1235, -2), (key1123, -2), (key1071, 6), (key1150, -2), (key1242, -2), (key1150, -2)]

theorem rawRowCheck15196 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form1 = rawRow15196 := by decide +kernel

def row15196 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck15196 : row15196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15196 := by decide +kernel

theorem rowEval15196 (x : Key → ℝ) : Integer.Sparse.eval row15196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15196, Integer.Sparse.eval_collectBalanced, rawRowCheck15196]

def rawRow15197 : Integer.Sparse Key := [(key1001, -2), (key1001, -2), (key993, -2), (key1015, 6), (key1036, -2), (key1036, -2), (key1028, -2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, -2), (key1123, -2), (key1123, -2), (key1071, 6), (key1242, -2), (key1150, -2), (key1150, -2)]

theorem rawRowCheck15197 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form1 = rawRow15197 := by decide +kernel

def row15197 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck15197 : row15197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15197 := by decide +kernel

theorem rowEval15197 (x : Key → ℝ) : Integer.Sparse.eval row15197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15197, Integer.Sparse.eval_collectBalanced, rawRowCheck15197]

def rawRow15198 : Integer.Sparse Key := [(key993, -2), (key1001, -2), (key1015, -2), (key1001, 6), (key1106, -2), (key1114, -2), (key1123, -2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1036, -2), (key1114, -2), (key1232, -2), (key1150, 6), (key1071, -2), (key1150, -2), (key1242, -2)]

theorem rawRowCheck15198 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form1 = rawRow15198 := by decide +kernel

def row15198 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15198 : row15198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15198 := by decide +kernel

theorem rowEval15198 (x : Key → ℝ) : Integer.Sparse.eval row15198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck15198, Integer.Sparse.eval_collectBalanced, rawRowCheck15198]

def rawRow15199 : Integer.Sparse Key := [(key1001, -2), (key993, -2), (key1015, -2), (key1001, 6), (key1114, -2), (key1106, -2), (key1123, -2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1036, -2), (key1232, -2), (key1114, -2), (key1150, 6), (key1071, -2), (key1242, -2), (key1150, -2)]

theorem rawRowCheck15199 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form1 = rawRow15199 := by decide +kernel

def row15199 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15199 : row15199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15199 := by decide +kernel

theorem rowEval15199 (x : Key → ℝ) : Integer.Sparse.eval row15199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15199, Integer.Sparse.eval_collectBalanced, rawRowCheck15199]

def rawRow15200 : Integer.Sparse Key := [(key993, -2), (key1015, -2), (key1001, -2), (key1001, 6), (key1106, -2), (key1123, -2), (key1114, -2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1114, -2), (key1036, -2), (key1232, -2), (key1150, 6), (key1150, -2), (key1071, -2), (key1242, -2)]

theorem rawRowCheck15200 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form1 = rawRow15200 := by decide +kernel

def row15200 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15200 : row15200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15200 := by decide +kernel

theorem rowEval15200 (x : Key → ℝ) : Integer.Sparse.eval row15200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck15200, Integer.Sparse.eval_collectBalanced, rawRowCheck15200]

def rawRow15201 : Integer.Sparse Key := [(key1015, -2), (key993, -2), (key1001, -2), (key1001, 6), (key1123, -2), (key1106, -2), (key1114, -2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1114, -2), (key1232, -2), (key1036, -2), (key1150, 6), (key1150, -2), (key1242, -2), (key1071, -2)]

theorem rawRowCheck15201 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form1 = rawRow15201 := by decide +kernel

def row15201 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15201 : row15201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15201 := by decide +kernel

theorem rowEval15201 (x : Key → ℝ) : Integer.Sparse.eval row15201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15201, Integer.Sparse.eval_collectBalanced, rawRowCheck15201]

def rawRow15202 : Integer.Sparse Key := [(key1001, -2), (key1015, -2), (key993, -2), (key1001, 6), (key1114, -2), (key1123, -2), (key1106, -2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1232, -2), (key1036, -2), (key1114, -2), (key1150, 6), (key1242, -2), (key1071, -2), (key1150, -2)]

theorem rawRowCheck15202 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form1 = rawRow15202 := by decide +kernel

def row15202 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15202 : row15202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15202 := by decide +kernel

theorem rowEval15202 (x : Key → ℝ) : Integer.Sparse.eval row15202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15202, Integer.Sparse.eval_collectBalanced, rawRowCheck15202]

def rawRow15203 : Integer.Sparse Key := [(key1015, -2), (key1001, -2), (key993, -2), (key1001, 6), (key1123, -2), (key1114, -2), (key1106, -2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1232, -2), (key1114, -2), (key1036, -2), (key1150, 6), (key1242, -2), (key1150, -2), (key1071, -2)]

theorem rawRowCheck15203 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form1 = rawRow15203 := by decide +kernel

def row15203 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15203 : row15203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15203 := by decide +kernel

theorem rowEval15203 (x : Key → ℝ) : Integer.Sparse.eval row15203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15203, Integer.Sparse.eval_collectBalanced, rawRowCheck15203]

def rawRow15204 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1036, -2), (key1071, 6), (key993, -2), (key1001, -2), (key1001, -2), (key1106, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1150, -2), (key1150, -2), (key1242, -2), (key1015, 6), (key1123, -2), (key1123, -2), (key1235, -2)]

theorem rawRowCheck15204 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form1 = rawRow15204 := by decide +kernel

def row15204 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck15204 : row15204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15204 := by decide +kernel

theorem rowEval15204 (x : Key → ℝ) : Integer.Sparse.eval row15204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck15204, Integer.Sparse.eval_collectBalanced, rawRowCheck15204]

def rawRow15205 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1036, -2), (key1071, 6), (key1001, -2), (key993, -2), (key1001, -2), (key1114, 2), (key1106, 2), (key1232, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1150, -2), (key1242, -2), (key1150, -2), (key1015, 6), (key1123, -2), (key1235, -2), (key1123, -2)]

theorem rawRowCheck15205 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form1 = rawRow15205 := by decide +kernel

def row15205 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck15205 : row15205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15205 := by decide +kernel

theorem rowEval15205 (x : Key → ℝ) : Integer.Sparse.eval row15205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15205, Integer.Sparse.eval_collectBalanced, rawRowCheck15205]

def rawRow15206 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1028, -2), (key1071, 6), (key1001, -2), (key1001, -2), (key993, -2), (key1232, 2), (key1232, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, -2), (key1150, -2), (key1150, -2), (key1015, 6), (key1235, -2), (key1123, -2), (key1123, -2)]

theorem rawRowCheck15206 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form1 = rawRow15206 := by decide +kernel

def row15206 : Integer.Sparse Key := [(key993, -2), (key1001, -4), (key1015, 6), (key1028, -2), (key1036, -4), (key1071, 6), (key1106, 4), (key1114, 4), (key1123, -4), (key1150, -4), (key1232, 4), (key1235, -2), (key1242, -2)]

theorem rowCheck15206 : row15206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15206 := by decide +kernel

theorem rowEval15206 (x : Key → ℝ) : Integer.Sparse.eval row15206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15206, Integer.Sparse.eval_collectBalanced, rawRowCheck15206]

def rawRow15207 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1123, -2), (key1150, 6), (key993, -2), (key1001, -2), (key1015, -2), (key1028, 2), (key1036, 2), (key1106, 2), (key1232, 2), (key1123, 2), (key1235, 2), (key1071, -2), (key1150, -2), (key1242, -2), (key1001, 6), (key1036, -2), (key1114, -2), (key1232, -2)]

theorem rawRowCheck15207 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form1 = rawRow15207 := by decide +kernel

def row15207 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15207 : row15207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15207 := by decide +kernel

theorem rowEval15207 (x : Key → ℝ) : Integer.Sparse.eval row15207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck15207, Integer.Sparse.eval_collectBalanced, rawRowCheck15207]

def rawRow15208 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1123, -2), (key1150, 6), (key1001, -2), (key993, -2), (key1015, -2), (key1036, 2), (key1028, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1071, -2), (key1242, -2), (key1150, -2), (key1001, 6), (key1036, -2), (key1232, -2), (key1114, -2)]

theorem rawRowCheck15208 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form1 = rawRow15208 := by decide +kernel

def row15208 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15208 : row15208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15208 := by decide +kernel

theorem rowEval15208 (x : Key → ℝ) : Integer.Sparse.eval row15208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15208, Integer.Sparse.eval_collectBalanced, rawRowCheck15208]

def rawRow15209 : Integer.Sparse Key := [(key1106, -2), (key1123, -2), (key1114, -2), (key1150, 6), (key993, -2), (key1015, -2), (key1001, -2), (key1106, 2), (key1123, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1150, -2), (key1071, -2), (key1242, -2), (key1001, 6), (key1114, -2), (key1036, -2), (key1232, -2)]

theorem rawRowCheck15209 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form1 = rawRow15209 := by decide +kernel

def row15209 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15209 : row15209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15209 := by decide +kernel

theorem rowEval15209 (x : Key → ℝ) : Integer.Sparse.eval row15209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck15209, Integer.Sparse.eval_collectBalanced, rawRowCheck15209]

def rawRow15210 : Integer.Sparse Key := [(key1123, -2), (key1106, -2), (key1114, -2), (key1150, 6), (key1015, -2), (key993, -2), (key1001, -2), (key1123, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1232, 2), (key1036, 2), (key1150, -2), (key1242, -2), (key1071, -2), (key1001, 6), (key1114, -2), (key1232, -2), (key1036, -2)]

theorem rawRowCheck15210 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form1 = rawRow15210 := by decide +kernel

def row15210 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15210 : row15210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15210 := by decide +kernel

theorem rowEval15210 (x : Key → ℝ) : Integer.Sparse.eval row15210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15210, Integer.Sparse.eval_collectBalanced, rawRowCheck15210]

def rawRow15211 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1106, -2), (key1150, 6), (key1001, -2), (key1015, -2), (key993, -2), (key1232, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1028, 2), (key1106, 2), (key1242, -2), (key1071, -2), (key1150, -2), (key1001, 6), (key1232, -2), (key1036, -2), (key1114, -2)]

theorem rawRowCheck15211 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form1 = rawRow15211 := by decide +kernel

def row15211 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15211 : row15211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15211 := by decide +kernel

theorem rowEval15211 (x : Key → ℝ) : Integer.Sparse.eval row15211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15211, Integer.Sparse.eval_collectBalanced, rawRowCheck15211]

def rawRow15212 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1106, -2), (key1150, 6), (key1015, -2), (key1001, -2), (key993, -2), (key1235, 2), (key1232, 2), (key1123, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, -2), (key1150, -2), (key1071, -2), (key1001, 6), (key1232, -2), (key1114, -2), (key1036, -2)]

theorem rawRowCheck15212 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form1 = rawRow15212 := by decide +kernel

def row15212 : Integer.Sparse Key := [(key993, -2), (key1001, 4), (key1015, -2), (key1028, 2), (key1071, -2), (key1114, -4), (key1150, 4), (key1235, 2), (key1242, -2)]

theorem rowCheck15212 : row15212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15212 := by decide +kernel

theorem rowEval15212 (x : Key → ℝ) : Integer.Sparse.eval row15212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15212, Integer.Sparse.eval_collectBalanced, rawRowCheck15212]

def rawRow15213 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2376, -2), (key2388, 6), (key2762, -2), (key2768, -2), (key2768, -2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key2916, -2), (key2916, -2), (key2925, -2), (key3005, 6), (key3019, -2), (key3019, -2), (key3028, -2)]

theorem rawRowCheck15213 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form2 = rawRow15213 := by decide +kernel

def row15213 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

theorem rowCheck15213 : row15213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15213 := by decide +kernel

theorem rowEval15213 (x : Key → ℝ) : Integer.Sparse.eval row15213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck15213, Integer.Sparse.eval_collectBalanced, rawRowCheck15213]

def rawRow15214 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2376, -2), (key2388, 6), (key2768, -2), (key2762, -2), (key2768, -2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2916, -2), (key2925, -2), (key2916, -2), (key3005, 6), (key3019, -2), (key3028, -2), (key3019, -2)]

theorem rawRowCheck15214 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form2 = rawRow15214 := by decide +kernel

def row15214 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

theorem rowCheck15214 : row15214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15214 := by decide +kernel

theorem rowEval15214 (x : Key → ℝ) : Integer.Sparse.eval row15214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15214, Integer.Sparse.eval_collectBalanced, rawRowCheck15214]

def rawRow15215 : Integer.Sparse Key := [(key2376, -2), (key2376, -2), (key2370, -2), (key2388, 6), (key2768, -2), (key2768, -2), (key2762, -2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key2925, -2), (key2916, -2), (key2916, -2), (key3005, 6), (key3028, -2), (key3019, -2), (key3019, -2)]

theorem rawRowCheck15215 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form2 = rawRow15215 := by decide +kernel

def row15215 : Integer.Sparse Key := [(key2370, -2), (key2376, -4), (key2388, 6), (key2762, -2), (key2768, -4), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3005, 6), (key3019, -4), (key3028, -2)]

theorem rowCheck15215 : row15215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15215 := by decide +kernel

theorem rowEval15215 (x : Key → ℝ) : Integer.Sparse.eval row15215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15215, Integer.Sparse.eval_collectBalanced, rawRowCheck15215]

def rawRow15216 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2376, 6), (key2839, -2), (key2845, -2), (key2916, -2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key2768, -2), (key2845, -2), (key2876, -2), (key3019, 6), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rawRowCheck15216 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form2 = rawRow15216 := by decide +kernel

def row15216 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

theorem rowCheck15216 : row15216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15216 := by decide +kernel

theorem rowEval15216 (x : Key → ℝ) : Integer.Sparse.eval row15216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck15216, Integer.Sparse.eval_collectBalanced, rawRowCheck15216]

def rawRow15217 : Integer.Sparse Key := [(key2376, -2), (key2370, -2), (key2388, -2), (key2376, 6), (key2845, -2), (key2839, -2), (key2916, -2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key2768, -2), (key2876, -2), (key2845, -2), (key3019, 6), (key3005, -2), (key3028, -2), (key3019, -2)]

theorem rawRowCheck15217 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form2 = rawRow15217 := by decide +kernel

def row15217 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

theorem rowCheck15217 : row15217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15217 := by decide +kernel

theorem rowEval15217 (x : Key → ℝ) : Integer.Sparse.eval row15217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15217, Integer.Sparse.eval_collectBalanced, rawRowCheck15217]

def rawRow15218 : Integer.Sparse Key := [(key2370, -2), (key2388, -2), (key2376, -2), (key2376, 6), (key2839, -2), (key2916, -2), (key2845, -2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key2845, -2), (key2768, -2), (key2876, -2), (key3019, 6), (key3019, -2), (key3005, -2), (key3028, -2)]

theorem rawRowCheck15218 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form2 = rawRow15218 := by decide +kernel

def row15218 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

theorem rowCheck15218 : row15218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15218 := by decide +kernel

theorem rowEval15218 (x : Key → ℝ) : Integer.Sparse.eval row15218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck15218, Integer.Sparse.eval_collectBalanced, rawRowCheck15218]

def rawRow15219 : Integer.Sparse Key := [(key2388, -2), (key2370, -2), (key2376, -2), (key2376, 6), (key2916, -2), (key2839, -2), (key2845, -2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key2845, -2), (key2876, -2), (key2768, -2), (key3019, 6), (key3019, -2), (key3028, -2), (key3005, -2)]

theorem rawRowCheck15219 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form2 = rawRow15219 := by decide +kernel

def row15219 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

theorem rowCheck15219 : row15219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15219 := by decide +kernel

theorem rowEval15219 (x : Key → ℝ) : Integer.Sparse.eval row15219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15219, Integer.Sparse.eval_collectBalanced, rawRowCheck15219]

def rawRow15220 : Integer.Sparse Key := [(key2376, -2), (key2388, -2), (key2370, -2), (key2376, 6), (key2845, -2), (key2916, -2), (key2839, -2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key2876, -2), (key2768, -2), (key2845, -2), (key3019, 6), (key3028, -2), (key3005, -2), (key3019, -2)]

theorem rawRowCheck15220 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form2 = rawRow15220 := by decide +kernel

def row15220 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

theorem rowCheck15220 : row15220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15220 := by decide +kernel

theorem rowEval15220 (x : Key → ℝ) : Integer.Sparse.eval row15220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15220, Integer.Sparse.eval_collectBalanced, rawRowCheck15220]

def rawRow15221 : Integer.Sparse Key := [(key2388, -2), (key2376, -2), (key2370, -2), (key2376, 6), (key2916, -2), (key2845, -2), (key2839, -2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key2876, -2), (key2845, -2), (key2768, -2), (key3019, 6), (key3028, -2), (key3019, -2), (key3005, -2)]

theorem rawRowCheck15221 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form2 = rawRow15221 := by decide +kernel

def row15221 : Integer.Sparse Key := [(key2370, -2), (key2376, 4), (key2388, -2), (key2762, 2), (key2845, -4), (key2925, 2), (key3005, -2), (key3019, 4), (key3028, -2)]

theorem rowCheck15221 : row15221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15221 := by decide +kernel

theorem rowEval15221 (x : Key → ℝ) : Integer.Sparse.eval row15221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15221, Integer.Sparse.eval_collectBalanced, rawRowCheck15221]

def rawRow15222 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2404, -2), (key2435, 6), (key2583, -2), (key2589, -2), (key2589, -2), (key2839, 2), (key2845, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key2876, 2), (key3019, -2), (key3019, -2), (key3028, -2), (key2604, 6), (key2916, -2), (key2916, -2), (key2925, -2)]

theorem rawRowCheck15222 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form2 = rawRow15222 := by decide +kernel

def row15222 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

theorem rowCheck15222 : row15222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15222 := by decide +kernel

theorem rowEval15222 (x : Key → ℝ) : Integer.Sparse.eval row15222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck15222, Integer.Sparse.eval_collectBalanced, rawRowCheck15222]

def rawRow15223 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2404, -2), (key2435, 6), (key2589, -2), (key2583, -2), (key2589, -2), (key2845, 2), (key2839, 2), (key2876, 2), (key2839, 2), (key2876, 2), (key2845, 2), (key3019, -2), (key3028, -2), (key3019, -2), (key2604, 6), (key2916, -2), (key2925, -2), (key2916, -2)]

theorem rawRowCheck15223 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form2 = rawRow15223 := by decide +kernel

def row15223 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

theorem rowCheck15223 : row15223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15223 := by decide +kernel

theorem rowEval15223 (x : Key → ℝ) : Integer.Sparse.eval row15223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15223, Integer.Sparse.eval_collectBalanced, rawRowCheck15223]

def rawRow15224 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2398, -2), (key2435, 6), (key2589, -2), (key2589, -2), (key2583, -2), (key2876, 2), (key2876, 2), (key2845, 2), (key2845, 2), (key2839, 2), (key2839, 2), (key3028, -2), (key3019, -2), (key3019, -2), (key2604, 6), (key2925, -2), (key2916, -2), (key2916, -2)]

theorem rawRowCheck15224 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form2 = rawRow15224 := by decide +kernel

def row15224 : Integer.Sparse Key := [(key2398, -2), (key2404, -4), (key2435, 6), (key2583, -2), (key2589, -4), (key2604, 6), (key2839, 4), (key2845, 4), (key2876, 4), (key2916, -4), (key2925, -2), (key3019, -4), (key3028, -2)]

theorem rowCheck15224 : row15224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15224 := by decide +kernel

theorem rowEval15224 (x : Key → ℝ) : Integer.Sparse.eval row15224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15224, Integer.Sparse.eval_collectBalanced, rawRowCheck15224]

def rawRow15225 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2370, -2), (key2376, -2), (key2388, -2), (key2762, 2), (key2768, 2), (key2839, 2), (key2876, 2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2), (key2589, 6), (key2768, -2), (key2845, -2), (key2876, -2)]

theorem rawRowCheck15225 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form2 = rawRow15225 := by decide +kernel

def row15225 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rowCheck15225 : row15225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15225 := by decide +kernel

theorem rowEval15225 (x : Key → ℝ) : Integer.Sparse.eval row15225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck15225, Integer.Sparse.eval_collectBalanced, rawRowCheck15225]

def rawRow15226 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2478, -2), (key2501, 6), (key2376, -2), (key2370, -2), (key2388, -2), (key2768, 2), (key2762, 2), (key2876, 2), (key2839, 2), (key2925, 2), (key2916, 2), (key3005, -2), (key3028, -2), (key3019, -2), (key2589, 6), (key2768, -2), (key2876, -2), (key2845, -2)]

theorem rawRowCheck15226 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form2 = rawRow15226 := by decide +kernel

def row15226 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rowCheck15226 : row15226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15226 := by decide +kernel

theorem rowEval15226 (x : Key → ℝ) : Integer.Sparse.eval row15226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15226, Integer.Sparse.eval_collectBalanced, rawRowCheck15226]

def rawRow15227 : Integer.Sparse Key := [(key2464, -2), (key2478, -2), (key2470, -2), (key2501, 6), (key2370, -2), (key2388, -2), (key2376, -2), (key2839, 2), (key2916, 2), (key2762, 2), (key2925, 2), (key2768, 2), (key2876, 2), (key3019, -2), (key3005, -2), (key3028, -2), (key2589, 6), (key2845, -2), (key2768, -2), (key2876, -2)]

theorem rawRowCheck15227 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form2 = rawRow15227 := by decide +kernel

def row15227 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rowCheck15227 : row15227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15227 := by decide +kernel

theorem rowEval15227 (x : Key → ℝ) : Integer.Sparse.eval row15227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck15227, Integer.Sparse.eval_collectBalanced, rawRowCheck15227]

def rawRow15228 : Integer.Sparse Key := [(key2478, -2), (key2464, -2), (key2470, -2), (key2501, 6), (key2388, -2), (key2370, -2), (key2376, -2), (key2916, 2), (key2839, 2), (key2925, 2), (key2762, 2), (key2876, 2), (key2768, 2), (key3019, -2), (key3028, -2), (key3005, -2), (key2589, 6), (key2845, -2), (key2876, -2), (key2768, -2)]

theorem rawRowCheck15228 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form2 = rawRow15228 := by decide +kernel

def row15228 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rowCheck15228 : row15228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15228 := by decide +kernel

theorem rowEval15228 (x : Key → ℝ) : Integer.Sparse.eval row15228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15228, Integer.Sparse.eval_collectBalanced, rawRowCheck15228]

def rawRow15229 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2464, -2), (key2501, 6), (key2376, -2), (key2388, -2), (key2370, -2), (key2876, 2), (key2925, 2), (key2768, 2), (key2916, 2), (key2762, 2), (key2839, 2), (key3028, -2), (key3005, -2), (key3019, -2), (key2589, 6), (key2876, -2), (key2768, -2), (key2845, -2)]

theorem rawRowCheck15229 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form2 = rawRow15229 := by decide +kernel

def row15229 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rowCheck15229 : row15229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15229 := by decide +kernel

theorem rowEval15229 (x : Key → ℝ) : Integer.Sparse.eval row15229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck15229, Integer.Sparse.eval_collectBalanced, rawRowCheck15229]

def rawRow15230 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2464, -2), (key2501, 6), (key2388, -2), (key2376, -2), (key2370, -2), (key2925, 2), (key2876, 2), (key2916, 2), (key2768, 2), (key2839, 2), (key2762, 2), (key3028, -2), (key3019, -2), (key3005, -2), (key2589, 6), (key2876, -2), (key2845, -2), (key2768, -2)]

theorem rawRowCheck15230 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form2 = rawRow15230 := by decide +kernel

def row15230 : Integer.Sparse Key := [(key2370, -2), (key2376, -2), (key2388, -2), (key2464, -2), (key2470, -2), (key2478, -2), (key2501, 6), (key2589, 6), (key2762, 2), (key2839, 2), (key2845, -2), (key2916, 2), (key2925, 2), (key3005, -2), (key3019, -2), (key3028, -2)]

theorem rowCheck15230 : row15230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15230 := by decide +kernel

theorem rowEval15230 (x : Key → ℝ) : Integer.Sparse.eval row15230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck15230, Integer.Sparse.eval_collectBalanced, rawRowCheck15230]

def rawRow15231 : Integer.Sparse Key := [(key2610, 6), (key2626, -2), (key2626, -2), (key2635, -2), (key2665, 6), (key2700, -2), (key2700, -2), (key2721, -2), (key2780, -2), (key2780, -2), (key2789, -2), (key2803, -2), (key2803, -2), (key2824, -2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck15231 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form3 = rawRow15231 := by decide +kernel

def row15231 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck15231 : row15231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15231 := by decide +kernel

theorem rowEval15231 (x : Key → ℝ) : Integer.Sparse.eval row15231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck15231, Integer.Sparse.eval_collectBalanced, rawRowCheck15231]

end MUB6.Certificate.GramRows

end OAI
