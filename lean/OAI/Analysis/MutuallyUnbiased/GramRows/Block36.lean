import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1536 : Integer.Sparse Key := [(key2893, -2), (key2897, -2), (key2904, -2), (key2782, 1), (key2795, 1), (key2805, 1), (key2897, 1), (key2831, 1), (key2904, 1), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1)]

theorem rawRowCheck1536 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form2 = rawRow1536 := by decide +kernel

def row1536 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

theorem rowCheck1536 : row1536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1536 := by decide +kernel

theorem rowEval1536 (x : Key → ℝ) : Integer.Sparse.eval row1536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1536, Integer.Sparse.eval_collectBalanced, rawRowCheck1536]

def rawRow1537 : Integer.Sparse Key := [(key2897, -2), (key2893, -2), (key2904, -2), (key2795, 1), (key2782, 1), (key2897, 1), (key2805, 1), (key2904, 1), (key2831, 1), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1)]

theorem rawRowCheck1537 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form2 = rawRow1537 := by decide +kernel

def row1537 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

theorem rowCheck1537 : row1537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1537 := by decide +kernel

theorem rowEval1537 (x : Key → ℝ) : Integer.Sparse.eval row1537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1537, Integer.Sparse.eval_collectBalanced, rawRowCheck1537]

def rawRow1538 : Integer.Sparse Key := [(key2893, -2), (key2904, -2), (key2897, -2), (key2805, 1), (key2831, 1), (key2782, 1), (key2904, 1), (key2795, 1), (key2897, 1), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1)]

theorem rawRowCheck1538 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form2 = rawRow1538 := by decide +kernel

def row1538 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

theorem rowCheck1538 : row1538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1538 := by decide +kernel

theorem rowEval1538 (x : Key → ℝ) : Integer.Sparse.eval row1538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1538, Integer.Sparse.eval_collectBalanced, rawRowCheck1538]

def rawRow1539 : Integer.Sparse Key := [(key2904, -2), (key2893, -2), (key2897, -2), (key2831, 1), (key2805, 1), (key2904, 1), (key2782, 1), (key2897, 1), (key2795, 1), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1)]

theorem rawRowCheck1539 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form2 = rawRow1539 := by decide +kernel

def row1539 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

theorem rowCheck1539 : row1539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1539 := by decide +kernel

theorem rowEval1539 (x : Key → ℝ) : Integer.Sparse.eval row1539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1539, Integer.Sparse.eval_collectBalanced, rawRowCheck1539]

def rawRow1540 : Integer.Sparse Key := [(key2897, -2), (key2904, -2), (key2893, -2), (key2897, 1), (key2904, 1), (key2795, 1), (key2831, 1), (key2782, 1), (key2805, 1), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1)]

theorem rawRowCheck1540 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form2 = rawRow1540 := by decide +kernel

def row1540 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

theorem rowCheck1540 : row1540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1540 := by decide +kernel

theorem rowEval1540 (x : Key → ℝ) : Integer.Sparse.eval row1540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1540, Integer.Sparse.eval_collectBalanced, rawRowCheck1540]

def rawRow1541 : Integer.Sparse Key := [(key2904, -2), (key2897, -2), (key2893, -2), (key2904, 1), (key2897, 1), (key2831, 1), (key2795, 1), (key2805, 1), (key2782, 1), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

theorem rawRowCheck1541 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form2 = rawRow1541 := by decide +kernel

def row1541 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2893, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, 2), (key2976, 1), (key2983, 1)]

theorem rowCheck1541 : row1541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1541 := by decide +kernel

theorem rowEval1541 (x : Key → ℝ) : Integer.Sparse.eval row1541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1541, Integer.Sparse.eval_collectBalanced, rawRowCheck1541]

def rawRow1542 : Integer.Sparse Key := [(key2936, -2), (key2938, -2), (key2943, -2), (key2948, 1), (key2950, 1), (key2972, 1), (key2997, 1), (key2976, 1), (key2998, 1), (key2646, 2), (key2648, 2), (key2653, 2), (key2735, -1), (key2737, -1), (key2893, -1), (key2997, -1), (key2897, -1), (key2998, -1), (key2612, -1), (key2618, -1), (key2628, -1), (key2648, -1), (key2641, -1), (key2653, -1), (key2667, 1), (key2673, 1), (key2782, 1), (key2938, 1), (key2795, 1), (key2943, 1)]

theorem rawRowCheck1542 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form2 = rawRow1542 := by decide +kernel

def row1542 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

theorem rowCheck1542 : row1542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1542 := by decide +kernel

theorem rowEval1542 (x : Key → ℝ) : Integer.Sparse.eval row1542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1542, Integer.Sparse.eval_collectBalanced, rawRowCheck1542]

def rawRow1543 : Integer.Sparse Key := [(key2938, -2), (key2936, -2), (key2943, -2), (key2950, 1), (key2948, 1), (key2997, 1), (key2972, 1), (key2998, 1), (key2976, 1), (key2648, 2), (key2646, 2), (key2653, 2), (key2737, -1), (key2735, -1), (key2997, -1), (key2893, -1), (key2998, -1), (key2897, -1), (key2618, -1), (key2612, -1), (key2648, -1), (key2628, -1), (key2653, -1), (key2641, -1), (key2673, 1), (key2667, 1), (key2938, 1), (key2782, 1), (key2943, 1), (key2795, 1)]

theorem rawRowCheck1543 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form2 = rawRow1543 := by decide +kernel

def row1543 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

theorem rowCheck1543 : row1543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1543 := by decide +kernel

theorem rowEval1543 (x : Key → ℝ) : Integer.Sparse.eval row1543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1543, Integer.Sparse.eval_collectBalanced, rawRowCheck1543]

def rawRow1544 : Integer.Sparse Key := [(key2936, -2), (key2943, -2), (key2938, -2), (key2972, 1), (key2976, 1), (key2948, 1), (key2998, 1), (key2950, 1), (key2997, 1), (key2646, 2), (key2653, 2), (key2648, 2), (key2893, -1), (key2897, -1), (key2735, -1), (key2998, -1), (key2737, -1), (key2997, -1), (key2628, -1), (key2641, -1), (key2612, -1), (key2653, -1), (key2618, -1), (key2648, -1), (key2782, 1), (key2795, 1), (key2667, 1), (key2943, 1), (key2673, 1), (key2938, 1)]

theorem rawRowCheck1544 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form2 = rawRow1544 := by decide +kernel

def row1544 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

theorem rowCheck1544 : row1544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1544 := by decide +kernel

theorem rowEval1544 (x : Key → ℝ) : Integer.Sparse.eval row1544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1544, Integer.Sparse.eval_collectBalanced, rawRowCheck1544]

def rawRow1545 : Integer.Sparse Key := [(key2943, -2), (key2936, -2), (key2938, -2), (key2976, 1), (key2972, 1), (key2998, 1), (key2948, 1), (key2997, 1), (key2950, 1), (key2653, 2), (key2646, 2), (key2648, 2), (key2897, -1), (key2893, -1), (key2998, -1), (key2735, -1), (key2997, -1), (key2737, -1), (key2641, -1), (key2628, -1), (key2653, -1), (key2612, -1), (key2648, -1), (key2618, -1), (key2795, 1), (key2782, 1), (key2943, 1), (key2667, 1), (key2938, 1), (key2673, 1)]

theorem rawRowCheck1545 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form2 = rawRow1545 := by decide +kernel

def row1545 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

theorem rowCheck1545 : row1545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1545 := by decide +kernel

theorem rowEval1545 (x : Key → ℝ) : Integer.Sparse.eval row1545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1545, Integer.Sparse.eval_collectBalanced, rawRowCheck1545]

def rawRow1546 : Integer.Sparse Key := [(key2938, -2), (key2943, -2), (key2936, -2), (key2997, 1), (key2998, 1), (key2950, 1), (key2976, 1), (key2948, 1), (key2972, 1), (key2648, 2), (key2653, 2), (key2646, 2), (key2997, -1), (key2998, -1), (key2737, -1), (key2897, -1), (key2735, -1), (key2893, -1), (key2648, -1), (key2653, -1), (key2618, -1), (key2641, -1), (key2612, -1), (key2628, -1), (key2938, 1), (key2943, 1), (key2673, 1), (key2795, 1), (key2667, 1), (key2782, 1)]

theorem rawRowCheck1546 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form2 = rawRow1546 := by decide +kernel

def row1546 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

theorem rowCheck1546 : row1546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1546 := by decide +kernel

theorem rowEval1546 (x : Key → ℝ) : Integer.Sparse.eval row1546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1546, Integer.Sparse.eval_collectBalanced, rawRowCheck1546]

def rawRow1547 : Integer.Sparse Key := [(key2943, -2), (key2938, -2), (key2936, -2), (key2998, 1), (key2997, 1), (key2976, 1), (key2950, 1), (key2972, 1), (key2948, 1), (key2653, 2), (key2648, 2), (key2646, 2), (key2998, -1), (key2997, -1), (key2897, -1), (key2737, -1), (key2893, -1), (key2735, -1), (key2653, -1), (key2648, -1), (key2641, -1), (key2618, -1), (key2628, -1), (key2612, -1), (key2943, 1), (key2938, 1), (key2795, 1), (key2673, 1), (key2782, 1), (key2667, 1)]

theorem rawRowCheck1547 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form2 = rawRow1547 := by decide +kernel

def row1547 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, -1), (key2641, -1), (key2646, 2), (key2648, 1), (key2653, 1), (key2667, 1), (key2673, 1), (key2735, -1), (key2737, -1), (key2782, 1), (key2795, 1), (key2893, -1), (key2897, -1), (key2936, -2), (key2938, -1), (key2943, -1), (key2948, 1), (key2950, 1), (key2972, 1), (key2976, 1)]

theorem rowCheck1547 : row1547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1547 := by decide +kernel

theorem rowEval1547 (x : Key → ℝ) : Integer.Sparse.eval row1547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1547, Integer.Sparse.eval_collectBalanced, rawRowCheck1547]

def rawRow1548 : Integer.Sparse Key := [(key2972, -2), (key2976, -2), (key2983, -2), (key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2893, 2), (key2897, 2), (key2904, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1)]

theorem rawRowCheck1548 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form2 = rawRow1548 := by decide +kernel

def row1548 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

theorem rowCheck1548 : row1548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1548 := by decide +kernel

theorem rowEval1548 (x : Key → ℝ) : Integer.Sparse.eval row1548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1548, Integer.Sparse.eval_collectBalanced, rawRowCheck1548]

def rawRow1549 : Integer.Sparse Key := [(key2976, -2), (key2972, -2), (key2983, -2), (key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2897, 2), (key2893, 2), (key2904, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1)]

theorem rawRowCheck1549 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form2 = rawRow1549 := by decide +kernel

def row1549 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

theorem rowCheck1549 : row1549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1549 := by decide +kernel

theorem rowEval1549 (x : Key → ℝ) : Integer.Sparse.eval row1549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1549, Integer.Sparse.eval_collectBalanced, rawRowCheck1549]

def rawRow1550 : Integer.Sparse Key := [(key2972, -2), (key2983, -2), (key2976, -2), (key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2893, 2), (key2904, 2), (key2897, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1)]

theorem rawRowCheck1550 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form2 = rawRow1550 := by decide +kernel

def row1550 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

theorem rowCheck1550 : row1550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1550 := by decide +kernel

theorem rowEval1550 (x : Key → ℝ) : Integer.Sparse.eval row1550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1550, Integer.Sparse.eval_collectBalanced, rawRowCheck1550]

def rawRow1551 : Integer.Sparse Key := [(key2983, -2), (key2972, -2), (key2976, -2), (key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2904, 2), (key2893, 2), (key2897, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1)]

theorem rawRowCheck1551 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form2 = rawRow1551 := by decide +kernel

def row1551 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

theorem rowCheck1551 : row1551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1551 := by decide +kernel

theorem rowEval1551 (x : Key → ℝ) : Integer.Sparse.eval row1551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1551, Integer.Sparse.eval_collectBalanced, rawRowCheck1551]

def rawRow1552 : Integer.Sparse Key := [(key2976, -2), (key2983, -2), (key2972, -2), (key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2897, 2), (key2904, 2), (key2893, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1)]

theorem rawRowCheck1552 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form2 = rawRow1552 := by decide +kernel

def row1552 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

theorem rowCheck1552 : row1552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1552 := by decide +kernel

theorem rowEval1552 (x : Key → ℝ) : Integer.Sparse.eval row1552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1552, Integer.Sparse.eval_collectBalanced, rawRowCheck1552]

def rawRow1553 : Integer.Sparse Key := [(key2983, -2), (key2976, -2), (key2972, -2), (key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key2904, 2), (key2897, 2), (key2893, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

theorem rawRowCheck1553 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form2 = rawRow1553 := by decide +kernel

def row1553 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -2), (key2976, -1), (key2983, -1)]

theorem rowCheck1553 : row1553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1553 := by decide +kernel

theorem rowEval1553 (x : Key → ℝ) : Integer.Sparse.eval row1553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck1553, Integer.Sparse.eval_collectBalanced, rawRowCheck1553]

def rawRow1554 : Integer.Sparse Key := [(key998, -2), (key998, -2), (key1019, -2), (key1006, 6), (key1111, 2), (key1111, 2), (key1127, 2), (key1041, -2), (key1193, -2), (key1193, -2), (key1155, -6), (key1076, 2), (key1212, 2), (key1212, 2)]

theorem rawRowCheck1554 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form3 = rawRow1554 := by decide +kernel

def row1554 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

theorem rowCheck1554 : row1554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1554 := by decide +kernel

theorem rowEval1554 (x : Key → ℝ) : Integer.Sparse.eval row1554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1554, Integer.Sparse.eval_collectBalanced, rawRowCheck1554]

def rawRow1555 : Integer.Sparse Key := [(key998, -2), (key1019, -2), (key998, -2), (key1006, 6), (key1111, 2), (key1127, 2), (key1111, 2), (key1193, -2), (key1041, -2), (key1193, -2), (key1155, -6), (key1212, 2), (key1076, 2), (key1212, 2)]

theorem rawRowCheck1555 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form3 = rawRow1555 := by decide +kernel

def row1555 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

theorem rowCheck1555 : row1555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1555 := by decide +kernel

theorem rowEval1555 (x : Key → ℝ) : Integer.Sparse.eval row1555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1555, Integer.Sparse.eval_collectBalanced, rawRowCheck1555]

def rawRow1556 : Integer.Sparse Key := [(key1019, -2), (key998, -2), (key998, -2), (key1006, 6), (key1127, 2), (key1111, 2), (key1111, 2), (key1193, -2), (key1193, -2), (key1041, -2), (key1155, -6), (key1212, 2), (key1212, 2), (key1076, 2)]

theorem rawRowCheck1556 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form3 = rawRow1556 := by decide +kernel

def row1556 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

theorem rowCheck1556 : row1556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1556 := by decide +kernel

theorem rowEval1556 (x : Key → ℝ) : Integer.Sparse.eval row1556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1556, Integer.Sparse.eval_collectBalanced, rawRowCheck1556]

def rawRow1557 : Integer.Sparse Key := [(key998, -2), (key1006, -2), (key1019, -2), (key998, 6), (key1190, 2), (key1193, 2), (key1199, 2), (key1033, -2), (key1111, -2), (key1190, -2), (key1212, -6), (key1076, 2), (key1155, 2), (key1212, 2)]

theorem rawRowCheck1557 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form3 = rawRow1557 := by decide +kernel

def row1557 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

theorem rowCheck1557 : row1557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1557 := by decide +kernel

theorem rowEval1557 (x : Key → ℝ) : Integer.Sparse.eval row1557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1557, Integer.Sparse.eval_collectBalanced, rawRowCheck1557]

def rawRow1558 : Integer.Sparse Key := [(key1006, -2), (key998, -2), (key1019, -2), (key998, 6), (key1193, 2), (key1190, 2), (key1199, 2), (key1033, -2), (key1190, -2), (key1111, -2), (key1212, -6), (key1076, 2), (key1212, 2), (key1155, 2)]

theorem rawRowCheck1558 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form3 = rawRow1558 := by decide +kernel

def row1558 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

theorem rowCheck1558 : row1558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1558 := by decide +kernel

theorem rowEval1558 (x : Key → ℝ) : Integer.Sparse.eval row1558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1558, Integer.Sparse.eval_collectBalanced, rawRowCheck1558]

def rawRow1559 : Integer.Sparse Key := [(key998, -2), (key1019, -2), (key1006, -2), (key998, 6), (key1190, 2), (key1199, 2), (key1193, 2), (key1111, -2), (key1033, -2), (key1190, -2), (key1212, -6), (key1155, 2), (key1076, 2), (key1212, 2)]

theorem rawRowCheck1559 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form3 = rawRow1559 := by decide +kernel

def row1559 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

theorem rowCheck1559 : row1559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1559 := by decide +kernel

theorem rowEval1559 (x : Key → ℝ) : Integer.Sparse.eval row1559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1559, Integer.Sparse.eval_collectBalanced, rawRowCheck1559]

def rawRow1560 : Integer.Sparse Key := [(key1019, -2), (key998, -2), (key1006, -2), (key998, 6), (key1199, 2), (key1190, 2), (key1193, 2), (key1111, -2), (key1190, -2), (key1033, -2), (key1212, -6), (key1155, 2), (key1212, 2), (key1076, 2)]

theorem rawRowCheck1560 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form3 = rawRow1560 := by decide +kernel

def row1560 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

theorem rowCheck1560 : row1560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1560 := by decide +kernel

theorem rowEval1560 (x : Key → ℝ) : Integer.Sparse.eval row1560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1560, Integer.Sparse.eval_collectBalanced, rawRowCheck1560]

def rawRow1561 : Integer.Sparse Key := [(key1006, -2), (key1019, -2), (key998, -2), (key998, 6), (key1193, 2), (key1199, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key1111, -2), (key1212, -6), (key1212, 2), (key1076, 2), (key1155, 2)]

theorem rawRowCheck1561 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form3 = rawRow1561 := by decide +kernel

def row1561 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

theorem rowCheck1561 : row1561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1561 := by decide +kernel

theorem rowEval1561 (x : Key → ℝ) : Integer.Sparse.eval row1561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1561, Integer.Sparse.eval_collectBalanced, rawRowCheck1561]

def rawRow1562 : Integer.Sparse Key := [(key1019, -2), (key1006, -2), (key998, -2), (key998, 6), (key1199, 2), (key1193, 2), (key1190, 2), (key1190, -2), (key1111, -2), (key1033, -2), (key1212, -6), (key1212, 2), (key1155, 2), (key1076, 2)]

theorem rawRowCheck1562 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form3 = rawRow1562 := by decide +kernel

def row1562 : Integer.Sparse Key := [(key998, 4), (key1006, -2), (key1019, -2), (key1033, -2), (key1076, 2), (key1111, -2), (key1155, 2), (key1193, 2), (key1199, 2), (key1212, -4)]

theorem rowCheck1562 : row1562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1562 := by decide +kernel

theorem rowEval1562 (x : Key → ℝ) : Integer.Sparse.eval row1562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1562, Integer.Sparse.eval_collectBalanced, rawRowCheck1562]

def rawRow1563 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1127, -2), (key1155, 6), (key998, 2), (key998, 2), (key1019, 2), (key1076, -2), (key1212, -2), (key1212, -2), (key1006, -6), (key1041, 2), (key1193, 2), (key1193, 2)]

theorem rawRowCheck1563 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form3 = rawRow1563 := by decide +kernel

def row1563 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

theorem rowCheck1563 : row1563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1563 := by decide +kernel

theorem rowEval1563 (x : Key → ℝ) : Integer.Sparse.eval row1563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1563, Integer.Sparse.eval_collectBalanced, rawRowCheck1563]

def rawRow1564 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1111, -2), (key1155, 6), (key998, 2), (key1019, 2), (key998, 2), (key1212, -2), (key1076, -2), (key1212, -2), (key1006, -6), (key1193, 2), (key1041, 2), (key1193, 2)]

theorem rawRowCheck1564 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form3 = rawRow1564 := by decide +kernel

def row1564 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

theorem rowCheck1564 : row1564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1564 := by decide +kernel

theorem rowEval1564 (x : Key → ℝ) : Integer.Sparse.eval row1564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1564, Integer.Sparse.eval_collectBalanced, rawRowCheck1564]

def rawRow1565 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1111, -2), (key1155, 6), (key1019, 2), (key998, 2), (key998, 2), (key1212, -2), (key1212, -2), (key1076, -2), (key1006, -6), (key1193, 2), (key1193, 2), (key1041, 2)]

theorem rawRowCheck1565 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form3 = rawRow1565 := by decide +kernel

def row1565 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

theorem rowCheck1565 : row1565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1565 := by decide +kernel

theorem rowEval1565 (x : Key → ℝ) : Integer.Sparse.eval row1565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1565, Integer.Sparse.eval_collectBalanced, rawRowCheck1565]

def rawRow1566 : Integer.Sparse Key := [(key1111, -2), (key1127, -2), (key1155, -2), (key1111, 6), (key1190, 2), (key1199, 2), (key1212, 2), (key998, -2), (key1033, -2), (key1190, -2), (key1193, -6), (key1006, 2), (key1041, 2), (key1193, 2)]

theorem rawRowCheck1566 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form3 = rawRow1566 := by decide +kernel

def row1566 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

theorem rowCheck1566 : row1566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1566 := by decide +kernel

theorem rowEval1566 (x : Key → ℝ) : Integer.Sparse.eval row1566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1566, Integer.Sparse.eval_collectBalanced, rawRowCheck1566]

def rawRow1567 : Integer.Sparse Key := [(key1127, -2), (key1111, -2), (key1155, -2), (key1111, 6), (key1199, 2), (key1190, 2), (key1212, 2), (key998, -2), (key1190, -2), (key1033, -2), (key1193, -6), (key1006, 2), (key1193, 2), (key1041, 2)]

theorem rawRowCheck1567 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form3 = rawRow1567 := by decide +kernel

def row1567 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

theorem rowCheck1567 : row1567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1567 := by decide +kernel

theorem rowEval1567 (x : Key → ℝ) : Integer.Sparse.eval row1567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1567, Integer.Sparse.eval_collectBalanced, rawRowCheck1567]

def rawRow1568 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1127, -2), (key1111, 6), (key1190, 2), (key1212, 2), (key1199, 2), (key1033, -2), (key998, -2), (key1190, -2), (key1193, -6), (key1041, 2), (key1006, 2), (key1193, 2)]

theorem rawRowCheck1568 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form3 = rawRow1568 := by decide +kernel

def row1568 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

theorem rowCheck1568 : row1568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1568 := by decide +kernel

theorem rowEval1568 (x : Key → ℝ) : Integer.Sparse.eval row1568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1568, Integer.Sparse.eval_collectBalanced, rawRowCheck1568]

def rawRow1569 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1127, -2), (key1111, 6), (key1212, 2), (key1190, 2), (key1199, 2), (key1033, -2), (key1190, -2), (key998, -2), (key1193, -6), (key1041, 2), (key1193, 2), (key1006, 2)]

theorem rawRowCheck1569 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form3 = rawRow1569 := by decide +kernel

def row1569 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

theorem rowCheck1569 : row1569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1569 := by decide +kernel

theorem rowEval1569 (x : Key → ℝ) : Integer.Sparse.eval row1569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1569, Integer.Sparse.eval_collectBalanced, rawRowCheck1569]

def rawRow1570 : Integer.Sparse Key := [(key1127, -2), (key1155, -2), (key1111, -2), (key1111, 6), (key1199, 2), (key1212, 2), (key1190, 2), (key1190, -2), (key998, -2), (key1033, -2), (key1193, -6), (key1193, 2), (key1006, 2), (key1041, 2)]

theorem rawRowCheck1570 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form3 = rawRow1570 := by decide +kernel

def row1570 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

theorem rowCheck1570 : row1570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1570 := by decide +kernel

theorem rowEval1570 (x : Key → ℝ) : Integer.Sparse.eval row1570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1570, Integer.Sparse.eval_collectBalanced, rawRowCheck1570]

def rawRow1571 : Integer.Sparse Key := [(key1155, -2), (key1127, -2), (key1111, -2), (key1111, 6), (key1212, 2), (key1199, 2), (key1190, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1193, -6), (key1193, 2), (key1041, 2), (key1006, 2)]

theorem rawRowCheck1571 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form3 = rawRow1571 := by decide +kernel

def row1571 : Integer.Sparse Key := [(key998, -2), (key1006, 2), (key1033, -2), (key1041, 2), (key1111, 4), (key1127, -2), (key1155, -2), (key1193, -4), (key1199, 2), (key1212, 2)]

theorem rowCheck1571 : row1571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1571 := by decide +kernel

theorem rowEval1571 (x : Key → ℝ) : Integer.Sparse.eval row1571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1571, Integer.Sparse.eval_collectBalanced, rawRowCheck1571]

def rawRow1572 : Integer.Sparse Key := [(key1190, -2), (key1193, -2), (key1199, -2), (key1212, 6), (key998, 2), (key1006, 2), (key1019, 2), (key1076, -2), (key1155, -2), (key1212, -2), (key998, -6), (key1033, 2), (key1111, 2), (key1190, 2)]

theorem rawRowCheck1572 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form3 = rawRow1572 := by decide +kernel

def row1572 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

theorem rowCheck1572 : row1572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1572 := by decide +kernel

theorem rowEval1572 (x : Key → ℝ) : Integer.Sparse.eval row1572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1572, Integer.Sparse.eval_collectBalanced, rawRowCheck1572]

def rawRow1573 : Integer.Sparse Key := [(key1193, -2), (key1190, -2), (key1199, -2), (key1212, 6), (key1006, 2), (key998, 2), (key1019, 2), (key1076, -2), (key1212, -2), (key1155, -2), (key998, -6), (key1033, 2), (key1190, 2), (key1111, 2)]

theorem rawRowCheck1573 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form3 = rawRow1573 := by decide +kernel

def row1573 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

theorem rowCheck1573 : row1573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1573 := by decide +kernel

theorem rowEval1573 (x : Key → ℝ) : Integer.Sparse.eval row1573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1573, Integer.Sparse.eval_collectBalanced, rawRowCheck1573]

def rawRow1574 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1193, -2), (key1212, 6), (key998, 2), (key1019, 2), (key1006, 2), (key1155, -2), (key1076, -2), (key1212, -2), (key998, -6), (key1111, 2), (key1033, 2), (key1190, 2)]

theorem rawRowCheck1574 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form3 = rawRow1574 := by decide +kernel

def row1574 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

theorem rowCheck1574 : row1574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1574 := by decide +kernel

theorem rowEval1574 (x : Key → ℝ) : Integer.Sparse.eval row1574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1574, Integer.Sparse.eval_collectBalanced, rawRowCheck1574]

def rawRow1575 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1193, -2), (key1212, 6), (key1019, 2), (key998, 2), (key1006, 2), (key1155, -2), (key1212, -2), (key1076, -2), (key998, -6), (key1111, 2), (key1190, 2), (key1033, 2)]

theorem rawRowCheck1575 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form3 = rawRow1575 := by decide +kernel

def row1575 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

theorem rowCheck1575 : row1575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1575 := by decide +kernel

theorem rowEval1575 (x : Key → ℝ) : Integer.Sparse.eval row1575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1575, Integer.Sparse.eval_collectBalanced, rawRowCheck1575]

def rawRow1576 : Integer.Sparse Key := [(key1193, -2), (key1199, -2), (key1190, -2), (key1212, 6), (key1006, 2), (key1019, 2), (key998, 2), (key1212, -2), (key1076, -2), (key1155, -2), (key998, -6), (key1190, 2), (key1033, 2), (key1111, 2)]

theorem rawRowCheck1576 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form3 = rawRow1576 := by decide +kernel

def row1576 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

theorem rowCheck1576 : row1576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1576 := by decide +kernel

theorem rowEval1576 (x : Key → ℝ) : Integer.Sparse.eval row1576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1576, Integer.Sparse.eval_collectBalanced, rawRowCheck1576]

def rawRow1577 : Integer.Sparse Key := [(key1199, -2), (key1193, -2), (key1190, -2), (key1212, 6), (key1019, 2), (key1006, 2), (key998, 2), (key1212, -2), (key1155, -2), (key1076, -2), (key998, -6), (key1190, 2), (key1111, 2), (key1033, 2)]

theorem rawRowCheck1577 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form3 = rawRow1577 := by decide +kernel

def row1577 : Integer.Sparse Key := [(key998, -4), (key1006, 2), (key1019, 2), (key1033, 2), (key1076, -2), (key1111, 2), (key1155, -2), (key1193, -2), (key1199, -2), (key1212, 4)]

theorem rowCheck1577 : row1577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1577 := by decide +kernel

theorem rowEval1577 (x : Key → ℝ) : Integer.Sparse.eval row1577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1577, Integer.Sparse.eval_collectBalanced, rawRowCheck1577]

def rawRow1578 : Integer.Sparse Key := [(key1190, -2), (key1199, -2), (key1212, -2), (key1193, 6), (key1111, 2), (key1127, 2), (key1155, 2), (key1006, -2), (key1041, -2), (key1193, -2), (key1111, -6), (key998, 2), (key1033, 2), (key1190, 2)]

theorem rawRowCheck1578 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form3 = rawRow1578 := by decide +kernel

def row1578 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

theorem rowCheck1578 : row1578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1578 := by decide +kernel

theorem rowEval1578 (x : Key → ℝ) : Integer.Sparse.eval row1578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1578, Integer.Sparse.eval_collectBalanced, rawRowCheck1578]

def rawRow1579 : Integer.Sparse Key := [(key1199, -2), (key1190, -2), (key1212, -2), (key1193, 6), (key1127, 2), (key1111, 2), (key1155, 2), (key1006, -2), (key1193, -2), (key1041, -2), (key1111, -6), (key998, 2), (key1190, 2), (key1033, 2)]

theorem rawRowCheck1579 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form3 = rawRow1579 := by decide +kernel

def row1579 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

theorem rowCheck1579 : row1579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1579 := by decide +kernel

theorem rowEval1579 (x : Key → ℝ) : Integer.Sparse.eval row1579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1579, Integer.Sparse.eval_collectBalanced, rawRowCheck1579]

def rawRow1580 : Integer.Sparse Key := [(key1190, -2), (key1212, -2), (key1199, -2), (key1193, 6), (key1111, 2), (key1155, 2), (key1127, 2), (key1041, -2), (key1006, -2), (key1193, -2), (key1111, -6), (key1033, 2), (key998, 2), (key1190, 2)]

theorem rawRowCheck1580 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form3 = rawRow1580 := by decide +kernel

def row1580 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

theorem rowCheck1580 : row1580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1580 := by decide +kernel

theorem rowEval1580 (x : Key → ℝ) : Integer.Sparse.eval row1580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1580, Integer.Sparse.eval_collectBalanced, rawRowCheck1580]

def rawRow1581 : Integer.Sparse Key := [(key1212, -2), (key1190, -2), (key1199, -2), (key1193, 6), (key1155, 2), (key1111, 2), (key1127, 2), (key1041, -2), (key1193, -2), (key1006, -2), (key1111, -6), (key1033, 2), (key1190, 2), (key998, 2)]

theorem rawRowCheck1581 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form3 = rawRow1581 := by decide +kernel

def row1581 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

theorem rowCheck1581 : row1581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1581 := by decide +kernel

theorem rowEval1581 (x : Key → ℝ) : Integer.Sparse.eval row1581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1581, Integer.Sparse.eval_collectBalanced, rawRowCheck1581]

def rawRow1582 : Integer.Sparse Key := [(key1199, -2), (key1212, -2), (key1190, -2), (key1193, 6), (key1127, 2), (key1155, 2), (key1111, 2), (key1193, -2), (key1006, -2), (key1041, -2), (key1111, -6), (key1190, 2), (key998, 2), (key1033, 2)]

theorem rawRowCheck1582 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form3 = rawRow1582 := by decide +kernel

def row1582 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

theorem rowCheck1582 : row1582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1582 := by decide +kernel

theorem rowEval1582 (x : Key → ℝ) : Integer.Sparse.eval row1582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1582, Integer.Sparse.eval_collectBalanced, rawRowCheck1582]

def rawRow1583 : Integer.Sparse Key := [(key1212, -2), (key1199, -2), (key1190, -2), (key1193, 6), (key1155, 2), (key1127, 2), (key1111, 2), (key1193, -2), (key1041, -2), (key1006, -2), (key1111, -6), (key1190, 2), (key1033, 2), (key998, 2)]

theorem rawRowCheck1583 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form3 = rawRow1583 := by decide +kernel

def row1583 : Integer.Sparse Key := [(key998, 2), (key1006, -2), (key1033, 2), (key1041, -2), (key1111, -4), (key1127, 2), (key1155, 2), (key1193, 4), (key1199, -2), (key1212, -2)]

theorem rowCheck1583 : row1583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1583 := by decide +kernel

theorem rowEval1583 (x : Key → ℝ) : Integer.Sparse.eval row1583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck1583, Integer.Sparse.eval_collectBalanced, rawRowCheck1583]

def rawRow1584 : Integer.Sparse Key := [(key2631, -6), (key2615, 2), (key2639, 2), (key2639, 2), (key2705, 6), (key2670, -2), (key2725, -2), (key2725, -2), (key2808, -2), (key2859, -2), (key2859, -2), (key2785, 2), (key2869, 2), (key2869, 2)]

theorem rawRowCheck1584 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form4 = rawRow1584 := by decide +kernel

def row1584 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1584 : row1584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1584 := by decide +kernel

theorem rowEval1584 (x : Key → ℝ) : Integer.Sparse.eval row1584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1584, Integer.Sparse.eval_collectBalanced, rawRowCheck1584]

def rawRow1585 : Integer.Sparse Key := [(key2631, -6), (key2639, 2), (key2615, 2), (key2639, 2), (key2705, 6), (key2725, -2), (key2670, -2), (key2725, -2), (key2859, -2), (key2808, -2), (key2859, -2), (key2869, 2), (key2785, 2), (key2869, 2)]

theorem rawRowCheck1585 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form4 = rawRow1585 := by decide +kernel

def row1585 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1585 : row1585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1585 := by decide +kernel

theorem rowEval1585 (x : Key → ℝ) : Integer.Sparse.eval row1585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1585, Integer.Sparse.eval_collectBalanced, rawRowCheck1585]

def rawRow1586 : Integer.Sparse Key := [(key2631, -6), (key2639, 2), (key2639, 2), (key2615, 2), (key2705, 6), (key2725, -2), (key2725, -2), (key2670, -2), (key2859, -2), (key2859, -2), (key2808, -2), (key2869, 2), (key2869, 2), (key2785, 2)]

theorem rawRowCheck1586 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form4 = rawRow1586 := by decide +kernel

def row1586 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1586 : row1586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1586 := by decide +kernel

theorem rowEval1586 (x : Key → ℝ) : Integer.Sparse.eval row1586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1586, Integer.Sparse.eval_collectBalanced, rawRowCheck1586]

def rawRow1587 : Integer.Sparse Key := [(key2639, -6), (key2615, 2), (key2631, 2), (key2639, 2), (key2725, 6), (key2670, -2), (key2705, -2), (key2725, -2), (key2828, -2), (key2869, -2), (key2879, -2), (key2793, 2), (key2859, 2), (key2879, 2)]

theorem rawRowCheck1587 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form4 = rawRow1587 := by decide +kernel

def row1587 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

theorem rowCheck1587 : row1587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1587 := by decide +kernel

theorem rowEval1587 (x : Key → ℝ) : Integer.Sparse.eval row1587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1587, Integer.Sparse.eval_collectBalanced, rawRowCheck1587]

def rawRow1588 : Integer.Sparse Key := [(key2639, -6), (key2615, 2), (key2639, 2), (key2631, 2), (key2725, 6), (key2670, -2), (key2725, -2), (key2705, -2), (key2828, -2), (key2879, -2), (key2869, -2), (key2793, 2), (key2879, 2), (key2859, 2)]

theorem rawRowCheck1588 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form4 = rawRow1588 := by decide +kernel

def row1588 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

theorem rowCheck1588 : row1588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1588 := by decide +kernel

theorem rowEval1588 (x : Key → ℝ) : Integer.Sparse.eval row1588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1588, Integer.Sparse.eval_collectBalanced, rawRowCheck1588]

def rawRow1589 : Integer.Sparse Key := [(key2639, -6), (key2631, 2), (key2615, 2), (key2639, 2), (key2725, 6), (key2705, -2), (key2670, -2), (key2725, -2), (key2869, -2), (key2828, -2), (key2879, -2), (key2859, 2), (key2793, 2), (key2879, 2)]

theorem rawRowCheck1589 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form4 = rawRow1589 := by decide +kernel

def row1589 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

theorem rowCheck1589 : row1589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1589 := by decide +kernel

theorem rowEval1589 (x : Key → ℝ) : Integer.Sparse.eval row1589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1589, Integer.Sparse.eval_collectBalanced, rawRowCheck1589]

def rawRow1590 : Integer.Sparse Key := [(key2639, -6), (key2631, 2), (key2639, 2), (key2615, 2), (key2725, 6), (key2705, -2), (key2725, -2), (key2670, -2), (key2869, -2), (key2879, -2), (key2828, -2), (key2859, 2), (key2879, 2), (key2793, 2)]

theorem rawRowCheck1590 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form4 = rawRow1590 := by decide +kernel

def row1590 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

theorem rowCheck1590 : row1590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1590 := by decide +kernel

theorem rowEval1590 (x : Key → ℝ) : Integer.Sparse.eval row1590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1590, Integer.Sparse.eval_collectBalanced, rawRowCheck1590]

def rawRow1591 : Integer.Sparse Key := [(key2639, -6), (key2639, 2), (key2615, 2), (key2631, 2), (key2725, 6), (key2725, -2), (key2670, -2), (key2705, -2), (key2879, -2), (key2828, -2), (key2869, -2), (key2879, 2), (key2793, 2), (key2859, 2)]

theorem rawRowCheck1591 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form4 = rawRow1591 := by decide +kernel

def row1591 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

theorem rowCheck1591 : row1591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1591 := by decide +kernel

theorem rowEval1591 (x : Key → ℝ) : Integer.Sparse.eval row1591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1591, Integer.Sparse.eval_collectBalanced, rawRowCheck1591]

def rawRow1592 : Integer.Sparse Key := [(key2639, -6), (key2639, 2), (key2631, 2), (key2615, 2), (key2725, 6), (key2725, -2), (key2705, -2), (key2670, -2), (key2879, -2), (key2869, -2), (key2828, -2), (key2879, 2), (key2859, 2), (key2793, 2)]

theorem rawRowCheck1592 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form4 = rawRow1592 := by decide +kernel

def row1592 : Integer.Sparse Key := [(key2615, 2), (key2631, 2), (key2639, -4), (key2670, -2), (key2705, -2), (key2725, 4), (key2793, 2), (key2828, -2), (key2859, 2), (key2869, -2)]

theorem rowCheck1592 : row1592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1592 := by decide +kernel

theorem rowEval1592 (x : Key → ℝ) : Integer.Sparse.eval row1592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1592, Integer.Sparse.eval_collectBalanced, rawRowCheck1592]

def rawRow1593 : Integer.Sparse Key := [(key2705, -6), (key2808, 2), (key2859, 2), (key2859, 2), (key2631, 6), (key2785, -2), (key2869, -2), (key2869, -2), (key2615, -2), (key2639, -2), (key2639, -2), (key2670, 2), (key2725, 2), (key2725, 2)]

theorem rawRowCheck1593 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form4 = rawRow1593 := by decide +kernel

def row1593 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1593 : row1593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1593 := by decide +kernel

theorem rowEval1593 (x : Key → ℝ) : Integer.Sparse.eval row1593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1593, Integer.Sparse.eval_collectBalanced, rawRowCheck1593]

def rawRow1594 : Integer.Sparse Key := [(key2705, -6), (key2859, 2), (key2808, 2), (key2859, 2), (key2631, 6), (key2869, -2), (key2785, -2), (key2869, -2), (key2639, -2), (key2615, -2), (key2639, -2), (key2725, 2), (key2670, 2), (key2725, 2)]

theorem rawRowCheck1594 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form4 = rawRow1594 := by decide +kernel

def row1594 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1594 : row1594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1594 := by decide +kernel

theorem rowEval1594 (x : Key → ℝ) : Integer.Sparse.eval row1594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1594, Integer.Sparse.eval_collectBalanced, rawRowCheck1594]

def rawRow1595 : Integer.Sparse Key := [(key2705, -6), (key2859, 2), (key2859, 2), (key2808, 2), (key2631, 6), (key2869, -2), (key2869, -2), (key2785, -2), (key2639, -2), (key2639, -2), (key2615, -2), (key2725, 2), (key2725, 2), (key2670, 2)]

theorem rawRowCheck1595 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form4 = rawRow1595 := by decide +kernel

def row1595 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1595 : row1595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1595 := by decide +kernel

theorem rowEval1595 (x : Key → ℝ) : Integer.Sparse.eval row1595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1595, Integer.Sparse.eval_collectBalanced, rawRowCheck1595]

def rawRow1596 : Integer.Sparse Key := [(key2859, -6), (key2705, 2), (key2808, 2), (key2859, 2), (key2869, 6), (key2631, -2), (key2785, -2), (key2869, -2), (key2725, -2), (key2828, -2), (key2879, -2), (key2639, 2), (key2793, 2), (key2879, 2)]

theorem rawRowCheck1596 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form4 = rawRow1596 := by decide +kernel

def row1596 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1596 : row1596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1596 := by decide +kernel

theorem rowEval1596 (x : Key → ℝ) : Integer.Sparse.eval row1596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1596, Integer.Sparse.eval_collectBalanced, rawRowCheck1596]

def rawRow1597 : Integer.Sparse Key := [(key2859, -6), (key2705, 2), (key2859, 2), (key2808, 2), (key2869, 6), (key2631, -2), (key2869, -2), (key2785, -2), (key2725, -2), (key2879, -2), (key2828, -2), (key2639, 2), (key2879, 2), (key2793, 2)]

theorem rawRowCheck1597 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form4 = rawRow1597 := by decide +kernel

def row1597 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1597 : row1597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1597 := by decide +kernel

theorem rowEval1597 (x : Key → ℝ) : Integer.Sparse.eval row1597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1597, Integer.Sparse.eval_collectBalanced, rawRowCheck1597]

def rawRow1598 : Integer.Sparse Key := [(key2859, -6), (key2808, 2), (key2705, 2), (key2859, 2), (key2869, 6), (key2785, -2), (key2631, -2), (key2869, -2), (key2828, -2), (key2725, -2), (key2879, -2), (key2793, 2), (key2639, 2), (key2879, 2)]

theorem rawRowCheck1598 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form4 = rawRow1598 := by decide +kernel

def row1598 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1598 : row1598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1598 := by decide +kernel

theorem rowEval1598 (x : Key → ℝ) : Integer.Sparse.eval row1598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1598, Integer.Sparse.eval_collectBalanced, rawRowCheck1598]

def rawRow1599 : Integer.Sparse Key := [(key2859, -6), (key2808, 2), (key2859, 2), (key2705, 2), (key2869, 6), (key2785, -2), (key2869, -2), (key2631, -2), (key2828, -2), (key2879, -2), (key2725, -2), (key2793, 2), (key2879, 2), (key2639, 2)]

theorem rawRowCheck1599 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form4 = rawRow1599 := by decide +kernel

def row1599 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1599 : row1599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1599 := by decide +kernel

theorem rowEval1599 (x : Key → ℝ) : Integer.Sparse.eval row1599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1599, Integer.Sparse.eval_collectBalanced, rawRowCheck1599]

def rawRow1600 : Integer.Sparse Key := [(key2859, -6), (key2859, 2), (key2705, 2), (key2808, 2), (key2869, 6), (key2869, -2), (key2631, -2), (key2785, -2), (key2879, -2), (key2725, -2), (key2828, -2), (key2879, 2), (key2639, 2), (key2793, 2)]

theorem rawRowCheck1600 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form4 = rawRow1600 := by decide +kernel

def row1600 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1600 : row1600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1600 := by decide +kernel

theorem rowEval1600 (x : Key → ℝ) : Integer.Sparse.eval row1600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1600, Integer.Sparse.eval_collectBalanced, rawRowCheck1600]

def rawRow1601 : Integer.Sparse Key := [(key2859, -6), (key2859, 2), (key2808, 2), (key2705, 2), (key2869, 6), (key2869, -2), (key2785, -2), (key2631, -2), (key2879, -2), (key2828, -2), (key2725, -2), (key2879, 2), (key2793, 2), (key2639, 2)]

theorem rawRowCheck1601 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form4 = rawRow1601 := by decide +kernel

def row1601 : Integer.Sparse Key := [(key2631, -2), (key2639, 2), (key2705, 2), (key2725, -2), (key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -4), (key2869, 4)]

theorem rowCheck1601 : row1601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1601 := by decide +kernel

theorem rowEval1601 (x : Key → ℝ) : Integer.Sparse.eval row1601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1601, Integer.Sparse.eval_collectBalanced, rawRowCheck1601]

def rawRow1602 : Integer.Sparse Key := [(key2725, -6), (key2828, 2), (key2869, 2), (key2879, 2), (key2639, 6), (key2793, -2), (key2859, -2), (key2879, -2), (key2615, -2), (key2631, -2), (key2639, -2), (key2670, 2), (key2705, 2), (key2725, 2)]

theorem rawRowCheck1602 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form4 = rawRow1602 := by decide +kernel

def row1602 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

theorem rowCheck1602 : row1602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1602 := by decide +kernel

theorem rowEval1602 (x : Key → ℝ) : Integer.Sparse.eval row1602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1602, Integer.Sparse.eval_collectBalanced, rawRowCheck1602]

def rawRow1603 : Integer.Sparse Key := [(key2725, -6), (key2828, 2), (key2879, 2), (key2869, 2), (key2639, 6), (key2793, -2), (key2879, -2), (key2859, -2), (key2615, -2), (key2639, -2), (key2631, -2), (key2670, 2), (key2725, 2), (key2705, 2)]

theorem rawRowCheck1603 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form4 = rawRow1603 := by decide +kernel

def row1603 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

theorem rowCheck1603 : row1603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1603 := by decide +kernel

theorem rowEval1603 (x : Key → ℝ) : Integer.Sparse.eval row1603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1603, Integer.Sparse.eval_collectBalanced, rawRowCheck1603]

def rawRow1604 : Integer.Sparse Key := [(key2725, -6), (key2869, 2), (key2828, 2), (key2879, 2), (key2639, 6), (key2859, -2), (key2793, -2), (key2879, -2), (key2631, -2), (key2615, -2), (key2639, -2), (key2705, 2), (key2670, 2), (key2725, 2)]

theorem rawRowCheck1604 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form4 = rawRow1604 := by decide +kernel

def row1604 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

theorem rowCheck1604 : row1604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1604 := by decide +kernel

theorem rowEval1604 (x : Key → ℝ) : Integer.Sparse.eval row1604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1604, Integer.Sparse.eval_collectBalanced, rawRowCheck1604]

def rawRow1605 : Integer.Sparse Key := [(key2725, -6), (key2869, 2), (key2879, 2), (key2828, 2), (key2639, 6), (key2859, -2), (key2879, -2), (key2793, -2), (key2631, -2), (key2639, -2), (key2615, -2), (key2705, 2), (key2725, 2), (key2670, 2)]

theorem rawRowCheck1605 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form4 = rawRow1605 := by decide +kernel

def row1605 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

theorem rowCheck1605 : row1605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1605 := by decide +kernel

theorem rowEval1605 (x : Key → ℝ) : Integer.Sparse.eval row1605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1605, Integer.Sparse.eval_collectBalanced, rawRowCheck1605]

def rawRow1606 : Integer.Sparse Key := [(key2725, -6), (key2879, 2), (key2828, 2), (key2869, 2), (key2639, 6), (key2879, -2), (key2793, -2), (key2859, -2), (key2639, -2), (key2615, -2), (key2631, -2), (key2725, 2), (key2670, 2), (key2705, 2)]

theorem rawRowCheck1606 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form4 = rawRow1606 := by decide +kernel

def row1606 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

theorem rowCheck1606 : row1606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1606 := by decide +kernel

theorem rowEval1606 (x : Key → ℝ) : Integer.Sparse.eval row1606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1606, Integer.Sparse.eval_collectBalanced, rawRowCheck1606]

def rawRow1607 : Integer.Sparse Key := [(key2725, -6), (key2879, 2), (key2869, 2), (key2828, 2), (key2639, 6), (key2879, -2), (key2859, -2), (key2793, -2), (key2639, -2), (key2631, -2), (key2615, -2), (key2725, 2), (key2705, 2), (key2670, 2)]

theorem rawRowCheck1607 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form4 = rawRow1607 := by decide +kernel

def row1607 : Integer.Sparse Key := [(key2615, -2), (key2631, -2), (key2639, 4), (key2670, 2), (key2705, 2), (key2725, -4), (key2793, -2), (key2828, 2), (key2859, -2), (key2869, 2)]

theorem rowCheck1607 : row1607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1607 := by decide +kernel

theorem rowEval1607 (x : Key → ℝ) : Integer.Sparse.eval row1607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1607, Integer.Sparse.eval_collectBalanced, rawRowCheck1607]

def rawRow1608 : Integer.Sparse Key := [(key2869, -6), (key2725, 2), (key2828, 2), (key2879, 2), (key2859, 6), (key2639, -2), (key2793, -2), (key2879, -2), (key2705, -2), (key2808, -2), (key2859, -2), (key2631, 2), (key2785, 2), (key2869, 2)]

theorem rawRowCheck1608 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form4 = rawRow1608 := by decide +kernel

def row1608 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1608 : row1608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1608 := by decide +kernel

theorem rowEval1608 (x : Key → ℝ) : Integer.Sparse.eval row1608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1608, Integer.Sparse.eval_collectBalanced, rawRowCheck1608]

def rawRow1609 : Integer.Sparse Key := [(key2869, -6), (key2725, 2), (key2879, 2), (key2828, 2), (key2859, 6), (key2639, -2), (key2879, -2), (key2793, -2), (key2705, -2), (key2859, -2), (key2808, -2), (key2631, 2), (key2869, 2), (key2785, 2)]

theorem rawRowCheck1609 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form4 = rawRow1609 := by decide +kernel

def row1609 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1609 : row1609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1609 := by decide +kernel

theorem rowEval1609 (x : Key → ℝ) : Integer.Sparse.eval row1609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1609, Integer.Sparse.eval_collectBalanced, rawRowCheck1609]

def rawRow1610 : Integer.Sparse Key := [(key2869, -6), (key2828, 2), (key2725, 2), (key2879, 2), (key2859, 6), (key2793, -2), (key2639, -2), (key2879, -2), (key2808, -2), (key2705, -2), (key2859, -2), (key2785, 2), (key2631, 2), (key2869, 2)]

theorem rawRowCheck1610 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form4 = rawRow1610 := by decide +kernel

def row1610 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1610 : row1610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1610 := by decide +kernel

theorem rowEval1610 (x : Key → ℝ) : Integer.Sparse.eval row1610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1610, Integer.Sparse.eval_collectBalanced, rawRowCheck1610]

def rawRow1611 : Integer.Sparse Key := [(key2869, -6), (key2828, 2), (key2879, 2), (key2725, 2), (key2859, 6), (key2793, -2), (key2879, -2), (key2639, -2), (key2808, -2), (key2859, -2), (key2705, -2), (key2785, 2), (key2869, 2), (key2631, 2)]

theorem rawRowCheck1611 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form4 = rawRow1611 := by decide +kernel

def row1611 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1611 : row1611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1611 := by decide +kernel

theorem rowEval1611 (x : Key → ℝ) : Integer.Sparse.eval row1611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1611, Integer.Sparse.eval_collectBalanced, rawRowCheck1611]

def rawRow1612 : Integer.Sparse Key := [(key2869, -6), (key2879, 2), (key2725, 2), (key2828, 2), (key2859, 6), (key2879, -2), (key2639, -2), (key2793, -2), (key2859, -2), (key2705, -2), (key2808, -2), (key2869, 2), (key2631, 2), (key2785, 2)]

theorem rawRowCheck1612 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form4 = rawRow1612 := by decide +kernel

def row1612 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1612 : row1612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1612 := by decide +kernel

theorem rowEval1612 (x : Key → ℝ) : Integer.Sparse.eval row1612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1612, Integer.Sparse.eval_collectBalanced, rawRowCheck1612]

def rawRow1613 : Integer.Sparse Key := [(key2869, -6), (key2879, 2), (key2828, 2), (key2725, 2), (key2859, 6), (key2879, -2), (key2793, -2), (key2639, -2), (key2859, -2), (key2808, -2), (key2705, -2), (key2869, 2), (key2785, 2), (key2631, 2)]

theorem rawRowCheck1613 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form4 = rawRow1613 := by decide +kernel

def row1613 : Integer.Sparse Key := [(key2631, 2), (key2639, -2), (key2705, -2), (key2725, 2), (key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 4), (key2869, -4)]

theorem rowCheck1613 : row1613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1613 := by decide +kernel

theorem rowEval1613 (x : Key → ℝ) : Integer.Sparse.eval row1613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck1613, Integer.Sparse.eval_collectBalanced, rawRowCheck1613]

def rawRow1614 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1781, -1), (key1781, -1), (key1398, 2), (key1775, 2), (key1775, 2), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1818, 1), (key1818, 1), (key1458, -1), (key1458, -1), (key1791, -1), (key1791, -1), (key1840, -1), (key1840, -1), (key1448, -2), (key1826, -2), (key1826, -2), (key1467, 1), (key1467, 1), (key1799, 1), (key1799, 1), (key1845, 1), (key1845, 1)]

theorem rawRowCheck1614 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form5 = rawRow1614 := by decide +kernel

def row1614 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

theorem rowCheck1614 : row1614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1614 := by decide +kernel

theorem rowEval1614 (x : Key → ℝ) : Integer.Sparse.eval row1614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1614, Integer.Sparse.eval_collectBalanced, rawRowCheck1614]

def rawRow1615 : Integer.Sparse Key := [(key1772, -1), (key1781, -1), (key1391, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1775, 2), (key1398, 2), (key1775, 2), (key1813, 1), (key1818, 1), (key1424, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1791, -1), (key1840, -1), (key1458, -1), (key1840, -1), (key1458, -1), (key1791, -1), (key1826, -2), (key1448, -2), (key1826, -2), (key1799, 1), (key1845, 1), (key1467, 1), (key1845, 1), (key1467, 1), (key1799, 1)]

theorem rawRowCheck1615 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form5 = rawRow1615 := by decide +kernel

def row1615 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

theorem rowCheck1615 : row1615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1615 := by decide +kernel

theorem rowEval1615 (x : Key → ℝ) : Integer.Sparse.eval row1615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1615, Integer.Sparse.eval_collectBalanced, rawRowCheck1615]

def rawRow1616 : Integer.Sparse Key := [(key1781, -1), (key1772, -1), (key1781, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1775, 2), (key1775, 2), (key1398, 2), (key1818, 1), (key1813, 1), (key1818, 1), (key1424, 1), (key1813, 1), (key1424, 1), (key1840, -1), (key1791, -1), (key1840, -1), (key1458, -1), (key1791, -1), (key1458, -1), (key1826, -2), (key1826, -2), (key1448, -2), (key1845, 1), (key1799, 1), (key1845, 1), (key1467, 1), (key1799, 1), (key1467, 1)]

theorem rawRowCheck1616 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form5 = rawRow1616 := by decide +kernel

def row1616 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

theorem rowCheck1616 : row1616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1616 := by decide +kernel

theorem rowEval1616 (x : Key → ℝ) : Integer.Sparse.eval row1616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1616, Integer.Sparse.eval_collectBalanced, rawRowCheck1616]

def rawRow1617 : Integer.Sparse Key := [(key1391, -1), (key1398, -1), (key1546, -1), (key1775, -1), (key1560, -1), (key1781, -1), (key1391, 2), (key1546, 2), (key1772, 2), (key1455, 1), (key1458, 1), (key1655, 1), (key1840, 1), (key1660, 1), (key1842, 1), (key1424, -1), (key1455, -1), (key1573, -1), (key1788, -1), (key1655, -1), (key1813, -1), (key1467, -2), (key1668, -2), (key1845, -2), (key1448, 1), (key1467, 1), (key1597, 1), (key1799, 1), (key1668, 1), (key1826, 1)]

theorem rawRowCheck1617 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form5 = rawRow1617 := by decide +kernel

def row1617 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

theorem rowCheck1617 : row1617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1617 := by decide +kernel

theorem rowEval1617 (x : Key → ℝ) : Integer.Sparse.eval row1617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1617, Integer.Sparse.eval_collectBalanced, rawRowCheck1617]

def rawRow1618 : Integer.Sparse Key := [(key1398, -1), (key1391, -1), (key1775, -1), (key1546, -1), (key1781, -1), (key1560, -1), (key1391, 2), (key1772, 2), (key1546, 2), (key1458, 1), (key1455, 1), (key1840, 1), (key1655, 1), (key1842, 1), (key1660, 1), (key1455, -1), (key1424, -1), (key1788, -1), (key1573, -1), (key1813, -1), (key1655, -1), (key1467, -2), (key1845, -2), (key1668, -2), (key1467, 1), (key1448, 1), (key1799, 1), (key1597, 1), (key1826, 1), (key1668, 1)]

theorem rawRowCheck1618 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form5 = rawRow1618 := by decide +kernel

def row1618 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

theorem rowCheck1618 : row1618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1618 := by decide +kernel

theorem rowEval1618 (x : Key → ℝ) : Integer.Sparse.eval row1618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1618, Integer.Sparse.eval_collectBalanced, rawRowCheck1618]

def rawRow1619 : Integer.Sparse Key := [(key1546, -1), (key1560, -1), (key1391, -1), (key1781, -1), (key1398, -1), (key1775, -1), (key1546, 2), (key1391, 2), (key1772, 2), (key1655, 1), (key1660, 1), (key1455, 1), (key1842, 1), (key1458, 1), (key1840, 1), (key1573, -1), (key1655, -1), (key1424, -1), (key1813, -1), (key1455, -1), (key1788, -1), (key1668, -2), (key1467, -2), (key1845, -2), (key1597, 1), (key1668, 1), (key1448, 1), (key1826, 1), (key1467, 1), (key1799, 1)]

theorem rawRowCheck1619 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form5 = rawRow1619 := by decide +kernel

def row1619 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

theorem rowCheck1619 : row1619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1619 := by decide +kernel

theorem rowEval1619 (x : Key → ℝ) : Integer.Sparse.eval row1619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1619, Integer.Sparse.eval_collectBalanced, rawRowCheck1619]

def rawRow1620 : Integer.Sparse Key := [(key1560, -1), (key1546, -1), (key1781, -1), (key1391, -1), (key1775, -1), (key1398, -1), (key1546, 2), (key1772, 2), (key1391, 2), (key1660, 1), (key1655, 1), (key1842, 1), (key1455, 1), (key1840, 1), (key1458, 1), (key1655, -1), (key1573, -1), (key1813, -1), (key1424, -1), (key1788, -1), (key1455, -1), (key1668, -2), (key1845, -2), (key1467, -2), (key1668, 1), (key1597, 1), (key1826, 1), (key1448, 1), (key1799, 1), (key1467, 1)]

theorem rawRowCheck1620 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form5 = rawRow1620 := by decide +kernel

def row1620 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

theorem rowCheck1620 : row1620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1620 := by decide +kernel

theorem rowEval1620 (x : Key → ℝ) : Integer.Sparse.eval row1620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1620, Integer.Sparse.eval_collectBalanced, rawRowCheck1620]

def rawRow1621 : Integer.Sparse Key := [(key1775, -1), (key1781, -1), (key1398, -1), (key1560, -1), (key1391, -1), (key1546, -1), (key1772, 2), (key1391, 2), (key1546, 2), (key1840, 1), (key1842, 1), (key1458, 1), (key1660, 1), (key1455, 1), (key1655, 1), (key1788, -1), (key1813, -1), (key1455, -1), (key1655, -1), (key1424, -1), (key1573, -1), (key1845, -2), (key1467, -2), (key1668, -2), (key1799, 1), (key1826, 1), (key1467, 1), (key1668, 1), (key1448, 1), (key1597, 1)]

theorem rawRowCheck1621 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form5 = rawRow1621 := by decide +kernel

def row1621 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

theorem rowCheck1621 : row1621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1621 := by decide +kernel

theorem rowEval1621 (x : Key → ℝ) : Integer.Sparse.eval row1621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1621, Integer.Sparse.eval_collectBalanced, rawRowCheck1621]

def rawRow1622 : Integer.Sparse Key := [(key1781, -1), (key1775, -1), (key1560, -1), (key1398, -1), (key1546, -1), (key1391, -1), (key1772, 2), (key1546, 2), (key1391, 2), (key1842, 1), (key1840, 1), (key1660, 1), (key1458, 1), (key1655, 1), (key1455, 1), (key1813, -1), (key1788, -1), (key1655, -1), (key1455, -1), (key1573, -1), (key1424, -1), (key1845, -2), (key1668, -2), (key1467, -2), (key1826, 1), (key1799, 1), (key1668, 1), (key1467, 1), (key1597, 1), (key1448, 1)]

theorem rawRowCheck1622 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form5 = rawRow1622 := by decide +kernel

def row1622 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, 1), (key1660, 1), (key1668, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1799, 1), (key1813, -1), (key1826, 1), (key1840, 1), (key1842, 1), (key1845, -2)]

theorem rowCheck1622 : row1622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1622 := by decide +kernel

theorem rowEval1622 (x : Key → ℝ) : Integer.Sparse.eval row1622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1622, Integer.Sparse.eval_collectBalanced, rawRowCheck1622]

def rawRow1623 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1818, -1), (key1818, -1), (key1448, 2), (key1826, 2), (key1826, 2), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1781, 1), (key1781, 1), (key1467, -1), (key1467, -1), (key1799, -1), (key1799, -1), (key1845, -1), (key1845, -1), (key1398, -2), (key1775, -2), (key1775, -2), (key1458, 1), (key1458, 1), (key1791, 1), (key1791, 1), (key1840, 1), (key1840, 1)]

theorem rawRowCheck1623 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form5 = rawRow1623 := by decide +kernel

def row1623 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

theorem rowCheck1623 : row1623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1623 := by decide +kernel

theorem rowEval1623 (x : Key → ℝ) : Integer.Sparse.eval row1623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1623, Integer.Sparse.eval_collectBalanced, rawRowCheck1623]

def rawRow1624 : Integer.Sparse Key := [(key1813, -1), (key1818, -1), (key1424, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1826, 2), (key1448, 2), (key1826, 2), (key1772, 1), (key1781, 1), (key1391, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1799, -1), (key1845, -1), (key1467, -1), (key1845, -1), (key1467, -1), (key1799, -1), (key1775, -2), (key1398, -2), (key1775, -2), (key1791, 1), (key1840, 1), (key1458, 1), (key1840, 1), (key1458, 1), (key1791, 1)]

theorem rawRowCheck1624 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form5 = rawRow1624 := by decide +kernel

def row1624 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

theorem rowCheck1624 : row1624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1624 := by decide +kernel

theorem rowEval1624 (x : Key → ℝ) : Integer.Sparse.eval row1624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1624, Integer.Sparse.eval_collectBalanced, rawRowCheck1624]

def rawRow1625 : Integer.Sparse Key := [(key1818, -1), (key1813, -1), (key1818, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1826, 2), (key1826, 2), (key1448, 2), (key1781, 1), (key1772, 1), (key1781, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1845, -1), (key1799, -1), (key1845, -1), (key1467, -1), (key1799, -1), (key1467, -1), (key1775, -2), (key1775, -2), (key1398, -2), (key1840, 1), (key1791, 1), (key1840, 1), (key1458, 1), (key1791, 1), (key1458, 1)]

theorem rawRowCheck1625 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form5 = rawRow1625 := by decide +kernel

def row1625 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

theorem rowCheck1625 : row1625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1625 := by decide +kernel

theorem rowEval1625 (x : Key → ℝ) : Integer.Sparse.eval row1625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1625, Integer.Sparse.eval_collectBalanced, rawRowCheck1625]

def rawRow1626 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1424, -1), (key1818, -1), (key1448, -1), (key1826, -1), (key1316, 2), (key1424, 2), (key1813, 2), (key1337, 1), (key1346, 1), (key1455, 1), (key1842, 1), (key1467, 1), (key1845, 1), (key1296, -1), (key1337, -1), (key1391, -1), (key1772, -1), (key1455, -1), (key1788, -1), (key1340, -2), (key1458, -2), (key1840, -2), (key1303, 1), (key1340, 1), (key1398, 1), (key1775, 1), (key1458, 1), (key1791, 1)]

theorem rawRowCheck1626 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form5 = rawRow1626 := by decide +kernel

def row1626 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

theorem rowCheck1626 : row1626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1626 := by decide +kernel

theorem rowEval1626 (x : Key → ℝ) : Integer.Sparse.eval row1626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1626, Integer.Sparse.eval_collectBalanced, rawRowCheck1626]

def rawRow1627 : Integer.Sparse Key := [(key1330, -1), (key1316, -1), (key1818, -1), (key1424, -1), (key1826, -1), (key1448, -1), (key1316, 2), (key1813, 2), (key1424, 2), (key1346, 1), (key1337, 1), (key1842, 1), (key1455, 1), (key1845, 1), (key1467, 1), (key1337, -1), (key1296, -1), (key1772, -1), (key1391, -1), (key1788, -1), (key1455, -1), (key1340, -2), (key1840, -2), (key1458, -2), (key1340, 1), (key1303, 1), (key1775, 1), (key1398, 1), (key1791, 1), (key1458, 1)]

theorem rawRowCheck1627 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form5 = rawRow1627 := by decide +kernel

def row1627 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

theorem rowCheck1627 : row1627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1627 := by decide +kernel

theorem rowEval1627 (x : Key → ℝ) : Integer.Sparse.eval row1627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1627, Integer.Sparse.eval_collectBalanced, rawRowCheck1627]

def rawRow1628 : Integer.Sparse Key := [(key1424, -1), (key1448, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1424, 2), (key1316, 2), (key1813, 2), (key1455, 1), (key1467, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1391, -1), (key1455, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1458, -2), (key1340, -2), (key1840, -2), (key1398, 1), (key1458, 1), (key1303, 1), (key1791, 1), (key1340, 1), (key1775, 1)]

theorem rawRowCheck1628 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form5 = rawRow1628 := by decide +kernel

def row1628 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

theorem rowCheck1628 : row1628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1628 := by decide +kernel

theorem rowEval1628 (x : Key → ℝ) : Integer.Sparse.eval row1628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1628, Integer.Sparse.eval_collectBalanced, rawRowCheck1628]

def rawRow1629 : Integer.Sparse Key := [(key1448, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1818, -1), (key1330, -1), (key1424, 2), (key1813, 2), (key1316, 2), (key1467, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1842, 1), (key1346, 1), (key1455, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1772, -1), (key1337, -1), (key1458, -2), (key1840, -2), (key1340, -2), (key1458, 1), (key1398, 1), (key1791, 1), (key1303, 1), (key1775, 1), (key1340, 1)]

theorem rawRowCheck1629 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form5 = rawRow1629 := by decide +kernel

def row1629 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

theorem rowCheck1629 : row1629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1629 := by decide +kernel

theorem rowEval1629 (x : Key → ℝ) : Integer.Sparse.eval row1629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1629, Integer.Sparse.eval_collectBalanced, rawRowCheck1629]

def rawRow1630 : Integer.Sparse Key := [(key1818, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1316, -1), (key1424, -1), (key1813, 2), (key1316, 2), (key1424, 2), (key1842, 1), (key1845, 1), (key1346, 1), (key1467, 1), (key1337, 1), (key1455, 1), (key1772, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1296, -1), (key1391, -1), (key1840, -2), (key1340, -2), (key1458, -2), (key1775, 1), (key1791, 1), (key1340, 1), (key1458, 1), (key1303, 1), (key1398, 1)]

theorem rawRowCheck1630 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form5 = rawRow1630 := by decide +kernel

def row1630 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

theorem rowCheck1630 : row1630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1630 := by decide +kernel

theorem rowEval1630 (x : Key → ℝ) : Integer.Sparse.eval row1630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1630, Integer.Sparse.eval_collectBalanced, rawRowCheck1630]

def rawRow1631 : Integer.Sparse Key := [(key1826, -1), (key1818, -1), (key1448, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1813, 2), (key1424, 2), (key1316, 2), (key1845, 1), (key1842, 1), (key1467, 1), (key1346, 1), (key1455, 1), (key1337, 1), (key1788, -1), (key1772, -1), (key1455, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1840, -2), (key1458, -2), (key1340, -2), (key1791, 1), (key1775, 1), (key1458, 1), (key1340, 1), (key1398, 1), (key1303, 1)]

theorem rawRowCheck1631 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form5 = rawRow1631 := by decide +kernel

def row1631 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1772, -1), (key1775, 1), (key1788, -1), (key1791, 1), (key1813, 2), (key1818, -1), (key1826, -1), (key1840, -2), (key1842, 1), (key1845, 1)]

theorem rowCheck1631 : row1631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1631 := by decide +kernel

theorem rowEval1631 (x : Key → ℝ) : Integer.Sparse.eval row1631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1631, Integer.Sparse.eval_collectBalanced, rawRowCheck1631]

def rawRow1632 : Integer.Sparse Key := [(key1455, -1), (key1458, -1), (key1655, -1), (key1840, -1), (key1660, -1), (key1842, -1), (key1467, 2), (key1668, 2), (key1845, 2), (key1391, 1), (key1398, 1), (key1546, 1), (key1775, 1), (key1560, 1), (key1781, 1), (key1448, -1), (key1467, -1), (key1597, -1), (key1799, -1), (key1668, -1), (key1826, -1), (key1391, -2), (key1546, -2), (key1772, -2), (key1424, 1), (key1455, 1), (key1573, 1), (key1788, 1), (key1655, 1), (key1813, 1)]

theorem rawRowCheck1632 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form5 = rawRow1632 := by decide +kernel

def row1632 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

theorem rowCheck1632 : row1632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1632 := by decide +kernel

theorem rowEval1632 (x : Key → ℝ) : Integer.Sparse.eval row1632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1632, Integer.Sparse.eval_collectBalanced, rawRowCheck1632]

def rawRow1633 : Integer.Sparse Key := [(key1458, -1), (key1455, -1), (key1840, -1), (key1655, -1), (key1842, -1), (key1660, -1), (key1467, 2), (key1845, 2), (key1668, 2), (key1398, 1), (key1391, 1), (key1775, 1), (key1546, 1), (key1781, 1), (key1560, 1), (key1467, -1), (key1448, -1), (key1799, -1), (key1597, -1), (key1826, -1), (key1668, -1), (key1391, -2), (key1772, -2), (key1546, -2), (key1455, 1), (key1424, 1), (key1788, 1), (key1573, 1), (key1813, 1), (key1655, 1)]

theorem rawRowCheck1633 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form5 = rawRow1633 := by decide +kernel

def row1633 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

theorem rowCheck1633 : row1633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1633 := by decide +kernel

theorem rowEval1633 (x : Key → ℝ) : Integer.Sparse.eval row1633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1633, Integer.Sparse.eval_collectBalanced, rawRowCheck1633]

def rawRow1634 : Integer.Sparse Key := [(key1655, -1), (key1660, -1), (key1455, -1), (key1842, -1), (key1458, -1), (key1840, -1), (key1668, 2), (key1467, 2), (key1845, 2), (key1546, 1), (key1560, 1), (key1391, 1), (key1781, 1), (key1398, 1), (key1775, 1), (key1597, -1), (key1668, -1), (key1448, -1), (key1826, -1), (key1467, -1), (key1799, -1), (key1546, -2), (key1391, -2), (key1772, -2), (key1573, 1), (key1655, 1), (key1424, 1), (key1813, 1), (key1455, 1), (key1788, 1)]

theorem rawRowCheck1634 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form5 = rawRow1634 := by decide +kernel

def row1634 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

theorem rowCheck1634 : row1634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1634 := by decide +kernel

theorem rowEval1634 (x : Key → ℝ) : Integer.Sparse.eval row1634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1634, Integer.Sparse.eval_collectBalanced, rawRowCheck1634]

def rawRow1635 : Integer.Sparse Key := [(key1660, -1), (key1655, -1), (key1842, -1), (key1455, -1), (key1840, -1), (key1458, -1), (key1668, 2), (key1845, 2), (key1467, 2), (key1560, 1), (key1546, 1), (key1781, 1), (key1391, 1), (key1775, 1), (key1398, 1), (key1668, -1), (key1597, -1), (key1826, -1), (key1448, -1), (key1799, -1), (key1467, -1), (key1546, -2), (key1772, -2), (key1391, -2), (key1655, 1), (key1573, 1), (key1813, 1), (key1424, 1), (key1788, 1), (key1455, 1)]

theorem rawRowCheck1635 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form5 = rawRow1635 := by decide +kernel

def row1635 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

theorem rowCheck1635 : row1635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1635 := by decide +kernel

theorem rowEval1635 (x : Key → ℝ) : Integer.Sparse.eval row1635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1635, Integer.Sparse.eval_collectBalanced, rawRowCheck1635]

def rawRow1636 : Integer.Sparse Key := [(key1840, -1), (key1842, -1), (key1458, -1), (key1660, -1), (key1455, -1), (key1655, -1), (key1845, 2), (key1467, 2), (key1668, 2), (key1775, 1), (key1781, 1), (key1398, 1), (key1560, 1), (key1391, 1), (key1546, 1), (key1799, -1), (key1826, -1), (key1467, -1), (key1668, -1), (key1448, -1), (key1597, -1), (key1772, -2), (key1391, -2), (key1546, -2), (key1788, 1), (key1813, 1), (key1455, 1), (key1655, 1), (key1424, 1), (key1573, 1)]

theorem rawRowCheck1636 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form5 = rawRow1636 := by decide +kernel

def row1636 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

theorem rowCheck1636 : row1636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1636 := by decide +kernel

theorem rowEval1636 (x : Key → ℝ) : Integer.Sparse.eval row1636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1636, Integer.Sparse.eval_collectBalanced, rawRowCheck1636]

def rawRow1637 : Integer.Sparse Key := [(key1842, -1), (key1840, -1), (key1660, -1), (key1458, -1), (key1655, -1), (key1455, -1), (key1845, 2), (key1668, 2), (key1467, 2), (key1781, 1), (key1775, 1), (key1560, 1), (key1398, 1), (key1546, 1), (key1391, 1), (key1826, -1), (key1799, -1), (key1668, -1), (key1467, -1), (key1597, -1), (key1448, -1), (key1772, -2), (key1546, -2), (key1391, -2), (key1813, 1), (key1788, 1), (key1655, 1), (key1455, 1), (key1573, 1), (key1424, 1)]

theorem rawRowCheck1637 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form5 = rawRow1637 := by decide +kernel

def row1637 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, -1), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, -1), (key1660, -1), (key1668, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1788, 1), (key1799, -1), (key1813, 1), (key1826, -1), (key1840, -1), (key1842, -1), (key1845, 2)]

theorem rowCheck1637 : row1637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1637 := by decide +kernel

theorem rowEval1637 (x : Key → ℝ) : Integer.Sparse.eval row1637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1637, Integer.Sparse.eval_collectBalanced, rawRowCheck1637]

def rawRow1638 : Integer.Sparse Key := [(key1337, -1), (key1346, -1), (key1455, -1), (key1842, -1), (key1467, -1), (key1845, -1), (key1340, 2), (key1458, 2), (key1840, 2), (key1316, 1), (key1330, 1), (key1424, 1), (key1818, 1), (key1448, 1), (key1826, 1), (key1303, -1), (key1340, -1), (key1398, -1), (key1775, -1), (key1458, -1), (key1791, -1), (key1316, -2), (key1424, -2), (key1813, -2), (key1296, 1), (key1337, 1), (key1391, 1), (key1772, 1), (key1455, 1), (key1788, 1)]

theorem rawRowCheck1638 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form5 = rawRow1638 := by decide +kernel

def row1638 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

theorem rowCheck1638 : row1638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1638 := by decide +kernel

theorem rowEval1638 (x : Key → ℝ) : Integer.Sparse.eval row1638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1638, Integer.Sparse.eval_collectBalanced, rawRowCheck1638]

def rawRow1639 : Integer.Sparse Key := [(key1346, -1), (key1337, -1), (key1842, -1), (key1455, -1), (key1845, -1), (key1467, -1), (key1340, 2), (key1840, 2), (key1458, 2), (key1330, 1), (key1316, 1), (key1818, 1), (key1424, 1), (key1826, 1), (key1448, 1), (key1340, -1), (key1303, -1), (key1775, -1), (key1398, -1), (key1791, -1), (key1458, -1), (key1316, -2), (key1813, -2), (key1424, -2), (key1337, 1), (key1296, 1), (key1772, 1), (key1391, 1), (key1788, 1), (key1455, 1)]

theorem rawRowCheck1639 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form5 = rawRow1639 := by decide +kernel

def row1639 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

theorem rowCheck1639 : row1639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1639 := by decide +kernel

theorem rowEval1639 (x : Key → ℝ) : Integer.Sparse.eval row1639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1639, Integer.Sparse.eval_collectBalanced, rawRowCheck1639]

def rawRow1640 : Integer.Sparse Key := [(key1455, -1), (key1467, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1458, 2), (key1340, 2), (key1840, 2), (key1424, 1), (key1448, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1818, 1), (key1398, -1), (key1458, -1), (key1303, -1), (key1791, -1), (key1340, -1), (key1775, -1), (key1424, -2), (key1316, -2), (key1813, -2), (key1391, 1), (key1455, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1772, 1)]

theorem rawRowCheck1640 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form5 = rawRow1640 := by decide +kernel

def row1640 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

theorem rowCheck1640 : row1640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1640 := by decide +kernel

theorem rowEval1640 (x : Key → ℝ) : Integer.Sparse.eval row1640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1640, Integer.Sparse.eval_collectBalanced, rawRowCheck1640]

def rawRow1641 : Integer.Sparse Key := [(key1467, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1842, -1), (key1346, -1), (key1458, 2), (key1840, 2), (key1340, 2), (key1448, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1818, 1), (key1330, 1), (key1458, -1), (key1398, -1), (key1791, -1), (key1303, -1), (key1775, -1), (key1340, -1), (key1424, -2), (key1813, -2), (key1316, -2), (key1455, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1772, 1), (key1337, 1)]

theorem rawRowCheck1641 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form5 = rawRow1641 := by decide +kernel

def row1641 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

theorem rowCheck1641 : row1641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1641 := by decide +kernel

theorem rowEval1641 (x : Key → ℝ) : Integer.Sparse.eval row1641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1641, Integer.Sparse.eval_collectBalanced, rawRowCheck1641]

def rawRow1642 : Integer.Sparse Key := [(key1842, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1337, -1), (key1455, -1), (key1840, 2), (key1340, 2), (key1458, 2), (key1818, 1), (key1826, 1), (key1330, 1), (key1448, 1), (key1316, 1), (key1424, 1), (key1775, -1), (key1791, -1), (key1340, -1), (key1458, -1), (key1303, -1), (key1398, -1), (key1813, -2), (key1316, -2), (key1424, -2), (key1772, 1), (key1788, 1), (key1337, 1), (key1455, 1), (key1296, 1), (key1391, 1)]

theorem rawRowCheck1642 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form5 = rawRow1642 := by decide +kernel

def row1642 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

theorem rowCheck1642 : row1642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1642 := by decide +kernel

theorem rowEval1642 (x : Key → ℝ) : Integer.Sparse.eval row1642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1642, Integer.Sparse.eval_collectBalanced, rawRowCheck1642]

def rawRow1643 : Integer.Sparse Key := [(key1845, -1), (key1842, -1), (key1467, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1840, 2), (key1458, 2), (key1340, 2), (key1826, 1), (key1818, 1), (key1448, 1), (key1330, 1), (key1424, 1), (key1316, 1), (key1791, -1), (key1775, -1), (key1458, -1), (key1340, -1), (key1398, -1), (key1303, -1), (key1813, -2), (key1424, -2), (key1316, -2), (key1788, 1), (key1772, 1), (key1455, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

theorem rawRowCheck1643 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form5 = rawRow1643 := by decide +kernel

def row1643 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1424, -1), (key1448, 1), (key1458, 1), (key1467, -1), (key1772, 1), (key1775, -1), (key1788, 1), (key1791, -1), (key1813, -2), (key1818, 1), (key1826, 1), (key1840, 2), (key1842, -1), (key1845, -1)]

theorem rowCheck1643 : row1643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1643 := by decide +kernel

theorem rowEval1643 (x : Key → ℝ) : Integer.Sparse.eval row1643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1643, Integer.Sparse.eval_collectBalanced, rawRowCheck1643]

def rawRow1644 : Integer.Sparse Key := [(key2693, -2), (key2693, -2), (key2759, -2), (key2695, 2), (key2695, 2), (key2733, 2), (key2822, 2), (key2822, 2), (key2924, 2), (key2836, -6), (key3015, -2), (key3015, -2), (key3027, -2), (key3018, 6)]

theorem rawRowCheck1644 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form6 = rawRow1644 := by decide +kernel

def row1644 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

theorem rowCheck1644 : row1644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1644 := by decide +kernel

theorem rowEval1644 (x : Key → ℝ) : Integer.Sparse.eval row1644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1644, Integer.Sparse.eval_collectBalanced, rawRowCheck1644]

def rawRow1645 : Integer.Sparse Key := [(key2693, -2), (key2759, -2), (key2693, -2), (key2695, 2), (key2733, 2), (key2695, 2), (key2822, 2), (key2924, 2), (key2822, 2), (key2836, -6), (key3015, -2), (key3027, -2), (key3015, -2), (key3018, 6)]

theorem rawRowCheck1645 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form6 = rawRow1645 := by decide +kernel

def row1645 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

theorem rowCheck1645 : row1645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1645 := by decide +kernel

theorem rowEval1645 (x : Key → ℝ) : Integer.Sparse.eval row1645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1645, Integer.Sparse.eval_collectBalanced, rawRowCheck1645]

def rawRow1646 : Integer.Sparse Key := [(key2759, -2), (key2693, -2), (key2693, -2), (key2733, 2), (key2695, 2), (key2695, 2), (key2924, 2), (key2822, 2), (key2822, 2), (key2836, -6), (key3027, -2), (key3015, -2), (key3015, -2), (key3018, 6)]

theorem rawRowCheck1646 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form6 = rawRow1646 := by decide +kernel

def row1646 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

theorem rowCheck1646 : row1646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1646 := by decide +kernel

theorem rowEval1646 (x : Key → ℝ) : Integer.Sparse.eval row1646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1646, Integer.Sparse.eval_collectBalanced, rawRowCheck1646]

def rawRow1647 : Integer.Sparse Key := [(key2686, -2), (key2695, -2), (key2756, -2), (key2686, 2), (key2693, 2), (key2719, 2), (key2822, 2), (key2836, 2), (key2924, 2), (key2822, -6), (key3015, -2), (key3018, -2), (key3027, -2), (key3015, 6)]

theorem rawRowCheck1647 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form6 = rawRow1647 := by decide +kernel

def row1647 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

theorem rowCheck1647 : row1647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1647 := by decide +kernel

theorem rowEval1647 (x : Key → ℝ) : Integer.Sparse.eval row1647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1647, Integer.Sparse.eval_collectBalanced, rawRowCheck1647]

def rawRow1648 : Integer.Sparse Key := [(key2695, -2), (key2686, -2), (key2756, -2), (key2693, 2), (key2686, 2), (key2719, 2), (key2836, 2), (key2822, 2), (key2924, 2), (key2822, -6), (key3018, -2), (key3015, -2), (key3027, -2), (key3015, 6)]

theorem rawRowCheck1648 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form6 = rawRow1648 := by decide +kernel

def row1648 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

theorem rowCheck1648 : row1648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1648 := by decide +kernel

theorem rowEval1648 (x : Key → ℝ) : Integer.Sparse.eval row1648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1648, Integer.Sparse.eval_collectBalanced, rawRowCheck1648]

def rawRow1649 : Integer.Sparse Key := [(key2686, -2), (key2756, -2), (key2695, -2), (key2686, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2924, 2), (key2836, 2), (key2822, -6), (key3015, -2), (key3027, -2), (key3018, -2), (key3015, 6)]

theorem rawRowCheck1649 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form6 = rawRow1649 := by decide +kernel

def row1649 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

theorem rowCheck1649 : row1649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1649 := by decide +kernel

theorem rowEval1649 (x : Key → ℝ) : Integer.Sparse.eval row1649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1649, Integer.Sparse.eval_collectBalanced, rawRowCheck1649]

def rawRow1650 : Integer.Sparse Key := [(key2756, -2), (key2686, -2), (key2695, -2), (key2719, 2), (key2686, 2), (key2693, 2), (key2924, 2), (key2822, 2), (key2836, 2), (key2822, -6), (key3027, -2), (key3015, -2), (key3018, -2), (key3015, 6)]

theorem rawRowCheck1650 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form6 = rawRow1650 := by decide +kernel

def row1650 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

theorem rowCheck1650 : row1650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1650 := by decide +kernel

theorem rowEval1650 (x : Key → ℝ) : Integer.Sparse.eval row1650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1650, Integer.Sparse.eval_collectBalanced, rawRowCheck1650]

def rawRow1651 : Integer.Sparse Key := [(key2695, -2), (key2756, -2), (key2686, -2), (key2693, 2), (key2719, 2), (key2686, 2), (key2836, 2), (key2924, 2), (key2822, 2), (key2822, -6), (key3018, -2), (key3027, -2), (key3015, -2), (key3015, 6)]

theorem rawRowCheck1651 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form6 = rawRow1651 := by decide +kernel

def row1651 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

theorem rowCheck1651 : row1651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1651 := by decide +kernel

theorem rowEval1651 (x : Key → ℝ) : Integer.Sparse.eval row1651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1651, Integer.Sparse.eval_collectBalanced, rawRowCheck1651]

def rawRow1652 : Integer.Sparse Key := [(key2756, -2), (key2695, -2), (key2686, -2), (key2719, 2), (key2693, 2), (key2686, 2), (key2924, 2), (key2836, 2), (key2822, 2), (key2822, -6), (key3027, -2), (key3018, -2), (key3015, -2), (key3015, 6)]

theorem rawRowCheck1652 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form6 = rawRow1652 := by decide +kernel

def row1652 : Integer.Sparse Key := [(key2693, 2), (key2695, -2), (key2719, 2), (key2756, -2), (key2822, -4), (key2836, 2), (key2924, 2), (key3015, 4), (key3018, -2), (key3027, -2)]

theorem rowCheck1652 : row1652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1652 := by decide +kernel

theorem rowEval1652 (x : Key → ℝ) : Integer.Sparse.eval row1652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1652, Integer.Sparse.eval_collectBalanced, rawRowCheck1652]

def rawRow1653 : Integer.Sparse Key := [(key3107, -2), (key3107, -2), (key3146, -2), (key3112, 2), (key3112, 2), (key3147, 2), (key2693, 2), (key2693, 2), (key2759, 2), (key3018, -6), (key2695, -2), (key2695, -2), (key2733, -2), (key2836, 6)]

theorem rawRowCheck1653 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form6 = rawRow1653 := by decide +kernel

def row1653 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

theorem rowCheck1653 : row1653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1653 := by decide +kernel

theorem rowEval1653 (x : Key → ℝ) : Integer.Sparse.eval row1653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1653, Integer.Sparse.eval_collectBalanced, rawRowCheck1653]

def rawRow1654 : Integer.Sparse Key := [(key3107, -2), (key3146, -2), (key3107, -2), (key3112, 2), (key3147, 2), (key3112, 2), (key2693, 2), (key2759, 2), (key2693, 2), (key3018, -6), (key2695, -2), (key2733, -2), (key2695, -2), (key2836, 6)]

theorem rawRowCheck1654 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form6 = rawRow1654 := by decide +kernel

def row1654 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

theorem rowCheck1654 : row1654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1654 := by decide +kernel

theorem rowEval1654 (x : Key → ℝ) : Integer.Sparse.eval row1654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1654, Integer.Sparse.eval_collectBalanced, rawRowCheck1654]

def rawRow1655 : Integer.Sparse Key := [(key3146, -2), (key3107, -2), (key3107, -2), (key3147, 2), (key3112, 2), (key3112, 2), (key2759, 2), (key2693, 2), (key2693, 2), (key3018, -6), (key2733, -2), (key2695, -2), (key2695, -2), (key2836, 6)]

theorem rawRowCheck1655 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form6 = rawRow1655 := by decide +kernel

def row1655 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

theorem rowCheck1655 : row1655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1655 := by decide +kernel

theorem rowEval1655 (x : Key → ℝ) : Integer.Sparse.eval row1655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1655, Integer.Sparse.eval_collectBalanced, rawRowCheck1655]

def rawRow1656 : Integer.Sparse Key := [(key3051, -2), (key3074, -2), (key3112, -2), (key3051, 2), (key3070, 2), (key3107, 2), (key3055, 2), (key3078, 2), (key3117, 2), (key2693, -6), (key2695, -2), (key2733, -2), (key2836, -2), (key2695, 6)]

theorem rawRowCheck1656 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form6 = rawRow1656 := by decide +kernel

def row1656 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

theorem rowCheck1656 : row1656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1656 := by decide +kernel

theorem rowEval1656 (x : Key → ℝ) : Integer.Sparse.eval row1656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1656, Integer.Sparse.eval_collectBalanced, rawRowCheck1656]

def rawRow1657 : Integer.Sparse Key := [(key3074, -2), (key3051, -2), (key3112, -2), (key3070, 2), (key3051, 2), (key3107, 2), (key3078, 2), (key3055, 2), (key3117, 2), (key2693, -6), (key2733, -2), (key2695, -2), (key2836, -2), (key2695, 6)]

theorem rawRowCheck1657 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form6 = rawRow1657 := by decide +kernel

def row1657 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

theorem rowCheck1657 : row1657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1657 := by decide +kernel

theorem rowEval1657 (x : Key → ℝ) : Integer.Sparse.eval row1657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1657, Integer.Sparse.eval_collectBalanced, rawRowCheck1657]

def rawRow1658 : Integer.Sparse Key := [(key3051, -2), (key3112, -2), (key3074, -2), (key3051, 2), (key3107, 2), (key3070, 2), (key3055, 2), (key3117, 2), (key3078, 2), (key2693, -6), (key2695, -2), (key2836, -2), (key2733, -2), (key2695, 6)]

theorem rawRowCheck1658 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form6 = rawRow1658 := by decide +kernel

def row1658 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

theorem rowCheck1658 : row1658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1658 := by decide +kernel

theorem rowEval1658 (x : Key → ℝ) : Integer.Sparse.eval row1658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1658, Integer.Sparse.eval_collectBalanced, rawRowCheck1658]

def rawRow1659 : Integer.Sparse Key := [(key3112, -2), (key3051, -2), (key3074, -2), (key3107, 2), (key3051, 2), (key3070, 2), (key3117, 2), (key3055, 2), (key3078, 2), (key2693, -6), (key2836, -2), (key2695, -2), (key2733, -2), (key2695, 6)]

theorem rawRowCheck1659 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form6 = rawRow1659 := by decide +kernel

def row1659 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

theorem rowCheck1659 : row1659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1659 := by decide +kernel

theorem rowEval1659 (x : Key → ℝ) : Integer.Sparse.eval row1659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1659, Integer.Sparse.eval_collectBalanced, rawRowCheck1659]

def rawRow1660 : Integer.Sparse Key := [(key3074, -2), (key3112, -2), (key3051, -2), (key3070, 2), (key3107, 2), (key3051, 2), (key3078, 2), (key3117, 2), (key3055, 2), (key2693, -6), (key2733, -2), (key2836, -2), (key2695, -2), (key2695, 6)]

theorem rawRowCheck1660 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form6 = rawRow1660 := by decide +kernel

def row1660 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

theorem rowCheck1660 : row1660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1660 := by decide +kernel

theorem rowEval1660 (x : Key → ℝ) : Integer.Sparse.eval row1660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1660, Integer.Sparse.eval_collectBalanced, rawRowCheck1660]

def rawRow1661 : Integer.Sparse Key := [(key3112, -2), (key3074, -2), (key3051, -2), (key3107, 2), (key3070, 2), (key3051, 2), (key3117, 2), (key3078, 2), (key3055, 2), (key2693, -6), (key2836, -2), (key2733, -2), (key2695, -2), (key2695, 6)]

theorem rawRowCheck1661 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form6 = rawRow1661 := by decide +kernel

def row1661 : Integer.Sparse Key := [(key2693, -6), (key2695, 4), (key2733, -2), (key2836, -2), (key3055, 2), (key3070, 2), (key3074, -2), (key3078, 2), (key3107, 2), (key3112, -2), (key3117, 2)]

theorem rowCheck1661 : row1661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1661 := by decide +kernel

theorem rowEval1661 (x : Key → ℝ) : Integer.Sparse.eval row1661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1661, Integer.Sparse.eval_collectBalanced, rawRowCheck1661]

def rawRow1662 : Integer.Sparse Key := [(key3107, -2), (key3116, -2), (key3146, -2), (key3112, 2), (key3117, 2), (key3147, 2), (key3051, 2), (key3057, 2), (key3074, 2), (key3112, -6), (key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6)]

theorem rawRowCheck1662 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form6 = rawRow1662 := by decide +kernel

def row1662 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

theorem rowCheck1662 : row1662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1662 := by decide +kernel

theorem rowEval1662 (x : Key → ℝ) : Integer.Sparse.eval row1662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1662, Integer.Sparse.eval_collectBalanced, rawRowCheck1662]

def rawRow1663 : Integer.Sparse Key := [(key3116, -2), (key3107, -2), (key3146, -2), (key3117, 2), (key3112, 2), (key3147, 2), (key3057, 2), (key3051, 2), (key3074, 2), (key3112, -6), (key2693, -2), (key2686, -2), (key2719, -2), (key2822, 6)]

theorem rawRowCheck1663 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form6 = rawRow1663 := by decide +kernel

def row1663 : Integer.Sparse Key := [(key2686, -2), (key2693, -2), (key2719, -2), (key2822, 6), (key3051, 2), (key3057, 2), (key3074, 2), (key3107, -2), (key3112, -4), (key3116, -2), (key3117, 2), (key3146, -2), (key3147, 2)]

theorem rowCheck1663 : row1663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1663 := by decide +kernel

theorem rowEval1663 (x : Key → ℝ) : Integer.Sparse.eval row1663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1663, Integer.Sparse.eval_collectBalanced, rawRowCheck1663]

end MUB6.Certificate.GramRows

end OAI
