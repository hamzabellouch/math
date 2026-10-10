import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow704 : Integer.Sparse Key := [(key3017, -2), (key2616, -2), (key2829, -2), (key2831, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2612, 1), (key2805, 1), (key2983, 2), (key2628, 2), (key2972, 2), (key2728, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2628, -1), (key2702, -1), (key2904, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2646, -1), (key2893, -1), (key2747, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2646, 1), (key2735, 1)]

theorem rawRowCheck704 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form0 = rawRow704 := by decide +kernel

def row704 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1), (key3017, -2)]

theorem rowCheck704 : row704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow704 := by decide +kernel

theorem rowEval704 (x : Key → ℝ) : Integer.Sparse.eval row704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck704, Integer.Sparse.eval_collectBalanced, rawRowCheck704]

def rawRow705 : Integer.Sparse Key := [(key3017, -2), (key2829, -2), (key2616, -2), (key2960, 1), (key2831, 1), (key2950, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2983, 2), (key2972, 2), (key2628, 2), (key2983, -1), (key2728, -1), (key2976, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2904, -1), (key2997, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key3000, 1), (key2747, 1), (key2998, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

theorem rawRowCheck705 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form0 = rawRow705 := by decide +kernel

def row705 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1), (key3017, -2)]

theorem rowCheck705 : row705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow705 := by decide +kernel

theorem rowEval705 (x : Key → ℝ) : Integer.Sparse.eval row705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck705, Integer.Sparse.eval_collectBalanced, rawRowCheck705]

def rawRow706 : Integer.Sparse Key := [(key2706, -2), (key2860, -2), (key3023, -2), (key2726, 1), (key2732, 1), (key2870, 1), (key3026, 1), (key2885, 1), (key3030, 1), (key2667, 2), (key2735, 2), (key2747, 2), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2897, 1), (key2904, 1)]

theorem rawRowCheck706 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form0 = rawRow706 := by decide +kernel

def row706 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck706 : row706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow706 := by decide +kernel

theorem rowEval706 (x : Key → ℝ) : Integer.Sparse.eval row706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck706, Integer.Sparse.eval_collectBalanced, rawRowCheck706]

def rawRow707 : Integer.Sparse Key := [(key2706, -2), (key3023, -2), (key2860, -2), (key2732, 1), (key2726, 1), (key3026, 1), (key2870, 1), (key3030, 1), (key2885, 1), (key2667, 2), (key2747, 2), (key2735, 2), (key2943, -1), (key2936, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2998, -1), (key2673, -1), (key2667, -1), (key2728, -1), (key2702, -1), (key2747, -1), (key2737, -1), (key2795, 1), (key2782, 1), (key2831, 1), (key2805, 1), (key2904, 1), (key2897, 1)]

theorem rawRowCheck707 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form0 = rawRow707 := by decide +kernel

def row707 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck707 : row707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow707 := by decide +kernel

theorem rowEval707 (x : Key → ℝ) : Integer.Sparse.eval row707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck707, Integer.Sparse.eval_collectBalanced, rawRowCheck707]

def rawRow708 : Integer.Sparse Key := [(key2860, -2), (key2706, -2), (key3023, -2), (key2870, 1), (key2885, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2735, 2), (key2667, 2), (key2747, 2), (key2948, -1), (key2998, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2702, -1), (key2737, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2805, 1), (key2897, 1), (key2782, 1), (key2904, 1), (key2795, 1), (key2831, 1)]

theorem rawRowCheck708 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form0 = rawRow708 := by decide +kernel

def row708 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck708 : row708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow708 := by decide +kernel

theorem rowEval708 (x : Key → ℝ) : Integer.Sparse.eval row708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck708, Integer.Sparse.eval_collectBalanced, rawRowCheck708]

def rawRow709 : Integer.Sparse Key := [(key2860, -2), (key3023, -2), (key2706, -2), (key2885, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key3026, 1), (key2732, 1), (key2735, 2), (key2747, 2), (key2667, 2), (key2998, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2960, -1), (key2943, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2728, -1), (key2673, -1), (key2897, 1), (key2805, 1), (key2904, 1), (key2782, 1), (key2831, 1), (key2795, 1)]

theorem rawRowCheck709 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form0 = rawRow709 := by decide +kernel

def row709 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck709 : row709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow709 := by decide +kernel

theorem rowEval709 (x : Key → ℝ) : Integer.Sparse.eval row709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck709, Integer.Sparse.eval_collectBalanced, rawRowCheck709]

def rawRow710 : Integer.Sparse Key := [(key3023, -2), (key2706, -2), (key2860, -2), (key3026, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2726, 1), (key2870, 1), (key2747, 2), (key2667, 2), (key2735, 2), (key2960, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2936, -1), (key2948, -1), (key2728, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2667, -1), (key2702, -1), (key2831, 1), (key2904, 1), (key2795, 1), (key2897, 1), (key2782, 1), (key2805, 1)]

theorem rawRowCheck710 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form0 = rawRow710 := by decide +kernel

def row710 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck710 : row710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow710 := by decide +kernel

theorem rowEval710 (x : Key → ℝ) : Integer.Sparse.eval row710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck710, Integer.Sparse.eval_collectBalanced, rawRowCheck710]

def rawRow711 : Integer.Sparse Key := [(key3023, -2), (key2860, -2), (key2706, -2), (key3030, 1), (key3026, 1), (key2885, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key2747, 2), (key2735, 2), (key2667, 2), (key3000, -1), (key2960, -1), (key2998, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2747, -1), (key2728, -1), (key2737, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2904, 1), (key2831, 1), (key2897, 1), (key2795, 1), (key2805, 1), (key2782, 1)]

theorem rawRowCheck711 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form0 = rawRow711 := by decide +kernel

def row711 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck711 : row711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow711 := by decide +kernel

theorem rowEval711 (x : Key → ℝ) : Integer.Sparse.eval row711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck711, Integer.Sparse.eval_collectBalanced, rawRowCheck711]

def rawRow712 : Integer.Sparse Key := [(key2632, -2), (key2870, -2), (key3026, -2), (key2640, 1), (key2644, 1), (key2860, 1), (key3023, 1), (key2885, 1), (key3030, 1), (key2612, 2), (key2948, 2), (key2960, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2747, -1), (key2998, -1), (key3000, -1), (key2612, -1), (key2618, -1), (key2805, -1), (key2831, -1), (key2950, -1), (key2960, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2728, 1), (key2976, 1), (key2983, 1)]

theorem rawRowCheck712 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form0 = rawRow712 := by decide +kernel

def row712 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2948, 2), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck712 : row712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow712 := by decide +kernel

theorem rowEval712 (x : Key → ℝ) : Integer.Sparse.eval row712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck712, Integer.Sparse.eval_collectBalanced, rawRowCheck712]

def rawRow713 : Integer.Sparse Key := [(key2632, -2), (key3026, -2), (key2870, -2), (key2644, 1), (key2640, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2885, 1), (key2616, 2), (key2960, 2), (key2948, 2), (key2653, -1), (key2646, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2998, -1), (key2618, -1), (key2612, -1), (key2831, -1), (key2805, -1), (key2960, -1), (key2950, -1), (key2641, 1), (key2628, 1), (key2728, 1), (key2702, 1), (key2983, 1), (key2976, 1)]

theorem rawRowCheck713 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form0 = rawRow713 := by decide +kernel

def row713 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2948, 2), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck713 : row713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow713 := by decide +kernel

theorem rowEval713 (x : Key → ℝ) : Integer.Sparse.eval row713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck713, Integer.Sparse.eval_collectBalanced, rawRowCheck713]

def rawRow714 : Integer.Sparse Key := [(key2870, -2), (key2632, -2), (key3026, -2), (key2860, 1), (key2885, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2829, 2), (key2612, 2), (key2960, 2), (key2735, -1), (key2998, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2805, -1), (key2950, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2702, 1), (key2976, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2728, 1)]

theorem rawRowCheck714 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form0 = rawRow714 := by decide +kernel

def row714 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck714 : row714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow714 := by decide +kernel

theorem rowEval714 (x : Key → ℝ) : Integer.Sparse.eval row714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck714, Integer.Sparse.eval_collectBalanced, rawRowCheck714]

def rawRow715 : Integer.Sparse Key := [(key2870, -2), (key3026, -2), (key2632, -2), (key2885, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key3023, 1), (key2644, 1), (key2829, 2), (key2960, 2), (key2612, 2), (key2998, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2747, -1), (key2653, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2831, -1), (key2618, -1), (key2976, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2728, 1), (key2641, 1)]

theorem rawRowCheck715 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form0 = rawRow715 := by decide +kernel

def row715 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck715 : row715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow715 := by decide +kernel

theorem rowEval715 (x : Key → ℝ) : Integer.Sparse.eval row715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck715, Integer.Sparse.eval_collectBalanced, rawRowCheck715]

def rawRow716 : Integer.Sparse Key := [(key3026, -2), (key2632, -2), (key2870, -2), (key3023, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2640, 1), (key2860, 1), (key3017, 2), (key2616, 2), (key2829, 2), (key2747, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2646, -1), (key2735, -1), (key2831, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2612, -1), (key2805, -1), (key2728, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2628, 1), (key2702, 1)]

theorem rawRowCheck716 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form0 = rawRow716 := by decide +kernel

def row716 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck716 : row716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow716 := by decide +kernel

theorem rowEval716 (x : Key → ℝ) : Integer.Sparse.eval row716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck716, Integer.Sparse.eval_collectBalanced, rawRowCheck716]

def rawRow717 : Integer.Sparse Key := [(key3026, -2), (key2870, -2), (key2632, -2), (key3030, 1), (key3023, 1), (key2885, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3017, 2), (key2829, 2), (key2616, 2), (key3000, -1), (key2747, -1), (key2998, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, -1), (key2831, -1), (key2950, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 1), (key2728, 1), (key2976, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

theorem rawRowCheck717 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form0 = rawRow717 := by decide +kernel

def row717 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

theorem rowCheck717 : row717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow717 := by decide +kernel

theorem rowEval717 (x : Key → ℝ) : Integer.Sparse.eval row717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck717, Integer.Sparse.eval_collectBalanced, rawRowCheck717]

def rawRow718 : Integer.Sparse Key := [(key1289, -6), (key1309, 2), (key1309, 2), (key1350, 2), (key1384, 6), (key1539, -2), (key1539, -2), (key1895, -2), (key1417, -2), (key1417, -2), (key1471, -2), (key1566, 2), (key1566, 2), (key1902, 2)]

theorem rawRowCheck718 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form1 = rawRow718 := by decide +kernel

def row718 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

theorem rowCheck718 : row718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow718 := by decide +kernel

theorem rowEval718 (x : Key → ℝ) : Integer.Sparse.eval row718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck718, Integer.Sparse.eval_collectBalanced, rawRowCheck718]

def rawRow719 : Integer.Sparse Key := [(key1289, -6), (key1309, 2), (key1350, 2), (key1309, 2), (key1384, 6), (key1539, -2), (key1895, -2), (key1539, -2), (key1417, -2), (key1471, -2), (key1417, -2), (key1566, 2), (key1902, 2), (key1566, 2)]

theorem rawRowCheck719 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form1 = rawRow719 := by decide +kernel

def row719 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

theorem rowCheck719 : row719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow719 := by decide +kernel

theorem rowEval719 (x : Key → ℝ) : Integer.Sparse.eval row719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck719, Integer.Sparse.eval_collectBalanced, rawRowCheck719]

def rawRow720 : Integer.Sparse Key := [(key1289, -6), (key1350, 2), (key1309, 2), (key1309, 2), (key1384, 6), (key1895, -2), (key1539, -2), (key1539, -2), (key1471, -2), (key1417, -2), (key1417, -2), (key1902, 2), (key1566, 2), (key1566, 2)]

theorem rawRowCheck720 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form1 = rawRow720 := by decide +kernel

def row720 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

theorem rowCheck720 : row720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow720 := by decide +kernel

theorem rowEval720 (x : Key → ℝ) : Integer.Sparse.eval row720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck720, Integer.Sparse.eval_collectBalanced, rawRowCheck720]

def rawRow721 : Integer.Sparse Key := [(key1309, -6), (key1289, 2), (key1309, 2), (key1350, 2), (key1539, 6), (key1384, -2), (key1539, -2), (key1895, -2), (key1566, -2), (key1615, -2), (key1680, -2), (key1417, 2), (key1615, 2), (key1917, 2)]

theorem rawRowCheck721 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form1 = rawRow721 := by decide +kernel

def row721 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

theorem rowCheck721 : row721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow721 := by decide +kernel

theorem rowEval721 (x : Key → ℝ) : Integer.Sparse.eval row721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck721, Integer.Sparse.eval_collectBalanced, rawRowCheck721]

def rawRow722 : Integer.Sparse Key := [(key1309, -6), (key1289, 2), (key1350, 2), (key1309, 2), (key1539, 6), (key1384, -2), (key1895, -2), (key1539, -2), (key1566, -2), (key1680, -2), (key1615, -2), (key1417, 2), (key1917, 2), (key1615, 2)]

theorem rawRowCheck722 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form1 = rawRow722 := by decide +kernel

def row722 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

theorem rowCheck722 : row722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow722 := by decide +kernel

theorem rowEval722 (x : Key → ℝ) : Integer.Sparse.eval row722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck722, Integer.Sparse.eval_collectBalanced, rawRowCheck722]

def rawRow723 : Integer.Sparse Key := [(key1309, -6), (key1309, 2), (key1289, 2), (key1350, 2), (key1539, 6), (key1539, -2), (key1384, -2), (key1895, -2), (key1615, -2), (key1566, -2), (key1680, -2), (key1615, 2), (key1417, 2), (key1917, 2)]

theorem rawRowCheck723 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form1 = rawRow723 := by decide +kernel

def row723 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

theorem rowCheck723 : row723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow723 := by decide +kernel

theorem rowEval723 (x : Key → ℝ) : Integer.Sparse.eval row723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck723, Integer.Sparse.eval_collectBalanced, rawRowCheck723]

def rawRow724 : Integer.Sparse Key := [(key1309, -6), (key1309, 2), (key1350, 2), (key1289, 2), (key1539, 6), (key1539, -2), (key1895, -2), (key1384, -2), (key1615, -2), (key1680, -2), (key1566, -2), (key1615, 2), (key1917, 2), (key1417, 2)]

theorem rawRowCheck724 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form1 = rawRow724 := by decide +kernel

def row724 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

theorem rowCheck724 : row724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow724 := by decide +kernel

theorem rowEval724 (x : Key → ℝ) : Integer.Sparse.eval row724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck724, Integer.Sparse.eval_collectBalanced, rawRowCheck724]

def rawRow725 : Integer.Sparse Key := [(key1309, -6), (key1350, 2), (key1289, 2), (key1309, 2), (key1539, 6), (key1895, -2), (key1384, -2), (key1539, -2), (key1680, -2), (key1566, -2), (key1615, -2), (key1917, 2), (key1417, 2), (key1615, 2)]

theorem rawRowCheck725 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form1 = rawRow725 := by decide +kernel

def row725 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

theorem rowCheck725 : row725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow725 := by decide +kernel

theorem rowEval725 (x : Key → ℝ) : Integer.Sparse.eval row725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck725, Integer.Sparse.eval_collectBalanced, rawRowCheck725]

def rawRow726 : Integer.Sparse Key := [(key1309, -6), (key1350, 2), (key1309, 2), (key1289, 2), (key1539, 6), (key1895, -2), (key1539, -2), (key1384, -2), (key1680, -2), (key1615, -2), (key1566, -2), (key1917, 2), (key1615, 2), (key1417, 2)]

theorem rawRowCheck726 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form1 = rawRow726 := by decide +kernel

def row726 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

theorem rowCheck726 : row726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow726 := by decide +kernel

theorem rowEval726 (x : Key → ℝ) : Integer.Sparse.eval row726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck726, Integer.Sparse.eval_collectBalanced, rawRowCheck726]

def rawRow727 : Integer.Sparse Key := [(key1384, -6), (key1417, 2), (key1417, 2), (key1471, 2), (key1289, 6), (key1566, -2), (key1566, -2), (key1902, -2), (key1309, -2), (key1309, -2), (key1350, -2), (key1539, 2), (key1539, 2), (key1895, 2)]

theorem rawRowCheck727 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form1 = rawRow727 := by decide +kernel

def row727 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck727 : row727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow727 := by decide +kernel

theorem rowEval727 (x : Key → ℝ) : Integer.Sparse.eval row727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck727, Integer.Sparse.eval_collectBalanced, rawRowCheck727]

def rawRow728 : Integer.Sparse Key := [(key1384, -6), (key1417, 2), (key1471, 2), (key1417, 2), (key1289, 6), (key1566, -2), (key1902, -2), (key1566, -2), (key1309, -2), (key1350, -2), (key1309, -2), (key1539, 2), (key1895, 2), (key1539, 2)]

theorem rawRowCheck728 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form1 = rawRow728 := by decide +kernel

def row728 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck728 : row728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow728 := by decide +kernel

theorem rowEval728 (x : Key → ℝ) : Integer.Sparse.eval row728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck728, Integer.Sparse.eval_collectBalanced, rawRowCheck728]

def rawRow729 : Integer.Sparse Key := [(key1384, -6), (key1471, 2), (key1417, 2), (key1417, 2), (key1289, 6), (key1902, -2), (key1566, -2), (key1566, -2), (key1350, -2), (key1309, -2), (key1309, -2), (key1895, 2), (key1539, 2), (key1539, 2)]

theorem rawRowCheck729 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form1 = rawRow729 := by decide +kernel

def row729 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

theorem rowCheck729 : row729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow729 := by decide +kernel

theorem rowEval729 (x : Key → ℝ) : Integer.Sparse.eval row729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck729, Integer.Sparse.eval_collectBalanced, rawRowCheck729]

def rawRow730 : Integer.Sparse Key := [(key1417, -6), (key1384, 2), (key1417, 2), (key1471, 2), (key1566, 6), (key1289, -2), (key1566, -2), (key1902, -2), (key1539, -2), (key1615, -2), (key1680, -2), (key1309, 2), (key1615, 2), (key1917, 2)]

theorem rawRowCheck730 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form1 = rawRow730 := by decide +kernel

def row730 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

theorem rowCheck730 : row730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow730 := by decide +kernel

theorem rowEval730 (x : Key → ℝ) : Integer.Sparse.eval row730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck730, Integer.Sparse.eval_collectBalanced, rawRowCheck730]

def rawRow731 : Integer.Sparse Key := [(key1417, -6), (key1384, 2), (key1471, 2), (key1417, 2), (key1566, 6), (key1289, -2), (key1902, -2), (key1566, -2), (key1539, -2), (key1680, -2), (key1615, -2), (key1309, 2), (key1917, 2), (key1615, 2)]

theorem rawRowCheck731 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form1 = rawRow731 := by decide +kernel

def row731 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

theorem rowCheck731 : row731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow731 := by decide +kernel

theorem rowEval731 (x : Key → ℝ) : Integer.Sparse.eval row731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck731, Integer.Sparse.eval_collectBalanced, rawRowCheck731]

def rawRow732 : Integer.Sparse Key := [(key1417, -6), (key1417, 2), (key1384, 2), (key1471, 2), (key1566, 6), (key1566, -2), (key1289, -2), (key1902, -2), (key1615, -2), (key1539, -2), (key1680, -2), (key1615, 2), (key1309, 2), (key1917, 2)]

theorem rawRowCheck732 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form1 = rawRow732 := by decide +kernel

def row732 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

theorem rowCheck732 : row732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow732 := by decide +kernel

theorem rowEval732 (x : Key → ℝ) : Integer.Sparse.eval row732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck732, Integer.Sparse.eval_collectBalanced, rawRowCheck732]

def rawRow733 : Integer.Sparse Key := [(key1417, -6), (key1417, 2), (key1471, 2), (key1384, 2), (key1566, 6), (key1566, -2), (key1902, -2), (key1289, -2), (key1615, -2), (key1680, -2), (key1539, -2), (key1615, 2), (key1917, 2), (key1309, 2)]

theorem rawRowCheck733 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form1 = rawRow733 := by decide +kernel

def row733 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

theorem rowCheck733 : row733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow733 := by decide +kernel

theorem rowEval733 (x : Key → ℝ) : Integer.Sparse.eval row733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck733, Integer.Sparse.eval_collectBalanced, rawRowCheck733]

def rawRow734 : Integer.Sparse Key := [(key1417, -6), (key1471, 2), (key1384, 2), (key1417, 2), (key1566, 6), (key1902, -2), (key1289, -2), (key1566, -2), (key1680, -2), (key1539, -2), (key1615, -2), (key1917, 2), (key1309, 2), (key1615, 2)]

theorem rawRowCheck734 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form1 = rawRow734 := by decide +kernel

def row734 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

theorem rowCheck734 : row734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow734 := by decide +kernel

theorem rowEval734 (x : Key → ℝ) : Integer.Sparse.eval row734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck734, Integer.Sparse.eval_collectBalanced, rawRowCheck734]

def rawRow735 : Integer.Sparse Key := [(key1417, -6), (key1471, 2), (key1417, 2), (key1384, 2), (key1566, 6), (key1902, -2), (key1566, -2), (key1289, -2), (key1680, -2), (key1615, -2), (key1539, -2), (key1917, 2), (key1615, 2), (key1309, 2)]

theorem rawRowCheck735 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form1 = rawRow735 := by decide +kernel

def row735 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

theorem rowCheck735 : row735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow735 := by decide +kernel

theorem rowEval735 (x : Key → ℝ) : Integer.Sparse.eval row735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck735, Integer.Sparse.eval_collectBalanced, rawRowCheck735]

end MUB6.Certificate.GramRows

end OAI
