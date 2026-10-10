import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6656 : Integer.Sparse Key := [(key2972, 1), (key2976, 1), (key2983, -2), (key2628, 1), (key2641, 1), (key2702, -2), (key2976, -2), (key2728, 1), (key2983, 1), (key2628, -2), (key2702, 1), (key2972, 1), (key2936, -1), (key2943, -1), (key2960, 1), (key3000, 1), (key2646, -1), (key2653, -1), (key2735, 1), (key2998, 1), (key2667, 1), (key2943, 1), (key2747, -1), (key2960, -1), (key2616, 1), (key2640, 1), (key2794, -1), (key2829, -1), (key2732, 2), (key2835, -1), (key2885, -1), (key2644, 2), (key2798, -1), (key2885, -1), (key2621, -1), (key2644, -1), (key2676, -1), (key2732, -1), (key2798, 2), (key2835, 2)]

theorem rawRowCheck6656 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form7 = rawRow6656 := by decide +kernel

def row6656 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2728, 1), (key2732, 1), (key2735, 1), (key2747, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2936, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

theorem rowCheck6656 : row6656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6656 := by decide +kernel

theorem rowEval6656 (x : Key → ℝ) : Integer.Sparse.eval row6656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6656, Integer.Sparse.eval_collectBalanced, rawRowCheck6656]

def rawRow6657 : Integer.Sparse Key := [(key2976, 1), (key2972, 1), (key2983, -2), (key2641, 1), (key2628, 1), (key2976, -2), (key2702, -2), (key2983, 1), (key2728, 1), (key2628, -2), (key2972, 1), (key2702, 1), (key2943, -1), (key2936, -1), (key3000, 1), (key2960, 1), (key2653, -1), (key2646, -1), (key2998, 1), (key2735, 1), (key2943, 1), (key2667, 1), (key2960, -1), (key2747, -1), (key2640, 1), (key2616, 1), (key2829, -1), (key2794, -1), (key2732, 2), (key2885, -1), (key2835, -1), (key2644, 2), (key2885, -1), (key2798, -1), (key2644, -1), (key2621, -1), (key2732, -1), (key2676, -1), (key2835, 2), (key2798, 2)]

theorem rawRowCheck6657 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form7 = rawRow6657 := by decide +kernel

def row6657 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2728, 1), (key2732, 1), (key2735, 1), (key2747, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2936, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

theorem rowCheck6657 : row6657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6657 := by decide +kernel

theorem rowEval6657 (x : Key → ℝ) : Integer.Sparse.eval row6657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6657, Integer.Sparse.eval_collectBalanced, rawRowCheck6657]

def rawRow6658 : Integer.Sparse Key := [(key2972, 1), (key2983, 1), (key2976, -2), (key2702, 1), (key2728, 1), (key2628, -2), (key2983, -2), (key2641, 1), (key2976, 1), (key2702, -2), (key2628, 1), (key2972, 1), (key2948, -1), (key2960, -1), (key2943, 1), (key2998, 1), (key2735, -1), (key2747, -1), (key2646, 1), (key3000, 1), (key2612, 1), (key2960, 1), (key2653, -1), (key2943, -1), (key2671, 1), (key2794, 1), (key2640, -1), (key2726, -1), (key2835, 2), (key2732, -1), (key2885, -1), (key2798, 2), (key2644, -1), (key2885, -1), (key2676, -1), (key2798, -1), (key2621, -1), (key2835, -1), (key2644, 2), (key2732, 2)]

theorem rawRowCheck6658 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form7 = rawRow6658 := by decide +kernel

def row6658 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2640, -1), (key2641, 1), (key2644, 1), (key2646, 1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2794, 1), (key2798, 1), (key2835, 1), (key2885, -2), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

theorem rowCheck6658 : row6658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6658 := by decide +kernel

theorem rowEval6658 (x : Key → ℝ) : Integer.Sparse.eval row6658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6658, Integer.Sparse.eval_collectBalanced, rawRowCheck6658]

def rawRow6659 : Integer.Sparse Key := [(key2983, 1), (key2972, 1), (key2976, -2), (key2728, 1), (key2702, 1), (key2983, -2), (key2628, -2), (key2976, 1), (key2641, 1), (key2702, -2), (key2972, 1), (key2628, 1), (key2960, -1), (key2948, -1), (key2998, 1), (key2943, 1), (key2747, -1), (key2735, -1), (key3000, 1), (key2646, 1), (key2960, 1), (key2612, 1), (key2943, -1), (key2653, -1), (key2794, 1), (key2671, 1), (key2726, -1), (key2640, -1), (key2835, 2), (key2885, -1), (key2732, -1), (key2798, 2), (key2885, -1), (key2644, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2732, 2), (key2644, 2)]

theorem rawRowCheck6659 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form7 = rawRow6659 := by decide +kernel

def row6659 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2640, -1), (key2641, 1), (key2644, 1), (key2646, 1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2794, 1), (key2798, 1), (key2835, 1), (key2885, -2), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, 1), (key3000, 1)]

theorem rowCheck6659 : row6659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6659 := by decide +kernel

theorem rowEval6659 (x : Key → ℝ) : Integer.Sparse.eval row6659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6659, Integer.Sparse.eval_collectBalanced, rawRowCheck6659]

def rawRow6660 : Integer.Sparse Key := [(key2976, 1), (key2983, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2641, -2), (key2728, -2), (key2628, 1), (key2702, 1), (key2972, -2), (key2628, 1), (key2702, 1), (key2998, -1), (key3000, -1), (key2936, 1), (key2948, 1), (key2998, -1), (key3000, -1), (key2653, 1), (key2747, 1), (key2653, 1), (key2747, 1), (key2612, -1), (key2667, -1), (key2726, 1), (key2829, 1), (key2616, -1), (key2671, -1), (key2885, 2), (key2732, -1), (key2835, -1), (key2885, 2), (key2644, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2621, 2), (key2676, 2)]

theorem rawRowCheck6660 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form7 = rawRow6660 := by decide +kernel

def row6660 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2653, 2), (key2667, -1), (key2671, -1), (key2676, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2732, -2), (key2747, 2), (key2798, -2), (key2829, 1), (key2835, -2), (key2885, 4), (key2936, 1), (key2948, 1), (key2972, -4), (key2976, 2), (key2983, 2), (key2998, -2), (key3000, -2)]

theorem rowCheck6660 : row6660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6660 := by decide +kernel

theorem rowEval6660 (x : Key → ℝ) : Integer.Sparse.eval row6660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6660, Integer.Sparse.eval_collectBalanced, rawRowCheck6660]

def rawRow6661 : Integer.Sparse Key := [(key2983, 1), (key2976, 1), (key2972, -2), (key2983, 1), (key2976, 1), (key2728, -2), (key2641, -2), (key2702, 1), (key2628, 1), (key2972, -2), (key2702, 1), (key2628, 1), (key3000, -1), (key2998, -1), (key2948, 1), (key2936, 1), (key3000, -1), (key2998, -1), (key2747, 1), (key2653, 1), (key2747, 1), (key2653, 1), (key2667, -1), (key2612, -1), (key2829, 1), (key2726, 1), (key2671, -1), (key2616, -1), (key2885, 2), (key2835, -1), (key2732, -1), (key2885, 2), (key2798, -1), (key2644, -1), (key2835, -1), (key2732, -1), (key2798, -1), (key2644, -1), (key2676, 2), (key2621, 2)]

theorem rawRowCheck6661 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form7 = rawRow6661 := by decide +kernel

def row6661 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2653, 2), (key2667, -1), (key2671, -1), (key2676, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2732, -2), (key2747, 2), (key2798, -2), (key2829, 1), (key2835, -2), (key2885, 4), (key2936, 1), (key2948, 1), (key2972, -4), (key2976, 2), (key2983, 2), (key2998, -2), (key3000, -2)]

theorem rowCheck6661 : row6661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6661 := by decide +kernel

theorem rowEval6661 (x : Key → ℝ) : Integer.Sparse.eval row6661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6661, Integer.Sparse.eval_collectBalanced, rawRowCheck6661]

def rawRow6662 : Integer.Sparse Key := [(key2646, 1), (key2648, 1), (key2653, -2), (key2735, 1), (key2737, 1), (key2893, -2), (key2997, -2), (key2897, 1), (key2998, 1), (key2747, -2), (key2904, 1), (key3000, 1), (key2612, -1), (key2618, -1), (key2641, 1), (key2653, 1), (key2667, -1), (key2673, -1), (key2782, 1), (key2938, 1), (key2805, 1), (key2950, 1), (key2897, -1), (key2976, -1), (key2728, 1), (key2747, 1), (key2904, -1), (key2983, -1), (key2616, 2), (key2632, -1), (key2640, -1), (key2671, 2), (key2706, -1), (key2726, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2)]

theorem rawRowCheck6662 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form7 = rawRow6662 := by decide +kernel

def row6662 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6662 : row6662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6662 := by decide +kernel

theorem rowEval6662 (x : Key → ℝ) : Integer.Sparse.eval row6662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6662, Integer.Sparse.eval_collectBalanced, rawRowCheck6662]

def rawRow6663 : Integer.Sparse Key := [(key2648, 1), (key2646, 1), (key2653, -2), (key2737, 1), (key2735, 1), (key2997, -2), (key2893, -2), (key2998, 1), (key2897, 1), (key2747, -2), (key3000, 1), (key2904, 1), (key2618, -1), (key2612, -1), (key2653, 1), (key2641, 1), (key2673, -1), (key2667, -1), (key2938, 1), (key2782, 1), (key2950, 1), (key2805, 1), (key2976, -1), (key2897, -1), (key2747, 1), (key2728, 1), (key2983, -1), (key2904, -1), (key2616, 2), (key2640, -1), (key2632, -1), (key2671, 2), (key2726, -1), (key2706, -1), (key2794, -1), (key2786, -1), (key2829, -1), (key2809, -1), (key2870, 2), (key2860, 2)]

theorem rawRowCheck6663 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form7 = rawRow6663 := by decide +kernel

def row6663 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6663 : row6663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6663 := by decide +kernel

theorem rowEval6663 (x : Key → ℝ) : Integer.Sparse.eval row6663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6663, Integer.Sparse.eval_collectBalanced, rawRowCheck6663]

def rawRow6664 : Integer.Sparse Key := [(key2648, 1), (key2653, 1), (key2646, -2), (key2997, 1), (key2998, 1), (key2737, -2), (key2897, -2), (key2735, 1), (key2893, 1), (key3000, -2), (key2747, 1), (key2904, 1), (key2648, -1), (key2653, -1), (key2612, 1), (key2628, 1), (key2938, -1), (key2943, -1), (key2673, 1), (key2795, 1), (key2737, 1), (key2897, 1), (key2702, -1), (key2805, -1), (key2960, 1), (key2983, 1), (key2728, -1), (key2831, -1), (key2640, 2), (key2616, -1), (key2632, -1), (key2726, 2), (key2671, -1), (key2706, -1), (key2829, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2786, 2), (key2809, 2)]

theorem rawRowCheck6664 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form7 = rawRow6664 := by decide +kernel

def row6664 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6664 : row6664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6664 := by decide +kernel

theorem rowEval6664 (x : Key → ℝ) : Integer.Sparse.eval row6664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6664, Integer.Sparse.eval_collectBalanced, rawRowCheck6664]

def rawRow6665 : Integer.Sparse Key := [(key2653, 1), (key2648, 1), (key2646, -2), (key2998, 1), (key2997, 1), (key2897, -2), (key2737, -2), (key2893, 1), (key2735, 1), (key3000, -2), (key2904, 1), (key2747, 1), (key2653, -1), (key2648, -1), (key2628, 1), (key2612, 1), (key2943, -1), (key2938, -1), (key2795, 1), (key2673, 1), (key2897, 1), (key2737, 1), (key2805, -1), (key2702, -1), (key2983, 1), (key2960, 1), (key2831, -1), (key2728, -1), (key2640, 2), (key2632, -1), (key2616, -1), (key2726, 2), (key2706, -1), (key2671, -1), (key2870, -1), (key2829, -1), (key2860, -1), (key2794, -1), (key2809, 2), (key2786, 2)]

theorem rawRowCheck6665 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form7 = rawRow6665 := by decide +kernel

def row6665 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6665 : row6665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6665 := by decide +kernel

theorem rowEval6665 (x : Key → ℝ) : Integer.Sparse.eval row6665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6665, Integer.Sparse.eval_collectBalanced, rawRowCheck6665]

def rawRow6666 : Integer.Sparse Key := [(key2735, 1), (key2737, 1), (key2747, -2), (key2646, 1), (key2648, 1), (key2893, -2), (key2997, -2), (key2904, 1), (key3000, 1), (key2653, -2), (key2897, 1), (key2998, 1), (key2667, -1), (key2673, -1), (key2728, 1), (key2747, 1), (key2612, -1), (key2618, -1), (key2805, 1), (key2950, 1), (key2782, 1), (key2938, 1), (key2904, -1), (key2983, -1), (key2641, 1), (key2653, 1), (key2897, -1), (key2976, -1), (key2671, 2), (key2786, -1), (key2794, -1), (key2616, 2), (key2809, -1), (key2829, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, 2), (key2870, 2)]

theorem rawRowCheck6666 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form7 = rawRow6666 := by decide +kernel

def row6666 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6666 : row6666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6666 := by decide +kernel

theorem rowEval6666 (x : Key → ℝ) : Integer.Sparse.eval row6666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6666, Integer.Sparse.eval_collectBalanced, rawRowCheck6666]

def rawRow6667 : Integer.Sparse Key := [(key2737, 1), (key2735, 1), (key2747, -2), (key2648, 1), (key2646, 1), (key2997, -2), (key2893, -2), (key3000, 1), (key2904, 1), (key2653, -2), (key2998, 1), (key2897, 1), (key2673, -1), (key2667, -1), (key2747, 1), (key2728, 1), (key2618, -1), (key2612, -1), (key2950, 1), (key2805, 1), (key2938, 1), (key2782, 1), (key2983, -1), (key2904, -1), (key2653, 1), (key2641, 1), (key2976, -1), (key2897, -1), (key2671, 2), (key2794, -1), (key2786, -1), (key2616, 2), (key2829, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, 2), (key2860, 2)]

theorem rawRowCheck6667 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form7 = rawRow6667 := by decide +kernel

def row6667 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6667 : row6667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6667 := by decide +kernel

theorem rowEval6667 (x : Key → ℝ) : Integer.Sparse.eval row6667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6667, Integer.Sparse.eval_collectBalanced, rawRowCheck6667]

def rawRow6668 : Integer.Sparse Key := [(key2735, 1), (key2747, 1), (key2737, -2), (key2893, 1), (key2904, 1), (key2646, -2), (key3000, -2), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, 1), (key2998, 1), (key2702, -1), (key2728, -1), (key2673, 1), (key2737, 1), (key2805, -1), (key2831, -1), (key2612, 1), (key2960, 1), (key2628, 1), (key2983, 1), (key2648, -1), (key2938, -1), (key2795, 1), (key2897, 1), (key2653, -1), (key2943, -1), (key2786, 2), (key2671, -1), (key2794, -1), (key2809, 2), (key2616, -1), (key2829, -1), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, 2), (key2726, 2)]

theorem rawRowCheck6668 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form7 = rawRow6668 := by decide +kernel

def row6668 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6668 : row6668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6668 := by decide +kernel

theorem rowEval6668 (x : Key → ℝ) : Integer.Sparse.eval row6668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6668, Integer.Sparse.eval_collectBalanced, rawRowCheck6668]

def rawRow6669 : Integer.Sparse Key := [(key2747, 1), (key2735, 1), (key2737, -2), (key2904, 1), (key2893, 1), (key3000, -2), (key2646, -2), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, 1), (key2653, 1), (key2728, -1), (key2702, -1), (key2737, 1), (key2673, 1), (key2831, -1), (key2805, -1), (key2960, 1), (key2612, 1), (key2983, 1), (key2628, 1), (key2938, -1), (key2648, -1), (key2897, 1), (key2795, 1), (key2943, -1), (key2653, -1), (key2786, 2), (key2794, -1), (key2671, -1), (key2809, 2), (key2829, -1), (key2616, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, 2), (key2640, 2)]

theorem rawRowCheck6669 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form7 = rawRow6669 := by decide +kernel

def row6669 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6669 : row6669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6669 := by decide +kernel

theorem rowEval6669 (x : Key → ℝ) : Integer.Sparse.eval row6669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6669, Integer.Sparse.eval_collectBalanced, rawRowCheck6669]

def rawRow6670 : Integer.Sparse Key := [(key2893, 1), (key2904, 1), (key2897, -2), (key2735, 1), (key2747, 1), (key2646, -2), (key3000, -2), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, 1), (key2997, 1), (key2805, -1), (key2831, -1), (key2795, 1), (key2897, 1), (key2702, -1), (key2728, -1), (key2628, 1), (key2983, 1), (key2612, 1), (key2960, 1), (key2653, -1), (key2943, -1), (key2673, 1), (key2737, 1), (key2648, -1), (key2938, -1), (key2809, 2), (key2706, -1), (key2860, -1), (key2786, 2), (key2632, -1), (key2870, -1), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, 2), (key2726, 2)]

theorem rawRowCheck6670 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form7 = rawRow6670 := by decide +kernel

def row6670 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6670 : row6670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6670 := by decide +kernel

theorem rowEval6670 (x : Key → ℝ) : Integer.Sparse.eval row6670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6670, Integer.Sparse.eval_collectBalanced, rawRowCheck6670]

def rawRow6671 : Integer.Sparse Key := [(key2904, 1), (key2893, 1), (key2897, -2), (key2747, 1), (key2735, 1), (key3000, -2), (key2646, -2), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, 1), (key2648, 1), (key2831, -1), (key2805, -1), (key2897, 1), (key2795, 1), (key2728, -1), (key2702, -1), (key2983, 1), (key2628, 1), (key2960, 1), (key2612, 1), (key2943, -1), (key2653, -1), (key2737, 1), (key2673, 1), (key2938, -1), (key2648, -1), (key2809, 2), (key2860, -1), (key2706, -1), (key2786, 2), (key2870, -1), (key2632, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, 2), (key2640, 2)]

theorem rawRowCheck6671 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form7 = rawRow6671 := by decide +kernel

def row6671 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6671 : row6671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6671 := by decide +kernel

theorem rowEval6671 (x : Key → ℝ) : Integer.Sparse.eval row6671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6671, Integer.Sparse.eval_collectBalanced, rawRowCheck6671]

def rawRow6672 : Integer.Sparse Key := [(key2897, 1), (key2904, 1), (key2893, -2), (key2998, 1), (key3000, 1), (key2653, -2), (key2747, -2), (key2646, 1), (key2735, 1), (key2997, -2), (key2648, 1), (key2737, 1), (key2897, -1), (key2904, -1), (key2782, 1), (key2805, 1), (key2976, -1), (key2983, -1), (key2641, 1), (key2728, 1), (key2653, 1), (key2747, 1), (key2612, -1), (key2667, -1), (key2938, 1), (key2950, 1), (key2618, -1), (key2673, -1), (key2860, 2), (key2706, -1), (key2809, -1), (key2870, 2), (key2632, -1), (key2786, -1), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, 2), (key2671, 2)]

theorem rawRowCheck6672 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form7 = rawRow6672 := by decide +kernel

def row6672 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6672 : row6672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6672 := by decide +kernel

theorem rowEval6672 (x : Key → ℝ) : Integer.Sparse.eval row6672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6672, Integer.Sparse.eval_collectBalanced, rawRowCheck6672]

def rawRow6673 : Integer.Sparse Key := [(key2904, 1), (key2897, 1), (key2893, -2), (key3000, 1), (key2998, 1), (key2747, -2), (key2653, -2), (key2735, 1), (key2646, 1), (key2997, -2), (key2737, 1), (key2648, 1), (key2904, -1), (key2897, -1), (key2805, 1), (key2782, 1), (key2983, -1), (key2976, -1), (key2728, 1), (key2641, 1), (key2747, 1), (key2653, 1), (key2667, -1), (key2612, -1), (key2950, 1), (key2938, 1), (key2673, -1), (key2618, -1), (key2860, 2), (key2809, -1), (key2706, -1), (key2870, 2), (key2786, -1), (key2632, -1), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, 2), (key2616, 2)]

theorem rawRowCheck6673 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form7 = rawRow6673 := by decide +kernel

def row6673 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6673 : row6673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6673 := by decide +kernel

theorem rowEval6673 (x : Key → ℝ) : Integer.Sparse.eval row6673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6673, Integer.Sparse.eval_collectBalanced, rawRowCheck6673]

def rawRow6674 : Integer.Sparse Key := [(key2997, 1), (key2998, 1), (key3000, -2), (key2648, 1), (key2653, 1), (key2737, -2), (key2897, -2), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, 1), (key2893, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2648, -1), (key2653, -1), (key2737, 1), (key2897, 1), (key2673, 1), (key2795, 1), (key2728, -1), (key2831, -1), (key2612, 1), (key2628, 1), (key2702, -1), (key2805, -1), (key2726, 2), (key2829, -1), (key2870, -1), (key2640, 2), (key2794, -1), (key2860, -1), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, 2), (key2809, 2)]

theorem rawRowCheck6674 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form7 = rawRow6674 := by decide +kernel

def row6674 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6674 : row6674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6674 := by decide +kernel

theorem rowEval6674 (x : Key → ℝ) : Integer.Sparse.eval row6674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6674, Integer.Sparse.eval_collectBalanced, rawRowCheck6674]

def rawRow6675 : Integer.Sparse Key := [(key2998, 1), (key2997, 1), (key3000, -2), (key2653, 1), (key2648, 1), (key2897, -2), (key2737, -2), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, 1), (key2735, 1), (key2943, -1), (key2938, -1), (key2983, 1), (key2960, 1), (key2653, -1), (key2648, -1), (key2897, 1), (key2737, 1), (key2795, 1), (key2673, 1), (key2831, -1), (key2728, -1), (key2628, 1), (key2612, 1), (key2805, -1), (key2702, -1), (key2726, 2), (key2870, -1), (key2829, -1), (key2640, 2), (key2860, -1), (key2794, -1), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, 2), (key2786, 2)]

theorem rawRowCheck6675 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form7 = rawRow6675 := by decide +kernel

def row6675 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, 1), (key2632, -1), (key2640, 2), (key2646, -2), (key2671, -1), (key2673, 1), (key2702, -1), (key2706, -1), (key2726, 2), (key2728, -1), (key2735, 1), (key2737, -1), (key2747, 1), (key2786, 2), (key2794, -1), (key2795, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, 1), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2997, 1), (key2998, 1), (key3000, -2)]

theorem rowCheck6675 : row6675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6675 := by decide +kernel

theorem rowEval6675 (x : Key → ℝ) : Integer.Sparse.eval row6675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6675, Integer.Sparse.eval_collectBalanced, rawRowCheck6675]

def rawRow6676 : Integer.Sparse Key := [(key2998, 1), (key3000, 1), (key2997, -2), (key2897, 1), (key2904, 1), (key2653, -2), (key2747, -2), (key2648, 1), (key2737, 1), (key2893, -2), (key2646, 1), (key2735, 1), (key2976, -1), (key2983, -1), (key2938, 1), (key2950, 1), (key2897, -1), (key2904, -1), (key2653, 1), (key2747, 1), (key2641, 1), (key2728, 1), (key2618, -1), (key2673, -1), (key2782, 1), (key2805, 1), (key2612, -1), (key2667, -1), (key2870, 2), (key2726, -1), (key2829, -1), (key2860, 2), (key2640, -1), (key2794, -1), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, 2), (key2671, 2)]

theorem rawRowCheck6676 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form7 = rawRow6676 := by decide +kernel

def row6676 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6676 : row6676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6676 := by decide +kernel

theorem rowEval6676 (x : Key → ℝ) : Integer.Sparse.eval row6676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6676, Integer.Sparse.eval_collectBalanced, rawRowCheck6676]

def rawRow6677 : Integer.Sparse Key := [(key3000, 1), (key2998, 1), (key2997, -2), (key2904, 1), (key2897, 1), (key2747, -2), (key2653, -2), (key2737, 1), (key2648, 1), (key2893, -2), (key2735, 1), (key2646, 1), (key2983, -1), (key2976, -1), (key2950, 1), (key2938, 1), (key2904, -1), (key2897, -1), (key2747, 1), (key2653, 1), (key2728, 1), (key2641, 1), (key2673, -1), (key2618, -1), (key2805, 1), (key2782, 1), (key2667, -1), (key2612, -1), (key2870, 2), (key2829, -1), (key2726, -1), (key2860, 2), (key2794, -1), (key2640, -1), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, 2), (key2616, 2)]

theorem rawRowCheck6677 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form7 = rawRow6677 := by decide +kernel

def row6677 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, -1), (key2640, -1), (key2641, 1), (key2646, 1), (key2648, 1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2737, 1), (key2747, -1), (key2782, 1), (key2786, -1), (key2794, -1), (key2805, 1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2), (key2893, -2), (key2938, 1), (key2950, 1), (key2976, -1), (key2983, -1), (key2997, -2), (key2998, 1), (key3000, 1)]

theorem rowCheck6677 : row6677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6677 := by decide +kernel

theorem rowEval6677 (x : Key → ℝ) : Integer.Sparse.eval row6677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6677, Integer.Sparse.eval_collectBalanced, rawRowCheck6677]

def rawRow6678 : Integer.Sparse Key := [(key2617, -2), (key2620, 1), (key2620, 1), (key2633, -2), (key2643, 1), (key2643, 1), (key2650, 1), (key2650, 1), (key2655, 1), (key2655, 1), (key2656, -2), (key2656, -2), (key2787, 2), (key2797, -1), (key2797, -1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, 2), (key2915, 2), (key2940, -1), (key2940, -1), (key2946, 1), (key2946, 1), (key2952, -1), (key2952, -1), (key2962, 1), (key2962, 1), (key2985, 1), (key2985, 1), (key2994, -1), (key2994, -1), (key2999, 1), (key2999, 1), (key3004, -1), (key3004, -1)]

theorem rawRowCheck6678 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form8 = rawRow6678 := by decide +kernel

def row6678 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

theorem rowCheck6678 : row6678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6678 := by decide +kernel

theorem rowEval6678 (x : Key → ℝ) : Integer.Sparse.eval row6678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6678, Integer.Sparse.eval_collectBalanced, rawRowCheck6678]

def rawRow6679 : Integer.Sparse Key := [(key2620, -2), (key2617, 1), (key2620, 1), (key2643, -2), (key2633, 1), (key2643, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2656, 1), (key2650, -2), (key2655, -2), (key2797, 2), (key2787, -1), (key2797, -1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, 2), (key2906, 2), (key2945, -1), (key2946, -1), (key2940, 1), (key2945, 1), (key2962, -1), (key2964, -1), (key2952, 1), (key2964, 1), (key2978, 1), (key2994, 1), (key2978, -1), (key2985, -1), (key3001, 1), (key3004, 1), (key2999, -1), (key3001, -1)]

theorem rawRowCheck6679 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form8 = rawRow6679 := by decide +kernel

def row6679 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6679 : row6679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6679 := by decide +kernel

theorem rowEval6679 (x : Key → ℝ) : Integer.Sparse.eval row6679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6679, Integer.Sparse.eval_collectBalanced, rawRowCheck6679]

def rawRow6680 : Integer.Sparse Key := [(key2620, -2), (key2620, 1), (key2617, 1), (key2643, -2), (key2643, 1), (key2633, 1), (key2656, 1), (key2655, 1), (key2656, 1), (key2650, 1), (key2655, -2), (key2650, -2), (key2797, 2), (key2797, -1), (key2787, -1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, 2), (key2899, 2), (key2946, -1), (key2945, -1), (key2945, 1), (key2940, 1), (key2964, -1), (key2962, -1), (key2964, 1), (key2952, 1), (key2994, 1), (key2978, 1), (key2985, -1), (key2978, -1), (key3004, 1), (key3001, 1), (key3001, -1), (key2999, -1)]

theorem rawRowCheck6680 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form8 = rawRow6680 := by decide +kernel

def row6680 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6680 : row6680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6680 := by decide +kernel

theorem rowEval6680 (x : Key → ℝ) : Integer.Sparse.eval row6680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6680, Integer.Sparse.eval_collectBalanced, rawRowCheck6680]

def rawRow6681 : Integer.Sparse Key := [(key2633, -2), (key2643, 1), (key2643, 1), (key2617, -2), (key2655, 1), (key2655, 1), (key2620, 1), (key2620, 1), (key2643, 1), (key2643, 1), (key2656, -2), (key2656, -2), (key2810, 2), (key2899, -1), (key2899, -1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, 2), (key2915, 2), (key2952, -1), (key2952, -1), (key2999, 1), (key2999, 1), (key2940, -1), (key2940, -1), (key2985, 1), (key2985, 1), (key2962, 1), (key2962, 1), (key3004, -1), (key3004, -1), (key2946, 1), (key2946, 1), (key2994, -1), (key2994, -1)]

theorem rawRowCheck6681 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form8 = rawRow6681 := by decide +kernel

def row6681 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 4), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

theorem rowCheck6681 : row6681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6681 := by decide +kernel

theorem rowEval6681 (x : Key → ℝ) : Integer.Sparse.eval row6681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6681, Integer.Sparse.eval_collectBalanced, rawRowCheck6681]

def rawRow6682 : Integer.Sparse Key := [(key2643, -2), (key2633, 1), (key2643, 1), (key2655, -2), (key2617, 1), (key2655, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2656, 1), (key2620, -2), (key2643, -2), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, 2), (key2833, 2), (key2978, -1), (key2999, -1), (key2952, 1), (key2978, 1), (key2985, -1), (key3001, -1), (key2940, 1), (key3001, 1), (key2945, 1), (key3004, 1), (key2945, -1), (key2962, -1), (key2964, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

theorem rawRowCheck6682 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form8 = rawRow6682 := by decide +kernel

def row6682 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6682 : row6682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6682 := by decide +kernel

theorem rowEval6682 (x : Key → ℝ) : Integer.Sparse.eval row6682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6682, Integer.Sparse.eval_collectBalanced, rawRowCheck6682]

def rawRow6683 : Integer.Sparse Key := [(key2643, -2), (key2643, 1), (key2633, 1), (key2655, -2), (key2655, 1), (key2617, 1), (key2656, 1), (key2643, 1), (key2656, 1), (key2620, 1), (key2643, -2), (key2620, -2), (key2899, 2), (key2899, -1), (key2810, -1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, 2), (key2797, 2), (key2999, -1), (key2978, -1), (key2978, 1), (key2952, 1), (key3001, -1), (key2985, -1), (key3001, 1), (key2940, 1), (key3004, 1), (key2945, 1), (key2962, -1), (key2945, -1), (key2994, 1), (key2964, 1), (key2964, -1), (key2946, -1)]

theorem rawRowCheck6683 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form8 = rawRow6683 := by decide +kernel

def row6683 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6683 : row6683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6683 := by decide +kernel

theorem rowEval6683 (x : Key → ℝ) : Integer.Sparse.eval row6683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6683, Integer.Sparse.eval_collectBalanced, rawRowCheck6683]

def rawRow6684 : Integer.Sparse Key := [(key2650, -2), (key2655, 1), (key2656, 1), (key2620, -2), (key2643, 1), (key2656, 1), (key2617, 1), (key2620, 1), (key2633, 1), (key2643, 1), (key2650, -2), (key2655, -2), (key2833, 2), (key2906, -1), (key2915, -1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, 2), (key2906, 2), (key2962, -1), (key2964, -1), (key3001, 1), (key3004, 1), (key2945, -1), (key2946, -1), (key2978, 1), (key2994, 1), (key2952, 1), (key2964, 1), (key2999, -1), (key3001, -1), (key2940, 1), (key2945, 1), (key2978, -1), (key2985, -1)]

theorem rawRowCheck6684 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form8 = rawRow6684 := by decide +kernel

def row6684 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, 2), (key2650, -4), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6684 : row6684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6684 := by decide +kernel

theorem rowEval6684 (x : Key → ℝ) : Integer.Sparse.eval row6684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6684, Integer.Sparse.eval_collectBalanced, rawRowCheck6684]

def rawRow6685 : Integer.Sparse Key := [(key2650, -2), (key2656, 1), (key2655, 1), (key2620, -2), (key2656, 1), (key2643, 1), (key2620, 1), (key2617, 1), (key2643, 1), (key2633, 1), (key2655, -2), (key2650, -2), (key2833, 2), (key2915, -1), (key2906, -1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, 2), (key2899, 2), (key2964, -1), (key2962, -1), (key3004, 1), (key3001, 1), (key2946, -1), (key2945, -1), (key2994, 1), (key2978, 1), (key2964, 1), (key2952, 1), (key3001, -1), (key2999, -1), (key2945, 1), (key2940, 1), (key2985, -1), (key2978, -1)]

theorem rawRowCheck6685 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form8 = rawRow6685 := by decide +kernel

def row6685 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, 2), (key2650, -4), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6685 : row6685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6685 := by decide +kernel

theorem rowEval6685 (x : Key → ℝ) : Integer.Sparse.eval row6685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6685, Integer.Sparse.eval_collectBalanced, rawRowCheck6685]

def rawRow6686 : Integer.Sparse Key := [(key2655, -2), (key2650, 1), (key2656, 1), (key2643, -2), (key2620, 1), (key2656, 1), (key2633, 1), (key2643, 1), (key2617, 1), (key2655, 1), (key2620, -2), (key2643, -2), (key2906, 2), (key2833, -1), (key2915, -1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, 2), (key2833, 2), (key2985, -1), (key3001, -1), (key2964, 1), (key2994, 1), (key2978, -1), (key2999, -1), (key2945, 1), (key3004, 1), (key2940, 1), (key3001, 1), (key2946, -1), (key2964, -1), (key2952, 1), (key2978, 1), (key2945, -1), (key2962, -1)]

theorem rawRowCheck6686 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form8 = rawRow6686 := by decide +kernel

def row6686 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -3), (key2650, 1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6686 : row6686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6686 := by decide +kernel

theorem rowEval6686 (x : Key → ℝ) : Integer.Sparse.eval row6686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6686, Integer.Sparse.eval_collectBalanced, rawRowCheck6686]

def rawRow6687 : Integer.Sparse Key := [(key2655, -2), (key2656, 1), (key2650, 1), (key2643, -2), (key2656, 1), (key2620, 1), (key2643, 1), (key2633, 1), (key2655, 1), (key2617, 1), (key2643, -2), (key2620, -2), (key2906, 2), (key2915, -1), (key2833, -1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, 2), (key2797, 2), (key3001, -1), (key2985, -1), (key2994, 1), (key2964, 1), (key2999, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key3001, 1), (key2940, 1), (key2964, -1), (key2946, -1), (key2978, 1), (key2952, 1), (key2962, -1), (key2945, -1)]

theorem rawRowCheck6687 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form8 = rawRow6687 := by decide +kernel

def row6687 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -3), (key2650, 1), (key2655, -1), (key2656, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2946, -1), (key2952, 1), (key2962, -1), (key2985, -1), (key2994, 1), (key2999, -1), (key3004, 1)]

theorem rowCheck6687 : row6687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6687 := by decide +kernel

theorem rowEval6687 (x : Key → ℝ) : Integer.Sparse.eval row6687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6687, Integer.Sparse.eval_collectBalanced, rawRowCheck6687]

def rawRow6688 : Integer.Sparse Key := [(key2656, -2), (key2650, 1), (key2655, 1), (key2656, -2), (key2620, 1), (key2643, 1), (key2650, 1), (key2655, 1), (key2620, 1), (key2643, 1), (key2617, -2), (key2633, -2), (key2915, 2), (key2833, -1), (key2906, -1), (key2915, 2), (key2797, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, 2), (key2810, 2), (key2994, -1), (key3004, -1), (key2962, 1), (key2985, 1), (key2994, -1), (key3004, -1), (key2946, 1), (key2999, 1), (key2946, 1), (key2999, 1), (key2940, -1), (key2952, -1), (key2962, 1), (key2985, 1), (key2940, -1), (key2952, -1)]

theorem rawRowCheck6688 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form8 = rawRow6688 := by decide +kernel

def row6688 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

theorem rowCheck6688 : row6688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6688 := by decide +kernel

theorem rowEval6688 (x : Key → ℝ) : Integer.Sparse.eval row6688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6688, Integer.Sparse.eval_collectBalanced, rawRowCheck6688]

def rawRow6689 : Integer.Sparse Key := [(key2656, -2), (key2655, 1), (key2650, 1), (key2656, -2), (key2643, 1), (key2620, 1), (key2655, 1), (key2650, 1), (key2643, 1), (key2620, 1), (key2633, -2), (key2617, -2), (key2915, 2), (key2906, -1), (key2833, -1), (key2915, 2), (key2899, -1), (key2797, -1), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, 2), (key2787, 2), (key3004, -1), (key2994, -1), (key2985, 1), (key2962, 1), (key3004, -1), (key2994, -1), (key2999, 1), (key2946, 1), (key2999, 1), (key2946, 1), (key2952, -1), (key2940, -1), (key2985, 1), (key2962, 1), (key2952, -1), (key2940, -1)]

theorem rawRowCheck6689 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form8 = rawRow6689 := by decide +kernel

def row6689 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, -2), (key2643, 2), (key2650, 2), (key2655, 2), (key2656, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2946, 2), (key2952, -2), (key2962, 2), (key2985, 2), (key2994, -2), (key2999, 2), (key3004, -2)]

theorem rowCheck6689 : row6689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6689 := by decide +kernel

theorem rowEval6689 (x : Key → ℝ) : Integer.Sparse.eval row6689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6689, Integer.Sparse.eval_collectBalanced, rawRowCheck6689]

def rawRow6690 : Integer.Sparse Key := [(key2787, -2), (key2797, 1), (key2797, 1), (key2810, -2), (key2899, 1), (key2899, 1), (key2833, 1), (key2833, 1), (key2906, 1), (key2906, 1), (key2915, -2), (key2915, -2), (key2617, 2), (key2655, -1), (key2655, -1), (key2672, 2), (key2749, -1), (key2749, -1), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, 2), (key3004, 2), (key2620, -1), (key2620, -1), (key2656, 1), (key2656, 1), (key2675, -1), (key2675, -1), (key2730, 1), (key2730, 1), (key2833, 1), (key2833, 1), (key2915, -1), (key2915, -1), (key2946, 1), (key2946, 1), (key2994, -1), (key2994, -1)]

theorem rawRowCheck6690 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form8 = rawRow6690 := by decide +kernel

def row6690 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

theorem rowCheck6690 : row6690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6690 := by decide +kernel

theorem rowEval6690 (x : Key → ℝ) : Integer.Sparse.eval row6690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6690, Integer.Sparse.eval_collectBalanced, rawRowCheck6690]

def rawRow6691 : Integer.Sparse Key := [(key2797, -2), (key2787, 1), (key2797, 1), (key2899, -2), (key2810, 1), (key2899, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2915, 1), (key2833, -2), (key2906, -2), (key2655, 2), (key2617, -1), (key2655, -1), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, 2), (key2962, 2), (key2643, -1), (key2656, -1), (key2620, 1), (key2643, 1), (key2730, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2797, 1), (key2915, 1), (key2797, -1), (key2833, -1), (key2964, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

theorem rawRowCheck6691 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form8 = rawRow6691 := by decide +kernel

def row6691 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6691 : row6691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6691 := by decide +kernel

theorem rowEval6691 (x : Key → ℝ) : Integer.Sparse.eval row6691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6691, Integer.Sparse.eval_collectBalanced, rawRowCheck6691]

def rawRow6692 : Integer.Sparse Key := [(key2797, -2), (key2797, 1), (key2787, 1), (key2899, -2), (key2899, 1), (key2810, 1), (key2915, 1), (key2906, 1), (key2915, 1), (key2833, 1), (key2906, -2), (key2833, -2), (key2655, 2), (key2655, -1), (key2617, -1), (key2749, 2), (key2749, -1), (key2672, -1), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, 2), (key2945, 2), (key2656, -1), (key2643, -1), (key2643, 1), (key2620, 1), (key2751, -1), (key2730, -1), (key2751, 1), (key2675, 1), (key2915, 1), (key2797, 1), (key2833, -1), (key2797, -1), (key2994, 1), (key2964, 1), (key2964, -1), (key2946, -1)]

theorem rawRowCheck6692 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form8 = rawRow6692 := by decide +kernel

def row6692 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6692 : row6692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6692 := by decide +kernel

theorem rowEval6692 (x : Key → ℝ) : Integer.Sparse.eval row6692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6692, Integer.Sparse.eval_collectBalanced, rawRowCheck6692]

def rawRow6693 : Integer.Sparse Key := [(key2810, -2), (key2833, 1), (key2833, 1), (key2787, -2), (key2906, 1), (key2906, 1), (key2797, 1), (key2797, 1), (key2899, 1), (key2899, 1), (key2915, -2), (key2915, -2), (key2672, 2), (key2749, -1), (key2749, -1), (key2617, 2), (key2962, -1), (key2962, -1), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, 2), (key3004, 2), (key2675, -1), (key2675, -1), (key2946, 1), (key2946, 1), (key2620, -1), (key2620, -1), (key2833, 1), (key2833, 1), (key2730, 1), (key2730, 1), (key2994, -1), (key2994, -1), (key2656, 1), (key2656, 1), (key2915, -1), (key2915, -1)]

theorem rawRowCheck6693 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form8 = rawRow6693 := by decide +kernel

def row6693 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -4), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

theorem rowCheck6693 : row6693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6693 := by decide +kernel

theorem rowEval6693 (x : Key → ℝ) : Integer.Sparse.eval row6693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6693, Integer.Sparse.eval_collectBalanced, rawRowCheck6693]

def rawRow6694 : Integer.Sparse Key := [(key2833, -2), (key2810, 1), (key2833, 1), (key2906, -2), (key2787, 1), (key2906, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2915, 1), (key2797, -2), (key2899, -2), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, 2), (key2617, -1), (key2962, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, 2), (key2749, 2), (key2797, -1), (key2946, -1), (key2675, 1), (key2797, 1), (key2833, -1), (key2964, -1), (key2620, 1), (key2964, 1), (key2643, 1), (key2994, 1), (key2643, -1), (key2730, -1), (key2751, 1), (key2915, 1), (key2656, -1), (key2751, -1)]

theorem rawRowCheck6694 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form8 = rawRow6694 := by decide +kernel

def row6694 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6694 : row6694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6694 := by decide +kernel

theorem rowEval6694 (x : Key → ℝ) : Integer.Sparse.eval row6694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6694, Integer.Sparse.eval_collectBalanced, rawRowCheck6694]

def rawRow6695 : Integer.Sparse Key := [(key2833, -2), (key2833, 1), (key2810, 1), (key2906, -2), (key2906, 1), (key2787, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2797, 1), (key2899, -2), (key2797, -2), (key2749, 2), (key2749, -1), (key2672, -1), (key2962, 2), (key2962, -1), (key2617, -1), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, 2), (key2655, 2), (key2946, -1), (key2797, -1), (key2797, 1), (key2675, 1), (key2964, -1), (key2833, -1), (key2964, 1), (key2620, 1), (key2994, 1), (key2643, 1), (key2730, -1), (key2643, -1), (key2915, 1), (key2751, 1), (key2751, -1), (key2656, -1)]

theorem rawRowCheck6695 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form8 = rawRow6695 := by decide +kernel

def row6695 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6695 : row6695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6695 := by decide +kernel

theorem rowEval6695 (x : Key → ℝ) : Integer.Sparse.eval row6695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6695, Integer.Sparse.eval_collectBalanced, rawRowCheck6695]

def rawRow6696 : Integer.Sparse Key := [(key2899, -2), (key2906, 1), (key2915, 1), (key2797, -2), (key2833, 1), (key2915, 1), (key2787, 1), (key2797, 1), (key2810, 1), (key2899, 1), (key2833, -2), (key2906, -2), (key2945, 2), (key2962, -1), (key3004, -1), (key2655, 2), (key2749, -1), (key3004, -1), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, 2), (key2962, 2), (key2730, -1), (key2751, -1), (key2964, 1), (key2994, 1), (key2643, -1), (key2656, -1), (key2797, 1), (key2915, 1), (key2675, 1), (key2751, 1), (key2946, -1), (key2964, -1), (key2620, 1), (key2643, 1), (key2797, -1), (key2833, -1)]

theorem rawRowCheck6696 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form8 = rawRow6696 := by decide +kernel

def row6696 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 4), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6696 : row6696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6696 := by decide +kernel

theorem rowEval6696 (x : Key → ℝ) : Integer.Sparse.eval row6696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6696, Integer.Sparse.eval_collectBalanced, rawRowCheck6696]

def rawRow6697 : Integer.Sparse Key := [(key2899, -2), (key2915, 1), (key2906, 1), (key2797, -2), (key2915, 1), (key2833, 1), (key2797, 1), (key2787, 1), (key2899, 1), (key2810, 1), (key2906, -2), (key2833, -2), (key2945, 2), (key3004, -1), (key2962, -1), (key2655, 2), (key3004, -1), (key2749, -1), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, 2), (key2945, 2), (key2751, -1), (key2730, -1), (key2994, 1), (key2964, 1), (key2656, -1), (key2643, -1), (key2915, 1), (key2797, 1), (key2751, 1), (key2675, 1), (key2964, -1), (key2946, -1), (key2643, 1), (key2620, 1), (key2833, -1), (key2797, -1)]

theorem rawRowCheck6697 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form8 = rawRow6697 := by decide +kernel

def row6697 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, 4), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6697 : row6697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6697 := by decide +kernel

theorem rowEval6697 (x : Key → ℝ) : Integer.Sparse.eval row6697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6697, Integer.Sparse.eval_collectBalanced, rawRowCheck6697]

def rawRow6698 : Integer.Sparse Key := [(key2906, -2), (key2899, 1), (key2915, 1), (key2833, -2), (key2797, 1), (key2915, 1), (key2810, 1), (key2833, 1), (key2787, 1), (key2906, 1), (key2797, -2), (key2899, -2), (key2962, 2), (key2945, -1), (key3004, -1), (key2749, 2), (key2655, -1), (key3004, -1), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, 2), (key2749, 2), (key2833, -1), (key2964, -1), (key2751, 1), (key2915, 1), (key2797, -1), (key2946, -1), (key2643, 1), (key2994, 1), (key2620, 1), (key2964, 1), (key2656, -1), (key2751, -1), (key2675, 1), (key2797, 1), (key2643, -1), (key2730, -1)]

theorem rawRowCheck6698 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form8 = rawRow6698 := by decide +kernel

def row6698 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 3), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, -1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6698 : row6698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6698 := by decide +kernel

theorem rowEval6698 (x : Key → ℝ) : Integer.Sparse.eval row6698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6698, Integer.Sparse.eval_collectBalanced, rawRowCheck6698]

def rawRow6699 : Integer.Sparse Key := [(key2906, -2), (key2915, 1), (key2899, 1), (key2833, -2), (key2915, 1), (key2797, 1), (key2833, 1), (key2810, 1), (key2906, 1), (key2787, 1), (key2899, -2), (key2797, -2), (key2962, 2), (key3004, -1), (key2945, -1), (key2749, 2), (key3004, -1), (key2655, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, 2), (key2655, 2), (key2964, -1), (key2833, -1), (key2915, 1), (key2751, 1), (key2946, -1), (key2797, -1), (key2994, 1), (key2643, 1), (key2964, 1), (key2620, 1), (key2751, -1), (key2656, -1), (key2797, 1), (key2675, 1), (key2730, -1), (key2643, -1)]

theorem rawRowCheck6699 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form8 = rawRow6699 := by decide +kernel

def row6699 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, -1), (key2749, 3), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, -1), (key2915, 3), (key2945, -1), (key2946, -1), (key2962, 1), (key2994, 1), (key3004, -2)]

theorem rowCheck6699 : row6699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6699 := by decide +kernel

theorem rowEval6699 (x : Key → ℝ) : Integer.Sparse.eval row6699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6699, Integer.Sparse.eval_collectBalanced, rawRowCheck6699]

def rawRow6700 : Integer.Sparse Key := [(key2915, -2), (key2899, 1), (key2906, 1), (key2915, -2), (key2797, 1), (key2833, 1), (key2899, 1), (key2906, 1), (key2797, 1), (key2833, 1), (key2787, -2), (key2810, -2), (key3004, 2), (key2945, -1), (key2962, -1), (key3004, 2), (key2655, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, 2), (key2672, 2), (key2915, -1), (key2994, -1), (key2730, 1), (key2833, 1), (key2915, -1), (key2994, -1), (key2656, 1), (key2946, 1), (key2656, 1), (key2946, 1), (key2620, -1), (key2675, -1), (key2730, 1), (key2833, 1), (key2620, -1), (key2675, -1)]

theorem rawRowCheck6700 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form8 = rawRow6700 := by decide +kernel

def row6700 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

theorem rowCheck6700 : row6700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6700 := by decide +kernel

theorem rowEval6700 (x : Key → ℝ) : Integer.Sparse.eval row6700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6700, Integer.Sparse.eval_collectBalanced, rawRowCheck6700]

def rawRow6701 : Integer.Sparse Key := [(key2915, -2), (key2906, 1), (key2899, 1), (key2915, -2), (key2833, 1), (key2797, 1), (key2906, 1), (key2899, 1), (key2833, 1), (key2797, 1), (key2810, -2), (key2787, -2), (key3004, 2), (key2962, -1), (key2945, -1), (key3004, 2), (key2749, -1), (key2655, -1), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, 2), (key2617, 2), (key2994, -1), (key2915, -1), (key2833, 1), (key2730, 1), (key2994, -1), (key2915, -1), (key2946, 1), (key2656, 1), (key2946, 1), (key2656, 1), (key2675, -1), (key2620, -1), (key2833, 1), (key2730, 1), (key2675, -1), (key2620, -1)]

theorem rawRowCheck6701 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form8 = rawRow6701 := by decide +kernel

def row6701 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2655, -2), (key2656, 2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, -2), (key2787, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2906, 2), (key2915, -6), (key2945, -2), (key2946, 2), (key2962, -2), (key2994, -2), (key3004, 4)]

theorem rowCheck6701 : row6701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6701 := by decide +kernel

theorem rowEval6701 (x : Key → ℝ) : Integer.Sparse.eval row6701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6701, Integer.Sparse.eval_collectBalanced, rawRowCheck6701]

def rawRow6702 : Integer.Sparse Key := [(key2940, -2), (key2945, 1), (key2946, 1), (key2952, -2), (key2978, 1), (key2999, 1), (key2962, 1), (key2964, 1), (key2985, 1), (key3001, 1), (key2994, -2), (key3004, -2), (key2620, 2), (key2643, -1), (key2656, -1), (key2675, 2), (key2797, -1), (key2946, -1), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, 2), (key2994, 2), (key2617, -1), (key2620, -1), (key2650, 1), (key2655, 1), (key2672, -1), (key2675, -1), (key2707, 1), (key2730, 1), (key2810, 1), (key2833, 1), (key2899, -1), (key2906, -1), (key2940, 1), (key2945, 1), (key2978, -1), (key2985, -1)]

theorem rawRowCheck6702 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form8 = rawRow6702 := by decide +kernel

def row6702 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 2), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6702 : row6702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6702 := by decide +kernel

theorem rowEval6702 (x : Key → ℝ) : Integer.Sparse.eval row6702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6702, Integer.Sparse.eval_collectBalanced, rawRowCheck6702]

def rawRow6703 : Integer.Sparse Key := [(key2940, -2), (key2946, 1), (key2945, 1), (key2952, -2), (key2999, 1), (key2978, 1), (key2964, 1), (key2962, 1), (key3001, 1), (key2985, 1), (key3004, -2), (key2994, -2), (key2620, 2), (key2656, -1), (key2643, -1), (key2675, 2), (key2946, -1), (key2797, -1), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, 2), (key2915, 2), (key2620, -1), (key2617, -1), (key2655, 1), (key2650, 1), (key2675, -1), (key2672, -1), (key2730, 1), (key2707, 1), (key2833, 1), (key2810, 1), (key2906, -1), (key2899, -1), (key2945, 1), (key2940, 1), (key2985, -1), (key2978, -1)]

theorem rawRowCheck6703 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form8 = rawRow6703 := by decide +kernel

def row6703 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 2), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6703 : row6703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6703 := by decide +kernel

theorem rowEval6703 (x : Key → ℝ) : Integer.Sparse.eval row6703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6703, Integer.Sparse.eval_collectBalanced, rawRowCheck6703]

def rawRow6704 : Integer.Sparse Key := [(key2946, -2), (key2940, 1), (key2945, 1), (key2999, -2), (key2952, 1), (key2978, 1), (key3001, 1), (key3004, 1), (key2964, 1), (key2994, 1), (key2962, -2), (key2985, -2), (key2656, 2), (key2620, -1), (key2643, -1), (key2946, 2), (key2675, -1), (key2797, -1), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, 2), (key2833, 2), (key2650, -1), (key2655, -1), (key2617, 1), (key2633, 1), (key2730, -1), (key2749, -1), (key2675, 1), (key2739, 1), (key2797, 1), (key2899, 1), (key2787, -1), (key2810, -1), (key2962, 1), (key2985, 1), (key2940, -1), (key2952, -1)]

theorem rawRowCheck6704 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form8 = rawRow6704 := by decide +kernel

def row6704 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2749, -1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2915, -1), (key2945, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6704 : row6704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6704 := by decide +kernel

theorem rowEval6704 (x : Key → ℝ) : Integer.Sparse.eval row6704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6704, Integer.Sparse.eval_collectBalanced, rawRowCheck6704]

def rawRow6705 : Integer.Sparse Key := [(key2946, -2), (key2945, 1), (key2940, 1), (key2999, -2), (key2978, 1), (key2952, 1), (key3004, 1), (key3001, 1), (key2994, 1), (key2964, 1), (key2985, -2), (key2962, -2), (key2656, 2), (key2643, -1), (key2620, -1), (key2946, 2), (key2797, -1), (key2675, -1), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, 2), (key2730, 2), (key2655, -1), (key2650, -1), (key2633, 1), (key2617, 1), (key2749, -1), (key2730, -1), (key2739, 1), (key2675, 1), (key2899, 1), (key2797, 1), (key2810, -1), (key2787, -1), (key2985, 1), (key2962, 1), (key2952, -1), (key2940, -1)]

theorem rawRowCheck6705 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form8 = rawRow6705 := by decide +kernel

def row6705 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2749, -1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2915, -1), (key2945, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6705 : row6705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6705 := by decide +kernel

theorem rowEval6705 (x : Key → ℝ) : Integer.Sparse.eval row6705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6705, Integer.Sparse.eval_collectBalanced, rawRowCheck6705]

def rawRow6706 : Integer.Sparse Key := [(key2952, -2), (key2962, 1), (key2964, 1), (key2940, -2), (key2985, 1), (key3001, 1), (key2945, 1), (key2946, 1), (key2978, 1), (key2999, 1), (key2994, -2), (key3004, -2), (key2675, 2), (key2730, -1), (key2751, -1), (key2620, 2), (key2833, -1), (key2964, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, 2), (key2994, 2), (key2672, -1), (key2675, -1), (key2730, 1), (key2749, 1), (key2617, -1), (key2620, -1), (key2810, 1), (key2833, 1), (key2707, 1), (key2730, 1), (key2978, -1), (key2985, -1), (key2650, 1), (key2655, 1), (key2899, -1), (key2906, -1)]

theorem rawRowCheck6706 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form8 = rawRow6706 := by decide +kernel

def row6706 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6706 : row6706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6706 := by decide +kernel

theorem rowEval6706 (x : Key → ℝ) : Integer.Sparse.eval row6706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6706, Integer.Sparse.eval_collectBalanced, rawRowCheck6706]

def rawRow6707 : Integer.Sparse Key := [(key2952, -2), (key2964, 1), (key2962, 1), (key2940, -2), (key3001, 1), (key2985, 1), (key2946, 1), (key2945, 1), (key2999, 1), (key2978, 1), (key3004, -2), (key2994, -2), (key2675, 2), (key2751, -1), (key2730, -1), (key2620, 2), (key2964, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, 2), (key2915, 2), (key2675, -1), (key2672, -1), (key2749, 1), (key2730, 1), (key2620, -1), (key2617, -1), (key2833, 1), (key2810, 1), (key2730, 1), (key2707, 1), (key2985, -1), (key2978, -1), (key2655, 1), (key2650, 1), (key2906, -1), (key2899, -1)]

theorem rawRowCheck6707 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form8 = rawRow6707 := by decide +kernel

def row6707 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2643, -1), (key2650, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6707 : row6707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6707 := by decide +kernel

theorem rowEval6707 (x : Key → ℝ) : Integer.Sparse.eval row6707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6707, Integer.Sparse.eval_collectBalanced, rawRowCheck6707]

def rawRow6708 : Integer.Sparse Key := [(key2962, -2), (key2952, 1), (key2964, 1), (key2985, -2), (key2940, 1), (key3001, 1), (key2978, 1), (key2994, 1), (key2945, 1), (key3004, 1), (key2946, -2), (key2999, -2), (key2730, 2), (key2675, -1), (key2751, -1), (key2833, 2), (key2620, -1), (key2964, -1), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, 2), (key2946, 2), (key2707, -1), (key2730, -1), (key2675, 1), (key2739, 1), (key2810, -1), (key2833, -1), (key2617, 1), (key2962, 1), (key2633, 1), (key2985, 1), (key2643, -1), (key2730, -1), (key2739, 1), (key2899, 1), (key2655, -1), (key2749, -1)]

theorem rawRowCheck6708 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form8 = rawRow6708 := by decide +kernel

def row6708 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2739, 2), (key2749, -1), (key2751, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6708 : row6708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6708 := by decide +kernel

theorem rowEval6708 (x : Key → ℝ) : Integer.Sparse.eval row6708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6708, Integer.Sparse.eval_collectBalanced, rawRowCheck6708]

def rawRow6709 : Integer.Sparse Key := [(key2962, -2), (key2964, 1), (key2952, 1), (key2985, -2), (key3001, 1), (key2940, 1), (key2994, 1), (key2978, 1), (key3004, 1), (key2945, 1), (key2999, -2), (key2946, -2), (key2730, 2), (key2751, -1), (key2675, -1), (key2833, 2), (key2964, -1), (key2620, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, 2), (key2656, 2), (key2730, -1), (key2707, -1), (key2739, 1), (key2675, 1), (key2833, -1), (key2810, -1), (key2962, 1), (key2617, 1), (key2985, 1), (key2633, 1), (key2730, -1), (key2643, -1), (key2899, 1), (key2739, 1), (key2749, -1), (key2655, -1)]

theorem rawRowCheck6709 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form8 = rawRow6709 := by decide +kernel

def row6709 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2739, 2), (key2749, -1), (key2751, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6709 : row6709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6709 := by decide +kernel

theorem rowEval6709 (x : Key → ℝ) : Integer.Sparse.eval row6709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6709, Integer.Sparse.eval_collectBalanced, rawRowCheck6709]

def rawRow6710 : Integer.Sparse Key := [(key2985, -2), (key2978, 1), (key2994, 1), (key2962, -2), (key2945, 1), (key3004, 1), (key2952, 1), (key2964, 1), (key2940, 1), (key3001, 1), (key2946, -2), (key2999, -2), (key2833, 2), (key2797, -1), (key2915, -1), (key2730, 2), (key2643, -1), (key2994, -1), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, 2), (key2946, 2), (key2810, -1), (key2833, -1), (key2797, 1), (key2899, 1), (key2707, -1), (key2730, -1), (key2633, 1), (key2985, 1), (key2617, 1), (key2962, 1), (key2655, -1), (key2749, -1), (key2675, 1), (key2797, 1), (key2643, -1), (key2730, -1)]

theorem rawRowCheck6710 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form8 = rawRow6710 := by decide +kernel

def row6710 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2749, -1), (key2751, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6710 : row6710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6710 := by decide +kernel

theorem rowEval6710 (x : Key → ℝ) : Integer.Sparse.eval row6710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6710, Integer.Sparse.eval_collectBalanced, rawRowCheck6710]

def rawRow6711 : Integer.Sparse Key := [(key2985, -2), (key2994, 1), (key2978, 1), (key2962, -2), (key3004, 1), (key2945, 1), (key2964, 1), (key2952, 1), (key3001, 1), (key2940, 1), (key2999, -2), (key2946, -2), (key2833, 2), (key2915, -1), (key2797, -1), (key2730, 2), (key2994, -1), (key2643, -1), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, 2), (key2656, 2), (key2833, -1), (key2810, -1), (key2899, 1), (key2797, 1), (key2730, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key2962, 1), (key2617, 1), (key2749, -1), (key2655, -1), (key2797, 1), (key2675, 1), (key2730, -1), (key2643, -1)]

theorem rawRowCheck6711 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form8 = rawRow6711 := by decide +kernel

def row6711 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -2), (key2655, -1), (key2656, 2), (key2707, -1), (key2749, -1), (key2751, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2940, 1), (key2945, 1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6711 : row6711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6711 := by decide +kernel

theorem rowEval6711 (x : Key → ℝ) : Integer.Sparse.eval row6711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6711, Integer.Sparse.eval_collectBalanced, rawRowCheck6711]

def rawRow6712 : Integer.Sparse Key := [(key2994, -2), (key2978, 1), (key2985, 1), (key3004, -2), (key2945, 1), (key2962, 1), (key2999, 1), (key3001, 1), (key2946, 1), (key2964, 1), (key2940, -2), (key2952, -2), (key2915, 2), (key2797, -1), (key2833, -1), (key2994, 2), (key2643, -1), (key2730, -1), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, 2), (key2675, 2), (key2899, -1), (key2906, -1), (key2787, 1), (key2810, 1), (key2978, -1), (key2985, -1), (key2643, 1), (key2730, 1), (key2655, 1), (key2749, 1), (key2617, -1), (key2672, -1), (key2730, 1), (key2833, 1), (key2620, -1), (key2675, -1)]

theorem rawRowCheck6712 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form8 = rawRow6712 := by decide +kernel

def row6712 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6712 : row6712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6712 := by decide +kernel

theorem rowEval6712 (x : Key → ℝ) : Integer.Sparse.eval row6712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6712, Integer.Sparse.eval_collectBalanced, rawRowCheck6712]

def rawRow6713 : Integer.Sparse Key := [(key2994, -2), (key2985, 1), (key2978, 1), (key3004, -2), (key2962, 1), (key2945, 1), (key3001, 1), (key2999, 1), (key2964, 1), (key2946, 1), (key2952, -2), (key2940, -2), (key2915, 2), (key2833, -1), (key2797, -1), (key2994, 2), (key2730, -1), (key2643, -1), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, 2), (key2620, 2), (key2906, -1), (key2899, -1), (key2810, 1), (key2787, 1), (key2985, -1), (key2978, -1), (key2730, 1), (key2643, 1), (key2749, 1), (key2655, 1), (key2672, -1), (key2617, -1), (key2833, 1), (key2730, 1), (key2675, -1), (key2620, -1)]

theorem rawRowCheck6713 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form8 = rawRow6713 := by decide +kernel

def row6713 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2730, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -2), (key2945, 1), (key2952, -2), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6713 : row6713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6713 := by decide +kernel

theorem rowEval6713 (x : Key → ℝ) : Integer.Sparse.eval row6713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6713, Integer.Sparse.eval_collectBalanced, rawRowCheck6713]

def rawRow6714 : Integer.Sparse Key := [(key2999, -2), (key3001, 1), (key3004, 1), (key2946, -2), (key2964, 1), (key2994, 1), (key2940, 1), (key2945, 1), (key2952, 1), (key2978, 1), (key2962, -2), (key2985, -2), (key2946, 2), (key2964, -1), (key2994, -1), (key2656, 2), (key2751, -1), (key2915, -1), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, 2), (key2833, 2), (key2940, -1), (key2945, -1), (key2962, 1), (key2985, 1), (key2650, -1), (key2655, -1), (key2739, 1), (key2899, 1), (key2675, 1), (key2797, 1), (key2730, -1), (key2833, -1), (key2617, 1), (key2633, 1), (key2787, -1), (key2810, -1)]

theorem rawRowCheck6714 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form8 = rawRow6714 := by decide +kernel

def row6714 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6714 : row6714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6714 := by decide +kernel

theorem rowEval6714 (x : Key → ℝ) : Integer.Sparse.eval row6714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form8) x := by
  rw [rowCheck6714, Integer.Sparse.eval_collectBalanced, rawRowCheck6714]

def rawRow6715 : Integer.Sparse Key := [(key2999, -2), (key3004, 1), (key3001, 1), (key2946, -2), (key2994, 1), (key2964, 1), (key2945, 1), (key2940, 1), (key2978, 1), (key2952, 1), (key2985, -2), (key2962, -2), (key2946, 2), (key2994, -1), (key2964, -1), (key2656, 2), (key2915, -1), (key2751, -1), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, 2), (key2730, 2), (key2945, -1), (key2940, -1), (key2985, 1), (key2962, 1), (key2655, -1), (key2650, -1), (key2899, 1), (key2739, 1), (key2797, 1), (key2675, 1), (key2833, -1), (key2730, -1), (key2633, 1), (key2617, 1), (key2810, -1), (key2787, -1)]

theorem rawRowCheck6715 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form8 = rawRow6715 := by decide +kernel

def row6715 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, 1), (key2643, -1), (key2650, -1), (key2655, -1), (key2656, 2), (key2730, 1), (key2739, 1), (key2751, -1), (key2787, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2915, -1), (key2952, 1), (key2962, -1), (key2978, 1), (key2985, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6715 : row6715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6715 := by decide +kernel

theorem rowEval6715 (x : Key → ℝ) : Integer.Sparse.eval row6715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6715, Integer.Sparse.eval_collectBalanced, rawRowCheck6715]

def rawRow6716 : Integer.Sparse Key := [(key3004, -2), (key2999, 1), (key3001, 1), (key2994, -2), (key2946, 1), (key2964, 1), (key2978, 1), (key2985, 1), (key2945, 1), (key2962, 1), (key2940, -2), (key2952, -2), (key2994, 2), (key2946, -1), (key2964, -1), (key2915, 2), (key2656, -1), (key2751, -1), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, 2), (key2675, 2), (key2978, -1), (key2985, -1), (key2940, 1), (key2952, 1), (key2899, -1), (key2906, -1), (key2655, 1), (key2749, 1), (key2643, 1), (key2730, 1), (key2620, -1), (key2675, -1), (key2787, 1), (key2810, 1), (key2617, -1), (key2672, -1)]

theorem rawRowCheck6716 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form8 = rawRow6716 := by decide +kernel

def row6716 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 1), (key2952, -1), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6716 : row6716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6716 := by decide +kernel

theorem rowEval6716 (x : Key → ℝ) : Integer.Sparse.eval row6716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form8) x := by
  rw [rowCheck6716, Integer.Sparse.eval_collectBalanced, rawRowCheck6716]

def rawRow6717 : Integer.Sparse Key := [(key3004, -2), (key3001, 1), (key2999, 1), (key2994, -2), (key2964, 1), (key2946, 1), (key2985, 1), (key2978, 1), (key2962, 1), (key2945, 1), (key2952, -2), (key2940, -2), (key2994, 2), (key2964, -1), (key2946, -1), (key2915, 2), (key2751, -1), (key2656, -1), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, 2), (key2620, 2), (key2985, -1), (key2978, -1), (key2952, 1), (key2940, 1), (key2906, -1), (key2899, -1), (key2749, 1), (key2655, 1), (key2730, 1), (key2643, 1), (key2675, -1), (key2620, -1), (key2810, 1), (key2787, 1), (key2672, -1), (key2617, -1)]

theorem rawRowCheck6717 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form8 = rawRow6717 := by decide +kernel

def row6717 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2655, 1), (key2656, -1), (key2672, -1), (key2675, 1), (key2749, 1), (key2751, -1), (key2787, 1), (key2797, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2906, -1), (key2915, 2), (key2940, -1), (key2945, 1), (key2952, -1), (key2962, 1), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck6717 : row6717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6717 := by decide +kernel

theorem rowEval6717 (x : Key → ℝ) : Integer.Sparse.eval row6717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form8) x := by
  rw [rowCheck6717, Integer.Sparse.eval_collectBalanced, rawRowCheck6717]

def rawRow6718 : Integer.Sparse Key := [(key2031, -1), (key2036, -1), (key2036, 2), (key2061, -1), (key2066, -1), (key2061, 2), (key2071, 2), (key2066, -1), (key2071, -1), (key2093, 2), (key2093, -1), (key2096, -1), (key2031, 1), (key2036, 1), (key2036, -2), (key2150, 1), (key2155, 1), (key2150, -2), (key2168, -2), (key2155, 1), (key2168, 1), (key2195, -2), (key2195, 1), (key2201, 1), (key2061, -1), (key2071, -1), (key2066, 1), (key2071, 1), (key2150, 1), (key2168, 1), (key2155, -1), (key2168, -1), (key2243, -1), (key2248, -1), (key2243, 1), (key2255, 1), (key2304, 1), (key2306, 1), (key2304, -1), (key2311, -1)]

theorem rawRowCheck6718 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow6718 := by decide +kernel

def row6718 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6718 : row6718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6718 := by decide +kernel

theorem rowEval6718 (x : Key → ℝ) : Integer.Sparse.eval row6718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6718, Integer.Sparse.eval_collectBalanced, rawRowCheck6718]

def rawRow6719 : Integer.Sparse Key := [(key2036, -1), (key2031, -1), (key2036, 2), (key2066, -1), (key2061, -1), (key2071, 2), (key2061, 2), (key2071, -1), (key2066, -1), (key2093, 2), (key2096, -1), (key2093, -1), (key2036, 1), (key2031, 1), (key2036, -2), (key2155, 1), (key2150, 1), (key2168, -2), (key2150, -2), (key2168, 1), (key2155, 1), (key2195, -2), (key2201, 1), (key2195, 1), (key2071, -1), (key2061, -1), (key2071, 1), (key2066, 1), (key2168, 1), (key2150, 1), (key2168, -1), (key2155, -1), (key2248, -1), (key2243, -1), (key2255, 1), (key2243, 1), (key2306, 1), (key2304, 1), (key2311, -1), (key2304, -1)]

theorem rawRowCheck6719 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow6719 := by decide +kernel

def row6719 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6719 : row6719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6719 := by decide +kernel

theorem rowEval6719 (x : Key → ℝ) : Integer.Sparse.eval row6719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6719, Integer.Sparse.eval_collectBalanced, rawRowCheck6719]

def rawRow6720 : Integer.Sparse Key := [(key2036, -1), (key2036, -1), (key2031, 2), (key2071, -1), (key2071, -1), (key2066, 2), (key2066, 2), (key2061, -1), (key2061, -1), (key2096, 2), (key2093, -1), (key2093, -1), (key2036, 1), (key2036, 1), (key2031, -2), (key2168, 1), (key2168, 1), (key2155, -2), (key2155, -2), (key2150, 1), (key2150, 1), (key2201, -2), (key2195, 1), (key2195, 1), (key2066, -1), (key2066, -1), (key2061, 1), (key2061, 1), (key2155, 1), (key2155, 1), (key2150, -1), (key2150, -1), (key2255, -1), (key2255, -1), (key2248, 1), (key2248, 1), (key2311, 1), (key2311, 1), (key2306, -1), (key2306, -1)]

theorem rawRowCheck6720 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow6720 := by decide +kernel

def row6720 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6720 : row6720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6720 := by decide +kernel

theorem rowEval6720 (x : Key → ℝ) : Integer.Sparse.eval row6720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6720, Integer.Sparse.eval_collectBalanced, rawRowCheck6720]

def rawRow6721 : Integer.Sparse Key := [(key2061, -1), (key2066, -1), (key2093, 2), (key2031, -1), (key2036, -1), (key2061, 2), (key2071, 2), (key2093, -1), (key2096, -1), (key2036, 2), (key2066, -1), (key2071, -1), (key2150, 1), (key2155, 1), (key2195, -2), (key2031, 1), (key2036, 1), (key2150, -2), (key2168, -2), (key2195, 1), (key2201, 1), (key2036, -2), (key2155, 1), (key2168, 1), (key2243, -1), (key2248, -1), (key2304, 1), (key2306, 1), (key2243, 1), (key2255, 1), (key2304, -1), (key2311, -1), (key2061, -1), (key2071, -1), (key2150, 1), (key2168, 1), (key2066, 1), (key2071, 1), (key2155, -1), (key2168, -1)]

theorem rawRowCheck6721 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form0 = rawRow6721 := by decide +kernel

def row6721 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6721 : row6721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6721 := by decide +kernel

theorem rowEval6721 (x : Key → ℝ) : Integer.Sparse.eval row6721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6721, Integer.Sparse.eval_collectBalanced, rawRowCheck6721]

def rawRow6722 : Integer.Sparse Key := [(key2066, -1), (key2061, -1), (key2093, 2), (key2036, -1), (key2031, -1), (key2071, 2), (key2061, 2), (key2096, -1), (key2093, -1), (key2036, 2), (key2071, -1), (key2066, -1), (key2155, 1), (key2150, 1), (key2195, -2), (key2036, 1), (key2031, 1), (key2168, -2), (key2150, -2), (key2201, 1), (key2195, 1), (key2036, -2), (key2168, 1), (key2155, 1), (key2248, -1), (key2243, -1), (key2306, 1), (key2304, 1), (key2255, 1), (key2243, 1), (key2311, -1), (key2304, -1), (key2071, -1), (key2061, -1), (key2168, 1), (key2150, 1), (key2071, 1), (key2066, 1), (key2168, -1), (key2155, -1)]

theorem rawRowCheck6722 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form0 = rawRow6722 := by decide +kernel

def row6722 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6722 : row6722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6722 := by decide +kernel

theorem rowEval6722 (x : Key → ℝ) : Integer.Sparse.eval row6722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6722, Integer.Sparse.eval_collectBalanced, rawRowCheck6722]

def rawRow6723 : Integer.Sparse Key := [(key2061, -1), (key2093, -1), (key2066, 2), (key2061, -1), (key2093, -1), (key2031, 2), (key2096, 2), (key2036, -1), (key2071, -1), (key2066, 2), (key2036, -1), (key2071, -1), (key2150, 1), (key2195, 1), (key2155, -2), (key2150, 1), (key2195, 1), (key2031, -2), (key2201, -2), (key2036, 1), (key2168, 1), (key2155, -2), (key2036, 1), (key2168, 1), (key2150, -1), (key2306, -1), (key2155, 1), (key2248, 1), (key2061, 1), (key2311, 1), (key2066, -1), (key2255, -1), (key2150, -1), (key2306, -1), (key2061, 1), (key2311, 1), (key2155, 1), (key2248, 1), (key2066, -1), (key2255, -1)]

theorem rawRowCheck6723 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form0 = rawRow6723 := by decide +kernel

def row6723 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6723 : row6723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6723 := by decide +kernel

theorem rowEval6723 (x : Key → ℝ) : Integer.Sparse.eval row6723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6723, Integer.Sparse.eval_collectBalanced, rawRowCheck6723]

def rawRow6724 : Integer.Sparse Key := [(key2093, -1), (key2061, -1), (key2066, 2), (key2093, -1), (key2061, -1), (key2096, 2), (key2031, 2), (key2071, -1), (key2036, -1), (key2066, 2), (key2071, -1), (key2036, -1), (key2195, 1), (key2150, 1), (key2155, -2), (key2195, 1), (key2150, 1), (key2201, -2), (key2031, -2), (key2168, 1), (key2036, 1), (key2155, -2), (key2168, 1), (key2036, 1), (key2306, -1), (key2150, -1), (key2248, 1), (key2155, 1), (key2311, 1), (key2061, 1), (key2255, -1), (key2066, -1), (key2306, -1), (key2150, -1), (key2311, 1), (key2061, 1), (key2248, 1), (key2155, 1), (key2255, -1), (key2066, -1)]

theorem rawRowCheck6724 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form0 = rawRow6724 := by decide +kernel

def row6724 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6724 : row6724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6724 := by decide +kernel

theorem rowEval6724 (x : Key → ℝ) : Integer.Sparse.eval row6724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6724, Integer.Sparse.eval_collectBalanced, rawRowCheck6724]

def rawRow6725 : Integer.Sparse Key := [(key2066, -1), (key2093, -1), (key2061, 2), (key2071, -1), (key2096, -1), (key2036, 2), (key2093, 2), (key2031, -1), (key2061, -1), (key2071, 2), (key2036, -1), (key2066, -1), (key2155, 1), (key2195, 1), (key2150, -2), (key2168, 1), (key2201, 1), (key2036, -2), (key2195, -2), (key2031, 1), (key2150, 1), (key2168, -2), (key2036, 1), (key2155, 1), (key2155, -1), (key2304, -1), (key2150, 1), (key2243, 1), (key2066, 1), (key2304, 1), (key2061, -1), (key2243, -1), (key2168, -1), (key2311, -1), (key2071, 1), (key2306, 1), (key2168, 1), (key2255, 1), (key2071, -1), (key2248, -1)]

theorem rawRowCheck6725 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form0 = rawRow6725 := by decide +kernel

def row6725 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6725 : row6725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6725 := by decide +kernel

theorem rowEval6725 (x : Key → ℝ) : Integer.Sparse.eval row6725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6725, Integer.Sparse.eval_collectBalanced, rawRowCheck6725]

def rawRow6726 : Integer.Sparse Key := [(key2093, -1), (key2066, -1), (key2061, 2), (key2096, -1), (key2071, -1), (key2093, 2), (key2036, 2), (key2061, -1), (key2031, -1), (key2071, 2), (key2066, -1), (key2036, -1), (key2195, 1), (key2155, 1), (key2150, -2), (key2201, 1), (key2168, 1), (key2195, -2), (key2036, -2), (key2150, 1), (key2031, 1), (key2168, -2), (key2155, 1), (key2036, 1), (key2304, -1), (key2155, -1), (key2243, 1), (key2150, 1), (key2304, 1), (key2066, 1), (key2243, -1), (key2061, -1), (key2311, -1), (key2168, -1), (key2306, 1), (key2071, 1), (key2255, 1), (key2168, 1), (key2248, -1), (key2071, -1)]

theorem rawRowCheck6726 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form0 = rawRow6726 := by decide +kernel

def row6726 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6726 : row6726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6726 := by decide +kernel

theorem rowEval6726 (x : Key → ℝ) : Integer.Sparse.eval row6726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6726, Integer.Sparse.eval_collectBalanced, rawRowCheck6726]

def rawRow6727 : Integer.Sparse Key := [(key2071, -1), (key2071, -1), (key2096, 2), (key2036, -1), (key2036, -1), (key2066, 2), (key2066, 2), (key2093, -1), (key2093, -1), (key2031, 2), (key2061, -1), (key2061, -1), (key2168, 1), (key2168, 1), (key2201, -2), (key2036, 1), (key2036, 1), (key2155, -2), (key2155, -2), (key2195, 1), (key2195, 1), (key2031, -2), (key2150, 1), (key2150, 1), (key2255, -1), (key2255, -1), (key2311, 1), (key2311, 1), (key2248, 1), (key2248, 1), (key2306, -1), (key2306, -1), (key2066, -1), (key2066, -1), (key2155, 1), (key2155, 1), (key2061, 1), (key2061, 1), (key2150, -1), (key2150, -1)]

theorem rawRowCheck6727 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form0 = rawRow6727 := by decide +kernel

def row6727 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6727 : row6727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6727 := by decide +kernel

theorem rowEval6727 (x : Key → ℝ) : Integer.Sparse.eval row6727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6727, Integer.Sparse.eval_collectBalanced, rawRowCheck6727]

def rawRow6728 : Integer.Sparse Key := [(key2071, -1), (key2096, -1), (key2071, 2), (key2066, -1), (key2093, -1), (key2036, 2), (key2093, 2), (key2036, -1), (key2066, -1), (key2061, 2), (key2031, -1), (key2061, -1), (key2168, 1), (key2201, 1), (key2168, -2), (key2155, 1), (key2195, 1), (key2036, -2), (key2195, -2), (key2036, 1), (key2155, 1), (key2150, -2), (key2031, 1), (key2150, 1), (key2168, -1), (key2311, -1), (key2168, 1), (key2255, 1), (key2071, 1), (key2306, 1), (key2071, -1), (key2248, -1), (key2155, -1), (key2304, -1), (key2066, 1), (key2304, 1), (key2150, 1), (key2243, 1), (key2061, -1), (key2243, -1)]

theorem rawRowCheck6728 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form0 = rawRow6728 := by decide +kernel

def row6728 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6728 : row6728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6728 := by decide +kernel

theorem rowEval6728 (x : Key → ℝ) : Integer.Sparse.eval row6728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6728, Integer.Sparse.eval_collectBalanced, rawRowCheck6728]

def rawRow6729 : Integer.Sparse Key := [(key2096, -1), (key2071, -1), (key2071, 2), (key2093, -1), (key2066, -1), (key2093, 2), (key2036, 2), (key2066, -1), (key2036, -1), (key2061, 2), (key2061, -1), (key2031, -1), (key2201, 1), (key2168, 1), (key2168, -2), (key2195, 1), (key2155, 1), (key2195, -2), (key2036, -2), (key2155, 1), (key2036, 1), (key2150, -2), (key2150, 1), (key2031, 1), (key2311, -1), (key2168, -1), (key2255, 1), (key2168, 1), (key2306, 1), (key2071, 1), (key2248, -1), (key2071, -1), (key2304, -1), (key2155, -1), (key2304, 1), (key2066, 1), (key2243, 1), (key2150, 1), (key2243, -1), (key2061, -1)]

theorem rawRowCheck6729 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form0 = rawRow6729 := by decide +kernel

def row6729 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6729 : row6729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6729 := by decide +kernel

theorem rowEval6729 (x : Key → ℝ) : Integer.Sparse.eval row6729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6729, Integer.Sparse.eval_collectBalanced, rawRowCheck6729]

def rawRow6730 : Integer.Sparse Key := [(key2150, -1), (key2155, -1), (key2195, 2), (key2150, -1), (key2155, -1), (key2243, 2), (key2248, 2), (key2304, -1), (key2306, -1), (key2195, 2), (key2304, -1), (key2306, -1), (key2061, 1), (key2066, 1), (key2093, -2), (key2061, 1), (key2066, 1), (key2243, -2), (key2255, -2), (key2304, 1), (key2311, 1), (key2093, -2), (key2304, 1), (key2311, 1), (key2061, -1), (key2071, -1), (key2093, 1), (key2096, 1), (key2150, 1), (key2168, 1), (key2195, -1), (key2201, -1), (key2061, -1), (key2071, -1), (key2150, 1), (key2168, 1), (key2093, 1), (key2096, 1), (key2195, -1), (key2201, -1)]

theorem rawRowCheck6730 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form0 = rawRow6730 := by decide +kernel

def row6730 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6730 : row6730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6730 := by decide +kernel

theorem rowEval6730 (x : Key → ℝ) : Integer.Sparse.eval row6730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6730, Integer.Sparse.eval_collectBalanced, rawRowCheck6730]

def rawRow6731 : Integer.Sparse Key := [(key2155, -1), (key2150, -1), (key2195, 2), (key2155, -1), (key2150, -1), (key2248, 2), (key2243, 2), (key2306, -1), (key2304, -1), (key2195, 2), (key2306, -1), (key2304, -1), (key2066, 1), (key2061, 1), (key2093, -2), (key2066, 1), (key2061, 1), (key2255, -2), (key2243, -2), (key2311, 1), (key2304, 1), (key2093, -2), (key2311, 1), (key2304, 1), (key2071, -1), (key2061, -1), (key2096, 1), (key2093, 1), (key2168, 1), (key2150, 1), (key2201, -1), (key2195, -1), (key2071, -1), (key2061, -1), (key2168, 1), (key2150, 1), (key2096, 1), (key2093, 1), (key2201, -1), (key2195, -1)]

theorem rawRowCheck6731 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form0 = rawRow6731 := by decide +kernel

def row6731 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6731 : row6731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6731 := by decide +kernel

theorem rowEval6731 (x : Key → ℝ) : Integer.Sparse.eval row6731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6731, Integer.Sparse.eval_collectBalanced, rawRowCheck6731]

def rawRow6732 : Integer.Sparse Key := [(key2150, -1), (key2195, -1), (key2155, 2), (key2243, -1), (key2304, -1), (key2150, 2), (key2306, 2), (key2155, -1), (key2248, -1), (key2304, 2), (key2195, -1), (key2306, -1), (key2061, 1), (key2093, 1), (key2066, -2), (key2243, 1), (key2304, 1), (key2061, -2), (key2311, -2), (key2066, 1), (key2255, 1), (key2304, -2), (key2093, 1), (key2311, 1), (key2031, -1), (key2096, -1), (key2036, 1), (key2071, 1), (key2031, 1), (key2201, 1), (key2036, -1), (key2168, -1), (key2150, -1), (key2306, -1), (key2061, 1), (key2311, 1), (key2195, 1), (key2306, 1), (key2093, -1), (key2311, -1)]

theorem rawRowCheck6732 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form0 = rawRow6732 := by decide +kernel

def row6732 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6732 : row6732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6732 := by decide +kernel

theorem rowEval6732 (x : Key → ℝ) : Integer.Sparse.eval row6732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6732, Integer.Sparse.eval_collectBalanced, rawRowCheck6732]

def rawRow6733 : Integer.Sparse Key := [(key2195, -1), (key2150, -1), (key2155, 2), (key2304, -1), (key2243, -1), (key2306, 2), (key2150, 2), (key2248, -1), (key2155, -1), (key2304, 2), (key2306, -1), (key2195, -1), (key2093, 1), (key2061, 1), (key2066, -2), (key2304, 1), (key2243, 1), (key2311, -2), (key2061, -2), (key2255, 1), (key2066, 1), (key2304, -2), (key2311, 1), (key2093, 1), (key2096, -1), (key2031, -1), (key2071, 1), (key2036, 1), (key2201, 1), (key2031, 1), (key2168, -1), (key2036, -1), (key2306, -1), (key2150, -1), (key2311, 1), (key2061, 1), (key2306, 1), (key2195, 1), (key2311, -1), (key2093, -1)]

theorem rawRowCheck6733 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form0 = rawRow6733 := by decide +kernel

def row6733 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6733 : row6733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6733 := by decide +kernel

theorem rowEval6733 (x : Key → ℝ) : Integer.Sparse.eval row6733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6733, Integer.Sparse.eval_collectBalanced, rawRowCheck6733]

def rawRow6734 : Integer.Sparse Key := [(key2155, -1), (key2195, -1), (key2150, 2), (key2248, -1), (key2306, -1), (key2155, 2), (key2304, 2), (key2150, -1), (key2243, -1), (key2306, 2), (key2195, -1), (key2304, -1), (key2066, 1), (key2093, 1), (key2061, -2), (key2255, 1), (key2311, 1), (key2066, -2), (key2304, -2), (key2061, 1), (key2243, 1), (key2311, -2), (key2093, 1), (key2304, 1), (key2036, -1), (key2093, -1), (key2031, 1), (key2061, 1), (key2036, 1), (key2195, 1), (key2031, -1), (key2150, -1), (key2168, -1), (key2311, -1), (key2071, 1), (key2306, 1), (key2201, 1), (key2311, 1), (key2096, -1), (key2306, -1)]

theorem rawRowCheck6734 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form0 = rawRow6734 := by decide +kernel

def row6734 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6734 : row6734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6734 := by decide +kernel

theorem rowEval6734 (x : Key → ℝ) : Integer.Sparse.eval row6734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6734, Integer.Sparse.eval_collectBalanced, rawRowCheck6734]

def rawRow6735 : Integer.Sparse Key := [(key2195, -1), (key2155, -1), (key2150, 2), (key2306, -1), (key2248, -1), (key2304, 2), (key2155, 2), (key2243, -1), (key2150, -1), (key2306, 2), (key2304, -1), (key2195, -1), (key2093, 1), (key2066, 1), (key2061, -2), (key2311, 1), (key2255, 1), (key2304, -2), (key2066, -2), (key2243, 1), (key2061, 1), (key2311, -2), (key2304, 1), (key2093, 1), (key2093, -1), (key2036, -1), (key2061, 1), (key2031, 1), (key2195, 1), (key2036, 1), (key2150, -1), (key2031, -1), (key2311, -1), (key2168, -1), (key2306, 1), (key2071, 1), (key2311, 1), (key2201, 1), (key2306, -1), (key2096, -1)]

theorem rawRowCheck6735 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form0 = rawRow6735 := by decide +kernel

def row6735 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6735 : row6735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6735 := by decide +kernel

theorem rowEval6735 (x : Key → ℝ) : Integer.Sparse.eval row6735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6735, Integer.Sparse.eval_collectBalanced, rawRowCheck6735]

def rawRow6736 : Integer.Sparse Key := [(key2243, -1), (key2304, -1), (key2304, 2), (key2150, -1), (key2195, -1), (key2150, 2), (key2306, 2), (key2195, -1), (key2306, -1), (key2155, 2), (key2155, -1), (key2248, -1), (key2243, 1), (key2304, 1), (key2304, -2), (key2061, 1), (key2093, 1), (key2061, -2), (key2311, -2), (key2093, 1), (key2311, 1), (key2066, -2), (key2066, 1), (key2255, 1), (key2150, -1), (key2306, -1), (key2195, 1), (key2306, 1), (key2061, 1), (key2311, 1), (key2093, -1), (key2311, -1), (key2031, -1), (key2096, -1), (key2031, 1), (key2201, 1), (key2036, 1), (key2071, 1), (key2036, -1), (key2168, -1)]

theorem rawRowCheck6736 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form0 = rawRow6736 := by decide +kernel

def row6736 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6736 : row6736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6736 := by decide +kernel

theorem rowEval6736 (x : Key → ℝ) : Integer.Sparse.eval row6736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6736, Integer.Sparse.eval_collectBalanced, rawRowCheck6736]

def rawRow6737 : Integer.Sparse Key := [(key2304, -1), (key2243, -1), (key2304, 2), (key2195, -1), (key2150, -1), (key2306, 2), (key2150, 2), (key2306, -1), (key2195, -1), (key2155, 2), (key2248, -1), (key2155, -1), (key2304, 1), (key2243, 1), (key2304, -2), (key2093, 1), (key2061, 1), (key2311, -2), (key2061, -2), (key2311, 1), (key2093, 1), (key2066, -2), (key2255, 1), (key2066, 1), (key2306, -1), (key2150, -1), (key2306, 1), (key2195, 1), (key2311, 1), (key2061, 1), (key2311, -1), (key2093, -1), (key2096, -1), (key2031, -1), (key2201, 1), (key2031, 1), (key2071, 1), (key2036, 1), (key2168, -1), (key2036, -1)]

theorem rawRowCheck6737 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form0 = rawRow6737 := by decide +kernel

def row6737 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6737 : row6737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6737 := by decide +kernel

theorem rowEval6737 (x : Key → ℝ) : Integer.Sparse.eval row6737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6737, Integer.Sparse.eval_collectBalanced, rawRowCheck6737]

def rawRow6738 : Integer.Sparse Key := [(key2304, -1), (key2304, -1), (key2243, 2), (key2306, -1), (key2306, -1), (key2195, 2), (key2195, 2), (key2150, -1), (key2150, -1), (key2248, 2), (key2155, -1), (key2155, -1), (key2304, 1), (key2304, 1), (key2243, -2), (key2311, 1), (key2311, 1), (key2093, -2), (key2093, -2), (key2061, 1), (key2061, 1), (key2255, -2), (key2066, 1), (key2066, 1), (key2195, -1), (key2195, -1), (key2150, 1), (key2150, 1), (key2093, 1), (key2093, 1), (key2061, -1), (key2061, -1), (key2201, -1), (key2201, -1), (key2096, 1), (key2096, 1), (key2168, 1), (key2168, 1), (key2071, -1), (key2071, -1)]

theorem rawRowCheck6738 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form0 = rawRow6738 := by decide +kernel

def row6738 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6738 : row6738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6738 := by decide +kernel

theorem rowEval6738 (x : Key → ℝ) : Integer.Sparse.eval row6738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6738, Integer.Sparse.eval_collectBalanced, rawRowCheck6738]

def rawRow6739 : Integer.Sparse Key := [(key2248, -1), (key2306, -1), (key2306, 2), (key2155, -1), (key2195, -1), (key2155, 2), (key2304, 2), (key2195, -1), (key2304, -1), (key2150, 2), (key2150, -1), (key2243, -1), (key2255, 1), (key2311, 1), (key2311, -2), (key2066, 1), (key2093, 1), (key2066, -2), (key2304, -2), (key2093, 1), (key2304, 1), (key2061, -2), (key2061, 1), (key2243, 1), (key2168, -1), (key2311, -1), (key2201, 1), (key2311, 1), (key2071, 1), (key2306, 1), (key2096, -1), (key2306, -1), (key2036, -1), (key2093, -1), (key2036, 1), (key2195, 1), (key2031, 1), (key2061, 1), (key2031, -1), (key2150, -1)]

theorem rawRowCheck6739 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form0 = rawRow6739 := by decide +kernel

def row6739 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6739 : row6739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6739 := by decide +kernel

theorem rowEval6739 (x : Key → ℝ) : Integer.Sparse.eval row6739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6739, Integer.Sparse.eval_collectBalanced, rawRowCheck6739]

def rawRow6740 : Integer.Sparse Key := [(key2306, -1), (key2248, -1), (key2306, 2), (key2195, -1), (key2155, -1), (key2304, 2), (key2155, 2), (key2304, -1), (key2195, -1), (key2150, 2), (key2243, -1), (key2150, -1), (key2311, 1), (key2255, 1), (key2311, -2), (key2093, 1), (key2066, 1), (key2304, -2), (key2066, -2), (key2304, 1), (key2093, 1), (key2061, -2), (key2243, 1), (key2061, 1), (key2311, -1), (key2168, -1), (key2311, 1), (key2201, 1), (key2306, 1), (key2071, 1), (key2306, -1), (key2096, -1), (key2093, -1), (key2036, -1), (key2195, 1), (key2036, 1), (key2061, 1), (key2031, 1), (key2150, -1), (key2031, -1)]

theorem rawRowCheck6740 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form0 = rawRow6740 := by decide +kernel

def row6740 : Integer.Sparse Key := [(key2066, -1), (key2071, 1), (key2093, 1), (key2096, -1), (key2155, 1), (key2168, -1), (key2195, -1), (key2201, 1), (key2248, -1), (key2255, 1), (key2306, 1), (key2311, -1)]

theorem rowCheck6740 : row6740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6740 := by decide +kernel

theorem rowEval6740 (x : Key → ℝ) : Integer.Sparse.eval row6740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6740, Integer.Sparse.eval_collectBalanced, rawRowCheck6740]

def rawRow6741 : Integer.Sparse Key := [(key2306, -1), (key2306, -1), (key2248, 2), (key2304, -1), (key2304, -1), (key2195, 2), (key2195, 2), (key2155, -1), (key2155, -1), (key2243, 2), (key2150, -1), (key2150, -1), (key2311, 1), (key2311, 1), (key2255, -2), (key2304, 1), (key2304, 1), (key2093, -2), (key2093, -2), (key2066, 1), (key2066, 1), (key2243, -2), (key2061, 1), (key2061, 1), (key2201, -1), (key2201, -1), (key2168, 1), (key2168, 1), (key2096, 1), (key2096, 1), (key2071, -1), (key2071, -1), (key2195, -1), (key2195, -1), (key2093, 1), (key2093, 1), (key2150, 1), (key2150, 1), (key2061, -1), (key2061, -1)]

theorem rawRowCheck6741 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form0 = rawRow6741 := by decide +kernel

def row6741 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6741 : row6741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6741 := by decide +kernel

theorem rowEval6741 (x : Key → ℝ) : Integer.Sparse.eval row6741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6741, Integer.Sparse.eval_collectBalanced, rawRowCheck6741]

def rawRow6742 : Integer.Sparse Key := [(key2168, -1), (key2168, -1), (key2201, 2), (key2168, -1), (key2168, -1), (key2255, 2), (key2255, 2), (key2311, -1), (key2311, -1), (key2201, 2), (key2311, -1), (key2311, -1), (key2071, 1), (key2071, 1), (key2096, -2), (key2071, 1), (key2071, 1), (key2248, -2), (key2248, -2), (key2306, 1), (key2306, 1), (key2096, -2), (key2306, 1), (key2306, 1), (key2066, -1), (key2066, -1), (key2093, 1), (key2093, 1), (key2155, 1), (key2155, 1), (key2195, -1), (key2195, -1), (key2066, -1), (key2066, -1), (key2155, 1), (key2155, 1), (key2093, 1), (key2093, 1), (key2195, -1), (key2195, -1)]

theorem rawRowCheck6742 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form0 = rawRow6742 := by decide +kernel

def row6742 : Integer.Sparse Key := [(key2066, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2155, 4), (key2168, -4), (key2195, -4), (key2201, 4), (key2248, -4), (key2255, 4), (key2306, 4), (key2311, -4)]

theorem rowCheck6742 : row6742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6742 := by decide +kernel

theorem rowEval6742 (x : Key → ℝ) : Integer.Sparse.eval row6742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6742, Integer.Sparse.eval_collectBalanced, rawRowCheck6742]

def rawRow6743 : Integer.Sparse Key := [(key2168, -1), (key2201, -1), (key2168, 2), (key2255, -1), (key2311, -1), (key2168, 2), (key2311, 2), (key2168, -1), (key2255, -1), (key2311, 2), (key2201, -1), (key2311, -1), (key2071, 1), (key2096, 1), (key2071, -2), (key2248, 1), (key2306, 1), (key2071, -2), (key2306, -2), (key2071, 1), (key2248, 1), (key2306, -2), (key2096, 1), (key2306, 1), (key2036, -1), (key2093, -1), (key2036, 1), (key2066, 1), (key2036, 1), (key2195, 1), (key2036, -1), (key2155, -1), (key2155, -1), (key2304, -1), (key2066, 1), (key2304, 1), (key2195, 1), (key2304, 1), (key2093, -1), (key2304, -1)]

theorem rawRowCheck6743 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form0 = rawRow6743 := by decide +kernel

def row6743 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6743 : row6743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6743 := by decide +kernel

theorem rowEval6743 (x : Key → ℝ) : Integer.Sparse.eval row6743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6743, Integer.Sparse.eval_collectBalanced, rawRowCheck6743]

def rawRow6744 : Integer.Sparse Key := [(key2201, -1), (key2168, -1), (key2168, 2), (key2311, -1), (key2255, -1), (key2311, 2), (key2168, 2), (key2255, -1), (key2168, -1), (key2311, 2), (key2311, -1), (key2201, -1), (key2096, 1), (key2071, 1), (key2071, -2), (key2306, 1), (key2248, 1), (key2306, -2), (key2071, -2), (key2248, 1), (key2071, 1), (key2306, -2), (key2306, 1), (key2096, 1), (key2093, -1), (key2036, -1), (key2066, 1), (key2036, 1), (key2195, 1), (key2036, 1), (key2155, -1), (key2036, -1), (key2304, -1), (key2155, -1), (key2304, 1), (key2066, 1), (key2304, 1), (key2195, 1), (key2304, -1), (key2093, -1)]

theorem rawRowCheck6744 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form0 = rawRow6744 := by decide +kernel

def row6744 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6744 : row6744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6744 := by decide +kernel

theorem rowEval6744 (x : Key → ℝ) : Integer.Sparse.eval row6744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6744, Integer.Sparse.eval_collectBalanced, rawRowCheck6744]

def rawRow6745 : Integer.Sparse Key := [(key2255, -1), (key2311, -1), (key2311, 2), (key2168, -1), (key2201, -1), (key2168, 2), (key2311, 2), (key2201, -1), (key2311, -1), (key2168, 2), (key2168, -1), (key2255, -1), (key2248, 1), (key2306, 1), (key2306, -2), (key2071, 1), (key2096, 1), (key2071, -2), (key2306, -2), (key2096, 1), (key2306, 1), (key2071, -2), (key2071, 1), (key2248, 1), (key2155, -1), (key2304, -1), (key2195, 1), (key2304, 1), (key2066, 1), (key2304, 1), (key2093, -1), (key2304, -1), (key2036, -1), (key2093, -1), (key2036, 1), (key2195, 1), (key2036, 1), (key2066, 1), (key2036, -1), (key2155, -1)]

theorem rawRowCheck6745 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form0 = rawRow6745 := by decide +kernel

def row6745 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6745 : row6745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6745 := by decide +kernel

theorem rowEval6745 (x : Key → ℝ) : Integer.Sparse.eval row6745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6745, Integer.Sparse.eval_collectBalanced, rawRowCheck6745]

def rawRow6746 : Integer.Sparse Key := [(key2311, -1), (key2255, -1), (key2311, 2), (key2201, -1), (key2168, -1), (key2311, 2), (key2168, 2), (key2311, -1), (key2201, -1), (key2168, 2), (key2255, -1), (key2168, -1), (key2306, 1), (key2248, 1), (key2306, -2), (key2096, 1), (key2071, 1), (key2306, -2), (key2071, -2), (key2306, 1), (key2096, 1), (key2071, -2), (key2248, 1), (key2071, 1), (key2304, -1), (key2155, -1), (key2304, 1), (key2195, 1), (key2304, 1), (key2066, 1), (key2304, -1), (key2093, -1), (key2093, -1), (key2036, -1), (key2195, 1), (key2036, 1), (key2066, 1), (key2036, 1), (key2155, -1), (key2036, -1)]

theorem rawRowCheck6746 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form0 = rawRow6746 := by decide +kernel

def row6746 : Integer.Sparse Key := [(key2066, 2), (key2071, -2), (key2093, -2), (key2096, 2), (key2155, -2), (key2168, 2), (key2195, 2), (key2201, -2), (key2248, 2), (key2255, -2), (key2306, -2), (key2311, 2)]

theorem rowCheck6746 : row6746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6746 := by decide +kernel

theorem rowEval6746 (x : Key → ℝ) : Integer.Sparse.eval row6746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6746, Integer.Sparse.eval_collectBalanced, rawRowCheck6746]

def rawRow6747 : Integer.Sparse Key := [(key2311, -1), (key2311, -1), (key2255, 2), (key2311, -1), (key2311, -1), (key2201, 2), (key2201, 2), (key2168, -1), (key2168, -1), (key2255, 2), (key2168, -1), (key2168, -1), (key2306, 1), (key2306, 1), (key2248, -2), (key2306, 1), (key2306, 1), (key2096, -2), (key2096, -2), (key2071, 1), (key2071, 1), (key2248, -2), (key2071, 1), (key2071, 1), (key2195, -1), (key2195, -1), (key2155, 1), (key2155, 1), (key2093, 1), (key2093, 1), (key2066, -1), (key2066, -1), (key2195, -1), (key2195, -1), (key2093, 1), (key2093, 1), (key2155, 1), (key2155, 1), (key2066, -1), (key2066, -1)]

theorem rawRowCheck6747 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form0 = rawRow6747 := by decide +kernel

def row6747 : Integer.Sparse Key := [(key2066, -4), (key2071, 4), (key2093, 4), (key2096, -4), (key2155, 4), (key2168, -4), (key2195, -4), (key2201, 4), (key2248, -4), (key2255, 4), (key2306, 4), (key2311, -4)]

theorem rowCheck6747 : row6747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6747 := by decide +kernel

theorem rowEval6747 (x : Key → ℝ) : Integer.Sparse.eval row6747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6747, Integer.Sparse.eval_collectBalanced, rawRowCheck6747]

def rawRow6748 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key313, 2), (key324, -1), (key325, -1), (key324, 2), (key339, 2), (key325, -1), (key339, -1), (key329, 2), (key329, -1), (key341, -1), (key312, 1), (key313, 1), (key313, -2), (key794, 1), (key796, 1), (key794, -2), (key815, -2), (key796, 1), (key815, 1), (key832, -2), (key832, 1), (key841, 1), (key728, -1), (key736, -1), (key730, 1), (key736, 1), (key794, 1), (key815, 1), (key796, -1), (key815, -1), (key864, -1), (key870, -1), (key864, 1), (key880, 1), (key926, 1), (key929, 1), (key926, -1), (key936, -1)]

theorem rawRowCheck6748 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow6748 := by decide +kernel

def row6748 : Integer.Sparse Key := [(key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key728, -1), (key730, 1), (key796, 1), (key815, -1), (key832, -1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6748 : row6748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6748 := by decide +kernel

theorem rowEval6748 (x : Key → ℝ) : Integer.Sparse.eval row6748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6748, Integer.Sparse.eval_collectBalanced, rawRowCheck6748]

def rawRow6749 : Integer.Sparse Key := [(key313, -1), (key312, -1), (key313, 2), (key325, -1), (key324, -1), (key339, 2), (key324, 2), (key339, -1), (key325, -1), (key329, 2), (key341, -1), (key329, -1), (key313, 1), (key312, 1), (key313, -2), (key796, 1), (key794, 1), (key815, -2), (key794, -2), (key815, 1), (key796, 1), (key832, -2), (key841, 1), (key832, 1), (key736, -1), (key728, -1), (key736, 1), (key730, 1), (key815, 1), (key794, 1), (key815, -1), (key796, -1), (key870, -1), (key864, -1), (key880, 1), (key864, 1), (key929, 1), (key926, 1), (key936, -1), (key926, -1)]

theorem rawRowCheck6749 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow6749 := by decide +kernel

def row6749 : Integer.Sparse Key := [(key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key728, -1), (key730, 1), (key796, 1), (key815, -1), (key832, -1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6749 : row6749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6749 := by decide +kernel

theorem rowEval6749 (x : Key → ℝ) : Integer.Sparse.eval row6749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6749, Integer.Sparse.eval_collectBalanced, rawRowCheck6749]

def rawRow6750 : Integer.Sparse Key := [(key313, -1), (key313, -1), (key312, 2), (key339, -1), (key339, -1), (key325, 2), (key325, 2), (key324, -1), (key324, -1), (key341, 2), (key329, -1), (key329, -1), (key313, 1), (key313, 1), (key312, -2), (key815, 1), (key815, 1), (key796, -2), (key796, -2), (key794, 1), (key794, 1), (key841, -2), (key832, 1), (key832, 1), (key730, -1), (key730, -1), (key728, 1), (key728, 1), (key796, 1), (key796, 1), (key794, -1), (key794, -1), (key880, -1), (key880, -1), (key870, 1), (key870, 1), (key936, 1), (key936, 1), (key929, -1), (key929, -1)]

theorem rawRowCheck6750 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow6750 := by decide +kernel

def row6750 : Integer.Sparse Key := [(key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key728, 2), (key730, -2), (key796, -2), (key815, 2), (key832, 2), (key841, -2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

theorem rowCheck6750 : row6750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6750 := by decide +kernel

theorem rowEval6750 (x : Key → ℝ) : Integer.Sparse.eval row6750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6750, Integer.Sparse.eval_collectBalanced, rawRowCheck6750]

def rawRow6751 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 2), (key312, -1), (key313, -1), (key324, 2), (key339, 2), (key329, -1), (key341, -1), (key313, 2), (key325, -1), (key339, -1), (key414, 1), (key415, 1), (key419, -2), (key312, 1), (key313, 1), (key794, -2), (key815, -2), (key832, 1), (key841, 1), (key727, -2), (key796, 1), (key815, 1), (key864, -1), (key870, -1), (key926, 1), (key929, 1), (key864, 1), (key880, 1), (key926, -1), (key936, -1), (key728, -1), (key736, -1), (key794, 1), (key815, 1), (key730, 1), (key736, 1), (key796, -1), (key815, -1)]

theorem rawRowCheck6751 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form1 = rawRow6751 := by decide +kernel

def row6751 : Integer.Sparse Key := [(key313, 2), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key727, -2), (key728, -1), (key730, 1), (key794, -1), (key815, -1), (key832, 1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6751 : row6751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6751 := by decide +kernel

theorem rowEval6751 (x : Key → ℝ) : Integer.Sparse.eval row6751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6751, Integer.Sparse.eval_collectBalanced, rawRowCheck6751]

def rawRow6752 : Integer.Sparse Key := [(key325, -1), (key324, -1), (key329, 2), (key313, -1), (key312, -1), (key339, 2), (key324, 2), (key341, -1), (key329, -1), (key313, 2), (key339, -1), (key325, -1), (key415, 1), (key414, 1), (key419, -2), (key313, 1), (key312, 1), (key815, -2), (key794, -2), (key841, 1), (key832, 1), (key727, -2), (key815, 1), (key796, 1), (key870, -1), (key864, -1), (key929, 1), (key926, 1), (key880, 1), (key864, 1), (key936, -1), (key926, -1), (key736, -1), (key728, -1), (key815, 1), (key794, 1), (key736, 1), (key730, 1), (key815, -1), (key796, -1)]

theorem rawRowCheck6752 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form1 = rawRow6752 := by decide +kernel

def row6752 : Integer.Sparse Key := [(key313, 2), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key727, -2), (key728, -1), (key730, 1), (key794, -1), (key815, -1), (key832, 1), (key841, 1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6752 : row6752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6752 := by decide +kernel

theorem rowEval6752 (x : Key → ℝ) : Integer.Sparse.eval row6752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6752, Integer.Sparse.eval_collectBalanced, rawRowCheck6752]

def rawRow6753 : Integer.Sparse Key := [(key324, -1), (key329, -1), (key325, 2), (key324, -1), (key329, -1), (key312, 2), (key341, 2), (key313, -1), (key339, -1), (key325, 2), (key313, -1), (key339, -1), (key414, 1), (key419, 1), (key415, -2), (key414, 1), (key419, 1), (key312, -2), (key841, -2), (key727, 1), (key815, 1), (key796, -2), (key727, 1), (key815, 1), (key794, -1), (key929, -1), (key796, 1), (key870, 1), (key728, 1), (key936, 1), (key730, -1), (key880, -1), (key794, -1), (key929, -1), (key728, 1), (key936, 1), (key796, 1), (key870, 1), (key730, -1), (key880, -1)]

theorem rawRowCheck6753 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form1 = rawRow6753 := by decide +kernel

def row6753 : Integer.Sparse Key := [(key313, -2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key414, 2), (key415, -2), (key419, 2), (key727, 2), (key728, 2), (key730, -2), (key794, -2), (key815, 2), (key841, -2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

theorem rowCheck6753 : row6753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6753 := by decide +kernel

theorem rowEval6753 (x : Key → ℝ) : Integer.Sparse.eval row6753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6753, Integer.Sparse.eval_collectBalanced, rawRowCheck6753]

def rawRow6754 : Integer.Sparse Key := [(key329, -1), (key324, -1), (key325, 2), (key329, -1), (key324, -1), (key341, 2), (key312, 2), (key339, -1), (key313, -1), (key325, 2), (key339, -1), (key313, -1), (key419, 1), (key414, 1), (key415, -2), (key419, 1), (key414, 1), (key584, -2), (key725, -2), (key815, 1), (key727, 1), (key796, -2), (key815, 1), (key727, 1), (key929, -1), (key794, -1), (key870, 1), (key796, 1), (key936, 1), (key728, 1), (key880, -1), (key730, -1), (key929, -1), (key794, -1), (key936, 1), (key728, 1), (key870, 1), (key796, 1), (key880, -1), (key730, -1)]

theorem rawRowCheck6754 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form1 = rawRow6754 := by decide +kernel

def row6754 : Integer.Sparse Key := [(key312, 2), (key313, -2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key414, 2), (key415, -2), (key419, 2), (key584, -2), (key725, -2), (key727, 2), (key728, 2), (key730, -2), (key794, -2), (key815, 2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

theorem rowCheck6754 : row6754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6754 := by decide +kernel

theorem rowEval6754 (x : Key → ℝ) : Integer.Sparse.eval row6754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6754, Integer.Sparse.eval_collectBalanced, rawRowCheck6754]

def rawRow6755 : Integer.Sparse Key := [(key325, -1), (key329, -1), (key324, 2), (key339, -1), (key341, -1), (key313, 2), (key329, 2), (key312, -1), (key324, -1), (key339, 2), (key313, -1), (key325, -1), (key415, 1), (key419, 1), (key414, -2), (key582, 1), (key584, 1), (key313, -2), (key419, -2), (key725, 1), (key794, 1), (key815, -2), (key727, 1), (key796, 1), (key796, -1), (key926, -1), (key794, 1), (key864, 1), (key730, 1), (key926, 1), (key728, -1), (key864, -1), (key815, -1), (key936, -1), (key736, 1), (key929, 1), (key815, 1), (key880, 1), (key736, -1), (key870, -1)]

theorem rawRowCheck6755 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form1 = rawRow6755 := by decide +kernel

def row6755 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, -2), (key415, 1), (key419, -1), (key582, 1), (key584, 1), (key725, 1), (key727, 1), (key728, -1), (key730, 1), (key794, 2), (key815, -2), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6755 : row6755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6755 := by decide +kernel

theorem rowEval6755 (x : Key → ℝ) : Integer.Sparse.eval row6755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6755, Integer.Sparse.eval_collectBalanced, rawRowCheck6755]

def rawRow6756 : Integer.Sparse Key := [(key329, -1), (key325, -1), (key324, 2), (key341, -1), (key339, -1), (key329, 2), (key313, 2), (key324, -1), (key312, -1), (key339, 2), (key325, -1), (key313, -1), (key419, 1), (key415, 1), (key414, -2), (key584, 1), (key582, 1), (key419, -2), (key313, -2), (key794, 1), (key725, 1), (key815, -2), (key796, 1), (key727, 1), (key926, -1), (key796, -1), (key864, 1), (key794, 1), (key926, 1), (key730, 1), (key864, -1), (key728, -1), (key936, -1), (key815, -1), (key929, 1), (key736, 1), (key880, 1), (key815, 1), (key870, -1), (key736, -1)]

theorem rawRowCheck6756 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form1 = rawRow6756 := by decide +kernel

def row6756 : Integer.Sparse Key := [(key312, -1), (key313, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key414, -2), (key415, 1), (key419, -1), (key582, 1), (key584, 1), (key725, 1), (key727, 1), (key728, -1), (key730, 1), (key794, 2), (key815, -2), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6756 : row6756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6756 := by decide +kernel

theorem rowEval6756 (x : Key → ℝ) : Integer.Sparse.eval row6756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6756, Integer.Sparse.eval_collectBalanced, rawRowCheck6756]

def rawRow6757 : Integer.Sparse Key := [(key339, -1), (key339, -1), (key341, 2), (key313, -1), (key313, -1), (key325, 2), (key325, 2), (key329, -1), (key329, -1), (key312, 2), (key324, -1), (key324, -1), (key582, 1), (key582, 1), (key584, -2), (key313, 1), (key313, 1), (key415, -2), (key415, -2), (key419, 1), (key419, 1), (key725, -2), (key794, 1), (key794, 1), (key880, -1), (key880, -1), (key936, 1), (key936, 1), (key870, 1), (key870, 1), (key929, -1), (key929, -1), (key730, -1), (key730, -1), (key796, 1), (key796, 1), (key728, 1), (key728, 1), (key794, -1), (key794, -1)]

theorem rawRowCheck6757 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow6757 := by decide +kernel

def row6757 : Integer.Sparse Key := [(key312, 2), (key324, -2), (key325, 4), (key329, -2), (key339, -2), (key341, 2), (key415, -4), (key419, 2), (key582, 2), (key584, -2), (key725, -2), (key728, 2), (key730, -2), (key796, 2), (key870, 2), (key880, -2), (key929, -2), (key936, 2)]

theorem rowCheck6757 : row6757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6757 := by decide +kernel

theorem rowEval6757 (x : Key → ℝ) : Integer.Sparse.eval row6757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6757, Integer.Sparse.eval_collectBalanced, rawRowCheck6757]

def rawRow6758 : Integer.Sparse Key := [(key339, -1), (key341, -1), (key339, 2), (key325, -1), (key329, -1), (key313, 2), (key329, 2), (key313, -1), (key325, -1), (key324, 2), (key312, -1), (key324, -1), (key582, 1), (key584, 1), (key582, -2), (key415, 1), (key419, 1), (key313, -2), (key419, -2), (key313, 1), (key415, 1), (key794, -2), (key725, 1), (key794, 1), (key815, -1), (key936, -1), (key815, 1), (key880, 1), (key736, 1), (key929, 1), (key736, -1), (key870, -1), (key796, -1), (key926, -1), (key730, 1), (key926, 1), (key794, 1), (key864, 1), (key728, -1), (key864, -1)]

theorem rawRowCheck6758 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow6758 := by decide +kernel

def row6758 : Integer.Sparse Key := [(key312, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key415, 2), (key419, -1), (key582, -1), (key584, 1), (key725, 1), (key728, -1), (key730, 1), (key796, -1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6758 : row6758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6758 := by decide +kernel

theorem rowEval6758 (x : Key → ℝ) : Integer.Sparse.eval row6758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6758, Integer.Sparse.eval_collectBalanced, rawRowCheck6758]

def rawRow6759 : Integer.Sparse Key := [(key341, -1), (key339, -1), (key339, 2), (key329, -1), (key325, -1), (key329, 2), (key313, 2), (key325, -1), (key313, -1), (key324, 2), (key324, -1), (key312, -1), (key584, 1), (key582, 1), (key582, -2), (key419, 1), (key415, 1), (key419, -2), (key313, -2), (key415, 1), (key313, 1), (key794, -2), (key794, 1), (key725, 1), (key936, -1), (key815, -1), (key880, 1), (key815, 1), (key929, 1), (key736, 1), (key870, -1), (key736, -1), (key926, -1), (key796, -1), (key926, 1), (key730, 1), (key864, 1), (key794, 1), (key864, -1), (key728, -1)]

theorem rawRowCheck6759 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow6759 := by decide +kernel

def row6759 : Integer.Sparse Key := [(key312, -1), (key324, 1), (key325, -2), (key329, 1), (key339, 1), (key341, -1), (key415, 2), (key419, -1), (key582, -1), (key584, 1), (key725, 1), (key728, -1), (key730, 1), (key796, -1), (key870, -1), (key880, 1), (key929, 1), (key936, -1)]

theorem rowCheck6759 : row6759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6759 := by decide +kernel

theorem rowEval6759 (x : Key → ℝ) : Integer.Sparse.eval row6759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6759, Integer.Sparse.eval_collectBalanced, rawRowCheck6759]

def rawRow6760 : Integer.Sparse Key := [(key414, -1), (key415, -1), (key419, 2), (key414, -1), (key415, -1), (key447, 2), (key474, 2), (key451, -1), (key476, -1), (key419, 2), (key451, -1), (key476, -1), (key324, 1), (key325, 1), (key329, -2), (key324, 1), (key325, 1), (key447, -2), (key600, -2), (key451, 1), (key602, 1), (key329, -2), (key451, 1), (key602, 1), (key324, -1), (key339, -1), (key329, 1), (key341, 1), (key794, 1), (key815, 1), (key832, -1), (key841, -1), (key728, -1), (key736, -1), (key794, 1), (key815, 1), (key748, 1), (key752, 1), (key832, -1), (key841, -1)]

theorem rawRowCheck6760 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form1 = rawRow6760 := by decide +kernel

def row6760 : Integer.Sparse Key := [(key324, 1), (key325, 2), (key329, -3), (key339, -1), (key341, 1), (key414, -2), (key415, -2), (key419, 4), (key474, 2), (key476, -2), (key600, -2), (key602, 2), (key728, -1), (key736, -1), (key748, 1), (key752, 1), (key794, 2), (key815, 2), (key832, -2), (key841, -2)]

theorem rowCheck6760 : row6760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6760 := by decide +kernel

theorem rowEval6760 (x : Key → ℝ) : Integer.Sparse.eval row6760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6760, Integer.Sparse.eval_collectBalanced, rawRowCheck6760]

def rawRow6761 : Integer.Sparse Key := [(key415, -1), (key414, -1), (key419, 2), (key415, -1), (key414, -1), (key474, 2), (key447, 2), (key476, -1), (key451, -1), (key419, 2), (key476, -1), (key451, -1), (key325, 1), (key324, 1), (key329, -2), (key325, 1), (key324, 1), (key600, -2), (key447, -2), (key602, 1), (key451, 1), (key329, -2), (key602, 1), (key451, 1), (key339, -1), (key324, -1), (key341, 1), (key329, 1), (key815, 1), (key794, 1), (key841, -1), (key832, -1), (key736, -1), (key728, -1), (key815, 1), (key794, 1), (key752, 1), (key748, 1), (key841, -1), (key832, -1)]

theorem rawRowCheck6761 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form1 = rawRow6761 := by decide +kernel

def row6761 : Integer.Sparse Key := [(key324, 1), (key325, 2), (key329, -3), (key339, -1), (key341, 1), (key414, -2), (key415, -2), (key419, 4), (key474, 2), (key476, -2), (key600, -2), (key602, 2), (key728, -1), (key736, -1), (key748, 1), (key752, 1), (key794, 2), (key815, 2), (key832, -2), (key841, -2)]

theorem rowCheck6761 : row6761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6761 := by decide +kernel

theorem rowEval6761 (x : Key → ℝ) : Integer.Sparse.eval row6761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6761, Integer.Sparse.eval_collectBalanced, rawRowCheck6761]

def rawRow6762 : Integer.Sparse Key := [(key414, -1), (key419, -1), (key415, 2), (key447, -1), (key451, -1), (key414, 2), (key476, 2), (key415, -1), (key474, -1), (key451, 2), (key419, -1), (key476, -1), (key324, 1), (key329, 1), (key325, -2), (key447, 1), (key451, 1), (key324, -2), (key602, -2), (key325, 1), (key600, 1), (key451, -2), (key329, 1), (key602, 1), (key312, -1), (key341, -1), (key313, 1), (key339, 1), (key312, 1), (key841, 1), (key727, -1), (key815, -1), (key794, -1), (key929, -1), (key728, 1), (key936, 1), (key832, 1), (key929, 1), (key748, -1), (key936, -1)]

theorem rawRowCheck6762 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form1 = rawRow6762 := by decide +kernel

def row6762 : Integer.Sparse Key := [(key313, 1), (key324, -1), (key325, -1), (key329, 2), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key727, -1), (key728, 1), (key748, -1), (key794, -1), (key815, -1), (key832, 1), (key841, 1)]

theorem rowCheck6762 : row6762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6762 := by decide +kernel

theorem rowEval6762 (x : Key → ℝ) : Integer.Sparse.eval row6762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6762, Integer.Sparse.eval_collectBalanced, rawRowCheck6762]

def rawRow6763 : Integer.Sparse Key := [(key419, -1), (key414, -1), (key415, 2), (key451, -1), (key447, -1), (key476, 2), (key414, 2), (key474, -1), (key415, -1), (key451, 2), (key476, -1), (key419, -1), (key329, 1), (key324, 1), (key325, -2), (key451, 1), (key447, 1), (key602, -2), (key324, -2), (key600, 1), (key325, 1), (key451, -2), (key602, 1), (key329, 1), (key341, -1), (key312, -1), (key339, 1), (key313, 1), (key584, 1), (key725, 1), (key815, -1), (key727, -1), (key929, -1), (key794, -1), (key936, 1), (key728, 1), (key929, 1), (key832, 1), (key936, -1), (key748, -1)]

theorem rawRowCheck6763 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form1 = rawRow6763 := by decide +kernel

def row6763 : Integer.Sparse Key := [(key312, -1), (key313, 1), (key324, -1), (key325, -1), (key329, 2), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -2), (key474, -1), (key476, 1), (key584, 1), (key600, 1), (key602, -1), (key725, 1), (key727, -1), (key728, 1), (key748, -1), (key794, -1), (key815, -1), (key832, 1)]

theorem rowCheck6763 : row6763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6763 := by decide +kernel

theorem rowEval6763 (x : Key → ℝ) : Integer.Sparse.eval row6763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6763, Integer.Sparse.eval_collectBalanced, rawRowCheck6763]

def rawRow6764 : Integer.Sparse Key := [(key415, -1), (key419, -1), (key414, 2), (key474, -1), (key476, -1), (key415, 2), (key451, 2), (key414, -1), (key447, -1), (key476, 2), (key419, -1), (key451, -1), (key325, 1), (key329, 1), (key324, -2), (key600, 1), (key602, 1), (key325, -2), (key451, -2), (key324, 1), (key447, 1), (key602, -2), (key329, 1), (key451, 1), (key313, -1), (key329, -1), (key312, 1), (key324, 1), (key313, 1), (key419, 1), (key725, -1), (key794, -1), (key815, -1), (key936, -1), (key736, 1), (key929, 1), (key841, 1), (key936, 1), (key752, -1), (key929, -1)]

theorem rawRowCheck6764 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form1 = rawRow6764 := by decide +kernel

def row6764 : Integer.Sparse Key := [(key312, 1), (key325, -1), (key329, 1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key725, -1), (key736, 1), (key752, -1), (key794, -1), (key815, -1), (key841, 1)]

theorem rowCheck6764 : row6764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6764 := by decide +kernel

theorem rowEval6764 (x : Key → ℝ) : Integer.Sparse.eval row6764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6764, Integer.Sparse.eval_collectBalanced, rawRowCheck6764]

def rawRow6765 : Integer.Sparse Key := [(key419, -1), (key415, -1), (key414, 2), (key476, -1), (key474, -1), (key451, 2), (key415, 2), (key447, -1), (key414, -1), (key476, 2), (key451, -1), (key419, -1), (key329, 1), (key325, 1), (key324, -2), (key602, 1), (key600, 1), (key451, -2), (key325, -2), (key447, 1), (key324, 1), (key602, -2), (key451, 1), (key329, 1), (key329, -1), (key313, -1), (key324, 1), (key312, 1), (key419, 1), (key313, 1), (key794, -1), (key725, -1), (key936, -1), (key815, -1), (key929, 1), (key736, 1), (key936, 1), (key841, 1), (key929, -1), (key752, -1)]

theorem rawRowCheck6765 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form1 = rawRow6765 := by decide +kernel

def row6765 : Integer.Sparse Key := [(key312, 1), (key325, -1), (key329, 1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key725, -1), (key736, 1), (key752, -1), (key794, -1), (key815, -1), (key841, 1)]

theorem rowCheck6765 : row6765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6765 := by decide +kernel

theorem rowEval6765 (x : Key → ℝ) : Integer.Sparse.eval row6765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6765, Integer.Sparse.eval_collectBalanced, rawRowCheck6765]

def rawRow6766 : Integer.Sparse Key := [(key447, -1), (key451, -1), (key451, 2), (key414, -1), (key419, -1), (key414, 2), (key476, 2), (key419, -1), (key476, -1), (key415, 2), (key415, -1), (key474, -1), (key447, 1), (key451, 1), (key451, -2), (key324, 1), (key329, 1), (key324, -2), (key602, -2), (key329, 1), (key602, 1), (key325, -2), (key325, 1), (key600, 1), (key414, -1), (key476, -1), (key419, 1), (key476, 1), (key324, 1), (key602, 1), (key329, -1), (key602, -1), (key312, -1), (key341, -1), (key312, 1), (key841, 1), (key727, 1), (key736, 1), (key727, -1), (key815, -1)]

theorem rawRowCheck6766 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form1 = rawRow6766 := by decide +kernel

def row6766 : Integer.Sparse Key := [(key325, -1), (key329, 1), (key341, -1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key600, 1), (key602, -1), (key736, 1), (key815, -1), (key841, 1)]

theorem rowCheck6766 : row6766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6766 := by decide +kernel

theorem rowEval6766 (x : Key → ℝ) : Integer.Sparse.eval row6766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6766, Integer.Sparse.eval_collectBalanced, rawRowCheck6766]

def rawRow6767 : Integer.Sparse Key := [(key451, -1), (key447, -1), (key451, 2), (key419, -1), (key414, -1), (key476, 2), (key414, 2), (key476, -1), (key419, -1), (key415, 2), (key474, -1), (key415, -1), (key451, 1), (key447, 1), (key451, -2), (key329, 1), (key324, 1), (key602, -2), (key324, -2), (key602, 1), (key329, 1), (key325, -2), (key600, 1), (key325, 1), (key476, -1), (key414, -1), (key476, 1), (key419, 1), (key602, 1), (key324, 1), (key602, -1), (key329, -1), (key341, -1), (key312, -1), (key584, 1), (key725, 1), (key736, 1), (key727, 1), (key815, -1), (key727, -1)]

theorem rawRowCheck6767 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form1 = rawRow6767 := by decide +kernel

def row6767 : Integer.Sparse Key := [(key312, -1), (key325, -1), (key329, 1), (key341, -1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key584, 1), (key600, 1), (key602, -1), (key725, 1), (key736, 1), (key815, -1)]

theorem rowCheck6767 : row6767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6767 := by decide +kernel

theorem rowEval6767 (x : Key → ℝ) : Integer.Sparse.eval row6767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6767, Integer.Sparse.eval_collectBalanced, rawRowCheck6767]

def rawRow6768 : Integer.Sparse Key := [(key451, -1), (key451, -1), (key447, 2), (key476, -1), (key476, -1), (key419, 2), (key419, 2), (key414, -1), (key414, -1), (key474, 2), (key415, -1), (key415, -1), (key451, 1), (key451, 1), (key447, -2), (key602, 1), (key602, 1), (key329, -2), (key329, -2), (key324, 1), (key324, 1), (key600, -2), (key325, 1), (key325, 1), (key419, -1), (key419, -1), (key414, 1), (key414, 1), (key329, 1), (key329, 1), (key324, -1), (key324, -1), (key584, -1), (key584, -1), (key341, 1), (key341, 1), (key815, 1), (key815, 1), (key736, -1), (key736, -1)]

theorem rawRowCheck6768 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form1 = rawRow6768 := by decide +kernel

def row6768 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key584, -2), (key600, -2), (key602, 2), (key736, -2), (key815, 2)]

theorem rowCheck6768 : row6768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6768 := by decide +kernel

theorem rowEval6768 (x : Key → ℝ) : Integer.Sparse.eval row6768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6768, Integer.Sparse.eval_collectBalanced, rawRowCheck6768]

def rawRow6769 : Integer.Sparse Key := [(key474, -1), (key476, -1), (key476, 2), (key415, -1), (key419, -1), (key415, 2), (key451, 2), (key419, -1), (key451, -1), (key414, 2), (key414, -1), (key447, -1), (key600, 1), (key602, 1), (key602, -2), (key325, 1), (key329, 1), (key325, -2), (key451, -2), (key329, 1), (key451, 1), (key324, -2), (key324, 1), (key447, 1), (key582, -1), (key602, -1), (key584, 1), (key602, 1), (key339, 1), (key476, 1), (key341, -1), (key476, -1), (key313, -1), (key329, -1), (key313, 1), (key419, 1), (key725, 1), (key728, 1), (key725, -1), (key794, -1)]

theorem rawRowCheck6769 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form1 = rawRow6769 := by decide +kernel

def row6769 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key582, -1), (key584, 1), (key600, 1), (key602, -1), (key728, 1), (key794, -1)]

theorem rowCheck6769 : row6769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6769 := by decide +kernel

theorem rowEval6769 (x : Key → ℝ) : Integer.Sparse.eval row6769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6769, Integer.Sparse.eval_collectBalanced, rawRowCheck6769]

def rawRow6770 : Integer.Sparse Key := [(key476, -1), (key474, -1), (key476, 2), (key419, -1), (key415, -1), (key451, 2), (key415, 2), (key451, -1), (key419, -1), (key414, 2), (key447, -1), (key414, -1), (key602, 1), (key600, 1), (key602, -2), (key329, 1), (key325, 1), (key451, -2), (key325, -2), (key451, 1), (key329, 1), (key324, -2), (key447, 1), (key324, 1), (key602, -1), (key582, -1), (key602, 1), (key584, 1), (key476, 1), (key339, 1), (key476, -1), (key341, -1), (key329, -1), (key313, -1), (key419, 1), (key313, 1), (key728, 1), (key725, 1), (key794, -1), (key725, -1)]

theorem rawRowCheck6770 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form1 = rawRow6770 := by decide +kernel

def row6770 : Integer.Sparse Key := [(key324, -1), (key325, -1), (key329, 1), (key339, 1), (key341, -1), (key414, 1), (key415, 1), (key419, -1), (key474, -1), (key476, 1), (key582, -1), (key584, 1), (key600, 1), (key602, -1), (key728, 1), (key794, -1)]

theorem rowCheck6770 : row6770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6770 := by decide +kernel

theorem rowEval6770 (x : Key → ℝ) : Integer.Sparse.eval row6770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6770, Integer.Sparse.eval_collectBalanced, rawRowCheck6770]

def rawRow6771 : Integer.Sparse Key := [(key476, -1), (key476, -1), (key474, 2), (key451, -1), (key451, -1), (key419, 2), (key419, 2), (key415, -1), (key415, -1), (key447, 2), (key414, -1), (key414, -1), (key602, 1), (key602, 1), (key600, -2), (key451, 1), (key451, 1), (key329, -2), (key329, -2), (key325, 1), (key325, 1), (key447, -2), (key324, 1), (key324, 1), (key584, -1), (key584, -1), (key582, 1), (key582, 1), (key341, 1), (key341, 1), (key339, -1), (key339, -1), (key419, -1), (key419, -1), (key329, 1), (key329, 1), (key794, 1), (key794, 1), (key728, -1), (key728, -1)]

theorem rawRowCheck6771 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form1 = rawRow6771 := by decide +kernel

def row6771 : Integer.Sparse Key := [(key324, 2), (key325, 2), (key329, -2), (key339, -2), (key341, 2), (key414, -2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2), (key728, -2), (key794, 2)]

theorem rowCheck6771 : row6771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6771 := by decide +kernel

theorem rowEval6771 (x : Key → ℝ) : Integer.Sparse.eval row6771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6771, Integer.Sparse.eval_collectBalanced, rawRowCheck6771]

def rawRow6772 : Integer.Sparse Key := [(key582, -1), (key582, -1), (key584, 2), (key582, -1), (key582, -1), (key600, 2), (key600, 2), (key602, -1), (key602, -1), (key584, 2), (key602, -1), (key602, -1), (key339, 1), (key339, 1), (key341, -2), (key339, 1), (key339, 1), (key474, -2), (key474, -2), (key476, 1), (key476, 1), (key341, -2), (key476, 1), (key476, 1), (key325, -1), (key325, -1), (key329, 1), (key329, 1), (key415, 1), (key415, 1), (key419, -1), (key419, -1), (key325, -1), (key325, -1), (key415, 1), (key415, 1), (key329, 1), (key329, 1), (key419, -1), (key419, -1)]

theorem rawRowCheck6772 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow6772 := by decide +kernel

def row6772 : Integer.Sparse Key := [(key325, -4), (key329, 4), (key339, 4), (key341, -4), (key415, 4), (key419, -4), (key474, -4), (key476, 4), (key582, -4), (key584, 4), (key600, 4), (key602, -4)]

theorem rowCheck6772 : row6772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6772 := by decide +kernel

theorem rowEval6772 (x : Key → ℝ) : Integer.Sparse.eval row6772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6772, Integer.Sparse.eval_collectBalanced, rawRowCheck6772]

def rawRow6773 : Integer.Sparse Key := [(key582, -1), (key584, -1), (key582, 2), (key600, -1), (key602, -1), (key582, 2), (key602, 2), (key582, -1), (key600, -1), (key602, 2), (key584, -1), (key602, -1), (key339, 1), (key341, 1), (key339, -2), (key474, 1), (key476, 1), (key339, -2), (key476, -2), (key339, 1), (key474, 1), (key476, -2), (key341, 1), (key476, 1), (key313, -1), (key329, -1), (key313, 1), (key325, 1), (key313, 1), (key419, 1), (key313, -1), (key415, -1), (key415, -1), (key451, -1), (key325, 1), (key451, 1), (key419, 1), (key451, 1), (key329, -1), (key451, -1)]

theorem rawRowCheck6773 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow6773 := by decide +kernel

def row6773 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

theorem rowCheck6773 : row6773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6773 := by decide +kernel

theorem rowEval6773 (x : Key → ℝ) : Integer.Sparse.eval row6773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6773, Integer.Sparse.eval_collectBalanced, rawRowCheck6773]

def rawRow6774 : Integer.Sparse Key := [(key584, -1), (key582, -1), (key582, 2), (key602, -1), (key600, -1), (key602, 2), (key582, 2), (key600, -1), (key582, -1), (key602, 2), (key602, -1), (key584, -1), (key341, 1), (key339, 1), (key339, -2), (key476, 1), (key474, 1), (key476, -2), (key339, -2), (key474, 1), (key339, 1), (key476, -2), (key476, 1), (key341, 1), (key329, -1), (key313, -1), (key325, 1), (key313, 1), (key419, 1), (key313, 1), (key415, -1), (key313, -1), (key451, -1), (key415, -1), (key451, 1), (key325, 1), (key451, 1), (key419, 1), (key451, -1), (key329, -1)]

theorem rawRowCheck6774 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow6774 := by decide +kernel

def row6774 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

theorem rowCheck6774 : row6774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6774 := by decide +kernel

theorem rowEval6774 (x : Key → ℝ) : Integer.Sparse.eval row6774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6774, Integer.Sparse.eval_collectBalanced, rawRowCheck6774]

def rawRow6775 : Integer.Sparse Key := [(key600, -1), (key602, -1), (key602, 2), (key582, -1), (key584, -1), (key582, 2), (key602, 2), (key584, -1), (key602, -1), (key582, 2), (key582, -1), (key600, -1), (key474, 1), (key476, 1), (key476, -2), (key339, 1), (key341, 1), (key339, -2), (key476, -2), (key341, 1), (key476, 1), (key339, -2), (key339, 1), (key474, 1), (key415, -1), (key451, -1), (key419, 1), (key451, 1), (key325, 1), (key451, 1), (key329, -1), (key451, -1), (key313, -1), (key329, -1), (key313, 1), (key419, 1), (key313, 1), (key325, 1), (key313, -1), (key415, -1)]

theorem rawRowCheck6775 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form1 = rawRow6775 := by decide +kernel

def row6775 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

theorem rowCheck6775 : row6775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6775 := by decide +kernel

theorem rowEval6775 (x : Key → ℝ) : Integer.Sparse.eval row6775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6775, Integer.Sparse.eval_collectBalanced, rawRowCheck6775]

def rawRow6776 : Integer.Sparse Key := [(key602, -1), (key600, -1), (key602, 2), (key584, -1), (key582, -1), (key602, 2), (key582, 2), (key602, -1), (key584, -1), (key582, 2), (key600, -1), (key582, -1), (key476, 1), (key474, 1), (key476, -2), (key341, 1), (key339, 1), (key476, -2), (key339, -2), (key476, 1), (key341, 1), (key339, -2), (key474, 1), (key339, 1), (key451, -1), (key415, -1), (key451, 1), (key419, 1), (key451, 1), (key325, 1), (key451, -1), (key329, -1), (key329, -1), (key313, -1), (key419, 1), (key313, 1), (key325, 1), (key313, 1), (key415, -1), (key313, -1)]

theorem rawRowCheck6776 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form1 = rawRow6776 := by decide +kernel

def row6776 : Integer.Sparse Key := [(key325, 2), (key329, -2), (key339, -2), (key341, 2), (key415, -2), (key419, 2), (key474, 2), (key476, -2), (key582, 2), (key584, -2), (key600, -2), (key602, 2)]

theorem rowCheck6776 : row6776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6776 := by decide +kernel

theorem rowEval6776 (x : Key → ℝ) : Integer.Sparse.eval row6776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6776, Integer.Sparse.eval_collectBalanced, rawRowCheck6776]

def rawRow6777 : Integer.Sparse Key := [(key602, -1), (key602, -1), (key600, 2), (key602, -1), (key602, -1), (key584, 2), (key584, 2), (key582, -1), (key582, -1), (key600, 2), (key582, -1), (key582, -1), (key476, 1), (key476, 1), (key474, -2), (key476, 1), (key476, 1), (key341, -2), (key341, -2), (key339, 1), (key339, 1), (key474, -2), (key339, 1), (key339, 1), (key419, -1), (key419, -1), (key415, 1), (key415, 1), (key329, 1), (key329, 1), (key325, -1), (key325, -1), (key419, -1), (key419, -1), (key329, 1), (key329, 1), (key415, 1), (key415, 1), (key325, -1), (key325, -1)]

theorem rawRowCheck6777 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form1 = rawRow6777 := by decide +kernel

def row6777 : Integer.Sparse Key := [(key325, -4), (key329, 4), (key339, 4), (key341, -4), (key415, 4), (key419, -4), (key474, -4), (key476, 4), (key582, -4), (key584, 4), (key600, 4), (key602, -4)]

theorem rowCheck6777 : row6777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6777 := by decide +kernel

theorem rowEval6777 (x : Key → ℝ) : Integer.Sparse.eval row6777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6777, Integer.Sparse.eval_collectBalanced, rawRowCheck6777]

def rawRow6778 : Integer.Sparse Key := [(key2031, -1), (key2034, -1), (key2034, 2), (key2061, -1), (key2064, -1), (key2061, 2), (key2070, 2), (key2064, -1), (key2070, -1), (key2080, 2), (key2080, -1), (key2086, -1), (key2031, 1), (key2034, 1), (key2034, -2), (key2150, 1), (key2153, 1), (key2150, -2), (key2167, -2), (key2153, 1), (key2167, 1), (key2177, -2), (key2177, 1), (key2188, 1), (key2061, -1), (key2070, -1), (key2064, 1), (key2070, 1), (key2150, 1), (key2167, 1), (key2153, -1), (key2167, -1), (key2243, -1), (key2247, -1), (key2243, 1), (key2254, 1), (key2277, 1), (key2280, 1), (key2277, -1), (key2288, -1)]

theorem rawRowCheck6778 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow6778 := by decide +kernel

def row6778 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6778 : row6778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6778 := by decide +kernel

theorem rowEval6778 (x : Key → ℝ) : Integer.Sparse.eval row6778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6778, Integer.Sparse.eval_collectBalanced, rawRowCheck6778]

def rawRow6779 : Integer.Sparse Key := [(key2034, -1), (key2031, -1), (key2034, 2), (key2064, -1), (key2061, -1), (key2070, 2), (key2061, 2), (key2070, -1), (key2064, -1), (key2080, 2), (key2086, -1), (key2080, -1), (key2034, 1), (key2031, 1), (key2034, -2), (key2153, 1), (key2150, 1), (key2167, -2), (key2150, -2), (key2167, 1), (key2153, 1), (key2177, -2), (key2188, 1), (key2177, 1), (key2070, -1), (key2061, -1), (key2070, 1), (key2064, 1), (key2167, 1), (key2150, 1), (key2167, -1), (key2153, -1), (key2247, -1), (key2243, -1), (key2254, 1), (key2243, 1), (key2280, 1), (key2277, 1), (key2288, -1), (key2277, -1)]

theorem rawRowCheck6779 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow6779 := by decide +kernel

def row6779 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6779 : row6779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6779 := by decide +kernel

theorem rowEval6779 (x : Key → ℝ) : Integer.Sparse.eval row6779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6779, Integer.Sparse.eval_collectBalanced, rawRowCheck6779]

def rawRow6780 : Integer.Sparse Key := [(key2034, -1), (key2034, -1), (key2031, 2), (key2070, -1), (key2070, -1), (key2064, 2), (key2064, 2), (key2061, -1), (key2061, -1), (key2086, 2), (key2080, -1), (key2080, -1), (key2034, 1), (key2034, 1), (key2031, -2), (key2167, 1), (key2167, 1), (key2153, -2), (key2153, -2), (key2150, 1), (key2150, 1), (key2188, -2), (key2177, 1), (key2177, 1), (key2064, -1), (key2064, -1), (key2061, 1), (key2061, 1), (key2153, 1), (key2153, 1), (key2150, -1), (key2150, -1), (key2254, -1), (key2254, -1), (key2247, 1), (key2247, 1), (key2288, 1), (key2288, 1), (key2280, -1), (key2280, -1)]

theorem rawRowCheck6780 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow6780 := by decide +kernel

def row6780 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6780 : row6780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6780 := by decide +kernel

theorem rowEval6780 (x : Key → ℝ) : Integer.Sparse.eval row6780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6780, Integer.Sparse.eval_collectBalanced, rawRowCheck6780]

def rawRow6781 : Integer.Sparse Key := [(key2061, -1), (key2064, -1), (key2080, 2), (key2031, -1), (key2034, -1), (key2061, 2), (key2070, 2), (key2080, -1), (key2086, -1), (key2034, 2), (key2064, -1), (key2070, -1), (key2150, 1), (key2153, 1), (key2177, -2), (key2031, 1), (key2034, 1), (key2150, -2), (key2167, -2), (key2177, 1), (key2188, 1), (key2034, -2), (key2153, 1), (key2167, 1), (key2243, -1), (key2247, -1), (key2277, 1), (key2280, 1), (key2243, 1), (key2254, 1), (key2277, -1), (key2288, -1), (key2061, -1), (key2070, -1), (key2150, 1), (key2167, 1), (key2064, 1), (key2070, 1), (key2153, -1), (key2167, -1)]

theorem rawRowCheck6781 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form2 = rawRow6781 := by decide +kernel

def row6781 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6781 : row6781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6781 := by decide +kernel

theorem rowEval6781 (x : Key → ℝ) : Integer.Sparse.eval row6781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6781, Integer.Sparse.eval_collectBalanced, rawRowCheck6781]

def rawRow6782 : Integer.Sparse Key := [(key2064, -1), (key2061, -1), (key2080, 2), (key2034, -1), (key2031, -1), (key2070, 2), (key2061, 2), (key2086, -1), (key2080, -1), (key2034, 2), (key2070, -1), (key2064, -1), (key2153, 1), (key2150, 1), (key2177, -2), (key2034, 1), (key2031, 1), (key2167, -2), (key2150, -2), (key2188, 1), (key2177, 1), (key2034, -2), (key2167, 1), (key2153, 1), (key2247, -1), (key2243, -1), (key2280, 1), (key2277, 1), (key2254, 1), (key2243, 1), (key2288, -1), (key2277, -1), (key2070, -1), (key2061, -1), (key2167, 1), (key2150, 1), (key2070, 1), (key2064, 1), (key2167, -1), (key2153, -1)]

theorem rawRowCheck6782 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form2 = rawRow6782 := by decide +kernel

def row6782 : Integer.Sparse Key := [(key2064, -1), (key2070, 1), (key2080, 1), (key2086, -1), (key2153, 1), (key2167, -1), (key2177, -1), (key2188, 1), (key2247, -1), (key2254, 1), (key2280, 1), (key2288, -1)]

theorem rowCheck6782 : row6782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6782 := by decide +kernel

theorem rowEval6782 (x : Key → ℝ) : Integer.Sparse.eval row6782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6782, Integer.Sparse.eval_collectBalanced, rawRowCheck6782]

def rawRow6783 : Integer.Sparse Key := [(key2061, -1), (key2080, -1), (key2064, 2), (key2061, -1), (key2080, -1), (key2031, 2), (key2086, 2), (key2034, -1), (key2070, -1), (key2064, 2), (key2034, -1), (key2070, -1), (key2150, 1), (key2177, 1), (key2153, -2), (key2150, 1), (key2177, 1), (key2031, -2), (key2188, -2), (key2034, 1), (key2167, 1), (key2153, -2), (key2034, 1), (key2167, 1), (key2150, -1), (key2280, -1), (key2153, 1), (key2247, 1), (key2061, 1), (key2288, 1), (key2064, -1), (key2254, -1), (key2150, -1), (key2280, -1), (key2061, 1), (key2288, 1), (key2153, 1), (key2247, 1), (key2064, -1), (key2254, -1)]

theorem rawRowCheck6783 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form2 = rawRow6783 := by decide +kernel

def row6783 : Integer.Sparse Key := [(key2064, 2), (key2070, -2), (key2080, -2), (key2086, 2), (key2153, -2), (key2167, 2), (key2177, 2), (key2188, -2), (key2247, 2), (key2254, -2), (key2280, -2), (key2288, 2)]

theorem rowCheck6783 : row6783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6783 := by decide +kernel

theorem rowEval6783 (x : Key → ℝ) : Integer.Sparse.eval row6783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6783, Integer.Sparse.eval_collectBalanced, rawRowCheck6783]

end MUB6.Certificate.GramRows

end OAI
