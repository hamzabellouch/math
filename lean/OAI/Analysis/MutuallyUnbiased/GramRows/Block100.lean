import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow9728 : Integer.Sparse Key := [(key3030, 1), (key2885, 1), (key3026, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3026, 1), (key2732, 1), (key3023, 1), (key2644, 1), (key2706, 1), (key2632, 1), (key2870, 1), (key2726, 1), (key2860, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2927, -2), (key2923, -2), (key2758, -2), (key2927, -2), (key2920, -2), (key2660, -2), (key2923, -2), (key2758, -2), (key2920, -2), (key2660, -2), (key2753, -2), (key2658, -2)]

theorem rawRowCheck9728 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form9 = rawRow9728 := by decide +kernel

def row9728 : Integer.Sparse Key := [(key2632, 2), (key2640, 2), (key2644, 2), (key2658, -2), (key2660, -4), (key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2860, 2), (key2870, 2), (key2885, 2), (key2920, -4), (key2923, -4), (key2927, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck9728 : row9728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9728 := by decide +kernel

theorem rowEval9728 (x : Key → ℝ) : Integer.Sparse.eval row9728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9728, Integer.Sparse.eval_collectBalanced, rawRowCheck9728]

def rawRow9729 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2660, 1), (key2660, 1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key2794, 1), (key2794, 1), (key2829, 1), (key2829, 1), (key2927, 1), (key2927, 1), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1), (key2621, -2), (key2644, -2), (key2644, -2), (key2676, -2), (key2732, -2), (key2732, -2), (key2798, -2), (key2798, -2), (key2835, -2), (key2835, -2), (key2885, -2), (key2885, -2)]

theorem rawRowCheck9729 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form9 = rawRow9729 := by decide +kernel

def row9729 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9729 : row9729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9729 := by decide +kernel

theorem rowEval9729 (x : Key → ℝ) : Integer.Sparse.eval row9729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9729, Integer.Sparse.eval_collectBalanced, rawRowCheck9729]

def rawRow9730 : Integer.Sparse Key := [(key2646, 1), (key2653, 1), (key2612, 1), (key2653, 1), (key2616, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key2644, -2), (key2621, -2), (key2644, -2), (key2732, -2), (key2676, -2), (key2732, -2), (key2835, -2), (key2885, -2), (key2798, -2), (key2885, -2), (key2798, -2), (key2835, -2)]

theorem rawRowCheck9730 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form9 = rawRow9730 := by decide +kernel

def row9730 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9730 : row9730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9730 := by decide +kernel

theorem rowEval9730 (x : Key → ℝ) : Integer.Sparse.eval row9730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9730, Integer.Sparse.eval_collectBalanced, rawRowCheck9730]

def rawRow9731 : Integer.Sparse Key := [(key2653, 1), (key2646, 1), (key2653, 1), (key2612, 1), (key2640, 1), (key2616, 1), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2927, 1), (key2829, 1), (key2927, 1), (key2794, 1), (key2829, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1), (key2644, -2), (key2644, -2), (key2621, -2), (key2732, -2), (key2732, -2), (key2676, -2), (key2885, -2), (key2835, -2), (key2885, -2), (key2798, -2), (key2835, -2), (key2798, -2)]

theorem rawRowCheck9731 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form9 = rawRow9731 := by decide +kernel

def row9731 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2671, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2758, 2), (key2794, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9731 : row9731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9731 := by decide +kernel

theorem rowEval9731 (x : Key → ℝ) : Integer.Sparse.eval row9731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9731, Integer.Sparse.eval_collectBalanced, rawRowCheck9731]

def rawRow9732 : Integer.Sparse Key := [(key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2640, 1), (key2640, 1), (key2726, 1), (key2726, 1), (key3030, 1), (key3030, 1), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1), (key2676, -2), (key2798, -2), (key2798, -2), (key2621, -2), (key2835, -2), (key2835, -2), (key2644, -2), (key2644, -2), (key2732, -2), (key2732, -2), (key2885, -2), (key2885, -2)]

theorem rawRowCheck9732 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form9 = rawRow9732 := by decide +kernel

def row9732 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 2), (key2835, -4), (key2885, -4), (key2927, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck9732 : row9732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9732 := by decide +kernel

theorem rowEval9732 (x : Key → ℝ) : Integer.Sparse.eval row9732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9732, Integer.Sparse.eval_collectBalanced, rawRowCheck9732]

def rawRow9733 : Integer.Sparse Key := [(key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2798, -2), (key2676, -2), (key2798, -2), (key2835, -2), (key2621, -2), (key2835, -2), (key2732, -2), (key2885, -2), (key2644, -2), (key2885, -2), (key2644, -2), (key2732, -2)]

theorem rawRowCheck9733 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form9 = rawRow9733 := by decide +kernel

def row9733 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2927, 2), (key2948, 1), (key2960, 2), (key3030, 2)]

theorem rowCheck9733 : row9733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9733 := by decide +kernel

theorem rowEval9733 (x : Key → ℝ) : Integer.Sparse.eval row9733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9733, Integer.Sparse.eval_collectBalanced, rawRowCheck9733]

def rawRow9734 : Integer.Sparse Key := [(key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key3030, 1), (key2726, 1), (key3030, 1), (key2640, 1), (key2726, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1), (key2798, -2), (key2798, -2), (key2676, -2), (key2835, -2), (key2835, -2), (key2621, -2), (key2885, -2), (key2732, -2), (key2885, -2), (key2644, -2), (key2732, -2), (key2644, -2)]

theorem rawRowCheck9734 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form9 = rawRow9734 := by decide +kernel

def row9734 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 2), (key2644, -4), (key2660, 2), (key2667, 2), (key2676, -2), (key2726, 2), (key2732, -4), (key2735, 2), (key2747, 2), (key2758, 2), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2927, 2), (key2948, 1), (key2960, 2), (key3030, 2)]

theorem rowCheck9734 : row9734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9734 := by decide +kernel

theorem rowEval9734 (x : Key → ℝ) : Integer.Sparse.eval row9734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9734, Integer.Sparse.eval_collectBalanced, rawRowCheck9734]

def rawRow9735 : Integer.Sparse Key := [(key2936, 1), (key2943, 1), (key2948, 1), (key2998, 1), (key2960, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2612, 1), (key2653, 1), (key2667, 1), (key2943, 1), (key2747, 1), (key2960, 1), (key2616, 1), (key2640, 1), (key2671, 1), (key2726, 1), (key2794, 1), (key2829, 1), (key2732, -2), (key2835, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2885, -2), (key2621, -2), (key2644, -2), (key2676, -2), (key2732, -2), (key2798, -2), (key2835, -2)]

theorem rawRowCheck9735 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form9 = rawRow9735 := by decide +kernel

def row9735 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

theorem rowCheck9735 : row9735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9735 := by decide +kernel

theorem rowEval9735 (x : Key → ℝ) : Integer.Sparse.eval row9735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9735, Integer.Sparse.eval_collectBalanced, rawRowCheck9735]

def rawRow9736 : Integer.Sparse Key := [(key2943, 1), (key2936, 1), (key2998, 1), (key2948, 1), (key3000, 1), (key2960, 1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2653, 1), (key2612, 1), (key2943, 1), (key2667, 1), (key2960, 1), (key2747, 1), (key2640, 1), (key2616, 1), (key2726, 1), (key2671, 1), (key2829, 1), (key2794, 1), (key2732, -2), (key2885, -2), (key2835, -2), (key2644, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2621, -2), (key2732, -2), (key2676, -2), (key2835, -2), (key2798, -2)]

theorem rawRowCheck9736 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form9 = rawRow9736 := by decide +kernel

def row9736 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

theorem rowCheck9736 : row9736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9736 := by decide +kernel

theorem rowEval9736 (x : Key → ℝ) : Integer.Sparse.eval row9736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9736, Integer.Sparse.eval_collectBalanced, rawRowCheck9736]

def rawRow9737 : Integer.Sparse Key := [(key2948, 1), (key2960, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2667, 1), (key2747, 1), (key2612, 1), (key2960, 1), (key2653, 1), (key2943, 1), (key2671, 1), (key2794, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2835, -2), (key2732, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2885, -2), (key2676, -2), (key2798, -2), (key2621, -2), (key2835, -2), (key2644, -2), (key2732, -2)]

theorem rawRowCheck9737 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form9 = rawRow9737 := by decide +kernel

def row9737 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

theorem rowCheck9737 : row9737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9737 := by decide +kernel

theorem rowEval9737 (x : Key → ℝ) : Integer.Sparse.eval row9737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9737, Integer.Sparse.eval_collectBalanced, rawRowCheck9737]

def rawRow9738 : Integer.Sparse Key := [(key2960, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2998, 1), (key2943, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2747, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2943, 1), (key2653, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2726, 1), (key2640, 1), (key2835, -2), (key2885, -2), (key2732, -2), (key2798, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2676, -2), (key2835, -2), (key2621, -2), (key2732, -2), (key2644, -2)]

theorem rawRowCheck9738 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form9 = rawRow9738 := by decide +kernel

def row9738 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

theorem rowCheck9738 : row9738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9738 := by decide +kernel

theorem rowEval9738 (x : Key → ℝ) : Integer.Sparse.eval row9738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9738, Integer.Sparse.eval_collectBalanced, rawRowCheck9738]

def rawRow9739 : Integer.Sparse Key := [(key2998, 1), (key3000, 1), (key2943, 1), (key2960, 1), (key2936, 1), (key2948, 1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2943, 1), (key2960, 1), (key2653, 1), (key2747, 1), (key2612, 1), (key2667, 1), (key2726, 1), (key2829, 1), (key2640, 1), (key2794, 1), (key2616, 1), (key2671, 1), (key2885, -2), (key2732, -2), (key2835, -2), (key2885, -2), (key2644, -2), (key2798, -2), (key2732, -2), (key2835, -2), (key2644, -2), (key2798, -2), (key2621, -2), (key2676, -2)]

theorem rawRowCheck9739 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form9 = rawRow9739 := by decide +kernel

def row9739 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

theorem rowCheck9739 : row9739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9739 := by decide +kernel

theorem rowEval9739 (x : Key → ℝ) : Integer.Sparse.eval row9739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9739, Integer.Sparse.eval_collectBalanced, rawRowCheck9739]

def rawRow9740 : Integer.Sparse Key := [(key3000, 1), (key2998, 1), (key2960, 1), (key2943, 1), (key2948, 1), (key2936, 1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2960, 1), (key2943, 1), (key2747, 1), (key2653, 1), (key2667, 1), (key2612, 1), (key2829, 1), (key2726, 1), (key2794, 1), (key2640, 1), (key2671, 1), (key2616, 1), (key2885, -2), (key2835, -2), (key2732, -2), (key2885, -2), (key2798, -2), (key2644, -2), (key2835, -2), (key2732, -2), (key2798, -2), (key2644, -2), (key2676, -2), (key2621, -2)]

theorem rawRowCheck9740 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form9 = rawRow9740 := by decide +kernel

def row9740 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, 1), (key2644, -4), (key2646, 1), (key2653, 2), (key2667, 1), (key2671, 1), (key2676, -2), (key2726, 1), (key2732, -4), (key2735, 1), (key2747, 2), (key2794, 1), (key2798, -4), (key2829, 1), (key2835, -4), (key2885, -4), (key2936, 1), (key2943, 2), (key2948, 1), (key2960, 2), (key2998, 2), (key3000, 2)]

theorem rowCheck9740 : row9740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9740 := by decide +kernel

theorem rowEval9740 (x : Key → ℝ) : Integer.Sparse.eval row9740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck9740, Integer.Sparse.eval_collectBalanced, rawRowCheck9740]

def rawRow9741 : Integer.Sparse Key := [(key1294, -6), (key1571, -6), (key1786, -6), (key1786, -6), (key1314, 2), (key1335, 2), (key1335, 2), (key1544, 2), (key1770, 2), (key1770, 2), (key1653, 2), (key1653, 2), (key1811, 2), (key1811, 2), (key1838, 2), (key1838, 2)]

theorem rawRowCheck9741 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form10 = rawRow9741 := by decide +kernel

def row9741 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9741 : row9741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9741 := by decide +kernel

theorem rowEval9741 (x : Key → ℝ) : Integer.Sparse.eval row9741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9741, Integer.Sparse.eval_collectBalanced, rawRowCheck9741]

def rawRow9742 : Integer.Sparse Key := [(key1294, -6), (key1786, -6), (key1571, -6), (key1786, -6), (key1335, 2), (key1314, 2), (key1335, 2), (key1770, 2), (key1544, 2), (key1770, 2), (key1811, 2), (key1838, 2), (key1653, 2), (key1838, 2), (key1653, 2), (key1811, 2)]

theorem rawRowCheck9742 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form10 = rawRow9742 := by decide +kernel

def row9742 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9742 : row9742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9742 := by decide +kernel

theorem rowEval9742 (x : Key → ℝ) : Integer.Sparse.eval row9742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9742, Integer.Sparse.eval_collectBalanced, rawRowCheck9742]

def rawRow9743 : Integer.Sparse Key := [(key1294, -6), (key1786, -6), (key1786, -6), (key1571, -6), (key1335, 2), (key1335, 2), (key1314, 2), (key1770, 2), (key1770, 2), (key1544, 2), (key1838, 2), (key1811, 2), (key1838, 2), (key1653, 2), (key1811, 2), (key1653, 2)]

theorem rawRowCheck9743 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form10 = rawRow9743 := by decide +kernel

def row9743 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9743 : row9743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9743 := by decide +kernel

theorem rowEval9743 (x : Key → ℝ) : Integer.Sparse.eval row9743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9743, Integer.Sparse.eval_collectBalanced, rawRowCheck9743]

def rawRow9744 : Integer.Sparse Key := [(key1571, -6), (key1294, -6), (key1786, -6), (key1786, -6), (key1544, 2), (key1653, 2), (key1653, 2), (key1314, 2), (key1811, 2), (key1811, 2), (key1335, 2), (key1335, 2), (key1770, 2), (key1770, 2), (key1838, 2), (key1838, 2)]

theorem rawRowCheck9744 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form10 = rawRow9744 := by decide +kernel

def row9744 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9744 : row9744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9744 := by decide +kernel

theorem rowEval9744 (x : Key → ℝ) : Integer.Sparse.eval row9744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9744, Integer.Sparse.eval_collectBalanced, rawRowCheck9744]

def rawRow9745 : Integer.Sparse Key := [(key1571, -6), (key1786, -6), (key1294, -6), (key1786, -6), (key1653, 2), (key1544, 2), (key1653, 2), (key1811, 2), (key1314, 2), (key1811, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1838, 2), (key1335, 2), (key1770, 2)]

theorem rawRowCheck9745 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form10 = rawRow9745 := by decide +kernel

def row9745 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9745 : row9745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9745 := by decide +kernel

theorem rowEval9745 (x : Key → ℝ) : Integer.Sparse.eval row9745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9745, Integer.Sparse.eval_collectBalanced, rawRowCheck9745]

def rawRow9746 : Integer.Sparse Key := [(key1571, -6), (key1786, -6), (key1786, -6), (key1294, -6), (key1653, 2), (key1653, 2), (key1544, 2), (key1811, 2), (key1811, 2), (key1314, 2), (key1838, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1770, 2), (key1335, 2)]

theorem rawRowCheck9746 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form10 = rawRow9746 := by decide +kernel

def row9746 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9746 : row9746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9746 := by decide +kernel

theorem rowEval9746 (x : Key → ℝ) : Integer.Sparse.eval row9746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9746, Integer.Sparse.eval_collectBalanced, rawRowCheck9746]

def rawRow9747 : Integer.Sparse Key := [(key1786, -6), (key1294, -6), (key1571, -6), (key1786, -6), (key1770, 2), (key1811, 2), (key1838, 2), (key1335, 2), (key1653, 2), (key1838, 2), (key1314, 2), (key1335, 2), (key1544, 2), (key1770, 2), (key1653, 2), (key1811, 2)]

theorem rawRowCheck9747 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form10 = rawRow9747 := by decide +kernel

def row9747 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9747 : row9747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9747 := by decide +kernel

theorem rowEval9747 (x : Key → ℝ) : Integer.Sparse.eval row9747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9747, Integer.Sparse.eval_collectBalanced, rawRowCheck9747]

def rawRow9748 : Integer.Sparse Key := [(key1786, -6), (key1294, -6), (key1786, -6), (key1571, -6), (key1770, 2), (key1838, 2), (key1811, 2), (key1335, 2), (key1838, 2), (key1653, 2), (key1335, 2), (key1314, 2), (key1770, 2), (key1544, 2), (key1811, 2), (key1653, 2)]

theorem rawRowCheck9748 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form10 = rawRow9748 := by decide +kernel

def row9748 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9748 : row9748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9748 := by decide +kernel

theorem rowEval9748 (x : Key → ℝ) : Integer.Sparse.eval row9748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9748, Integer.Sparse.eval_collectBalanced, rawRowCheck9748]

def rawRow9749 : Integer.Sparse Key := [(key1786, -6), (key1571, -6), (key1294, -6), (key1786, -6), (key1811, 2), (key1770, 2), (key1838, 2), (key1653, 2), (key1335, 2), (key1838, 2), (key1544, 2), (key1653, 2), (key1314, 2), (key1811, 2), (key1335, 2), (key1770, 2)]

theorem rawRowCheck9749 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form10 = rawRow9749 := by decide +kernel

def row9749 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9749 : row9749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9749 := by decide +kernel

theorem rowEval9749 (x : Key → ℝ) : Integer.Sparse.eval row9749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9749, Integer.Sparse.eval_collectBalanced, rawRowCheck9749]

def rawRow9750 : Integer.Sparse Key := [(key1786, -6), (key1571, -6), (key1786, -6), (key1294, -6), (key1811, 2), (key1838, 2), (key1770, 2), (key1653, 2), (key1838, 2), (key1335, 2), (key1653, 2), (key1544, 2), (key1811, 2), (key1314, 2), (key1770, 2), (key1335, 2)]

theorem rawRowCheck9750 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form10 = rawRow9750 := by decide +kernel

def row9750 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9750 : row9750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9750 := by decide +kernel

theorem rowEval9750 (x : Key → ℝ) : Integer.Sparse.eval row9750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9750, Integer.Sparse.eval_collectBalanced, rawRowCheck9750]

def rawRow9751 : Integer.Sparse Key := [(key1786, -6), (key1786, -6), (key1294, -6), (key1571, -6), (key1838, 2), (key1770, 2), (key1811, 2), (key1838, 2), (key1335, 2), (key1653, 2), (key1770, 2), (key1811, 2), (key1335, 2), (key1653, 2), (key1314, 2), (key1544, 2)]

theorem rawRowCheck9751 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form10 = rawRow9751 := by decide +kernel

def row9751 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9751 : row9751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9751 := by decide +kernel

theorem rowEval9751 (x : Key → ℝ) : Integer.Sparse.eval row9751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9751, Integer.Sparse.eval_collectBalanced, rawRowCheck9751]

def rawRow9752 : Integer.Sparse Key := [(key1786, -6), (key1786, -6), (key1571, -6), (key1294, -6), (key1838, 2), (key1811, 2), (key1770, 2), (key1838, 2), (key1653, 2), (key1335, 2), (key1811, 2), (key1770, 2), (key1653, 2), (key1335, 2), (key1544, 2), (key1314, 2)]

theorem rawRowCheck9752 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form10 = rawRow9752 := by decide +kernel

def row9752 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1544, 2), (key1571, -6), (key1653, 4), (key1770, 4), (key1786, -12), (key1811, 4), (key1838, 4)]

theorem rowCheck9752 : row9752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9752 := by decide +kernel

theorem rowEval9752 (x : Key → ℝ) : Integer.Sparse.eval row9752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9752, Integer.Sparse.eval_collectBalanced, rawRowCheck9752]

def rawRow9753 : Integer.Sparse Key := [(key1314, -6), (key1422, -6), (key1811, -6), (key1811, -6), (key1294, 2), (key1335, 2), (key1335, 2), (key1389, 2), (key1770, 2), (key1770, 2), (key1453, 2), (key1453, 2), (key1786, 2), (key1786, 2), (key1838, 2), (key1838, 2)]

theorem rawRowCheck9753 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form10 = rawRow9753 := by decide +kernel

def row9753 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9753 : row9753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9753 := by decide +kernel

theorem rowEval9753 (x : Key → ℝ) : Integer.Sparse.eval row9753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9753, Integer.Sparse.eval_collectBalanced, rawRowCheck9753]

def rawRow9754 : Integer.Sparse Key := [(key1314, -6), (key1811, -6), (key1422, -6), (key1811, -6), (key1335, 2), (key1294, 2), (key1335, 2), (key1770, 2), (key1389, 2), (key1770, 2), (key1786, 2), (key1838, 2), (key1453, 2), (key1838, 2), (key1453, 2), (key1786, 2)]

theorem rawRowCheck9754 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form10 = rawRow9754 := by decide +kernel

def row9754 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9754 : row9754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9754 := by decide +kernel

theorem rowEval9754 (x : Key → ℝ) : Integer.Sparse.eval row9754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9754, Integer.Sparse.eval_collectBalanced, rawRowCheck9754]

def rawRow9755 : Integer.Sparse Key := [(key1314, -6), (key1811, -6), (key1811, -6), (key1422, -6), (key1335, 2), (key1335, 2), (key1294, 2), (key1770, 2), (key1770, 2), (key1389, 2), (key1838, 2), (key1786, 2), (key1838, 2), (key1453, 2), (key1786, 2), (key1453, 2)]

theorem rawRowCheck9755 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form10 = rawRow9755 := by decide +kernel

def row9755 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9755 : row9755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9755 := by decide +kernel

theorem rowEval9755 (x : Key → ℝ) : Integer.Sparse.eval row9755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9755, Integer.Sparse.eval_collectBalanced, rawRowCheck9755]

def rawRow9756 : Integer.Sparse Key := [(key1422, -6), (key1314, -6), (key1811, -6), (key1811, -6), (key1389, 2), (key1453, 2), (key1453, 2), (key1294, 2), (key1786, 2), (key1786, 2), (key1335, 2), (key1335, 2), (key1770, 2), (key1770, 2), (key1838, 2), (key1838, 2)]

theorem rawRowCheck9756 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form10 = rawRow9756 := by decide +kernel

def row9756 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9756 : row9756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9756 := by decide +kernel

theorem rowEval9756 (x : Key → ℝ) : Integer.Sparse.eval row9756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9756, Integer.Sparse.eval_collectBalanced, rawRowCheck9756]

def rawRow9757 : Integer.Sparse Key := [(key1422, -6), (key1811, -6), (key1314, -6), (key1811, -6), (key1453, 2), (key1389, 2), (key1453, 2), (key1786, 2), (key1294, 2), (key1786, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1838, 2), (key1335, 2), (key1770, 2)]

theorem rawRowCheck9757 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form10 = rawRow9757 := by decide +kernel

def row9757 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9757 : row9757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9757 := by decide +kernel

theorem rowEval9757 (x : Key → ℝ) : Integer.Sparse.eval row9757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9757, Integer.Sparse.eval_collectBalanced, rawRowCheck9757]

def rawRow9758 : Integer.Sparse Key := [(key1422, -6), (key1811, -6), (key1811, -6), (key1314, -6), (key1453, 2), (key1453, 2), (key1389, 2), (key1786, 2), (key1786, 2), (key1294, 2), (key1838, 2), (key1770, 2), (key1838, 2), (key1335, 2), (key1770, 2), (key1335, 2)]

theorem rawRowCheck9758 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form10 = rawRow9758 := by decide +kernel

def row9758 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9758 : row9758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9758 := by decide +kernel

theorem rowEval9758 (x : Key → ℝ) : Integer.Sparse.eval row9758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9758, Integer.Sparse.eval_collectBalanced, rawRowCheck9758]

def rawRow9759 : Integer.Sparse Key := [(key1811, -6), (key1314, -6), (key1422, -6), (key1811, -6), (key1770, 2), (key1786, 2), (key1838, 2), (key1335, 2), (key1453, 2), (key1838, 2), (key1294, 2), (key1335, 2), (key1389, 2), (key1770, 2), (key1453, 2), (key1786, 2)]

theorem rawRowCheck9759 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form10 = rawRow9759 := by decide +kernel

def row9759 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9759 : row9759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9759 := by decide +kernel

theorem rowEval9759 (x : Key → ℝ) : Integer.Sparse.eval row9759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9759, Integer.Sparse.eval_collectBalanced, rawRowCheck9759]

def rawRow9760 : Integer.Sparse Key := [(key1811, -6), (key1314, -6), (key1811, -6), (key1422, -6), (key1770, 2), (key1838, 2), (key1786, 2), (key1335, 2), (key1838, 2), (key1453, 2), (key1335, 2), (key1294, 2), (key1770, 2), (key1389, 2), (key1786, 2), (key1453, 2)]

theorem rawRowCheck9760 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form10 = rawRow9760 := by decide +kernel

def row9760 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9760 : row9760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9760 := by decide +kernel

theorem rowEval9760 (x : Key → ℝ) : Integer.Sparse.eval row9760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9760, Integer.Sparse.eval_collectBalanced, rawRowCheck9760]

def rawRow9761 : Integer.Sparse Key := [(key1811, -6), (key1422, -6), (key1314, -6), (key1811, -6), (key1786, 2), (key1770, 2), (key1838, 2), (key1453, 2), (key1335, 2), (key1838, 2), (key1389, 2), (key1453, 2), (key1294, 2), (key1786, 2), (key1335, 2), (key1770, 2)]

theorem rawRowCheck9761 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form10 = rawRow9761 := by decide +kernel

def row9761 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9761 : row9761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9761 := by decide +kernel

theorem rowEval9761 (x : Key → ℝ) : Integer.Sparse.eval row9761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9761, Integer.Sparse.eval_collectBalanced, rawRowCheck9761]

def rawRow9762 : Integer.Sparse Key := [(key1811, -6), (key1422, -6), (key1811, -6), (key1314, -6), (key1786, 2), (key1838, 2), (key1770, 2), (key1453, 2), (key1838, 2), (key1335, 2), (key1453, 2), (key1389, 2), (key1786, 2), (key1294, 2), (key1770, 2), (key1335, 2)]

theorem rawRowCheck9762 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form10 = rawRow9762 := by decide +kernel

def row9762 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9762 : row9762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9762 := by decide +kernel

theorem rowEval9762 (x : Key → ℝ) : Integer.Sparse.eval row9762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9762, Integer.Sparse.eval_collectBalanced, rawRowCheck9762]

def rawRow9763 : Integer.Sparse Key := [(key1811, -6), (key1811, -6), (key1314, -6), (key1422, -6), (key1838, 2), (key1770, 2), (key1786, 2), (key1838, 2), (key1335, 2), (key1453, 2), (key1770, 2), (key1786, 2), (key1335, 2), (key1453, 2), (key1294, 2), (key1389, 2)]

theorem rawRowCheck9763 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form10 = rawRow9763 := by decide +kernel

def row9763 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9763 : row9763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9763 := by decide +kernel

theorem rowEval9763 (x : Key → ℝ) : Integer.Sparse.eval row9763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9763, Integer.Sparse.eval_collectBalanced, rawRowCheck9763]

def rawRow9764 : Integer.Sparse Key := [(key1811, -6), (key1811, -6), (key1422, -6), (key1314, -6), (key1838, 2), (key1786, 2), (key1770, 2), (key1838, 2), (key1453, 2), (key1335, 2), (key1786, 2), (key1770, 2), (key1453, 2), (key1335, 2), (key1389, 2), (key1294, 2)]

theorem rawRowCheck9764 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form10 = rawRow9764 := by decide +kernel

def row9764 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, 2), (key1422, -6), (key1453, 4), (key1770, 4), (key1786, 4), (key1811, -12), (key1838, 4)]

theorem rowCheck9764 : row9764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9764 := by decide +kernel

theorem rowEval9764 (x : Key → ℝ) : Integer.Sparse.eval row9764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9764, Integer.Sparse.eval_collectBalanced, rawRowCheck9764]

def rawRow9765 : Integer.Sparse Key := [(key2770, 6), (key2770, 6), (key2773, 6), (key2932, 6), (key2601, -6), (key2890, -6), (key2911, -6), (key2911, -6)]

theorem rawRowCheck9765 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form11 = rawRow9765 := by decide +kernel

def row9765 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9765 : row9765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9765 := by decide +kernel

theorem rowEval9765 (x : Key → ℝ) : Integer.Sparse.eval row9765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9765, Integer.Sparse.eval_collectBalanced, rawRowCheck9765]

def rawRow9766 : Integer.Sparse Key := [(key2770, 6), (key2773, 6), (key2770, 6), (key2932, 6), (key2601, -6), (key2911, -6), (key2890, -6), (key2911, -6)]

theorem rawRowCheck9766 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form11 = rawRow9766 := by decide +kernel

def row9766 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9766 : row9766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9766 := by decide +kernel

theorem rowEval9766 (x : Key → ℝ) : Integer.Sparse.eval row9766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9766, Integer.Sparse.eval_collectBalanced, rawRowCheck9766]

def rawRow9767 : Integer.Sparse Key := [(key2773, 6), (key2770, 6), (key2770, 6), (key2932, 6), (key2601, -6), (key2911, -6), (key2911, -6), (key2890, -6)]

theorem rawRowCheck9767 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form11 = rawRow9767 := by decide +kernel

def row9767 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9767 : row9767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9767 := by decide +kernel

theorem rowEval9767 (x : Key → ℝ) : Integer.Sparse.eval row9767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9767, Integer.Sparse.eval_collectBalanced, rawRowCheck9767]

def rawRow9768 : Integer.Sparse Key := [(key2770, 6), (key2770, 6), (key2932, 6), (key2773, 6), (key2890, -6), (key2601, -6), (key2911, -6), (key2911, -6)]

theorem rawRowCheck9768 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form11 = rawRow9768 := by decide +kernel

def row9768 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9768 : row9768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9768 := by decide +kernel

theorem rowEval9768 (x : Key → ℝ) : Integer.Sparse.eval row9768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9768, Integer.Sparse.eval_collectBalanced, rawRowCheck9768]

def rawRow9769 : Integer.Sparse Key := [(key2770, 6), (key2932, 6), (key2770, 6), (key2773, 6), (key2890, -6), (key2911, -6), (key2601, -6), (key2911, -6)]

theorem rawRowCheck9769 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form11 = rawRow9769 := by decide +kernel

def row9769 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9769 : row9769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9769 := by decide +kernel

theorem rowEval9769 (x : Key → ℝ) : Integer.Sparse.eval row9769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9769, Integer.Sparse.eval_collectBalanced, rawRowCheck9769]

def rawRow9770 : Integer.Sparse Key := [(key2932, 6), (key2770, 6), (key2770, 6), (key2773, 6), (key2890, -6), (key2911, -6), (key2911, -6), (key2601, -6)]

theorem rawRowCheck9770 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form11 = rawRow9770 := by decide +kernel

def row9770 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9770 : row9770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9770 := by decide +kernel

theorem rowEval9770 (x : Key → ℝ) : Integer.Sparse.eval row9770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9770, Integer.Sparse.eval_collectBalanced, rawRowCheck9770]

def rawRow9771 : Integer.Sparse Key := [(key2770, 6), (key2773, 6), (key2932, 6), (key2770, 6), (key2911, -6), (key2601, -6), (key2890, -6), (key2911, -6)]

theorem rawRowCheck9771 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form11 = rawRow9771 := by decide +kernel

def row9771 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9771 : row9771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9771 := by decide +kernel

theorem rowEval9771 (x : Key → ℝ) : Integer.Sparse.eval row9771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9771, Integer.Sparse.eval_collectBalanced, rawRowCheck9771]

def rawRow9772 : Integer.Sparse Key := [(key2773, 6), (key2770, 6), (key2932, 6), (key2770, 6), (key2911, -6), (key2601, -6), (key2911, -6), (key2890, -6)]

theorem rawRowCheck9772 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form11 = rawRow9772 := by decide +kernel

def row9772 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9772 : row9772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9772 := by decide +kernel

theorem rowEval9772 (x : Key → ℝ) : Integer.Sparse.eval row9772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9772, Integer.Sparse.eval_collectBalanced, rawRowCheck9772]

def rawRow9773 : Integer.Sparse Key := [(key2770, 6), (key2932, 6), (key2773, 6), (key2770, 6), (key2911, -6), (key2890, -6), (key2601, -6), (key2911, -6)]

theorem rawRowCheck9773 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form11 = rawRow9773 := by decide +kernel

def row9773 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9773 : row9773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9773 := by decide +kernel

theorem rowEval9773 (x : Key → ℝ) : Integer.Sparse.eval row9773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9773, Integer.Sparse.eval_collectBalanced, rawRowCheck9773]

def rawRow9774 : Integer.Sparse Key := [(key2932, 6), (key2770, 6), (key2773, 6), (key2770, 6), (key2911, -6), (key2890, -6), (key2911, -6), (key2601, -6)]

theorem rawRowCheck9774 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form11 = rawRow9774 := by decide +kernel

def row9774 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9774 : row9774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9774 := by decide +kernel

theorem rowEval9774 (x : Key → ℝ) : Integer.Sparse.eval row9774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9774, Integer.Sparse.eval_collectBalanced, rawRowCheck9774]

def rawRow9775 : Integer.Sparse Key := [(key2773, 6), (key2932, 6), (key2770, 6), (key2770, 6), (key2911, -6), (key2911, -6), (key2601, -6), (key2890, -6)]

theorem rawRowCheck9775 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form11 = rawRow9775 := by decide +kernel

def row9775 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9775 : row9775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9775 := by decide +kernel

theorem rowEval9775 (x : Key → ℝ) : Integer.Sparse.eval row9775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9775, Integer.Sparse.eval_collectBalanced, rawRowCheck9775]

def rawRow9776 : Integer.Sparse Key := [(key2932, 6), (key2773, 6), (key2770, 6), (key2770, 6), (key2911, -6), (key2911, -6), (key2890, -6), (key2601, -6)]

theorem rawRowCheck9776 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form11 = rawRow9776 := by decide +kernel

def row9776 : Integer.Sparse Key := [(key2601, -6), (key2770, 12), (key2773, 6), (key2890, -6), (key2911, -12), (key2932, 6)]

theorem rowCheck9776 : row9776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9776 := by decide +kernel

theorem rowEval9776 (x : Key → ℝ) : Integer.Sparse.eval row9776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9776, Integer.Sparse.eval_collectBalanced, rawRowCheck9776]

def rawRow9777 : Integer.Sparse Key := [(key2847, 6), (key2847, 6), (key2890, 6), (key2969, 6), (key2594, -6), (key2773, -6), (key2881, -6), (key2881, -6)]

theorem rawRowCheck9777 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form11 = rawRow9777 := by decide +kernel

def row9777 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9777 : row9777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9777 := by decide +kernel

theorem rowEval9777 (x : Key → ℝ) : Integer.Sparse.eval row9777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9777, Integer.Sparse.eval_collectBalanced, rawRowCheck9777]

def rawRow9778 : Integer.Sparse Key := [(key2847, 6), (key2890, 6), (key2847, 6), (key2969, 6), (key2594, -6), (key2881, -6), (key2773, -6), (key2881, -6)]

theorem rawRowCheck9778 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form11 = rawRow9778 := by decide +kernel

def row9778 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9778 : row9778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9778 := by decide +kernel

theorem rowEval9778 (x : Key → ℝ) : Integer.Sparse.eval row9778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9778, Integer.Sparse.eval_collectBalanced, rawRowCheck9778]

def rawRow9779 : Integer.Sparse Key := [(key2890, 6), (key2847, 6), (key2847, 6), (key2969, 6), (key2594, -6), (key2881, -6), (key2881, -6), (key2773, -6)]

theorem rawRowCheck9779 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form11 = rawRow9779 := by decide +kernel

def row9779 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9779 : row9779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9779 := by decide +kernel

theorem rowEval9779 (x : Key → ℝ) : Integer.Sparse.eval row9779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9779, Integer.Sparse.eval_collectBalanced, rawRowCheck9779]

def rawRow9780 : Integer.Sparse Key := [(key2847, 6), (key2847, 6), (key2969, 6), (key2890, 6), (key2773, -6), (key2594, -6), (key2881, -6), (key2881, -6)]

theorem rawRowCheck9780 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form11 = rawRow9780 := by decide +kernel

def row9780 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9780 : row9780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9780 := by decide +kernel

theorem rowEval9780 (x : Key → ℝ) : Integer.Sparse.eval row9780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9780, Integer.Sparse.eval_collectBalanced, rawRowCheck9780]

def rawRow9781 : Integer.Sparse Key := [(key2847, 6), (key2969, 6), (key2847, 6), (key2890, 6), (key2773, -6), (key2881, -6), (key2594, -6), (key2881, -6)]

theorem rawRowCheck9781 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form11 = rawRow9781 := by decide +kernel

def row9781 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9781 : row9781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9781 := by decide +kernel

theorem rowEval9781 (x : Key → ℝ) : Integer.Sparse.eval row9781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9781, Integer.Sparse.eval_collectBalanced, rawRowCheck9781]

def rawRow9782 : Integer.Sparse Key := [(key2969, 6), (key2847, 6), (key2847, 6), (key2890, 6), (key2773, -6), (key2881, -6), (key2881, -6), (key2594, -6)]

theorem rawRowCheck9782 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form11 = rawRow9782 := by decide +kernel

def row9782 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9782 : row9782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9782 := by decide +kernel

theorem rowEval9782 (x : Key → ℝ) : Integer.Sparse.eval row9782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9782, Integer.Sparse.eval_collectBalanced, rawRowCheck9782]

def rawRow9783 : Integer.Sparse Key := [(key2847, 6), (key2890, 6), (key2969, 6), (key2847, 6), (key2881, -6), (key2594, -6), (key2773, -6), (key2881, -6)]

theorem rawRowCheck9783 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form11 = rawRow9783 := by decide +kernel

def row9783 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9783 : row9783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9783 := by decide +kernel

theorem rowEval9783 (x : Key → ℝ) : Integer.Sparse.eval row9783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9783, Integer.Sparse.eval_collectBalanced, rawRowCheck9783]

def rawRow9784 : Integer.Sparse Key := [(key2890, 6), (key2847, 6), (key2969, 6), (key2847, 6), (key2881, -6), (key2594, -6), (key2881, -6), (key2773, -6)]

theorem rawRowCheck9784 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form11 = rawRow9784 := by decide +kernel

def row9784 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9784 : row9784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9784 := by decide +kernel

theorem rowEval9784 (x : Key → ℝ) : Integer.Sparse.eval row9784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9784, Integer.Sparse.eval_collectBalanced, rawRowCheck9784]

def rawRow9785 : Integer.Sparse Key := [(key2847, 6), (key2969, 6), (key2890, 6), (key2847, 6), (key2881, -6), (key2773, -6), (key2594, -6), (key2881, -6)]

theorem rawRowCheck9785 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form11 = rawRow9785 := by decide +kernel

def row9785 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9785 : row9785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9785 := by decide +kernel

theorem rowEval9785 (x : Key → ℝ) : Integer.Sparse.eval row9785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9785, Integer.Sparse.eval_collectBalanced, rawRowCheck9785]

def rawRow9786 : Integer.Sparse Key := [(key2969, 6), (key2847, 6), (key2890, 6), (key2847, 6), (key2881, -6), (key2773, -6), (key2881, -6), (key2594, -6)]

theorem rawRowCheck9786 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form11 = rawRow9786 := by decide +kernel

def row9786 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9786 : row9786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9786 := by decide +kernel

theorem rowEval9786 (x : Key → ℝ) : Integer.Sparse.eval row9786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9786, Integer.Sparse.eval_collectBalanced, rawRowCheck9786]

def rawRow9787 : Integer.Sparse Key := [(key2890, 6), (key2969, 6), (key2847, 6), (key2847, 6), (key2881, -6), (key2881, -6), (key2594, -6), (key2773, -6)]

theorem rawRowCheck9787 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form11 = rawRow9787 := by decide +kernel

def row9787 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9787 : row9787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9787 := by decide +kernel

theorem rowEval9787 (x : Key → ℝ) : Integer.Sparse.eval row9787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9787, Integer.Sparse.eval_collectBalanced, rawRowCheck9787]

def rawRow9788 : Integer.Sparse Key := [(key2969, 6), (key2890, 6), (key2847, 6), (key2847, 6), (key2881, -6), (key2881, -6), (key2773, -6), (key2594, -6)]

theorem rawRowCheck9788 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form11 = rawRow9788 := by decide +kernel

def row9788 : Integer.Sparse Key := [(key2594, -6), (key2773, -6), (key2847, 12), (key2881, -12), (key2890, 6), (key2969, 6)]

theorem rowCheck9788 : row9788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9788 := by decide +kernel

theorem rowEval9788 (x : Key → ℝ) : Integer.Sparse.eval row9788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck9788, Integer.Sparse.eval_collectBalanced, rawRowCheck9788]

def rawRow9789 : Integer.Sparse Key := [(key2402, 6), (key2402, 6), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -6), (key2926, -6)]

theorem rawRowCheck9789 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form12 = rawRow9789 := by decide +kernel

def row9789 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9789 : row9789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9789 := by decide +kernel

theorem rowEval9789 (x : Key → ℝ) : Integer.Sparse.eval row9789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9789, Integer.Sparse.eval_collectBalanced, rawRowCheck9789]

def rawRow9790 : Integer.Sparse Key := [(key2402, 6), (key2408, 6), (key2402, 6), (key2439, 6), (key2605, -6), (key2926, -6), (key2917, -6), (key2926, -6)]

theorem rawRowCheck9790 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form12 = rawRow9790 := by decide +kernel

def row9790 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9790 : row9790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9790 := by decide +kernel

theorem rowEval9790 (x : Key → ℝ) : Integer.Sparse.eval row9790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9790, Integer.Sparse.eval_collectBalanced, rawRowCheck9790]

def rawRow9791 : Integer.Sparse Key := [(key2408, 6), (key2402, 6), (key2402, 6), (key2439, 6), (key2605, -6), (key2926, -6), (key2926, -6), (key2917, -6)]

theorem rawRowCheck9791 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form12 = rawRow9791 := by decide +kernel

def row9791 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9791 : row9791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9791 := by decide +kernel

theorem rowEval9791 (x : Key → ℝ) : Integer.Sparse.eval row9791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9791, Integer.Sparse.eval_collectBalanced, rawRowCheck9791]

def rawRow9792 : Integer.Sparse Key := [(key2402, 6), (key2402, 6), (key2439, 6), (key2408, 6), (key2917, -6), (key2605, -6), (key2926, -6), (key2926, -6)]

theorem rawRowCheck9792 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form12 = rawRow9792 := by decide +kernel

def row9792 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9792 : row9792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9792 := by decide +kernel

theorem rowEval9792 (x : Key → ℝ) : Integer.Sparse.eval row9792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9792, Integer.Sparse.eval_collectBalanced, rawRowCheck9792]

def rawRow9793 : Integer.Sparse Key := [(key2402, 6), (key2439, 6), (key2402, 6), (key2408, 6), (key2917, -6), (key2926, -6), (key2605, -6), (key2926, -6)]

theorem rawRowCheck9793 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form12 = rawRow9793 := by decide +kernel

def row9793 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9793 : row9793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9793 := by decide +kernel

theorem rowEval9793 (x : Key → ℝ) : Integer.Sparse.eval row9793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9793, Integer.Sparse.eval_collectBalanced, rawRowCheck9793]

def rawRow9794 : Integer.Sparse Key := [(key2439, 6), (key2402, 6), (key2402, 6), (key2408, 6), (key2917, -6), (key2926, -6), (key2926, -6), (key2605, -6)]

theorem rawRowCheck9794 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form12 = rawRow9794 := by decide +kernel

def row9794 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9794 : row9794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9794 := by decide +kernel

theorem rowEval9794 (x : Key → ℝ) : Integer.Sparse.eval row9794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9794, Integer.Sparse.eval_collectBalanced, rawRowCheck9794]

def rawRow9795 : Integer.Sparse Key := [(key2402, 6), (key2408, 6), (key2439, 6), (key2402, 6), (key2926, -6), (key2605, -6), (key2917, -6), (key2926, -6)]

theorem rawRowCheck9795 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow9795 := by decide +kernel

def row9795 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9795 : row9795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9795 := by decide +kernel

theorem rowEval9795 (x : Key → ℝ) : Integer.Sparse.eval row9795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9795, Integer.Sparse.eval_collectBalanced, rawRowCheck9795]

def rawRow9796 : Integer.Sparse Key := [(key2408, 6), (key2402, 6), (key2439, 6), (key2402, 6), (key2926, -6), (key2605, -6), (key2926, -6), (key2917, -6)]

theorem rawRowCheck9796 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow9796 := by decide +kernel

def row9796 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9796 : row9796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9796 := by decide +kernel

theorem rowEval9796 (x : Key → ℝ) : Integer.Sparse.eval row9796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9796, Integer.Sparse.eval_collectBalanced, rawRowCheck9796]

def rawRow9797 : Integer.Sparse Key := [(key2402, 6), (key2439, 6), (key2408, 6), (key2402, 6), (key2926, -6), (key2917, -6), (key2605, -6), (key2926, -6)]

theorem rawRowCheck9797 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow9797 := by decide +kernel

def row9797 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9797 : row9797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9797 := by decide +kernel

theorem rowEval9797 (x : Key → ℝ) : Integer.Sparse.eval row9797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9797, Integer.Sparse.eval_collectBalanced, rawRowCheck9797]

def rawRow9798 : Integer.Sparse Key := [(key2439, 6), (key2402, 6), (key2408, 6), (key2402, 6), (key2926, -6), (key2917, -6), (key2926, -6), (key2605, -6)]

theorem rawRowCheck9798 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow9798 := by decide +kernel

def row9798 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9798 : row9798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9798 := by decide +kernel

theorem rowEval9798 (x : Key → ℝ) : Integer.Sparse.eval row9798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9798, Integer.Sparse.eval_collectBalanced, rawRowCheck9798]

def rawRow9799 : Integer.Sparse Key := [(key2408, 6), (key2439, 6), (key2402, 6), (key2402, 6), (key2926, -6), (key2926, -6), (key2605, -6), (key2917, -6)]

theorem rawRowCheck9799 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form12 = rawRow9799 := by decide +kernel

def row9799 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9799 : row9799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9799 := by decide +kernel

theorem rowEval9799 (x : Key → ℝ) : Integer.Sparse.eval row9799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9799, Integer.Sparse.eval_collectBalanced, rawRowCheck9799]

def rawRow9800 : Integer.Sparse Key := [(key2439, 6), (key2408, 6), (key2402, 6), (key2402, 6), (key2926, -6), (key2926, -6), (key2917, -6), (key2605, -6)]

theorem rawRowCheck9800 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form12 = rawRow9800 := by decide +kernel

def row9800 : Integer.Sparse Key := [(key2402, 12), (key2408, 6), (key2439, 6), (key2605, -6), (key2917, -6), (key2926, -12)]

theorem rowCheck9800 : row9800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9800 := by decide +kernel

theorem rowEval9800 (x : Key → ℝ) : Integer.Sparse.eval row9800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9800, Integer.Sparse.eval_collectBalanced, rawRowCheck9800]

def rawRow9801 : Integer.Sparse Key := [(key2468, 6), (key2468, 6), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -6), (key2884, -6)]

theorem rawRowCheck9801 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form12 = rawRow9801 := by decide +kernel

def row9801 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9801 : row9801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9801 := by decide +kernel

theorem rowEval9801 (x : Key → ℝ) : Integer.Sparse.eval row9801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9801, Integer.Sparse.eval_collectBalanced, rawRowCheck9801]

def rawRow9802 : Integer.Sparse Key := [(key2468, 6), (key2481, 6), (key2468, 6), (key2505, 6), (key2596, -6), (key2884, -6), (key2775, -6), (key2884, -6)]

theorem rawRowCheck9802 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form12 = rawRow9802 := by decide +kernel

def row9802 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9802 : row9802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9802 := by decide +kernel

theorem rowEval9802 (x : Key → ℝ) : Integer.Sparse.eval row9802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9802, Integer.Sparse.eval_collectBalanced, rawRowCheck9802]

def rawRow9803 : Integer.Sparse Key := [(key2481, 6), (key2468, 6), (key2468, 6), (key2505, 6), (key2596, -6), (key2884, -6), (key2884, -6), (key2775, -6)]

theorem rawRowCheck9803 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form12 = rawRow9803 := by decide +kernel

def row9803 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9803 : row9803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9803 := by decide +kernel

theorem rowEval9803 (x : Key → ℝ) : Integer.Sparse.eval row9803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9803, Integer.Sparse.eval_collectBalanced, rawRowCheck9803]

def rawRow9804 : Integer.Sparse Key := [(key2468, 6), (key2468, 6), (key2505, 6), (key2481, 6), (key2775, -6), (key2596, -6), (key2884, -6), (key2884, -6)]

theorem rawRowCheck9804 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form12 = rawRow9804 := by decide +kernel

def row9804 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9804 : row9804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9804 := by decide +kernel

theorem rowEval9804 (x : Key → ℝ) : Integer.Sparse.eval row9804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9804, Integer.Sparse.eval_collectBalanced, rawRowCheck9804]

def rawRow9805 : Integer.Sparse Key := [(key2468, 6), (key2505, 6), (key2468, 6), (key2481, 6), (key2775, -6), (key2884, -6), (key2596, -6), (key2884, -6)]

theorem rawRowCheck9805 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form12 = rawRow9805 := by decide +kernel

def row9805 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9805 : row9805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9805 := by decide +kernel

theorem rowEval9805 (x : Key → ℝ) : Integer.Sparse.eval row9805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9805, Integer.Sparse.eval_collectBalanced, rawRowCheck9805]

def rawRow9806 : Integer.Sparse Key := [(key2505, 6), (key2468, 6), (key2468, 6), (key2481, 6), (key2775, -6), (key2884, -6), (key2884, -6), (key2596, -6)]

theorem rawRowCheck9806 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form12 = rawRow9806 := by decide +kernel

def row9806 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9806 : row9806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9806 := by decide +kernel

theorem rowEval9806 (x : Key → ℝ) : Integer.Sparse.eval row9806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9806, Integer.Sparse.eval_collectBalanced, rawRowCheck9806]

def rawRow9807 : Integer.Sparse Key := [(key2468, 6), (key2481, 6), (key2505, 6), (key2468, 6), (key2884, -6), (key2596, -6), (key2775, -6), (key2884, -6)]

theorem rawRowCheck9807 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form12 = rawRow9807 := by decide +kernel

def row9807 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9807 : row9807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9807 := by decide +kernel

theorem rowEval9807 (x : Key → ℝ) : Integer.Sparse.eval row9807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9807, Integer.Sparse.eval_collectBalanced, rawRowCheck9807]

def rawRow9808 : Integer.Sparse Key := [(key2481, 6), (key2468, 6), (key2505, 6), (key2468, 6), (key2884, -6), (key2596, -6), (key2884, -6), (key2775, -6)]

theorem rawRowCheck9808 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form12 = rawRow9808 := by decide +kernel

def row9808 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9808 : row9808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9808 := by decide +kernel

theorem rowEval9808 (x : Key → ℝ) : Integer.Sparse.eval row9808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9808, Integer.Sparse.eval_collectBalanced, rawRowCheck9808]

def rawRow9809 : Integer.Sparse Key := [(key2468, 6), (key2505, 6), (key2481, 6), (key2468, 6), (key2884, -6), (key2775, -6), (key2596, -6), (key2884, -6)]

theorem rawRowCheck9809 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form12 = rawRow9809 := by decide +kernel

def row9809 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9809 : row9809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9809 := by decide +kernel

theorem rowEval9809 (x : Key → ℝ) : Integer.Sparse.eval row9809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9809, Integer.Sparse.eval_collectBalanced, rawRowCheck9809]

def rawRow9810 : Integer.Sparse Key := [(key2505, 6), (key2468, 6), (key2481, 6), (key2468, 6), (key2884, -6), (key2775, -6), (key2884, -6), (key2596, -6)]

theorem rawRowCheck9810 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form12 = rawRow9810 := by decide +kernel

def row9810 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9810 : row9810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9810 := by decide +kernel

theorem rowEval9810 (x : Key → ℝ) : Integer.Sparse.eval row9810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9810, Integer.Sparse.eval_collectBalanced, rawRowCheck9810]

def rawRow9811 : Integer.Sparse Key := [(key2481, 6), (key2505, 6), (key2468, 6), (key2468, 6), (key2884, -6), (key2884, -6), (key2596, -6), (key2775, -6)]

theorem rawRowCheck9811 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form12 = rawRow9811 := by decide +kernel

def row9811 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9811 : row9811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9811 := by decide +kernel

theorem rowEval9811 (x : Key → ℝ) : Integer.Sparse.eval row9811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9811, Integer.Sparse.eval_collectBalanced, rawRowCheck9811]

def rawRow9812 : Integer.Sparse Key := [(key2505, 6), (key2481, 6), (key2468, 6), (key2468, 6), (key2884, -6), (key2884, -6), (key2775, -6), (key2596, -6)]

theorem rawRowCheck9812 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form12 = rawRow9812 := by decide +kernel

def row9812 : Integer.Sparse Key := [(key2468, 12), (key2481, 6), (key2505, 6), (key2596, -6), (key2775, -6), (key2884, -12)]

theorem rowCheck9812 : row9812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9812 := by decide +kernel

theorem rowEval9812 (x : Key → ℝ) : Integer.Sparse.eval row9812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck9812, Integer.Sparse.eval_collectBalanced, rawRowCheck9812]

def rawRow9813 : Integer.Sparse Key := [(key2175, -6), (key2175, -6), (key2179, -6), (key2189, -6), (key2078, 2), (key2078, 2), (key2082, 2), (key2275, 2), (key2275, 2), (key2327, 2), (key2327, 2), (key2328, 2), (key2328, 2), (key2289, 2), (key2333, 2), (key2333, 2)]

theorem rawRowCheck9813 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form13 = rawRow9813 := by decide +kernel

def row9813 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9813 : row9813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9813 := by decide +kernel

theorem rowEval9813 (x : Key → ℝ) : Integer.Sparse.eval row9813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9813, Integer.Sparse.eval_collectBalanced, rawRowCheck9813]

def rawRow9814 : Integer.Sparse Key := [(key2175, -6), (key2179, -6), (key2175, -6), (key2189, -6), (key2078, 2), (key2082, 2), (key2078, 2), (key2327, 2), (key2328, 2), (key2275, 2), (key2328, 2), (key2275, 2), (key2327, 2), (key2333, 2), (key2289, 2), (key2333, 2)]

theorem rawRowCheck9814 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form13 = rawRow9814 := by decide +kernel

def row9814 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9814 : row9814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9814 := by decide +kernel

theorem rowEval9814 (x : Key → ℝ) : Integer.Sparse.eval row9814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9814, Integer.Sparse.eval_collectBalanced, rawRowCheck9814]

def rawRow9815 : Integer.Sparse Key := [(key2179, -6), (key2175, -6), (key2175, -6), (key2189, -6), (key2082, 2), (key2078, 2), (key2078, 2), (key2328, 2), (key2327, 2), (key2328, 2), (key2275, 2), (key2327, 2), (key2275, 2), (key2333, 2), (key2333, 2), (key2289, 2)]

theorem rawRowCheck9815 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form13 = rawRow9815 := by decide +kernel

def row9815 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9815 : row9815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9815 := by decide +kernel

theorem rowEval9815 (x : Key → ℝ) : Integer.Sparse.eval row9815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9815, Integer.Sparse.eval_collectBalanced, rawRowCheck9815]

def rawRow9816 : Integer.Sparse Key := [(key2175, -6), (key2175, -6), (key2189, -6), (key2179, -6), (key2275, 2), (key2275, 2), (key2289, 2), (key2078, 2), (key2078, 2), (key2327, 2), (key2327, 2), (key2333, 2), (key2333, 2), (key2082, 2), (key2328, 2), (key2328, 2)]

theorem rawRowCheck9816 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form13 = rawRow9816 := by decide +kernel

def row9816 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9816 : row9816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9816 := by decide +kernel

theorem rowEval9816 (x : Key → ℝ) : Integer.Sparse.eval row9816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9816, Integer.Sparse.eval_collectBalanced, rawRowCheck9816]

def rawRow9817 : Integer.Sparse Key := [(key2175, -6), (key2189, -6), (key2175, -6), (key2179, -6), (key2275, 2), (key2289, 2), (key2275, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2328, 2), (key2082, 2), (key2328, 2)]

theorem rawRowCheck9817 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form13 = rawRow9817 := by decide +kernel

def row9817 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9817 : row9817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9817 := by decide +kernel

theorem rowEval9817 (x : Key → ℝ) : Integer.Sparse.eval row9817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9817, Integer.Sparse.eval_collectBalanced, rawRowCheck9817]

def rawRow9818 : Integer.Sparse Key := [(key2189, -6), (key2175, -6), (key2175, -6), (key2179, -6), (key2289, 2), (key2275, 2), (key2275, 2), (key2333, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2078, 2), (key2328, 2), (key2328, 2), (key2082, 2)]

theorem rawRowCheck9818 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form13 = rawRow9818 := by decide +kernel

def row9818 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9818 : row9818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9818 := by decide +kernel

theorem rowEval9818 (x : Key → ℝ) : Integer.Sparse.eval row9818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9818, Integer.Sparse.eval_collectBalanced, rawRowCheck9818]

def rawRow9819 : Integer.Sparse Key := [(key2175, -6), (key2179, -6), (key2189, -6), (key2175, -6), (key2327, 2), (key2328, 2), (key2333, 2), (key2078, 2), (key2082, 2), (key2275, 2), (key2328, 2), (key2289, 2), (key2333, 2), (key2078, 2), (key2275, 2), (key2327, 2)]

theorem rawRowCheck9819 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form13 = rawRow9819 := by decide +kernel

def row9819 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9819 : row9819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9819 := by decide +kernel

theorem rowEval9819 (x : Key → ℝ) : Integer.Sparse.eval row9819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9819, Integer.Sparse.eval_collectBalanced, rawRowCheck9819]

def rawRow9820 : Integer.Sparse Key := [(key2179, -6), (key2175, -6), (key2189, -6), (key2175, -6), (key2328, 2), (key2327, 2), (key2333, 2), (key2082, 2), (key2078, 2), (key2328, 2), (key2275, 2), (key2333, 2), (key2289, 2), (key2078, 2), (key2327, 2), (key2275, 2)]

theorem rawRowCheck9820 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form13 = rawRow9820 := by decide +kernel

def row9820 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9820 : row9820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9820 := by decide +kernel

theorem rowEval9820 (x : Key → ℝ) : Integer.Sparse.eval row9820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9820, Integer.Sparse.eval_collectBalanced, rawRowCheck9820]

def rawRow9821 : Integer.Sparse Key := [(key2175, -6), (key2189, -6), (key2179, -6), (key2175, -6), (key2327, 2), (key2333, 2), (key2328, 2), (key2275, 2), (key2289, 2), (key2078, 2), (key2333, 2), (key2082, 2), (key2328, 2), (key2275, 2), (key2078, 2), (key2327, 2)]

theorem rawRowCheck9821 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form13 = rawRow9821 := by decide +kernel

def row9821 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9821 : row9821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9821 := by decide +kernel

theorem rowEval9821 (x : Key → ℝ) : Integer.Sparse.eval row9821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9821, Integer.Sparse.eval_collectBalanced, rawRowCheck9821]

def rawRow9822 : Integer.Sparse Key := [(key2189, -6), (key2175, -6), (key2179, -6), (key2175, -6), (key2333, 2), (key2327, 2), (key2328, 2), (key2289, 2), (key2275, 2), (key2333, 2), (key2078, 2), (key2328, 2), (key2082, 2), (key2275, 2), (key2327, 2), (key2078, 2)]

theorem rawRowCheck9822 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form13 = rawRow9822 := by decide +kernel

def row9822 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9822 : row9822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9822 := by decide +kernel

theorem rowEval9822 (x : Key → ℝ) : Integer.Sparse.eval row9822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9822, Integer.Sparse.eval_collectBalanced, rawRowCheck9822]

def rawRow9823 : Integer.Sparse Key := [(key2179, -6), (key2189, -6), (key2175, -6), (key2175, -6), (key2328, 2), (key2333, 2), (key2327, 2), (key2328, 2), (key2333, 2), (key2082, 2), (key2289, 2), (key2078, 2), (key2275, 2), (key2327, 2), (key2078, 2), (key2275, 2)]

theorem rawRowCheck9823 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form13 = rawRow9823 := by decide +kernel

def row9823 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9823 : row9823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9823 := by decide +kernel

theorem rowEval9823 (x : Key → ℝ) : Integer.Sparse.eval row9823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9823, Integer.Sparse.eval_collectBalanced, rawRowCheck9823]

def rawRow9824 : Integer.Sparse Key := [(key2189, -6), (key2179, -6), (key2175, -6), (key2175, -6), (key2333, 2), (key2328, 2), (key2327, 2), (key2333, 2), (key2328, 2), (key2289, 2), (key2082, 2), (key2275, 2), (key2078, 2), (key2327, 2), (key2275, 2), (key2078, 2)]

theorem rawRowCheck9824 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form13 = rawRow9824 := by decide +kernel

def row9824 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2175, -12), (key2179, -6), (key2189, -6), (key2275, 4), (key2289, 2), (key2327, 4), (key2328, 4), (key2333, 4)]

theorem rowCheck9824 : row9824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9824 := by decide +kernel

theorem rowEval9824 (x : Key → ℝ) : Integer.Sparse.eval row9824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9824, Integer.Sparse.eval_collectBalanced, rawRowCheck9824]

def rawRow9825 : Integer.Sparse Key := [(key2275, -6), (key2275, -6), (key2281, -6), (key2289, -6), (key2078, 2), (key2078, 2), (key2087, 2), (key2175, 2), (key2175, 2), (key2327, 2), (key2327, 2), (key2330, 2), (key2330, 2), (key2189, 2), (key2333, 2), (key2333, 2)]

theorem rawRowCheck9825 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form13 = rawRow9825 := by decide +kernel

def row9825 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9825 : row9825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9825 := by decide +kernel

theorem rowEval9825 (x : Key → ℝ) : Integer.Sparse.eval row9825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9825, Integer.Sparse.eval_collectBalanced, rawRowCheck9825]

def rawRow9826 : Integer.Sparse Key := [(key2275, -6), (key2281, -6), (key2275, -6), (key2289, -6), (key2078, 2), (key2087, 2), (key2078, 2), (key2327, 2), (key2330, 2), (key2175, 2), (key2330, 2), (key2175, 2), (key2327, 2), (key2333, 2), (key2189, 2), (key2333, 2)]

theorem rawRowCheck9826 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form13 = rawRow9826 := by decide +kernel

def row9826 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9826 : row9826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9826 := by decide +kernel

theorem rowEval9826 (x : Key → ℝ) : Integer.Sparse.eval row9826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9826, Integer.Sparse.eval_collectBalanced, rawRowCheck9826]

def rawRow9827 : Integer.Sparse Key := [(key2281, -6), (key2275, -6), (key2275, -6), (key2289, -6), (key2087, 2), (key2078, 2), (key2078, 2), (key2330, 2), (key2327, 2), (key2330, 2), (key2175, 2), (key2327, 2), (key2175, 2), (key2333, 2), (key2333, 2), (key2189, 2)]

theorem rawRowCheck9827 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form13 = rawRow9827 := by decide +kernel

def row9827 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9827 : row9827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9827 := by decide +kernel

theorem rowEval9827 (x : Key → ℝ) : Integer.Sparse.eval row9827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9827, Integer.Sparse.eval_collectBalanced, rawRowCheck9827]

def rawRow9828 : Integer.Sparse Key := [(key2275, -6), (key2275, -6), (key2289, -6), (key2281, -6), (key2175, 2), (key2175, 2), (key2189, 2), (key2078, 2), (key2078, 2), (key2327, 2), (key2327, 2), (key2333, 2), (key2333, 2), (key2087, 2), (key2330, 2), (key2330, 2)]

theorem rawRowCheck9828 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form13 = rawRow9828 := by decide +kernel

def row9828 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9828 : row9828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9828 := by decide +kernel

theorem rowEval9828 (x : Key → ℝ) : Integer.Sparse.eval row9828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9828, Integer.Sparse.eval_collectBalanced, rawRowCheck9828]

def rawRow9829 : Integer.Sparse Key := [(key2275, -6), (key2289, -6), (key2275, -6), (key2281, -6), (key2175, 2), (key2189, 2), (key2175, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2330, 2), (key2087, 2), (key2330, 2)]

theorem rawRowCheck9829 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form13 = rawRow9829 := by decide +kernel

def row9829 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9829 : row9829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9829 := by decide +kernel

theorem rowEval9829 (x : Key → ℝ) : Integer.Sparse.eval row9829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9829, Integer.Sparse.eval_collectBalanced, rawRowCheck9829]

def rawRow9830 : Integer.Sparse Key := [(key2289, -6), (key2275, -6), (key2275, -6), (key2281, -6), (key2189, 2), (key2175, 2), (key2175, 2), (key2333, 2), (key2327, 2), (key2333, 2), (key2078, 2), (key2327, 2), (key2078, 2), (key2330, 2), (key2330, 2), (key2087, 2)]

theorem rawRowCheck9830 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form13 = rawRow9830 := by decide +kernel

def row9830 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9830 : row9830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9830 := by decide +kernel

theorem rowEval9830 (x : Key → ℝ) : Integer.Sparse.eval row9830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9830, Integer.Sparse.eval_collectBalanced, rawRowCheck9830]

def rawRow9831 : Integer.Sparse Key := [(key2275, -6), (key2281, -6), (key2289, -6), (key2275, -6), (key2327, 2), (key2330, 2), (key2333, 2), (key2078, 2), (key2087, 2), (key2175, 2), (key2330, 2), (key2189, 2), (key2333, 2), (key2078, 2), (key2175, 2), (key2327, 2)]

theorem rawRowCheck9831 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form13 = rawRow9831 := by decide +kernel

def row9831 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9831 : row9831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9831 := by decide +kernel

theorem rowEval9831 (x : Key → ℝ) : Integer.Sparse.eval row9831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9831, Integer.Sparse.eval_collectBalanced, rawRowCheck9831]

def rawRow9832 : Integer.Sparse Key := [(key2281, -6), (key2275, -6), (key2289, -6), (key2275, -6), (key2330, 2), (key2327, 2), (key2333, 2), (key2087, 2), (key2078, 2), (key2330, 2), (key2175, 2), (key2333, 2), (key2189, 2), (key2078, 2), (key2327, 2), (key2175, 2)]

theorem rawRowCheck9832 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form13 = rawRow9832 := by decide +kernel

def row9832 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9832 : row9832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9832 := by decide +kernel

theorem rowEval9832 (x : Key → ℝ) : Integer.Sparse.eval row9832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9832, Integer.Sparse.eval_collectBalanced, rawRowCheck9832]

def rawRow9833 : Integer.Sparse Key := [(key2275, -6), (key2289, -6), (key2281, -6), (key2275, -6), (key2327, 2), (key2333, 2), (key2330, 2), (key2175, 2), (key2189, 2), (key2078, 2), (key2333, 2), (key2087, 2), (key2330, 2), (key2175, 2), (key2078, 2), (key2327, 2)]

theorem rawRowCheck9833 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form13 = rawRow9833 := by decide +kernel

def row9833 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9833 : row9833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9833 := by decide +kernel

theorem rowEval9833 (x : Key → ℝ) : Integer.Sparse.eval row9833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9833, Integer.Sparse.eval_collectBalanced, rawRowCheck9833]

def rawRow9834 : Integer.Sparse Key := [(key2289, -6), (key2275, -6), (key2281, -6), (key2275, -6), (key2333, 2), (key2327, 2), (key2330, 2), (key2189, 2), (key2175, 2), (key2333, 2), (key2078, 2), (key2330, 2), (key2087, 2), (key2175, 2), (key2327, 2), (key2078, 2)]

theorem rawRowCheck9834 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form13 = rawRow9834 := by decide +kernel

def row9834 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9834 : row9834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9834 := by decide +kernel

theorem rowEval9834 (x : Key → ℝ) : Integer.Sparse.eval row9834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9834, Integer.Sparse.eval_collectBalanced, rawRowCheck9834]

def rawRow9835 : Integer.Sparse Key := [(key2281, -6), (key2289, -6), (key2275, -6), (key2275, -6), (key2330, 2), (key2333, 2), (key2327, 2), (key2330, 2), (key2333, 2), (key2087, 2), (key2189, 2), (key2078, 2), (key2175, 2), (key2327, 2), (key2078, 2), (key2175, 2)]

theorem rawRowCheck9835 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form13 = rawRow9835 := by decide +kernel

def row9835 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9835 : row9835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9835 := by decide +kernel

theorem rowEval9835 (x : Key → ℝ) : Integer.Sparse.eval row9835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9835, Integer.Sparse.eval_collectBalanced, rawRowCheck9835]

def rawRow9836 : Integer.Sparse Key := [(key2289, -6), (key2281, -6), (key2275, -6), (key2275, -6), (key2333, 2), (key2330, 2), (key2327, 2), (key2333, 2), (key2330, 2), (key2189, 2), (key2087, 2), (key2175, 2), (key2078, 2), (key2327, 2), (key2175, 2), (key2078, 2)]

theorem rawRowCheck9836 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form13 = rawRow9836 := by decide +kernel

def row9836 : Integer.Sparse Key := [(key2078, 4), (key2087, 2), (key2175, 4), (key2189, 2), (key2275, -12), (key2281, -6), (key2289, -6), (key2327, 4), (key2330, 4), (key2333, 4)]

theorem rowCheck9836 : row9836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9836 := by decide +kernel

theorem rowEval9836 (x : Key → ℝ) : Integer.Sparse.eval row9836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9836, Integer.Sparse.eval_collectBalanced, rawRowCheck9836]

def rawRow9837 : Integer.Sparse Key := [(key1033, 6), (key1033, 6), (key1041, 6), (key1076, 6), (key1019, -6), (key1127, -6), (key1199, -6), (key1199, -6)]

theorem rawRowCheck9837 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form14 = rawRow9837 := by decide +kernel

def row9837 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9837 : row9837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9837 := by decide +kernel

theorem rowEval9837 (x : Key → ℝ) : Integer.Sparse.eval row9837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9837, Integer.Sparse.eval_collectBalanced, rawRowCheck9837]

def rawRow9838 : Integer.Sparse Key := [(key1033, 6), (key1041, 6), (key1033, 6), (key1076, 6), (key1019, -6), (key1199, -6), (key1127, -6), (key1199, -6)]

theorem rawRowCheck9838 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form14 = rawRow9838 := by decide +kernel

def row9838 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9838 : row9838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9838 := by decide +kernel

theorem rowEval9838 (x : Key → ℝ) : Integer.Sparse.eval row9838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9838, Integer.Sparse.eval_collectBalanced, rawRowCheck9838]

def rawRow9839 : Integer.Sparse Key := [(key1041, 6), (key1033, 6), (key1033, 6), (key1076, 6), (key1019, -6), (key1199, -6), (key1199, -6), (key1127, -6)]

theorem rawRowCheck9839 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form14 = rawRow9839 := by decide +kernel

def row9839 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9839 : row9839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9839 := by decide +kernel

theorem rowEval9839 (x : Key → ℝ) : Integer.Sparse.eval row9839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9839, Integer.Sparse.eval_collectBalanced, rawRowCheck9839]

def rawRow9840 : Integer.Sparse Key := [(key1033, 6), (key1033, 6), (key1076, 6), (key1041, 6), (key1127, -6), (key1019, -6), (key1199, -6), (key1199, -6)]

theorem rawRowCheck9840 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form14 = rawRow9840 := by decide +kernel

def row9840 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9840 : row9840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9840 := by decide +kernel

theorem rowEval9840 (x : Key → ℝ) : Integer.Sparse.eval row9840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9840, Integer.Sparse.eval_collectBalanced, rawRowCheck9840]

def rawRow9841 : Integer.Sparse Key := [(key1033, 6), (key1076, 6), (key1033, 6), (key1041, 6), (key1127, -6), (key1199, -6), (key1019, -6), (key1199, -6)]

theorem rawRowCheck9841 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form14 = rawRow9841 := by decide +kernel

def row9841 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9841 : row9841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9841 := by decide +kernel

theorem rowEval9841 (x : Key → ℝ) : Integer.Sparse.eval row9841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9841, Integer.Sparse.eval_collectBalanced, rawRowCheck9841]

def rawRow9842 : Integer.Sparse Key := [(key1076, 6), (key1033, 6), (key1033, 6), (key1041, 6), (key1127, -6), (key1199, -6), (key1199, -6), (key1019, -6)]

theorem rawRowCheck9842 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form14 = rawRow9842 := by decide +kernel

def row9842 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9842 : row9842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9842 := by decide +kernel

theorem rowEval9842 (x : Key → ℝ) : Integer.Sparse.eval row9842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9842, Integer.Sparse.eval_collectBalanced, rawRowCheck9842]

def rawRow9843 : Integer.Sparse Key := [(key1033, 6), (key1041, 6), (key1076, 6), (key1033, 6), (key1199, -6), (key1019, -6), (key1127, -6), (key1199, -6)]

theorem rawRowCheck9843 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form14 = rawRow9843 := by decide +kernel

def row9843 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9843 : row9843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9843 := by decide +kernel

theorem rowEval9843 (x : Key → ℝ) : Integer.Sparse.eval row9843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9843, Integer.Sparse.eval_collectBalanced, rawRowCheck9843]

def rawRow9844 : Integer.Sparse Key := [(key1041, 6), (key1033, 6), (key1076, 6), (key1033, 6), (key1199, -6), (key1019, -6), (key1199, -6), (key1127, -6)]

theorem rawRowCheck9844 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form14 = rawRow9844 := by decide +kernel

def row9844 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9844 : row9844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9844 := by decide +kernel

theorem rowEval9844 (x : Key → ℝ) : Integer.Sparse.eval row9844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9844, Integer.Sparse.eval_collectBalanced, rawRowCheck9844]

def rawRow9845 : Integer.Sparse Key := [(key1033, 6), (key1076, 6), (key1041, 6), (key1033, 6), (key1199, -6), (key1127, -6), (key1019, -6), (key1199, -6)]

theorem rawRowCheck9845 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form14 = rawRow9845 := by decide +kernel

def row9845 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9845 : row9845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9845 := by decide +kernel

theorem rowEval9845 (x : Key → ℝ) : Integer.Sparse.eval row9845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9845, Integer.Sparse.eval_collectBalanced, rawRowCheck9845]

def rawRow9846 : Integer.Sparse Key := [(key1076, 6), (key1033, 6), (key1041, 6), (key1033, 6), (key1199, -6), (key1127, -6), (key1199, -6), (key1019, -6)]

theorem rawRowCheck9846 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form14 = rawRow9846 := by decide +kernel

def row9846 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9846 : row9846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9846 := by decide +kernel

theorem rowEval9846 (x : Key → ℝ) : Integer.Sparse.eval row9846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9846, Integer.Sparse.eval_collectBalanced, rawRowCheck9846]

def rawRow9847 : Integer.Sparse Key := [(key1041, 6), (key1076, 6), (key1033, 6), (key1033, 6), (key1199, -6), (key1199, -6), (key1019, -6), (key1127, -6)]

theorem rawRowCheck9847 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form14 = rawRow9847 := by decide +kernel

def row9847 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9847 : row9847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9847 := by decide +kernel

theorem rowEval9847 (x : Key → ℝ) : Integer.Sparse.eval row9847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9847, Integer.Sparse.eval_collectBalanced, rawRowCheck9847]

def rawRow9848 : Integer.Sparse Key := [(key1076, 6), (key1041, 6), (key1033, 6), (key1033, 6), (key1199, -6), (key1199, -6), (key1127, -6), (key1019, -6)]

theorem rawRowCheck9848 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form14 = rawRow9848 := by decide +kernel

def row9848 : Integer.Sparse Key := [(key1019, -6), (key1033, 12), (key1041, 6), (key1076, 6), (key1127, -6), (key1199, -12)]

theorem rowCheck9848 : row9848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9848 := by decide +kernel

theorem rowEval9848 (x : Key → ℝ) : Integer.Sparse.eval row9848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9848, Integer.Sparse.eval_collectBalanced, rawRowCheck9848]

def rawRow9849 : Integer.Sparse Key := [(key1111, 6), (key1111, 6), (key1127, 6), (key1155, 6), (key1006, -6), (key1041, -6), (key1193, -6), (key1193, -6)]

theorem rawRowCheck9849 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form14 = rawRow9849 := by decide +kernel

def row9849 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9849 : row9849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9849 := by decide +kernel

theorem rowEval9849 (x : Key → ℝ) : Integer.Sparse.eval row9849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9849, Integer.Sparse.eval_collectBalanced, rawRowCheck9849]

def rawRow9850 : Integer.Sparse Key := [(key1111, 6), (key1127, 6), (key1111, 6), (key1155, 6), (key1006, -6), (key1193, -6), (key1041, -6), (key1193, -6)]

theorem rawRowCheck9850 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form14 = rawRow9850 := by decide +kernel

def row9850 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9850 : row9850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9850 := by decide +kernel

theorem rowEval9850 (x : Key → ℝ) : Integer.Sparse.eval row9850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9850, Integer.Sparse.eval_collectBalanced, rawRowCheck9850]

def rawRow9851 : Integer.Sparse Key := [(key1127, 6), (key1111, 6), (key1111, 6), (key1155, 6), (key1006, -6), (key1193, -6), (key1193, -6), (key1041, -6)]

theorem rawRowCheck9851 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form14 = rawRow9851 := by decide +kernel

def row9851 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9851 : row9851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9851 := by decide +kernel

theorem rowEval9851 (x : Key → ℝ) : Integer.Sparse.eval row9851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9851, Integer.Sparse.eval_collectBalanced, rawRowCheck9851]

def rawRow9852 : Integer.Sparse Key := [(key1111, 6), (key1111, 6), (key1155, 6), (key1127, 6), (key1041, -6), (key1006, -6), (key1193, -6), (key1193, -6)]

theorem rawRowCheck9852 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form14 = rawRow9852 := by decide +kernel

def row9852 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9852 : row9852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9852 := by decide +kernel

theorem rowEval9852 (x : Key → ℝ) : Integer.Sparse.eval row9852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9852, Integer.Sparse.eval_collectBalanced, rawRowCheck9852]

def rawRow9853 : Integer.Sparse Key := [(key1111, 6), (key1155, 6), (key1111, 6), (key1127, 6), (key1041, -6), (key1193, -6), (key1006, -6), (key1193, -6)]

theorem rawRowCheck9853 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form14 = rawRow9853 := by decide +kernel

def row9853 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9853 : row9853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9853 := by decide +kernel

theorem rowEval9853 (x : Key → ℝ) : Integer.Sparse.eval row9853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9853, Integer.Sparse.eval_collectBalanced, rawRowCheck9853]

def rawRow9854 : Integer.Sparse Key := [(key1155, 6), (key1111, 6), (key1111, 6), (key1127, 6), (key1041, -6), (key1193, -6), (key1193, -6), (key1006, -6)]

theorem rawRowCheck9854 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form14 = rawRow9854 := by decide +kernel

def row9854 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9854 : row9854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9854 := by decide +kernel

theorem rowEval9854 (x : Key → ℝ) : Integer.Sparse.eval row9854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9854, Integer.Sparse.eval_collectBalanced, rawRowCheck9854]

def rawRow9855 : Integer.Sparse Key := [(key1111, 6), (key1127, 6), (key1155, 6), (key1111, 6), (key1193, -6), (key1006, -6), (key1041, -6), (key1193, -6)]

theorem rawRowCheck9855 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form14 = rawRow9855 := by decide +kernel

def row9855 : Integer.Sparse Key := [(key1006, -6), (key1041, -6), (key1111, 12), (key1127, 6), (key1155, 6), (key1193, -12)]

theorem rowCheck9855 : row9855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9855 := by decide +kernel

theorem rowEval9855 (x : Key → ℝ) : Integer.Sparse.eval row9855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9855, Integer.Sparse.eval_collectBalanced, rawRowCheck9855]

end MUB6.Certificate.GramRows

end OAI
