import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow5760 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2860, 2), (key2898, -1), (key2977, -1), (key2738, 2), (key2951, 2), (key2706, -1), (key2809, -1), (key2860, 2), (key2706, -1), (key2809, -1), (key2905, 1), (key2984, 1), (key2870, -2), (key2905, 1), (key2984, 1), (key2649, -2), (key2939, -2), (key2632, 1), (key2786, 1), (key2870, -2), (key2632, 1), (key2786, 1), (key2748, -1), (key2961, -1), (key2726, 1), (key2829, 1), (key2654, 1), (key2944, 1), (key2640, -1), (key2794, -1), (key2748, -1), (key2961, -1), (key2654, 1), (key2944, 1), (key2726, 1), (key2829, 1), (key2640, -1), (key2794, -1)]

theorem rawRowCheck5760 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form2 = rawRow5760 := by decide +kernel

def row5760 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck5760 : row5760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5760 := by decide +kernel

theorem rowEval5760 (x : Key → ℝ) : Integer.Sparse.eval row5760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5760, Integer.Sparse.eval_collectBalanced, rawRowCheck5760]

def rawRow5761 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2860, 2), (key2977, -1), (key2898, -1), (key2951, 2), (key2738, 2), (key2809, -1), (key2706, -1), (key2860, 2), (key2809, -1), (key2706, -1), (key2984, 1), (key2905, 1), (key2870, -2), (key2984, 1), (key2905, 1), (key2939, -2), (key2649, -2), (key2786, 1), (key2632, 1), (key2870, -2), (key2786, 1), (key2632, 1), (key2961, -1), (key2748, -1), (key2829, 1), (key2726, 1), (key2944, 1), (key2654, 1), (key2794, -1), (key2640, -1), (key2961, -1), (key2748, -1), (key2944, 1), (key2654, 1), (key2829, 1), (key2726, 1), (key2794, -1), (key2640, -1)]

theorem rawRowCheck5761 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form2 = rawRow5761 := by decide +kernel

def row5761 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck5761 : row5761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5761 := by decide +kernel

theorem rowEval5761 (x : Key → ℝ) : Integer.Sparse.eval row5761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5761, Integer.Sparse.eval_collectBalanced, rawRowCheck5761]

def rawRow5762 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2748, 2), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2961, 2), (key2984, -1), (key2992, -1), (key2640, 1), (key2642, 1), (key2654, -2), (key2794, 1), (key2796, 1), (key2860, -2), (key2883, -2), (key2898, 1), (key2913, 1), (key2944, -2), (key2977, 1), (key2992, 1), (key2632, -1), (key2642, -1), (key2649, 1), (key2654, 1), (key2706, 1), (key2729, 1), (key2738, -1), (key2748, -1), (key2786, -1), (key2796, -1), (key2809, 1), (key2832, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1)]

theorem rawRowCheck5762 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form2 = rawRow5762 := by decide +kernel

def row5762 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5762 : row5762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5762 := by decide +kernel

theorem rowEval5762 (x : Key → ℝ) : Integer.Sparse.eval row5762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5762, Integer.Sparse.eval_collectBalanced, rawRowCheck5762]

def rawRow5763 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2748, 2), (key2832, -1), (key2829, -1), (key2883, 2), (key2870, 2), (key2913, -1), (key2905, -1), (key2961, 2), (key2992, -1), (key2984, -1), (key2642, 1), (key2640, 1), (key2654, -2), (key2796, 1), (key2794, 1), (key2883, -2), (key2860, -2), (key2913, 1), (key2898, 1), (key2944, -2), (key2992, 1), (key2977, 1), (key2642, -1), (key2632, -1), (key2654, 1), (key2649, 1), (key2729, 1), (key2706, 1), (key2748, -1), (key2738, -1), (key2796, -1), (key2786, -1), (key2832, 1), (key2809, 1), (key2944, 1), (key2939, 1), (key2961, -1), (key2951, -1)]

theorem rawRowCheck5763 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form2 = rawRow5763 := by decide +kernel

def row5763 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5763 : row5763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5763 := by decide +kernel

theorem rowEval5763 (x : Key → ℝ) : Integer.Sparse.eval row5763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5763, Integer.Sparse.eval_collectBalanced, rawRowCheck5763]

def rawRow5764 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2729, 2), (key2870, -1), (key2905, -1), (key2829, 2), (key2913, 2), (key2832, -1), (key2883, -1), (key2984, 2), (key2961, -1), (key2992, -1), (key2640, 1), (key2654, 1), (key2642, -2), (key2860, 1), (key2898, 1), (key2794, -2), (key2913, -2), (key2796, 1), (key2883, 1), (key2977, -2), (key2944, 1), (key2992, 1), (key2616, -1), (key2654, -1), (key2619, 1), (key2642, 1), (key2671, 1), (key2748, 1), (key2674, -1), (key2729, -1), (key2809, -1), (key2898, -1), (key2786, 1), (key2905, 1), (key2951, 1), (key2977, 1), (key2939, -1), (key2984, -1)]

theorem rawRowCheck5764 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form2 = rawRow5764 := by decide +kernel

def row5764 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5764 : row5764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5764 := by decide +kernel

theorem rowEval5764 (x : Key → ℝ) : Integer.Sparse.eval row5764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5764, Integer.Sparse.eval_collectBalanced, rawRowCheck5764]

def rawRow5765 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2729, 2), (key2905, -1), (key2870, -1), (key2913, 2), (key2829, 2), (key2883, -1), (key2832, -1), (key2984, 2), (key2992, -1), (key2961, -1), (key2654, 1), (key2640, 1), (key2642, -2), (key2898, 1), (key2860, 1), (key2913, -2), (key2794, -2), (key2883, 1), (key2796, 1), (key2977, -2), (key2992, 1), (key2944, 1), (key2654, -1), (key2616, -1), (key2642, 1), (key2619, 1), (key2748, 1), (key2671, 1), (key2729, -1), (key2674, -1), (key2898, -1), (key2809, -1), (key2905, 1), (key2786, 1), (key2977, 1), (key2951, 1), (key2984, -1), (key2939, -1)]

theorem rawRowCheck5765 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form2 = rawRow5765 := by decide +kernel

def row5765 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5765 : row5765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5765 := by decide +kernel

theorem rowEval5765 (x : Key → ℝ) : Integer.Sparse.eval row5765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5765, Integer.Sparse.eval_collectBalanced, rawRowCheck5765]

def rawRow5766 : Integer.Sparse Key := [(key2829, -1), (key2832, -1), (key2961, 2), (key2726, -1), (key2729, -1), (key2870, 2), (key2883, 2), (key2984, -1), (key2992, -1), (key2748, 2), (key2905, -1), (key2913, -1), (key2794, 1), (key2796, 1), (key2944, -2), (key2640, 1), (key2642, 1), (key2860, -2), (key2883, -2), (key2977, 1), (key2992, 1), (key2654, -2), (key2898, 1), (key2913, 1), (key2786, -1), (key2796, -1), (key2939, 1), (key2944, 1), (key2809, 1), (key2832, 1), (key2951, -1), (key2961, -1), (key2632, -1), (key2642, -1), (key2706, 1), (key2729, 1), (key2649, 1), (key2654, 1), (key2738, -1), (key2748, -1)]

theorem rawRowCheck5766 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form2 = rawRow5766 := by decide +kernel

def row5766 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5766 : row5766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5766 := by decide +kernel

theorem rowEval5766 (x : Key → ℝ) : Integer.Sparse.eval row5766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5766, Integer.Sparse.eval_collectBalanced, rawRowCheck5766]

def rawRow5767 : Integer.Sparse Key := [(key2832, -1), (key2829, -1), (key2961, 2), (key2729, -1), (key2726, -1), (key2883, 2), (key2870, 2), (key2992, -1), (key2984, -1), (key2748, 2), (key2913, -1), (key2905, -1), (key2796, 1), (key2794, 1), (key2944, -2), (key2642, 1), (key2640, 1), (key2883, -2), (key2860, -2), (key2992, 1), (key2977, 1), (key2654, -2), (key2913, 1), (key2898, 1), (key2796, -1), (key2786, -1), (key2944, 1), (key2939, 1), (key2832, 1), (key2809, 1), (key2961, -1), (key2951, -1), (key2642, -1), (key2632, -1), (key2729, 1), (key2706, 1), (key2654, 1), (key2649, 1), (key2748, -1), (key2738, -1)]

theorem rawRowCheck5767 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form2 = rawRow5767 := by decide +kernel

def row5767 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5767 : row5767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5767 := by decide +kernel

theorem rowEval5767 (x : Key → ℝ) : Integer.Sparse.eval row5767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5767, Integer.Sparse.eval_collectBalanced, rawRowCheck5767]

def rawRow5768 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2829, 2), (key2883, -1), (key2992, -1), (key2729, 2), (key2984, 2), (key2726, -1), (key2870, -1), (key2913, 2), (key2748, -1), (key2905, -1), (key2796, 1), (key2944, 1), (key2794, -2), (key2883, 1), (key2992, 1), (key2642, -2), (key2977, -2), (key2640, 1), (key2860, 1), (key2913, -2), (key2654, 1), (key2898, 1), (key2674, -1), (key2939, -1), (key2671, 1), (key2786, 1), (key2619, 1), (key2951, 1), (key2616, -1), (key2809, -1), (key2729, -1), (key2984, -1), (key2642, 1), (key2977, 1), (key2748, 1), (key2905, 1), (key2654, -1), (key2898, -1)]

theorem rawRowCheck5768 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form2 = rawRow5768 := by decide +kernel

def row5768 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5768 : row5768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5768 := by decide +kernel

theorem rowEval5768 (x : Key → ℝ) : Integer.Sparse.eval row5768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5768, Integer.Sparse.eval_collectBalanced, rawRowCheck5768]

def rawRow5769 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2829, 2), (key2992, -1), (key2883, -1), (key2984, 2), (key2729, 2), (key2870, -1), (key2726, -1), (key2913, 2), (key2905, -1), (key2748, -1), (key2944, 1), (key2796, 1), (key2794, -2), (key2992, 1), (key2883, 1), (key2977, -2), (key2642, -2), (key2860, 1), (key2640, 1), (key2913, -2), (key2898, 1), (key2654, 1), (key2939, -1), (key2674, -1), (key2786, 1), (key2671, 1), (key2951, 1), (key2619, 1), (key2809, -1), (key2616, -1), (key2984, -1), (key2729, -1), (key2977, 1), (key2642, 1), (key2905, 1), (key2748, 1), (key2898, -1), (key2654, -1)]

theorem rawRowCheck5769 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form2 = rawRow5769 := by decide +kernel

def row5769 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5769 : row5769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5769 := by decide +kernel

theorem rowEval5769 (x : Key → ℝ) : Integer.Sparse.eval row5769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5769, Integer.Sparse.eval_collectBalanced, rawRowCheck5769]

def rawRow5770 : Integer.Sparse Key := [(key2870, -1), (key2905, -1), (key2984, 2), (key2726, -1), (key2748, -1), (key2829, 2), (key2913, 2), (key2961, -1), (key2992, -1), (key2729, 2), (key2832, -1), (key2883, -1), (key2860, 1), (key2898, 1), (key2977, -2), (key2640, 1), (key2654, 1), (key2794, -2), (key2913, -2), (key2944, 1), (key2992, 1), (key2642, -2), (key2796, 1), (key2883, 1), (key2809, -1), (key2898, -1), (key2951, 1), (key2977, 1), (key2786, 1), (key2905, 1), (key2939, -1), (key2984, -1), (key2616, -1), (key2654, -1), (key2671, 1), (key2748, 1), (key2619, 1), (key2642, 1), (key2674, -1), (key2729, -1)]

theorem rawRowCheck5770 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form2 = rawRow5770 := by decide +kernel

def row5770 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5770 : row5770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5770 := by decide +kernel

theorem rowEval5770 (x : Key → ℝ) : Integer.Sparse.eval row5770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5770, Integer.Sparse.eval_collectBalanced, rawRowCheck5770]

def rawRow5771 : Integer.Sparse Key := [(key2905, -1), (key2870, -1), (key2984, 2), (key2748, -1), (key2726, -1), (key2913, 2), (key2829, 2), (key2992, -1), (key2961, -1), (key2729, 2), (key2883, -1), (key2832, -1), (key2898, 1), (key2860, 1), (key2977, -2), (key2654, 1), (key2640, 1), (key2913, -2), (key2794, -2), (key2992, 1), (key2944, 1), (key2642, -2), (key2883, 1), (key2796, 1), (key2898, -1), (key2809, -1), (key2977, 1), (key2951, 1), (key2905, 1), (key2786, 1), (key2984, -1), (key2939, -1), (key2654, -1), (key2616, -1), (key2748, 1), (key2671, 1), (key2642, 1), (key2619, 1), (key2729, -1), (key2674, -1)]

theorem rawRowCheck5771 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form2 = rawRow5771 := by decide +kernel

def row5771 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5771 : row5771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5771 := by decide +kernel

theorem rowEval5771 (x : Key → ℝ) : Integer.Sparse.eval row5771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5771, Integer.Sparse.eval_collectBalanced, rawRowCheck5771]

def rawRow5772 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2870, 2), (key2913, -1), (key2992, -1), (key2748, 2), (key2961, 2), (key2726, -1), (key2829, -1), (key2883, 2), (key2729, -1), (key2832, -1), (key2898, 1), (key2977, 1), (key2860, -2), (key2913, 1), (key2992, 1), (key2654, -2), (key2944, -2), (key2640, 1), (key2794, 1), (key2883, -2), (key2642, 1), (key2796, 1), (key2738, -1), (key2951, -1), (key2706, 1), (key2809, 1), (key2649, 1), (key2939, 1), (key2632, -1), (key2786, -1), (key2748, -1), (key2961, -1), (key2654, 1), (key2944, 1), (key2729, 1), (key2832, 1), (key2642, -1), (key2796, -1)]

theorem rawRowCheck5772 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form2 = rawRow5772 := by decide +kernel

def row5772 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5772 : row5772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5772 := by decide +kernel

theorem rowEval5772 (x : Key → ℝ) : Integer.Sparse.eval row5772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5772, Integer.Sparse.eval_collectBalanced, rawRowCheck5772]

def rawRow5773 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2870, 2), (key2992, -1), (key2913, -1), (key2961, 2), (key2748, 2), (key2829, -1), (key2726, -1), (key2883, 2), (key2832, -1), (key2729, -1), (key2977, 1), (key2898, 1), (key2860, -2), (key2992, 1), (key2913, 1), (key2944, -2), (key2654, -2), (key2794, 1), (key2640, 1), (key2883, -2), (key2796, 1), (key2642, 1), (key2951, -1), (key2738, -1), (key2809, 1), (key2706, 1), (key2939, 1), (key2649, 1), (key2786, -1), (key2632, -1), (key2961, -1), (key2748, -1), (key2944, 1), (key2654, 1), (key2832, 1), (key2729, 1), (key2796, -1), (key2642, -1)]

theorem rawRowCheck5773 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form2 = rawRow5773 := by decide +kernel

def row5773 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5773 : row5773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5773 := by decide +kernel

theorem rowEval5773 (x : Key → ℝ) : Integer.Sparse.eval row5773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5773, Integer.Sparse.eval_collectBalanced, rawRowCheck5773]

def rawRow5774 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2913, 2), (key2832, -1), (key2961, -1), (key2729, 2), (key2984, 2), (key2748, -1), (key2905, -1), (key2829, 2), (key2726, -1), (key2870, -1), (key2883, 1), (key2992, 1), (key2913, -2), (key2796, 1), (key2944, 1), (key2642, -2), (key2977, -2), (key2654, 1), (key2898, 1), (key2794, -2), (key2640, 1), (key2860, 1), (key2729, -1), (key2984, -1), (key2748, 1), (key2905, 1), (key2642, 1), (key2977, 1), (key2654, -1), (key2898, -1), (key2674, -1), (key2939, -1), (key2619, 1), (key2951, 1), (key2671, 1), (key2786, 1), (key2616, -1), (key2809, -1)]

theorem rawRowCheck5774 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form2 = rawRow5774 := by decide +kernel

def row5774 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5774 : row5774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5774 := by decide +kernel

theorem rowEval5774 (x : Key → ℝ) : Integer.Sparse.eval row5774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5774, Integer.Sparse.eval_collectBalanced, rawRowCheck5774]

def rawRow5775 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2913, 2), (key2961, -1), (key2832, -1), (key2984, 2), (key2729, 2), (key2905, -1), (key2748, -1), (key2829, 2), (key2870, -1), (key2726, -1), (key2992, 1), (key2883, 1), (key2913, -2), (key2944, 1), (key2796, 1), (key2977, -2), (key2642, -2), (key2898, 1), (key2654, 1), (key2794, -2), (key2860, 1), (key2640, 1), (key2984, -1), (key2729, -1), (key2905, 1), (key2748, 1), (key2977, 1), (key2642, 1), (key2898, -1), (key2654, -1), (key2939, -1), (key2674, -1), (key2951, 1), (key2619, 1), (key2786, 1), (key2671, 1), (key2809, -1), (key2616, -1)]

theorem rawRowCheck5775 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form2 = rawRow5775 := by decide +kernel

def row5775 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5775 : row5775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5775 := by decide +kernel

theorem rowEval5775 (x : Key → ℝ) : Integer.Sparse.eval row5775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5775, Integer.Sparse.eval_collectBalanced, rawRowCheck5775]

def rawRow5776 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2883, 2), (key2905, -1), (key2984, -1), (key2748, 2), (key2961, 2), (key2729, -1), (key2832, -1), (key2870, 2), (key2726, -1), (key2829, -1), (key2913, 1), (key2992, 1), (key2883, -2), (key2898, 1), (key2977, 1), (key2654, -2), (key2944, -2), (key2642, 1), (key2796, 1), (key2860, -2), (key2640, 1), (key2794, 1), (key2748, -1), (key2961, -1), (key2729, 1), (key2832, 1), (key2654, 1), (key2944, 1), (key2642, -1), (key2796, -1), (key2738, -1), (key2951, -1), (key2649, 1), (key2939, 1), (key2706, 1), (key2809, 1), (key2632, -1), (key2786, -1)]

theorem rawRowCheck5776 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form2 = rawRow5776 := by decide +kernel

def row5776 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5776 : row5776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5776 := by decide +kernel

theorem rowEval5776 (x : Key → ℝ) : Integer.Sparse.eval row5776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5776, Integer.Sparse.eval_collectBalanced, rawRowCheck5776]

def rawRow5777 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2883, 2), (key2984, -1), (key2905, -1), (key2961, 2), (key2748, 2), (key2832, -1), (key2729, -1), (key2870, 2), (key2829, -1), (key2726, -1), (key2992, 1), (key2913, 1), (key2883, -2), (key2977, 1), (key2898, 1), (key2944, -2), (key2654, -2), (key2796, 1), (key2642, 1), (key2860, -2), (key2794, 1), (key2640, 1), (key2961, -1), (key2748, -1), (key2832, 1), (key2729, 1), (key2944, 1), (key2654, 1), (key2796, -1), (key2642, -1), (key2951, -1), (key2738, -1), (key2939, 1), (key2649, 1), (key2809, 1), (key2706, 1), (key2786, -1), (key2632, -1)]

theorem rawRowCheck5777 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form2 = rawRow5777 := by decide +kernel

def row5777 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5777 : row5777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5777 := by decide +kernel

theorem rowEval5777 (x : Key → ℝ) : Integer.Sparse.eval row5777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5777, Integer.Sparse.eval_collectBalanced, rawRowCheck5777]

def rawRow5778 : Integer.Sparse Key := [(key1039, -4), (key1043, 2), (key1043, 2), (key1078, 2), (key1078, 2), (key1081, -4), (key1004, 2), (key1008, -1), (key1008, -1), (key1117, 2), (key1195, -1), (key1195, -1), (key1157, -1), (key1157, -1), (key1214, -1), (key1214, -1), (key1216, 2), (key1216, 2), (key1021, -1), (key1021, -1), (key1023, 2), (key1129, -1), (key1129, -1), (key1201, 2), (key1201, 2), (key1202, -1), (key1202, -1), (key1176, 2), (key1225, -1), (key1225, -1)]

theorem rawRowCheck5778 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5778 := by decide +kernel

def row5778 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck5778 : row5778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5778 := by decide +kernel

theorem rowEval5778 (x : Key → ℝ) : Integer.Sparse.eval row5778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5778, Integer.Sparse.eval_collectBalanced, rawRowCheck5778]

def rawRow5779 : Integer.Sparse Key := [(key1043, -4), (key1039, 2), (key1043, 2), (key1078, 2), (key1081, 2), (key1078, -4), (key1008, 2), (key1004, -1), (key1008, -1), (key1195, 2), (key1117, -1), (key1195, -1), (key1214, -1), (key1216, -1), (key1157, -1), (key1216, -1), (key1157, 2), (key1214, 2), (key1021, -1), (key1023, -1), (key1021, 2), (key1201, -1), (key1202, -1), (key1129, 2), (key1202, 2), (key1129, -1), (key1201, -1), (key1225, 2), (key1176, -1), (key1225, -1)]

theorem rawRowCheck5779 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5779 := by decide +kernel

def row5779 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5779 : row5779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5779 := by decide +kernel

theorem rowEval5779 (x : Key → ℝ) : Integer.Sparse.eval row5779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5779, Integer.Sparse.eval_collectBalanced, rawRowCheck5779]

def rawRow5780 : Integer.Sparse Key := [(key1043, -4), (key1043, 2), (key1039, 2), (key1081, 2), (key1078, 2), (key1078, -4), (key1008, 2), (key1008, -1), (key1004, -1), (key1195, 2), (key1195, -1), (key1117, -1), (key1216, -1), (key1214, -1), (key1216, -1), (key1157, -1), (key1214, 2), (key1157, 2), (key1023, -1), (key1021, -1), (key1021, 2), (key1202, -1), (key1201, -1), (key1202, 2), (key1129, 2), (key1201, -1), (key1129, -1), (key1225, 2), (key1225, -1), (key1176, -1)]

theorem rawRowCheck5780 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5780 := by decide +kernel

def row5780 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5780 : row5780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5780 := by decide +kernel

theorem rowEval5780 (x : Key → ℝ) : Integer.Sparse.eval row5780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5780, Integer.Sparse.eval_collectBalanced, rawRowCheck5780]

def rawRow5781 : Integer.Sparse Key := [(key1039, -4), (key1078, 2), (key1078, 2), (key1043, 2), (key1043, 2), (key1081, -4), (key1117, 2), (key1157, -1), (key1157, -1), (key1004, 2), (key1214, -1), (key1214, -1), (key1008, -1), (key1008, -1), (key1195, -1), (key1195, -1), (key1216, 2), (key1216, 2), (key1129, -1), (key1129, -1), (key1176, 2), (key1021, -1), (key1021, -1), (key1201, 2), (key1201, 2), (key1225, -1), (key1225, -1), (key1023, 2), (key1202, -1), (key1202, -1)]

theorem rawRowCheck5781 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form3 = rawRow5781 := by decide +kernel

def row5781 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck5781 : row5781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5781 := by decide +kernel

theorem rowEval5781 (x : Key → ℝ) : Integer.Sparse.eval row5781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5781, Integer.Sparse.eval_collectBalanced, rawRowCheck5781]

def rawRow5782 : Integer.Sparse Key := [(key1078, -4), (key1039, 2), (key1078, 2), (key1043, 2), (key1081, 2), (key1043, -4), (key1157, 2), (key1117, -1), (key1157, -1), (key1214, 2), (key1004, -1), (key1214, -1), (key1195, -1), (key1216, -1), (key1008, -1), (key1216, -1), (key1008, 2), (key1195, 2), (key1129, -1), (key1176, -1), (key1129, 2), (key1201, -1), (key1225, -1), (key1021, 2), (key1225, 2), (key1021, -1), (key1201, -1), (key1202, 2), (key1023, -1), (key1202, -1)]

theorem rawRowCheck5782 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form3 = rawRow5782 := by decide +kernel

def row5782 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5782 : row5782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5782 := by decide +kernel

theorem rowEval5782 (x : Key → ℝ) : Integer.Sparse.eval row5782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5782, Integer.Sparse.eval_collectBalanced, rawRowCheck5782]

def rawRow5783 : Integer.Sparse Key := [(key1078, -4), (key1078, 2), (key1039, 2), (key1081, 2), (key1043, 2), (key1043, -4), (key1157, 2), (key1157, -1), (key1117, -1), (key1214, 2), (key1214, -1), (key1004, -1), (key1216, -1), (key1195, -1), (key1216, -1), (key1008, -1), (key1195, 2), (key1008, 2), (key1176, -1), (key1129, -1), (key1129, 2), (key1225, -1), (key1201, -1), (key1225, 2), (key1021, 2), (key1201, -1), (key1021, -1), (key1202, 2), (key1202, -1), (key1023, -1)]

theorem rawRowCheck5783 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form3 = rawRow5783 := by decide +kernel

def row5783 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5783 : row5783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5783 := by decide +kernel

theorem rowEval5783 (x : Key → ℝ) : Integer.Sparse.eval row5783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5783, Integer.Sparse.eval_collectBalanced, rawRowCheck5783]

def rawRow5784 : Integer.Sparse Key := [(key1043, -4), (key1078, 2), (key1081, 2), (key1039, 2), (key1043, 2), (key1078, -4), (key1195, 2), (key1214, -1), (key1216, -1), (key1008, 2), (key1157, -1), (key1216, -1), (key1004, -1), (key1008, -1), (key1117, -1), (key1195, -1), (key1157, 2), (key1214, 2), (key1201, -1), (key1202, -1), (key1225, 2), (key1021, -1), (key1023, -1), (key1129, 2), (key1202, 2), (key1176, -1), (key1225, -1), (key1021, 2), (key1129, -1), (key1201, -1)]

theorem rawRowCheck5784 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form3 = rawRow5784 := by decide +kernel

def row5784 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5784 : row5784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5784 := by decide +kernel

theorem rowEval5784 (x : Key → ℝ) : Integer.Sparse.eval row5784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5784, Integer.Sparse.eval_collectBalanced, rawRowCheck5784]

def rawRow5785 : Integer.Sparse Key := [(key1043, -4), (key1081, 2), (key1078, 2), (key1043, 2), (key1039, 2), (key1078, -4), (key1195, 2), (key1216, -1), (key1214, -1), (key1008, 2), (key1216, -1), (key1157, -1), (key1008, -1), (key1004, -1), (key1195, -1), (key1117, -1), (key1214, 2), (key1157, 2), (key1202, -1), (key1201, -1), (key1225, 2), (key1023, -1), (key1021, -1), (key1202, 2), (key1129, 2), (key1225, -1), (key1176, -1), (key1021, 2), (key1201, -1), (key1129, -1)]

theorem rawRowCheck5785 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form3 = rawRow5785 := by decide +kernel

def row5785 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5785 : row5785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5785 := by decide +kernel

theorem rowEval5785 (x : Key → ℝ) : Integer.Sparse.eval row5785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5785, Integer.Sparse.eval_collectBalanced, rawRowCheck5785]

def rawRow5786 : Integer.Sparse Key := [(key1078, -4), (key1043, 2), (key1081, 2), (key1039, 2), (key1078, 2), (key1043, -4), (key1214, 2), (key1195, -1), (key1216, -1), (key1157, 2), (key1008, -1), (key1216, -1), (key1117, -1), (key1157, -1), (key1004, -1), (key1214, -1), (key1008, 2), (key1195, 2), (key1201, -1), (key1225, -1), (key1202, 2), (key1129, -1), (key1176, -1), (key1021, 2), (key1225, 2), (key1023, -1), (key1202, -1), (key1129, 2), (key1021, -1), (key1201, -1)]

theorem rawRowCheck5786 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form3 = rawRow5786 := by decide +kernel

def row5786 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5786 : row5786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5786 := by decide +kernel

theorem rowEval5786 (x : Key → ℝ) : Integer.Sparse.eval row5786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5786, Integer.Sparse.eval_collectBalanced, rawRowCheck5786]

def rawRow5787 : Integer.Sparse Key := [(key1078, -4), (key1081, 2), (key1043, 2), (key1078, 2), (key1039, 2), (key1043, -4), (key1214, 2), (key1216, -1), (key1195, -1), (key1157, 2), (key1216, -1), (key1008, -1), (key1157, -1), (key1117, -1), (key1214, -1), (key1004, -1), (key1195, 2), (key1008, 2), (key1225, -1), (key1201, -1), (key1202, 2), (key1176, -1), (key1129, -1), (key1225, 2), (key1021, 2), (key1202, -1), (key1023, -1), (key1129, 2), (key1201, -1), (key1021, -1)]

theorem rawRowCheck5787 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form3 = rawRow5787 := by decide +kernel

def row5787 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5787 : row5787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5787 := by decide +kernel

theorem rowEval5787 (x : Key → ℝ) : Integer.Sparse.eval row5787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5787, Integer.Sparse.eval_collectBalanced, rawRowCheck5787]

def rawRow5788 : Integer.Sparse Key := [(key1081, -4), (key1043, 2), (key1078, 2), (key1043, 2), (key1078, 2), (key1039, -4), (key1216, 2), (key1195, -1), (key1214, -1), (key1216, 2), (key1008, -1), (key1157, -1), (key1195, -1), (key1214, -1), (key1008, -1), (key1157, -1), (key1004, 2), (key1117, 2), (key1202, -1), (key1225, -1), (key1201, 2), (key1202, -1), (key1225, -1), (key1023, 2), (key1176, 2), (key1021, -1), (key1129, -1), (key1201, 2), (key1021, -1), (key1129, -1)]

theorem rawRowCheck5788 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form3 = rawRow5788 := by decide +kernel

def row5788 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck5788 : row5788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5788 := by decide +kernel

theorem rowEval5788 (x : Key → ℝ) : Integer.Sparse.eval row5788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5788, Integer.Sparse.eval_collectBalanced, rawRowCheck5788]

def rawRow5789 : Integer.Sparse Key := [(key1081, -4), (key1078, 2), (key1043, 2), (key1078, 2), (key1043, 2), (key1039, -4), (key1216, 2), (key1214, -1), (key1195, -1), (key1216, 2), (key1157, -1), (key1008, -1), (key1214, -1), (key1195, -1), (key1157, -1), (key1008, -1), (key1117, 2), (key1004, 2), (key1225, -1), (key1202, -1), (key1201, 2), (key1225, -1), (key1202, -1), (key1176, 2), (key1023, 2), (key1129, -1), (key1021, -1), (key1201, 2), (key1129, -1), (key1021, -1)]

theorem rawRowCheck5789 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form3 = rawRow5789 := by decide +kernel

def row5789 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -4), (key1043, 4), (key1078, 4), (key1081, -4), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck5789 : row5789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5789 := by decide +kernel

theorem rowEval5789 (x : Key → ℝ) : Integer.Sparse.eval row5789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5789, Integer.Sparse.eval_collectBalanced, rawRowCheck5789]

def rawRow5790 : Integer.Sparse Key := [(key1117, -4), (key1129, 2), (key1129, 2), (key1157, 2), (key1157, 2), (key1176, -4), (key1004, 2), (key1021, -1), (key1021, -1), (key1039, 2), (key1201, -1), (key1201, -1), (key1078, -1), (key1078, -1), (key1214, -1), (key1214, -1), (key1225, 2), (key1225, 2), (key1008, -1), (key1008, -1), (key1023, 2), (key1043, -1), (key1043, -1), (key1195, 2), (key1195, 2), (key1202, -1), (key1202, -1), (key1081, 2), (key1216, -1), (key1216, -1)]

theorem rawRowCheck5790 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form3 = rawRow5790 := by decide +kernel

def row5790 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck5790 : row5790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5790 := by decide +kernel

theorem rowEval5790 (x : Key → ℝ) : Integer.Sparse.eval row5790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5790, Integer.Sparse.eval_collectBalanced, rawRowCheck5790]

def rawRow5791 : Integer.Sparse Key := [(key1129, -4), (key1117, 2), (key1129, 2), (key1157, 2), (key1176, 2), (key1157, -4), (key1021, 2), (key1004, -1), (key1021, -1), (key1201, 2), (key1039, -1), (key1201, -1), (key1214, -1), (key1225, -1), (key1078, -1), (key1225, -1), (key1078, 2), (key1214, 2), (key1008, -1), (key1023, -1), (key1008, 2), (key1195, -1), (key1202, -1), (key1043, 2), (key1202, 2), (key1043, -1), (key1195, -1), (key1216, 2), (key1081, -1), (key1216, -1)]

theorem rawRowCheck5791 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form3 = rawRow5791 := by decide +kernel

def row5791 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5791 : row5791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5791 := by decide +kernel

theorem rowEval5791 (x : Key → ℝ) : Integer.Sparse.eval row5791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5791, Integer.Sparse.eval_collectBalanced, rawRowCheck5791]

def rawRow5792 : Integer.Sparse Key := [(key1129, -4), (key1129, 2), (key1117, 2), (key1176, 2), (key1157, 2), (key1157, -4), (key1021, 2), (key1021, -1), (key1004, -1), (key1201, 2), (key1201, -1), (key1039, -1), (key1225, -1), (key1214, -1), (key1225, -1), (key1078, -1), (key1214, 2), (key1078, 2), (key1023, -1), (key1008, -1), (key1008, 2), (key1202, -1), (key1195, -1), (key1202, 2), (key1043, 2), (key1195, -1), (key1043, -1), (key1216, 2), (key1216, -1), (key1081, -1)]

theorem rawRowCheck5792 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form3 = rawRow5792 := by decide +kernel

def row5792 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5792 : row5792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5792 := by decide +kernel

theorem rowEval5792 (x : Key → ℝ) : Integer.Sparse.eval row5792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5792, Integer.Sparse.eval_collectBalanced, rawRowCheck5792]

def rawRow5793 : Integer.Sparse Key := [(key1117, -4), (key1157, 2), (key1157, 2), (key1129, 2), (key1129, 2), (key1176, -4), (key1039, 2), (key1078, -1), (key1078, -1), (key1004, 2), (key1214, -1), (key1214, -1), (key1021, -1), (key1021, -1), (key1201, -1), (key1201, -1), (key1225, 2), (key1225, 2), (key1043, -1), (key1043, -1), (key1081, 2), (key1008, -1), (key1008, -1), (key1195, 2), (key1195, 2), (key1216, -1), (key1216, -1), (key1023, 2), (key1202, -1), (key1202, -1)]

theorem rawRowCheck5793 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form3 = rawRow5793 := by decide +kernel

def row5793 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck5793 : row5793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5793 := by decide +kernel

theorem rowEval5793 (x : Key → ℝ) : Integer.Sparse.eval row5793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5793, Integer.Sparse.eval_collectBalanced, rawRowCheck5793]

def rawRow5794 : Integer.Sparse Key := [(key1157, -4), (key1117, 2), (key1157, 2), (key1129, 2), (key1176, 2), (key1129, -4), (key1078, 2), (key1039, -1), (key1078, -1), (key1214, 2), (key1004, -1), (key1214, -1), (key1201, -1), (key1225, -1), (key1021, -1), (key1225, -1), (key1021, 2), (key1201, 2), (key1043, -1), (key1081, -1), (key1043, 2), (key1195, -1), (key1216, -1), (key1008, 2), (key1216, 2), (key1008, -1), (key1195, -1), (key1202, 2), (key1023, -1), (key1202, -1)]

theorem rawRowCheck5794 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form3 = rawRow5794 := by decide +kernel

def row5794 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5794 : row5794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5794 := by decide +kernel

theorem rowEval5794 (x : Key → ℝ) : Integer.Sparse.eval row5794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5794, Integer.Sparse.eval_collectBalanced, rawRowCheck5794]

def rawRow5795 : Integer.Sparse Key := [(key1157, -4), (key1157, 2), (key1117, 2), (key1176, 2), (key1129, 2), (key1129, -4), (key1078, 2), (key1078, -1), (key1039, -1), (key1214, 2), (key1214, -1), (key1004, -1), (key1225, -1), (key1201, -1), (key1225, -1), (key1021, -1), (key1201, 2), (key1021, 2), (key1081, -1), (key1043, -1), (key1043, 2), (key1216, -1), (key1195, -1), (key1216, 2), (key1008, 2), (key1195, -1), (key1008, -1), (key1202, 2), (key1202, -1), (key1023, -1)]

theorem rawRowCheck5795 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form3 = rawRow5795 := by decide +kernel

def row5795 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5795 : row5795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5795 := by decide +kernel

theorem rowEval5795 (x : Key → ℝ) : Integer.Sparse.eval row5795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5795, Integer.Sparse.eval_collectBalanced, rawRowCheck5795]

def rawRow5796 : Integer.Sparse Key := [(key1129, -4), (key1157, 2), (key1176, 2), (key1117, 2), (key1129, 2), (key1157, -4), (key1201, 2), (key1214, -1), (key1225, -1), (key1021, 2), (key1078, -1), (key1225, -1), (key1004, -1), (key1021, -1), (key1039, -1), (key1201, -1), (key1078, 2), (key1214, 2), (key1195, -1), (key1202, -1), (key1216, 2), (key1008, -1), (key1023, -1), (key1043, 2), (key1202, 2), (key1081, -1), (key1216, -1), (key1008, 2), (key1043, -1), (key1195, -1)]

theorem rawRowCheck5796 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form3 = rawRow5796 := by decide +kernel

def row5796 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5796 : row5796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5796 := by decide +kernel

theorem rowEval5796 (x : Key → ℝ) : Integer.Sparse.eval row5796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5796, Integer.Sparse.eval_collectBalanced, rawRowCheck5796]

def rawRow5797 : Integer.Sparse Key := [(key1129, -4), (key1176, 2), (key1157, 2), (key1129, 2), (key1117, 2), (key1157, -4), (key1201, 2), (key1225, -1), (key1214, -1), (key1021, 2), (key1225, -1), (key1078, -1), (key1021, -1), (key1004, -1), (key1201, -1), (key1039, -1), (key1214, 2), (key1078, 2), (key1202, -1), (key1195, -1), (key1216, 2), (key1023, -1), (key1008, -1), (key1202, 2), (key1043, 2), (key1216, -1), (key1081, -1), (key1008, 2), (key1195, -1), (key1043, -1)]

theorem rawRowCheck5797 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form3 = rawRow5797 := by decide +kernel

def row5797 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5797 : row5797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5797 := by decide +kernel

theorem rowEval5797 (x : Key → ℝ) : Integer.Sparse.eval row5797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5797, Integer.Sparse.eval_collectBalanced, rawRowCheck5797]

def rawRow5798 : Integer.Sparse Key := [(key1157, -4), (key1129, 2), (key1176, 2), (key1117, 2), (key1157, 2), (key1129, -4), (key1214, 2), (key1201, -1), (key1225, -1), (key1078, 2), (key1021, -1), (key1225, -1), (key1039, -1), (key1078, -1), (key1004, -1), (key1214, -1), (key1021, 2), (key1201, 2), (key1195, -1), (key1216, -1), (key1202, 2), (key1043, -1), (key1081, -1), (key1008, 2), (key1216, 2), (key1023, -1), (key1202, -1), (key1043, 2), (key1008, -1), (key1195, -1)]

theorem rawRowCheck5798 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form3 = rawRow5798 := by decide +kernel

def row5798 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5798 : row5798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5798 := by decide +kernel

theorem rowEval5798 (x : Key → ℝ) : Integer.Sparse.eval row5798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5798, Integer.Sparse.eval_collectBalanced, rawRowCheck5798]

def rawRow5799 : Integer.Sparse Key := [(key1157, -4), (key1176, 2), (key1129, 2), (key1157, 2), (key1117, 2), (key1129, -4), (key1214, 2), (key1225, -1), (key1201, -1), (key1078, 2), (key1225, -1), (key1021, -1), (key1078, -1), (key1039, -1), (key1214, -1), (key1004, -1), (key1201, 2), (key1021, 2), (key1216, -1), (key1195, -1), (key1202, 2), (key1081, -1), (key1043, -1), (key1216, 2), (key1008, 2), (key1202, -1), (key1023, -1), (key1043, 2), (key1195, -1), (key1008, -1)]

theorem rawRowCheck5799 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form3 = rawRow5799 := by decide +kernel

def row5799 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5799 : row5799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5799 := by decide +kernel

theorem rowEval5799 (x : Key → ℝ) : Integer.Sparse.eval row5799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5799, Integer.Sparse.eval_collectBalanced, rawRowCheck5799]

def rawRow5800 : Integer.Sparse Key := [(key1176, -4), (key1129, 2), (key1157, 2), (key1129, 2), (key1157, 2), (key1117, -4), (key1225, 2), (key1201, -1), (key1214, -1), (key1225, 2), (key1021, -1), (key1078, -1), (key1201, -1), (key1214, -1), (key1021, -1), (key1078, -1), (key1004, 2), (key1039, 2), (key1202, -1), (key1216, -1), (key1195, 2), (key1202, -1), (key1216, -1), (key1023, 2), (key1081, 2), (key1008, -1), (key1043, -1), (key1195, 2), (key1008, -1), (key1043, -1)]

theorem rawRowCheck5800 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form3 = rawRow5800 := by decide +kernel

def row5800 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck5800 : row5800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5800 := by decide +kernel

theorem rowEval5800 (x : Key → ℝ) : Integer.Sparse.eval row5800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5800, Integer.Sparse.eval_collectBalanced, rawRowCheck5800]

def rawRow5801 : Integer.Sparse Key := [(key1176, -4), (key1157, 2), (key1129, 2), (key1157, 2), (key1129, 2), (key1117, -4), (key1225, 2), (key1214, -1), (key1201, -1), (key1225, 2), (key1078, -1), (key1021, -1), (key1214, -1), (key1201, -1), (key1078, -1), (key1021, -1), (key1039, 2), (key1004, 2), (key1216, -1), (key1202, -1), (key1195, 2), (key1216, -1), (key1202, -1), (key1081, 2), (key1023, 2), (key1043, -1), (key1008, -1), (key1195, 2), (key1043, -1), (key1008, -1)]

theorem rawRowCheck5801 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form3 = rawRow5801 := by decide +kernel

def row5801 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -4), (key1129, 4), (key1157, 4), (key1176, -4), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck5801 : row5801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5801 := by decide +kernel

theorem rowEval5801 (x : Key → ℝ) : Integer.Sparse.eval row5801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5801, Integer.Sparse.eval_collectBalanced, rawRowCheck5801]

def rawRow5802 : Integer.Sparse Key := [(key1195, -4), (key1201, 2), (key1202, 2), (key1214, 2), (key1216, 2), (key1225, -4), (key1008, 2), (key1021, -1), (key1023, -1), (key1043, 2), (key1129, -1), (key1202, -1), (key1078, -1), (key1081, -1), (key1157, -1), (key1216, -1), (key1176, 2), (key1225, 2), (key1004, -1), (key1008, -1), (key1021, 2), (key1039, -1), (key1043, -1), (key1117, 2), (key1195, 2), (key1129, -1), (key1201, -1), (key1078, 2), (key1157, -1), (key1214, -1)]

theorem rawRowCheck5802 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form3 = rawRow5802 := by decide +kernel

def row5802 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5802 : row5802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5802 := by decide +kernel

theorem rowEval5802 (x : Key → ℝ) : Integer.Sparse.eval row5802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5802, Integer.Sparse.eval_collectBalanced, rawRowCheck5802]

def rawRow5803 : Integer.Sparse Key := [(key1195, -4), (key1202, 2), (key1201, 2), (key1216, 2), (key1214, 2), (key1225, -4), (key1008, 2), (key1023, -1), (key1021, -1), (key1043, 2), (key1202, -1), (key1129, -1), (key1081, -1), (key1078, -1), (key1216, -1), (key1157, -1), (key1225, 2), (key1176, 2), (key1008, -1), (key1004, -1), (key1021, 2), (key1043, -1), (key1039, -1), (key1195, 2), (key1117, 2), (key1201, -1), (key1129, -1), (key1078, 2), (key1214, -1), (key1157, -1)]

theorem rawRowCheck5803 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form3 = rawRow5803 := by decide +kernel

def row5803 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5803 : row5803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5803 := by decide +kernel

theorem rowEval5803 (x : Key → ℝ) : Integer.Sparse.eval row5803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5803, Integer.Sparse.eval_collectBalanced, rawRowCheck5803]

def rawRow5804 : Integer.Sparse Key := [(key1201, -4), (key1195, 2), (key1202, 2), (key1214, 2), (key1225, 2), (key1216, -4), (key1021, 2), (key1008, -1), (key1023, -1), (key1129, 2), (key1043, -1), (key1202, -1), (key1157, -1), (key1176, -1), (key1078, -1), (key1225, -1), (key1081, 2), (key1216, 2), (key1004, -1), (key1021, -1), (key1008, 2), (key1117, -1), (key1129, -1), (key1039, 2), (key1201, 2), (key1043, -1), (key1195, -1), (key1157, 2), (key1078, -1), (key1214, -1)]

theorem rawRowCheck5804 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form3 = rawRow5804 := by decide +kernel

def row5804 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5804 : row5804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5804 := by decide +kernel

theorem rowEval5804 (x : Key → ℝ) : Integer.Sparse.eval row5804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5804, Integer.Sparse.eval_collectBalanced, rawRowCheck5804]

def rawRow5805 : Integer.Sparse Key := [(key1201, -4), (key1202, 2), (key1195, 2), (key1225, 2), (key1214, 2), (key1216, -4), (key1021, 2), (key1023, -1), (key1008, -1), (key1129, 2), (key1202, -1), (key1043, -1), (key1176, -1), (key1157, -1), (key1225, -1), (key1078, -1), (key1216, 2), (key1081, 2), (key1021, -1), (key1004, -1), (key1008, 2), (key1129, -1), (key1117, -1), (key1201, 2), (key1039, 2), (key1195, -1), (key1043, -1), (key1157, 2), (key1214, -1), (key1078, -1)]

theorem rawRowCheck5805 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form3 = rawRow5805 := by decide +kernel

def row5805 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5805 : row5805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5805 := by decide +kernel

theorem rowEval5805 (x : Key → ℝ) : Integer.Sparse.eval row5805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5805, Integer.Sparse.eval_collectBalanced, rawRowCheck5805]

def rawRow5806 : Integer.Sparse Key := [(key1195, -4), (key1214, 2), (key1216, 2), (key1201, 2), (key1202, 2), (key1225, -4), (key1043, 2), (key1078, -1), (key1081, -1), (key1008, 2), (key1157, -1), (key1216, -1), (key1021, -1), (key1023, -1), (key1129, -1), (key1202, -1), (key1176, 2), (key1225, 2), (key1039, -1), (key1043, -1), (key1078, 2), (key1004, -1), (key1008, -1), (key1117, 2), (key1195, 2), (key1157, -1), (key1214, -1), (key1021, 2), (key1129, -1), (key1201, -1)]

theorem rawRowCheck5806 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form3 = rawRow5806 := by decide +kernel

def row5806 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5806 : row5806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5806 := by decide +kernel

theorem rowEval5806 (x : Key → ℝ) : Integer.Sparse.eval row5806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5806, Integer.Sparse.eval_collectBalanced, rawRowCheck5806]

def rawRow5807 : Integer.Sparse Key := [(key1195, -4), (key1216, 2), (key1214, 2), (key1202, 2), (key1201, 2), (key1225, -4), (key1043, 2), (key1081, -1), (key1078, -1), (key1008, 2), (key1216, -1), (key1157, -1), (key1023, -1), (key1021, -1), (key1202, -1), (key1129, -1), (key1225, 2), (key1176, 2), (key1043, -1), (key1039, -1), (key1078, 2), (key1008, -1), (key1004, -1), (key1195, 2), (key1117, 2), (key1214, -1), (key1157, -1), (key1021, 2), (key1201, -1), (key1129, -1)]

theorem rawRowCheck5807 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form3 = rawRow5807 := by decide +kernel

def row5807 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5807 : row5807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5807 := by decide +kernel

theorem rowEval5807 (x : Key → ℝ) : Integer.Sparse.eval row5807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5807, Integer.Sparse.eval_collectBalanced, rawRowCheck5807]

def rawRow5808 : Integer.Sparse Key := [(key1216, -4), (key1195, 2), (key1214, 2), (key1202, 2), (key1225, 2), (key1201, -4), (key1081, 2), (key1043, -1), (key1078, -1), (key1216, 2), (key1008, -1), (key1157, -1), (key1202, -1), (key1225, -1), (key1023, -1), (key1176, -1), (key1021, 2), (key1129, 2), (key1043, -1), (key1078, -1), (key1039, 2), (key1195, -1), (key1214, -1), (key1008, 2), (key1157, 2), (key1004, -1), (key1117, -1), (key1201, 2), (key1021, -1), (key1129, -1)]

theorem rawRowCheck5808 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form3 = rawRow5808 := by decide +kernel

def row5808 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5808 : row5808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5808 := by decide +kernel

theorem rowEval5808 (x : Key → ℝ) : Integer.Sparse.eval row5808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5808, Integer.Sparse.eval_collectBalanced, rawRowCheck5808]

def rawRow5809 : Integer.Sparse Key := [(key1216, -4), (key1214, 2), (key1195, 2), (key1225, 2), (key1202, 2), (key1201, -4), (key1081, 2), (key1078, -1), (key1043, -1), (key1216, 2), (key1157, -1), (key1008, -1), (key1225, -1), (key1202, -1), (key1176, -1), (key1023, -1), (key1129, 2), (key1021, 2), (key1078, -1), (key1043, -1), (key1039, 2), (key1214, -1), (key1195, -1), (key1157, 2), (key1008, 2), (key1117, -1), (key1004, -1), (key1201, 2), (key1129, -1), (key1021, -1)]

theorem rawRowCheck5809 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form3 = rawRow5809 := by decide +kernel

def row5809 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5809 : row5809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5809 := by decide +kernel

theorem rowEval5809 (x : Key → ℝ) : Integer.Sparse.eval row5809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5809, Integer.Sparse.eval_collectBalanced, rawRowCheck5809]

def rawRow5810 : Integer.Sparse Key := [(key1201, -4), (key1214, 2), (key1225, 2), (key1195, 2), (key1202, 2), (key1216, -4), (key1129, 2), (key1157, -1), (key1176, -1), (key1021, 2), (key1078, -1), (key1225, -1), (key1008, -1), (key1023, -1), (key1043, -1), (key1202, -1), (key1081, 2), (key1216, 2), (key1117, -1), (key1129, -1), (key1157, 2), (key1004, -1), (key1021, -1), (key1039, 2), (key1201, 2), (key1078, -1), (key1214, -1), (key1008, 2), (key1043, -1), (key1195, -1)]

theorem rawRowCheck5810 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form3 = rawRow5810 := by decide +kernel

def row5810 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5810 : row5810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5810 := by decide +kernel

theorem rowEval5810 (x : Key → ℝ) : Integer.Sparse.eval row5810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5810, Integer.Sparse.eval_collectBalanced, rawRowCheck5810]

def rawRow5811 : Integer.Sparse Key := [(key1201, -4), (key1225, 2), (key1214, 2), (key1202, 2), (key1195, 2), (key1216, -4), (key1129, 2), (key1176, -1), (key1157, -1), (key1021, 2), (key1225, -1), (key1078, -1), (key1023, -1), (key1008, -1), (key1202, -1), (key1043, -1), (key1216, 2), (key1081, 2), (key1129, -1), (key1117, -1), (key1157, 2), (key1021, -1), (key1004, -1), (key1201, 2), (key1039, 2), (key1214, -1), (key1078, -1), (key1008, 2), (key1195, -1), (key1043, -1)]

theorem rawRowCheck5811 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form3 = rawRow5811 := by decide +kernel

def row5811 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5811 : row5811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5811 := by decide +kernel

theorem rowEval5811 (x : Key → ℝ) : Integer.Sparse.eval row5811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5811, Integer.Sparse.eval_collectBalanced, rawRowCheck5811]

def rawRow5812 : Integer.Sparse Key := [(key1225, -4), (key1201, 2), (key1214, 2), (key1202, 2), (key1216, 2), (key1195, -4), (key1176, 2), (key1129, -1), (key1157, -1), (key1225, 2), (key1021, -1), (key1078, -1), (key1202, -1), (key1216, -1), (key1023, -1), (key1081, -1), (key1008, 2), (key1043, 2), (key1129, -1), (key1157, -1), (key1117, 2), (key1201, -1), (key1214, -1), (key1021, 2), (key1078, 2), (key1004, -1), (key1039, -1), (key1195, 2), (key1008, -1), (key1043, -1)]

theorem rawRowCheck5812 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form3 = rawRow5812 := by decide +kernel

def row5812 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5812 : row5812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5812 := by decide +kernel

theorem rowEval5812 (x : Key → ℝ) : Integer.Sparse.eval row5812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5812, Integer.Sparse.eval_collectBalanced, rawRowCheck5812]

def rawRow5813 : Integer.Sparse Key := [(key1225, -4), (key1214, 2), (key1201, 2), (key1216, 2), (key1202, 2), (key1195, -4), (key1176, 2), (key1157, -1), (key1129, -1), (key1225, 2), (key1078, -1), (key1021, -1), (key1216, -1), (key1202, -1), (key1081, -1), (key1023, -1), (key1043, 2), (key1008, 2), (key1157, -1), (key1129, -1), (key1117, 2), (key1214, -1), (key1201, -1), (key1078, 2), (key1021, 2), (key1039, -1), (key1004, -1), (key1195, 2), (key1043, -1), (key1008, -1)]

theorem rawRowCheck5813 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form3 = rawRow5813 := by decide +kernel

def row5813 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5813 : row5813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5813 := by decide +kernel

theorem rowEval5813 (x : Key → ℝ) : Integer.Sparse.eval row5813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5813, Integer.Sparse.eval_collectBalanced, rawRowCheck5813]

def rawRow5814 : Integer.Sparse Key := [(key1216, -4), (key1202, 2), (key1225, 2), (key1195, 2), (key1214, 2), (key1201, -4), (key1216, 2), (key1202, -1), (key1225, -1), (key1081, 2), (key1023, -1), (key1176, -1), (key1043, -1), (key1078, -1), (key1008, -1), (key1157, -1), (key1021, 2), (key1129, 2), (key1195, -1), (key1214, -1), (key1201, 2), (key1043, -1), (key1078, -1), (key1008, 2), (key1157, 2), (key1021, -1), (key1129, -1), (key1039, 2), (key1004, -1), (key1117, -1)]

theorem rawRowCheck5814 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form3 = rawRow5814 := by decide +kernel

def row5814 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5814 : row5814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5814 := by decide +kernel

theorem rowEval5814 (x : Key → ℝ) : Integer.Sparse.eval row5814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5814, Integer.Sparse.eval_collectBalanced, rawRowCheck5814]

def rawRow5815 : Integer.Sparse Key := [(key1216, -4), (key1225, 2), (key1202, 2), (key1214, 2), (key1195, 2), (key1201, -4), (key1216, 2), (key1225, -1), (key1202, -1), (key1081, 2), (key1176, -1), (key1023, -1), (key1078, -1), (key1043, -1), (key1157, -1), (key1008, -1), (key1129, 2), (key1021, 2), (key1214, -1), (key1195, -1), (key1201, 2), (key1078, -1), (key1043, -1), (key1157, 2), (key1008, 2), (key1129, -1), (key1021, -1), (key1039, 2), (key1117, -1), (key1004, -1)]

theorem rawRowCheck5815 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form3 = rawRow5815 := by decide +kernel

def row5815 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, -2), (key1202, 1), (key1214, 1), (key1216, -2), (key1225, 1)]

theorem rowCheck5815 : row5815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5815 := by decide +kernel

theorem rowEval5815 (x : Key → ℝ) : Integer.Sparse.eval row5815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5815, Integer.Sparse.eval_collectBalanced, rawRowCheck5815]

def rawRow5816 : Integer.Sparse Key := [(key1225, -4), (key1202, 2), (key1216, 2), (key1201, 2), (key1214, 2), (key1195, -4), (key1225, 2), (key1202, -1), (key1216, -1), (key1176, 2), (key1023, -1), (key1081, -1), (key1129, -1), (key1157, -1), (key1021, -1), (key1078, -1), (key1008, 2), (key1043, 2), (key1201, -1), (key1214, -1), (key1195, 2), (key1129, -1), (key1157, -1), (key1021, 2), (key1078, 2), (key1008, -1), (key1043, -1), (key1117, 2), (key1004, -1), (key1039, -1)]

theorem rawRowCheck5816 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form3 = rawRow5816 := by decide +kernel

def row5816 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5816 : row5816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5816 := by decide +kernel

theorem rowEval5816 (x : Key → ℝ) : Integer.Sparse.eval row5816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5816, Integer.Sparse.eval_collectBalanced, rawRowCheck5816]

def rawRow5817 : Integer.Sparse Key := [(key1225, -4), (key1216, 2), (key1202, 2), (key1214, 2), (key1201, 2), (key1195, -4), (key1225, 2), (key1216, -1), (key1202, -1), (key1176, 2), (key1081, -1), (key1023, -1), (key1157, -1), (key1129, -1), (key1078, -1), (key1021, -1), (key1043, 2), (key1008, 2), (key1214, -1), (key1201, -1), (key1195, 2), (key1157, -1), (key1129, -1), (key1078, 2), (key1021, 2), (key1043, -1), (key1008, -1), (key1117, 2), (key1039, -1), (key1004, -1)]

theorem rawRowCheck5817 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form3 = rawRow5817 := by decide +kernel

def row5817 : Integer.Sparse Key := [(key1004, -1), (key1008, 1), (key1021, 1), (key1023, -1), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, 1), (key1202, 1), (key1214, 1), (key1216, 1), (key1225, -2)]

theorem rowCheck5817 : row5817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5817 := by decide +kernel

theorem rowEval5817 (x : Key → ℝ) : Integer.Sparse.eval row5817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck5817, Integer.Sparse.eval_collectBalanced, rawRowCheck5817]

def rawRow5818 : Integer.Sparse Key := [(key2407, -4), (key2410, 2), (key2410, 2), (key2441, 2), (key2441, 2), (key2445, -4), (key2592, 2), (key2595, -1), (key2595, -1), (key2848, 2), (key2882, -1), (key2882, -1), (key2970, -1), (key2970, -1), (key2991, -1), (key2991, -1), (key2993, 2), (key2993, 2), (key2602, -1), (key2602, -1), (key2603, 2), (key2891, -1), (key2891, -1), (key2912, 2), (key2912, 2), (key2914, -1), (key2914, -1), (key2996, 2), (key3003, -1), (key3003, -1)]

theorem rawRowCheck5818 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form4 = rawRow5818 := by decide +kernel

def row5818 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

theorem rowCheck5818 : row5818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5818 := by decide +kernel

theorem rowEval5818 (x : Key → ℝ) : Integer.Sparse.eval row5818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5818, Integer.Sparse.eval_collectBalanced, rawRowCheck5818]

def rawRow5819 : Integer.Sparse Key := [(key2410, -4), (key2407, 2), (key2410, 2), (key2441, 2), (key2445, 2), (key2441, -4), (key2595, 2), (key2592, -1), (key2595, -1), (key2882, 2), (key2848, -1), (key2882, -1), (key2991, -1), (key2993, -1), (key2970, -1), (key2993, -1), (key2970, 2), (key2991, 2), (key2602, -1), (key2603, -1), (key2602, 2), (key2912, -1), (key2914, -1), (key2891, 2), (key2914, 2), (key2891, -1), (key2912, -1), (key3003, 2), (key2996, -1), (key3003, -1)]

theorem rawRowCheck5819 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form4 = rawRow5819 := by decide +kernel

def row5819 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5819 : row5819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5819 := by decide +kernel

theorem rowEval5819 (x : Key → ℝ) : Integer.Sparse.eval row5819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5819, Integer.Sparse.eval_collectBalanced, rawRowCheck5819]

def rawRow5820 : Integer.Sparse Key := [(key2410, -4), (key2410, 2), (key2407, 2), (key2445, 2), (key2441, 2), (key2441, -4), (key2595, 2), (key2595, -1), (key2592, -1), (key2882, 2), (key2882, -1), (key2848, -1), (key2993, -1), (key2991, -1), (key2993, -1), (key2970, -1), (key2991, 2), (key2970, 2), (key2603, -1), (key2602, -1), (key2602, 2), (key2914, -1), (key2912, -1), (key2914, 2), (key2891, 2), (key2912, -1), (key2891, -1), (key3003, 2), (key3003, -1), (key2996, -1)]

theorem rawRowCheck5820 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form4 = rawRow5820 := by decide +kernel

def row5820 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5820 : row5820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5820 := by decide +kernel

theorem rowEval5820 (x : Key → ℝ) : Integer.Sparse.eval row5820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5820, Integer.Sparse.eval_collectBalanced, rawRowCheck5820]

def rawRow5821 : Integer.Sparse Key := [(key2407, -4), (key2441, 2), (key2441, 2), (key2410, 2), (key2410, 2), (key2445, -4), (key2848, 2), (key2970, -1), (key2970, -1), (key2592, 2), (key2991, -1), (key2991, -1), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, 2), (key2993, 2), (key2891, -1), (key2891, -1), (key2996, 2), (key2602, -1), (key2602, -1), (key2912, 2), (key2912, 2), (key3003, -1), (key3003, -1), (key2603, 2), (key2914, -1), (key2914, -1)]

theorem rawRowCheck5821 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form4 = rawRow5821 := by decide +kernel

def row5821 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

theorem rowCheck5821 : row5821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5821 := by decide +kernel

theorem rowEval5821 (x : Key → ℝ) : Integer.Sparse.eval row5821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5821, Integer.Sparse.eval_collectBalanced, rawRowCheck5821]

def rawRow5822 : Integer.Sparse Key := [(key2441, -4), (key2407, 2), (key2441, 2), (key2410, 2), (key2445, 2), (key2410, -4), (key2970, 2), (key2848, -1), (key2970, -1), (key2991, 2), (key2592, -1), (key2991, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, 2), (key2882, 2), (key2891, -1), (key2996, -1), (key2891, 2), (key2912, -1), (key3003, -1), (key2602, 2), (key3003, 2), (key2602, -1), (key2912, -1), (key2914, 2), (key2603, -1), (key2914, -1)]

theorem rawRowCheck5822 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form4 = rawRow5822 := by decide +kernel

def row5822 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5822 : row5822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5822 := by decide +kernel

theorem rowEval5822 (x : Key → ℝ) : Integer.Sparse.eval row5822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5822, Integer.Sparse.eval_collectBalanced, rawRowCheck5822]

def rawRow5823 : Integer.Sparse Key := [(key2441, -4), (key2441, 2), (key2407, 2), (key2445, 2), (key2410, 2), (key2410, -4), (key2970, 2), (key2970, -1), (key2848, -1), (key2991, 2), (key2991, -1), (key2592, -1), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, 2), (key2595, 2), (key2996, -1), (key2891, -1), (key2891, 2), (key3003, -1), (key2912, -1), (key3003, 2), (key2602, 2), (key2912, -1), (key2602, -1), (key2914, 2), (key2914, -1), (key2603, -1)]

theorem rawRowCheck5823 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form4 = rawRow5823 := by decide +kernel

def row5823 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5823 : row5823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5823 := by decide +kernel

theorem rowEval5823 (x : Key → ℝ) : Integer.Sparse.eval row5823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5823, Integer.Sparse.eval_collectBalanced, rawRowCheck5823]

def rawRow5824 : Integer.Sparse Key := [(key2410, -4), (key2441, 2), (key2445, 2), (key2407, 2), (key2410, 2), (key2441, -4), (key2882, 2), (key2991, -1), (key2993, -1), (key2595, 2), (key2970, -1), (key2993, -1), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, 2), (key2991, 2), (key2912, -1), (key2914, -1), (key3003, 2), (key2602, -1), (key2603, -1), (key2891, 2), (key2914, 2), (key2996, -1), (key3003, -1), (key2602, 2), (key2891, -1), (key2912, -1)]

theorem rawRowCheck5824 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form4 = rawRow5824 := by decide +kernel

def row5824 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5824 : row5824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5824 := by decide +kernel

theorem rowEval5824 (x : Key → ℝ) : Integer.Sparse.eval row5824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5824, Integer.Sparse.eval_collectBalanced, rawRowCheck5824]

def rawRow5825 : Integer.Sparse Key := [(key2410, -4), (key2445, 2), (key2441, 2), (key2410, 2), (key2407, 2), (key2441, -4), (key2882, 2), (key2993, -1), (key2991, -1), (key2595, 2), (key2993, -1), (key2970, -1), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, 2), (key2970, 2), (key2914, -1), (key2912, -1), (key3003, 2), (key2603, -1), (key2602, -1), (key2914, 2), (key2891, 2), (key3003, -1), (key2996, -1), (key2602, 2), (key2912, -1), (key2891, -1)]

theorem rawRowCheck5825 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form4 = rawRow5825 := by decide +kernel

def row5825 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5825 : row5825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5825 := by decide +kernel

theorem rowEval5825 (x : Key → ℝ) : Integer.Sparse.eval row5825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5825, Integer.Sparse.eval_collectBalanced, rawRowCheck5825]

def rawRow5826 : Integer.Sparse Key := [(key2441, -4), (key2410, 2), (key2445, 2), (key2407, 2), (key2441, 2), (key2410, -4), (key2991, 2), (key2882, -1), (key2993, -1), (key2970, 2), (key2595, -1), (key2993, -1), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, 2), (key2882, 2), (key2912, -1), (key3003, -1), (key2914, 2), (key2891, -1), (key2996, -1), (key2602, 2), (key3003, 2), (key2603, -1), (key2914, -1), (key2891, 2), (key2602, -1), (key2912, -1)]

theorem rawRowCheck5826 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form4 = rawRow5826 := by decide +kernel

def row5826 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5826 : row5826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5826 := by decide +kernel

theorem rowEval5826 (x : Key → ℝ) : Integer.Sparse.eval row5826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5826, Integer.Sparse.eval_collectBalanced, rawRowCheck5826]

def rawRow5827 : Integer.Sparse Key := [(key2441, -4), (key2445, 2), (key2410, 2), (key2441, 2), (key2407, 2), (key2410, -4), (key2991, 2), (key2993, -1), (key2882, -1), (key2970, 2), (key2993, -1), (key2595, -1), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, 2), (key2595, 2), (key3003, -1), (key2912, -1), (key2914, 2), (key2996, -1), (key2891, -1), (key3003, 2), (key2602, 2), (key2914, -1), (key2603, -1), (key2891, 2), (key2912, -1), (key2602, -1)]

theorem rawRowCheck5827 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form4 = rawRow5827 := by decide +kernel

def row5827 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

theorem rowCheck5827 : row5827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5827 := by decide +kernel

theorem rowEval5827 (x : Key → ℝ) : Integer.Sparse.eval row5827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5827, Integer.Sparse.eval_collectBalanced, rawRowCheck5827]

def rawRow5828 : Integer.Sparse Key := [(key2445, -4), (key2410, 2), (key2441, 2), (key2410, 2), (key2441, 2), (key2407, -4), (key2993, 2), (key2882, -1), (key2991, -1), (key2993, 2), (key2595, -1), (key2970, -1), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, 2), (key2848, 2), (key2914, -1), (key3003, -1), (key2912, 2), (key2914, -1), (key3003, -1), (key2603, 2), (key2996, 2), (key2602, -1), (key2891, -1), (key2912, 2), (key2602, -1), (key2891, -1)]

theorem rawRowCheck5828 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form4 = rawRow5828 := by decide +kernel

def row5828 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

theorem rowCheck5828 : row5828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5828 := by decide +kernel

theorem rowEval5828 (x : Key → ℝ) : Integer.Sparse.eval row5828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5828, Integer.Sparse.eval_collectBalanced, rawRowCheck5828]

def rawRow5829 : Integer.Sparse Key := [(key2445, -4), (key2441, 2), (key2410, 2), (key2441, 2), (key2410, 2), (key2407, -4), (key2993, 2), (key2991, -1), (key2882, -1), (key2993, 2), (key2970, -1), (key2595, -1), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, 2), (key2592, 2), (key3003, -1), (key2914, -1), (key2912, 2), (key3003, -1), (key2914, -1), (key2996, 2), (key2603, 2), (key2891, -1), (key2602, -1), (key2912, 2), (key2891, -1), (key2602, -1)]

theorem rawRowCheck5829 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form4 = rawRow5829 := by decide +kernel

def row5829 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

theorem rowCheck5829 : row5829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5829 := by decide +kernel

theorem rowEval5829 (x : Key → ℝ) : Integer.Sparse.eval row5829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5829, Integer.Sparse.eval_collectBalanced, rawRowCheck5829]

def rawRow5830 : Integer.Sparse Key := [(key2473, -4), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2526, -4), (key2379, 2), (key2393, -1), (key2393, -1), (key2771, 2), (key2912, -1), (key2912, -1), (key2933, -1), (key2933, -1), (key2991, -1), (key2991, -1), (key3003, 2), (key3003, 2), (key2595, -1), (key2595, -1), (key2603, 2), (key2774, -1), (key2774, -1), (key2882, 2), (key2882, 2), (key2914, -1), (key2914, -1), (key2934, 2), (key2993, -1), (key2993, -1)]

theorem rawRowCheck5830 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form4 = rawRow5830 := by decide +kernel

def row5830 : Integer.Sparse Key := [(key2379, 2), (key2393, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2595, -2), (key2603, 2), (key2771, 2), (key2774, -2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, 2), (key2991, -2), (key2993, -2), (key3003, 4)]

theorem rowCheck5830 : row5830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5830 := by decide +kernel

theorem rowEval5830 (x : Key → ℝ) : Integer.Sparse.eval row5830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5830, Integer.Sparse.eval_collectBalanced, rawRowCheck5830]

def rawRow5831 : Integer.Sparse Key := [(key2483, -4), (key2473, 2), (key2483, 2), (key2507, 2), (key2526, 2), (key2507, -4), (key2393, 2), (key2379, -1), (key2393, -1), (key2912, 2), (key2771, -1), (key2912, -1), (key2991, -1), (key3003, -1), (key2933, -1), (key3003, -1), (key2933, 2), (key2991, 2), (key2595, -1), (key2603, -1), (key2595, 2), (key2882, -1), (key2914, -1), (key2774, 2), (key2914, 2), (key2774, -1), (key2882, -1), (key2993, 2), (key2934, -1), (key2993, -1)]

theorem rawRowCheck5831 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form4 = rawRow5831 := by decide +kernel

def row5831 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2933, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

theorem rowCheck5831 : row5831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5831 := by decide +kernel

theorem rowEval5831 (x : Key → ℝ) : Integer.Sparse.eval row5831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5831, Integer.Sparse.eval_collectBalanced, rawRowCheck5831]

def rawRow5832 : Integer.Sparse Key := [(key2483, -4), (key2483, 2), (key2473, 2), (key2526, 2), (key2507, 2), (key2507, -4), (key2393, 2), (key2393, -1), (key2379, -1), (key2912, 2), (key2912, -1), (key2771, -1), (key3003, -1), (key2991, -1), (key3003, -1), (key2933, -1), (key2991, 2), (key2933, 2), (key2603, -1), (key2595, -1), (key2595, 2), (key2914, -1), (key2882, -1), (key2914, 2), (key2774, 2), (key2882, -1), (key2774, -1), (key2993, 2), (key2993, -1), (key2934, -1)]

theorem rawRowCheck5832 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form4 = rawRow5832 := by decide +kernel

def row5832 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2933, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

theorem rowCheck5832 : row5832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5832 := by decide +kernel

theorem rowEval5832 (x : Key → ℝ) : Integer.Sparse.eval row5832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5832, Integer.Sparse.eval_collectBalanced, rawRowCheck5832]

def rawRow5833 : Integer.Sparse Key := [(key2473, -4), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2526, -4), (key2407, 2), (key2441, -1), (key2441, -1), (key2592, 2), (key2991, -1), (key2991, -1), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, 2), (key3003, 2), (key2774, -1), (key2774, -1), (key2934, 2), (key2595, -1), (key2595, -1), (key2882, 2), (key2882, 2), (key2993, -1), (key2993, -1), (key2603, 2), (key2914, -1), (key2914, -1)]

theorem rawRowCheck5833 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form4 = rawRow5833 := by decide +kernel

def row5833 : Integer.Sparse Key := [(key2407, 2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2774, -2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, 2), (key2991, -2), (key2993, -2), (key3003, 4)]

theorem rowCheck5833 : row5833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5833 := by decide +kernel

theorem rowEval5833 (x : Key → ℝ) : Integer.Sparse.eval row5833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5833, Integer.Sparse.eval_collectBalanced, rawRowCheck5833]

def rawRow5834 : Integer.Sparse Key := [(key2507, -4), (key2473, 2), (key2507, 2), (key2483, 2), (key2526, 2), (key2483, -4), (key2441, 2), (key2407, -1), (key2441, -1), (key2991, 2), (key2592, -1), (key2991, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, 2), (key2912, 2), (key2774, -1), (key2934, -1), (key2774, 2), (key2882, -1), (key2993, -1), (key2595, 2), (key2993, 2), (key2595, -1), (key2882, -1), (key2914, 2), (key2603, -1), (key2914, -1)]

theorem rawRowCheck5834 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form4 = rawRow5834 := by decide +kernel

def row5834 : Integer.Sparse Key := [(key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

theorem rowCheck5834 : row5834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5834 := by decide +kernel

theorem rowEval5834 (x : Key → ℝ) : Integer.Sparse.eval row5834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5834, Integer.Sparse.eval_collectBalanced, rawRowCheck5834]

def rawRow5835 : Integer.Sparse Key := [(key2507, -4), (key2507, 2), (key2473, 2), (key2526, 2), (key2483, 2), (key2483, -4), (key2441, 2), (key2441, -1), (key2407, -1), (key2991, 2), (key2991, -1), (key2592, -1), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, 2), (key2602, 2), (key2934, -1), (key2774, -1), (key2774, 2), (key2993, -1), (key2882, -1), (key2993, 2), (key2595, 2), (key2882, -1), (key2595, -1), (key2914, 2), (key2914, -1), (key2603, -1)]

theorem rawRowCheck5835 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form4 = rawRow5835 := by decide +kernel

def row5835 : Integer.Sparse Key := [(key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

theorem rowCheck5835 : row5835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5835 := by decide +kernel

theorem rowEval5835 (x : Key → ℝ) : Integer.Sparse.eval row5835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5835, Integer.Sparse.eval_collectBalanced, rawRowCheck5835]

def rawRow5836 : Integer.Sparse Key := [(key2483, -4), (key2507, 2), (key2526, 2), (key2473, 2), (key2483, 2), (key2507, -4), (key2544, 2), (key2555, -1), (key2565, -1), (key2393, 2), (key2441, -1), (key2565, -1), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, 2), (key2991, 2), (key2882, -1), (key2914, -1), (key2993, 2), (key2595, -1), (key2603, -1), (key2774, 2), (key2914, 2), (key2934, -1), (key2993, -1), (key2595, 2), (key2774, -1), (key2882, -1)]

theorem rawRowCheck5836 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form4 = rawRow5836 := by decide +kernel

def row5836 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2441, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, 2), (key2555, -1), (key2565, -2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, -1), (key2914, 1), (key2933, 2), (key2934, -1), (key2991, 2), (key2993, 1)]

theorem rowCheck5836 : row5836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5836 := by decide +kernel

theorem rowEval5836 (x : Key → ℝ) : Integer.Sparse.eval row5836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5836, Integer.Sparse.eval_collectBalanced, rawRowCheck5836]

def rawRow5837 : Integer.Sparse Key := [(key2483, -4), (key2526, 2), (key2507, 2), (key2483, 2), (key2473, 2), (key2507, -4), (key2544, 2), (key2565, -1), (key2555, -1), (key2393, 2), (key2565, -1), (key2441, -1), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, 2), (key2933, 2), (key2914, -1), (key2882, -1), (key2993, 2), (key2603, -1), (key2595, -1), (key2914, 2), (key2774, 2), (key2993, -1), (key2934, -1), (key2595, 2), (key2882, -1), (key2774, -1)]

theorem rawRowCheck5837 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form4 = rawRow5837 := by decide +kernel

def row5837 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2441, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, 2), (key2555, -1), (key2565, -2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, -1), (key2914, 1), (key2933, 2), (key2934, -1), (key2991, 2), (key2993, 1)]

theorem rowCheck5837 : row5837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5837 := by decide +kernel

theorem rowEval5837 (x : Key → ℝ) : Integer.Sparse.eval row5837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5837, Integer.Sparse.eval_collectBalanced, rawRowCheck5837]

def rawRow5838 : Integer.Sparse Key := [(key2507, -4), (key2483, 2), (key2526, 2), (key2473, 2), (key2507, 2), (key2483, -4), (key2555, 2), (key2544, -1), (key2565, -1), (key2441, 2), (key2393, -1), (key2565, -1), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, 2), (key2912, 2), (key2882, -1), (key2993, -1), (key2914, 2), (key2774, -1), (key2934, -1), (key2595, 2), (key2993, 2), (key2603, -1), (key2914, -1), (key2774, 2), (key2595, -1), (key2882, -1)]

theorem rawRowCheck5838 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form4 = rawRow5838 := by decide +kernel

def row5838 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, -1), (key2555, 2), (key2565, -2), (key2592, -1), (key2595, 1), (key2602, 2), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 2), (key2914, 1), (key2934, -1), (key2991, -1), (key2993, 1)]

theorem rowCheck5838 : row5838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5838 := by decide +kernel

theorem rowEval5838 (x : Key → ℝ) : Integer.Sparse.eval row5838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5838, Integer.Sparse.eval_collectBalanced, rawRowCheck5838]

def rawRow5839 : Integer.Sparse Key := [(key2507, -4), (key2526, 2), (key2483, 2), (key2507, 2), (key2473, 2), (key2483, -4), (key2555, 2), (key2565, -1), (key2544, -1), (key2441, 2), (key2565, -1), (key2393, -1), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, 2), (key2602, 2), (key2993, -1), (key2882, -1), (key2914, 2), (key2934, -1), (key2774, -1), (key2993, 2), (key2595, 2), (key2914, -1), (key2603, -1), (key2774, 2), (key2882, -1), (key2595, -1)]

theorem rawRowCheck5839 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form4 = rawRow5839 := by decide +kernel

def row5839 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, -1), (key2555, 2), (key2565, -2), (key2592, -1), (key2595, 1), (key2602, 2), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 2), (key2914, 1), (key2934, -1), (key2991, -1), (key2993, 1)]

theorem rowCheck5839 : row5839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5839 := by decide +kernel

theorem rowEval5839 (x : Key → ℝ) : Integer.Sparse.eval row5839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5839, Integer.Sparse.eval_collectBalanced, rawRowCheck5839]

def rawRow5840 : Integer.Sparse Key := [(key2526, -4), (key2483, 2), (key2507, 2), (key2483, 2), (key2507, 2), (key2473, -4), (key2565, 2), (key2544, -1), (key2555, -1), (key2565, 2), (key2393, -1), (key2441, -1), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, 2), (key2771, 2), (key2914, -1), (key2993, -1), (key2882, 2), (key2914, -1), (key2993, -1), (key2603, 2), (key2934, 2), (key2595, -1), (key2774, -1), (key2882, 2), (key2595, -1), (key2774, -1)]

theorem rawRowCheck5840 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form4 = rawRow5840 := by decide +kernel

def row5840 : Integer.Sparse Key := [(key2379, 2), (key2393, -2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2544, -2), (key2555, -2), (key2565, 4), (key2595, -2), (key2603, 2), (key2771, 2), (key2774, -2), (key2882, 4), (key2914, -2), (key2934, 2), (key2993, -2)]

theorem rowCheck5840 : row5840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5840 := by decide +kernel

theorem rowEval5840 (x : Key → ℝ) : Integer.Sparse.eval row5840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5840, Integer.Sparse.eval_collectBalanced, rawRowCheck5840]

def rawRow5841 : Integer.Sparse Key := [(key2526, -4), (key2507, 2), (key2483, 2), (key2507, 2), (key2483, 2), (key2473, -4), (key2565, 2), (key2555, -1), (key2544, -1), (key2565, 2), (key2441, -1), (key2393, -1), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, 2), (key2592, 2), (key2993, -1), (key2914, -1), (key2882, 2), (key2993, -1), (key2914, -1), (key2934, 2), (key2603, 2), (key2774, -1), (key2595, -1), (key2882, 2), (key2774, -1), (key2595, -1)]

theorem rawRowCheck5841 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form4 = rawRow5841 := by decide +kernel

def row5841 : Integer.Sparse Key := [(key2393, -2), (key2407, 2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2544, -2), (key2555, -2), (key2565, 4), (key2592, 2), (key2595, -2), (key2603, 2), (key2774, -2), (key2882, 4), (key2914, -2), (key2934, 2), (key2993, -2)]

theorem rowCheck5841 : row5841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5841 := by decide +kernel

theorem rowEval5841 (x : Key → ℝ) : Integer.Sparse.eval row5841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5841, Integer.Sparse.eval_collectBalanced, rawRowCheck5841]

def rawRow5842 : Integer.Sparse Key := [(key2539, -4), (key2544, 2), (key2545, 2), (key2555, 2), (key2557, 2), (key2565, -4), (key2382, 2), (key2393, -1), (key2395, -1), (key2410, 2), (key2483, -1), (key2545, -1), (key2441, -1), (key2445, -1), (key2507, -1), (key2557, -1), (key2526, 2), (key2565, 2), (key2379, -1), (key2382, -1), (key2393, 2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

theorem rawRowCheck5842 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form4 = rawRow5842 := by decide +kernel

def row5842 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

theorem rowCheck5842 : row5842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5842 := by decide +kernel

theorem rowEval5842 (x : Key → ℝ) : Integer.Sparse.eval row5842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5842, Integer.Sparse.eval_collectBalanced, rawRowCheck5842]

def rawRow5843 : Integer.Sparse Key := [(key2539, -4), (key2545, 2), (key2544, 2), (key2557, 2), (key2555, 2), (key2565, -4), (key2382, 2), (key2395, -1), (key2393, -1), (key2410, 2), (key2545, -1), (key2483, -1), (key2445, -1), (key2441, -1), (key2557, -1), (key2507, -1), (key2565, 2), (key2526, 2), (key2382, -1), (key2379, -1), (key2393, 2), (key2774, -1), (key2771, -1), (key2882, 2), (key2848, 2), (key2912, -1), (key2891, -1), (key2933, 2), (key2991, -1), (key2970, -1)]

theorem rawRowCheck5843 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form4 = rawRow5843 := by decide +kernel

def row5843 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

theorem rowCheck5843 : row5843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5843 := by decide +kernel

theorem rowEval5843 (x : Key → ℝ) : Integer.Sparse.eval row5843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5843, Integer.Sparse.eval_collectBalanced, rawRowCheck5843]

def rawRow5844 : Integer.Sparse Key := [(key2544, -4), (key2539, 2), (key2545, 2), (key2555, 2), (key2565, 2), (key2557, -4), (key2393, 2), (key2382, -1), (key2395, -1), (key2483, 2), (key2410, -1), (key2545, -1), (key2507, -1), (key2526, -1), (key2441, -1), (key2565, -1), (key2445, 2), (key2557, 2), (key2379, -1), (key2393, -1), (key2382, 2), (key2848, -1), (key2891, -1), (key2771, 2), (key2912, 2), (key2774, -1), (key2882, -1), (key2970, 2), (key2933, -1), (key2991, -1)]

theorem rawRowCheck5844 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form4 = rawRow5844 := by decide +kernel

def row5844 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2771, 2), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2933, -1), (key2970, 2), (key2991, -1)]

theorem rowCheck5844 : row5844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5844 := by decide +kernel

theorem rowEval5844 (x : Key → ℝ) : Integer.Sparse.eval row5844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5844, Integer.Sparse.eval_collectBalanced, rawRowCheck5844]

def rawRow5845 : Integer.Sparse Key := [(key2544, -4), (key2545, 2), (key2539, 2), (key2565, 2), (key2555, 2), (key2557, -4), (key2393, 2), (key2395, -1), (key2382, -1), (key2483, 2), (key2545, -1), (key2410, -1), (key2526, -1), (key2507, -1), (key2565, -1), (key2441, -1), (key2557, 2), (key2445, 2), (key2393, -1), (key2379, -1), (key2382, 2), (key2891, -1), (key2848, -1), (key2912, 2), (key2771, 2), (key2882, -1), (key2774, -1), (key2970, 2), (key2991, -1), (key2933, -1)]

theorem rawRowCheck5845 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form4 = rawRow5845 := by decide +kernel

def row5845 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2771, 2), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2933, -1), (key2970, 2), (key2991, -1)]

theorem rowCheck5845 : row5845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5845 := by decide +kernel

theorem rowEval5845 (x : Key → ℝ) : Integer.Sparse.eval row5845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5845, Integer.Sparse.eval_collectBalanced, rawRowCheck5845]

def rawRow5846 : Integer.Sparse Key := [(key2539, -4), (key2555, 2), (key2557, 2), (key2544, 2), (key2545, 2), (key2565, -4), (key2410, 2), (key2441, -1), (key2445, -1), (key2382, 2), (key2507, -1), (key2557, -1), (key2393, -1), (key2395, -1), (key2483, -1), (key2545, -1), (key2526, 2), (key2565, 2), (key2407, -1), (key2410, -1), (key2441, 2), (key2592, -1), (key2595, -1), (key2848, 2), (key2882, 2), (key2970, -1), (key2991, -1), (key2602, 2), (key2891, -1), (key2912, -1)]

theorem rawRowCheck5846 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form4 = rawRow5846 := by decide +kernel

def row5846 : Integer.Sparse Key := [(key2382, 2), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2602, 2), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2970, -1), (key2991, -1)]

theorem rowCheck5846 : row5846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5846 := by decide +kernel

theorem rowEval5846 (x : Key → ℝ) : Integer.Sparse.eval row5846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5846, Integer.Sparse.eval_collectBalanced, rawRowCheck5846]

def rawRow5847 : Integer.Sparse Key := [(key2539, -4), (key2557, 2), (key2555, 2), (key2545, 2), (key2544, 2), (key2565, -4), (key2410, 2), (key2445, -1), (key2441, -1), (key2382, 2), (key2557, -1), (key2507, -1), (key2395, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, 2), (key2526, 2), (key2410, -1), (key2407, -1), (key2441, 2), (key2595, -1), (key2592, -1), (key2882, 2), (key2848, 2), (key2991, -1), (key2970, -1), (key2602, 2), (key2912, -1), (key2891, -1)]

theorem rawRowCheck5847 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form4 = rawRow5847 := by decide +kernel

def row5847 : Integer.Sparse Key := [(key2382, 2), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2602, 2), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2970, -1), (key2991, -1)]

theorem rowCheck5847 : row5847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5847 := by decide +kernel

theorem rowEval5847 (x : Key → ℝ) : Integer.Sparse.eval row5847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5847, Integer.Sparse.eval_collectBalanced, rawRowCheck5847]

def rawRow5848 : Integer.Sparse Key := [(key2557, -4), (key2539, 2), (key2555, 2), (key2545, 2), (key2565, 2), (key2544, -4), (key2445, 2), (key2410, -1), (key2441, -1), (key2557, 2), (key2382, -1), (key2507, -1), (key2545, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2393, 2), (key2483, 2), (key2410, -1), (key2441, -1), (key2407, 2), (key2882, -1), (key2991, -1), (key2595, 2), (key2970, 2), (key2592, -1), (key2848, -1), (key2912, 2), (key2602, -1), (key2891, -1)]

theorem rawRowCheck5848 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form4 = rawRow5848 := by decide +kernel

def row5848 : Integer.Sparse Key := [(key2382, -1), (key2393, 2), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2592, -1), (key2595, 2), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2970, 2), (key2991, -1)]

theorem rowCheck5848 : row5848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5848 := by decide +kernel

theorem rowEval5848 (x : Key → ℝ) : Integer.Sparse.eval row5848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5848, Integer.Sparse.eval_collectBalanced, rawRowCheck5848]

def rawRow5849 : Integer.Sparse Key := [(key2557, -4), (key2555, 2), (key2539, 2), (key2565, 2), (key2545, 2), (key2544, -4), (key2445, 2), (key2441, -1), (key2410, -1), (key2557, 2), (key2507, -1), (key2382, -1), (key2565, -1), (key2545, -1), (key2526, -1), (key2395, -1), (key2483, 2), (key2393, 2), (key2441, -1), (key2410, -1), (key2407, 2), (key2991, -1), (key2882, -1), (key2970, 2), (key2595, 2), (key2848, -1), (key2592, -1), (key2912, 2), (key2891, -1), (key2602, -1)]

theorem rawRowCheck5849 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form4 = rawRow5849 := by decide +kernel

def row5849 : Integer.Sparse Key := [(key2382, -1), (key2393, 2), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2592, -1), (key2595, 2), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2970, 2), (key2991, -1)]

theorem rowCheck5849 : row5849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5849 := by decide +kernel

theorem rowEval5849 (x : Key → ℝ) : Integer.Sparse.eval row5849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5849, Integer.Sparse.eval_collectBalanced, rawRowCheck5849]

def rawRow5850 : Integer.Sparse Key := [(key2544, -4), (key2555, 2), (key2565, 2), (key2539, 2), (key2545, 2), (key2557, -4), (key2483, 2), (key2507, -1), (key2526, -1), (key2393, 2), (key2441, -1), (key2565, -1), (key2382, -1), (key2395, -1), (key2410, -1), (key2545, -1), (key2445, 2), (key2557, 2), (key2473, -1), (key2483, -1), (key2507, 2), (key2379, -1), (key2393, -1), (key2771, 2), (key2912, 2), (key2933, -1), (key2991, -1), (key2595, 2), (key2774, -1), (key2882, -1)]

theorem rawRowCheck5850 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form4 = rawRow5850 := by decide +kernel

def row5850 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2595, 2), (key2771, 2), (key2774, -1), (key2882, -1), (key2912, 2), (key2933, -1), (key2991, -1)]

theorem rowCheck5850 : row5850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5850 := by decide +kernel

theorem rowEval5850 (x : Key → ℝ) : Integer.Sparse.eval row5850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5850, Integer.Sparse.eval_collectBalanced, rawRowCheck5850]

def rawRow5851 : Integer.Sparse Key := [(key2544, -4), (key2565, 2), (key2555, 2), (key2545, 2), (key2539, 2), (key2557, -4), (key2483, 2), (key2526, -1), (key2507, -1), (key2393, 2), (key2565, -1), (key2441, -1), (key2395, -1), (key2382, -1), (key2545, -1), (key2410, -1), (key2557, 2), (key2445, 2), (key2483, -1), (key2473, -1), (key2507, 2), (key2393, -1), (key2379, -1), (key2912, 2), (key2771, 2), (key2991, -1), (key2933, -1), (key2595, 2), (key2882, -1), (key2774, -1)]

theorem rawRowCheck5851 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form4 = rawRow5851 := by decide +kernel

def row5851 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2595, 2), (key2771, 2), (key2774, -1), (key2882, -1), (key2912, 2), (key2933, -1), (key2991, -1)]

theorem rowCheck5851 : row5851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5851 := by decide +kernel

theorem rowEval5851 (x : Key → ℝ) : Integer.Sparse.eval row5851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5851, Integer.Sparse.eval_collectBalanced, rawRowCheck5851]

def rawRow5852 : Integer.Sparse Key := [(key2565, -4), (key2544, 2), (key2555, 2), (key2545, 2), (key2557, 2), (key2539, -4), (key2526, 2), (key2483, -1), (key2507, -1), (key2565, 2), (key2393, -1), (key2441, -1), (key2545, -1), (key2557, -1), (key2395, -1), (key2445, -1), (key2382, 2), (key2410, 2), (key2483, -1), (key2507, -1), (key2473, 2), (key2544, -1), (key2555, -1), (key2393, 2), (key2441, 2), (key2379, -1), (key2771, -1), (key2882, 2), (key2595, -1), (key2774, -1)]

theorem rawRowCheck5852 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form4 = rawRow5852 := by decide +kernel

def row5852 : Integer.Sparse Key := [(key2379, -1), (key2382, 2), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -4), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2595, -1), (key2771, -1), (key2774, -1), (key2882, 2)]

theorem rowCheck5852 : row5852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5852 := by decide +kernel

theorem rowEval5852 (x : Key → ℝ) : Integer.Sparse.eval row5852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5852, Integer.Sparse.eval_collectBalanced, rawRowCheck5852]

def rawRow5853 : Integer.Sparse Key := [(key2565, -4), (key2555, 2), (key2544, 2), (key2557, 2), (key2545, 2), (key2539, -4), (key2526, 2), (key2507, -1), (key2483, -1), (key2565, 2), (key2441, -1), (key2393, -1), (key2557, -1), (key2545, -1), (key2445, -1), (key2395, -1), (key2410, 2), (key2382, 2), (key2507, -1), (key2483, -1), (key2473, 2), (key2555, -1), (key2544, -1), (key2441, 2), (key2393, 2), (key2407, -1), (key2592, -1), (key2882, 2), (key2774, -1), (key2595, -1)]

theorem rawRowCheck5853 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form4 = rawRow5853 := by decide +kernel

def row5853 : Integer.Sparse Key := [(key2382, 2), (key2393, 1), (key2395, -1), (key2407, -1), (key2410, 2), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -4), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2774, -1), (key2882, 2)]

theorem rowCheck5853 : row5853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5853 := by decide +kernel

theorem rowEval5853 (x : Key → ℝ) : Integer.Sparse.eval row5853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5853, Integer.Sparse.eval_collectBalanced, rawRowCheck5853]

def rawRow5854 : Integer.Sparse Key := [(key2557, -4), (key2545, 2), (key2565, 2), (key2539, 2), (key2555, 2), (key2544, -4), (key2557, 2), (key2545, -1), (key2565, -1), (key2445, 2), (key2395, -1), (key2526, -1), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, 2), (key2483, 2), (key2539, -1), (key2555, -1), (key2544, 2), (key2410, -1), (key2441, -1), (key2382, 2), (key2507, 2), (key2393, -1), (key2483, -1), (key2407, 2), (key2592, -1), (key2848, -1)]

theorem rawRowCheck5854 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form4 = rawRow5854 := by decide +kernel

def row5854 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, -2), (key2545, 1), (key2555, 1), (key2557, -2), (key2565, 1), (key2592, -1), (key2848, -1)]

theorem rowCheck5854 : row5854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5854 := by decide +kernel

theorem rowEval5854 (x : Key → ℝ) : Integer.Sparse.eval row5854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5854, Integer.Sparse.eval_collectBalanced, rawRowCheck5854]

def rawRow5855 : Integer.Sparse Key := [(key2557, -4), (key2565, 2), (key2545, 2), (key2555, 2), (key2539, 2), (key2544, -4), (key2557, 2), (key2565, -1), (key2545, -1), (key2445, 2), (key2526, -1), (key2395, -1), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, 2), (key2393, 2), (key2555, -1), (key2539, -1), (key2544, 2), (key2441, -1), (key2410, -1), (key2507, 2), (key2382, 2), (key2483, -1), (key2393, -1), (key2407, 2), (key2848, -1), (key2592, -1)]

theorem rawRowCheck5855 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form4 = rawRow5855 := by decide +kernel

def row5855 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, -2), (key2545, 1), (key2555, 1), (key2557, -2), (key2565, 1), (key2592, -1), (key2848, -1)]

theorem rowCheck5855 : row5855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5855 := by decide +kernel

theorem rowEval5855 (x : Key → ℝ) : Integer.Sparse.eval row5855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5855, Integer.Sparse.eval_collectBalanced, rawRowCheck5855]

def rawRow5856 : Integer.Sparse Key := [(key2565, -4), (key2545, 2), (key2557, 2), (key2544, 2), (key2555, 2), (key2539, -4), (key2565, 2), (key2545, -1), (key2557, -1), (key2526, 2), (key2395, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, 2), (key2410, 2), (key2544, -1), (key2555, -1), (key2539, 2), (key2483, -1), (key2507, -1), (key2393, 2), (key2441, 2), (key2382, -1), (key2410, -1), (key2473, 2), (key2379, -1), (key2771, -1)]

theorem rawRowCheck5856 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form4 = rawRow5856 := by decide +kernel

def row5856 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2771, -1)]

theorem rowCheck5856 : row5856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5856 := by decide +kernel

theorem rowEval5856 (x : Key → ℝ) : Integer.Sparse.eval row5856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5856, Integer.Sparse.eval_collectBalanced, rawRowCheck5856]

def rawRow5857 : Integer.Sparse Key := [(key2565, -4), (key2557, 2), (key2545, 2), (key2555, 2), (key2544, 2), (key2539, -4), (key2565, 2), (key2557, -1), (key2545, -1), (key2526, 2), (key2445, -1), (key2395, -1), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, 2), (key2382, 2), (key2555, -1), (key2544, -1), (key2539, 2), (key2507, -1), (key2483, -1), (key2441, 2), (key2393, 2), (key2410, -1), (key2382, -1), (key2473, 2), (key2407, -1), (key2592, -1)]

theorem rawRowCheck5857 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form4 = rawRow5857 := by decide +kernel

def row5857 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2592, -1)]

theorem rowCheck5857 : row5857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5857 := by decide +kernel

theorem rowEval5857 (x : Key → ℝ) : Integer.Sparse.eval row5857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck5857, Integer.Sparse.eval_collectBalanced, rawRowCheck5857]

def rawRow5858 : Integer.Sparse Key := [(key2617, -2), (key2620, 1), (key2620, 1), (key2810, -2), (key2833, 1), (key2833, 1), (key2952, 1), (key2952, 1), (key2962, 1), (key2962, 1), (key2964, -2), (key2964, -2), (key2633, 2), (key2643, -1), (key2643, -1), (key2707, 2), (key2730, -1), (key2730, -1), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, 2), (key2994, 2), (key2650, -1), (key2650, -1), (key2655, 1), (key2655, 1), (key2739, -1), (key2739, -1), (key2751, 1), (key2751, 1), (key2899, 1), (key2899, 1), (key2915, -1), (key2915, -1), (key3001, 1), (key3001, 1), (key3004, -1), (key3004, -1)]

theorem rawRowCheck5858 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form5 = rawRow5858 := by decide +kernel

def row5858 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

theorem rowCheck5858 : row5858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5858 := by decide +kernel

theorem rowEval5858 (x : Key → ℝ) : Integer.Sparse.eval row5858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5858, Integer.Sparse.eval_collectBalanced, rawRowCheck5858]

def rawRow5859 : Integer.Sparse Key := [(key2620, -2), (key2617, 1), (key2620, 1), (key2833, -2), (key2810, 1), (key2833, 1), (key2962, 1), (key2964, 1), (key2952, 1), (key2964, 1), (key2952, -2), (key2962, -2), (key2643, 2), (key2633, -1), (key2643, -1), (key2730, 2), (key2707, -1), (key2730, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, 2), (key2985, 2), (key2655, -1), (key2656, -1), (key2650, 1), (key2656, 1), (key2749, -1), (key2751, -1), (key2739, 1), (key2749, 1), (key2906, 1), (key2915, 1), (key2899, -1), (key2906, -1), (key2999, 1), (key3004, 1), (key2999, -1), (key3001, -1)]

theorem rawRowCheck5859 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form5 = rawRow5859 := by decide +kernel

def row5859 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, 1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5859 : row5859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5859 := by decide +kernel

theorem rowEval5859 (x : Key → ℝ) : Integer.Sparse.eval row5859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5859, Integer.Sparse.eval_collectBalanced, rawRowCheck5859]

def rawRow5860 : Integer.Sparse Key := [(key2620, -2), (key2620, 1), (key2617, 1), (key2833, -2), (key2833, 1), (key2810, 1), (key2964, 1), (key2962, 1), (key2964, 1), (key2952, 1), (key2962, -2), (key2952, -2), (key2643, 2), (key2643, -1), (key2633, -1), (key2730, 2), (key2730, -1), (key2707, -1), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, 2), (key2978, 2), (key2656, -1), (key2655, -1), (key2656, 1), (key2650, 1), (key2751, -1), (key2749, -1), (key2749, 1), (key2739, 1), (key2915, 1), (key2906, 1), (key2906, -1), (key2899, -1), (key3004, 1), (key2999, 1), (key3001, -1), (key2999, -1)]

theorem rawRowCheck5860 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form5 = rawRow5860 := by decide +kernel

def row5860 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, 1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5860 : row5860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5860 := by decide +kernel

theorem rowEval5860 (x : Key → ℝ) : Integer.Sparse.eval row5860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5860, Integer.Sparse.eval_collectBalanced, rawRowCheck5860]

def rawRow5861 : Integer.Sparse Key := [(key2810, -2), (key2833, 1), (key2833, 1), (key2617, -2), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2833, 1), (key2833, 1), (key2964, -2), (key2964, -2), (key2707, 2), (key2978, -1), (key2978, -1), (key2633, 2), (key2985, -1), (key2985, -1), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, 2), (key2994, 2), (key2739, -1), (key2739, -1), (key2899, 1), (key2899, 1), (key2650, -1), (key2650, -1), (key3001, 1), (key3001, 1), (key2655, 1), (key2655, 1), (key3004, -1), (key3004, -1), (key2751, 1), (key2751, 1), (key2915, -1), (key2915, -1)]

theorem rawRowCheck5861 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form5 = rawRow5861 := by decide +kernel

def row5861 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 4), (key2899, 2), (key2915, -2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

theorem rowCheck5861 : row5861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5861 := by decide +kernel

theorem rowEval5861 (x : Key → ℝ) : Integer.Sparse.eval row5861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5861, Integer.Sparse.eval_collectBalanced, rawRowCheck5861]

def rawRow5862 : Integer.Sparse Key := [(key2833, -2), (key2810, 1), (key2833, 1), (key2962, -2), (key2617, 1), (key2962, 1), (key2833, 1), (key2964, 1), (key2620, 1), (key2964, 1), (key2620, -2), (key2833, -2), (key2978, 2), (key2707, -1), (key2978, -1), (key2985, 2), (key2633, -1), (key2985, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, 2), (key2730, 2), (key2899, -1), (key2999, -1), (key2739, 1), (key2999, 1), (key2906, -1), (key3001, -1), (key2650, 1), (key2906, 1), (key2749, 1), (key3004, 1), (key2655, -1), (key2749, -1), (key2656, 1), (key2915, 1), (key2656, -1), (key2751, -1)]

theorem rawRowCheck5862 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form5 = rawRow5862 := by decide +kernel

def row5862 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2915, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5862 : row5862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5862 := by decide +kernel

theorem rowEval5862 (x : Key → ℝ) : Integer.Sparse.eval row5862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5862, Integer.Sparse.eval_collectBalanced, rawRowCheck5862]

def rawRow5863 : Integer.Sparse Key := [(key2833, -2), (key2833, 1), (key2810, 1), (key2962, -2), (key2962, 1), (key2617, 1), (key2964, 1), (key2833, 1), (key2964, 1), (key2620, 1), (key2833, -2), (key2620, -2), (key2978, 2), (key2978, -1), (key2707, -1), (key2985, 2), (key2985, -1), (key2633, -1), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, 2), (key2643, 2), (key2999, -1), (key2899, -1), (key2999, 1), (key2739, 1), (key3001, -1), (key2906, -1), (key2906, 1), (key2650, 1), (key3004, 1), (key2749, 1), (key2749, -1), (key2655, -1), (key2915, 1), (key2656, 1), (key2751, -1), (key2656, -1)]

theorem rawRowCheck5863 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form5 = rawRow5863 := by decide +kernel

def row5863 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -2), (key2899, -1), (key2915, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5863 : row5863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5863 := by decide +kernel

theorem rowEval5863 (x : Key → ℝ) : Integer.Sparse.eval row5863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5863, Integer.Sparse.eval_collectBalanced, rawRowCheck5863]

def rawRow5864 : Integer.Sparse Key := [(key2952, -2), (key2962, 1), (key2964, 1), (key2620, -2), (key2833, 1), (key2964, 1), (key2617, 1), (key2620, 1), (key2810, 1), (key2833, 1), (key2952, -2), (key2962, -2), (key2730, 2), (key2985, -1), (key2994, -1), (key2643, 2), (key2978, -1), (key2994, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2730, -1), (key2978, 2), (key2985, 2), (key2749, -1), (key2751, -1), (key2906, 1), (key2915, 1), (key2655, -1), (key2656, -1), (key2999, 1), (key3004, 1), (key2650, 1), (key2656, 1), (key2999, -1), (key3001, -1), (key2739, 1), (key2749, 1), (key2899, -1), (key2906, -1)]

theorem rawRowCheck5864 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form5 = rawRow5864 := by decide +kernel

def row5864 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, 2), (key2899, -1), (key2915, 1), (key2952, -4), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5864 : row5864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5864 := by decide +kernel

theorem rowEval5864 (x : Key → ℝ) : Integer.Sparse.eval row5864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5864, Integer.Sparse.eval_collectBalanced, rawRowCheck5864]

def rawRow5865 : Integer.Sparse Key := [(key2952, -2), (key2964, 1), (key2962, 1), (key2620, -2), (key2964, 1), (key2833, 1), (key2620, 1), (key2617, 1), (key2833, 1), (key2810, 1), (key2962, -2), (key2952, -2), (key2730, 2), (key2994, -1), (key2985, -1), (key2643, 2), (key2994, -1), (key2978, -1), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, 2), (key2978, 2), (key2751, -1), (key2749, -1), (key2915, 1), (key2906, 1), (key2656, -1), (key2655, -1), (key3004, 1), (key2999, 1), (key2656, 1), (key2650, 1), (key3001, -1), (key2999, -1), (key2749, 1), (key2739, 1), (key2906, -1), (key2899, -1)]

theorem rawRowCheck5865 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form5 = rawRow5865 := by decide +kernel

def row5865 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, 2), (key2899, -1), (key2915, 1), (key2952, -4), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5865 : row5865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5865 := by decide +kernel

theorem rowEval5865 (x : Key → ℝ) : Integer.Sparse.eval row5865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5865, Integer.Sparse.eval_collectBalanced, rawRowCheck5865]

def rawRow5866 : Integer.Sparse Key := [(key2962, -2), (key2952, 1), (key2964, 1), (key2833, -2), (key2620, 1), (key2964, 1), (key2810, 1), (key2833, 1), (key2617, 1), (key2962, 1), (key2620, -2), (key2833, -2), (key2985, 2), (key2730, -1), (key2994, -1), (key2978, 2), (key2643, -1), (key2994, -1), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, 2), (key2730, 2), (key2906, -1), (key3001, -1), (key2749, 1), (key3004, 1), (key2899, -1), (key2999, -1), (key2656, 1), (key2915, 1), (key2739, 1), (key2999, 1), (key2656, -1), (key2751, -1), (key2650, 1), (key2906, 1), (key2655, -1), (key2749, -1)]

theorem rawRowCheck5866 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form5 = rawRow5866 := by decide +kernel

def row5866 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -3), (key2899, -1), (key2915, 1), (key2952, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5866 : row5866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5866 := by decide +kernel

theorem rowEval5866 (x : Key → ℝ) : Integer.Sparse.eval row5866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5866, Integer.Sparse.eval_collectBalanced, rawRowCheck5866]

def rawRow5867 : Integer.Sparse Key := [(key2962, -2), (key2964, 1), (key2952, 1), (key2833, -2), (key2964, 1), (key2620, 1), (key2833, 1), (key2810, 1), (key2962, 1), (key2617, 1), (key2833, -2), (key2620, -2), (key2985, 2), (key2994, -1), (key2730, -1), (key2978, 2), (key2994, -1), (key2643, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, 2), (key2643, 2), (key3001, -1), (key2906, -1), (key3004, 1), (key2749, 1), (key2999, -1), (key2899, -1), (key2915, 1), (key2656, 1), (key2999, 1), (key2739, 1), (key2751, -1), (key2656, -1), (key2906, 1), (key2650, 1), (key2749, -1), (key2655, -1)]

theorem rawRowCheck5867 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form5 = rawRow5867 := by decide +kernel

def row5867 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2751, -1), (key2810, 1), (key2833, -3), (key2899, -1), (key2915, 1), (key2952, 1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -2), (key3001, -1), (key3004, 1)]

theorem rowCheck5867 : row5867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5867 := by decide +kernel

theorem rowEval5867 (x : Key → ℝ) : Integer.Sparse.eval row5867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5867, Integer.Sparse.eval_collectBalanced, rawRowCheck5867]

def rawRow5868 : Integer.Sparse Key := [(key2964, -2), (key2952, 1), (key2962, 1), (key2964, -2), (key2620, 1), (key2833, 1), (key2952, 1), (key2962, 1), (key2620, 1), (key2833, 1), (key2617, -2), (key2810, -2), (key2994, 2), (key2730, -1), (key2985, -1), (key2994, 2), (key2643, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, 2), (key2707, 2), (key2915, -1), (key3004, -1), (key2751, 1), (key3001, 1), (key2915, -1), (key3004, -1), (key2655, 1), (key2899, 1), (key2751, 1), (key3001, 1), (key2650, -1), (key2739, -1), (key2655, 1), (key2899, 1), (key2650, -1), (key2739, -1)]

theorem rawRowCheck5868 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form5 = rawRow5868 := by decide +kernel

def row5868 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

theorem rowCheck5868 : row5868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5868 := by decide +kernel

theorem rowEval5868 (x : Key → ℝ) : Integer.Sparse.eval row5868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5868, Integer.Sparse.eval_collectBalanced, rawRowCheck5868]

def rawRow5869 : Integer.Sparse Key := [(key2964, -2), (key2962, 1), (key2952, 1), (key2964, -2), (key2833, 1), (key2620, 1), (key2962, 1), (key2952, 1), (key2833, 1), (key2620, 1), (key2810, -2), (key2617, -2), (key2994, 2), (key2985, -1), (key2730, -1), (key2994, 2), (key2978, -1), (key2643, -1), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, 2), (key2633, 2), (key3004, -1), (key2915, -1), (key3001, 1), (key2751, 1), (key3004, -1), (key2915, -1), (key2899, 1), (key2655, 1), (key3001, 1), (key2751, 1), (key2739, -1), (key2650, -1), (key2899, 1), (key2655, 1), (key2739, -1), (key2650, -1)]

theorem rawRowCheck5869 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form5 = rawRow5869 := by decide +kernel

def row5869 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2707, 2), (key2730, -2), (key2739, -2), (key2751, 2), (key2810, -2), (key2833, 2), (key2899, 2), (key2915, -2), (key2952, 2), (key2962, 2), (key2964, -4), (key2978, -2), (key2985, -2), (key2994, 4), (key3001, 2), (key3004, -2)]

theorem rowCheck5869 : row5869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5869 := by decide +kernel

theorem rowEval5869 (x : Key → ℝ) : Integer.Sparse.eval row5869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5869, Integer.Sparse.eval_collectBalanced, rawRowCheck5869]

def rawRow5870 : Integer.Sparse Key := [(key2633, -2), (key2643, 1), (key2643, 1), (key2707, -2), (key2978, 1), (key2978, 1), (key2730, 1), (key2730, 1), (key2985, 1), (key2985, 1), (key2994, -2), (key2994, -2), (key2617, 2), (key2655, -1), (key2655, -1), (key2672, 2), (key2749, -1), (key2749, -1), (key2945, -1), (key2945, -1), (key2962, -1), (key2962, -1), (key3004, 2), (key3004, 2), (key2620, -1), (key2620, -1), (key2643, 1), (key2643, 1), (key2675, -1), (key2675, -1), (key2751, 1), (key2751, 1), (key2797, 1), (key2797, 1), (key2915, -1), (key2915, -1), (key2964, 1), (key2964, 1), (key2994, -1), (key2994, -1)]

theorem rawRowCheck5870 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form5 = rawRow5870 := by decide +kernel

def row5870 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

theorem rowCheck5870 : row5870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5870 := by decide +kernel

theorem rowEval5870 (x : Key → ℝ) : Integer.Sparse.eval row5870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5870, Integer.Sparse.eval_collectBalanced, rawRowCheck5870]

def rawRow5871 : Integer.Sparse Key := [(key2643, -2), (key2633, 1), (key2643, 1), (key2978, -2), (key2707, 1), (key2978, 1), (key2985, 1), (key2994, 1), (key2730, 1), (key2994, 1), (key2730, -2), (key2985, -2), (key2655, 2), (key2617, -1), (key2655, -1), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key3004, -1), (key2945, 2), (key2962, 2), (key2643, -1), (key2656, -1), (key2620, 1), (key2656, 1), (key2730, -1), (key2751, -1), (key2675, 1), (key2730, 1), (key2833, 1), (key2915, 1), (key2797, -1), (key2833, -1), (key2946, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

theorem rawRowCheck5871 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form5 = rawRow5871 := by decide +kernel

def row5871 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5871 : row5871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5871 := by decide +kernel

theorem rowEval5871 (x : Key → ℝ) : Integer.Sparse.eval row5871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5871, Integer.Sparse.eval_collectBalanced, rawRowCheck5871]

def rawRow5872 : Integer.Sparse Key := [(key2643, -2), (key2643, 1), (key2633, 1), (key2978, -2), (key2978, 1), (key2707, 1), (key2994, 1), (key2985, 1), (key2994, 1), (key2730, 1), (key2985, -2), (key2730, -2), (key2655, 2), (key2655, -1), (key2617, -1), (key2749, 2), (key2749, -1), (key2672, -1), (key3004, -1), (key2962, -1), (key3004, -1), (key2945, -1), (key2962, 2), (key2945, 2), (key2656, -1), (key2643, -1), (key2656, 1), (key2620, 1), (key2751, -1), (key2730, -1), (key2730, 1), (key2675, 1), (key2915, 1), (key2833, 1), (key2833, -1), (key2797, -1), (key2994, 1), (key2946, 1), (key2964, -1), (key2946, -1)]

theorem rawRowCheck5872 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form5 = rawRow5872 := by decide +kernel

def row5872 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 1), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5872 : row5872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5872 := by decide +kernel

theorem rowEval5872 (x : Key → ℝ) : Integer.Sparse.eval row5872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5872, Integer.Sparse.eval_collectBalanced, rawRowCheck5872]

def rawRow5873 : Integer.Sparse Key := [(key2707, -2), (key2730, 1), (key2730, 1), (key2633, -2), (key2985, 1), (key2985, 1), (key2643, 1), (key2643, 1), (key2978, 1), (key2978, 1), (key2994, -2), (key2994, -2), (key2672, 2), (key2749, -1), (key2749, -1), (key2617, 2), (key2962, -1), (key2962, -1), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, 2), (key3004, 2), (key2675, -1), (key2675, -1), (key2797, 1), (key2797, 1), (key2620, -1), (key2620, -1), (key2964, 1), (key2964, 1), (key2643, 1), (key2643, 1), (key2994, -1), (key2994, -1), (key2751, 1), (key2751, 1), (key2915, -1), (key2915, -1)]

theorem rawRowCheck5873 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form5 = rawRow5873 := by decide +kernel

def row5873 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -4), (key2751, 2), (key2797, 2), (key2915, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

theorem rowCheck5873 : row5873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5873 := by decide +kernel

theorem rowEval5873 (x : Key → ℝ) : Integer.Sparse.eval row5873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5873, Integer.Sparse.eval_collectBalanced, rawRowCheck5873]

def rawRow5874 : Integer.Sparse Key := [(key2730, -2), (key2707, 1), (key2730, 1), (key2985, -2), (key2633, 1), (key2985, 1), (key2978, 1), (key2994, 1), (key2643, 1), (key2994, 1), (key2643, -2), (key2978, -2), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, 2), (key2617, -1), (key2962, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, 2), (key2749, 2), (key2797, -1), (key2946, -1), (key2675, 1), (key2946, 1), (key2833, -1), (key2964, -1), (key2620, 1), (key2833, 1), (key2730, 1), (key2994, 1), (key2643, -1), (key2730, -1), (key2656, 1), (key2915, 1), (key2656, -1), (key2751, -1)]

theorem rawRowCheck5874 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form5 = rawRow5874 := by decide +kernel

def row5874 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2751, -1), (key2797, -1), (key2915, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5874 : row5874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5874 := by decide +kernel

theorem rowEval5874 (x : Key → ℝ) : Integer.Sparse.eval row5874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5874, Integer.Sparse.eval_collectBalanced, rawRowCheck5874]

def rawRow5875 : Integer.Sparse Key := [(key2730, -2), (key2730, 1), (key2707, 1), (key2985, -2), (key2985, 1), (key2633, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2643, 1), (key2978, -2), (key2643, -2), (key2749, 2), (key2749, -1), (key2672, -1), (key2962, 2), (key2962, -1), (key2617, -1), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, 2), (key2655, 2), (key2946, -1), (key2797, -1), (key2946, 1), (key2675, 1), (key2964, -1), (key2833, -1), (key2833, 1), (key2620, 1), (key2994, 1), (key2730, 1), (key2730, -1), (key2643, -1), (key2915, 1), (key2656, 1), (key2751, -1), (key2656, -1)]

theorem rawRowCheck5875 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form5 = rawRow5875 := by decide +kernel

def row5875 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2751, -1), (key2797, -1), (key2915, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5875 : row5875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5875 := by decide +kernel

theorem rowEval5875 (x : Key → ℝ) : Integer.Sparse.eval row5875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5875, Integer.Sparse.eval_collectBalanced, rawRowCheck5875]

def rawRow5876 : Integer.Sparse Key := [(key2978, -2), (key2985, 1), (key2994, 1), (key2643, -2), (key2730, 1), (key2994, 1), (key2633, 1), (key2643, 1), (key2707, 1), (key2978, 1), (key2730, -2), (key2985, -2), (key2945, 2), (key2962, -1), (key3004, -1), (key2655, 2), (key2749, -1), (key3004, -1), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, 2), (key2962, 2), (key2730, -1), (key2751, -1), (key2833, 1), (key2915, 1), (key2643, -1), (key2656, -1), (key2946, 1), (key2994, 1), (key2620, 1), (key2656, 1), (key2946, -1), (key2964, -1), (key2675, 1), (key2730, 1), (key2797, -1), (key2833, -1)]

theorem rawRowCheck5876 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form5 = rawRow5876 := by decide +kernel

def row5876 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, -2), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 4), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5876 : row5876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5876 := by decide +kernel

theorem rowEval5876 (x : Key → ℝ) : Integer.Sparse.eval row5876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5876, Integer.Sparse.eval_collectBalanced, rawRowCheck5876]

def rawRow5877 : Integer.Sparse Key := [(key2978, -2), (key2994, 1), (key2985, 1), (key2643, -2), (key2994, 1), (key2730, 1), (key2643, 1), (key2633, 1), (key2978, 1), (key2707, 1), (key2985, -2), (key2730, -2), (key2945, 2), (key3004, -1), (key2962, -1), (key2655, 2), (key3004, -1), (key2749, -1), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, 2), (key2945, 2), (key2751, -1), (key2730, -1), (key2915, 1), (key2833, 1), (key2656, -1), (key2643, -1), (key2994, 1), (key2946, 1), (key2656, 1), (key2620, 1), (key2964, -1), (key2946, -1), (key2730, 1), (key2675, 1), (key2833, -1), (key2797, -1)]

theorem rawRowCheck5877 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form5 = rawRow5877 := by decide +kernel

def row5877 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, -2), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, 4), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5877 : row5877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5877 := by decide +kernel

theorem rowEval5877 (x : Key → ℝ) : Integer.Sparse.eval row5877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5877, Integer.Sparse.eval_collectBalanced, rawRowCheck5877]

def rawRow5878 : Integer.Sparse Key := [(key2985, -2), (key2978, 1), (key2994, 1), (key2730, -2), (key2643, 1), (key2994, 1), (key2707, 1), (key2730, 1), (key2633, 1), (key2985, 1), (key2643, -2), (key2978, -2), (key2962, 2), (key2945, -1), (key3004, -1), (key2749, 2), (key2655, -1), (key3004, -1), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, 2), (key2749, 2), (key2833, -1), (key2964, -1), (key2730, 1), (key2994, 1), (key2797, -1), (key2946, -1), (key2656, 1), (key2915, 1), (key2675, 1), (key2946, 1), (key2656, -1), (key2751, -1), (key2620, 1), (key2833, 1), (key2643, -1), (key2730, -1)]

theorem rawRowCheck5878 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form5 = rawRow5878 := by decide +kernel

def row5878 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 3), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5878 : row5878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5878 := by decide +kernel

theorem rowEval5878 (x : Key → ℝ) : Integer.Sparse.eval row5878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5878, Integer.Sparse.eval_collectBalanced, rawRowCheck5878]

def rawRow5879 : Integer.Sparse Key := [(key2985, -2), (key2994, 1), (key2978, 1), (key2730, -2), (key2994, 1), (key2643, 1), (key2730, 1), (key2707, 1), (key2985, 1), (key2633, 1), (key2978, -2), (key2643, -2), (key2962, 2), (key3004, -1), (key2945, -1), (key2749, 2), (key3004, -1), (key2655, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, 2), (key2655, 2), (key2964, -1), (key2833, -1), (key2994, 1), (key2730, 1), (key2946, -1), (key2797, -1), (key2915, 1), (key2656, 1), (key2946, 1), (key2675, 1), (key2751, -1), (key2656, -1), (key2833, 1), (key2620, 1), (key2730, -1), (key2643, -1)]

theorem rawRowCheck5879 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form5 = rawRow5879 := by decide +kernel

def row5879 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2643, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 3), (key2751, -1), (key2797, -1), (key2915, 1), (key2945, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 3), (key3004, -2)]

theorem rowCheck5879 : row5879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5879 := by decide +kernel

theorem rowEval5879 (x : Key → ℝ) : Integer.Sparse.eval row5879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5879, Integer.Sparse.eval_collectBalanced, rawRowCheck5879]

def rawRow5880 : Integer.Sparse Key := [(key2994, -2), (key2978, 1), (key2985, 1), (key2994, -2), (key2643, 1), (key2730, 1), (key2978, 1), (key2985, 1), (key2643, 1), (key2730, 1), (key2633, -2), (key2707, -2), (key3004, 2), (key2945, -1), (key2962, -1), (key3004, 2), (key2655, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, 2), (key2672, 2), (key2915, -1), (key2994, -1), (key2751, 1), (key2964, 1), (key2915, -1), (key2994, -1), (key2643, 1), (key2797, 1), (key2751, 1), (key2964, 1), (key2620, -1), (key2675, -1), (key2643, 1), (key2797, 1), (key2620, -1), (key2675, -1)]

theorem rawRowCheck5880 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form5 = rawRow5880 := by decide +kernel

def row5880 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

theorem rowCheck5880 : row5880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5880 := by decide +kernel

theorem rowEval5880 (x : Key → ℝ) : Integer.Sparse.eval row5880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5880, Integer.Sparse.eval_collectBalanced, rawRowCheck5880]

def rawRow5881 : Integer.Sparse Key := [(key2994, -2), (key2985, 1), (key2978, 1), (key2994, -2), (key2730, 1), (key2643, 1), (key2985, 1), (key2978, 1), (key2730, 1), (key2643, 1), (key2707, -2), (key2633, -2), (key3004, 2), (key2962, -1), (key2945, -1), (key3004, 2), (key2749, -1), (key2655, -1), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, 2), (key2617, 2), (key2994, -1), (key2915, -1), (key2964, 1), (key2751, 1), (key2994, -1), (key2915, -1), (key2797, 1), (key2643, 1), (key2964, 1), (key2751, 1), (key2675, -1), (key2620, -1), (key2797, 1), (key2643, 1), (key2675, -1), (key2620, -1)]

theorem rawRowCheck5881 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form5 = rawRow5881 := by decide +kernel

def row5881 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2672, 2), (key2675, -2), (key2707, -2), (key2730, 2), (key2749, -2), (key2751, 2), (key2797, 2), (key2915, -2), (key2945, -2), (key2962, -2), (key2964, 2), (key2978, 2), (key2985, 2), (key2994, -6), (key3004, 4)]

theorem rowCheck5881 : row5881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5881 := by decide +kernel

theorem rowEval5881 (x : Key → ℝ) : Integer.Sparse.eval row5881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck5881, Integer.Sparse.eval_collectBalanced, rawRowCheck5881]

def rawRow5882 : Integer.Sparse Key := [(key2650, -2), (key2655, 1), (key2656, 1), (key2739, -2), (key2899, 1), (key2999, 1), (key2749, 1), (key2751, 1), (key2906, 1), (key3001, 1), (key2915, -2), (key3004, -2), (key2620, 2), (key2643, -1), (key2656, -1), (key2675, 2), (key2797, -1), (key2946, -1), (key2730, -1), (key2751, -1), (key2833, -1), (key2964, -1), (key2915, 2), (key2994, 2), (key2617, -1), (key2620, -1), (key2633, 1), (key2643, 1), (key2672, -1), (key2675, -1), (key2739, 1), (key2749, 1), (key2787, 1), (key2797, 1), (key2899, -1), (key2906, -1), (key2952, 1), (key2962, 1), (key2978, -1), (key2985, -1)]

theorem rawRowCheck5882 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form5 = rawRow5882 := by decide +kernel

def row5882 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2739, -1), (key2749, 2), (key2787, 1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5882 : row5882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5882 := by decide +kernel

theorem rowEval5882 (x : Key → ℝ) : Integer.Sparse.eval row5882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5882, Integer.Sparse.eval_collectBalanced, rawRowCheck5882]

def rawRow5883 : Integer.Sparse Key := [(key2650, -2), (key2656, 1), (key2655, 1), (key2739, -2), (key2999, 1), (key2899, 1), (key2751, 1), (key2749, 1), (key3001, 1), (key2906, 1), (key3004, -2), (key2915, -2), (key2620, 2), (key2656, -1), (key2643, -1), (key2675, 2), (key2946, -1), (key2797, -1), (key2751, -1), (key2730, -1), (key2964, -1), (key2833, -1), (key2994, 2), (key2915, 2), (key2620, -1), (key2617, -1), (key2643, 1), (key2633, 1), (key2675, -1), (key2672, -1), (key2749, 1), (key2739, 1), (key2797, 1), (key2787, 1), (key2906, -1), (key2899, -1), (key2962, 1), (key2952, 1), (key2985, -1), (key2978, -1)]

theorem rawRowCheck5883 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form5 = rawRow5883 := by decide +kernel

def row5883 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2730, -1), (key2739, -1), (key2749, 2), (key2787, 1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5883 : row5883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5883 := by decide +kernel

theorem rowEval5883 (x : Key → ℝ) : Integer.Sparse.eval row5883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5883, Integer.Sparse.eval_collectBalanced, rawRowCheck5883]

def rawRow5884 : Integer.Sparse Key := [(key2655, -2), (key2650, 1), (key2656, 1), (key2899, -2), (key2739, 1), (key2999, 1), (key2906, 1), (key2915, 1), (key2749, 1), (key3004, 1), (key2751, -2), (key3001, -2), (key2643, 2), (key2620, -1), (key2656, -1), (key2797, 2), (key2675, -1), (key2946, -1), (key2833, -1), (key2915, -1), (key2730, -1), (key2994, -1), (key2751, 2), (key2964, 2), (key2633, -1), (key2643, -1), (key2617, 1), (key2655, 1), (key2707, -1), (key2739, -1), (key2675, 1), (key2730, 1), (key2810, 1), (key2899, 1), (key2797, -1), (key2833, -1), (key2940, 1), (key2985, 1), (key2945, -1), (key2962, -1)]

theorem rawRowCheck5884 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form5 = rawRow5884 := by decide +kernel

def row5884 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2749, 1), (key2797, 1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5884 : row5884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5884 := by decide +kernel

theorem rowEval5884 (x : Key → ℝ) : Integer.Sparse.eval row5884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5884, Integer.Sparse.eval_collectBalanced, rawRowCheck5884]

def rawRow5885 : Integer.Sparse Key := [(key2655, -2), (key2656, 1), (key2650, 1), (key2899, -2), (key2999, 1), (key2739, 1), (key2915, 1), (key2906, 1), (key3004, 1), (key2749, 1), (key3001, -2), (key2751, -2), (key2643, 2), (key2656, -1), (key2620, -1), (key2797, 2), (key2946, -1), (key2675, -1), (key2915, -1), (key2833, -1), (key2994, -1), (key2730, -1), (key2964, 2), (key2751, 2), (key2643, -1), (key2633, -1), (key2655, 1), (key2617, 1), (key2739, -1), (key2707, -1), (key2730, 1), (key2675, 1), (key2899, 1), (key2810, 1), (key2833, -1), (key2797, -1), (key2985, 1), (key2940, 1), (key2962, -1), (key2945, -1)]

theorem rawRowCheck5885 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form5 = rawRow5885 := by decide +kernel

def row5885 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2749, 1), (key2797, 1), (key2810, 1), (key2833, -2), (key2899, -1), (key2906, 1), (key2940, 1), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, 2), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

theorem rowCheck5885 : row5885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5885 := by decide +kernel

theorem rowEval5885 (x : Key → ℝ) : Integer.Sparse.eval row5885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5885, Integer.Sparse.eval_collectBalanced, rawRowCheck5885]

def rawRow5886 : Integer.Sparse Key := [(key2739, -2), (key2749, 1), (key2751, 1), (key2650, -2), (key2906, 1), (key3001, 1), (key2655, 1), (key2656, 1), (key2899, 1), (key2999, 1), (key2915, -2), (key3004, -2), (key2675, 2), (key2730, -1), (key2751, -1), (key2620, 2), (key2833, -1), (key2964, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, 2), (key2994, 2), (key2672, -1), (key2675, -1), (key2707, 1), (key2739, 1), (key2617, -1), (key2620, -1), (key2952, 1), (key2962, 1), (key2633, 1), (key2643, 1), (key2978, -1), (key2985, -1), (key2739, 1), (key2749, 1), (key2899, -1), (key2906, -1)]

theorem rawRowCheck5886 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form5 = rawRow5886 := by decide +kernel

def row5886 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2797, -1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5886 : row5886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5886 := by decide +kernel

theorem rowEval5886 (x : Key → ℝ) : Integer.Sparse.eval row5886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck5886, Integer.Sparse.eval_collectBalanced, rawRowCheck5886]

def rawRow5887 : Integer.Sparse Key := [(key2739, -2), (key2751, 1), (key2749, 1), (key2650, -2), (key3001, 1), (key2906, 1), (key2656, 1), (key2655, 1), (key2999, 1), (key2899, 1), (key3004, -2), (key2915, -2), (key2675, 2), (key2751, -1), (key2730, -1), (key2620, 2), (key2964, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, 2), (key2915, 2), (key2675, -1), (key2672, -1), (key2739, 1), (key2707, 1), (key2620, -1), (key2617, -1), (key2962, 1), (key2952, 1), (key2643, 1), (key2633, 1), (key2985, -1), (key2978, -1), (key2749, 1), (key2739, 1), (key2906, -1), (key2899, -1)]

theorem rawRowCheck5887 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form5 = rawRow5887 := by decide +kernel

def row5887 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2672, -1), (key2675, 1), (key2707, 1), (key2730, -1), (key2749, 2), (key2797, -1), (key2833, -1), (key2946, -1), (key2952, 1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

theorem rowCheck5887 : row5887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5887 := by decide +kernel

theorem rowEval5887 (x : Key → ℝ) : Integer.Sparse.eval row5887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck5887, Integer.Sparse.eval_collectBalanced, rawRowCheck5887]

end MUB6.Certificate.GramRows

end OAI
