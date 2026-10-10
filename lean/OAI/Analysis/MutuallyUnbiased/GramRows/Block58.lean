import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
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

def rawRow4352 : Integer.Sparse Key := [(key2796, -2), (key2832, -2), (key2883, -2), (key2786, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2829, 1), (key2870, 1), (key2944, 2), (key2961, 2), (key2992, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2939, -1), (key2944, -1), (key2951, -1), (key2977, -1), (key2961, -1), (key2984, -1), (key2619, 1), (key2642, 1), (key2674, 1), (key2796, 1), (key2729, 1), (key2832, 1)]

theorem rawRowCheck4352 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form9 = rawRow4352 := by decide +kernel

def row4352 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

theorem rowCheck4352 : row4352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4352 := by decide +kernel

theorem rowEval4352 (x : Key → ℝ) : Integer.Sparse.eval row4352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4352, Integer.Sparse.eval_collectBalanced, rawRowCheck4352]

def rawRow4353 : Integer.Sparse Key := [(key2796, -2), (key2883, -2), (key2832, -2), (key2794, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, 1), (key2829, 1), (key2944, 2), (key2992, 2), (key2961, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2944, -1), (key2939, -1), (key2977, -1), (key2951, -1), (key2984, -1), (key2961, -1), (key2642, 1), (key2619, 1), (key2796, 1), (key2674, 1), (key2832, 1), (key2729, 1)]

theorem rawRowCheck4353 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form9 = rawRow4353 := by decide +kernel

def row4353 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

theorem rowCheck4353 : row4353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4353 := by decide +kernel

theorem rowEval4353 (x : Key → ℝ) : Integer.Sparse.eval row4353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4353, Integer.Sparse.eval_collectBalanced, rawRowCheck4353]

def rawRow4354 : Integer.Sparse Key := [(key2832, -2), (key2796, -2), (key2883, -2), (key2809, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2794, 1), (key2860, 1), (key2961, 2), (key2944, 2), (key2992, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2951, -1), (key2961, -1), (key2939, -1), (key2984, -1), (key2944, -1), (key2977, -1), (key2674, 1), (key2729, 1), (key2619, 1), (key2832, 1), (key2642, 1), (key2796, 1)]

theorem rawRowCheck4354 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form9 = rawRow4354 := by decide +kernel

def row4354 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

theorem rowCheck4354 : row4354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4354 := by decide +kernel

theorem rowEval4354 (x : Key → ℝ) : Integer.Sparse.eval row4354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4354, Integer.Sparse.eval_collectBalanced, rawRowCheck4354]

def rawRow4355 : Integer.Sparse Key := [(key2832, -2), (key2883, -2), (key2796, -2), (key2829, 1), (key2809, 1), (key2870, 1), (key2786, 1), (key2860, 1), (key2794, 1), (key2961, 2), (key2992, 2), (key2944, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2961, -1), (key2951, -1), (key2984, -1), (key2939, -1), (key2977, -1), (key2944, -1), (key2729, 1), (key2674, 1), (key2832, 1), (key2619, 1), (key2796, 1), (key2642, 1)]

theorem rawRowCheck4355 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form9 = rawRow4355 := by decide +kernel

def row4355 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

theorem rowCheck4355 : row4355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4355 := by decide +kernel

theorem rowEval4355 (x : Key → ℝ) : Integer.Sparse.eval row4355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4355, Integer.Sparse.eval_collectBalanced, rawRowCheck4355]

def rawRow4356 : Integer.Sparse Key := [(key2883, -2), (key2796, -2), (key2832, -2), (key2860, 1), (key2870, 1), (key2794, 1), (key2829, 1), (key2786, 1), (key2809, 1), (key2992, 2), (key2944, 2), (key2961, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2977, -1), (key2984, -1), (key2944, -1), (key2961, -1), (key2939, -1), (key2951, -1), (key2796, 1), (key2832, 1), (key2642, 1), (key2729, 1), (key2619, 1), (key2674, 1)]

theorem rawRowCheck4356 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form9 = rawRow4356 := by decide +kernel

def row4356 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

theorem rowCheck4356 : row4356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4356 := by decide +kernel

theorem rowEval4356 (x : Key → ℝ) : Integer.Sparse.eval row4356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4356, Integer.Sparse.eval_collectBalanced, rawRowCheck4356]

def rawRow4357 : Integer.Sparse Key := [(key2883, -2), (key2832, -2), (key2796, -2), (key2870, 1), (key2860, 1), (key2829, 1), (key2794, 1), (key2809, 1), (key2786, 1), (key2992, 2), (key2961, 2), (key2944, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2984, -1), (key2977, -1), (key2961, -1), (key2944, -1), (key2951, -1), (key2939, -1), (key2832, 1), (key2796, 1), (key2729, 1), (key2642, 1), (key2674, 1), (key2619, 1)]

theorem rawRowCheck4357 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form9 = rawRow4357 := by decide +kernel

def row4357 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

theorem rowCheck4357 : row4357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4357 := by decide +kernel

theorem rowEval4357 (x : Key → ℝ) : Integer.Sparse.eval row4357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4357, Integer.Sparse.eval_collectBalanced, rawRowCheck4357]

def rawRow4358 : Integer.Sparse Key := [(key2944, -2), (key2961, -2), (key2992, -2), (key2939, 1), (key2944, 1), (key2951, 1), (key2977, 1), (key2961, 1), (key2984, 1), (key2796, 2), (key2832, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2796, -1), (key2729, -1), (key2832, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2860, -1), (key2829, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

theorem rawRowCheck4358 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form9 = rawRow4358 := by decide +kernel

def row4358 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

theorem rowCheck4358 : row4358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4358 := by decide +kernel

theorem rowEval4358 (x : Key → ℝ) : Integer.Sparse.eval row4358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4358, Integer.Sparse.eval_collectBalanced, rawRowCheck4358]

def rawRow4359 : Integer.Sparse Key := [(key2944, -2), (key2992, -2), (key2961, -2), (key2944, 1), (key2939, 1), (key2977, 1), (key2951, 1), (key2984, 1), (key2961, 1), (key2796, 2), (key2883, 2), (key2832, 2), (key2642, -1), (key2619, -1), (key2796, -1), (key2674, -1), (key2832, -1), (key2729, -1), (key2794, -1), (key2786, -1), (key2860, -1), (key2809, -1), (key2870, -1), (key2829, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

theorem rawRowCheck4359 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form9 = rawRow4359 := by decide +kernel

def row4359 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

theorem rowCheck4359 : row4359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4359 := by decide +kernel

theorem rowEval4359 (x : Key → ℝ) : Integer.Sparse.eval row4359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4359, Integer.Sparse.eval_collectBalanced, rawRowCheck4359]

def rawRow4360 : Integer.Sparse Key := [(key2961, -2), (key2944, -2), (key2992, -2), (key2951, 1), (key2961, 1), (key2939, 1), (key2984, 1), (key2944, 1), (key2977, 1), (key2832, 2), (key2796, 2), (key2883, 2), (key2674, -1), (key2729, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2809, -1), (key2829, -1), (key2786, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

theorem rawRowCheck4360 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form9 = rawRow4360 := by decide +kernel

def row4360 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

theorem rowCheck4360 : row4360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4360 := by decide +kernel

theorem rowEval4360 (x : Key → ℝ) : Integer.Sparse.eval row4360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck4360, Integer.Sparse.eval_collectBalanced, rawRowCheck4360]

def rawRow4361 : Integer.Sparse Key := [(key2961, -2), (key2992, -2), (key2944, -2), (key2961, 1), (key2951, 1), (key2984, 1), (key2939, 1), (key2977, 1), (key2944, 1), (key2832, 2), (key2883, 2), (key2796, 2), (key2729, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2796, -1), (key2642, -1), (key2829, -1), (key2809, -1), (key2870, -1), (key2786, -1), (key2860, -1), (key2794, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

theorem rawRowCheck4361 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form9 = rawRow4361 := by decide +kernel

def row4361 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

theorem rowCheck4361 : row4361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4361 := by decide +kernel

theorem rowEval4361 (x : Key → ℝ) : Integer.Sparse.eval row4361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4361, Integer.Sparse.eval_collectBalanced, rawRowCheck4361]

def rawRow4362 : Integer.Sparse Key := [(key2992, -2), (key2944, -2), (key2961, -2), (key2977, 1), (key2984, 1), (key2944, 1), (key2961, 1), (key2939, 1), (key2951, 1), (key2883, 2), (key2796, 2), (key2832, 2), (key2796, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2619, -1), (key2674, -1), (key2860, -1), (key2870, -1), (key2794, -1), (key2829, -1), (key2786, -1), (key2809, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

theorem rawRowCheck4362 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form9 = rawRow4362 := by decide +kernel

def row4362 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

theorem rowCheck4362 : row4362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4362 := by decide +kernel

theorem rowEval4362 (x : Key → ℝ) : Integer.Sparse.eval row4362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck4362, Integer.Sparse.eval_collectBalanced, rawRowCheck4362]

def rawRow4363 : Integer.Sparse Key := [(key2992, -2), (key2961, -2), (key2944, -2), (key2984, 1), (key2977, 1), (key2961, 1), (key2944, 1), (key2951, 1), (key2939, 1), (key2883, 2), (key2832, 2), (key2796, 2), (key2832, -1), (key2796, -1), (key2729, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, -1), (key2860, -1), (key2829, -1), (key2794, -1), (key2809, -1), (key2786, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

theorem rawRowCheck4363 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form9 = rawRow4363 := by decide +kernel

def row4363 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

theorem rowCheck4363 : row4363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4363 := by decide +kernel

theorem rowEval4363 (x : Key → ℝ) : Integer.Sparse.eval row4363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck4363, Integer.Sparse.eval_collectBalanced, rawRowCheck4363]

def rawRow4364 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2500, -2), (key2465, 6), (key2536, 2), (key2541, 2), (key2552, 2), (key2371, -2), (key2399, -2), (key2465, -2), (key2536, -6), (key2375, 2), (key2403, 2), (key2469, 2)]

theorem rawRowCheck4364 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form10 = rawRow4364 := by decide +kernel

def row4364 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck4364 : row4364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4364 := by decide +kernel

theorem rowEval4364 (x : Key → ℝ) : Integer.Sparse.eval row4364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4364, Integer.Sparse.eval_collectBalanced, rawRowCheck4364]

def rawRow4365 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2500, -2), (key2465, 6), (key2541, 2), (key2536, 2), (key2552, 2), (key2371, -2), (key2465, -2), (key2399, -2), (key2536, -6), (key2375, 2), (key2469, 2), (key2403, 2)]

theorem rawRowCheck4365 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form10 = rawRow4365 := by decide +kernel

def row4365 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck4365 : row4365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4365 := by decide +kernel

theorem rowEval4365 (x : Key → ℝ) : Integer.Sparse.eval row4365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4365, Integer.Sparse.eval_collectBalanced, rawRowCheck4365]

def rawRow4366 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2477, -2), (key2465, 6), (key2536, 2), (key2552, 2), (key2541, 2), (key2399, -2), (key2371, -2), (key2465, -2), (key2536, -6), (key2403, 2), (key2375, 2), (key2469, 2)]

theorem rawRowCheck4366 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form10 = rawRow4366 := by decide +kernel

def row4366 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck4366 : row4366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4366 := by decide +kernel

theorem rowEval4366 (x : Key → ℝ) : Integer.Sparse.eval row4366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4366, Integer.Sparse.eval_collectBalanced, rawRowCheck4366]

def rawRow4367 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2477, -2), (key2465, 6), (key2552, 2), (key2536, 2), (key2541, 2), (key2399, -2), (key2465, -2), (key2371, -2), (key2536, -6), (key2403, 2), (key2469, 2), (key2375, 2)]

theorem rawRowCheck4367 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form10 = rawRow4367 := by decide +kernel

def row4367 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck4367 : row4367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4367 := by decide +kernel

theorem rowEval4367 (x : Key → ℝ) : Integer.Sparse.eval row4367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4367, Integer.Sparse.eval_collectBalanced, rawRowCheck4367]

def rawRow4368 : Integer.Sparse Key := [(key2477, -2), (key2500, -2), (key2469, -2), (key2465, 6), (key2541, 2), (key2552, 2), (key2536, 2), (key2465, -2), (key2371, -2), (key2399, -2), (key2536, -6), (key2469, 2), (key2375, 2), (key2403, 2)]

theorem rawRowCheck4368 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form10 = rawRow4368 := by decide +kernel

def row4368 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck4368 : row4368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4368 := by decide +kernel

theorem rowEval4368 (x : Key → ℝ) : Integer.Sparse.eval row4368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4368, Integer.Sparse.eval_collectBalanced, rawRowCheck4368]

def rawRow4369 : Integer.Sparse Key := [(key2500, -2), (key2477, -2), (key2469, -2), (key2465, 6), (key2552, 2), (key2541, 2), (key2536, 2), (key2465, -2), (key2399, -2), (key2371, -2), (key2536, -6), (key2469, 2), (key2403, 2), (key2375, 2)]

theorem rawRowCheck4369 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form10 = rawRow4369 := by decide +kernel

def row4369 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

theorem rowCheck4369 : row4369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4369 := by decide +kernel

theorem rowEval4369 (x : Key → ℝ) : Integer.Sparse.eval row4369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4369, Integer.Sparse.eval_collectBalanced, rawRowCheck4369]

def rawRow4370 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2552, -2), (key2536, 6), (key2469, 2), (key2477, 2), (key2500, 2), (key2375, -2), (key2403, -2), (key2469, -2), (key2465, -6), (key2371, 2), (key2399, 2), (key2465, 2)]

theorem rawRowCheck4370 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form10 = rawRow4370 := by decide +kernel

def row4370 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck4370 : row4370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4370 := by decide +kernel

theorem rowEval4370 (x : Key → ℝ) : Integer.Sparse.eval row4370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4370, Integer.Sparse.eval_collectBalanced, rawRowCheck4370]

def rawRow4371 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2552, -2), (key2536, 6), (key2477, 2), (key2469, 2), (key2500, 2), (key2375, -2), (key2469, -2), (key2403, -2), (key2465, -6), (key2371, 2), (key2465, 2), (key2399, 2)]

theorem rawRowCheck4371 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form10 = rawRow4371 := by decide +kernel

def row4371 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck4371 : row4371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4371 := by decide +kernel

theorem rowEval4371 (x : Key → ℝ) : Integer.Sparse.eval row4371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4371, Integer.Sparse.eval_collectBalanced, rawRowCheck4371]

def rawRow4372 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2541, -2), (key2536, 6), (key2469, 2), (key2500, 2), (key2477, 2), (key2403, -2), (key2375, -2), (key2469, -2), (key2465, -6), (key2399, 2), (key2371, 2), (key2465, 2)]

theorem rawRowCheck4372 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form10 = rawRow4372 := by decide +kernel

def row4372 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck4372 : row4372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4372 := by decide +kernel

theorem rowEval4372 (x : Key → ℝ) : Integer.Sparse.eval row4372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck4372, Integer.Sparse.eval_collectBalanced, rawRowCheck4372]

def rawRow4373 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2541, -2), (key2536, 6), (key2500, 2), (key2469, 2), (key2477, 2), (key2403, -2), (key2469, -2), (key2375, -2), (key2465, -6), (key2399, 2), (key2465, 2), (key2371, 2)]

theorem rawRowCheck4373 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form10 = rawRow4373 := by decide +kernel

def row4373 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck4373 : row4373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4373 := by decide +kernel

theorem rowEval4373 (x : Key → ℝ) : Integer.Sparse.eval row4373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4373, Integer.Sparse.eval_collectBalanced, rawRowCheck4373]

def rawRow4374 : Integer.Sparse Key := [(key2541, -2), (key2552, -2), (key2536, -2), (key2536, 6), (key2477, 2), (key2500, 2), (key2469, 2), (key2469, -2), (key2375, -2), (key2403, -2), (key2465, -6), (key2465, 2), (key2371, 2), (key2399, 2)]

theorem rawRowCheck4374 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form10 = rawRow4374 := by decide +kernel

def row4374 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck4374 : row4374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4374 := by decide +kernel

theorem rowEval4374 (x : Key → ℝ) : Integer.Sparse.eval row4374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck4374, Integer.Sparse.eval_collectBalanced, rawRowCheck4374]

def rawRow4375 : Integer.Sparse Key := [(key2552, -2), (key2541, -2), (key2536, -2), (key2536, 6), (key2500, 2), (key2477, 2), (key2469, 2), (key2469, -2), (key2403, -2), (key2375, -2), (key2465, -6), (key2465, 2), (key2399, 2), (key2371, 2)]

theorem rawRowCheck4375 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form10 = rawRow4375 := by decide +kernel

def row4375 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

theorem rowCheck4375 : row4375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4375 := by decide +kernel

theorem rowEval4375 (x : Key → ℝ) : Integer.Sparse.eval row4375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck4375, Integer.Sparse.eval_collectBalanced, rawRowCheck4375]

def rawRow4376 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2499, -2), (key2464, 6), (key2534, 2), (key2540, 2), (key2551, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2874, -6), (key2586, 2), (key2765, 2), (key2842, 2)]

theorem rawRowCheck4376 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form11 = rawRow4376 := by decide +kernel

def row4376 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

theorem rowCheck4376 : row4376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4376 := by decide +kernel

theorem rowEval4376 (x : Key → ℝ) : Integer.Sparse.eval row4376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4376, Integer.Sparse.eval_collectBalanced, rawRowCheck4376]

def rawRow4377 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2499, -2), (key2464, 6), (key2540, 2), (key2534, 2), (key2551, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2874, -6), (key2586, 2), (key2842, 2), (key2765, 2)]

theorem rawRowCheck4377 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form11 = rawRow4377 := by decide +kernel

def row4377 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

theorem rowCheck4377 : row4377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4377 := by decide +kernel

theorem rowEval4377 (x : Key → ℝ) : Integer.Sparse.eval row4377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4377, Integer.Sparse.eval_collectBalanced, rawRowCheck4377]

def rawRow4378 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2476, -2), (key2464, 6), (key2534, 2), (key2551, 2), (key2540, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2874, -6), (key2765, 2), (key2586, 2), (key2842, 2)]

theorem rawRowCheck4378 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form11 = rawRow4378 := by decide +kernel

def row4378 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

theorem rowCheck4378 : row4378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4378 := by decide +kernel

theorem rowEval4378 (x : Key → ℝ) : Integer.Sparse.eval row4378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4378, Integer.Sparse.eval_collectBalanced, rawRowCheck4378]

def rawRow4379 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2476, -2), (key2464, 6), (key2551, 2), (key2534, 2), (key2540, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2874, -6), (key2765, 2), (key2842, 2), (key2586, 2)]

theorem rawRowCheck4379 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form11 = rawRow4379 := by decide +kernel

def row4379 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

theorem rowCheck4379 : row4379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4379 := by decide +kernel

theorem rowEval4379 (x : Key → ℝ) : Integer.Sparse.eval row4379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4379, Integer.Sparse.eval_collectBalanced, rawRowCheck4379]

def rawRow4380 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2467, -2), (key2464, 6), (key2540, 2), (key2551, 2), (key2534, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2874, -6), (key2842, 2), (key2586, 2), (key2765, 2)]

theorem rawRowCheck4380 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form11 = rawRow4380 := by decide +kernel

def row4380 : Integer.Sparse Key := [(key2370, -2), (key2464, 4), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2842, 2), (key2874, -6)]

theorem rowCheck4380 : row4380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4380 := by decide +kernel

theorem rowEval4380 (x : Key → ℝ) : Integer.Sparse.eval row4380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4380, Integer.Sparse.eval_collectBalanced, rawRowCheck4380]

def rawRow4381 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2467, -2), (key2464, 6), (key2551, 2), (key2540, 2), (key2534, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2874, -6), (key2842, 2), (key2765, 2), (key2586, 2)]

theorem rawRowCheck4381 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form11 = rawRow4381 := by decide +kernel

def row4381 : Integer.Sparse Key := [(key2398, -2), (key2464, 4), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2842, 2), (key2874, -6)]

theorem rowCheck4381 : row4381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4381 := by decide +kernel

theorem rowEval4381 (x : Key → ℝ) : Integer.Sparse.eval row4381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4381, Integer.Sparse.eval_collectBalanced, rawRowCheck4381]

def rawRow4382 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2551, -2), (key2534, 6), (key2467, 2), (key2476, 2), (key2499, 2), (key2373, -2), (key2401, -2), (key2467, -2), (key2464, -6), (key2370, 2), (key2762, 2), (key2839, 2)]

theorem rawRowCheck4382 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form11 = rawRow4382 := by decide +kernel

def row4382 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2), (key2839, 2)]

theorem rowCheck4382 : row4382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4382 := by decide +kernel

theorem rowEval4382 (x : Key → ℝ) : Integer.Sparse.eval row4382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4382, Integer.Sparse.eval_collectBalanced, rawRowCheck4382]

def rawRow4383 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2551, -2), (key2534, 6), (key2476, 2), (key2467, 2), (key2499, 2), (key2373, -2), (key2467, -2), (key2401, -2), (key2464, -6), (key2370, 2), (key2839, 2), (key2762, 2)]

theorem rawRowCheck4383 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form11 = rawRow4383 := by decide +kernel

def row4383 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2), (key2839, 2)]

theorem rowCheck4383 : row4383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4383 := by decide +kernel

theorem rowEval4383 (x : Key → ℝ) : Integer.Sparse.eval row4383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4383, Integer.Sparse.eval_collectBalanced, rawRowCheck4383]

def rawRow4384 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2540, -2), (key2534, 6), (key2467, 2), (key2499, 2), (key2476, 2), (key2401, -2), (key2373, -2), (key2467, -2), (key2464, -6), (key2398, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck4384 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form11 = rawRow4384 := by decide +kernel

def row4384 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2), (key2839, 2)]

theorem rowCheck4384 : row4384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4384 := by decide +kernel

theorem rowEval4384 (x : Key → ℝ) : Integer.Sparse.eval row4384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck4384, Integer.Sparse.eval_collectBalanced, rawRowCheck4384]

def rawRow4385 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2540, -2), (key2534, 6), (key2499, 2), (key2467, 2), (key2476, 2), (key2401, -2), (key2467, -2), (key2373, -2), (key2464, -6), (key2398, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck4385 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form11 = rawRow4385 := by decide +kernel

def row4385 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2), (key2839, 2)]

theorem rowCheck4385 : row4385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4385 := by decide +kernel

theorem rowEval4385 (x : Key → ℝ) : Integer.Sparse.eval row4385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4385, Integer.Sparse.eval_collectBalanced, rawRowCheck4385]

def rawRow4386 : Integer.Sparse Key := [(key2540, -2), (key2551, -2), (key2534, -2), (key2534, 6), (key2476, 2), (key2499, 2), (key2467, 2), (key2467, -2), (key2373, -2), (key2401, -2), (key2464, -6), (key2464, 2), (key2370, 2), (key2762, 2)]

theorem rawRowCheck4386 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form11 = rawRow4386 := by decide +kernel

def row4386 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -4), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2)]

theorem rowCheck4386 : row4386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4386 := by decide +kernel

theorem rowEval4386 (x : Key → ℝ) : Integer.Sparse.eval row4386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck4386, Integer.Sparse.eval_collectBalanced, rawRowCheck4386]

def rawRow4387 : Integer.Sparse Key := [(key2551, -2), (key2540, -2), (key2534, -2), (key2534, 6), (key2499, 2), (key2476, 2), (key2467, 2), (key2467, -2), (key2401, -2), (key2373, -2), (key2464, -6), (key2464, 2), (key2398, 2), (key2583, 2)]

theorem rawRowCheck4387 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form11 = rawRow4387 := by decide +kernel

def row4387 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -4), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2)]

theorem rowCheck4387 : row4387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4387 := by decide +kernel

theorem rowEval4387 (x : Key → ℝ) : Integer.Sparse.eval row4387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck4387, Integer.Sparse.eval_collectBalanced, rawRowCheck4387]

def rawRow4388 : Integer.Sparse Key := [(key2892, -2), (key2895, -2), (key2902, -2), (key2781, 1), (key2790, 1), (key2804, 1), (key2856, 1), (key2825, 1), (key2866, 1), (key2971, 2), (key2974, 2), (key2981, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2974, -1), (key2958, -1), (key2981, -1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1)]

theorem rawRowCheck4388 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form12 = rawRow4388 := by decide +kernel

def row4388 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

theorem rowCheck4388 : row4388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4388 := by decide +kernel

theorem rowEval4388 (x : Key → ℝ) : Integer.Sparse.eval row4388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4388, Integer.Sparse.eval_collectBalanced, rawRowCheck4388]

def rawRow4389 : Integer.Sparse Key := [(key2895, -2), (key2892, -2), (key2902, -2), (key2790, 1), (key2781, 1), (key2856, 1), (key2804, 1), (key2866, 1), (key2825, 1), (key2974, 2), (key2971, 2), (key2981, 2), (key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2941, -1), (key2935, -1), (key2974, -1), (key2947, -1), (key2981, -1), (key2958, -1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1)]

theorem rawRowCheck4389 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form12 = rawRow4389 := by decide +kernel

def row4389 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

theorem rowCheck4389 : row4389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4389 := by decide +kernel

theorem rowEval4389 (x : Key → ℝ) : Integer.Sparse.eval row4389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4389, Integer.Sparse.eval_collectBalanced, rawRowCheck4389]

def rawRow4390 : Integer.Sparse Key := [(key2892, -2), (key2902, -2), (key2895, -2), (key2804, 1), (key2825, 1), (key2781, 1), (key2866, 1), (key2790, 1), (key2856, 1), (key2971, 2), (key2981, 2), (key2974, 2), (key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2947, -1), (key2958, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1)]

theorem rawRowCheck4390 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form12 = rawRow4390 := by decide +kernel

def row4390 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

theorem rowCheck4390 : row4390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4390 := by decide +kernel

theorem rowEval4390 (x : Key → ℝ) : Integer.Sparse.eval row4390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4390, Integer.Sparse.eval_collectBalanced, rawRowCheck4390]

def rawRow4391 : Integer.Sparse Key := [(key2902, -2), (key2892, -2), (key2895, -2), (key2825, 1), (key2804, 1), (key2866, 1), (key2781, 1), (key2856, 1), (key2790, 1), (key2981, 2), (key2971, 2), (key2974, 2), (key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2974, -1), (key2941, -1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1)]

theorem rawRowCheck4391 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form12 = rawRow4391 := by decide +kernel

def row4391 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

theorem rowCheck4391 : row4391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4391 := by decide +kernel

theorem rowEval4391 (x : Key → ℝ) : Integer.Sparse.eval row4391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4391, Integer.Sparse.eval_collectBalanced, rawRowCheck4391]

def rawRow4392 : Integer.Sparse Key := [(key2895, -2), (key2902, -2), (key2892, -2), (key2856, 1), (key2866, 1), (key2790, 1), (key2825, 1), (key2781, 1), (key2804, 1), (key2974, 2), (key2981, 2), (key2971, 2), (key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2974, -1), (key2981, -1), (key2941, -1), (key2958, -1), (key2935, -1), (key2947, -1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1)]

theorem rawRowCheck4392 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form12 = rawRow4392 := by decide +kernel

def row4392 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

theorem rowCheck4392 : row4392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4392 := by decide +kernel

theorem rowEval4392 (x : Key → ℝ) : Integer.Sparse.eval row4392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4392, Integer.Sparse.eval_collectBalanced, rawRowCheck4392]

def rawRow4393 : Integer.Sparse Key := [(key2902, -2), (key2895, -2), (key2892, -2), (key2866, 1), (key2856, 1), (key2825, 1), (key2790, 1), (key2804, 1), (key2781, 1), (key2981, 2), (key2974, 2), (key2971, 2), (key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2981, -1), (key2974, -1), (key2958, -1), (key2941, -1), (key2947, -1), (key2935, -1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

theorem rawRowCheck4393 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form12 = rawRow4393 := by decide +kernel

def row4393 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

theorem rowCheck4393 : row4393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4393 := by decide +kernel

theorem rowEval4393 (x : Key → ℝ) : Integer.Sparse.eval row4393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4393, Integer.Sparse.eval_collectBalanced, rawRowCheck4393]

def rawRow4394 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2892, 2), (key2895, 2), (key2902, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2856, -1), (key2825, -1), (key2866, -1), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1)]

theorem rawRowCheck4394 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form12 = rawRow4394 := by decide +kernel

def row4394 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck4394 : row4394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4394 := by decide +kernel

theorem rowEval4394 (x : Key → ℝ) : Integer.Sparse.eval row4394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4394, Integer.Sparse.eval_collectBalanced, rawRowCheck4394]

def rawRow4395 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2895, 2), (key2892, 2), (key2902, 2), (key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2790, -1), (key2781, -1), (key2856, -1), (key2804, -1), (key2866, -1), (key2825, -1), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1)]

theorem rawRowCheck4395 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form12 = rawRow4395 := by decide +kernel

def row4395 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck4395 : row4395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4395 := by decide +kernel

theorem rowEval4395 (x : Key → ℝ) : Integer.Sparse.eval row4395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4395, Integer.Sparse.eval_collectBalanced, rawRowCheck4395]

def rawRow4396 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2892, 2), (key2902, 2), (key2895, 2), (key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2804, -1), (key2825, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1)]

theorem rawRowCheck4396 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form12 = rawRow4396 := by decide +kernel

def row4396 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck4396 : row4396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4396 := by decide +kernel

theorem rowEval4396 (x : Key → ℝ) : Integer.Sparse.eval row4396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4396, Integer.Sparse.eval_collectBalanced, rawRowCheck4396]

def rawRow4397 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2902, 2), (key2892, 2), (key2895, 2), (key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2856, -1), (key2790, -1), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1)]

theorem rawRowCheck4397 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form12 = rawRow4397 := by decide +kernel

def row4397 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck4397 : row4397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4397 := by decide +kernel

theorem rowEval4397 (x : Key → ℝ) : Integer.Sparse.eval row4397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4397, Integer.Sparse.eval_collectBalanced, rawRowCheck4397]

def rawRow4398 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 2), (key2902, 2), (key2892, 2), (key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2856, -1), (key2866, -1), (key2790, -1), (key2825, -1), (key2781, -1), (key2804, -1), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1)]

theorem rawRowCheck4398 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form12 = rawRow4398 := by decide +kernel

def row4398 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck4398 : row4398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4398 := by decide +kernel

theorem rowEval4398 (x : Key → ℝ) : Integer.Sparse.eval row4398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4398, Integer.Sparse.eval_collectBalanced, rawRowCheck4398]

def rawRow4399 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 2), (key2895, 2), (key2892, 2), (key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2866, -1), (key2856, -1), (key2825, -1), (key2790, -1), (key2804, -1), (key2781, -1), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

theorem rawRowCheck4399 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form12 = rawRow4399 := by decide +kernel

def row4399 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

theorem rowCheck4399 : row4399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4399 := by decide +kernel

theorem rowEval4399 (x : Key → ℝ) : Integer.Sparse.eval row4399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4399, Integer.Sparse.eval_collectBalanced, rawRowCheck4399]

def rawRow4400 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2200, -2), (key2194, 6), (key2302, 2), (key2303, 2), (key2310, 2), (key2092, -2), (key2303, -2), (key2341, -2), (key2305, -6), (key2095, 2), (key2305, 2), (key2343, 2)]

theorem rawRowCheck4400 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form13 = rawRow4400 := by decide +kernel

def row4400 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck4400 : row4400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4400 := by decide +kernel

theorem rowEval4400 (x : Key → ℝ) : Integer.Sparse.eval row4400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4400, Integer.Sparse.eval_collectBalanced, rawRowCheck4400]

def rawRow4401 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2200, -2), (key2194, 6), (key2303, 2), (key2302, 2), (key2310, 2), (key2092, -2), (key2341, -2), (key2303, -2), (key2305, -6), (key2095, 2), (key2343, 2), (key2305, 2)]

theorem rawRowCheck4401 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form13 = rawRow4401 := by decide +kernel

def row4401 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck4401 : row4401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4401 := by decide +kernel

theorem rowEval4401 (x : Key → ℝ) : Integer.Sparse.eval row4401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4401, Integer.Sparse.eval_collectBalanced, rawRowCheck4401]

def rawRow4402 : Integer.Sparse Key := [(key2193, -2), (key2200, -2), (key2194, -2), (key2194, 6), (key2302, 2), (key2310, 2), (key2303, 2), (key2303, -2), (key2092, -2), (key2341, -2), (key2305, -6), (key2305, 2), (key2095, 2), (key2343, 2)]

theorem rawRowCheck4402 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form13 = rawRow4402 := by decide +kernel

def row4402 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck4402 : row4402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4402 := by decide +kernel

theorem rowEval4402 (x : Key → ℝ) : Integer.Sparse.eval row4402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4402, Integer.Sparse.eval_collectBalanced, rawRowCheck4402]

def rawRow4403 : Integer.Sparse Key := [(key2200, -2), (key2193, -2), (key2194, -2), (key2194, 6), (key2310, 2), (key2302, 2), (key2303, 2), (key2303, -2), (key2341, -2), (key2092, -2), (key2305, -6), (key2305, 2), (key2343, 2), (key2095, 2)]

theorem rawRowCheck4403 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form13 = rawRow4403 := by decide +kernel

def row4403 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck4403 : row4403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4403 := by decide +kernel

theorem rowEval4403 (x : Key → ℝ) : Integer.Sparse.eval row4403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4403, Integer.Sparse.eval_collectBalanced, rawRowCheck4403]

def rawRow4404 : Integer.Sparse Key := [(key2194, -2), (key2200, -2), (key2193, -2), (key2194, 6), (key2303, 2), (key2310, 2), (key2302, 2), (key2341, -2), (key2092, -2), (key2303, -2), (key2305, -6), (key2343, 2), (key2095, 2), (key2305, 2)]

theorem rawRowCheck4404 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form13 = rawRow4404 := by decide +kernel

def row4404 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck4404 : row4404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4404 := by decide +kernel

theorem rowEval4404 (x : Key → ℝ) : Integer.Sparse.eval row4404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4404, Integer.Sparse.eval_collectBalanced, rawRowCheck4404]

def rawRow4405 : Integer.Sparse Key := [(key2200, -2), (key2194, -2), (key2193, -2), (key2194, 6), (key2310, 2), (key2303, 2), (key2302, 2), (key2341, -2), (key2303, -2), (key2092, -2), (key2305, -6), (key2343, 2), (key2305, 2), (key2095, 2)]

theorem rawRowCheck4405 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form13 = rawRow4405 := by decide +kernel

def row4405 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

theorem rowCheck4405 : row4405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4405 := by decide +kernel

theorem rowEval4405 (x : Key → ℝ) : Integer.Sparse.eval row4405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4405, Integer.Sparse.eval_collectBalanced, rawRowCheck4405]

def rawRow4406 : Integer.Sparse Key := [(key2302, -2), (key2303, -2), (key2310, -2), (key2305, 6), (key2193, 2), (key2194, 2), (key2200, 2), (key2095, -2), (key2305, -2), (key2343, -2), (key2194, -6), (key2092, 2), (key2303, 2), (key2341, 2)]

theorem rawRowCheck4406 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form13 = rawRow4406 := by decide +kernel

def row4406 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck4406 : row4406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4406 := by decide +kernel

theorem rowEval4406 (x : Key → ℝ) : Integer.Sparse.eval row4406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4406, Integer.Sparse.eval_collectBalanced, rawRowCheck4406]

def rawRow4407 : Integer.Sparse Key := [(key2303, -2), (key2302, -2), (key2310, -2), (key2305, 6), (key2194, 2), (key2193, 2), (key2200, 2), (key2095, -2), (key2343, -2), (key2305, -2), (key2194, -6), (key2092, 2), (key2341, 2), (key2303, 2)]

theorem rawRowCheck4407 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form13 = rawRow4407 := by decide +kernel

def row4407 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck4407 : row4407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4407 := by decide +kernel

theorem rowEval4407 (x : Key → ℝ) : Integer.Sparse.eval row4407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4407, Integer.Sparse.eval_collectBalanced, rawRowCheck4407]

def rawRow4408 : Integer.Sparse Key := [(key2302, -2), (key2310, -2), (key2303, -2), (key2305, 6), (key2193, 2), (key2200, 2), (key2194, 2), (key2305, -2), (key2095, -2), (key2343, -2), (key2194, -6), (key2303, 2), (key2092, 2), (key2341, 2)]

theorem rawRowCheck4408 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form13 = rawRow4408 := by decide +kernel

def row4408 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck4408 : row4408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4408 := by decide +kernel

theorem rowEval4408 (x : Key → ℝ) : Integer.Sparse.eval row4408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4408, Integer.Sparse.eval_collectBalanced, rawRowCheck4408]

def rawRow4409 : Integer.Sparse Key := [(key2310, -2), (key2302, -2), (key2303, -2), (key2305, 6), (key2200, 2), (key2193, 2), (key2194, 2), (key2305, -2), (key2343, -2), (key2095, -2), (key2194, -6), (key2303, 2), (key2341, 2), (key2092, 2)]

theorem rawRowCheck4409 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form13 = rawRow4409 := by decide +kernel

def row4409 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck4409 : row4409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4409 := by decide +kernel

theorem rowEval4409 (x : Key → ℝ) : Integer.Sparse.eval row4409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4409, Integer.Sparse.eval_collectBalanced, rawRowCheck4409]

def rawRow4410 : Integer.Sparse Key := [(key2303, -2), (key2310, -2), (key2302, -2), (key2305, 6), (key2194, 2), (key2200, 2), (key2193, 2), (key2343, -2), (key2095, -2), (key2305, -2), (key2194, -6), (key2341, 2), (key2092, 2), (key2303, 2)]

theorem rawRowCheck4410 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form13 = rawRow4410 := by decide +kernel

def row4410 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck4410 : row4410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4410 := by decide +kernel

theorem rowEval4410 (x : Key → ℝ) : Integer.Sparse.eval row4410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4410, Integer.Sparse.eval_collectBalanced, rawRowCheck4410]

def rawRow4411 : Integer.Sparse Key := [(key2310, -2), (key2303, -2), (key2302, -2), (key2305, 6), (key2200, 2), (key2194, 2), (key2193, 2), (key2343, -2), (key2305, -2), (key2095, -2), (key2194, -6), (key2341, 2), (key2303, 2), (key2092, 2)]

theorem rawRowCheck4411 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form13 = rawRow4411 := by decide +kernel

def row4411 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

theorem rowCheck4411 : row4411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4411 := by decide +kernel

theorem rowEval4411 (x : Key → ℝ) : Integer.Sparse.eval row4411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4411, Integer.Sparse.eval_collectBalanced, rawRowCheck4411]

def rawRow4412 : Integer.Sparse Key := [(key2303, -2), (key2305, -2), (key2310, -2), (key2302, 6), (key2341, 2), (key2343, 2), (key2347, 2), (key2091, -2), (key2193, -2), (key2302, -2), (key2341, -6), (key2092, 2), (key2194, 2), (key2303, 2)]

theorem rawRowCheck4412 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form13 = rawRow4412 := by decide +kernel

def row4412 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck4412 : row4412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4412 := by decide +kernel

theorem rowEval4412 (x : Key → ℝ) : Integer.Sparse.eval row4412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4412, Integer.Sparse.eval_collectBalanced, rawRowCheck4412]

def rawRow4413 : Integer.Sparse Key := [(key2305, -2), (key2303, -2), (key2310, -2), (key2302, 6), (key2343, 2), (key2341, 2), (key2347, 2), (key2091, -2), (key2302, -2), (key2193, -2), (key2341, -6), (key2092, 2), (key2303, 2), (key2194, 2)]

theorem rawRowCheck4413 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form13 = rawRow4413 := by decide +kernel

def row4413 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck4413 : row4413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4413 := by decide +kernel

theorem rowEval4413 (x : Key → ℝ) : Integer.Sparse.eval row4413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4413, Integer.Sparse.eval_collectBalanced, rawRowCheck4413]

def rawRow4414 : Integer.Sparse Key := [(key2303, -2), (key2310, -2), (key2305, -2), (key2302, 6), (key2341, 2), (key2347, 2), (key2343, 2), (key2193, -2), (key2091, -2), (key2302, -2), (key2341, -6), (key2194, 2), (key2092, 2), (key2303, 2)]

theorem rawRowCheck4414 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form13 = rawRow4414 := by decide +kernel

def row4414 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck4414 : row4414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4414 := by decide +kernel

theorem rowEval4414 (x : Key → ℝ) : Integer.Sparse.eval row4414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4414, Integer.Sparse.eval_collectBalanced, rawRowCheck4414]

def rawRow4415 : Integer.Sparse Key := [(key2310, -2), (key2303, -2), (key2305, -2), (key2302, 6), (key2347, 2), (key2341, 2), (key2343, 2), (key2193, -2), (key2302, -2), (key2091, -2), (key2341, -6), (key2194, 2), (key2303, 2), (key2092, 2)]

theorem rawRowCheck4415 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form13 = rawRow4415 := by decide +kernel

def row4415 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck4415 : row4415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4415 := by decide +kernel

theorem rowEval4415 (x : Key → ℝ) : Integer.Sparse.eval row4415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4415, Integer.Sparse.eval_collectBalanced, rawRowCheck4415]

def rawRow4416 : Integer.Sparse Key := [(key2305, -2), (key2310, -2), (key2303, -2), (key2302, 6), (key2343, 2), (key2347, 2), (key2341, 2), (key2302, -2), (key2091, -2), (key2193, -2), (key2341, -6), (key2303, 2), (key2092, 2), (key2194, 2)]

theorem rawRowCheck4416 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form13 = rawRow4416 := by decide +kernel

def row4416 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck4416 : row4416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4416 := by decide +kernel

theorem rowEval4416 (x : Key → ℝ) : Integer.Sparse.eval row4416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4416, Integer.Sparse.eval_collectBalanced, rawRowCheck4416]

def rawRow4417 : Integer.Sparse Key := [(key2310, -2), (key2305, -2), (key2303, -2), (key2302, 6), (key2347, 2), (key2343, 2), (key2341, 2), (key2302, -2), (key2193, -2), (key2091, -2), (key2341, -6), (key2303, 2), (key2194, 2), (key2092, 2)]

theorem rawRowCheck4417 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form13 = rawRow4417 := by decide +kernel

def row4417 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

theorem rowCheck4417 : row4417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4417 := by decide +kernel

theorem rowEval4417 (x : Key → ℝ) : Integer.Sparse.eval row4417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4417, Integer.Sparse.eval_collectBalanced, rawRowCheck4417]

def rawRow4418 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2347, -2), (key2341, 6), (key2303, 2), (key2305, 2), (key2310, 2), (key2092, -2), (key2194, -2), (key2303, -2), (key2302, -6), (key2091, 2), (key2193, 2), (key2302, 2)]

theorem rawRowCheck4418 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form13 = rawRow4418 := by decide +kernel

def row4418 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck4418 : row4418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4418 := by decide +kernel

theorem rowEval4418 (x : Key → ℝ) : Integer.Sparse.eval row4418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4418, Integer.Sparse.eval_collectBalanced, rawRowCheck4418]

def rawRow4419 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2347, -2), (key2341, 6), (key2305, 2), (key2303, 2), (key2310, 2), (key2092, -2), (key2303, -2), (key2194, -2), (key2302, -6), (key2091, 2), (key2302, 2), (key2193, 2)]

theorem rawRowCheck4419 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form13 = rawRow4419 := by decide +kernel

def row4419 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck4419 : row4419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4419 := by decide +kernel

theorem rowEval4419 (x : Key → ℝ) : Integer.Sparse.eval row4419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4419, Integer.Sparse.eval_collectBalanced, rawRowCheck4419]

def rawRow4420 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2343, -2), (key2341, 6), (key2303, 2), (key2310, 2), (key2305, 2), (key2194, -2), (key2092, -2), (key2303, -2), (key2302, -6), (key2193, 2), (key2091, 2), (key2302, 2)]

theorem rawRowCheck4420 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form13 = rawRow4420 := by decide +kernel

def row4420 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck4420 : row4420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4420 := by decide +kernel

theorem rowEval4420 (x : Key → ℝ) : Integer.Sparse.eval row4420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4420, Integer.Sparse.eval_collectBalanced, rawRowCheck4420]

def rawRow4421 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2343, -2), (key2341, 6), (key2310, 2), (key2303, 2), (key2305, 2), (key2194, -2), (key2303, -2), (key2092, -2), (key2302, -6), (key2193, 2), (key2302, 2), (key2091, 2)]

theorem rawRowCheck4421 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form13 = rawRow4421 := by decide +kernel

def row4421 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck4421 : row4421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4421 := by decide +kernel

theorem rowEval4421 (x : Key → ℝ) : Integer.Sparse.eval row4421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4421, Integer.Sparse.eval_collectBalanced, rawRowCheck4421]

def rawRow4422 : Integer.Sparse Key := [(key2343, -2), (key2347, -2), (key2341, -2), (key2341, 6), (key2305, 2), (key2310, 2), (key2303, 2), (key2303, -2), (key2092, -2), (key2194, -2), (key2302, -6), (key2302, 2), (key2091, 2), (key2193, 2)]

theorem rawRowCheck4422 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form13 = rawRow4422 := by decide +kernel

def row4422 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck4422 : row4422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4422 := by decide +kernel

theorem rowEval4422 (x : Key → ℝ) : Integer.Sparse.eval row4422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4422, Integer.Sparse.eval_collectBalanced, rawRowCheck4422]

def rawRow4423 : Integer.Sparse Key := [(key2347, -2), (key2343, -2), (key2341, -2), (key2341, 6), (key2310, 2), (key2305, 2), (key2303, 2), (key2303, -2), (key2194, -2), (key2092, -2), (key2302, -6), (key2302, 2), (key2193, 2), (key2091, 2)]

theorem rawRowCheck4423 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form13 = rawRow4423 := by decide +kernel

def row4423 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

theorem rowCheck4423 : row4423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4423 := by decide +kernel

theorem rowEval4423 (x : Key → ℝ) : Integer.Sparse.eval row4423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4423, Integer.Sparse.eval_collectBalanced, rawRowCheck4423]

def rawRow4424 : Integer.Sparse Key := [(key2406, -2), (key2437, -2), (key2440, -2), (key2406, 2), (key2409, 2), (key2440, 2), (key2472, 2), (key2503, 2), (key2506, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, 1), (key2392, 1), (key2480, 1), (key2543, 1), (key2522, 1), (key2563, 1)]

theorem rawRowCheck4424 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form14 = rawRow4424 := by decide +kernel

def row4424 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

theorem rowCheck4424 : row4424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4424 := by decide +kernel

theorem rowEval4424 (x : Key → ℝ) : Integer.Sparse.eval row4424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4424, Integer.Sparse.eval_collectBalanced, rawRowCheck4424]

def rawRow4425 : Integer.Sparse Key := [(key2406, -2), (key2440, -2), (key2437, -2), (key2409, 2), (key2406, 2), (key2440, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, 1), (key2390, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2522, 1)]

theorem rawRowCheck4425 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form14 = rawRow4425 := by decide +kernel

def row4425 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

theorem rowCheck4425 : row4425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4425 := by decide +kernel

theorem rowEval4425 (x : Key → ℝ) : Integer.Sparse.eval row4425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4425, Integer.Sparse.eval_collectBalanced, rawRowCheck4425]

def rawRow4426 : Integer.Sparse Key := [(key2437, -2), (key2406, -2), (key2440, -2), (key2406, 2), (key2440, 2), (key2409, 2), (key2503, 2), (key2472, 2), (key2506, 2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, 1), (key2522, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2543, 1)]

theorem rawRowCheck4426 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form14 = rawRow4426 := by decide +kernel

def row4426 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

theorem rowCheck4426 : row4426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4426 := by decide +kernel

theorem rowEval4426 (x : Key → ℝ) : Integer.Sparse.eval row4426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4426, Integer.Sparse.eval_collectBalanced, rawRowCheck4426]

def rawRow4427 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2406, -2), (key2440, 2), (key2406, 2), (key2409, 2), (key2503, 2), (key2506, 2), (key2472, 2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2543, 1), (key2392, 1)]

theorem rawRowCheck4427 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form14 = rawRow4427 := by decide +kernel

def row4427 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

theorem rowCheck4427 : row4427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4427 := by decide +kernel

theorem rowEval4427 (x : Key → ℝ) : Integer.Sparse.eval row4427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4427, Integer.Sparse.eval_collectBalanced, rawRowCheck4427]

def rawRow4428 : Integer.Sparse Key := [(key2440, -2), (key2406, -2), (key2437, -2), (key2409, 2), (key2440, 2), (key2406, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2390, 1), (key2480, 1)]

theorem rawRowCheck4428 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form14 = rawRow4428 := by decide +kernel

def row4428 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

theorem rowCheck4428 : row4428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4428 := by decide +kernel

theorem rowEval4428 (x : Key → ℝ) : Integer.Sparse.eval row4428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4428, Integer.Sparse.eval_collectBalanced, rawRowCheck4428]

def rawRow4429 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2406, -2), (key2440, 2), (key2409, 2), (key2406, 2), (key2506, 2), (key2503, 2), (key2472, 2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, 1), (key2543, 1), (key2522, 1), (key2392, 1), (key2480, 1), (key2390, 1)]

theorem rawRowCheck4429 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form14 = rawRow4429 := by decide +kernel

def row4429 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

theorem rowCheck4429 : row4429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4429 := by decide +kernel

theorem rowEval4429 (x : Key → ℝ) : Integer.Sparse.eval row4429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4429, Integer.Sparse.eval_collectBalanced, rawRowCheck4429]

def rawRow4430 : Integer.Sparse Key := [(key2472, -2), (key2503, -2), (key2506, -2), (key2480, 2), (key2482, 2), (key2522, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, 1), (key2381, 1), (key2472, 1), (key2538, 1), (key2506, 1), (key2554, 1)]

theorem rawRowCheck4430 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form14 = rawRow4430 := by decide +kernel

def row4430 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

theorem rowCheck4430 : row4430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4430 := by decide +kernel

theorem rowEval4430 (x : Key → ℝ) : Integer.Sparse.eval row4430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4430, Integer.Sparse.eval_collectBalanced, rawRowCheck4430]

def rawRow4431 : Integer.Sparse Key := [(key2472, -2), (key2506, -2), (key2503, -2), (key2482, 2), (key2480, 2), (key2522, 2), (key2406, 2), (key2440, 2), (key2437, 2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, 1), (key2378, 1), (key2538, 1), (key2472, 1), (key2554, 1), (key2506, 1)]

theorem rawRowCheck4431 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form14 = rawRow4431 := by decide +kernel

def row4431 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

theorem rowCheck4431 : row4431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4431 := by decide +kernel

theorem rowEval4431 (x : Key → ℝ) : Integer.Sparse.eval row4431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4431, Integer.Sparse.eval_collectBalanced, rawRowCheck4431]

def rawRow4432 : Integer.Sparse Key := [(key2503, -2), (key2472, -2), (key2506, -2), (key2480, 2), (key2522, 2), (key2482, 2), (key2437, 2), (key2406, 2), (key2440, 2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, 1), (key2506, 1), (key2378, 1), (key2554, 1), (key2381, 1), (key2538, 1)]

theorem rawRowCheck4432 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form14 = rawRow4432 := by decide +kernel

def row4432 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

theorem rowCheck4432 : row4432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4432 := by decide +kernel

theorem rowEval4432 (x : Key → ℝ) : Integer.Sparse.eval row4432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4432, Integer.Sparse.eval_collectBalanced, rawRowCheck4432]

def rawRow4433 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2472, -2), (key2522, 2), (key2480, 2), (key2482, 2), (key2437, 2), (key2440, 2), (key2406, 2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, 1), (key2472, 1), (key2554, 1), (key2378, 1), (key2538, 1), (key2381, 1)]

theorem rawRowCheck4433 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form14 = rawRow4433 := by decide +kernel

def row4433 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

theorem rowCheck4433 : row4433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4433 := by decide +kernel

theorem rowEval4433 (x : Key → ℝ) : Integer.Sparse.eval row4433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4433, Integer.Sparse.eval_collectBalanced, rawRowCheck4433]

def rawRow4434 : Integer.Sparse Key := [(key2506, -2), (key2472, -2), (key2503, -2), (key2482, 2), (key2522, 2), (key2480, 2), (key2440, 2), (key2406, 2), (key2437, 2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, 1), (key2554, 1), (key2381, 1), (key2506, 1), (key2378, 1), (key2472, 1)]

theorem rawRowCheck4434 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form14 = rawRow4434 := by decide +kernel

def row4434 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

theorem rowCheck4434 : row4434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4434 := by decide +kernel

theorem rowEval4434 (x : Key → ℝ) : Integer.Sparse.eval row4434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4434, Integer.Sparse.eval_collectBalanced, rawRowCheck4434]

def rawRow4435 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2472, -2), (key2522, 2), (key2482, 2), (key2480, 2), (key2440, 2), (key2437, 2), (key2406, 2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, 1), (key2538, 1), (key2506, 1), (key2381, 1), (key2472, 1), (key2378, 1)]

theorem rawRowCheck4435 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form14 = rawRow4435 := by decide +kernel

def row4435 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

theorem rowCheck4435 : row4435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4435 := by decide +kernel

theorem rowEval4435 (x : Key → ℝ) : Integer.Sparse.eval row4435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4435, Integer.Sparse.eval_collectBalanced, rawRowCheck4435]

def rawRow4436 : Integer.Sparse Key := [(key2482, -2), (key2506, -2), (key2522, -2), (key2472, 2), (key2480, 2), (key2503, 2), (key2543, 2), (key2554, 2), (key2563, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, -1), (key2503, -1), (key2538, -2), (key2543, -2), (key2554, -2), (key2381, 1), (key2392, 1), (key2409, 1), (key2482, 1), (key2440, 1), (key2506, 1)]

theorem rawRowCheck4436 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form14 = rawRow4436 := by decide +kernel

def row4436 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

theorem rowCheck4436 : row4436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4436 := by decide +kernel

theorem rowEval4436 (x : Key → ℝ) : Integer.Sparse.eval row4436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4436, Integer.Sparse.eval_collectBalanced, rawRowCheck4436]

def rawRow4437 : Integer.Sparse Key := [(key2482, -2), (key2522, -2), (key2506, -2), (key2480, 2), (key2472, 2), (key2503, 2), (key2543, 2), (key2563, 2), (key2554, 2), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, -1), (key2437, -1), (key2543, -2), (key2538, -2), (key2554, -2), (key2392, 1), (key2381, 1), (key2482, 1), (key2409, 1), (key2506, 1), (key2440, 1)]

theorem rawRowCheck4437 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form14 = rawRow4437 := by decide +kernel

def row4437 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

theorem rowCheck4437 : row4437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4437 := by decide +kernel

theorem rowEval4437 (x : Key → ℝ) : Integer.Sparse.eval row4437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4437, Integer.Sparse.eval_collectBalanced, rawRowCheck4437]

def rawRow4438 : Integer.Sparse Key := [(key2506, -2), (key2482, -2), (key2522, -2), (key2472, 2), (key2503, 2), (key2480, 2), (key2554, 2), (key2543, 2), (key2563, 2), (key2406, -1), (key2437, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2538, -2), (key2554, -2), (key2543, -2), (key2409, 1), (key2440, 1), (key2381, 1), (key2506, 1), (key2392, 1), (key2482, 1)]

theorem rawRowCheck4438 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form14 = rawRow4438 := by decide +kernel

def row4438 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

theorem rowCheck4438 : row4438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4438 := by decide +kernel

theorem rowEval4438 (x : Key → ℝ) : Integer.Sparse.eval row4438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4438, Integer.Sparse.eval_collectBalanced, rawRowCheck4438]

def rawRow4439 : Integer.Sparse Key := [(key2506, -2), (key2522, -2), (key2482, -2), (key2503, 2), (key2472, 2), (key2480, 2), (key2554, 2), (key2563, 2), (key2543, 2), (key2437, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2480, -1), (key2390, -1), (key2554, -2), (key2538, -2), (key2543, -2), (key2440, 1), (key2409, 1), (key2506, 1), (key2381, 1), (key2482, 1), (key2392, 1)]

theorem rawRowCheck4439 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form14 = rawRow4439 := by decide +kernel

def row4439 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

theorem rowCheck4439 : row4439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4439 := by decide +kernel

theorem rowEval4439 (x : Key → ℝ) : Integer.Sparse.eval row4439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4439, Integer.Sparse.eval_collectBalanced, rawRowCheck4439]

def rawRow4440 : Integer.Sparse Key := [(key2522, -2), (key2482, -2), (key2506, -2), (key2480, 2), (key2503, 2), (key2472, 2), (key2563, 2), (key2543, 2), (key2554, 2), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, -1), (key2406, -1), (key2543, -2), (key2554, -2), (key2538, -2), (key2482, 1), (key2506, 1), (key2392, 1), (key2440, 1), (key2381, 1), (key2409, 1)]

theorem rawRowCheck4440 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form14 = rawRow4440 := by decide +kernel

def row4440 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

theorem rowCheck4440 : row4440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4440 := by decide +kernel

theorem rowEval4440 (x : Key → ℝ) : Integer.Sparse.eval row4440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4440, Integer.Sparse.eval_collectBalanced, rawRowCheck4440]

def rawRow4441 : Integer.Sparse Key := [(key2522, -2), (key2506, -2), (key2482, -2), (key2503, 2), (key2480, 2), (key2472, 2), (key2563, 2), (key2554, 2), (key2543, 2), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2554, -2), (key2543, -2), (key2538, -2), (key2506, 1), (key2482, 1), (key2440, 1), (key2392, 1), (key2409, 1), (key2381, 1)]

theorem rawRowCheck4441 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form14 = rawRow4441 := by decide +kernel

def row4441 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

theorem rowCheck4441 : row4441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4441 := by decide +kernel

theorem rowEval4441 (x : Key → ℝ) : Integer.Sparse.eval row4441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4441, Integer.Sparse.eval_collectBalanced, rawRowCheck4441]

def rawRow4442 : Integer.Sparse Key := [(key2543, -2), (key2554, -2), (key2563, -2), (key2538, 2), (key2543, 2), (key2554, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2482, -1), (key2440, -1), (key2506, -1), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, 1), (key2390, 1), (key2406, 1), (key2480, 1), (key2437, 1), (key2503, 1)]

theorem rawRowCheck4442 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form14 = rawRow4442 := by decide +kernel

def row4442 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

theorem rowCheck4442 : row4442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4442 := by decide +kernel

theorem rowEval4442 (x : Key → ℝ) : Integer.Sparse.eval row4442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4442, Integer.Sparse.eval_collectBalanced, rawRowCheck4442]

def rawRow4443 : Integer.Sparse Key := [(key2543, -2), (key2563, -2), (key2554, -2), (key2543, 2), (key2538, 2), (key2554, 2), (key2482, 2), (key2522, 2), (key2506, 2), (key2392, -1), (key2381, -1), (key2482, -1), (key2409, -1), (key2506, -1), (key2440, -1), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2437, 1)]

theorem rawRowCheck4443 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form14 = rawRow4443 := by decide +kernel

def row4443 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

theorem rowCheck4443 : row4443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4443 := by decide +kernel

theorem rowEval4443 (x : Key → ℝ) : Integer.Sparse.eval row4443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4443, Integer.Sparse.eval_collectBalanced, rawRowCheck4443]

def rawRow4444 : Integer.Sparse Key := [(key2554, -2), (key2543, -2), (key2563, -2), (key2538, 2), (key2554, 2), (key2543, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2409, -1), (key2440, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, 1), (key2437, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2480, 1)]

theorem rawRowCheck4444 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form14 = rawRow4444 := by decide +kernel

def row4444 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

theorem rowCheck4444 : row4444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4444 := by decide +kernel

theorem rowEval4444 (x : Key → ℝ) : Integer.Sparse.eval row4444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4444, Integer.Sparse.eval_collectBalanced, rawRowCheck4444]

def rawRow4445 : Integer.Sparse Key := [(key2554, -2), (key2563, -2), (key2543, -2), (key2554, 2), (key2538, 2), (key2543, 2), (key2506, 2), (key2522, 2), (key2482, 2), (key2440, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2482, -1), (key2392, -1), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2480, 1), (key2390, 1)]

theorem rawRowCheck4445 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form14 = rawRow4445 := by decide +kernel

def row4445 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

theorem rowCheck4445 : row4445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4445 := by decide +kernel

theorem rowEval4445 (x : Key → ℝ) : Integer.Sparse.eval row4445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4445, Integer.Sparse.eval_collectBalanced, rawRowCheck4445]

def rawRow4446 : Integer.Sparse Key := [(key2563, -2), (key2543, -2), (key2554, -2), (key2543, 2), (key2554, 2), (key2538, 2), (key2522, 2), (key2482, 2), (key2506, 2), (key2482, -1), (key2506, -1), (key2392, -1), (key2440, -1), (key2381, -1), (key2409, -1), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2378, 1), (key2406, 1)]

theorem rawRowCheck4446 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form14 = rawRow4446 := by decide +kernel

def row4446 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

theorem rowCheck4446 : row4446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4446 := by decide +kernel

theorem rowEval4446 (x : Key → ℝ) : Integer.Sparse.eval row4446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4446, Integer.Sparse.eval_collectBalanced, rawRowCheck4446]

def rawRow4447 : Integer.Sparse Key := [(key2563, -2), (key2554, -2), (key2543, -2), (key2554, 2), (key2543, 2), (key2538, 2), (key2522, 2), (key2506, 2), (key2482, 2), (key2506, -1), (key2482, -1), (key2440, -1), (key2392, -1), (key2409, -1), (key2381, -1), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, 1), (key2480, 1), (key2437, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

theorem rawRowCheck4447 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form14 = rawRow4447 := by decide +kernel

def row4447 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

theorem rowCheck4447 : row4447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4447 := by decide +kernel

theorem rowEval4447 (x : Key → ℝ) : Integer.Sparse.eval row4447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4447, Integer.Sparse.eval_collectBalanced, rawRowCheck4447]

def rawRow4448 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1), (key2637, -2), (key2857, -2), (key2975, -2), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1)]

theorem rawRowCheck4448 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form15 = rawRow4448 := by decide +kernel

def row4448 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck4448 : row4448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4448 := by decide +kernel

theorem rowEval4448 (x : Key → ℝ) : Integer.Sparse.eval row4448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4448, Integer.Sparse.eval_collectBalanced, rawRowCheck4448]

def rawRow4449 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1), (key2637, -2), (key2975, -2), (key2857, -2), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1)]

theorem rawRowCheck4449 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form15 = rawRow4449 := by decide +kernel

def row4449 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck4449 : row4449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4449 := by decide +kernel

theorem rowEval4449 (x : Key → ℝ) : Integer.Sparse.eval row4449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4449, Integer.Sparse.eval_collectBalanced, rawRowCheck4449]

def rawRow4450 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2857, -2), (key2637, -2), (key2975, -2), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1)]

theorem rawRowCheck4450 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form15 = rawRow4450 := by decide +kernel

def row4450 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck4450 : row4450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4450 := by decide +kernel

theorem rowEval4450 (x : Key → ℝ) : Integer.Sparse.eval row4450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4450, Integer.Sparse.eval_collectBalanced, rawRowCheck4450]

def rawRow4451 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1), (key2857, -2), (key2975, -2), (key2637, -2), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1)]

theorem rawRowCheck4451 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form15 = rawRow4451 := by decide +kernel

def row4451 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck4451 : row4451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4451 := by decide +kernel

theorem rowEval4451 (x : Key → ℝ) : Integer.Sparse.eval row4451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4451, Integer.Sparse.eval_collectBalanced, rawRowCheck4451]

def rawRow4452 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1), (key2975, -2), (key2637, -2), (key2857, -2), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1)]

theorem rawRowCheck4452 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form15 = rawRow4452 := by decide +kernel

def row4452 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck4452 : row4452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4452 := by decide +kernel

theorem rowEval4452 (x : Key → ℝ) : Integer.Sparse.eval row4452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4452, Integer.Sparse.eval_collectBalanced, rawRowCheck4452]

def rawRow4453 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2975, -2), (key2857, -2), (key2637, -2), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

theorem rawRowCheck4453 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form15 = rawRow4453 := by decide +kernel

def row4453 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck4453 : row4453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4453 := by decide +kernel

theorem rowEval4453 (x : Key → ℝ) : Integer.Sparse.eval row4453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4453, Integer.Sparse.eval_collectBalanced, rawRowCheck4453]

def rawRow4454 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1), (key2613, -2), (key2806, -2), (key2949, -2), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1)]

theorem rawRowCheck4454 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form15 = rawRow4454 := by decide +kernel

def row4454 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck4454 : row4454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4454 := by decide +kernel

theorem rowEval4454 (x : Key → ℝ) : Integer.Sparse.eval row4454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4454, Integer.Sparse.eval_collectBalanced, rawRowCheck4454]

def rawRow4455 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1), (key2613, -2), (key2949, -2), (key2806, -2), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1)]

theorem rawRowCheck4455 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form15 = rawRow4455 := by decide +kernel

def row4455 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck4455 : row4455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4455 := by decide +kernel

theorem rowEval4455 (x : Key → ℝ) : Integer.Sparse.eval row4455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4455, Integer.Sparse.eval_collectBalanced, rawRowCheck4455]

def rawRow4456 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2806, -2), (key2613, -2), (key2949, -2), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1)]

theorem rawRowCheck4456 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form15 = rawRow4456 := by decide +kernel

def row4456 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck4456 : row4456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4456 := by decide +kernel

theorem rowEval4456 (x : Key → ℝ) : Integer.Sparse.eval row4456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4456, Integer.Sparse.eval_collectBalanced, rawRowCheck4456]

def rawRow4457 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1), (key2806, -2), (key2949, -2), (key2613, -2), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1)]

theorem rawRowCheck4457 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form15 = rawRow4457 := by decide +kernel

def row4457 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck4457 : row4457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4457 := by decide +kernel

theorem rowEval4457 (x : Key → ℝ) : Integer.Sparse.eval row4457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4457, Integer.Sparse.eval_collectBalanced, rawRowCheck4457]

def rawRow4458 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1), (key2949, -2), (key2613, -2), (key2806, -2), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1)]

theorem rawRowCheck4458 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form15 = rawRow4458 := by decide +kernel

def row4458 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck4458 : row4458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4458 := by decide +kernel

theorem rowEval4458 (x : Key → ℝ) : Integer.Sparse.eval row4458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4458, Integer.Sparse.eval_collectBalanced, rawRowCheck4458]

def rawRow4459 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2949, -2), (key2806, -2), (key2613, -2), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

theorem rawRowCheck4459 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form15 = rawRow4459 := by decide +kernel

def row4459 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck4459 : row4459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4459 := by decide +kernel

theorem rowEval4459 (x : Key → ℝ) : Integer.Sparse.eval row4459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4459, Integer.Sparse.eval_collectBalanced, rawRowCheck4459]

def rawRow4460 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1), (key2647, -2), (key2736, -2), (key2894, -2), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1)]

theorem rawRowCheck4460 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form15 = rawRow4460 := by decide +kernel

def row4460 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

theorem rowCheck4460 : row4460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4460 := by decide +kernel

theorem rowEval4460 (x : Key → ℝ) : Integer.Sparse.eval row4460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4460, Integer.Sparse.eval_collectBalanced, rawRowCheck4460]

def rawRow4461 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1), (key2647, -2), (key2894, -2), (key2736, -2), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1)]

theorem rawRowCheck4461 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form15 = rawRow4461 := by decide +kernel

def row4461 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

theorem rowCheck4461 : row4461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4461 := by decide +kernel

theorem rowEval4461 (x : Key → ℝ) : Integer.Sparse.eval row4461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4461, Integer.Sparse.eval_collectBalanced, rawRowCheck4461]

def rawRow4462 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1), (key2736, -2), (key2647, -2), (key2894, -2), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1)]

theorem rawRowCheck4462 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form15 = rawRow4462 := by decide +kernel

def row4462 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

theorem rowCheck4462 : row4462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4462 := by decide +kernel

theorem rowEval4462 (x : Key → ℝ) : Integer.Sparse.eval row4462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4462, Integer.Sparse.eval_collectBalanced, rawRowCheck4462]

def rawRow4463 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1), (key2736, -2), (key2894, -2), (key2647, -2), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1)]

theorem rawRowCheck4463 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form15 = rawRow4463 := by decide +kernel

def row4463 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

theorem rowCheck4463 : row4463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4463 := by decide +kernel

theorem rowEval4463 (x : Key → ℝ) : Integer.Sparse.eval row4463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4463, Integer.Sparse.eval_collectBalanced, rawRowCheck4463]

def rawRow4464 : Integer.Sparse Key := [(key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1), (key2894, -2), (key2647, -2), (key2736, -2), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1)]

theorem rawRowCheck4464 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form15 = rawRow4464 := by decide +kernel

def row4464 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

theorem rowCheck4464 : row4464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4464 := by decide +kernel

theorem rowEval4464 (x : Key → ℝ) : Integer.Sparse.eval row4464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4464, Integer.Sparse.eval_collectBalanced, rawRowCheck4464]

def rawRow4465 : Integer.Sparse Key := [(key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1), (key2894, -2), (key2736, -2), (key2647, -2), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1)]

theorem rawRowCheck4465 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form15 = rawRow4465 := by decide +kernel

def row4465 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

theorem rowCheck4465 : row4465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4465 := by decide +kernel

theorem rowEval4465 (x : Key → ℝ) : Integer.Sparse.eval row4465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4465, Integer.Sparse.eval_collectBalanced, rawRowCheck4465]

def rawRow4466 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1), (key2625, -2), (key2699, -2), (key2852, -2), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1)]

theorem rawRowCheck4466 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form15 = rawRow4466 := by decide +kernel

def row4466 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck4466 : row4466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4466 := by decide +kernel

theorem rowEval4466 (x : Key → ℝ) : Integer.Sparse.eval row4466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4466, Integer.Sparse.eval_collectBalanced, rawRowCheck4466]

def rawRow4467 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1), (key2625, -2), (key2852, -2), (key2699, -2), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1)]

theorem rawRowCheck4467 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form15 = rawRow4467 := by decide +kernel

def row4467 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck4467 : row4467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4467 := by decide +kernel

theorem rowEval4467 (x : Key → ℝ) : Integer.Sparse.eval row4467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4467, Integer.Sparse.eval_collectBalanced, rawRowCheck4467]

def rawRow4468 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1), (key2699, -2), (key2625, -2), (key2852, -2), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1)]

theorem rawRowCheck4468 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form15 = rawRow4468 := by decide +kernel

def row4468 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck4468 : row4468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4468 := by decide +kernel

theorem rowEval4468 (x : Key → ℝ) : Integer.Sparse.eval row4468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4468, Integer.Sparse.eval_collectBalanced, rawRowCheck4468]

def rawRow4469 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1), (key2699, -2), (key2852, -2), (key2625, -2), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1)]

theorem rawRowCheck4469 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form15 = rawRow4469 := by decide +kernel

def row4469 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck4469 : row4469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4469 := by decide +kernel

theorem rowEval4469 (x : Key → ℝ) : Integer.Sparse.eval row4469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4469, Integer.Sparse.eval_collectBalanced, rawRowCheck4469]

def rawRow4470 : Integer.Sparse Key := [(key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1), (key2852, -2), (key2625, -2), (key2699, -2), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1)]

theorem rawRowCheck4470 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form15 = rawRow4470 := by decide +kernel

def row4470 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck4470 : row4470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4470 := by decide +kernel

theorem rowEval4470 (x : Key → ℝ) : Integer.Sparse.eval row4470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4470, Integer.Sparse.eval_collectBalanced, rawRowCheck4470]

def rawRow4471 : Integer.Sparse Key := [(key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1), (key2852, -2), (key2699, -2), (key2625, -2), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1)]

theorem rawRowCheck4471 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form15 = rawRow4471 := by decide +kernel

def row4471 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

theorem rowCheck4471 : row4471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4471 := by decide +kernel

theorem rowEval4471 (x : Key → ℝ) : Integer.Sparse.eval row4471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4471, Integer.Sparse.eval_collectBalanced, rawRowCheck4471]

def rawRow4472 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2666, 2), (key2701, 2), (key2734, 2), (key2801, 2), (key2804, 2), (key2825, 2), (key2611, -2), (key2804, -2), (key2825, -2), (key2734, -2), (key2892, -2), (key2895, -2), (key2645, 2), (key2892, 2), (key2902, 2)]

theorem rawRowCheck4472 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form16 = rawRow4472 := by decide +kernel

def row4472 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

theorem rowCheck4472 : row4472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4472 := by decide +kernel

theorem rowEval4472 (x : Key → ℝ) : Integer.Sparse.eval row4472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4472, Integer.Sparse.eval_collectBalanced, rawRowCheck4472]

def rawRow4473 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2666, 2), (key2734, 2), (key2701, 2), (key2804, 2), (key2801, 2), (key2825, 2), (key2611, -2), (key2825, -2), (key2804, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, 2), (key2902, 2), (key2892, 2)]

theorem rawRowCheck4473 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form16 = rawRow4473 := by decide +kernel

def row4473 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

theorem rowCheck4473 : row4473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4473 := by decide +kernel

theorem rowEval4473 (x : Key → ℝ) : Integer.Sparse.eval row4473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4473, Integer.Sparse.eval_collectBalanced, rawRowCheck4473]

def rawRow4474 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2701, 2), (key2666, 2), (key2734, 2), (key2801, 2), (key2825, 2), (key2804, 2), (key2804, -2), (key2611, -2), (key2825, -2), (key2892, -2), (key2734, -2), (key2895, -2), (key2892, 2), (key2645, 2), (key2902, 2)]

theorem rawRowCheck4474 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form16 = rawRow4474 := by decide +kernel

def row4474 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

theorem rowCheck4474 : row4474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4474 := by decide +kernel

theorem rowEval4474 (x : Key → ℝ) : Integer.Sparse.eval row4474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4474, Integer.Sparse.eval_collectBalanced, rawRowCheck4474]

def rawRow4475 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2701, 2), (key2734, 2), (key2666, 2), (key2825, 2), (key2801, 2), (key2804, 2), (key2804, -2), (key2825, -2), (key2611, -2), (key2892, -2), (key2895, -2), (key2734, -2), (key2892, 2), (key2902, 2), (key2645, 2)]

theorem rawRowCheck4475 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form16 = rawRow4475 := by decide +kernel

def row4475 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

theorem rowCheck4475 : row4475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4475 := by decide +kernel

theorem rowEval4475 (x : Key → ℝ) : Integer.Sparse.eval row4475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4475, Integer.Sparse.eval_collectBalanced, rawRowCheck4475]

def rawRow4476 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2734, 2), (key2666, 2), (key2701, 2), (key2804, 2), (key2825, 2), (key2801, 2), (key2825, -2), (key2611, -2), (key2804, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, 2), (key2645, 2), (key2892, 2)]

theorem rawRowCheck4476 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form16 = rawRow4476 := by decide +kernel

def row4476 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

theorem rowCheck4476 : row4476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4476 := by decide +kernel

theorem rowEval4476 (x : Key → ℝ) : Integer.Sparse.eval row4476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4476, Integer.Sparse.eval_collectBalanced, rawRowCheck4476]

def rawRow4477 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2734, 2), (key2701, 2), (key2666, 2), (key2825, 2), (key2804, 2), (key2801, 2), (key2825, -2), (key2804, -2), (key2611, -2), (key2895, -2), (key2892, -2), (key2734, -2), (key2902, 2), (key2892, 2), (key2645, 2)]

theorem rawRowCheck4477 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form16 = rawRow4477 := by decide +kernel

def row4477 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

theorem rowCheck4477 : row4477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4477 := by decide +kernel

theorem rowEval4477 (x : Key → ℝ) : Integer.Sparse.eval row4477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4477, Integer.Sparse.eval_collectBalanced, rawRowCheck4477]

def rawRow4478 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2790, 2), (key2856, 2), (key2895, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2636, -2), (key2856, -2), (key2974, -2), (key2666, -2), (key2781, -2), (key2790, -2), (key2611, 2), (key2804, 2), (key2825, 2)]

theorem rawRowCheck4478 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form16 = rawRow4478 := by decide +kernel

def row4478 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

theorem rowCheck4478 : row4478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4478 := by decide +kernel

theorem rowEval4478 (x : Key → ℝ) : Integer.Sparse.eval row4478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4478, Integer.Sparse.eval_collectBalanced, rawRowCheck4478]

def rawRow4479 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2790, 2), (key2895, 2), (key2856, 2), (key2701, 2), (key2698, 2), (key2722, 2), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, -2), (key2790, -2), (key2781, -2), (key2611, 2), (key2825, 2), (key2804, 2)]

theorem rawRowCheck4479 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form16 = rawRow4479 := by decide +kernel

def row4479 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

theorem rowCheck4479 : row4479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4479 := by decide +kernel

theorem rowEval4479 (x : Key → ℝ) : Integer.Sparse.eval row4479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4479, Integer.Sparse.eval_collectBalanced, rawRowCheck4479]

end MUB6.Certificate.GramRows

end OAI
