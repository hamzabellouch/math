import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
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

def rawRow3584 : Integer.Sparse Key := [(key2619, -2), (key2642, -2), (key2642, -2), (key2616, 1), (key2616, 1), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2951, 2), (key2977, 2), (key2977, 2), (key2706, -1), (key2706, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2961, -1), (key2961, -1), (key2984, -1), (key2984, -1), (key2992, -1), (key2992, -1), (key2729, 1), (key2729, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

theorem rawRowCheck3584 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form9 = rawRow3584 := by decide +kernel

def row3584 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

theorem rowCheck3584 : row3584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3584 := by decide +kernel

theorem rowEval3584 (x : Key → ℝ) : Integer.Sparse.eval row3584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3584, Integer.Sparse.eval_collectBalanced, rawRowCheck3584]

def rawRow3585 : Integer.Sparse Key := [(key2642, -2), (key2619, -2), (key2642, -2), (key2632, 1), (key2640, 1), (key2616, 1), (key2640, 1), (key2616, 1), (key2632, 1), (key2977, 2), (key2951, 2), (key2977, 2), (key2809, -1), (key2860, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2984, -1), (key2992, -1), (key2961, -1), (key2992, -1), (key2961, -1), (key2984, -1), (key2832, 1), (key2883, 1), (key2729, 1), (key2883, 1), (key2729, 1), (key2832, 1)]

theorem rawRowCheck3585 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form9 = rawRow3585 := by decide +kernel

def row3585 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

theorem rowCheck3585 : row3585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3585 := by decide +kernel

theorem rowEval3585 (x : Key → ℝ) : Integer.Sparse.eval row3585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3585, Integer.Sparse.eval_collectBalanced, rawRowCheck3585]

def rawRow3586 : Integer.Sparse Key := [(key2642, -2), (key2642, -2), (key2619, -2), (key2640, 1), (key2632, 1), (key2640, 1), (key2616, 1), (key2632, 1), (key2616, 1), (key2977, 2), (key2977, 2), (key2951, 2), (key2860, -1), (key2809, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2706, -1), (key2992, -1), (key2984, -1), (key2992, -1), (key2961, -1), (key2984, -1), (key2961, -1), (key2883, 1), (key2832, 1), (key2883, 1), (key2729, 1), (key2832, 1), (key2729, 1)]

theorem rawRowCheck3586 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form9 = rawRow3586 := by decide +kernel

def row3586 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

theorem rowCheck3586 : row3586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3586 := by decide +kernel

theorem rowEval3586 (x : Key → ℝ) : Integer.Sparse.eval row3586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3586, Integer.Sparse.eval_collectBalanced, rawRowCheck3586]

def rawRow3587 : Integer.Sparse Key := [(key2674, -2), (key2729, -2), (key2729, -2), (key2671, 1), (key2671, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2939, 2), (key2984, 2), (key2984, 2), (key2632, -1), (key2632, -1), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2944, -1), (key2944, -1), (key2977, -1), (key2977, -1), (key2992, -1), (key2992, -1), (key2642, 1), (key2642, 1), (key2796, 1), (key2796, 1), (key2883, 1), (key2883, 1)]

theorem rawRowCheck3587 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3587 := by decide +kernel

def row3587 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

theorem rowCheck3587 : row3587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3587 := by decide +kernel

theorem rowEval3587 (x : Key → ℝ) : Integer.Sparse.eval row3587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3587, Integer.Sparse.eval_collectBalanced, rawRowCheck3587]

def rawRow3588 : Integer.Sparse Key := [(key2729, -2), (key2674, -2), (key2729, -2), (key2706, 1), (key2726, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2984, 2), (key2939, 2), (key2984, 2), (key2786, -1), (key2870, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2977, -1), (key2992, -1), (key2944, -1), (key2992, -1), (key2944, -1), (key2977, -1), (key2796, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2796, 1)]

theorem rawRowCheck3588 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3588 := by decide +kernel

def row3588 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

theorem rowCheck3588 : row3588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3588 := by decide +kernel

theorem rowEval3588 (x : Key → ℝ) : Integer.Sparse.eval row3588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3588, Integer.Sparse.eval_collectBalanced, rawRowCheck3588]

def rawRow3589 : Integer.Sparse Key := [(key2729, -2), (key2729, -2), (key2674, -2), (key2726, 1), (key2706, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2671, 1), (key2984, 2), (key2984, 2), (key2939, 2), (key2870, -1), (key2786, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2632, -1), (key2992, -1), (key2977, -1), (key2992, -1), (key2944, -1), (key2977, -1), (key2944, -1), (key2883, 1), (key2796, 1), (key2883, 1), (key2642, 1), (key2796, 1), (key2642, 1)]

theorem rawRowCheck3589 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3589 := by decide +kernel

def row3589 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

theorem rowCheck3589 : row3589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3589 := by decide +kernel

theorem rowEval3589 (x : Key → ℝ) : Integer.Sparse.eval row3589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3589, Integer.Sparse.eval_collectBalanced, rawRowCheck3589]

def rawRow3590 : Integer.Sparse Key := [(key2951, -2), (key2977, -2), (key2977, -2), (key2961, 1), (key2961, 1), (key2984, 1), (key2984, 1), (key2992, 1), (key2992, 1), (key2619, 2), (key2642, 2), (key2642, 2), (key2729, -1), (key2729, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2616, -1), (key2616, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2706, 1), (key2706, 1), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1)]

theorem rawRowCheck3590 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form9 = rawRow3590 := by decide +kernel

def row3590 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

theorem rowCheck3590 : row3590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3590 := by decide +kernel

theorem rowEval3590 (x : Key → ℝ) : Integer.Sparse.eval row3590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3590, Integer.Sparse.eval_collectBalanced, rawRowCheck3590]

def rawRow3591 : Integer.Sparse Key := [(key2977, -2), (key2951, -2), (key2977, -2), (key2984, 1), (key2992, 1), (key2961, 1), (key2992, 1), (key2961, 1), (key2984, 1), (key2642, 2), (key2619, 2), (key2642, 2), (key2832, -1), (key2883, -1), (key2729, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2632, -1), (key2640, -1), (key2616, -1), (key2640, -1), (key2616, -1), (key2632, -1), (key2809, 1), (key2860, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2809, 1)]

theorem rawRowCheck3591 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form9 = rawRow3591 := by decide +kernel

def row3591 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

theorem rowCheck3591 : row3591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3591 := by decide +kernel

theorem rowEval3591 (x : Key → ℝ) : Integer.Sparse.eval row3591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3591, Integer.Sparse.eval_collectBalanced, rawRowCheck3591]

def rawRow3592 : Integer.Sparse Key := [(key2977, -2), (key2977, -2), (key2951, -2), (key2992, 1), (key2984, 1), (key2992, 1), (key2961, 1), (key2984, 1), (key2961, 1), (key2642, 2), (key2642, 2), (key2619, 2), (key2883, -1), (key2832, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2729, -1), (key2640, -1), (key2632, -1), (key2640, -1), (key2616, -1), (key2632, -1), (key2616, -1), (key2860, 1), (key2809, 1), (key2860, 1), (key2706, 1), (key2809, 1), (key2706, 1)]

theorem rawRowCheck3592 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form9 = rawRow3592 := by decide +kernel

def row3592 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

theorem rowCheck3592 : row3592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3592 := by decide +kernel

theorem rowEval3592 (x : Key → ℝ) : Integer.Sparse.eval row3592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3592, Integer.Sparse.eval_collectBalanced, rawRowCheck3592]

def rawRow3593 : Integer.Sparse Key := [(key2939, -2), (key2984, -2), (key2984, -2), (key2944, 1), (key2944, 1), (key2977, 1), (key2977, 1), (key2992, 1), (key2992, 1), (key2674, 2), (key2729, 2), (key2729, 2), (key2642, -1), (key2642, -1), (key2796, -1), (key2796, -1), (key2883, -1), (key2883, -1), (key2671, -1), (key2671, -1), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

theorem rawRowCheck3593 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3593 := by decide +kernel

def row3593 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

theorem rowCheck3593 : row3593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3593 := by decide +kernel

theorem rowEval3593 (x : Key → ℝ) : Integer.Sparse.eval row3593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3593, Integer.Sparse.eval_collectBalanced, rawRowCheck3593]

def rawRow3594 : Integer.Sparse Key := [(key2984, -2), (key2939, -2), (key2984, -2), (key2977, 1), (key2992, 1), (key2944, 1), (key2992, 1), (key2944, 1), (key2977, 1), (key2729, 2), (key2674, 2), (key2729, 2), (key2796, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

theorem rawRowCheck3594 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3594 := by decide +kernel

def row3594 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

theorem rowCheck3594 : row3594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3594 := by decide +kernel

theorem rowEval3594 (x : Key → ℝ) : Integer.Sparse.eval row3594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3594, Integer.Sparse.eval_collectBalanced, rawRowCheck3594]

def rawRow3595 : Integer.Sparse Key := [(key2984, -2), (key2984, -2), (key2939, -2), (key2992, 1), (key2977, 1), (key2992, 1), (key2944, 1), (key2977, 1), (key2944, 1), (key2729, 2), (key2729, 2), (key2674, 2), (key2883, -1), (key2796, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2642, -1), (key2726, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2671, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

theorem rawRowCheck3595 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3595 := by decide +kernel

def row3595 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

theorem rowCheck3595 : row3595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3595 := by decide +kernel

theorem rowEval3595 (x : Key → ℝ) : Integer.Sparse.eval row3595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3595, Integer.Sparse.eval_collectBalanced, rawRowCheck3595]

def rawRow3596 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2387, -2), (key2371, 6), (key2536, 2), (key2536, 2), (key2541, 2), (key2399, -2), (key2465, -2), (key2465, -2), (key2552, -6), (key2434, 2), (key2500, 2), (key2500, 2)]

theorem rawRowCheck3596 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form10 = rawRow3596 := by decide +kernel

def row3596 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

theorem rowCheck3596 : row3596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3596 := by decide +kernel

theorem rowEval3596 (x : Key → ℝ) : Integer.Sparse.eval row3596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3596, Integer.Sparse.eval_collectBalanced, rawRowCheck3596]

def rawRow3597 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2375, -2), (key2371, 6), (key2536, 2), (key2541, 2), (key2536, 2), (key2465, -2), (key2399, -2), (key2465, -2), (key2552, -6), (key2500, 2), (key2434, 2), (key2500, 2)]

theorem rawRowCheck3597 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form10 = rawRow3597 := by decide +kernel

def row3597 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

theorem rowCheck3597 : row3597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3597 := by decide +kernel

theorem rowEval3597 (x : Key → ℝ) : Integer.Sparse.eval row3597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3597, Integer.Sparse.eval_collectBalanced, rawRowCheck3597]

def rawRow3598 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2375, -2), (key2371, 6), (key2541, 2), (key2536, 2), (key2536, 2), (key2465, -2), (key2465, -2), (key2399, -2), (key2552, -6), (key2500, 2), (key2500, 2), (key2434, 2)]

theorem rawRowCheck3598 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form10 = rawRow3598 := by decide +kernel

def row3598 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

theorem rowCheck3598 : row3598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3598 := by decide +kernel

theorem rowEval3598 (x : Key → ℝ) : Integer.Sparse.eval row3598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3598, Integer.Sparse.eval_collectBalanced, rawRowCheck3598]

def rawRow3599 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2434, -2), (key2399, 6), (key2536, 2), (key2536, 2), (key2552, 2), (key2371, -2), (key2465, -2), (key2465, -2), (key2541, -6), (key2387, 2), (key2477, 2), (key2477, 2)]

theorem rawRowCheck3599 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow3599 := by decide +kernel

def row3599 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

theorem rowCheck3599 : row3599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3599 := by decide +kernel

theorem rowEval3599 (x : Key → ℝ) : Integer.Sparse.eval row3599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3599, Integer.Sparse.eval_collectBalanced, rawRowCheck3599]

def rawRow3600 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2403, -2), (key2399, 6), (key2536, 2), (key2552, 2), (key2536, 2), (key2465, -2), (key2371, -2), (key2465, -2), (key2541, -6), (key2477, 2), (key2387, 2), (key2477, 2)]

theorem rawRowCheck3600 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow3600 := by decide +kernel

def row3600 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

theorem rowCheck3600 : row3600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3600 := by decide +kernel

theorem rowEval3600 (x : Key → ℝ) : Integer.Sparse.eval row3600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3600, Integer.Sparse.eval_collectBalanced, rawRowCheck3600]

def rawRow3601 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2403, -2), (key2399, 6), (key2552, 2), (key2536, 2), (key2536, 2), (key2465, -2), (key2465, -2), (key2371, -2), (key2541, -6), (key2477, 2), (key2477, 2), (key2387, 2)]

theorem rawRowCheck3601 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow3601 := by decide +kernel

def row3601 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

theorem rowCheck3601 : row3601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3601 := by decide +kernel

theorem rowEval3601 (x : Key → ℝ) : Integer.Sparse.eval row3601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3601, Integer.Sparse.eval_collectBalanced, rawRowCheck3601]

def rawRow3602 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2541, -2), (key2552, 6), (key2375, 2), (key2375, 2), (key2387, 2), (key2434, -2), (key2500, -2), (key2500, -2), (key2371, -6), (key2399, 2), (key2465, 2), (key2465, 2)]

theorem rawRowCheck3602 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form10 = rawRow3602 := by decide +kernel

def row3602 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck3602 : row3602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3602 := by decide +kernel

theorem rowEval3602 (x : Key → ℝ) : Integer.Sparse.eval row3602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3602, Integer.Sparse.eval_collectBalanced, rawRowCheck3602]

def rawRow3603 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2536, -2), (key2552, 6), (key2375, 2), (key2387, 2), (key2375, 2), (key2500, -2), (key2434, -2), (key2500, -2), (key2371, -6), (key2465, 2), (key2399, 2), (key2465, 2)]

theorem rawRowCheck3603 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form10 = rawRow3603 := by decide +kernel

def row3603 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck3603 : row3603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3603 := by decide +kernel

theorem rowEval3603 (x : Key → ℝ) : Integer.Sparse.eval row3603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3603, Integer.Sparse.eval_collectBalanced, rawRowCheck3603]

def rawRow3604 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2536, -2), (key2552, 6), (key2387, 2), (key2375, 2), (key2375, 2), (key2500, -2), (key2500, -2), (key2434, -2), (key2371, -6), (key2465, 2), (key2465, 2), (key2399, 2)]

theorem rawRowCheck3604 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form10 = rawRow3604 := by decide +kernel

def row3604 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

theorem rowCheck3604 : row3604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3604 := by decide +kernel

theorem rowEval3604 (x : Key → ℝ) : Integer.Sparse.eval row3604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3604, Integer.Sparse.eval_collectBalanced, rawRowCheck3604]

def rawRow3605 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2552, -2), (key2541, 6), (key2403, 2), (key2403, 2), (key2434, 2), (key2387, -2), (key2477, -2), (key2477, -2), (key2399, -6), (key2371, 2), (key2465, 2), (key2465, 2)]

theorem rawRowCheck3605 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow3605 := by decide +kernel

def row3605 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck3605 : row3605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3605 := by decide +kernel

theorem rowEval3605 (x : Key → ℝ) : Integer.Sparse.eval row3605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3605, Integer.Sparse.eval_collectBalanced, rawRowCheck3605]

def rawRow3606 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2536, -2), (key2541, 6), (key2403, 2), (key2434, 2), (key2403, 2), (key2477, -2), (key2387, -2), (key2477, -2), (key2399, -6), (key2465, 2), (key2371, 2), (key2465, 2)]

theorem rawRowCheck3606 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow3606 := by decide +kernel

def row3606 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck3606 : row3606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3606 := by decide +kernel

theorem rowEval3606 (x : Key → ℝ) : Integer.Sparse.eval row3606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3606, Integer.Sparse.eval_collectBalanced, rawRowCheck3606]

def rawRow3607 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2536, -2), (key2541, 6), (key2434, 2), (key2403, 2), (key2403, 2), (key2477, -2), (key2477, -2), (key2387, -2), (key2399, -6), (key2465, 2), (key2465, 2), (key2371, 2)]

theorem rawRowCheck3607 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow3607 := by decide +kernel

def row3607 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

theorem rowCheck3607 : row3607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3607 := by decide +kernel

theorem rowEval3607 (x : Key → ℝ) : Integer.Sparse.eval row3607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3607, Integer.Sparse.eval_collectBalanced, rawRowCheck3607]

def rawRow3608 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2386, -2), (key2370, 6), (key2874, 2), (key2874, 2), (key2908, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key2987, -6), (key2928, 2), (key2965, 2), (key2965, 2)]

theorem rawRowCheck3608 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form11 = rawRow3608 := by decide +kernel

def row3608 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

theorem rowCheck3608 : row3608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3608 := by decide +kernel

theorem rowEval3608 (x : Key → ℝ) : Integer.Sparse.eval row3608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3608, Integer.Sparse.eval_collectBalanced, rawRowCheck3608]

def rawRow3609 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2373, -2), (key2370, 6), (key2874, 2), (key2908, 2), (key2874, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key2987, -6), (key2965, 2), (key2928, 2), (key2965, 2)]

theorem rawRowCheck3609 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form11 = rawRow3609 := by decide +kernel

def row3609 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

theorem rowCheck3609 : row3609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3609 := by decide +kernel

theorem rowEval3609 (x : Key → ℝ) : Integer.Sparse.eval row3609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3609, Integer.Sparse.eval_collectBalanced, rawRowCheck3609]

def rawRow3610 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2373, -2), (key2370, 6), (key2908, 2), (key2874, 2), (key2874, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key2987, -6), (key2965, 2), (key2965, 2), (key2928, 2)]

theorem rawRowCheck3610 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form11 = rawRow3610 := by decide +kernel

def row3610 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

theorem rowCheck3610 : row3610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3610 := by decide +kernel

theorem rowEval3610 (x : Key → ℝ) : Integer.Sparse.eval row3610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3610, Integer.Sparse.eval_collectBalanced, rawRowCheck3610]

def rawRow3611 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2433, -2), (key2398, 6), (key2874, 2), (key2874, 2), (key2987, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2908, -6), (key2597, 2), (key2886, 2), (key2886, 2)]

theorem rawRowCheck3611 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow3611 := by decide +kernel

def row3611 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

theorem rowCheck3611 : row3611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3611 := by decide +kernel

theorem rowEval3611 (x : Key → ℝ) : Integer.Sparse.eval row3611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3611, Integer.Sparse.eval_collectBalanced, rawRowCheck3611]

def rawRow3612 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2401, -2), (key2398, 6), (key2874, 2), (key2987, 2), (key2874, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2908, -6), (key2886, 2), (key2597, 2), (key2886, 2)]

theorem rawRowCheck3612 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow3612 := by decide +kernel

def row3612 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

theorem rowCheck3612 : row3612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3612 := by decide +kernel

theorem rowEval3612 (x : Key → ℝ) : Integer.Sparse.eval row3612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3612, Integer.Sparse.eval_collectBalanced, rawRowCheck3612]

def rawRow3613 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2401, -2), (key2398, 6), (key2987, 2), (key2874, 2), (key2874, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2908, -6), (key2886, 2), (key2886, 2), (key2597, 2)]

theorem rawRowCheck3613 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow3613 := by decide +kernel

def row3613 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

theorem rowCheck3613 : row3613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3613 := by decide +kernel

theorem rowEval3613 (x : Key → ℝ) : Integer.Sparse.eval row3613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3613, Integer.Sparse.eval_collectBalanced, rawRowCheck3613]

def rawRow3614 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2540, -2), (key2551, 6), (key2373, 2), (key2373, 2), (key2386, 2), (key2433, -2), (key2499, -2), (key2499, -2), (key2370, -6), (key2762, 2), (key2839, 2), (key2839, 2)]

theorem rawRowCheck3614 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form11 = rawRow3614 := by decide +kernel

def row3614 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

theorem rowCheck3614 : row3614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3614 := by decide +kernel

theorem rowEval3614 (x : Key → ℝ) : Integer.Sparse.eval row3614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3614, Integer.Sparse.eval_collectBalanced, rawRowCheck3614]

def rawRow3615 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2534, -2), (key2551, 6), (key2373, 2), (key2386, 2), (key2373, 2), (key2499, -2), (key2433, -2), (key2499, -2), (key2370, -6), (key2839, 2), (key2762, 2), (key2839, 2)]

theorem rawRowCheck3615 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form11 = rawRow3615 := by decide +kernel

def row3615 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

theorem rowCheck3615 : row3615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3615 := by decide +kernel

theorem rowEval3615 (x : Key → ℝ) : Integer.Sparse.eval row3615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3615, Integer.Sparse.eval_collectBalanced, rawRowCheck3615]

def rawRow3616 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2534, -2), (key2551, 6), (key2386, 2), (key2373, 2), (key2373, 2), (key2499, -2), (key2499, -2), (key2433, -2), (key2370, -6), (key2839, 2), (key2839, 2), (key2762, 2)]

theorem rawRowCheck3616 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form11 = rawRow3616 := by decide +kernel

def row3616 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

theorem rowCheck3616 : row3616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3616 := by decide +kernel

theorem rowEval3616 (x : Key → ℝ) : Integer.Sparse.eval row3616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck3616, Integer.Sparse.eval_collectBalanced, rawRowCheck3616]

def rawRow3617 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2551, -2), (key2540, 6), (key2401, 2), (key2401, 2), (key2433, 2), (key2386, -2), (key2476, -2), (key2476, -2), (key2398, -6), (key2583, 2), (key2839, 2), (key2839, 2)]

theorem rawRowCheck3617 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form11 = rawRow3617 := by decide +kernel

def row3617 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

theorem rowCheck3617 : row3617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3617 := by decide +kernel

theorem rowEval3617 (x : Key → ℝ) : Integer.Sparse.eval row3617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3617, Integer.Sparse.eval_collectBalanced, rawRowCheck3617]

def rawRow3618 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2534, -2), (key2540, 6), (key2401, 2), (key2433, 2), (key2401, 2), (key2476, -2), (key2386, -2), (key2476, -2), (key2398, -6), (key2839, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck3618 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form11 = rawRow3618 := by decide +kernel

def row3618 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

theorem rowCheck3618 : row3618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3618 := by decide +kernel

theorem rowEval3618 (x : Key → ℝ) : Integer.Sparse.eval row3618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3618, Integer.Sparse.eval_collectBalanced, rawRowCheck3618]

def rawRow3619 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2534, -2), (key2540, 6), (key2433, 2), (key2401, 2), (key2401, 2), (key2476, -2), (key2476, -2), (key2386, -2), (key2398, -6), (key2839, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck3619 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form11 = rawRow3619 := by decide +kernel

def row3619 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

theorem rowCheck3619 : row3619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3619 := by decide +kernel

theorem rowEval3619 (x : Key → ℝ) : Integer.Sparse.eval row3619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3619, Integer.Sparse.eval_collectBalanced, rawRowCheck3619]

def rawRow3620 : Integer.Sparse Key := [(key2645, -2), (key2645, -2), (key2651, -2), (key2611, 1), (key2611, 1), (key2627, 1), (key2627, 1), (key2636, 1), (key2636, 1), (key2722, 2), (key2722, 2), (key2745, 2), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2734, -1), (key2734, -1), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2902, -1), (key2902, -1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2895, 1), (key2895, 1)]

theorem rawRowCheck3620 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form12 = rawRow3620 := by decide +kernel

def row3620 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

theorem rowCheck3620 : row3620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3620 := by decide +kernel

theorem rowEval3620 (x : Key → ℝ) : Integer.Sparse.eval row3620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3620, Integer.Sparse.eval_collectBalanced, rawRowCheck3620]

def rawRow3621 : Integer.Sparse Key := [(key2645, -2), (key2651, -2), (key2645, -2), (key2627, 1), (key2636, 1), (key2611, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2722, 2), (key2745, 2), (key2722, 2), (key2701, -1), (key2734, -1), (key2666, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2856, 1), (key2895, 1), (key2790, 1), (key2895, 1), (key2790, 1), (key2856, 1)]

theorem rawRowCheck3621 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form12 = rawRow3621 := by decide +kernel

def row3621 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

theorem rowCheck3621 : row3621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3621 := by decide +kernel

theorem rowEval3621 (x : Key → ℝ) : Integer.Sparse.eval row3621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3621, Integer.Sparse.eval_collectBalanced, rawRowCheck3621]

def rawRow3622 : Integer.Sparse Key := [(key2651, -2), (key2645, -2), (key2645, -2), (key2636, 1), (key2627, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2611, 1), (key2745, 2), (key2722, 2), (key2722, 2), (key2734, -1), (key2701, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2902, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2825, -1), (key2895, 1), (key2856, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2790, 1)]

theorem rawRowCheck3622 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form12 = rawRow3622 := by decide +kernel

def row3622 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

theorem rowCheck3622 : row3622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3622 := by decide +kernel

theorem rowEval3622 (x : Key → ℝ) : Integer.Sparse.eval row3622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3622, Integer.Sparse.eval_collectBalanced, rawRowCheck3622]

def rawRow3623 : Integer.Sparse Key := [(key2734, -2), (key2734, -2), (key2745, -2), (key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2722, 1), (key2722, 1), (key2947, 2), (key2947, 2), (key2958, 2), (key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2722, -1), (key2722, -1), (key2866, -1), (key2866, -1), (key2981, -1), (key2981, -1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1)]

theorem rawRowCheck3623 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow3623 := by decide +kernel

def row3623 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck3623 : row3623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3623 := by decide +kernel

theorem rowEval3623 (x : Key → ℝ) : Integer.Sparse.eval row3623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3623, Integer.Sparse.eval_collectBalanced, rawRowCheck3623]

def rawRow3624 : Integer.Sparse Key := [(key2734, -2), (key2745, -2), (key2734, -2), (key2701, 1), (key2722, 1), (key2666, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2947, 2), (key2958, 2), (key2947, 2), (key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1)]

theorem rawRowCheck3624 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow3624 := by decide +kernel

def row3624 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck3624 : row3624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3624 := by decide +kernel

theorem rowEval3624 (x : Key → ℝ) : Integer.Sparse.eval row3624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3624, Integer.Sparse.eval_collectBalanced, rawRowCheck3624]

def rawRow3625 : Integer.Sparse Key := [(key2745, -2), (key2734, -2), (key2734, -2), (key2722, 1), (key2701, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2958, 2), (key2947, 2), (key2947, 2), (key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2981, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1)]

theorem rawRowCheck3625 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow3625 := by decide +kernel

def row3625 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck3625 : row3625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3625 := by decide +kernel

theorem rowEval3625 (x : Key → ℝ) : Integer.Sparse.eval row3625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3625, Integer.Sparse.eval_collectBalanced, rawRowCheck3625]

def rawRow3626 : Integer.Sparse Key := [(key2935, -2), (key2935, -2), (key2941, -2), (key2947, 1), (key2947, 1), (key2971, 1), (key2971, 1), (key2974, 1), (key2974, 1), (key2645, 2), (key2645, 2), (key2651, 2), (key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1), (key2895, -1), (key2895, -1), (key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1)]

theorem rawRowCheck3626 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form12 = rawRow3626 := by decide +kernel

def row3626 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

theorem rowCheck3626 : row3626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3626 := by decide +kernel

theorem rowEval3626 (x : Key → ℝ) : Integer.Sparse.eval row3626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3626, Integer.Sparse.eval_collectBalanced, rawRowCheck3626]

def rawRow3627 : Integer.Sparse Key := [(key2935, -2), (key2941, -2), (key2935, -2), (key2971, 1), (key2974, 1), (key2947, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2645, 2), (key2651, 2), (key2645, 2), (key2892, -1), (key2895, -1), (key2734, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1)]

theorem rawRowCheck3627 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form12 = rawRow3627 := by decide +kernel

def row3627 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

theorem rowCheck3627 : row3627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3627 := by decide +kernel

theorem rowEval3627 (x : Key → ℝ) : Integer.Sparse.eval row3627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3627, Integer.Sparse.eval_collectBalanced, rawRowCheck3627]

def rawRow3628 : Integer.Sparse Key := [(key2941, -2), (key2935, -2), (key2935, -2), (key2974, 1), (key2971, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2947, 1), (key2651, 2), (key2645, 2), (key2645, 2), (key2895, -1), (key2892, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2734, -1), (key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1)]

theorem rawRowCheck3628 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form12 = rawRow3628 := by decide +kernel

def row3628 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

theorem rowCheck3628 : row3628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3628 := by decide +kernel

theorem rowEval3628 (x : Key → ℝ) : Integer.Sparse.eval row3628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck3628, Integer.Sparse.eval_collectBalanced, rawRowCheck3628]

def rawRow3629 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2935, 1), (key2935, 1), (key2971, 1), (key2971, 1), (key2981, 1), (key2981, 1), (key2734, 2), (key2734, 2), (key2745, 2), (key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1)]

theorem rawRowCheck3629 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form12 = rawRow3629 := by decide +kernel

def row3629 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

theorem rowCheck3629 : row3629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3629 := by decide +kernel

theorem rowEval3629 (x : Key → ℝ) : Integer.Sparse.eval row3629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3629, Integer.Sparse.eval_collectBalanced, rawRowCheck3629]

def rawRow3630 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2971, 1), (key2981, 1), (key2935, 1), (key2981, 1), (key2935, 1), (key2971, 1), (key2734, 2), (key2745, 2), (key2734, 2), (key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1)]

theorem rawRowCheck3630 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form12 = rawRow3630 := by decide +kernel

def row3630 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

theorem rowCheck3630 : row3630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3630 := by decide +kernel

theorem rowEval3630 (x : Key → ℝ) : Integer.Sparse.eval row3630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck3630, Integer.Sparse.eval_collectBalanced, rawRowCheck3630]

def rawRow3631 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2981, 1), (key2971, 1), (key2981, 1), (key2935, 1), (key2971, 1), (key2935, 1), (key2745, 2), (key2734, 2), (key2734, 2), (key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1)]

theorem rawRowCheck3631 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form12 = rawRow3631 := by decide +kernel

def row3631 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

theorem rowCheck3631 : row3631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3631 := by decide +kernel

theorem rowEval3631 (x : Key → ℝ) : Integer.Sparse.eval row3631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck3631, Integer.Sparse.eval_collectBalanced, rawRowCheck3631]

def rawRow3632 : Integer.Sparse Key := [(key2091, -2), (key2092, -2), (key2092, -2), (key2095, 6), (key2193, 2), (key2194, 2), (key2194, 2), (key2305, -2), (key2305, -2), (key2343, -2), (key2200, -6), (key2310, 2), (key2310, 2), (key2347, 2)]

theorem rawRowCheck3632 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form13 = rawRow3632 := by decide +kernel

def row3632 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck3632 : row3632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3632 := by decide +kernel

theorem rowEval3632 (x : Key → ℝ) : Integer.Sparse.eval row3632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3632, Integer.Sparse.eval_collectBalanced, rawRowCheck3632]

def rawRow3633 : Integer.Sparse Key := [(key2092, -2), (key2091, -2), (key2092, -2), (key2095, 6), (key2194, 2), (key2193, 2), (key2194, 2), (key2305, -2), (key2343, -2), (key2305, -2), (key2200, -6), (key2310, 2), (key2347, 2), (key2310, 2)]

theorem rawRowCheck3633 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3633 := by decide +kernel

def row3633 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck3633 : row3633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3633 := by decide +kernel

theorem rowEval3633 (x : Key → ℝ) : Integer.Sparse.eval row3633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3633, Integer.Sparse.eval_collectBalanced, rawRowCheck3633]

def rawRow3634 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2091, -2), (key2095, 6), (key2194, 2), (key2194, 2), (key2193, 2), (key2343, -2), (key2305, -2), (key2305, -2), (key2200, -6), (key2347, 2), (key2310, 2), (key2310, 2)]

theorem rawRowCheck3634 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3634 := by decide +kernel

def row3634 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck3634 : row3634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3634 := by decide +kernel

theorem rowEval3634 (x : Key → ℝ) : Integer.Sparse.eval row3634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3634, Integer.Sparse.eval_collectBalanced, rawRowCheck3634]

def rawRow3635 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2095, -2), (key2091, 6), (key2341, 2), (key2341, 2), (key2343, 2), (key2193, -2), (key2302, -2), (key2302, -2), (key2347, -6), (key2200, 2), (key2310, 2), (key2310, 2)]

theorem rawRowCheck3635 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form13 = rawRow3635 := by decide +kernel

def row3635 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

theorem rowCheck3635 : row3635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3635 := by decide +kernel

theorem rowEval3635 (x : Key → ℝ) : Integer.Sparse.eval row3635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3635, Integer.Sparse.eval_collectBalanced, rawRowCheck3635]

def rawRow3636 : Integer.Sparse Key := [(key2092, -2), (key2095, -2), (key2092, -2), (key2091, 6), (key2341, 2), (key2343, 2), (key2341, 2), (key2302, -2), (key2193, -2), (key2302, -2), (key2347, -6), (key2310, 2), (key2200, 2), (key2310, 2)]

theorem rawRowCheck3636 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form13 = rawRow3636 := by decide +kernel

def row3636 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

theorem rowCheck3636 : row3636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3636 := by decide +kernel

theorem rowEval3636 (x : Key → ℝ) : Integer.Sparse.eval row3636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3636, Integer.Sparse.eval_collectBalanced, rawRowCheck3636]

def rawRow3637 : Integer.Sparse Key := [(key2095, -2), (key2092, -2), (key2092, -2), (key2091, 6), (key2343, 2), (key2341, 2), (key2341, 2), (key2302, -2), (key2302, -2), (key2193, -2), (key2347, -6), (key2310, 2), (key2310, 2), (key2200, 2)]

theorem rawRowCheck3637 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form13 = rawRow3637 := by decide +kernel

def row3637 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

theorem rowCheck3637 : row3637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3637 := by decide +kernel

theorem rowEval3637 (x : Key → ℝ) : Integer.Sparse.eval row3637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3637, Integer.Sparse.eval_collectBalanced, rawRowCheck3637]

def rawRow3638 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2194, -2), (key2200, 6), (key2091, 2), (key2092, 2), (key2092, 2), (key2310, -2), (key2310, -2), (key2347, -2), (key2095, -6), (key2305, 2), (key2305, 2), (key2343, 2)]

theorem rawRowCheck3638 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form13 = rawRow3638 := by decide +kernel

def row3638 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

theorem rowCheck3638 : row3638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3638 := by decide +kernel

theorem rowEval3638 (x : Key → ℝ) : Integer.Sparse.eval row3638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3638, Integer.Sparse.eval_collectBalanced, rawRowCheck3638]

def rawRow3639 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2194, -2), (key2200, 6), (key2092, 2), (key2091, 2), (key2092, 2), (key2310, -2), (key2347, -2), (key2310, -2), (key2095, -6), (key2305, 2), (key2343, 2), (key2305, 2)]

theorem rawRowCheck3639 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form13 = rawRow3639 := by decide +kernel

def row3639 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

theorem rowCheck3639 : row3639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3639 := by decide +kernel

theorem rowEval3639 (x : Key → ℝ) : Integer.Sparse.eval row3639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3639, Integer.Sparse.eval_collectBalanced, rawRowCheck3639]

def rawRow3640 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2193, -2), (key2200, 6), (key2092, 2), (key2092, 2), (key2091, 2), (key2347, -2), (key2310, -2), (key2310, -2), (key2095, -6), (key2343, 2), (key2305, 2), (key2305, 2)]

theorem rawRowCheck3640 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form13 = rawRow3640 := by decide +kernel

def row3640 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

theorem rowCheck3640 : row3640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3640 := by decide +kernel

theorem rowEval3640 (x : Key → ℝ) : Integer.Sparse.eval row3640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3640, Integer.Sparse.eval_collectBalanced, rawRowCheck3640]

def rawRow3641 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2200, -2), (key2193, 6), (key2341, 2), (key2341, 2), (key2347, 2), (key2091, -2), (key2302, -2), (key2302, -2), (key2343, -6), (key2095, 2), (key2305, 2), (key2305, 2)]

theorem rawRowCheck3641 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3641 := by decide +kernel

def row3641 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

theorem rowCheck3641 : row3641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3641 := by decide +kernel

theorem rowEval3641 (x : Key → ℝ) : Integer.Sparse.eval row3641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3641, Integer.Sparse.eval_collectBalanced, rawRowCheck3641]

def rawRow3642 : Integer.Sparse Key := [(key2194, -2), (key2200, -2), (key2194, -2), (key2193, 6), (key2341, 2), (key2347, 2), (key2341, 2), (key2302, -2), (key2091, -2), (key2302, -2), (key2343, -6), (key2305, 2), (key2095, 2), (key2305, 2)]

theorem rawRowCheck3642 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3642 := by decide +kernel

def row3642 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

theorem rowCheck3642 : row3642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3642 := by decide +kernel

theorem rowEval3642 (x : Key → ℝ) : Integer.Sparse.eval row3642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3642, Integer.Sparse.eval_collectBalanced, rawRowCheck3642]

def rawRow3643 : Integer.Sparse Key := [(key2200, -2), (key2194, -2), (key2194, -2), (key2193, 6), (key2347, 2), (key2341, 2), (key2341, 2), (key2302, -2), (key2302, -2), (key2091, -2), (key2343, -6), (key2305, 2), (key2305, 2), (key2095, 2)]

theorem rawRowCheck3643 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3643 := by decide +kernel

def row3643 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

theorem rowCheck3643 : row3643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3643 := by decide +kernel

theorem rowEval3643 (x : Key → ℝ) : Integer.Sparse.eval row3643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3643, Integer.Sparse.eval_collectBalanced, rawRowCheck3643]

def rawRow3644 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2343, -2), (key2347, 6), (key2092, 2), (key2092, 2), (key2095, 2), (key2200, -2), (key2310, -2), (key2310, -2), (key2091, -6), (key2193, 2), (key2302, 2), (key2302, 2)]

theorem rawRowCheck3644 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form13 = rawRow3644 := by decide +kernel

def row3644 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

theorem rowCheck3644 : row3644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3644 := by decide +kernel

theorem rowEval3644 (x : Key → ℝ) : Integer.Sparse.eval row3644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3644, Integer.Sparse.eval_collectBalanced, rawRowCheck3644]

def rawRow3645 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2341, -2), (key2347, 6), (key2092, 2), (key2095, 2), (key2092, 2), (key2310, -2), (key2200, -2), (key2310, -2), (key2091, -6), (key2302, 2), (key2193, 2), (key2302, 2)]

theorem rawRowCheck3645 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form13 = rawRow3645 := by decide +kernel

def row3645 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

theorem rowCheck3645 : row3645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3645 := by decide +kernel

theorem rowEval3645 (x : Key → ℝ) : Integer.Sparse.eval row3645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3645, Integer.Sparse.eval_collectBalanced, rawRowCheck3645]

def rawRow3646 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2341, -2), (key2347, 6), (key2095, 2), (key2092, 2), (key2092, 2), (key2310, -2), (key2310, -2), (key2200, -2), (key2091, -6), (key2302, 2), (key2302, 2), (key2193, 2)]

theorem rawRowCheck3646 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form13 = rawRow3646 := by decide +kernel

def row3646 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

theorem rowCheck3646 : row3646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3646 := by decide +kernel

theorem rowEval3646 (x : Key → ℝ) : Integer.Sparse.eval row3646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck3646, Integer.Sparse.eval_collectBalanced, rawRowCheck3646]

def rawRow3647 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2347, -2), (key2343, 6), (key2194, 2), (key2194, 2), (key2200, 2), (key2095, -2), (key2305, -2), (key2305, -2), (key2193, -6), (key2091, 2), (key2302, 2), (key2302, 2)]

theorem rawRowCheck3647 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow3647 := by decide +kernel

def row3647 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

theorem rowCheck3647 : row3647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3647 := by decide +kernel

theorem rowEval3647 (x : Key → ℝ) : Integer.Sparse.eval row3647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3647, Integer.Sparse.eval_collectBalanced, rawRowCheck3647]

def rawRow3648 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2341, -2), (key2343, 6), (key2194, 2), (key2200, 2), (key2194, 2), (key2305, -2), (key2095, -2), (key2305, -2), (key2193, -6), (key2302, 2), (key2091, 2), (key2302, 2)]

theorem rawRowCheck3648 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow3648 := by decide +kernel

def row3648 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

theorem rowCheck3648 : row3648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3648 := by decide +kernel

theorem rowEval3648 (x : Key → ℝ) : Integer.Sparse.eval row3648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3648, Integer.Sparse.eval_collectBalanced, rawRowCheck3648]

def rawRow3649 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2341, -2), (key2343, 6), (key2200, 2), (key2194, 2), (key2194, 2), (key2305, -2), (key2305, -2), (key2095, -2), (key2193, -6), (key2302, 2), (key2302, 2), (key2091, 2)]

theorem rawRowCheck3649 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow3649 := by decide +kernel

def row3649 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

theorem rowCheck3649 : row3649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3649 := by decide +kernel

theorem rowEval3649 (x : Key → ℝ) : Integer.Sparse.eval row3649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck3649, Integer.Sparse.eval_collectBalanced, rawRowCheck3649]

def rawRow3650 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2392, 2), (key2406, 2), (key2406, 2), (key2409, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2543, -1), (key2482, -1), (key2543, -1), (key2437, -2), (key2440, -2), (key2440, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2554, 1), (key2506, 1), (key2554, 1)]

theorem rawRowCheck3650 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3650 := by decide +kernel

def row3650 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

theorem rowCheck3650 : row3650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3650 := by decide +kernel

theorem rowEval3650 (x : Key → ℝ) : Integer.Sparse.eval row3650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3650, Integer.Sparse.eval_collectBalanced, rawRowCheck3650]

def rawRow3651 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2392, 2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2406, 2), (key2482, -1), (key2480, -1), (key2543, -1), (key2480, -1), (key2543, -1), (key2482, -1), (key2440, -2), (key2437, -2), (key2440, -2), (key2506, 1), (key2503, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2506, 1)]

theorem rawRowCheck3651 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3651 := by decide +kernel

def row3651 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

theorem rowCheck3651 : row3651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3651 := by decide +kernel

theorem rowEval3651 (x : Key → ℝ) : Integer.Sparse.eval row3651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3651, Integer.Sparse.eval_collectBalanced, rawRowCheck3651]

def rawRow3652 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2392, 2), (key2392, 2), (key2390, 2), (key2409, 2), (key2406, 2), (key2406, 2), (key2543, -1), (key2543, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2440, -2), (key2440, -2), (key2437, -2), (key2554, 1), (key2554, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1)]

theorem rawRowCheck3652 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3652 := by decide +kernel

def row3652 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

theorem rowCheck3652 : row3652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3652 := by decide +kernel

theorem rowEval3652 (x : Key → ℝ) : Integer.Sparse.eval row3652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3652, Integer.Sparse.eval_collectBalanced, rawRowCheck3652]

def rawRow3653 : Integer.Sparse Key := [(key2381, -2), (key2392, -2), (key2392, -2), (key2378, 2), (key2378, 2), (key2390, 2), (key2538, 2), (key2543, 2), (key2543, 2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2554, -2), (key2554, -2), (key2563, -2), (key2440, 1), (key2440, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1)]

theorem rawRowCheck3653 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form14 = rawRow3653 := by decide +kernel

def row3653 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck3653 : row3653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3653 := by decide +kernel

theorem rowEval3653 (x : Key → ℝ) : Integer.Sparse.eval row3653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3653, Integer.Sparse.eval_collectBalanced, rawRowCheck3653]

def rawRow3654 : Integer.Sparse Key := [(key2392, -2), (key2381, -2), (key2392, -2), (key2378, 2), (key2390, 2), (key2378, 2), (key2543, 2), (key2538, 2), (key2543, 2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2554, -2), (key2563, -2), (key2554, -2), (key2506, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2440, 1), (key2506, 1)]

theorem rawRowCheck3654 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form14 = rawRow3654 := by decide +kernel

def row3654 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck3654 : row3654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3654 := by decide +kernel

theorem rowEval3654 (x : Key → ℝ) : Integer.Sparse.eval row3654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3654, Integer.Sparse.eval_collectBalanced, rawRowCheck3654]

def rawRow3655 : Integer.Sparse Key := [(key2392, -2), (key2392, -2), (key2381, -2), (key2390, 2), (key2378, 2), (key2378, 2), (key2543, 2), (key2543, 2), (key2538, 2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2563, -2), (key2554, -2), (key2554, -2), (key2522, 1), (key2506, 1), (key2522, 1), (key2440, 1), (key2506, 1), (key2440, 1)]

theorem rawRowCheck3655 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form14 = rawRow3655 := by decide +kernel

def row3655 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

theorem rowCheck3655 : row3655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3655 := by decide +kernel

theorem rowEval3655 (x : Key → ℝ) : Integer.Sparse.eval row3655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3655, Integer.Sparse.eval_collectBalanced, rawRowCheck3655]

def rawRow3656 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2440, 2), (key2378, 2), (key2378, 2), (key2381, 2), (key2503, -1), (key2506, -1), (key2503, -1), (key2554, -1), (key2506, -1), (key2554, -1), (key2390, -2), (key2392, -2), (key2392, -2), (key2480, 1), (key2482, 1), (key2480, 1), (key2543, 1), (key2482, 1), (key2543, 1)]

theorem rawRowCheck3656 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form14 = rawRow3656 := by decide +kernel

def row3656 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

theorem rowCheck3656 : row3656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3656 := by decide +kernel

theorem rowEval3656 (x : Key → ℝ) : Integer.Sparse.eval row3656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3656, Integer.Sparse.eval_collectBalanced, rawRowCheck3656]

def rawRow3657 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2440, 2), (key2437, 2), (key2440, 2), (key2378, 2), (key2381, 2), (key2378, 2), (key2506, -1), (key2503, -1), (key2554, -1), (key2503, -1), (key2554, -1), (key2506, -1), (key2392, -2), (key2390, -2), (key2392, -2), (key2482, 1), (key2480, 1), (key2543, 1), (key2480, 1), (key2543, 1), (key2482, 1)]

theorem rawRowCheck3657 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form14 = rawRow3657 := by decide +kernel

def row3657 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

theorem rowCheck3657 : row3657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3657 := by decide +kernel

theorem rowEval3657 (x : Key → ℝ) : Integer.Sparse.eval row3657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3657, Integer.Sparse.eval_collectBalanced, rawRowCheck3657]

def rawRow3658 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2440, 2), (key2440, 2), (key2437, 2), (key2381, 2), (key2378, 2), (key2378, 2), (key2554, -1), (key2554, -1), (key2506, -1), (key2506, -1), (key2503, -1), (key2503, -1), (key2392, -2), (key2392, -2), (key2390, -2), (key2543, 1), (key2543, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1)]

theorem rawRowCheck3658 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form14 = rawRow3658 := by decide +kernel

def row3658 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

theorem rowCheck3658 : row3658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3658 := by decide +kernel

theorem rowEval3658 (x : Key → ℝ) : Integer.Sparse.eval row3658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3658, Integer.Sparse.eval_collectBalanced, rawRowCheck3658]

def rawRow3659 : Integer.Sparse Key := [(key2409, -2), (key2440, -2), (key2440, -2), (key2406, 2), (key2406, 2), (key2437, 2), (key2538, 2), (key2554, 2), (key2554, 2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, 1), (key2392, 1), (key2482, 1), (key2482, 1), (key2522, 1), (key2522, 1)]

theorem rawRowCheck3659 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow3659 := by decide +kernel

def row3659 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck3659 : row3659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3659 := by decide +kernel

theorem rowEval3659 (x : Key → ℝ) : Integer.Sparse.eval row3659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3659, Integer.Sparse.eval_collectBalanced, rawRowCheck3659]

def rawRow3660 : Integer.Sparse Key := [(key2440, -2), (key2409, -2), (key2440, -2), (key2406, 2), (key2437, 2), (key2406, 2), (key2554, 2), (key2538, 2), (key2554, 2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2482, 1)]

theorem rawRowCheck3660 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow3660 := by decide +kernel

def row3660 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck3660 : row3660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3660 := by decide +kernel

theorem rowEval3660 (x : Key → ℝ) : Integer.Sparse.eval row3660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3660, Integer.Sparse.eval_collectBalanced, rawRowCheck3660]

def rawRow3661 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2409, -2), (key2437, 2), (key2406, 2), (key2406, 2), (key2554, 2), (key2554, 2), (key2538, 2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, 1), (key2482, 1), (key2522, 1), (key2392, 1), (key2482, 1), (key2392, 1)]

theorem rawRowCheck3661 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow3661 := by decide +kernel

def row3661 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

theorem rowCheck3661 : row3661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3661 := by decide +kernel

theorem rowEval3661 (x : Key → ℝ) : Integer.Sparse.eval row3661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3661, Integer.Sparse.eval_collectBalanced, rawRowCheck3661]

def rawRow3662 : Integer.Sparse Key := [(key2538, -2), (key2543, -2), (key2543, -2), (key2554, 2), (key2554, 2), (key2563, 2), (key2381, 2), (key2392, 2), (key2392, 2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, 1), (key2406, 1), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1)]

theorem rawRowCheck3662 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form14 = rawRow3662 := by decide +kernel

def row3662 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

theorem rowCheck3662 : row3662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3662 := by decide +kernel

theorem rowEval3662 (x : Key → ℝ) : Integer.Sparse.eval row3662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3662, Integer.Sparse.eval_collectBalanced, rawRowCheck3662]

def rawRow3663 : Integer.Sparse Key := [(key2543, -2), (key2538, -2), (key2543, -2), (key2554, 2), (key2563, 2), (key2554, 2), (key2392, 2), (key2381, 2), (key2392, 2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, 1), (key2480, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2472, 1)]

theorem rawRowCheck3663 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form14 = rawRow3663 := by decide +kernel

def row3663 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

theorem rowCheck3663 : row3663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3663 := by decide +kernel

theorem rowEval3663 (x : Key → ℝ) : Integer.Sparse.eval row3663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3663, Integer.Sparse.eval_collectBalanced, rawRowCheck3663]

def rawRow3664 : Integer.Sparse Key := [(key2543, -2), (key2543, -2), (key2538, -2), (key2563, 2), (key2554, 2), (key2554, 2), (key2392, 2), (key2392, 2), (key2381, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, 1), (key2472, 1), (key2480, 1), (key2406, 1), (key2472, 1), (key2406, 1)]

theorem rawRowCheck3664 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form14 = rawRow3664 := by decide +kernel

def row3664 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

theorem rowCheck3664 : row3664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3664 := by decide +kernel

theorem rowEval3664 (x : Key → ℝ) : Integer.Sparse.eval row3664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck3664, Integer.Sparse.eval_collectBalanced, rawRowCheck3664]

def rawRow3665 : Integer.Sparse Key := [(key2538, -2), (key2554, -2), (key2554, -2), (key2543, 2), (key2543, 2), (key2563, 2), (key2409, 2), (key2440, 2), (key2440, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, 1), (key2378, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1)]

theorem rawRowCheck3665 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow3665 := by decide +kernel

def row3665 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

theorem rowCheck3665 : row3665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3665 := by decide +kernel

theorem rowEval3665 (x : Key → ℝ) : Integer.Sparse.eval row3665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3665, Integer.Sparse.eval_collectBalanced, rawRowCheck3665]

def rawRow3666 : Integer.Sparse Key := [(key2554, -2), (key2538, -2), (key2554, -2), (key2543, 2), (key2563, 2), (key2543, 2), (key2440, 2), (key2409, 2), (key2440, 2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, 1), (key2503, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2472, 1)]

theorem rawRowCheck3666 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow3666 := by decide +kernel

def row3666 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

theorem rowCheck3666 : row3666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3666 := by decide +kernel

theorem rowEval3666 (x : Key → ℝ) : Integer.Sparse.eval row3666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck3666, Integer.Sparse.eval_collectBalanced, rawRowCheck3666]

def rawRow3667 : Integer.Sparse Key := [(key2554, -2), (key2554, -2), (key2538, -2), (key2563, 2), (key2543, 2), (key2543, 2), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, 1), (key2472, 1), (key2503, 1), (key2378, 1), (key2472, 1), (key2378, 1)]

theorem rawRowCheck3667 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow3667 := by decide +kernel

def row3667 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

theorem rowCheck3667 : row3667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3667 := by decide +kernel

theorem rowEval3667 (x : Key → ℝ) : Integer.Sparse.eval row3667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck3667, Integer.Sparse.eval_collectBalanced, rawRowCheck3667]

def rawRow3668 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2791, 2), (key2791, 2), (key2942, 2), (key2802, 1), (key2806, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2949, 1), (key2857, -1), (key2896, -1), (key2857, -1), (key2975, -1), (key2896, -1), (key2975, -1), (key2826, -2), (key2826, -2), (key2959, -2), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1)]

theorem rawRowCheck3668 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form15 = rawRow3668 := by decide +kernel

def row3668 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck3668 : row3668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3668 := by decide +kernel

theorem rowEval3668 (x : Key → ℝ) : Integer.Sparse.eval row3668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3668, Integer.Sparse.eval_collectBalanced, rawRowCheck3668]

def rawRow3669 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2937, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2791, 2), (key2942, 2), (key2791, 2), (key2806, 1), (key2802, 1), (key2949, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2896, -1), (key2857, -1), (key2975, -1), (key2857, -1), (key2975, -1), (key2896, -1), (key2826, -2), (key2959, -2), (key2826, -2), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1)]

theorem rawRowCheck3669 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form15 = rawRow3669 := by decide +kernel

def row3669 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck3669 : row3669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3669 := by decide +kernel

theorem rowEval3669 (x : Key → ℝ) : Integer.Sparse.eval row3669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3669, Integer.Sparse.eval_collectBalanced, rawRowCheck3669]

def rawRow3670 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2783, -1), (key2783, -1), (key2779, -1), (key2779, -1), (key2942, 2), (key2791, 2), (key2791, 2), (key2949, 1), (key2949, 1), (key2806, 1), (key2806, 1), (key2802, 1), (key2802, 1), (key2975, -1), (key2975, -1), (key2896, -1), (key2896, -1), (key2857, -1), (key2857, -1), (key2959, -2), (key2826, -2), (key2826, -2), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1)]

theorem rawRowCheck3670 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form15 = rawRow3670 := by decide +kernel

def row3670 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck3670 : row3670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3670 := by decide +kernel

theorem rowEval3670 (x : Key → ℝ) : Integer.Sparse.eval row3670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3670, Integer.Sparse.eval_collectBalanced, rawRowCheck3670]

def rawRow3671 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2746, -2), (key2903, -2), (key2903, -2), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1)]

theorem rawRowCheck3671 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form15 = rawRow3671 := by decide +kernel

def row3671 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

theorem rowCheck3671 : row3671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3671 := by decide +kernel

theorem rowEval3671 (x : Key → ℝ) : Integer.Sparse.eval row3671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3671, Integer.Sparse.eval_collectBalanced, rawRowCheck3671]

def rawRow3672 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2903, -2), (key2746, -2), (key2903, -2), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1)]

theorem rawRowCheck3672 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form15 = rawRow3672 := by decide +kernel

def row3672 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

theorem rowCheck3672 : row3672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3672 := by decide +kernel

theorem rowEval3672 (x : Key → ℝ) : Integer.Sparse.eval row3672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3672, Integer.Sparse.eval_collectBalanced, rawRowCheck3672]

def rawRow3673 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1), (key2903, -2), (key2903, -2), (key2746, -2), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1)]

theorem rawRowCheck3673 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form15 = rawRow3673 := by decide +kernel

def row3673 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

theorem rowCheck3673 : row3673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3673 := by decide +kernel

theorem rowEval3673 (x : Key → ℝ) : Integer.Sparse.eval row3673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3673, Integer.Sparse.eval_collectBalanced, rawRowCheck3673]

def rawRow3674 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2949, -1), (key2826, 2), (key2826, 2), (key2959, 2), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2867, -1), (key2903, -1), (key2867, -1), (key2982, -1), (key2903, -1), (key2982, -1), (key2791, -2), (key2791, -2), (key2942, -2), (key2857, 1), (key2896, 1), (key2857, 1), (key2975, 1), (key2896, 1), (key2975, 1)]

theorem rawRowCheck3674 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form15 = rawRow3674 := by decide +kernel

def row3674 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck3674 : row3674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3674 := by decide +kernel

theorem rowEval3674 (x : Key → ℝ) : Integer.Sparse.eval row3674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3674, Integer.Sparse.eval_collectBalanced, rawRowCheck3674]

def rawRow3675 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2949, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2826, 2), (key2959, 2), (key2826, 2), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2903, -1), (key2867, -1), (key2982, -1), (key2867, -1), (key2982, -1), (key2903, -1), (key2791, -2), (key2942, -2), (key2791, -2), (key2896, 1), (key2857, 1), (key2975, 1), (key2857, 1), (key2975, 1), (key2896, 1)]

theorem rawRowCheck3675 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form15 = rawRow3675 := by decide +kernel

def row3675 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck3675 : row3675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3675 := by decide +kernel

theorem rowEval3675 (x : Key → ℝ) : Integer.Sparse.eval row3675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3675, Integer.Sparse.eval_collectBalanced, rawRowCheck3675]

def rawRow3676 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2959, 2), (key2826, 2), (key2826, 2), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2982, -1), (key2982, -1), (key2903, -1), (key2903, -1), (key2867, -1), (key2867, -1), (key2942, -2), (key2791, -2), (key2791, -2), (key2975, 1), (key2975, 1), (key2896, 1), (key2896, 1), (key2857, 1), (key2857, 1)]

theorem rawRowCheck3676 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form15 = rawRow3676 := by decide +kernel

def row3676 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck3676 : row3676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3676 := by decide +kernel

theorem rowEval3676 (x : Key → ℝ) : Integer.Sparse.eval row3676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3676, Integer.Sparse.eval_collectBalanced, rawRowCheck3676]

def rawRow3677 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1), (key2652, -2), (key2896, -2), (key2896, -2), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1)]

theorem rawRowCheck3677 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow3677 := by decide +kernel

def row3677 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

theorem rowCheck3677 : row3677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3677 := by decide +kernel

theorem rowEval3677 (x : Key → ℝ) : Integer.Sparse.eval row3677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3677, Integer.Sparse.eval_collectBalanced, rawRowCheck3677]

def rawRow3678 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2896, -2), (key2652, -2), (key2896, -2), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1)]

theorem rawRowCheck3678 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow3678 := by decide +kernel

def row3678 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

theorem rowCheck3678 : row3678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3678 := by decide +kernel

theorem rowEval3678 (x : Key → ℝ) : Integer.Sparse.eval row3678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3678, Integer.Sparse.eval_collectBalanced, rawRowCheck3678]

def rawRow3679 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1), (key2896, -2), (key2896, -2), (key2652, -2), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1)]

theorem rawRowCheck3679 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow3679 := by decide +kernel

def row3679 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

theorem rowCheck3679 : row3679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3679 := by decide +kernel

theorem rowEval3679 (x : Key → ℝ) : Integer.Sparse.eval row3679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3679, Integer.Sparse.eval_collectBalanced, rawRowCheck3679]

def rawRow3680 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1), (key2664, -2), (key2779, -2), (key2779, -2), (key2699, 1), (key2699, 1), (key2802, 1), (key2802, 1), (key2852, 1), (key2852, 1)]

theorem rawRowCheck3680 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form15 = rawRow3680 := by decide +kernel

def row3680 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck3680 : row3680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3680 := by decide +kernel

theorem rowEval3680 (x : Key → ℝ) : Integer.Sparse.eval row3680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3680, Integer.Sparse.eval_collectBalanced, rawRowCheck3680]

def rawRow3681 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2779, -2), (key2664, -2), (key2779, -2), (key2802, 1), (key2852, 1), (key2699, 1), (key2852, 1), (key2699, 1), (key2802, 1)]

theorem rawRowCheck3681 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form15 = rawRow3681 := by decide +kernel

def row3681 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck3681 : row3681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3681 := by decide +kernel

theorem rowEval3681 (x : Key → ℝ) : Integer.Sparse.eval row3681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3681, Integer.Sparse.eval_collectBalanced, rawRowCheck3681]

def rawRow3682 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1), (key2779, -2), (key2779, -2), (key2664, -2), (key2852, 1), (key2802, 1), (key2852, 1), (key2699, 1), (key2802, 1), (key2699, 1)]

theorem rawRowCheck3682 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form15 = rawRow3682 := by decide +kernel

def row3682 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

theorem rowCheck3682 : row3682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3682 := by decide +kernel

theorem rowEval3682 (x : Key → ℝ) : Integer.Sparse.eval row3682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck3682, Integer.Sparse.eval_collectBalanced, rawRowCheck3682]

def rawRow3683 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2609, -2), (key2802, -2), (key2802, -2), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1)]

theorem rawRowCheck3683 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow3683 := by decide +kernel

def row3683 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck3683 : row3683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3683 := by decide +kernel

theorem rowEval3683 (x : Key → ℝ) : Integer.Sparse.eval row3683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3683, Integer.Sparse.eval_collectBalanced, rawRowCheck3683]

def rawRow3684 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2802, -2), (key2609, -2), (key2802, -2), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1)]

theorem rawRowCheck3684 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow3684 := by decide +kernel

def row3684 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck3684 : row3684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3684 := by decide +kernel

theorem rowEval3684 (x : Key → ℝ) : Integer.Sparse.eval row3684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck3684, Integer.Sparse.eval_collectBalanced, rawRowCheck3684]

def rawRow3685 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1), (key2802, -2), (key2802, -2), (key2609, -2), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1)]

theorem rawRowCheck3685 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow3685 := by decide +kernel

def row3685 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

theorem rowCheck3685 : row3685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3685 := by decide +kernel

theorem rowEval3685 (x : Key → ℝ) : Integer.Sparse.eval row3685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck3685, Integer.Sparse.eval_collectBalanced, rawRowCheck3685]

def rawRow3686 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2645, 2), (key2645, 2), (key2651, 2), (key2663, 2), (key2666, 2), (key2666, 2), (key2734, -2), (key2734, -2), (key2745, -2), (key2935, -2), (key2935, -2), (key2941, -2), (key2947, 2), (key2947, 2), (key2958, 2)]

theorem rawRowCheck3686 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form16 = rawRow3686 := by decide +kernel

def row3686 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

theorem rowCheck3686 : row3686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3686 := by decide +kernel

theorem rowEval3686 (x : Key → ℝ) : Integer.Sparse.eval row3686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3686, Integer.Sparse.eval_collectBalanced, rawRowCheck3686]

def rawRow3687 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2645, 2), (key2651, 2), (key2645, 2), (key2666, 2), (key2663, 2), (key2666, 2), (key2734, -2), (key2745, -2), (key2734, -2), (key2935, -2), (key2941, -2), (key2935, -2), (key2947, 2), (key2958, 2), (key2947, 2)]

theorem rawRowCheck3687 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form16 = rawRow3687 := by decide +kernel

def row3687 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

theorem rowCheck3687 : row3687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3687 := by decide +kernel

theorem rowEval3687 (x : Key → ℝ) : Integer.Sparse.eval row3687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3687, Integer.Sparse.eval_collectBalanced, rawRowCheck3687]

def rawRow3688 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2651, 2), (key2645, 2), (key2645, 2), (key2666, 2), (key2666, 2), (key2663, 2), (key2745, -2), (key2734, -2), (key2734, -2), (key2941, -2), (key2935, -2), (key2935, -2), (key2958, 2), (key2947, 2), (key2947, 2)]

theorem rawRowCheck3688 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form16 = rawRow3688 := by decide +kernel

def row3688 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

theorem rowCheck3688 : row3688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3688 := by decide +kernel

theorem rowEval3688 (x : Key → ℝ) : Integer.Sparse.eval row3688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3688, Integer.Sparse.eval_collectBalanced, rawRowCheck3688]

def rawRow3689 : Integer.Sparse Key := [(key2645, -2), (key2645, -2), (key2651, -2), (key2608, 2), (key2624, 2), (key2624, 2), (key2722, 2), (key2722, 2), (key2745, 2), (key2663, -2), (key2698, -2), (key2698, -2), (key2958, -2), (key2981, -2), (key2981, -2), (key2941, 2), (key2974, 2), (key2974, 2)]

theorem rawRowCheck3689 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form16 = rawRow3689 := by decide +kernel

def row3689 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

theorem rowCheck3689 : row3689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3689 := by decide +kernel

theorem rowEval3689 (x : Key → ℝ) : Integer.Sparse.eval row3689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3689, Integer.Sparse.eval_collectBalanced, rawRowCheck3689]

def rawRow3690 : Integer.Sparse Key := [(key2645, -2), (key2651, -2), (key2645, -2), (key2624, 2), (key2608, 2), (key2624, 2), (key2722, 2), (key2745, 2), (key2722, 2), (key2698, -2), (key2663, -2), (key2698, -2), (key2981, -2), (key2958, -2), (key2981, -2), (key2974, 2), (key2941, 2), (key2974, 2)]

theorem rawRowCheck3690 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form16 = rawRow3690 := by decide +kernel

def row3690 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

theorem rowCheck3690 : row3690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3690 := by decide +kernel

theorem rowEval3690 (x : Key → ℝ) : Integer.Sparse.eval row3690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3690, Integer.Sparse.eval_collectBalanced, rawRowCheck3690]

def rawRow3691 : Integer.Sparse Key := [(key2651, -2), (key2645, -2), (key2645, -2), (key2624, 2), (key2624, 2), (key2608, 2), (key2745, 2), (key2722, 2), (key2722, 2), (key2698, -2), (key2698, -2), (key2663, -2), (key2981, -2), (key2981, -2), (key2958, -2), (key2974, 2), (key2974, 2), (key2941, 2)]

theorem rawRowCheck3691 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form16 = rawRow3691 := by decide +kernel

def row3691 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

theorem rowCheck3691 : row3691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3691 := by decide +kernel

theorem rowEval3691 (x : Key → ℝ) : Integer.Sparse.eval row3691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3691, Integer.Sparse.eval_collectBalanced, rawRowCheck3691]

def rawRow3692 : Integer.Sparse Key := [(key2663, -2), (key2666, -2), (key2666, -2), (key2722, 2), (key2722, 2), (key2745, 2), (key2608, 2), (key2611, 2), (key2611, 2), (key2947, -2), (key2947, -2), (key2958, -2), (key2645, -2), (key2645, -2), (key2651, -2), (key2734, 2), (key2734, 2), (key2745, 2)]

theorem rawRowCheck3692 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form16 = rawRow3692 := by decide +kernel

def row3692 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

theorem rowCheck3692 : row3692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3692 := by decide +kernel

theorem rowEval3692 (x : Key → ℝ) : Integer.Sparse.eval row3692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3692, Integer.Sparse.eval_collectBalanced, rawRowCheck3692]

def rawRow3693 : Integer.Sparse Key := [(key2666, -2), (key2663, -2), (key2666, -2), (key2722, 2), (key2745, 2), (key2722, 2), (key2611, 2), (key2608, 2), (key2611, 2), (key2947, -2), (key2958, -2), (key2947, -2), (key2645, -2), (key2651, -2), (key2645, -2), (key2734, 2), (key2745, 2), (key2734, 2)]

theorem rawRowCheck3693 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form16 = rawRow3693 := by decide +kernel

def row3693 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

theorem rowCheck3693 : row3693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3693 := by decide +kernel

theorem rowEval3693 (x : Key → ℝ) : Integer.Sparse.eval row3693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3693, Integer.Sparse.eval_collectBalanced, rawRowCheck3693]

def rawRow3694 : Integer.Sparse Key := [(key2666, -2), (key2666, -2), (key2663, -2), (key2745, 2), (key2722, 2), (key2722, 2), (key2611, 2), (key2611, 2), (key2608, 2), (key2958, -2), (key2947, -2), (key2947, -2), (key2651, -2), (key2645, -2), (key2645, -2), (key2745, 2), (key2734, 2), (key2734, 2)]

theorem rawRowCheck3694 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form16 = rawRow3694 := by decide +kernel

def row3694 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

theorem rowCheck3694 : row3694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3694 := by decide +kernel

theorem rowEval3694 (x : Key → ℝ) : Integer.Sparse.eval row3694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3694, Integer.Sparse.eval_collectBalanced, rawRowCheck3694]

def rawRow3695 : Integer.Sparse Key := [(key2734, -2), (key2734, -2), (key2745, -2), (key2663, 2), (key2698, 2), (key2698, 2), (key2947, 2), (key2947, 2), (key2958, 2), (key2608, -2), (key2801, -2), (key2801, -2), (key2745, -2), (key2902, -2), (key2902, -2), (key2651, 2), (key2895, 2), (key2895, 2)]

theorem rawRowCheck3695 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow3695 := by decide +kernel

def row3695 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

theorem rowCheck3695 : row3695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3695 := by decide +kernel

theorem rowEval3695 (x : Key → ℝ) : Integer.Sparse.eval row3695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3695, Integer.Sparse.eval_collectBalanced, rawRowCheck3695]

def rawRow3696 : Integer.Sparse Key := [(key2734, -2), (key2745, -2), (key2734, -2), (key2698, 2), (key2663, 2), (key2698, 2), (key2947, 2), (key2958, 2), (key2947, 2), (key2801, -2), (key2608, -2), (key2801, -2), (key2902, -2), (key2745, -2), (key2902, -2), (key2895, 2), (key2651, 2), (key2895, 2)]

theorem rawRowCheck3696 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow3696 := by decide +kernel

def row3696 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

theorem rowCheck3696 : row3696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3696 := by decide +kernel

theorem rowEval3696 (x : Key → ℝ) : Integer.Sparse.eval row3696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3696, Integer.Sparse.eval_collectBalanced, rawRowCheck3696]

def rawRow3697 : Integer.Sparse Key := [(key2745, -2), (key2734, -2), (key2734, -2), (key2698, 2), (key2698, 2), (key2663, 2), (key2958, 2), (key2947, 2), (key2947, 2), (key2801, -2), (key2801, -2), (key2608, -2), (key2902, -2), (key2902, -2), (key2745, -2), (key2895, 2), (key2895, 2), (key2651, 2)]

theorem rawRowCheck3697 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow3697 := by decide +kernel

def row3697 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

theorem rowCheck3697 : row3697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3697 := by decide +kernel

theorem rowEval3697 (x : Key → ℝ) : Integer.Sparse.eval row3697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck3697, Integer.Sparse.eval_collectBalanced, rawRowCheck3697]

def rawRow3698 : Integer.Sparse Key := [(key2935, -2), (key2935, -2), (key2941, -2), (key2958, 2), (key2981, 2), (key2981, 2), (key2645, 2), (key2645, 2), (key2651, 2), (key2745, -2), (key2902, -2), (key2902, -2), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, 2), (key2698, 2), (key2698, 2)]

theorem rawRowCheck3698 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form16 = rawRow3698 := by decide +kernel

def row3698 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

theorem rowCheck3698 : row3698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3698 := by decide +kernel

theorem rowEval3698 (x : Key → ℝ) : Integer.Sparse.eval row3698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3698, Integer.Sparse.eval_collectBalanced, rawRowCheck3698]

def rawRow3699 : Integer.Sparse Key := [(key2935, -2), (key2941, -2), (key2935, -2), (key2981, 2), (key2958, 2), (key2981, 2), (key2645, 2), (key2651, 2), (key2645, 2), (key2902, -2), (key2745, -2), (key2902, -2), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, 2), (key2663, 2), (key2698, 2)]

theorem rawRowCheck3699 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form16 = rawRow3699 := by decide +kernel

def row3699 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

theorem rowCheck3699 : row3699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3699 := by decide +kernel

theorem rowEval3699 (x : Key → ℝ) : Integer.Sparse.eval row3699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3699, Integer.Sparse.eval_collectBalanced, rawRowCheck3699]

def rawRow3700 : Integer.Sparse Key := [(key2941, -2), (key2935, -2), (key2935, -2), (key2981, 2), (key2981, 2), (key2958, 2), (key2651, 2), (key2645, 2), (key2645, 2), (key2902, -2), (key2902, -2), (key2745, -2), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, 2), (key2698, 2), (key2663, 2)]

theorem rawRowCheck3700 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form16 = rawRow3700 := by decide +kernel

def row3700 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

theorem rowCheck3700 : row3700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3700 := by decide +kernel

theorem rowEval3700 (x : Key → ℝ) : Integer.Sparse.eval row3700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck3700, Integer.Sparse.eval_collectBalanced, rawRowCheck3700]

def rawRow3701 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2941, 2), (key2974, 2), (key2974, 2), (key2734, 2), (key2734, 2), (key2745, 2), (key2651, -2), (key2895, -2), (key2895, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, 2), (key2801, 2), (key2801, 2)]

theorem rawRowCheck3701 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow3701 := by decide +kernel

def row3701 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

theorem rowCheck3701 : row3701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3701 := by decide +kernel

theorem rowEval3701 (x : Key → ℝ) : Integer.Sparse.eval row3701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3701, Integer.Sparse.eval_collectBalanced, rawRowCheck3701]

def rawRow3702 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2974, 2), (key2941, 2), (key2974, 2), (key2734, 2), (key2745, 2), (key2734, 2), (key2895, -2), (key2651, -2), (key2895, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, 2), (key2608, 2), (key2801, 2)]

theorem rawRowCheck3702 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow3702 := by decide +kernel

def row3702 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

theorem rowCheck3702 : row3702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3702 := by decide +kernel

theorem rowEval3702 (x : Key → ℝ) : Integer.Sparse.eval row3702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck3702, Integer.Sparse.eval_collectBalanced, rawRowCheck3702]

def rawRow3703 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2974, 2), (key2974, 2), (key2941, 2), (key2745, 2), (key2734, 2), (key2734, 2), (key2895, -2), (key2895, -2), (key2651, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, 2), (key2801, 2), (key2608, 2)]

theorem rawRowCheck3703 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow3703 := by decide +kernel

def row3703 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

theorem rowCheck3703 : row3703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3703 := by decide +kernel

theorem rowEval3703 (x : Key → ℝ) : Integer.Sparse.eval row3703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck3703, Integer.Sparse.eval_collectBalanced, rawRowCheck3703]

def rawRow3704 : Integer.Sparse Key := [(key1296, -2), (key1788, -2), (key1798, -2), (key1296, 1), (key1302, 1), (key1573, 1), (key1596, 1), (key1790, 1), (key1798, 1), (key1316, 2), (key1813, 2), (key1825, 2), (key1316, -1), (key1329, -1), (key1424, -1), (key1447, -1), (key1817, -1), (key1825, -1), (key1337, -1), (key1339, -1), (key1655, -1), (key1667, -1), (key1839, -1), (key1844, -1), (key1337, 1), (key1345, 1), (key1455, 1), (key1466, 1), (key1841, 1), (key1844, 1)]

theorem rawRowCheck3704 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form0 = rawRow3704 := by decide +kernel

def row3704 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

theorem rowCheck3704 : row3704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3704 := by decide +kernel

theorem rowEval3704 (x : Key → ℝ) : Integer.Sparse.eval row3704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3704, Integer.Sparse.eval_collectBalanced, rawRowCheck3704]

def rawRow3705 : Integer.Sparse Key := [(key1296, -2), (key1798, -2), (key1788, -2), (key1302, 1), (key1296, 1), (key1596, 1), (key1573, 1), (key1798, 1), (key1790, 1), (key1316, 2), (key1825, 2), (key1813, 2), (key1329, -1), (key1316, -1), (key1447, -1), (key1424, -1), (key1825, -1), (key1817, -1), (key1339, -1), (key1337, -1), (key1667, -1), (key1655, -1), (key1844, -1), (key1839, -1), (key1345, 1), (key1337, 1), (key1466, 1), (key1455, 1), (key1844, 1), (key1841, 1)]

theorem rawRowCheck3705 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form0 = rawRow3705 := by decide +kernel

def row3705 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

theorem rowCheck3705 : row3705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3705 := by decide +kernel

theorem rowEval3705 (x : Key → ℝ) : Integer.Sparse.eval row3705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3705, Integer.Sparse.eval_collectBalanced, rawRowCheck3705]

def rawRow3706 : Integer.Sparse Key := [(key1788, -2), (key1296, -2), (key1798, -2), (key1573, 1), (key1790, 1), (key1296, 1), (key1798, 1), (key1302, 1), (key1596, 1), (key1813, 2), (key1316, 2), (key1825, 2), (key1424, -1), (key1817, -1), (key1316, -1), (key1825, -1), (key1329, -1), (key1447, -1), (key1655, -1), (key1839, -1), (key1337, -1), (key1844, -1), (key1339, -1), (key1667, -1), (key1455, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, 1), (key1466, 1)]

theorem rawRowCheck3706 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form0 = rawRow3706 := by decide +kernel

def row3706 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

theorem rowCheck3706 : row3706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3706 := by decide +kernel

theorem rowEval3706 (x : Key → ℝ) : Integer.Sparse.eval row3706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck3706, Integer.Sparse.eval_collectBalanced, rawRowCheck3706]

def rawRow3707 : Integer.Sparse Key := [(key1788, -2), (key1798, -2), (key1296, -2), (key1790, 1), (key1573, 1), (key1798, 1), (key1296, 1), (key1596, 1), (key1302, 1), (key1813, 2), (key1825, 2), (key1316, 2), (key1817, -1), (key1424, -1), (key1825, -1), (key1316, -1), (key1447, -1), (key1329, -1), (key1839, -1), (key1655, -1), (key1844, -1), (key1337, -1), (key1667, -1), (key1339, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1337, 1), (key1466, 1), (key1345, 1)]

theorem rawRowCheck3707 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form0 = rawRow3707 := by decide +kernel

def row3707 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

theorem rowCheck3707 : row3707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3707 := by decide +kernel

theorem rowEval3707 (x : Key → ℝ) : Integer.Sparse.eval row3707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3707, Integer.Sparse.eval_collectBalanced, rawRowCheck3707]

def rawRow3708 : Integer.Sparse Key := [(key1798, -2), (key1296, -2), (key1788, -2), (key1596, 1), (key1798, 1), (key1302, 1), (key1790, 1), (key1296, 1), (key1573, 1), (key1825, 2), (key1316, 2), (key1813, 2), (key1447, -1), (key1825, -1), (key1329, -1), (key1817, -1), (key1316, -1), (key1424, -1), (key1667, -1), (key1844, -1), (key1339, -1), (key1839, -1), (key1337, -1), (key1655, -1), (key1466, 1), (key1844, 1), (key1345, 1), (key1841, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck3708 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form0 = rawRow3708 := by decide +kernel

def row3708 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

theorem rowCheck3708 : row3708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3708 := by decide +kernel

theorem rowEval3708 (x : Key → ℝ) : Integer.Sparse.eval row3708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3708, Integer.Sparse.eval_collectBalanced, rawRowCheck3708]

def rawRow3709 : Integer.Sparse Key := [(key1798, -2), (key1788, -2), (key1296, -2), (key1798, 1), (key1596, 1), (key1790, 1), (key1302, 1), (key1573, 1), (key1296, 1), (key1825, 2), (key1813, 2), (key1316, 2), (key1825, -1), (key1447, -1), (key1817, -1), (key1329, -1), (key1424, -1), (key1316, -1), (key1844, -1), (key1667, -1), (key1839, -1), (key1339, -1), (key1655, -1), (key1337, -1), (key1844, 1), (key1466, 1), (key1841, 1), (key1345, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck3709 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form0 = rawRow3709 := by decide +kernel

def row3709 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

theorem rowCheck3709 : row3709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3709 := by decide +kernel

theorem rowEval3709 (x : Key → ℝ) : Integer.Sparse.eval row3709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck3709, Integer.Sparse.eval_collectBalanced, rawRowCheck3709]

def rawRow3710 : Integer.Sparse Key := [(key1302, -2), (key1790, -2), (key1790, -2), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1329, 2), (key1817, 2), (key1817, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1345, -1), (key1345, -1), (key1659, -1), (key1659, -1), (key1841, -1), (key1841, -1), (key1339, 1), (key1339, 1), (key1457, 1), (key1457, 1), (key1839, 1), (key1839, 1)]

theorem rawRowCheck3710 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow3710 := by decide +kernel

def row3710 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

theorem rowCheck3710 : row3710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3710 := by decide +kernel

theorem rowEval3710 (x : Key → ℝ) : Integer.Sparse.eval row3710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3710, Integer.Sparse.eval_collectBalanced, rawRowCheck3710]

def rawRow3711 : Integer.Sparse Key := [(key1790, -2), (key1302, -2), (key1790, -2), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1817, 2), (key1329, 2), (key1817, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1659, -1), (key1841, -1), (key1345, -1), (key1841, -1), (key1345, -1), (key1659, -1), (key1457, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1457, 1)]

theorem rawRowCheck3711 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow3711 := by decide +kernel

def row3711 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

theorem rowCheck3711 : row3711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3711 := by decide +kernel

theorem rowEval3711 (x : Key → ℝ) : Integer.Sparse.eval row3711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck3711, Integer.Sparse.eval_collectBalanced, rawRowCheck3711]

end MUB6.Certificate.GramRows

end OAI
