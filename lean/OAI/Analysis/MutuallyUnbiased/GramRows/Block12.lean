import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow480 : Integer.Sparse Key := [(key2748, -2), (key2738, 1), (key2748, 1), (key2729, 2), (key2674, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key2961, 2), (key2951, -1), (key2961, -1), (key2832, -2), (key2619, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2616, -1), (key2829, -1), (key2984, -2), (key2939, 1), (key2984, 1), (key2905, 2), (key2649, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2632, 1), (key2870, 1), (key2977, 1), (key2992, 1), (key2944, -1), (key2992, -1), (key2898, -1), (key2913, -1), (key2654, 1), (key2913, 1), (key2796, 1), (key2883, 1), (key2642, -1), (key2883, -1)]

theorem rawRowCheck480 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow480 := by decide +kernel

def row480 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck480 : row480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow480 := by decide +kernel

theorem rowEval480 (x : Key → ℝ) : Integer.Sparse.eval row480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck480, Integer.Sparse.eval_collectBalanced, rawRowCheck480]

def rawRow481 : Integer.Sparse Key := [(key2748, -2), (key2748, 1), (key2738, 1), (key2729, 2), (key2729, -1), (key2674, -1), (key2726, -1), (key2706, -1), (key2726, 1), (key2671, 1), (key2961, 2), (key2961, -1), (key2951, -1), (key2832, -2), (key2832, 1), (key2619, 1), (key2829, 1), (key2809, 1), (key2829, -1), (key2616, -1), (key2984, -2), (key2984, 1), (key2939, 1), (key2905, 2), (key2905, -1), (key2649, -1), (key2870, -1), (key2786, -1), (key2870, 1), (key2632, 1), (key2992, 1), (key2977, 1), (key2992, -1), (key2944, -1), (key2913, -1), (key2898, -1), (key2913, 1), (key2654, 1), (key2883, 1), (key2796, 1), (key2883, -1), (key2642, -1)]

theorem rawRowCheck481 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow481 := by decide +kernel

def row481 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck481 : row481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow481 := by decide +kernel

theorem rowEval481 (x : Key → ℝ) : Integer.Sparse.eval row481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck481, Integer.Sparse.eval_collectBalanced, rawRowCheck481]

def rawRow482 : Integer.Sparse Key := [(key2786, -2), (key2794, 1), (key2796, 1), (key2809, 2), (key2860, -1), (key2898, -1), (key2829, -1), (key2832, -1), (key2870, 1), (key2905, 1), (key2632, 2), (key2640, -1), (key2642, -1), (key2706, -2), (key2860, 1), (key2977, 1), (key2726, 1), (key2729, 1), (key2870, -1), (key2984, -1), (key2616, -2), (key2640, 1), (key2654, 1), (key2671, 2), (key2794, -1), (key2944, -1), (key2726, -1), (key2748, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2619, 1), (key2632, -1), (key2649, -1), (key2671, -1), (key2674, -1), (key2786, 1), (key2939, 1), (key2706, 1), (key2738, 1), (key2809, -1), (key2951, -1)]

theorem rawRowCheck482 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow482 := by decide +kernel

def row482 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck482 : row482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow482 := by decide +kernel

theorem rowEval482 (x : Key → ℝ) : Integer.Sparse.eval row482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck482, Integer.Sparse.eval_collectBalanced, rawRowCheck482]

def rawRow483 : Integer.Sparse Key := [(key2786, -2), (key2796, 1), (key2794, 1), (key2809, 2), (key2898, -1), (key2860, -1), (key2832, -1), (key2829, -1), (key2905, 1), (key2870, 1), (key2632, 2), (key2642, -1), (key2640, -1), (key2706, -2), (key2977, 1), (key2860, 1), (key2729, 1), (key2726, 1), (key2984, -1), (key2870, -1), (key2616, -2), (key2654, 1), (key2640, 1), (key2671, 2), (key2944, -1), (key2794, -1), (key2748, -1), (key2726, -1), (key2961, 1), (key2829, 1), (key2619, 1), (key2616, 1), (key2649, -1), (key2632, -1), (key2674, -1), (key2671, -1), (key2939, 1), (key2786, 1), (key2738, 1), (key2706, 1), (key2951, -1), (key2809, -1)]

theorem rawRowCheck483 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow483 := by decide +kernel

def row483 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck483 : row483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow483 := by decide +kernel

theorem rowEval483 (x : Key → ℝ) : Integer.Sparse.eval row483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck483, Integer.Sparse.eval_collectBalanced, rawRowCheck483]

def rawRow484 : Integer.Sparse Key := [(key2796, -2), (key2786, 1), (key2794, 1), (key2898, 2), (key2809, -1), (key2860, -1), (key2905, -1), (key2913, -1), (key2832, 1), (key2883, 1), (key2642, 2), (key2632, -1), (key2640, -1), (key2977, -2), (key2706, 1), (key2860, 1), (key2984, 1), (key2992, 1), (key2729, -1), (key2883, -1), (key2654, -2), (key2616, 1), (key2640, 1), (key2944, 2), (key2671, -1), (key2794, -1), (key2961, -1), (key2992, -1), (key2748, 1), (key2913, 1), (key2649, 1), (key2654, 1), (key2619, -1), (key2642, -1), (key2939, -1), (key2944, -1), (key2674, 1), (key2796, 1), (key2951, 1), (key2977, 1), (key2738, -1), (key2898, -1)]

theorem rawRowCheck484 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form1 = rawRow484 := by decide +kernel

def row484 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck484 : row484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow484 := by decide +kernel

theorem rowEval484 (x : Key → ℝ) : Integer.Sparse.eval row484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck484, Integer.Sparse.eval_collectBalanced, rawRowCheck484]

def rawRow485 : Integer.Sparse Key := [(key2796, -2), (key2794, 1), (key2786, 1), (key2898, 2), (key2860, -1), (key2809, -1), (key2913, -1), (key2905, -1), (key2883, 1), (key2832, 1), (key2642, 2), (key2640, -1), (key2632, -1), (key2977, -2), (key2860, 1), (key2706, 1), (key2992, 1), (key2984, 1), (key2883, -1), (key2729, -1), (key2654, -2), (key2640, 1), (key2616, 1), (key2944, 2), (key2794, -1), (key2671, -1), (key2992, -1), (key2961, -1), (key2913, 1), (key2748, 1), (key2654, 1), (key2649, 1), (key2642, -1), (key2619, -1), (key2944, -1), (key2939, -1), (key2796, 1), (key2674, 1), (key2977, 1), (key2951, 1), (key2898, -1), (key2738, -1)]

theorem rawRowCheck485 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form1 = rawRow485 := by decide +kernel

def row485 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck485 : row485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow485 := by decide +kernel

theorem rowEval485 (x : Key → ℝ) : Integer.Sparse.eval row485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck485, Integer.Sparse.eval_collectBalanced, rawRowCheck485]

def rawRow486 : Integer.Sparse Key := [(key2809, -2), (key2829, 1), (key2832, 1), (key2786, 2), (key2870, -1), (key2905, -1), (key2794, -1), (key2796, -1), (key2860, 1), (key2898, 1), (key2706, 2), (key2726, -1), (key2729, -1), (key2632, -2), (key2870, 1), (key2984, 1), (key2640, 1), (key2642, 1), (key2860, -1), (key2977, -1), (key2671, -2), (key2726, 1), (key2748, 1), (key2616, 2), (key2829, -1), (key2961, -1), (key2640, -1), (key2654, -1), (key2794, 1), (key2944, 1), (key2671, 1), (key2674, 1), (key2706, -1), (key2738, -1), (key2616, -1), (key2619, -1), (key2809, 1), (key2951, 1), (key2632, 1), (key2649, 1), (key2786, -1), (key2939, -1)]

theorem rawRowCheck486 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow486 := by decide +kernel

def row486 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck486 : row486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow486 := by decide +kernel

theorem rowEval486 (x : Key → ℝ) : Integer.Sparse.eval row486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck486, Integer.Sparse.eval_collectBalanced, rawRowCheck486]

def rawRow487 : Integer.Sparse Key := [(key2809, -2), (key2832, 1), (key2829, 1), (key2786, 2), (key2905, -1), (key2870, -1), (key2796, -1), (key2794, -1), (key2898, 1), (key2860, 1), (key2706, 2), (key2729, -1), (key2726, -1), (key2632, -2), (key2984, 1), (key2870, 1), (key2642, 1), (key2640, 1), (key2977, -1), (key2860, -1), (key2671, -2), (key2748, 1), (key2726, 1), (key2616, 2), (key2961, -1), (key2829, -1), (key2654, -1), (key2640, -1), (key2944, 1), (key2794, 1), (key2674, 1), (key2671, 1), (key2738, -1), (key2706, -1), (key2619, -1), (key2616, -1), (key2951, 1), (key2809, 1), (key2649, 1), (key2632, 1), (key2939, -1), (key2786, -1)]

theorem rawRowCheck487 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow487 := by decide +kernel

def row487 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck487 : row487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow487 := by decide +kernel

theorem rowEval487 (x : Key → ℝ) : Integer.Sparse.eval row487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck487, Integer.Sparse.eval_collectBalanced, rawRowCheck487]

def rawRow488 : Integer.Sparse Key := [(key2832, -2), (key2809, 1), (key2829, 1), (key2905, 2), (key2786, -1), (key2870, -1), (key2898, -1), (key2913, -1), (key2796, 1), (key2883, 1), (key2729, 2), (key2706, -1), (key2726, -1), (key2984, -2), (key2632, 1), (key2870, 1), (key2977, 1), (key2992, 1), (key2642, -1), (key2883, -1), (key2748, -2), (key2671, 1), (key2726, 1), (key2961, 2), (key2616, -1), (key2829, -1), (key2944, -1), (key2992, -1), (key2654, 1), (key2913, 1), (key2738, 1), (key2748, 1), (key2674, -1), (key2729, -1), (key2951, -1), (key2961, -1), (key2619, 1), (key2832, 1), (key2939, 1), (key2984, 1), (key2649, -1), (key2905, -1)]

theorem rawRowCheck488 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form1 = rawRow488 := by decide +kernel

def row488 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck488 : row488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow488 := by decide +kernel

theorem rowEval488 (x : Key → ℝ) : Integer.Sparse.eval row488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck488, Integer.Sparse.eval_collectBalanced, rawRowCheck488]

def rawRow489 : Integer.Sparse Key := [(key2832, -2), (key2829, 1), (key2809, 1), (key2905, 2), (key2870, -1), (key2786, -1), (key2913, -1), (key2898, -1), (key2883, 1), (key2796, 1), (key2729, 2), (key2726, -1), (key2706, -1), (key2984, -2), (key2870, 1), (key2632, 1), (key2992, 1), (key2977, 1), (key2883, -1), (key2642, -1), (key2748, -2), (key2726, 1), (key2671, 1), (key2961, 2), (key2829, -1), (key2616, -1), (key2992, -1), (key2944, -1), (key2913, 1), (key2654, 1), (key2748, 1), (key2738, 1), (key2729, -1), (key2674, -1), (key2961, -1), (key2951, -1), (key2832, 1), (key2619, 1), (key2984, 1), (key2939, 1), (key2905, -1), (key2649, -1)]

theorem rawRowCheck489 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form1 = rawRow489 := by decide +kernel

def row489 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck489 : row489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow489 := by decide +kernel

theorem rowEval489 (x : Key → ℝ) : Integer.Sparse.eval row489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck489, Integer.Sparse.eval_collectBalanced, rawRowCheck489]

def rawRow490 : Integer.Sparse Key := [(key2898, -2), (key2905, 1), (key2913, 1), (key2796, 2), (key2832, -1), (key2883, -1), (key2786, -1), (key2794, -1), (key2809, 1), (key2860, 1), (key2977, 2), (key2984, -1), (key2992, -1), (key2642, -2), (key2729, 1), (key2883, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2860, -1), (key2944, -2), (key2961, 1), (key2992, 1), (key2654, 2), (key2748, -1), (key2913, -1), (key2616, -1), (key2640, -1), (key2671, 1), (key2794, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2977, -1), (key2649, -1), (key2654, -1), (key2738, 1), (key2898, 1), (key2619, 1), (key2642, 1), (key2674, -1), (key2796, -1)]

theorem rawRowCheck490 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form1 = rawRow490 := by decide +kernel

def row490 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck490 : row490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow490 := by decide +kernel

theorem rowEval490 (x : Key → ℝ) : Integer.Sparse.eval row490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck490, Integer.Sparse.eval_collectBalanced, rawRowCheck490]

def rawRow491 : Integer.Sparse Key := [(key2898, -2), (key2913, 1), (key2905, 1), (key2796, 2), (key2883, -1), (key2832, -1), (key2794, -1), (key2786, -1), (key2860, 1), (key2809, 1), (key2977, 2), (key2992, -1), (key2984, -1), (key2642, -2), (key2883, 1), (key2729, 1), (key2640, 1), (key2632, 1), (key2860, -1), (key2706, -1), (key2944, -2), (key2992, 1), (key2961, 1), (key2654, 2), (key2913, -1), (key2748, -1), (key2640, -1), (key2616, -1), (key2794, 1), (key2671, 1), (key2944, 1), (key2939, 1), (key2977, -1), (key2951, -1), (key2654, -1), (key2649, -1), (key2898, 1), (key2738, 1), (key2642, 1), (key2619, 1), (key2796, -1), (key2674, -1)]

theorem rawRowCheck491 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form1 = rawRow491 := by decide +kernel

def row491 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck491 : row491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow491 := by decide +kernel

theorem rowEval491 (x : Key → ℝ) : Integer.Sparse.eval row491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck491, Integer.Sparse.eval_collectBalanced, rawRowCheck491]

def rawRow492 : Integer.Sparse Key := [(key2905, -2), (key2898, 1), (key2913, 1), (key2832, 2), (key2796, -1), (key2883, -1), (key2809, -1), (key2829, -1), (key2786, 1), (key2870, 1), (key2984, 2), (key2977, -1), (key2992, -1), (key2729, -2), (key2642, 1), (key2883, 1), (key2706, 1), (key2726, 1), (key2632, -1), (key2870, -1), (key2961, -2), (key2944, 1), (key2992, 1), (key2748, 2), (key2654, -1), (key2913, -1), (key2671, -1), (key2726, -1), (key2616, 1), (key2829, 1), (key2951, 1), (key2961, 1), (key2939, -1), (key2984, -1), (key2738, -1), (key2748, -1), (key2649, 1), (key2905, 1), (key2674, 1), (key2729, 1), (key2619, -1), (key2832, -1)]

theorem rawRowCheck492 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form1 = rawRow492 := by decide +kernel

def row492 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck492 : row492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow492 := by decide +kernel

theorem rowEval492 (x : Key → ℝ) : Integer.Sparse.eval row492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck492, Integer.Sparse.eval_collectBalanced, rawRowCheck492]

def rawRow493 : Integer.Sparse Key := [(key2905, -2), (key2913, 1), (key2898, 1), (key2832, 2), (key2883, -1), (key2796, -1), (key2829, -1), (key2809, -1), (key2870, 1), (key2786, 1), (key2984, 2), (key2992, -1), (key2977, -1), (key2729, -2), (key2883, 1), (key2642, 1), (key2726, 1), (key2706, 1), (key2870, -1), (key2632, -1), (key2961, -2), (key2992, 1), (key2944, 1), (key2748, 2), (key2913, -1), (key2654, -1), (key2726, -1), (key2671, -1), (key2829, 1), (key2616, 1), (key2961, 1), (key2951, 1), (key2984, -1), (key2939, -1), (key2748, -1), (key2738, -1), (key2905, 1), (key2649, 1), (key2729, 1), (key2674, 1), (key2832, -1), (key2619, -1)]

theorem rawRowCheck493 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form1 = rawRow493 := by decide +kernel

def row493 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck493 : row493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow493 := by decide +kernel

theorem rowEval493 (x : Key → ℝ) : Integer.Sparse.eval row493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck493, Integer.Sparse.eval_collectBalanced, rawRowCheck493]

def rawRow494 : Integer.Sparse Key := [(key2939, -2), (key2944, 1), (key2944, 1), (key2951, 2), (key2977, -1), (key2977, -1), (key2961, -1), (key2961, -1), (key2984, 1), (key2984, 1), (key2649, 2), (key2654, -1), (key2654, -1), (key2738, -2), (key2898, 1), (key2898, 1), (key2748, 1), (key2748, 1), (key2905, -1), (key2905, -1), (key2619, -2), (key2642, 1), (key2642, 1), (key2674, 2), (key2796, -1), (key2796, -1), (key2729, -1), (key2729, -1), (key2832, 1), (key2832, 1), (key2616, 1), (key2616, 1), (key2632, -1), (key2632, -1), (key2671, -1), (key2671, -1), (key2786, 1), (key2786, 1), (key2706, 1), (key2706, 1), (key2809, -1), (key2809, -1)]

theorem rawRowCheck494 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form1 = rawRow494 := by decide +kernel

def row494 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck494 : row494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow494 := by decide +kernel

theorem rowEval494 (x : Key → ℝ) : Integer.Sparse.eval row494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck494, Integer.Sparse.eval_collectBalanced, rawRowCheck494]

def rawRow495 : Integer.Sparse Key := [(key2944, -2), (key2939, 1), (key2944, 1), (key2977, 2), (key2951, -1), (key2977, -1), (key2984, -1), (key2992, -1), (key2961, 1), (key2992, 1), (key2654, 2), (key2649, -1), (key2654, -1), (key2898, -2), (key2738, 1), (key2898, 1), (key2905, 1), (key2913, 1), (key2748, -1), (key2913, -1), (key2642, -2), (key2619, 1), (key2642, 1), (key2796, 2), (key2674, -1), (key2796, -1), (key2832, -1), (key2883, -1), (key2729, 1), (key2883, 1), (key2632, 1), (key2640, 1), (key2616, -1), (key2640, -1), (key2786, -1), (key2794, -1), (key2671, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2706, -1), (key2860, -1)]

theorem rawRowCheck495 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form1 = rawRow495 := by decide +kernel

def row495 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck495 : row495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow495 := by decide +kernel

theorem rowEval495 (x : Key → ℝ) : Integer.Sparse.eval row495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck495, Integer.Sparse.eval_collectBalanced, rawRowCheck495]

def rawRow496 : Integer.Sparse Key := [(key2944, -2), (key2944, 1), (key2939, 1), (key2977, 2), (key2977, -1), (key2951, -1), (key2992, -1), (key2984, -1), (key2992, 1), (key2961, 1), (key2654, 2), (key2654, -1), (key2649, -1), (key2898, -2), (key2898, 1), (key2738, 1), (key2913, 1), (key2905, 1), (key2913, -1), (key2748, -1), (key2642, -2), (key2642, 1), (key2619, 1), (key2796, 2), (key2796, -1), (key2674, -1), (key2883, -1), (key2832, -1), (key2883, 1), (key2729, 1), (key2640, 1), (key2632, 1), (key2640, -1), (key2616, -1), (key2794, -1), (key2786, -1), (key2794, 1), (key2671, 1), (key2860, 1), (key2809, 1), (key2860, -1), (key2706, -1)]

theorem rawRowCheck496 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form1 = rawRow496 := by decide +kernel

def row496 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck496 : row496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow496 := by decide +kernel

theorem rowEval496 (x : Key → ℝ) : Integer.Sparse.eval row496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck496, Integer.Sparse.eval_collectBalanced, rawRowCheck496]

def rawRow497 : Integer.Sparse Key := [(key2951, -2), (key2961, 1), (key2961, 1), (key2939, 2), (key2984, -1), (key2984, -1), (key2944, -1), (key2944, -1), (key2977, 1), (key2977, 1), (key2738, 2), (key2748, -1), (key2748, -1), (key2649, -2), (key2905, 1), (key2905, 1), (key2654, 1), (key2654, 1), (key2898, -1), (key2898, -1), (key2674, -2), (key2729, 1), (key2729, 1), (key2619, 2), (key2832, -1), (key2832, -1), (key2642, -1), (key2642, -1), (key2796, 1), (key2796, 1), (key2671, 1), (key2671, 1), (key2706, -1), (key2706, -1), (key2616, -1), (key2616, -1), (key2809, 1), (key2809, 1), (key2632, 1), (key2632, 1), (key2786, -1), (key2786, -1)]

theorem rawRowCheck497 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow497 := by decide +kernel

def row497 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck497 : row497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow497 := by decide +kernel

theorem rowEval497 (x : Key → ℝ) : Integer.Sparse.eval row497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck497, Integer.Sparse.eval_collectBalanced, rawRowCheck497]

def rawRow498 : Integer.Sparse Key := [(key2961, -2), (key2951, 1), (key2961, 1), (key2984, 2), (key2939, -1), (key2984, -1), (key2977, -1), (key2992, -1), (key2944, 1), (key2992, 1), (key2748, 2), (key2738, -1), (key2748, -1), (key2905, -2), (key2649, 1), (key2905, 1), (key2898, 1), (key2913, 1), (key2654, -1), (key2913, -1), (key2729, -2), (key2674, 1), (key2729, 1), (key2832, 2), (key2619, -1), (key2832, -1), (key2796, -1), (key2883, -1), (key2642, 1), (key2883, 1), (key2706, 1), (key2726, 1), (key2671, -1), (key2726, -1), (key2809, -1), (key2829, -1), (key2616, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2632, -1), (key2870, -1)]

theorem rawRowCheck498 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form1 = rawRow498 := by decide +kernel

def row498 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck498 : row498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow498 := by decide +kernel

theorem rowEval498 (x : Key → ℝ) : Integer.Sparse.eval row498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck498, Integer.Sparse.eval_collectBalanced, rawRowCheck498]

def rawRow499 : Integer.Sparse Key := [(key2961, -2), (key2961, 1), (key2951, 1), (key2984, 2), (key2984, -1), (key2939, -1), (key2992, -1), (key2977, -1), (key2992, 1), (key2944, 1), (key2748, 2), (key2748, -1), (key2738, -1), (key2905, -2), (key2905, 1), (key2649, 1), (key2913, 1), (key2898, 1), (key2913, -1), (key2654, -1), (key2729, -2), (key2729, 1), (key2674, 1), (key2832, 2), (key2832, -1), (key2619, -1), (key2883, -1), (key2796, -1), (key2883, 1), (key2642, 1), (key2726, 1), (key2706, 1), (key2726, -1), (key2671, -1), (key2829, -1), (key2809, -1), (key2829, 1), (key2616, 1), (key2870, 1), (key2786, 1), (key2870, -1), (key2632, -1)]

theorem rawRowCheck499 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form1 = rawRow499 := by decide +kernel

def row499 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck499 : row499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow499 := by decide +kernel

theorem rowEval499 (x : Key → ℝ) : Integer.Sparse.eval row499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck499, Integer.Sparse.eval_collectBalanced, rawRowCheck499]

def rawRow500 : Integer.Sparse Key := [(key2977, -2), (key2984, 1), (key2992, 1), (key2944, 2), (key2961, -1), (key2992, -1), (key2939, -1), (key2944, -1), (key2951, 1), (key2977, 1), (key2898, 2), (key2905, -1), (key2913, -1), (key2654, -2), (key2748, 1), (key2913, 1), (key2649, 1), (key2654, 1), (key2738, -1), (key2898, -1), (key2796, -2), (key2832, 1), (key2883, 1), (key2642, 2), (key2729, -1), (key2883, -1), (key2619, -1), (key2642, -1), (key2674, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2860, -1), (key2632, -1), (key2640, -1), (key2706, 1), (key2860, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2794, -1)]

theorem rawRowCheck500 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form1 = rawRow500 := by decide +kernel

def row500 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck500 : row500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow500 := by decide +kernel

theorem rowEval500 (x : Key → ℝ) : Integer.Sparse.eval row500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck500, Integer.Sparse.eval_collectBalanced, rawRowCheck500]

def rawRow501 : Integer.Sparse Key := [(key2977, -2), (key2992, 1), (key2984, 1), (key2944, 2), (key2992, -1), (key2961, -1), (key2944, -1), (key2939, -1), (key2977, 1), (key2951, 1), (key2898, 2), (key2913, -1), (key2905, -1), (key2654, -2), (key2913, 1), (key2748, 1), (key2654, 1), (key2649, 1), (key2898, -1), (key2738, -1), (key2796, -2), (key2883, 1), (key2832, 1), (key2642, 2), (key2883, -1), (key2729, -1), (key2642, -1), (key2619, -1), (key2796, 1), (key2674, 1), (key2794, 1), (key2786, 1), (key2860, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2860, 1), (key2706, 1), (key2640, 1), (key2616, 1), (key2794, -1), (key2671, -1)]

theorem rawRowCheck501 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form1 = rawRow501 := by decide +kernel

def row501 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck501 : row501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow501 := by decide +kernel

theorem rowEval501 (x : Key → ℝ) : Integer.Sparse.eval row501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck501, Integer.Sparse.eval_collectBalanced, rawRowCheck501]

def rawRow502 : Integer.Sparse Key := [(key2984, -2), (key2977, 1), (key2992, 1), (key2961, 2), (key2944, -1), (key2992, -1), (key2951, -1), (key2961, -1), (key2939, 1), (key2984, 1), (key2905, 2), (key2898, -1), (key2913, -1), (key2748, -2), (key2654, 1), (key2913, 1), (key2738, 1), (key2748, 1), (key2649, -1), (key2905, -1), (key2832, -2), (key2796, 1), (key2883, 1), (key2729, 2), (key2642, -1), (key2883, -1), (key2674, -1), (key2729, -1), (key2619, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2786, -1), (key2870, -1), (key2706, -1), (key2726, -1), (key2632, 1), (key2870, 1), (key2671, 1), (key2726, 1), (key2616, -1), (key2829, -1)]

theorem rawRowCheck502 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form1 = rawRow502 := by decide +kernel

def row502 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck502 : row502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow502 := by decide +kernel

theorem rowEval502 (x : Key → ℝ) : Integer.Sparse.eval row502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck502, Integer.Sparse.eval_collectBalanced, rawRowCheck502]

def rawRow503 : Integer.Sparse Key := [(key2984, -2), (key2992, 1), (key2977, 1), (key2961, 2), (key2992, -1), (key2944, -1), (key2961, -1), (key2951, -1), (key2984, 1), (key2939, 1), (key2905, 2), (key2913, -1), (key2898, -1), (key2748, -2), (key2913, 1), (key2654, 1), (key2748, 1), (key2738, 1), (key2905, -1), (key2649, -1), (key2832, -2), (key2883, 1), (key2796, 1), (key2729, 2), (key2883, -1), (key2642, -1), (key2729, -1), (key2674, -1), (key2832, 1), (key2619, 1), (key2829, 1), (key2809, 1), (key2870, -1), (key2786, -1), (key2726, -1), (key2706, -1), (key2870, 1), (key2632, 1), (key2726, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

theorem rawRowCheck503 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form1 = rawRow503 := by decide +kernel

def row503 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck503 : row503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow503 := by decide +kernel

theorem rowEval503 (x : Key → ℝ) : Integer.Sparse.eval row503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck503, Integer.Sparse.eval_collectBalanced, rawRowCheck503]

def rawRow504 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2613, 2), (key2625, 1), (key2629, 1), (key2629, -1), (key2647, -1), (key2637, -2), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2668, -2), (key2779, -1), (key2783, -1), (key2783, 1), (key2937, 1), (key2791, 2), (key2791, -1), (key2942, -1), (key2699, -1), (key2703, -1), (key2703, 1), (key2736, 1), (key2802, 1), (key2806, 1), (key2806, -1), (key2949, -1), (key2857, -1), (key2896, -1), (key2857, 1), (key2975, 1), (key2723, 2), (key2723, -1), (key2746, -1), (key2826, -2), (key2826, 1), (key2959, 1), (key2867, 1), (key2903, 1), (key2867, -1), (key2982, -1)]

theorem rawRowCheck504 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form2 = rawRow504 := by decide +kernel

def row504 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck504 : row504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow504 := by decide +kernel

theorem rowEval504 (x : Key → ℝ) : Integer.Sparse.eval row504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck504, Integer.Sparse.eval_collectBalanced, rawRowCheck504]

def rawRow505 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2613, 2), (key2629, 1), (key2625, 1), (key2647, -1), (key2629, -1), (key2637, -2), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2668, -2), (key2783, -1), (key2779, -1), (key2937, 1), (key2783, 1), (key2791, 2), (key2942, -1), (key2791, -1), (key2703, -1), (key2699, -1), (key2736, 1), (key2703, 1), (key2806, 1), (key2802, 1), (key2949, -1), (key2806, -1), (key2896, -1), (key2857, -1), (key2975, 1), (key2857, 1), (key2723, 2), (key2746, -1), (key2723, -1), (key2826, -2), (key2959, 1), (key2826, 1), (key2903, 1), (key2867, 1), (key2982, -1), (key2867, -1)]

theorem rawRowCheck505 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form2 = rawRow505 := by decide +kernel

def row505 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck505 : row505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow505 := by decide +kernel

theorem rowEval505 (x : Key → ℝ) : Integer.Sparse.eval row505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck505, Integer.Sparse.eval_collectBalanced, rawRowCheck505]

def rawRow506 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2609, 2), (key2647, 1), (key2647, 1), (key2625, -1), (key2625, -1), (key2652, -2), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2664, -2), (key2937, -1), (key2937, -1), (key2779, 1), (key2779, 1), (key2942, 2), (key2791, -1), (key2791, -1), (key2736, -1), (key2736, -1), (key2699, 1), (key2699, 1), (key2949, 1), (key2949, 1), (key2802, -1), (key2802, -1), (key2975, -1), (key2975, -1), (key2896, 1), (key2896, 1), (key2746, 2), (key2723, -1), (key2723, -1), (key2959, -2), (key2826, 1), (key2826, 1), (key2982, 1), (key2982, 1), (key2903, -1), (key2903, -1)]

theorem rawRowCheck506 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form2 = rawRow506 := by decide +kernel

def row506 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck506 : row506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow506 := by decide +kernel

theorem rowEval506 (x : Key → ℝ) : Integer.Sparse.eval row506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck506, Integer.Sparse.eval_collectBalanced, rawRowCheck506]

def rawRow507 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2637, 2), (key2609, 1), (key2613, 1), (key2637, -1), (key2652, -1), (key2613, -2), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2791, -2), (key2664, -1), (key2668, -1), (key2791, 1), (key2942, 1), (key2668, 2), (key2783, -1), (key2937, -1), (key2802, -1), (key2806, -1), (key2857, 1), (key2896, 1), (key2699, 1), (key2703, 1), (key2857, -1), (key2975, -1), (key2703, -1), (key2736, -1), (key2806, 1), (key2949, 1), (key2826, 2), (key2867, -1), (key2903, -1), (key2723, -2), (key2867, 1), (key2982, 1), (key2723, 1), (key2746, 1), (key2826, -1), (key2959, -1)]

theorem rawRowCheck507 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form2 = rawRow507 := by decide +kernel

def row507 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck507 : row507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow507 := by decide +kernel

theorem rowEval507 (x : Key → ℝ) : Integer.Sparse.eval row507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck507, Integer.Sparse.eval_collectBalanced, rawRowCheck507]

def rawRow508 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2637, 2), (key2613, 1), (key2609, 1), (key2652, -1), (key2637, -1), (key2613, -2), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2791, -2), (key2668, -1), (key2664, -1), (key2942, 1), (key2791, 1), (key2668, 2), (key2937, -1), (key2783, -1), (key2806, -1), (key2802, -1), (key2896, 1), (key2857, 1), (key2703, 1), (key2699, 1), (key2975, -1), (key2857, -1), (key2736, -1), (key2703, -1), (key2949, 1), (key2806, 1), (key2826, 2), (key2903, -1), (key2867, -1), (key2723, -2), (key2982, 1), (key2867, 1), (key2746, 1), (key2723, 1), (key2959, -1), (key2826, -1)]

theorem rawRowCheck508 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form2 = rawRow508 := by decide +kernel

def row508 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck508 : row508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow508 := by decide +kernel

theorem rowEval508 (x : Key → ℝ) : Integer.Sparse.eval row508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck508, Integer.Sparse.eval_collectBalanced, rawRowCheck508]

def rawRow509 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2625, 2), (key2647, 1), (key2652, 1), (key2609, -1), (key2625, -1), (key2647, -2), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2779, -2), (key2937, -1), (key2942, -1), (key2664, 1), (key2779, 1), (key2937, 2), (key2668, -1), (key2783, -1), (key2894, -1), (key2896, -1), (key2802, 1), (key2852, 1), (key2973, 1), (key2975, 1), (key2699, -1), (key2852, -1), (key2949, -1), (key2973, -1), (key2736, 1), (key2894, 1), (key2903, 2), (key2826, -1), (key2867, -1), (key2982, -2), (key2723, 1), (key2867, 1), (key2959, 1), (key2982, 1), (key2746, -1), (key2903, -1)]

theorem rawRowCheck509 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form2 = rawRow509 := by decide +kernel

def row509 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck509 : row509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow509 := by decide +kernel

theorem rowEval509 (x : Key → ℝ) : Integer.Sparse.eval row509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck509, Integer.Sparse.eval_collectBalanced, rawRowCheck509]

def rawRow510 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2625, 2), (key2652, 1), (key2647, 1), (key2625, -1), (key2609, -1), (key2647, -2), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2779, -2), (key2942, -1), (key2937, -1), (key2779, 1), (key2664, 1), (key2937, 2), (key2783, -1), (key2668, -1), (key2896, -1), (key2894, -1), (key2852, 1), (key2802, 1), (key2975, 1), (key2973, 1), (key2852, -1), (key2699, -1), (key2973, -1), (key2949, -1), (key2894, 1), (key2736, 1), (key2903, 2), (key2867, -1), (key2826, -1), (key2982, -2), (key2867, 1), (key2723, 1), (key2982, 1), (key2959, 1), (key2903, -1), (key2746, -1)]

theorem rawRowCheck510 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form2 = rawRow510 := by decide +kernel

def row510 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck510 : row510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow510 := by decide +kernel

theorem rowEval510 (x : Key → ℝ) : Integer.Sparse.eval row510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck510, Integer.Sparse.eval_collectBalanced, rawRowCheck510]

def rawRow511 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2652, 2), (key2613, 1), (key2613, 1), (key2637, -1), (key2637, -1), (key2609, -2), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2942, -2), (key2668, -1), (key2668, -1), (key2791, 1), (key2791, 1), (key2664, 2), (key2779, -1), (key2779, -1), (key2949, -1), (key2949, -1), (key2975, 1), (key2975, 1), (key2736, 1), (key2736, 1), (key2896, -1), (key2896, -1), (key2699, -1), (key2699, -1), (key2802, 1), (key2802, 1), (key2959, 2), (key2982, -1), (key2982, -1), (key2746, -2), (key2903, 1), (key2903, 1), (key2723, 1), (key2723, 1), (key2826, -1), (key2826, -1)]

theorem rawRowCheck511 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form2 = rawRow511 := by decide +kernel

def row511 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck511 : row511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow511 := by decide +kernel

theorem rowEval511 (x : Key → ℝ) : Integer.Sparse.eval row511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck511, Integer.Sparse.eval_collectBalanced, rawRowCheck511]

end MUB6.Certificate.GramRows

end OAI
