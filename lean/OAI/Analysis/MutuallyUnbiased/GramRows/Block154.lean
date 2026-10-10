import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
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

def rawRow16640 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, 1), (key2951, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, -1), (key2984, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2860, 1), (key2977, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2905, 2), (key2748, 2), (key2913, 2), (key2898, -2), (key2654, -2), (key2913, -2)]

theorem rawRowCheck16640 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form15 = rawRow16640 := by decide +kernel

def row16640 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16640 : row16640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16640 := by decide +kernel

theorem rowEval16640 (x : Key → ℝ) : Integer.Sparse.eval row16640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16640, Integer.Sparse.eval_collectBalanced, rawRowCheck16640]

def rawRow16641 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2796, -1), (key2674, -1), (key2786, 2), (key2794, 2), (key2671, 2), (key2951, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2832, 1), (key2619, 1), (key2809, -2), (key2829, -2), (key2616, -2), (key2984, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2883, -1), (key2729, -1), (key2977, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2883, 1), (key2642, 1), (key2905, 2), (key2913, 2), (key2748, 2), (key2898, -2), (key2913, -2), (key2654, -2)]

theorem rawRowCheck16641 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form15 = rawRow16641 := by decide +kernel

def row16641 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16641 : row16641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16641 := by decide +kernel

theorem rowEval16641 (x : Key → ℝ) : Integer.Sparse.eval row16641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16641, Integer.Sparse.eval_collectBalanced, rawRowCheck16641]

def rawRow16642 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2671, -1), (key2786, -1), (key2794, 2), (key2671, 2), (key2786, 2), (key2832, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2616, 1), (key2809, 1), (key2829, -2), (key2616, -2), (key2809, -2), (key2883, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2726, -1), (key2870, -1), (key2883, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2640, 1), (key2860, 1), (key2913, 2), (key2748, 2), (key2905, 2), (key2913, -2), (key2654, -2), (key2898, -2)]

theorem rawRowCheck16642 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form15 = rawRow16642 := by decide +kernel

def row16642 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16642 : row16642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16642 := by decide +kernel

theorem rowEval16642 (x : Key → ℝ) : Integer.Sparse.eval row16642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16642, Integer.Sparse.eval_collectBalanced, rawRowCheck16642]

def rawRow16643 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2939, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2794, 2), (key2786, 2), (key2671, 2), (key2961, 1), (key2832, 1), (key2951, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2829, -2), (key2809, -2), (key2616, -2), (key2992, -1), (key2883, -1), (key2984, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2992, 1), (key2883, 1), (key2977, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2913, 2), (key2905, 2), (key2748, 2), (key2913, -2), (key2898, -2), (key2654, -2)]

theorem rawRowCheck16643 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form15 = rawRow16643 := by decide +kernel

def row16643 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16643 : row16643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16643 := by decide +kernel

theorem rowEval16643 (x : Key → ℝ) : Integer.Sparse.eval row16643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16643, Integer.Sparse.eval_collectBalanced, rawRowCheck16643]

def rawRow16644 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2738, 2), (key2898, 2), (key2898, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2649, -2), (key2905, -2), (key2905, -2), (key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2674, 2), (key2796, 2), (key2796, 2), (key2619, -2), (key2832, -2), (key2832, -2)]

theorem rawRowCheck16644 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form15 = rawRow16644 := by decide +kernel

def row16644 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck16644 : row16644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16644 := by decide +kernel

theorem rowEval16644 (x : Key → ℝ) : Integer.Sparse.eval row16644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16644, Integer.Sparse.eval_collectBalanced, rawRowCheck16644]

def rawRow16645 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2898, 2), (key2738, 2), (key2898, 2), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2905, -2), (key2649, -2), (key2905, -2), (key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, -2), (key2619, -2), (key2832, -2)]

theorem rawRowCheck16645 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form15 = rawRow16645 := by decide +kernel

def row16645 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck16645 : row16645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16645 := by decide +kernel

theorem rowEval16645 (x : Key → ℝ) : Integer.Sparse.eval row16645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16645, Integer.Sparse.eval_collectBalanced, rawRowCheck16645]

def rawRow16646 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2898, 2), (key2898, 2), (key2738, 2), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2905, -2), (key2905, -2), (key2649, -2), (key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2796, 2), (key2796, 2), (key2674, 2), (key2832, -2), (key2832, -2), (key2619, -2)]

theorem rawRowCheck16646 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form15 = rawRow16646 := by decide +kernel

def row16646 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck16646 : row16646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16646 := by decide +kernel

theorem rowEval16646 (x : Key → ℝ) : Integer.Sparse.eval row16646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16646, Integer.Sparse.eval_collectBalanced, rawRowCheck16646]

def rawRow16647 : Integer.Sparse Key := [(key2706, -1), (key2738, -1), (key2809, -1), (key2898, -1), (key2951, -1), (key2977, -1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, 1), (key2649, 1), (key2786, 1), (key2905, 1), (key2939, 1), (key2984, 1), (key2632, -2), (key2786, -2), (key2870, -2), (key2726, -1), (key2748, -1), (key2829, -1), (key2913, -1), (key2961, -1), (key2992, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2913, 1), (key2944, 1), (key2992, 1), (key2729, 2), (key2832, 2), (key2883, 2), (key2642, -2), (key2796, -2), (key2883, -2)]

theorem rawRowCheck16647 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form15 = rawRow16647 := by decide +kernel

def row16647 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16647 : row16647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16647 := by decide +kernel

theorem rowEval16647 (x : Key → ℝ) : Integer.Sparse.eval row16647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16647, Integer.Sparse.eval_collectBalanced, rawRowCheck16647]

def rawRow16648 : Integer.Sparse Key := [(key2738, -1), (key2706, -1), (key2898, -1), (key2809, -1), (key2977, -1), (key2951, -1), (key2706, 2), (key2860, 2), (key2809, 2), (key2649, 1), (key2632, 1), (key2905, 1), (key2786, 1), (key2984, 1), (key2939, 1), (key2632, -2), (key2870, -2), (key2786, -2), (key2748, -1), (key2726, -1), (key2913, -1), (key2829, -1), (key2992, -1), (key2961, -1), (key2654, 1), (key2640, 1), (key2913, 1), (key2794, 1), (key2992, 1), (key2944, 1), (key2729, 2), (key2883, 2), (key2832, 2), (key2642, -2), (key2883, -2), (key2796, -2)]

theorem rawRowCheck16648 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form15 = rawRow16648 := by decide +kernel

def row16648 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16648 : row16648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16648 := by decide +kernel

theorem rowEval16648 (x : Key → ℝ) : Integer.Sparse.eval row16648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16648, Integer.Sparse.eval_collectBalanced, rawRowCheck16648]

def rawRow16649 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, 1), (key2939, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2786, -2), (key2632, -2), (key2870, -2), (key2829, -1), (key2961, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2794, 1), (key2944, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2832, 2), (key2729, 2), (key2883, 2), (key2796, -2), (key2642, -2), (key2883, -2)]

theorem rawRowCheck16649 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form15 = rawRow16649 := by decide +kernel

def row16649 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16649 : row16649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16649 := by decide +kernel

theorem rowEval16649 (x : Key → ℝ) : Integer.Sparse.eval row16649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16649, Integer.Sparse.eval_collectBalanced, rawRowCheck16649]

def rawRow16650 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2898, -1), (key2738, -1), (key2809, 2), (key2860, 2), (key2706, 2), (key2939, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2905, 1), (key2649, 1), (key2786, -2), (key2870, -2), (key2632, -2), (key2961, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2913, -1), (key2748, -1), (key2944, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2913, 1), (key2654, 1), (key2832, 2), (key2883, 2), (key2729, 2), (key2796, -2), (key2883, -2), (key2642, -2)]

theorem rawRowCheck16650 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form15 = rawRow16650 := by decide +kernel

def row16650 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16650 : row16650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16650 := by decide +kernel

theorem rowEval16650 (x : Key → ℝ) : Integer.Sparse.eval row16650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16650, Integer.Sparse.eval_collectBalanced, rawRowCheck16650]

def rawRow16651 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2706, -1), (key2809, -1), (key2860, 2), (key2706, 2), (key2809, 2), (key2905, 1), (key2984, 1), (key2649, 1), (key2939, 1), (key2632, 1), (key2786, 1), (key2870, -2), (key2632, -2), (key2786, -2), (key2913, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2726, -1), (key2829, -1), (key2913, 1), (key2992, 1), (key2654, 1), (key2944, 1), (key2640, 1), (key2794, 1), (key2883, 2), (key2729, 2), (key2832, 2), (key2883, -2), (key2642, -2), (key2796, -2)]

theorem rawRowCheck16651 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form15 = rawRow16651 := by decide +kernel

def row16651 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16651 : row16651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16651 := by decide +kernel

theorem rowEval16651 (x : Key → ℝ) : Integer.Sparse.eval row16651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16651, Integer.Sparse.eval_collectBalanced, rawRowCheck16651]

def rawRow16652 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2951, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2860, 2), (key2809, 2), (key2706, 2), (key2984, 1), (key2905, 1), (key2939, 1), (key2649, 1), (key2786, 1), (key2632, 1), (key2870, -2), (key2786, -2), (key2632, -2), (key2992, -1), (key2913, -1), (key2961, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2992, 1), (key2913, 1), (key2944, 1), (key2654, 1), (key2794, 1), (key2640, 1), (key2883, 2), (key2832, 2), (key2729, 2), (key2883, -2), (key2796, -2), (key2642, -2)]

theorem rawRowCheck16652 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form15 = rawRow16652 := by decide +kernel

def row16652 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16652 : row16652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16652 := by decide +kernel

theorem rowEval16652 (x : Key → ℝ) : Integer.Sparse.eval row16652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16652, Integer.Sparse.eval_collectBalanced, rawRowCheck16652]

def rawRow16653 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2870, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2748, 2), (key2905, 2), (key2913, 2), (key2640, 1), (key2642, 1), (key2860, 1), (key2883, 1), (key2977, 1), (key2992, 1), (key2654, -2), (key2898, -2), (key2913, -2), (key2671, -1), (key2674, -1), (key2786, -1), (key2796, -1), (key2939, -1), (key2944, -1), (key2616, 1), (key2619, 1), (key2809, 1), (key2832, 1), (key2951, 1), (key2961, 1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, -2), (key2809, -2), (key2829, -2)]

theorem rawRowCheck16653 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form15 = rawRow16653 := by decide +kernel

def row16653 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16653 : row16653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16653 := by decide +kernel

theorem rowEval16653 (x : Key → ℝ) : Integer.Sparse.eval row16653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16653, Integer.Sparse.eval_collectBalanced, rawRowCheck16653]

def rawRow16654 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2984, -1), (key2748, 2), (key2913, 2), (key2905, 2), (key2642, 1), (key2640, 1), (key2883, 1), (key2860, 1), (key2992, 1), (key2977, 1), (key2654, -2), (key2913, -2), (key2898, -2), (key2674, -1), (key2671, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2939, -1), (key2619, 1), (key2616, 1), (key2832, 1), (key2809, 1), (key2961, 1), (key2951, 1), (key2671, 2), (key2794, 2), (key2786, 2), (key2616, -2), (key2829, -2), (key2809, -2)]

theorem rawRowCheck16654 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form15 = rawRow16654 := by decide +kernel

def row16654 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16654 : row16654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16654 := by decide +kernel

theorem rowEval16654 (x : Key → ℝ) : Integer.Sparse.eval row16654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16654, Integer.Sparse.eval_collectBalanced, rawRowCheck16654]

def rawRow16655 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2905, 2), (key2748, 2), (key2913, 2), (key2860, 1), (key2977, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2898, -2), (key2654, -2), (key2913, -2), (key2786, -1), (key2939, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2809, 1), (key2951, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, -2), (key2616, -2), (key2829, -2)]

theorem rawRowCheck16655 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form15 = rawRow16655 := by decide +kernel

def row16655 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16655 : row16655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16655 := by decide +kernel

theorem rowEval16655 (x : Key → ℝ) : Integer.Sparse.eval row16655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16655, Integer.Sparse.eval_collectBalanced, rawRowCheck16655]

def rawRow16656 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2883, -1), (key2729, -1), (key2905, 2), (key2913, 2), (key2748, 2), (key2977, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2883, 1), (key2642, 1), (key2898, -2), (key2913, -2), (key2654, -2), (key2939, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2796, -1), (key2674, -1), (key2951, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2832, 1), (key2619, 1), (key2786, 2), (key2794, 2), (key2671, 2), (key2809, -2), (key2829, -2), (key2616, -2)]

theorem rawRowCheck16656 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form15 = rawRow16656 := by decide +kernel

def row16656 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16656 : row16656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16656 := by decide +kernel

theorem rowEval16656 (x : Key → ℝ) : Integer.Sparse.eval row16656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16656, Integer.Sparse.eval_collectBalanced, rawRowCheck16656]

def rawRow16657 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2726, -1), (key2870, -1), (key2913, 2), (key2748, 2), (key2905, 2), (key2883, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2640, 1), (key2860, 1), (key2913, -2), (key2654, -2), (key2898, -2), (key2796, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2671, -1), (key2786, -1), (key2832, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2616, 1), (key2809, 1), (key2794, 2), (key2671, 2), (key2786, 2), (key2829, -2), (key2616, -2), (key2809, -2)]

theorem rawRowCheck16657 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form15 = rawRow16657 := by decide +kernel

def row16657 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16657 : row16657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16657 := by decide +kernel

theorem rowEval16657 (x : Key → ℝ) : Integer.Sparse.eval row16657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16657, Integer.Sparse.eval_collectBalanced, rawRowCheck16657]

def rawRow16658 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2984, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2913, 2), (key2905, 2), (key2748, 2), (key2992, 1), (key2883, 1), (key2977, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2913, -2), (key2898, -2), (key2654, -2), (key2944, -1), (key2796, -1), (key2939, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2961, 1), (key2832, 1), (key2951, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2794, 2), (key2786, 2), (key2671, 2), (key2829, -2), (key2809, -2), (key2616, -2)]

theorem rawRowCheck16658 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form15 = rawRow16658 := by decide +kernel

def row16658 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck16658 : row16658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16658 := by decide +kernel

theorem rowEval16658 (x : Key → ℝ) : Integer.Sparse.eval row16658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16658, Integer.Sparse.eval_collectBalanced, rawRowCheck16658]

def rawRow16659 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2829, -1), (key2913, -1), (key2961, -1), (key2992, -1), (key2729, 2), (key2832, 2), (key2883, 2), (key2640, 1), (key2654, 1), (key2794, 1), (key2913, 1), (key2944, 1), (key2992, 1), (key2642, -2), (key2796, -2), (key2883, -2), (key2706, -1), (key2738, -1), (key2809, -1), (key2898, -1), (key2951, -1), (key2977, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2905, 1), (key2939, 1), (key2984, 1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, -2), (key2786, -2), (key2870, -2)]

theorem rawRowCheck16659 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form15 = rawRow16659 := by decide +kernel

def row16659 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16659 : row16659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16659 := by decide +kernel

theorem rowEval16659 (x : Key → ℝ) : Integer.Sparse.eval row16659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16659, Integer.Sparse.eval_collectBalanced, rawRowCheck16659]

def rawRow16660 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2913, -1), (key2829, -1), (key2992, -1), (key2961, -1), (key2729, 2), (key2883, 2), (key2832, 2), (key2654, 1), (key2640, 1), (key2913, 1), (key2794, 1), (key2992, 1), (key2944, 1), (key2642, -2), (key2883, -2), (key2796, -2), (key2738, -1), (key2706, -1), (key2898, -1), (key2809, -1), (key2977, -1), (key2951, -1), (key2649, 1), (key2632, 1), (key2905, 1), (key2786, 1), (key2984, 1), (key2939, 1), (key2706, 2), (key2860, 2), (key2809, 2), (key2632, -2), (key2870, -2), (key2786, -2)]

theorem rawRowCheck16660 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form15 = rawRow16660 := by decide +kernel

def row16660 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16660 : row16660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16660 := by decide +kernel

theorem rowEval16660 (x : Key → ℝ) : Integer.Sparse.eval row16660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16660, Integer.Sparse.eval_collectBalanced, rawRowCheck16660]

def rawRow16661 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2832, 2), (key2729, 2), (key2883, 2), (key2794, 1), (key2944, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2796, -2), (key2642, -2), (key2883, -2), (key2809, -1), (key2951, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2786, 1), (key2939, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, -2), (key2632, -2), (key2870, -2)]

theorem rawRowCheck16661 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form15 = rawRow16661 := by decide +kernel

def row16661 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16661 : row16661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16661 := by decide +kernel

theorem rowEval16661 (x : Key → ℝ) : Integer.Sparse.eval row16661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16661, Integer.Sparse.eval_collectBalanced, rawRowCheck16661]

def rawRow16662 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2913, -1), (key2748, -1), (key2832, 2), (key2883, 2), (key2729, 2), (key2944, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2913, 1), (key2654, 1), (key2796, -2), (key2883, -2), (key2642, -2), (key2951, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2898, -1), (key2738, -1), (key2939, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2905, 1), (key2649, 1), (key2809, 2), (key2860, 2), (key2706, 2), (key2786, -2), (key2870, -2), (key2632, -2)]

theorem rawRowCheck16662 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form15 = rawRow16662 := by decide +kernel

def row16662 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16662 : row16662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16662 := by decide +kernel

theorem rowEval16662 (x : Key → ℝ) : Integer.Sparse.eval row16662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16662, Integer.Sparse.eval_collectBalanced, rawRowCheck16662]

def rawRow16663 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2726, -1), (key2829, -1), (key2883, 2), (key2729, 2), (key2832, 2), (key2913, 1), (key2992, 1), (key2654, 1), (key2944, 1), (key2640, 1), (key2794, 1), (key2883, -2), (key2642, -2), (key2796, -2), (key2898, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2706, -1), (key2809, -1), (key2905, 1), (key2984, 1), (key2649, 1), (key2939, 1), (key2632, 1), (key2786, 1), (key2860, 2), (key2706, 2), (key2809, 2), (key2870, -2), (key2632, -2), (key2786, -2)]

theorem rawRowCheck16663 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form15 = rawRow16663 := by decide +kernel

def row16663 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16663 : row16663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16663 := by decide +kernel

theorem rowEval16663 (x : Key → ℝ) : Integer.Sparse.eval row16663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16663, Integer.Sparse.eval_collectBalanced, rawRowCheck16663]

def rawRow16664 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2961, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2883, 2), (key2832, 2), (key2729, 2), (key2992, 1), (key2913, 1), (key2944, 1), (key2654, 1), (key2794, 1), (key2640, 1), (key2883, -2), (key2796, -2), (key2642, -2), (key2977, -1), (key2898, -1), (key2951, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2984, 1), (key2905, 1), (key2939, 1), (key2649, 1), (key2786, 1), (key2632, 1), (key2860, 2), (key2809, 2), (key2706, 2), (key2870, -2), (key2786, -2), (key2632, -2)]

theorem rawRowCheck16664 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form15 = rawRow16664 := by decide +kernel

def row16664 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck16664 : row16664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16664 := by decide +kernel

theorem rowEval16664 (x : Key → ℝ) : Integer.Sparse.eval row16664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16664, Integer.Sparse.eval_collectBalanced, rawRowCheck16664]

def rawRow16665 : Integer.Sparse Key := [(key2729, -1), (key2748, -1), (key2832, -1), (key2905, -1), (key2961, -1), (key2984, -1), (key2726, 2), (key2829, 2), (key2870, 2), (key2642, 1), (key2654, 1), (key2796, 1), (key2898, 1), (key2944, 1), (key2977, 1), (key2640, -2), (key2794, -2), (key2860, -2), (key2729, -1), (key2748, -1), (key2832, -1), (key2905, -1), (key2961, -1), (key2984, -1), (key2642, 1), (key2654, 1), (key2796, 1), (key2898, 1), (key2944, 1), (key2977, 1), (key2726, 2), (key2829, 2), (key2870, 2), (key2640, -2), (key2794, -2), (key2860, -2)]

theorem rawRowCheck16665 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form15 = rawRow16665 := by decide +kernel

def row16665 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck16665 : row16665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16665 := by decide +kernel

theorem rowEval16665 (x : Key → ℝ) : Integer.Sparse.eval row16665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16665, Integer.Sparse.eval_collectBalanced, rawRowCheck16665]

def rawRow16666 : Integer.Sparse Key := [(key2748, -1), (key2729, -1), (key2905, -1), (key2832, -1), (key2984, -1), (key2961, -1), (key2726, 2), (key2870, 2), (key2829, 2), (key2654, 1), (key2642, 1), (key2898, 1), (key2796, 1), (key2977, 1), (key2944, 1), (key2640, -2), (key2860, -2), (key2794, -2), (key2748, -1), (key2729, -1), (key2905, -1), (key2832, -1), (key2984, -1), (key2961, -1), (key2654, 1), (key2642, 1), (key2898, 1), (key2796, 1), (key2977, 1), (key2944, 1), (key2726, 2), (key2870, 2), (key2829, 2), (key2640, -2), (key2860, -2), (key2794, -2)]

theorem rawRowCheck16666 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form15 = rawRow16666 := by decide +kernel

def row16666 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck16666 : row16666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16666 := by decide +kernel

theorem rowEval16666 (x : Key → ℝ) : Integer.Sparse.eval row16666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16666, Integer.Sparse.eval_collectBalanced, rawRowCheck16666]

def rawRow16667 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2729, -1), (key2984, -1), (key2748, -1), (key2905, -1), (key2829, 2), (key2726, 2), (key2870, 2), (key2796, 1), (key2944, 1), (key2642, 1), (key2977, 1), (key2654, 1), (key2898, 1), (key2794, -2), (key2640, -2), (key2860, -2), (key2832, -1), (key2961, -1), (key2729, -1), (key2984, -1), (key2748, -1), (key2905, -1), (key2796, 1), (key2944, 1), (key2642, 1), (key2977, 1), (key2654, 1), (key2898, 1), (key2829, 2), (key2726, 2), (key2870, 2), (key2794, -2), (key2640, -2), (key2860, -2)]

theorem rawRowCheck16667 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form15 = rawRow16667 := by decide +kernel

def row16667 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck16667 : row16667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16667 := by decide +kernel

theorem rowEval16667 (x : Key → ℝ) : Integer.Sparse.eval row16667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16667, Integer.Sparse.eval_collectBalanced, rawRowCheck16667]

def rawRow16668 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2984, -1), (key2729, -1), (key2905, -1), (key2748, -1), (key2829, 2), (key2870, 2), (key2726, 2), (key2944, 1), (key2796, 1), (key2977, 1), (key2642, 1), (key2898, 1), (key2654, 1), (key2794, -2), (key2860, -2), (key2640, -2), (key2961, -1), (key2832, -1), (key2984, -1), (key2729, -1), (key2905, -1), (key2748, -1), (key2944, 1), (key2796, 1), (key2977, 1), (key2642, 1), (key2898, 1), (key2654, 1), (key2829, 2), (key2870, 2), (key2726, 2), (key2794, -2), (key2860, -2), (key2640, -2)]

theorem rawRowCheck16668 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form15 = rawRow16668 := by decide +kernel

def row16668 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck16668 : row16668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16668 := by decide +kernel

theorem rowEval16668 (x : Key → ℝ) : Integer.Sparse.eval row16668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16668, Integer.Sparse.eval_collectBalanced, rawRowCheck16668]

def rawRow16669 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2748, -1), (key2961, -1), (key2729, -1), (key2832, -1), (key2870, 2), (key2726, 2), (key2829, 2), (key2898, 1), (key2977, 1), (key2654, 1), (key2944, 1), (key2642, 1), (key2796, 1), (key2860, -2), (key2640, -2), (key2794, -2), (key2905, -1), (key2984, -1), (key2748, -1), (key2961, -1), (key2729, -1), (key2832, -1), (key2898, 1), (key2977, 1), (key2654, 1), (key2944, 1), (key2642, 1), (key2796, 1), (key2870, 2), (key2726, 2), (key2829, 2), (key2860, -2), (key2640, -2), (key2794, -2)]

theorem rawRowCheck16669 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form15 = rawRow16669 := by decide +kernel

def row16669 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck16669 : row16669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16669 := by decide +kernel

theorem rowEval16669 (x : Key → ℝ) : Integer.Sparse.eval row16669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16669, Integer.Sparse.eval_collectBalanced, rawRowCheck16669]

def rawRow16670 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2961, -1), (key2748, -1), (key2832, -1), (key2729, -1), (key2870, 2), (key2829, 2), (key2726, 2), (key2977, 1), (key2898, 1), (key2944, 1), (key2654, 1), (key2796, 1), (key2642, 1), (key2860, -2), (key2794, -2), (key2640, -2), (key2984, -1), (key2905, -1), (key2961, -1), (key2748, -1), (key2832, -1), (key2729, -1), (key2977, 1), (key2898, 1), (key2944, 1), (key2654, 1), (key2796, 1), (key2642, 1), (key2870, 2), (key2829, 2), (key2726, 2), (key2860, -2), (key2794, -2), (key2640, -2)]

theorem rawRowCheck16670 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form15 = rawRow16670 := by decide +kernel

def row16670 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck16670 : row16670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16670 := by decide +kernel

theorem rowEval16670 (x : Key → ℝ) : Integer.Sparse.eval row16670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16670, Integer.Sparse.eval_collectBalanced, rawRowCheck16670]

def rawRow16671 : Integer.Sparse Key := [(key2617, 2), (key2962, 2), (key2962, 2), (key2620, -1), (key2620, -1), (key2833, -1), (key2833, -1), (key2964, -1), (key2964, -1), (key2633, 2), (key2985, 2), (key2985, 2), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2650, -1), (key2650, -1), (key2906, -1), (key2906, -1), (key3001, -1), (key3001, -1), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2656, 2), (key2656, 2), (key2751, 2), (key2751, 2), (key2915, 2), (key2915, 2)]

theorem rawRowCheck16671 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form16 = rawRow16671 := by decide +kernel

def row16671 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

theorem rowCheck16671 : row16671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16671 := by decide +kernel

theorem rowEval16671 (x : Key → ℝ) : Integer.Sparse.eval row16671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16671, Integer.Sparse.eval_collectBalanced, rawRowCheck16671]

def rawRow16672 : Integer.Sparse Key := [(key2962, 2), (key2617, 2), (key2962, 2), (key2833, -1), (key2964, -1), (key2620, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2985, 2), (key2633, 2), (key2985, 2), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2906, -1), (key3001, -1), (key2650, -1), (key3001, -1), (key2650, -1), (key2906, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2751, 2), (key2915, 2), (key2656, 2), (key2915, 2), (key2656, 2), (key2751, 2)]

theorem rawRowCheck16672 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form16 = rawRow16672 := by decide +kernel

def row16672 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

theorem rowCheck16672 : row16672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16672 := by decide +kernel

theorem rowEval16672 (x : Key → ℝ) : Integer.Sparse.eval row16672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16672, Integer.Sparse.eval_collectBalanced, rawRowCheck16672]

def rawRow16673 : Integer.Sparse Key := [(key2962, 2), (key2962, 2), (key2617, 2), (key2964, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2620, -1), (key2985, 2), (key2985, 2), (key2633, 2), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key3001, -1), (key2906, -1), (key3001, -1), (key2650, -1), (key2906, -1), (key2650, -1), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2915, 2), (key2751, 2), (key2915, 2), (key2656, 2), (key2751, 2), (key2656, 2)]

theorem rawRowCheck16673 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form16 = rawRow16673 := by decide +kernel

def row16673 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2906, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, -2)]

theorem rowCheck16673 : row16673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16673 := by decide +kernel

theorem rowEval16673 (x : Key → ℝ) : Integer.Sparse.eval row16673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16673, Integer.Sparse.eval_collectBalanced, rawRowCheck16673]

def rawRow16674 : Integer.Sparse Key := [(key2620, 2), (key2833, 2), (key2964, 2), (key2617, -1), (key2620, -1), (key2810, -1), (key2833, -1), (key2952, -1), (key2962, -1), (key2643, 2), (key2978, 2), (key2994, 2), (key2633, -1), (key2643, -1), (key2707, -1), (key2730, -1), (key2978, -1), (key2985, -1), (key2655, -1), (key2656, -1), (key2899, -1), (key2915, -1), (key2999, -1), (key3004, -1), (key2650, -1), (key2656, -1), (key2739, -1), (key2751, -1), (key2999, -1), (key3001, -1), (key2650, 2), (key2655, 2), (key2739, 2), (key2749, 2), (key2899, 2), (key2906, 2)]

theorem rawRowCheck16674 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form16 = rawRow16674 := by decide +kernel

def row16674 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

theorem rowCheck16674 : row16674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16674 := by decide +kernel

theorem rowEval16674 (x : Key → ℝ) : Integer.Sparse.eval row16674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16674, Integer.Sparse.eval_collectBalanced, rawRowCheck16674]

def rawRow16675 : Integer.Sparse Key := [(key2620, 2), (key2964, 2), (key2833, 2), (key2620, -1), (key2617, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2952, -1), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2915, -1), (key2899, -1), (key3004, -1), (key2999, -1), (key2656, -1), (key2650, -1), (key2751, -1), (key2739, -1), (key3001, -1), (key2999, -1), (key2655, 2), (key2650, 2), (key2749, 2), (key2739, 2), (key2906, 2), (key2899, 2)]

theorem rawRowCheck16675 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form16 = rawRow16675 := by decide +kernel

def row16675 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

theorem rowCheck16675 : row16675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16675 := by decide +kernel

theorem rowEval16675 (x : Key → ℝ) : Integer.Sparse.eval row16675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16675, Integer.Sparse.eval_collectBalanced, rawRowCheck16675]

def rawRow16676 : Integer.Sparse Key := [(key2833, 2), (key2620, 2), (key2964, 2), (key2810, -1), (key2833, -1), (key2617, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2655, -1), (key3004, -1), (key2656, -1), (key2915, -1), (key2739, -1), (key2999, -1), (key2650, -1), (key3001, -1), (key2656, -1), (key2751, -1), (key2739, 2), (key2899, 2), (key2650, 2), (key2906, 2), (key2655, 2), (key2749, 2)]

theorem rawRowCheck16676 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form16 = rawRow16676 := by decide +kernel

def row16676 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2899, 1), (key2906, 2), (key2915, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

theorem rowCheck16676 : row16676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16676 := by decide +kernel

theorem rowEval16676 (x : Key → ℝ) : Integer.Sparse.eval row16676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16676, Integer.Sparse.eval_collectBalanced, rawRowCheck16676]

def rawRow16677 : Integer.Sparse Key := [(key2833, 2), (key2964, 2), (key2620, 2), (key2833, -1), (key2810, -1), (key2962, -1), (key2617, -1), (key2833, -1), (key2620, -1), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key3004, -1), (key2655, -1), (key2915, -1), (key2656, -1), (key2999, -1), (key2739, -1), (key3001, -1), (key2650, -1), (key2751, -1), (key2656, -1), (key2899, 2), (key2739, 2), (key2906, 2), (key2650, 2), (key2749, 2), (key2655, 2)]

theorem rawRowCheck16677 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form16 = rawRow16677 := by decide +kernel

def row16677 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2899, 1), (key2906, 2), (key2915, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

theorem rowCheck16677 : row16677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16677 := by decide +kernel

theorem rowEval16677 (x : Key → ℝ) : Integer.Sparse.eval row16677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16677, Integer.Sparse.eval_collectBalanced, rawRowCheck16677]

def rawRow16678 : Integer.Sparse Key := [(key2964, 2), (key2620, 2), (key2833, 2), (key2952, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2617, -1), (key2810, -1), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, -1), (key2707, -1), (key2915, -1), (key3004, -1), (key2656, -1), (key2999, -1), (key2655, -1), (key2899, -1), (key2751, -1), (key3001, -1), (key2656, -1), (key2999, -1), (key2650, -1), (key2739, -1), (key2749, 2), (key2906, 2), (key2655, 2), (key2899, 2), (key2650, 2), (key2739, 2)]

theorem rawRowCheck16678 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form16 = rawRow16678 := by decide +kernel

def row16678 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

theorem rowCheck16678 : row16678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16678 := by decide +kernel

theorem rowEval16678 (x : Key → ℝ) : Integer.Sparse.eval row16678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16678, Integer.Sparse.eval_collectBalanced, rawRowCheck16678]

def rawRow16679 : Integer.Sparse Key := [(key2964, 2), (key2833, 2), (key2620, 2), (key2962, -1), (key2952, -1), (key2833, -1), (key2620, -1), (key2810, -1), (key2617, -1), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key3004, -1), (key2915, -1), (key2999, -1), (key2656, -1), (key2899, -1), (key2655, -1), (key3001, -1), (key2751, -1), (key2999, -1), (key2656, -1), (key2739, -1), (key2650, -1), (key2906, 2), (key2749, 2), (key2899, 2), (key2655, 2), (key2739, 2), (key2650, 2)]

theorem rawRowCheck16679 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form16 = rawRow16679 := by decide +kernel

def row16679 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 1), (key2749, 2), (key2751, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 2), (key2915, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, -1), (key2994, 2), (key2999, -2), (key3001, -1), (key3004, -1)]

theorem rowCheck16679 : row16679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16679 := by decide +kernel

theorem rowEval16679 (x : Key → ℝ) : Integer.Sparse.eval row16679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16679, Integer.Sparse.eval_collectBalanced, rawRowCheck16679]

def rawRow16680 : Integer.Sparse Key := [(key2633, 2), (key2985, 2), (key2985, 2), (key2643, -1), (key2643, -1), (key2978, -1), (key2978, -1), (key2994, -1), (key2994, -1), (key2617, 2), (key2962, 2), (key2962, 2), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2620, -1), (key2620, -1), (key2833, -1), (key2833, -1), (key2964, -1), (key2964, -1), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2656, 2), (key2656, 2), (key2751, 2), (key2751, 2), (key2915, 2), (key2915, 2)]

theorem rawRowCheck16680 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form16 = rawRow16680 := by decide +kernel

def row16680 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

theorem rowCheck16680 : row16680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16680 := by decide +kernel

theorem rowEval16680 (x : Key → ℝ) : Integer.Sparse.eval row16680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16680, Integer.Sparse.eval_collectBalanced, rawRowCheck16680]

def rawRow16681 : Integer.Sparse Key := [(key2985, 2), (key2633, 2), (key2985, 2), (key2978, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2978, -1), (key2962, 2), (key2617, 2), (key2962, 2), (key2749, -1), (key3004, -1), (key2655, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2751, 2), (key2915, 2), (key2656, 2), (key2915, 2), (key2656, 2), (key2751, 2)]

theorem rawRowCheck16681 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form16 = rawRow16681 := by decide +kernel

def row16681 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

theorem rowCheck16681 : row16681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16681 := by decide +kernel

theorem rowEval16681 (x : Key → ℝ) : Integer.Sparse.eval row16681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16681, Integer.Sparse.eval_collectBalanced, rawRowCheck16681]

def rawRow16682 : Integer.Sparse Key := [(key2985, 2), (key2985, 2), (key2633, 2), (key2994, -1), (key2978, -1), (key2994, -1), (key2643, -1), (key2978, -1), (key2643, -1), (key2962, 2), (key2962, 2), (key2617, 2), (key3004, -1), (key2749, -1), (key3004, -1), (key2655, -1), (key2749, -1), (key2655, -1), (key2964, -1), (key2833, -1), (key2964, -1), (key2620, -1), (key2833, -1), (key2620, -1), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key2915, 2), (key2751, 2), (key2915, 2), (key2656, 2), (key2751, 2), (key2656, 2)]

theorem rawRowCheck16682 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form16 = rawRow16682 := by decide +kernel

def row16682 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -4), (key2655, -2), (key2656, 4), (key2730, -2), (key2749, -2), (key2751, 4), (key2833, -2), (key2915, 4), (key2962, 4), (key2964, -2), (key2978, -2), (key2985, 4), (key2994, -4), (key3004, -2)]

theorem rowCheck16682 : row16682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16682 := by decide +kernel

theorem rowEval16682 (x : Key → ℝ) : Integer.Sparse.eval row16682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16682, Integer.Sparse.eval_collectBalanced, rawRowCheck16682]

def rawRow16683 : Integer.Sparse Key := [(key2643, 2), (key2730, 2), (key2994, 2), (key2633, -1), (key2643, -1), (key2707, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2915, -1), (key2946, -1), (key2994, -1), (key2620, -1), (key2656, -1), (key2675, -1), (key2751, -1), (key2946, -1), (key2964, -1), (key2620, 2), (key2643, 2), (key2675, 2), (key2730, 2), (key2797, 2), (key2833, 2)]

theorem rawRowCheck16683 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form16 = rawRow16683 := by decide +kernel

def row16683 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

theorem rowCheck16683 : row16683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16683 := by decide +kernel

theorem rowEval16683 (x : Key → ℝ) : Integer.Sparse.eval row16683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16683, Integer.Sparse.eval_collectBalanced, rawRowCheck16683]

def rawRow16684 : Integer.Sparse Key := [(key2643, 2), (key2994, 2), (key2730, 2), (key2643, -1), (key2633, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2730, -1), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2946, -1), (key2656, -1), (key2620, -1), (key2751, -1), (key2675, -1), (key2964, -1), (key2946, -1), (key2643, 2), (key2620, 2), (key2730, 2), (key2675, 2), (key2833, 2), (key2797, 2)]

theorem rawRowCheck16684 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form16 = rawRow16684 := by decide +kernel

def row16684 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

theorem rowCheck16684 : row16684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16684 := by decide +kernel

theorem rowEval16684 (x : Key → ℝ) : Integer.Sparse.eval row16684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16684, Integer.Sparse.eval_collectBalanced, rawRowCheck16684]

def rawRow16685 : Integer.Sparse Key := [(key2730, 2), (key2643, 2), (key2994, 2), (key2707, -1), (key2730, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2675, -1), (key2946, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2675, 2), (key2797, 2), (key2620, 2), (key2833, 2), (key2643, 2), (key2730, 2)]

theorem rawRowCheck16685 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form16 = rawRow16685 := by decide +kernel

def row16685 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

theorem rowCheck16685 : row16685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16685 := by decide +kernel

theorem rowEval16685 (x : Key → ℝ) : Integer.Sparse.eval row16685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16685, Integer.Sparse.eval_collectBalanced, rawRowCheck16685]

def rawRow16686 : Integer.Sparse Key := [(key2730, 2), (key2994, 2), (key2643, 2), (key2730, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2978, -1), (key2643, -1), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2915, -1), (key2656, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2751, -1), (key2656, -1), (key2797, 2), (key2675, 2), (key2833, 2), (key2620, 2), (key2730, 2), (key2643, 2)]

theorem rawRowCheck16686 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form16 = rawRow16686 := by decide +kernel

def row16686 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

theorem rowCheck16686 : row16686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16686 := by decide +kernel

theorem rowEval16686 (x : Key → ℝ) : Integer.Sparse.eval row16686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16686, Integer.Sparse.eval_collectBalanced, rawRowCheck16686]

def rawRow16687 : Integer.Sparse Key := [(key2994, 2), (key2643, 2), (key2730, 2), (key2978, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2633, -1), (key2707, -1), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2643, -1), (key2797, -1), (key2751, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2620, -1), (key2675, -1), (key2730, 2), (key2833, 2), (key2643, 2), (key2797, 2), (key2620, 2), (key2675, 2)]

theorem rawRowCheck16687 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form16 = rawRow16687 := by decide +kernel

def row16687 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

theorem rowCheck16687 : row16687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16687 := by decide +kernel

theorem rowEval16687 (x : Key → ℝ) : Integer.Sparse.eval row16687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16687, Integer.Sparse.eval_collectBalanced, rawRowCheck16687]

def rawRow16688 : Integer.Sparse Key := [(key2994, 2), (key2730, 2), (key2643, 2), (key2985, -1), (key2978, -1), (key2730, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2946, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2964, -1), (key2751, -1), (key2946, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2833, 2), (key2730, 2), (key2797, 2), (key2643, 2), (key2675, 2), (key2620, 2)]

theorem rawRowCheck16688 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form16 = rawRow16688 := by decide +kernel

def row16688 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 2), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2749, 1), (key2751, -1), (key2797, 1), (key2833, 2), (key2915, -1), (key2945, -1), (key2946, -2), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 1), (key3004, 2)]

theorem rowCheck16688 : row16688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16688 := by decide +kernel

theorem rowEval16688 (x : Key → ℝ) : Integer.Sparse.eval row16688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16688, Integer.Sparse.eval_collectBalanced, rawRowCheck16688]

def rawRow16689 : Integer.Sparse Key := [(key2650, 2), (key2906, 2), (key3001, 2), (key2655, -1), (key2656, -1), (key2899, -1), (key2999, -1), (key2915, -1), (key3004, -1), (key2620, 2), (key2833, 2), (key2964, 2), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2810, -1), (key2833, -1), (key2952, -1), (key2962, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2730, -1), (key2978, -1), (key2985, -1), (key2650, 2), (key2655, 2), (key2739, 2), (key2749, 2), (key2899, 2), (key2906, 2)]

theorem rawRowCheck16689 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form16 = rawRow16689 := by decide +kernel

def row16689 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

theorem rowCheck16689 : row16689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16689 := by decide +kernel

theorem rowEval16689 (x : Key → ℝ) : Integer.Sparse.eval row16689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16689, Integer.Sparse.eval_collectBalanced, rawRowCheck16689]

def rawRow16690 : Integer.Sparse Key := [(key2650, 2), (key3001, 2), (key2906, 2), (key2656, -1), (key2655, -1), (key2999, -1), (key2899, -1), (key3004, -1), (key2915, -1), (key2620, 2), (key2964, 2), (key2833, 2), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2952, -1), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2978, -1), (key2655, 2), (key2650, 2), (key2749, 2), (key2739, 2), (key2906, 2), (key2899, 2)]

theorem rawRowCheck16690 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form16 = rawRow16690 := by decide +kernel

def row16690 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

theorem rowCheck16690 : row16690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16690 := by decide +kernel

theorem rowEval16690 (x : Key → ℝ) : Integer.Sparse.eval row16690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16690, Integer.Sparse.eval_collectBalanced, rawRowCheck16690]

def rawRow16691 : Integer.Sparse Key := [(key2906, 2), (key2650, 2), (key3001, 2), (key2899, -1), (key2915, -1), (key2655, -1), (key3004, -1), (key2656, -1), (key2999, -1), (key2833, 2), (key2620, 2), (key2964, 2), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2617, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2739, 2), (key2899, 2), (key2650, 2), (key2906, 2), (key2655, 2), (key2749, 2)]

theorem rawRowCheck16691 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form16 = rawRow16691 := by decide +kernel

def row16691 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

theorem rowCheck16691 : row16691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16691 := by decide +kernel

theorem rowEval16691 (x : Key → ℝ) : Integer.Sparse.eval row16691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16691, Integer.Sparse.eval_collectBalanced, rawRowCheck16691]

def rawRow16692 : Integer.Sparse Key := [(key2906, 2), (key3001, 2), (key2650, 2), (key2915, -1), (key2899, -1), (key3004, -1), (key2655, -1), (key2999, -1), (key2656, -1), (key2833, 2), (key2964, 2), (key2620, 2), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2617, -1), (key2833, -1), (key2620, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, -1), (key2643, -1), (key2899, 2), (key2739, 2), (key2906, 2), (key2650, 2), (key2749, 2), (key2655, 2)]

theorem rawRowCheck16692 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form16 = rawRow16692 := by decide +kernel

def row16692 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

theorem rowCheck16692 : row16692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16692 := by decide +kernel

theorem rowEval16692 (x : Key → ℝ) : Integer.Sparse.eval row16692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16692, Integer.Sparse.eval_collectBalanced, rawRowCheck16692]

def rawRow16693 : Integer.Sparse Key := [(key3001, 2), (key2650, 2), (key2906, 2), (key2999, -1), (key3004, -1), (key2656, -1), (key2915, -1), (key2655, -1), (key2899, -1), (key2964, 2), (key2620, 2), (key2833, 2), (key2946, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2643, -1), (key2797, -1), (key2952, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2617, -1), (key2810, -1), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, -1), (key2707, -1), (key2749, 2), (key2906, 2), (key2655, 2), (key2899, 2), (key2650, 2), (key2739, 2)]

theorem rawRowCheck16693 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form16 = rawRow16693 := by decide +kernel

def row16693 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

theorem rowCheck16693 : row16693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16693 := by decide +kernel

theorem rowEval16693 (x : Key → ℝ) : Integer.Sparse.eval row16693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16693, Integer.Sparse.eval_collectBalanced, rawRowCheck16693]

def rawRow16694 : Integer.Sparse Key := [(key3001, 2), (key2906, 2), (key2650, 2), (key3004, -1), (key2999, -1), (key2915, -1), (key2656, -1), (key2899, -1), (key2655, -1), (key2964, 2), (key2833, 2), (key2620, 2), (key2994, -1), (key2946, -1), (key2915, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2962, -1), (key2952, -1), (key2833, -1), (key2620, -1), (key2810, -1), (key2617, -1), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key2906, 2), (key2749, 2), (key2899, 2), (key2655, 2), (key2739, 2), (key2650, 2)]

theorem rawRowCheck16694 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form16 = rawRow16694 := by decide +kernel

def row16694 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, -2), (key2650, 4), (key2655, 1), (key2656, -2), (key2707, -1), (key2730, -1), (key2739, 2), (key2749, 2), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 4), (key2915, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, -1), (key2985, -1), (key2994, -1), (key2999, -1), (key3001, 2), (key3004, -1)]

theorem rowCheck16694 : row16694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16694 := by decide +kernel

theorem rowEval16694 (x : Key → ℝ) : Integer.Sparse.eval row16694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16694, Integer.Sparse.eval_collectBalanced, rawRowCheck16694]

def rawRow16695 : Integer.Sparse Key := [(key2655, 2), (key2749, 2), (key3004, 2), (key2650, -1), (key2656, -1), (key2739, -1), (key2999, -1), (key2751, -1), (key3001, -1), (key2643, 2), (key2730, 2), (key2994, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2620, 2), (key2643, 2), (key2675, 2), (key2730, 2), (key2797, 2), (key2833, 2)]

theorem rawRowCheck16695 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form16 = rawRow16695 := by decide +kernel

def row16695 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

theorem rowCheck16695 : row16695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16695 := by decide +kernel

theorem rowEval16695 (x : Key → ℝ) : Integer.Sparse.eval row16695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16695, Integer.Sparse.eval_collectBalanced, rawRowCheck16695]

def rawRow16696 : Integer.Sparse Key := [(key2655, 2), (key3004, 2), (key2749, 2), (key2656, -1), (key2650, -1), (key2999, -1), (key2739, -1), (key3001, -1), (key2751, -1), (key2643, 2), (key2994, 2), (key2730, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2730, -1), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2643, 2), (key2620, 2), (key2730, 2), (key2675, 2), (key2833, 2), (key2797, 2)]

theorem rawRowCheck16696 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form16 = rawRow16696 := by decide +kernel

def row16696 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

theorem rowCheck16696 : row16696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16696 := by decide +kernel

theorem rowEval16696 (x : Key → ℝ) : Integer.Sparse.eval row16696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16696, Integer.Sparse.eval_collectBalanced, rawRowCheck16696]

def rawRow16697 : Integer.Sparse Key := [(key2749, 2), (key2655, 2), (key3004, 2), (key2739, -1), (key2751, -1), (key2650, -1), (key3001, -1), (key2656, -1), (key2999, -1), (key2730, 2), (key2643, 2), (key2994, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2707, -1), (key2730, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2675, 2), (key2797, 2), (key2620, 2), (key2833, 2), (key2643, 2), (key2730, 2)]

theorem rawRowCheck16697 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form16 = rawRow16697 := by decide +kernel

def row16697 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2751, -2), (key2797, 2), (key2833, 2), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

theorem rowCheck16697 : row16697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16697 := by decide +kernel

theorem rowEval16697 (x : Key → ℝ) : Integer.Sparse.eval row16697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16697, Integer.Sparse.eval_collectBalanced, rawRowCheck16697]

def rawRow16698 : Integer.Sparse Key := [(key2749, 2), (key3004, 2), (key2655, 2), (key2751, -1), (key2739, -1), (key3001, -1), (key2650, -1), (key2999, -1), (key2656, -1), (key2730, 2), (key2994, 2), (key2643, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2978, -1), (key2643, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2797, 2), (key2675, 2), (key2833, 2), (key2620, 2), (key2730, 2), (key2643, 2)]

theorem rawRowCheck16698 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form16 = rawRow16698 := by decide +kernel

def row16698 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2751, -2), (key2797, 2), (key2833, 2), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

theorem rowCheck16698 : row16698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16698 := by decide +kernel

theorem rowEval16698 (x : Key → ℝ) : Integer.Sparse.eval row16698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16698, Integer.Sparse.eval_collectBalanced, rawRowCheck16698]

def rawRow16699 : Integer.Sparse Key := [(key3004, 2), (key2655, 2), (key2749, 2), (key2999, -1), (key3001, -1), (key2656, -1), (key2751, -1), (key2650, -1), (key2739, -1), (key2994, 2), (key2643, 2), (key2730, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2978, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2633, -1), (key2707, -1), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2730, 2), (key2833, 2), (key2643, 2), (key2797, 2), (key2620, 2), (key2675, 2)]

theorem rawRowCheck16699 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form16 = rawRow16699 := by decide +kernel

def row16699 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

theorem rowCheck16699 : row16699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16699 := by decide +kernel

theorem rowEval16699 (x : Key → ℝ) : Integer.Sparse.eval row16699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16699, Integer.Sparse.eval_collectBalanced, rawRowCheck16699]

def rawRow16700 : Integer.Sparse Key := [(key3004, 2), (key2749, 2), (key2655, 2), (key3001, -1), (key2999, -1), (key2751, -1), (key2656, -1), (key2739, -1), (key2650, -1), (key2994, 2), (key2730, 2), (key2643, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2985, -1), (key2978, -1), (key2730, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2833, 2), (key2730, 2), (key2797, 2), (key2643, 2), (key2675, 2), (key2620, 2)]

theorem rawRowCheck16700 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form16 = rawRow16700 := by decide +kernel

def row16700 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, -1), (key2643, 3), (key2650, -1), (key2655, 1), (key2656, -2), (key2672, -1), (key2675, 1), (key2707, -1), (key2730, 3), (key2739, -1), (key2749, 1), (key2751, -2), (key2797, 2), (key2833, 2), (key2945, -1), (key2946, -1), (key2962, -1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, -1), (key3001, -1), (key3004, 2)]

theorem rowCheck16700 : row16700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16700 := by decide +kernel

theorem rowEval16700 (x : Key → ℝ) : Integer.Sparse.eval row16700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16700, Integer.Sparse.eval_collectBalanced, rawRowCheck16700]

def rawRow16701 : Integer.Sparse Key := [(key2656, 2), (key2751, 2), (key2915, 2), (key2650, -1), (key2655, -1), (key2739, -1), (key2899, -1), (key2749, -1), (key2906, -1), (key2656, 2), (key2751, 2), (key2915, 2), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, -1), (key2833, -1), (key2650, -1), (key2655, -1), (key2739, -1), (key2899, -1), (key2749, -1), (key2906, -1), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, -1), (key2833, -1), (key2617, 2), (key2633, 2), (key2672, 2), (key2707, 2), (key2787, 2), (key2810, 2)]

theorem rawRowCheck16701 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form16 = rawRow16701 := by decide +kernel

def row16701 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

theorem rowCheck16701 : row16701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16701 := by decide +kernel

theorem rowEval16701 (x : Key → ℝ) : Integer.Sparse.eval row16701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16701, Integer.Sparse.eval_collectBalanced, rawRowCheck16701]

def rawRow16702 : Integer.Sparse Key := [(key2656, 2), (key2915, 2), (key2751, 2), (key2655, -1), (key2650, -1), (key2899, -1), (key2739, -1), (key2906, -1), (key2749, -1), (key2656, 2), (key2915, 2), (key2751, 2), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, -1), (key2730, -1), (key2655, -1), (key2650, -1), (key2899, -1), (key2739, -1), (key2906, -1), (key2749, -1), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, -1), (key2730, -1), (key2633, 2), (key2617, 2), (key2707, 2), (key2672, 2), (key2810, 2), (key2787, 2)]

theorem rawRowCheck16702 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form16 = rawRow16702 := by decide +kernel

def row16702 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

theorem rowCheck16702 : row16702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16702 := by decide +kernel

theorem rowEval16702 (x : Key → ℝ) : Integer.Sparse.eval row16702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16702, Integer.Sparse.eval_collectBalanced, rawRowCheck16702]

def rawRow16703 : Integer.Sparse Key := [(key2751, 2), (key2656, 2), (key2915, 2), (key2739, -1), (key2749, -1), (key2650, -1), (key2906, -1), (key2655, -1), (key2899, -1), (key2751, 2), (key2656, 2), (key2915, 2), (key2675, -1), (key2730, -1), (key2620, -1), (key2833, -1), (key2643, -1), (key2797, -1), (key2739, -1), (key2749, -1), (key2650, -1), (key2906, -1), (key2655, -1), (key2899, -1), (key2675, -1), (key2730, -1), (key2620, -1), (key2833, -1), (key2643, -1), (key2797, -1), (key2672, 2), (key2707, 2), (key2617, 2), (key2810, 2), (key2633, 2), (key2707, 2)]

theorem rawRowCheck16703 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form16 = rawRow16703 := by decide +kernel

def row16703 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 4), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

theorem rowCheck16703 : row16703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16703 := by decide +kernel

theorem rowEval16703 (x : Key → ℝ) : Integer.Sparse.eval row16703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck16703, Integer.Sparse.eval_collectBalanced, rawRowCheck16703]

def rawRow16704 : Integer.Sparse Key := [(key2751, 2), (key2915, 2), (key2656, 2), (key2749, -1), (key2739, -1), (key2906, -1), (key2650, -1), (key2899, -1), (key2655, -1), (key2751, 2), (key2915, 2), (key2656, 2), (key2730, -1), (key2675, -1), (key2833, -1), (key2620, -1), (key2797, -1), (key2643, -1), (key2749, -1), (key2739, -1), (key2906, -1), (key2650, -1), (key2899, -1), (key2655, -1), (key2730, -1), (key2675, -1), (key2833, -1), (key2620, -1), (key2797, -1), (key2643, -1), (key2707, 2), (key2672, 2), (key2810, 2), (key2617, 2), (key2707, 2), (key2633, 2)]

theorem rawRowCheck16704 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form16 = rawRow16704 := by decide +kernel

def row16704 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 4), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

theorem rowCheck16704 : row16704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16704 := by decide +kernel

theorem rowEval16704 (x : Key → ℝ) : Integer.Sparse.eval row16704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16704, Integer.Sparse.eval_collectBalanced, rawRowCheck16704]

def rawRow16705 : Integer.Sparse Key := [(key2915, 2), (key2656, 2), (key2751, 2), (key2899, -1), (key2906, -1), (key2655, -1), (key2749, -1), (key2650, -1), (key2739, -1), (key2915, 2), (key2656, 2), (key2751, 2), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, -1), (key2675, -1), (key2899, -1), (key2906, -1), (key2655, -1), (key2749, -1), (key2650, -1), (key2739, -1), (key2797, -1), (key2833, -1), (key2643, -1), (key2730, -1), (key2620, -1), (key2675, -1), (key2787, 2), (key2810, 2), (key2633, 2), (key2707, 2), (key2617, 2), (key2672, 2)]

theorem rawRowCheck16705 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form16 = rawRow16705 := by decide +kernel

def row16705 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

theorem rowCheck16705 : row16705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16705 := by decide +kernel

theorem rowEval16705 (x : Key → ℝ) : Integer.Sparse.eval row16705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck16705, Integer.Sparse.eval_collectBalanced, rawRowCheck16705]

def rawRow16706 : Integer.Sparse Key := [(key2915, 2), (key2751, 2), (key2656, 2), (key2906, -1), (key2899, -1), (key2749, -1), (key2655, -1), (key2739, -1), (key2650, -1), (key2915, 2), (key2751, 2), (key2656, 2), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, -1), (key2620, -1), (key2906, -1), (key2899, -1), (key2749, -1), (key2655, -1), (key2739, -1), (key2650, -1), (key2833, -1), (key2797, -1), (key2730, -1), (key2643, -1), (key2675, -1), (key2620, -1), (key2810, 2), (key2787, 2), (key2707, 2), (key2633, 2), (key2672, 2), (key2617, 2)]

theorem rawRowCheck16706 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form16 = rawRow16706 := by decide +kernel

def row16706 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, -2), (key2656, 4), (key2672, 2), (key2675, -2), (key2707, 2), (key2730, -2), (key2739, -2), (key2749, -2), (key2751, 4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4)]

theorem rowCheck16706 : row16706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16706 := by decide +kernel

theorem rowEval16706 (x : Key → ℝ) : Integer.Sparse.eval row16706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form16) x := by
  rw [rowCheck16706, Integer.Sparse.eval_collectBalanced, rawRowCheck16706]

def rawRow16707 : Integer.Sparse Key := [(key2234, 4), (key2234, 4), (key2259, 4), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2324, 4), (key2324, 4), (key2336, 4)]

theorem rawRowCheck16707 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form0 = rawRow16707 := by decide +kernel

def row16707 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

theorem rowCheck16707 : row16707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16707 := by decide +kernel

theorem rowEval16707 (x : Key → ℝ) : Integer.Sparse.eval row16707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16707, Integer.Sparse.eval_collectBalanced, rawRowCheck16707]

def rawRow16708 : Integer.Sparse Key := [(key2234, 4), (key2259, 4), (key2234, 4), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2324, 4), (key2336, 4), (key2324, 4)]

theorem rawRowCheck16708 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form0 = rawRow16708 := by decide +kernel

def row16708 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

theorem rowCheck16708 : row16708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16708 := by decide +kernel

theorem rowEval16708 (x : Key → ℝ) : Integer.Sparse.eval row16708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16708, Integer.Sparse.eval_collectBalanced, rawRowCheck16708]

def rawRow16709 : Integer.Sparse Key := [(key2259, 4), (key2234, 4), (key2234, 4), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2336, 4), (key2324, 4), (key2324, 4)]

theorem rawRowCheck16709 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form0 = rawRow16709 := by decide +kernel

def row16709 : Integer.Sparse Key := [(key2234, 8), (key2259, 4), (key2268, -8), (key2272, -8), (key2294, -8), (key2324, 8), (key2336, 4)]

theorem rowCheck16709 : row16709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16709 := by decide +kernel

theorem rowEval16709 (x : Key → ℝ) : Integer.Sparse.eval row16709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16709, Integer.Sparse.eval_collectBalanced, rawRowCheck16709]

def rawRow16710 : Integer.Sparse Key := [(key1989, 4), (key2268, 4), (key2294, 4), (key1989, -2), (key1994, -2), (key2234, -2), (key2259, -2), (key2272, -2), (key2294, -2), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key2003, 4), (key2272, 4), (key2294, 4)]

theorem rawRowCheck16710 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form0 = rawRow16710 := by decide +kernel

def row16710 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16710 : row16710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16710 := by decide +kernel

theorem rowEval16710 (x : Key → ℝ) : Integer.Sparse.eval row16710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16710, Integer.Sparse.eval_collectBalanced, rawRowCheck16710]

def rawRow16711 : Integer.Sparse Key := [(key1989, 4), (key2294, 4), (key2268, 4), (key1994, -2), (key1989, -2), (key2259, -2), (key2234, -2), (key2294, -2), (key2272, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2003, 4), (key2294, 4), (key2272, 4)]

theorem rawRowCheck16711 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form0 = rawRow16711 := by decide +kernel

def row16711 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16711 : row16711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16711 := by decide +kernel

theorem rowEval16711 (x : Key → ℝ) : Integer.Sparse.eval row16711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16711, Integer.Sparse.eval_collectBalanced, rawRowCheck16711]

def rawRow16712 : Integer.Sparse Key := [(key2268, 4), (key1989, 4), (key2294, 4), (key2234, -2), (key2272, -2), (key1989, -2), (key2294, -2), (key1994, -2), (key2259, -2), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2272, 4), (key2003, 4), (key2294, 4)]

theorem rawRowCheck16712 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form0 = rawRow16712 := by decide +kernel

def row16712 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16712 : row16712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16712 := by decide +kernel

theorem rowEval16712 (x : Key → ℝ) : Integer.Sparse.eval row16712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16712, Integer.Sparse.eval_collectBalanced, rawRowCheck16712]

def rawRow16713 : Integer.Sparse Key := [(key2268, 4), (key2294, 4), (key1989, 4), (key2272, -2), (key2234, -2), (key2294, -2), (key1989, -2), (key2259, -2), (key1994, -2), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, 4), (key2294, 4), (key2003, 4)]

theorem rawRowCheck16713 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form0 = rawRow16713 := by decide +kernel

def row16713 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16713 : row16713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16713 := by decide +kernel

theorem rowEval16713 (x : Key → ℝ) : Integer.Sparse.eval row16713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16713, Integer.Sparse.eval_collectBalanced, rawRowCheck16713]

def rawRow16714 : Integer.Sparse Key := [(key2294, 4), (key1989, 4), (key2268, 4), (key2259, -2), (key2294, -2), (key1994, -2), (key2272, -2), (key1989, -2), (key2234, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2294, 4), (key2003, 4), (key2272, 4)]

theorem rawRowCheck16714 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form0 = rawRow16714 := by decide +kernel

def row16714 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16714 : row16714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16714 := by decide +kernel

theorem rowEval16714 (x : Key → ℝ) : Integer.Sparse.eval row16714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16714, Integer.Sparse.eval_collectBalanced, rawRowCheck16714]

def rawRow16715 : Integer.Sparse Key := [(key2294, 4), (key2268, 4), (key1989, 4), (key2294, -2), (key2259, -2), (key2272, -2), (key1994, -2), (key2234, -2), (key1989, -2), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, 4), (key2272, 4), (key2003, 4)]

theorem rawRowCheck16715 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form0 = rawRow16715 := by decide +kernel

def row16715 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16715 : row16715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16715 := by decide +kernel

theorem rowEval16715 (x : Key → ℝ) : Integer.Sparse.eval row16715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16715, Integer.Sparse.eval_collectBalanced, rawRowCheck16715]

def rawRow16716 : Integer.Sparse Key := [(key1989, 4), (key2268, 4), (key2294, 4), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key1989, -2), (key1994, -2), (key2234, -2), (key2259, -2), (key2272, -2), (key2294, -2), (key2003, 4), (key2272, 4), (key2294, 4)]

theorem rawRowCheck16716 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form0 = rawRow16716 := by decide +kernel

def row16716 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16716 : row16716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16716 := by decide +kernel

theorem rowEval16716 (x : Key → ℝ) : Integer.Sparse.eval row16716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16716, Integer.Sparse.eval_collectBalanced, rawRowCheck16716]

def rawRow16717 : Integer.Sparse Key := [(key1989, 4), (key2294, 4), (key2268, 4), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key1994, -2), (key1989, -2), (key2259, -2), (key2234, -2), (key2294, -2), (key2272, -2), (key2003, 4), (key2294, 4), (key2272, 4)]

theorem rawRowCheck16717 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form0 = rawRow16717 := by decide +kernel

def row16717 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16717 : row16717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16717 := by decide +kernel

theorem rowEval16717 (x : Key → ℝ) : Integer.Sparse.eval row16717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16717, Integer.Sparse.eval_collectBalanced, rawRowCheck16717]

def rawRow16718 : Integer.Sparse Key := [(key2268, 4), (key1989, 4), (key2294, 4), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2234, -2), (key2272, -2), (key1989, -2), (key2294, -2), (key1994, -2), (key2259, -2), (key2272, 4), (key2003, 4), (key2294, 4)]

theorem rawRowCheck16718 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form0 = rawRow16718 := by decide +kernel

def row16718 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16718 : row16718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16718 := by decide +kernel

theorem rowEval16718 (x : Key → ℝ) : Integer.Sparse.eval row16718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16718, Integer.Sparse.eval_collectBalanced, rawRowCheck16718]

def rawRow16719 : Integer.Sparse Key := [(key2268, 4), (key2294, 4), (key1989, 4), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, -2), (key2234, -2), (key2294, -2), (key1989, -2), (key2259, -2), (key1994, -2), (key2272, 4), (key2294, 4), (key2003, 4)]

theorem rawRowCheck16719 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form0 = rawRow16719 := by decide +kernel

def row16719 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16719 : row16719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16719 := by decide +kernel

theorem rowEval16719 (x : Key → ℝ) : Integer.Sparse.eval row16719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16719, Integer.Sparse.eval_collectBalanced, rawRowCheck16719]

def rawRow16720 : Integer.Sparse Key := [(key2294, 4), (key1989, 4), (key2268, 4), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2259, -2), (key2294, -2), (key1994, -2), (key2272, -2), (key1989, -2), (key2234, -2), (key2294, 4), (key2003, 4), (key2272, 4)]

theorem rawRowCheck16720 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form0 = rawRow16720 := by decide +kernel

def row16720 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16720 : row16720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16720 := by decide +kernel

theorem rowEval16720 (x : Key → ℝ) : Integer.Sparse.eval row16720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16720, Integer.Sparse.eval_collectBalanced, rawRowCheck16720]

def rawRow16721 : Integer.Sparse Key := [(key2294, 4), (key2268, 4), (key1989, 4), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, -2), (key2259, -2), (key2272, -2), (key1994, -2), (key2234, -2), (key1989, -2), (key2294, 4), (key2272, 4), (key2003, 4)]

theorem rawRowCheck16721 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form0 = rawRow16721 := by decide +kernel

def row16721 : Integer.Sparse Key := [(key1989, 2), (key1994, -2), (key1999, -2), (key2003, 2), (key2234, -2), (key2259, -2), (key2268, 2), (key2272, 2), (key2294, 4), (key2324, -2), (key2336, -2)]

theorem rowCheck16721 : row16721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16721 := by decide +kernel

theorem rowEval16721 (x : Key → ℝ) : Integer.Sparse.eval row16721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16721, Integer.Sparse.eval_collectBalanced, rawRowCheck16721]

def rawRow16722 : Integer.Sparse Key := [(key1999, 4), (key1999, 4), (key2336, 4), (key1989, -2), (key2003, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key2294, -2), (key1989, -2), (key2003, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key2294, -2), (key1994, 4), (key1994, 4), (key2259, 4)]

theorem rawRowCheck16722 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form0 = rawRow16722 := by decide +kernel

def row16722 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

theorem rowCheck16722 : row16722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16722 := by decide +kernel

theorem rowEval16722 (x : Key → ℝ) : Integer.Sparse.eval row16722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16722, Integer.Sparse.eval_collectBalanced, rawRowCheck16722]

def rawRow16723 : Integer.Sparse Key := [(key1999, 4), (key2336, 4), (key1999, 4), (key2003, -2), (key1989, -2), (key2294, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key2003, -2), (key1989, -2), (key2294, -2), (key1989, -2), (key2294, -2), (key2003, -2), (key1994, 4), (key2259, 4), (key1994, 4)]

theorem rawRowCheck16723 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form0 = rawRow16723 := by decide +kernel

def row16723 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

theorem rowCheck16723 : row16723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16723 := by decide +kernel

theorem rowEval16723 (x : Key → ℝ) : Integer.Sparse.eval row16723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16723, Integer.Sparse.eval_collectBalanced, rawRowCheck16723]

def rawRow16724 : Integer.Sparse Key := [(key2336, 4), (key1999, 4), (key1999, 4), (key2294, -2), (key2294, -2), (key2003, -2), (key2003, -2), (key1989, -2), (key1989, -2), (key2294, -2), (key2294, -2), (key2003, -2), (key2003, -2), (key1989, -2), (key1989, -2), (key2259, 4), (key1994, 4), (key1994, 4)]

theorem rawRowCheck16724 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form0 = rawRow16724 := by decide +kernel

def row16724 : Integer.Sparse Key := [(key1989, -8), (key1994, 8), (key1999, 8), (key2003, -8), (key2259, 4), (key2294, -8), (key2336, 4)]

theorem rowCheck16724 : row16724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16724 := by decide +kernel

theorem rowEval16724 (x : Key → ℝ) : Integer.Sparse.eval row16724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16724, Integer.Sparse.eval_collectBalanced, rawRowCheck16724]

def rawRow16725 : Integer.Sparse Key := [(key702, -2), (key706, -2), (key706, -2), (key722, 6), (key702, -2), (key706, -2), (key706, -2), (key856, 2), (key860, 2), (key856, 2), (key883, 2), (key860, 2), (key883, 2), (key922, -2), (key922, -2), (key939, -2), (key722, 6), (key922, -2), (key922, -2), (key939, -2)]

theorem rawRowCheck16725 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form1 = rawRow16725 := by decide +kernel

def row16725 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

theorem rowCheck16725 : row16725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16725 := by decide +kernel

theorem rowEval16725 (x : Key → ℝ) : Integer.Sparse.eval row16725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16725, Integer.Sparse.eval_collectBalanced, rawRowCheck16725]

def rawRow16726 : Integer.Sparse Key := [(key706, -2), (key702, -2), (key706, -2), (key722, 6), (key706, -2), (key702, -2), (key706, -2), (key860, 2), (key856, 2), (key883, 2), (key856, 2), (key883, 2), (key860, 2), (key922, -2), (key939, -2), (key922, -2), (key722, 6), (key922, -2), (key939, -2), (key922, -2)]

theorem rawRowCheck16726 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form1 = rawRow16726 := by decide +kernel

def row16726 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

theorem rowCheck16726 : row16726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16726 := by decide +kernel

theorem rowEval16726 (x : Key → ℝ) : Integer.Sparse.eval row16726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16726, Integer.Sparse.eval_collectBalanced, rawRowCheck16726]

def rawRow16727 : Integer.Sparse Key := [(key706, -2), (key706, -2), (key702, -2), (key722, 6), (key706, -2), (key706, -2), (key702, -2), (key883, 2), (key883, 2), (key860, 2), (key860, 2), (key856, 2), (key856, 2), (key939, -2), (key922, -2), (key922, -2), (key722, 6), (key939, -2), (key922, -2), (key922, -2)]

theorem rawRowCheck16727 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form1 = rawRow16727 := by decide +kernel

def row16727 : Integer.Sparse Key := [(key702, -4), (key706, -8), (key722, 12), (key856, 4), (key860, 4), (key883, 4), (key922, -8), (key939, -4)]

theorem rowCheck16727 : row16727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16727 := by decide +kernel

theorem rowEval16727 (x : Key → ℝ) : Integer.Sparse.eval row16727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16727, Integer.Sparse.eval_collectBalanced, rawRowCheck16727]

def rawRow16728 : Integer.Sparse Key := [(key702, -2), (key706, -2), (key722, -2), (key706, 6), (key856, -2), (key860, -2), (key922, -2), (key702, 2), (key706, 2), (key856, 2), (key883, 2), (key922, 2), (key939, 2), (key706, -2), (key860, -2), (key883, -2), (key922, 6), (key722, -2), (key922, -2), (key939, -2)]

theorem rawRowCheck16728 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form1 = rawRow16728 := by decide +kernel

def row16728 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16728 : row16728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16728 := by decide +kernel

theorem rowEval16728 (x : Key → ℝ) : Integer.Sparse.eval row16728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16728, Integer.Sparse.eval_collectBalanced, rawRowCheck16728]

def rawRow16729 : Integer.Sparse Key := [(key706, -2), (key702, -2), (key722, -2), (key706, 6), (key860, -2), (key856, -2), (key922, -2), (key706, 2), (key702, 2), (key883, 2), (key856, 2), (key939, 2), (key922, 2), (key706, -2), (key883, -2), (key860, -2), (key922, 6), (key722, -2), (key939, -2), (key922, -2)]

theorem rawRowCheck16729 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form1 = rawRow16729 := by decide +kernel

def row16729 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16729 : row16729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16729 := by decide +kernel

theorem rowEval16729 (x : Key → ℝ) : Integer.Sparse.eval row16729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16729, Integer.Sparse.eval_collectBalanced, rawRowCheck16729]

def rawRow16730 : Integer.Sparse Key := [(key702, -2), (key722, -2), (key706, -2), (key706, 6), (key856, -2), (key922, -2), (key860, -2), (key856, 2), (key922, 2), (key702, 2), (key939, 2), (key706, 2), (key883, 2), (key860, -2), (key706, -2), (key883, -2), (key922, 6), (key922, -2), (key722, -2), (key939, -2)]

theorem rawRowCheck16730 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form1 = rawRow16730 := by decide +kernel

def row16730 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16730 : row16730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16730 := by decide +kernel

theorem rowEval16730 (x : Key → ℝ) : Integer.Sparse.eval row16730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16730, Integer.Sparse.eval_collectBalanced, rawRowCheck16730]

def rawRow16731 : Integer.Sparse Key := [(key722, -2), (key702, -2), (key706, -2), (key706, 6), (key922, -2), (key856, -2), (key860, -2), (key922, 2), (key856, 2), (key939, 2), (key702, 2), (key883, 2), (key706, 2), (key860, -2), (key883, -2), (key706, -2), (key922, 6), (key922, -2), (key939, -2), (key722, -2)]

theorem rawRowCheck16731 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form1 = rawRow16731 := by decide +kernel

def row16731 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16731 : row16731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16731 := by decide +kernel

theorem rowEval16731 (x : Key → ℝ) : Integer.Sparse.eval row16731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16731, Integer.Sparse.eval_collectBalanced, rawRowCheck16731]

def rawRow16732 : Integer.Sparse Key := [(key706, -2), (key722, -2), (key702, -2), (key706, 6), (key860, -2), (key922, -2), (key856, -2), (key883, 2), (key939, 2), (key706, 2), (key922, 2), (key702, 2), (key856, 2), (key883, -2), (key706, -2), (key860, -2), (key922, 6), (key939, -2), (key722, -2), (key922, -2)]

theorem rawRowCheck16732 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form1 = rawRow16732 := by decide +kernel

def row16732 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16732 : row16732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16732 := by decide +kernel

theorem rowEval16732 (x : Key → ℝ) : Integer.Sparse.eval row16732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16732, Integer.Sparse.eval_collectBalanced, rawRowCheck16732]

def rawRow16733 : Integer.Sparse Key := [(key722, -2), (key706, -2), (key702, -2), (key706, 6), (key922, -2), (key860, -2), (key856, -2), (key939, 2), (key883, 2), (key922, 2), (key706, 2), (key856, 2), (key702, 2), (key883, -2), (key860, -2), (key706, -2), (key922, 6), (key939, -2), (key922, -2), (key722, -2)]

theorem rawRowCheck16733 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form1 = rawRow16733 := by decide +kernel

def row16733 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16733 : row16733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16733 := by decide +kernel

theorem rowEval16733 (x : Key → ℝ) : Integer.Sparse.eval row16733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16733, Integer.Sparse.eval_collectBalanced, rawRowCheck16733]

def rawRow16734 : Integer.Sparse Key := [(key856, -2), (key860, -2), (key922, -2), (key922, 6), (key702, -2), (key706, -2), (key722, -2), (key702, 2), (key706, 2), (key856, 2), (key883, 2), (key922, 2), (key939, 2), (key722, -2), (key922, -2), (key939, -2), (key706, 6), (key706, -2), (key860, -2), (key883, -2)]

theorem rawRowCheck16734 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form1 = rawRow16734 := by decide +kernel

def row16734 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16734 : row16734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16734 := by decide +kernel

theorem rowEval16734 (x : Key → ℝ) : Integer.Sparse.eval row16734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16734, Integer.Sparse.eval_collectBalanced, rawRowCheck16734]

def rawRow16735 : Integer.Sparse Key := [(key860, -2), (key856, -2), (key922, -2), (key922, 6), (key706, -2), (key702, -2), (key722, -2), (key706, 2), (key702, 2), (key883, 2), (key856, 2), (key939, 2), (key922, 2), (key722, -2), (key939, -2), (key922, -2), (key706, 6), (key706, -2), (key883, -2), (key860, -2)]

theorem rawRowCheck16735 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form1 = rawRow16735 := by decide +kernel

def row16735 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16735 : row16735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16735 := by decide +kernel

theorem rowEval16735 (x : Key → ℝ) : Integer.Sparse.eval row16735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16735, Integer.Sparse.eval_collectBalanced, rawRowCheck16735]

def rawRow16736 : Integer.Sparse Key := [(key856, -2), (key922, -2), (key860, -2), (key922, 6), (key702, -2), (key722, -2), (key706, -2), (key856, 2), (key922, 2), (key702, 2), (key939, 2), (key706, 2), (key883, 2), (key922, -2), (key722, -2), (key939, -2), (key706, 6), (key860, -2), (key706, -2), (key883, -2)]

theorem rawRowCheck16736 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form1 = rawRow16736 := by decide +kernel

def row16736 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16736 : row16736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16736 := by decide +kernel

theorem rowEval16736 (x : Key → ℝ) : Integer.Sparse.eval row16736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16736, Integer.Sparse.eval_collectBalanced, rawRowCheck16736]

def rawRow16737 : Integer.Sparse Key := [(key922, -2), (key856, -2), (key860, -2), (key922, 6), (key722, -2), (key702, -2), (key706, -2), (key922, 2), (key856, 2), (key939, 2), (key702, 2), (key883, 2), (key706, 2), (key922, -2), (key939, -2), (key722, -2), (key706, 6), (key860, -2), (key883, -2), (key706, -2)]

theorem rawRowCheck16737 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form1 = rawRow16737 := by decide +kernel

def row16737 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16737 : row16737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16737 := by decide +kernel

theorem rowEval16737 (x : Key → ℝ) : Integer.Sparse.eval row16737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16737, Integer.Sparse.eval_collectBalanced, rawRowCheck16737]

def rawRow16738 : Integer.Sparse Key := [(key860, -2), (key922, -2), (key856, -2), (key922, 6), (key706, -2), (key722, -2), (key702, -2), (key883, 2), (key939, 2), (key706, 2), (key922, 2), (key702, 2), (key856, 2), (key939, -2), (key722, -2), (key922, -2), (key706, 6), (key883, -2), (key706, -2), (key860, -2)]

theorem rawRowCheck16738 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form1 = rawRow16738 := by decide +kernel

def row16738 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16738 : row16738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16738 := by decide +kernel

theorem rowEval16738 (x : Key → ℝ) : Integer.Sparse.eval row16738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck16738, Integer.Sparse.eval_collectBalanced, rawRowCheck16738]

def rawRow16739 : Integer.Sparse Key := [(key922, -2), (key860, -2), (key856, -2), (key922, 6), (key722, -2), (key706, -2), (key702, -2), (key939, 2), (key883, 2), (key922, 2), (key706, 2), (key856, 2), (key702, 2), (key939, -2), (key922, -2), (key722, -2), (key706, 6), (key883, -2), (key860, -2), (key706, -2)]

theorem rawRowCheck16739 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form1 = rawRow16739 := by decide +kernel

def row16739 : Integer.Sparse Key := [(key706, 4), (key722, -4), (key860, -4), (key922, 4)]

theorem rowCheck16739 : row16739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16739 := by decide +kernel

theorem rowEval16739 (x : Key → ℝ) : Integer.Sparse.eval row16739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16739, Integer.Sparse.eval_collectBalanced, rawRowCheck16739]

def rawRow16740 : Integer.Sparse Key := [(key856, -2), (key922, -2), (key922, -2), (key860, 6), (key856, -2), (key922, -2), (key922, -2), (key702, 2), (key722, 2), (key702, 2), (key939, 2), (key722, 2), (key939, 2), (key706, -2), (key706, -2), (key883, -2), (key860, 6), (key706, -2), (key706, -2), (key883, -2)]

theorem rawRowCheck16740 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form1 = rawRow16740 := by decide +kernel

def row16740 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

theorem rowCheck16740 : row16740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16740 := by decide +kernel

theorem rowEval16740 (x : Key → ℝ) : Integer.Sparse.eval row16740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16740, Integer.Sparse.eval_collectBalanced, rawRowCheck16740]

def rawRow16741 : Integer.Sparse Key := [(key922, -2), (key856, -2), (key922, -2), (key860, 6), (key922, -2), (key856, -2), (key922, -2), (key722, 2), (key702, 2), (key939, 2), (key702, 2), (key939, 2), (key722, 2), (key706, -2), (key883, -2), (key706, -2), (key860, 6), (key706, -2), (key883, -2), (key706, -2)]

theorem rawRowCheck16741 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form1 = rawRow16741 := by decide +kernel

def row16741 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

theorem rowCheck16741 : row16741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16741 := by decide +kernel

theorem rowEval16741 (x : Key → ℝ) : Integer.Sparse.eval row16741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16741, Integer.Sparse.eval_collectBalanced, rawRowCheck16741]

def rawRow16742 : Integer.Sparse Key := [(key922, -2), (key922, -2), (key856, -2), (key860, 6), (key922, -2), (key922, -2), (key856, -2), (key939, 2), (key939, 2), (key722, 2), (key722, 2), (key702, 2), (key702, 2), (key883, -2), (key706, -2), (key706, -2), (key860, 6), (key883, -2), (key706, -2), (key706, -2)]

theorem rawRowCheck16742 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form1 = rawRow16742 := by decide +kernel

def row16742 : Integer.Sparse Key := [(key702, 4), (key706, -8), (key722, 4), (key856, -4), (key860, 12), (key883, -4), (key922, -8), (key939, 4)]

theorem rowCheck16742 : row16742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16742 := by decide +kernel

theorem rowEval16742 (x : Key → ℝ) : Integer.Sparse.eval row16742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck16742, Integer.Sparse.eval_collectBalanced, rawRowCheck16742]

def rawRow16743 : Integer.Sparse Key := [(key1986, -2), (key1990, -2), (key1990, -2), (key2007, 6), (key1986, -2), (key1990, -2), (key1990, -2), (key2231, 2), (key2235, 2), (key2231, 2), (key2256, 2), (key2235, 2), (key2256, 2), (key2300, -2), (key2300, -2), (key2313, -2), (key2007, 6), (key2300, -2), (key2300, -2), (key2313, -2)]

theorem rawRowCheck16743 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form2 = rawRow16743 := by decide +kernel

def row16743 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

theorem rowCheck16743 : row16743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16743 := by decide +kernel

theorem rowEval16743 (x : Key → ℝ) : Integer.Sparse.eval row16743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16743, Integer.Sparse.eval_collectBalanced, rawRowCheck16743]

def rawRow16744 : Integer.Sparse Key := [(key1990, -2), (key1986, -2), (key1990, -2), (key2007, 6), (key1990, -2), (key1986, -2), (key1990, -2), (key2235, 2), (key2231, 2), (key2256, 2), (key2231, 2), (key2256, 2), (key2235, 2), (key2300, -2), (key2313, -2), (key2300, -2), (key2007, 6), (key2300, -2), (key2313, -2), (key2300, -2)]

theorem rawRowCheck16744 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form2 = rawRow16744 := by decide +kernel

def row16744 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

theorem rowCheck16744 : row16744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16744 := by decide +kernel

theorem rowEval16744 (x : Key → ℝ) : Integer.Sparse.eval row16744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16744, Integer.Sparse.eval_collectBalanced, rawRowCheck16744]

def rawRow16745 : Integer.Sparse Key := [(key1990, -2), (key1990, -2), (key1986, -2), (key2007, 6), (key1990, -2), (key1990, -2), (key1986, -2), (key2256, 2), (key2256, 2), (key2235, 2), (key2235, 2), (key2231, 2), (key2231, 2), (key2313, -2), (key2300, -2), (key2300, -2), (key2007, 6), (key2313, -2), (key2300, -2), (key2300, -2)]

theorem rawRowCheck16745 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form2 = rawRow16745 := by decide +kernel

def row16745 : Integer.Sparse Key := [(key1986, -4), (key1990, -8), (key2007, 12), (key2231, 4), (key2235, 4), (key2256, 4), (key2300, -8), (key2313, -4)]

theorem rowCheck16745 : row16745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16745 := by decide +kernel

theorem rowEval16745 (x : Key → ℝ) : Integer.Sparse.eval row16745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16745, Integer.Sparse.eval_collectBalanced, rawRowCheck16745]

def rawRow16746 : Integer.Sparse Key := [(key1986, -2), (key1990, -2), (key2007, -2), (key1990, 6), (key2231, -2), (key2235, -2), (key2300, -2), (key1986, 2), (key1990, 2), (key2231, 2), (key2256, 2), (key2300, 2), (key2313, 2), (key1990, -2), (key2235, -2), (key2256, -2), (key2300, 6), (key2007, -2), (key2300, -2), (key2313, -2)]

theorem rawRowCheck16746 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form2 = rawRow16746 := by decide +kernel

def row16746 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16746 : row16746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16746 := by decide +kernel

theorem rowEval16746 (x : Key → ℝ) : Integer.Sparse.eval row16746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16746, Integer.Sparse.eval_collectBalanced, rawRowCheck16746]

def rawRow16747 : Integer.Sparse Key := [(key1990, -2), (key1986, -2), (key2007, -2), (key1990, 6), (key2235, -2), (key2231, -2), (key2300, -2), (key1990, 2), (key1986, 2), (key2256, 2), (key2231, 2), (key2313, 2), (key2300, 2), (key1990, -2), (key2256, -2), (key2235, -2), (key2300, 6), (key2007, -2), (key2313, -2), (key2300, -2)]

theorem rawRowCheck16747 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form2 = rawRow16747 := by decide +kernel

def row16747 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16747 : row16747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16747 := by decide +kernel

theorem rowEval16747 (x : Key → ℝ) : Integer.Sparse.eval row16747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16747, Integer.Sparse.eval_collectBalanced, rawRowCheck16747]

def rawRow16748 : Integer.Sparse Key := [(key1986, -2), (key2007, -2), (key1990, -2), (key1990, 6), (key2231, -2), (key2300, -2), (key2235, -2), (key2231, 2), (key2300, 2), (key1986, 2), (key2313, 2), (key1990, 2), (key2256, 2), (key2235, -2), (key1990, -2), (key2256, -2), (key2300, 6), (key2300, -2), (key2007, -2), (key2313, -2)]

theorem rawRowCheck16748 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form2 = rawRow16748 := by decide +kernel

def row16748 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16748 : row16748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16748 := by decide +kernel

theorem rowEval16748 (x : Key → ℝ) : Integer.Sparse.eval row16748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16748, Integer.Sparse.eval_collectBalanced, rawRowCheck16748]

def rawRow16749 : Integer.Sparse Key := [(key2007, -2), (key1986, -2), (key1990, -2), (key1990, 6), (key2300, -2), (key2231, -2), (key2235, -2), (key2300, 2), (key2231, 2), (key2313, 2), (key1986, 2), (key2256, 2), (key1990, 2), (key2235, -2), (key2256, -2), (key1990, -2), (key2300, 6), (key2300, -2), (key2313, -2), (key2007, -2)]

theorem rawRowCheck16749 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form2 = rawRow16749 := by decide +kernel

def row16749 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16749 : row16749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16749 := by decide +kernel

theorem rowEval16749 (x : Key → ℝ) : Integer.Sparse.eval row16749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16749, Integer.Sparse.eval_collectBalanced, rawRowCheck16749]

def rawRow16750 : Integer.Sparse Key := [(key1990, -2), (key2007, -2), (key1986, -2), (key1990, 6), (key2235, -2), (key2300, -2), (key2231, -2), (key2256, 2), (key2313, 2), (key1990, 2), (key2300, 2), (key1986, 2), (key2231, 2), (key2256, -2), (key1990, -2), (key2235, -2), (key2300, 6), (key2313, -2), (key2007, -2), (key2300, -2)]

theorem rawRowCheck16750 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form2 = rawRow16750 := by decide +kernel

def row16750 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16750 : row16750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16750 := by decide +kernel

theorem rowEval16750 (x : Key → ℝ) : Integer.Sparse.eval row16750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16750, Integer.Sparse.eval_collectBalanced, rawRowCheck16750]

def rawRow16751 : Integer.Sparse Key := [(key2007, -2), (key1990, -2), (key1986, -2), (key1990, 6), (key2300, -2), (key2235, -2), (key2231, -2), (key2313, 2), (key2256, 2), (key2300, 2), (key1990, 2), (key2231, 2), (key1986, 2), (key2256, -2), (key2235, -2), (key1990, -2), (key2300, 6), (key2313, -2), (key2300, -2), (key2007, -2)]

theorem rawRowCheck16751 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form2 = rawRow16751 := by decide +kernel

def row16751 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16751 : row16751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16751 := by decide +kernel

theorem rowEval16751 (x : Key → ℝ) : Integer.Sparse.eval row16751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16751, Integer.Sparse.eval_collectBalanced, rawRowCheck16751]

def rawRow16752 : Integer.Sparse Key := [(key2231, -2), (key2235, -2), (key2300, -2), (key2300, 6), (key1986, -2), (key1990, -2), (key2007, -2), (key1986, 2), (key1990, 2), (key2231, 2), (key2256, 2), (key2300, 2), (key2313, 2), (key2007, -2), (key2300, -2), (key2313, -2), (key1990, 6), (key1990, -2), (key2235, -2), (key2256, -2)]

theorem rawRowCheck16752 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form2 = rawRow16752 := by decide +kernel

def row16752 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16752 : row16752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16752 := by decide +kernel

theorem rowEval16752 (x : Key → ℝ) : Integer.Sparse.eval row16752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16752, Integer.Sparse.eval_collectBalanced, rawRowCheck16752]

def rawRow16753 : Integer.Sparse Key := [(key2235, -2), (key2231, -2), (key2300, -2), (key2300, 6), (key1990, -2), (key1986, -2), (key2007, -2), (key1990, 2), (key1986, 2), (key2256, 2), (key2231, 2), (key2313, 2), (key2300, 2), (key2007, -2), (key2313, -2), (key2300, -2), (key1990, 6), (key1990, -2), (key2256, -2), (key2235, -2)]

theorem rawRowCheck16753 : GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form2 = rawRow16753 := by decide +kernel

def row16753 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16753 : row16753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16753 := by decide +kernel

theorem rowEval16753 (x : Key → ℝ) : Integer.Sparse.eval row16753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16753, Integer.Sparse.eval_collectBalanced, rawRowCheck16753]

def rawRow16754 : Integer.Sparse Key := [(key2231, -2), (key2300, -2), (key2235, -2), (key2300, 6), (key1986, -2), (key2007, -2), (key1990, -2), (key2231, 2), (key2300, 2), (key1986, 2), (key2313, 2), (key1990, 2), (key2256, 2), (key2300, -2), (key2007, -2), (key2313, -2), (key1990, 6), (key2235, -2), (key1990, -2), (key2256, -2)]

theorem rawRowCheck16754 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form2 = rawRow16754 := by decide +kernel

def row16754 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16754 : row16754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16754 := by decide +kernel

theorem rowEval16754 (x : Key → ℝ) : Integer.Sparse.eval row16754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16754, Integer.Sparse.eval_collectBalanced, rawRowCheck16754]

def rawRow16755 : Integer.Sparse Key := [(key2300, -2), (key2231, -2), (key2235, -2), (key2300, 6), (key2007, -2), (key1986, -2), (key1990, -2), (key2300, 2), (key2231, 2), (key2313, 2), (key1986, 2), (key2256, 2), (key1990, 2), (key2300, -2), (key2313, -2), (key2007, -2), (key1990, 6), (key2235, -2), (key2256, -2), (key1990, -2)]

theorem rawRowCheck16755 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form2 = rawRow16755 := by decide +kernel

def row16755 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16755 : row16755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16755 := by decide +kernel

theorem rowEval16755 (x : Key → ℝ) : Integer.Sparse.eval row16755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16755, Integer.Sparse.eval_collectBalanced, rawRowCheck16755]

def rawRow16756 : Integer.Sparse Key := [(key2235, -2), (key2300, -2), (key2231, -2), (key2300, 6), (key1990, -2), (key2007, -2), (key1986, -2), (key2256, 2), (key2313, 2), (key1990, 2), (key2300, 2), (key1986, 2), (key2231, 2), (key2313, -2), (key2007, -2), (key2300, -2), (key1990, 6), (key2256, -2), (key1990, -2), (key2235, -2)]

theorem rawRowCheck16756 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form2 = rawRow16756 := by decide +kernel

def row16756 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16756 : row16756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16756 := by decide +kernel

theorem rowEval16756 (x : Key → ℝ) : Integer.Sparse.eval row16756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck16756, Integer.Sparse.eval_collectBalanced, rawRowCheck16756]

def rawRow16757 : Integer.Sparse Key := [(key2300, -2), (key2235, -2), (key2231, -2), (key2300, 6), (key2007, -2), (key1990, -2), (key1986, -2), (key2313, 2), (key2256, 2), (key2300, 2), (key1990, 2), (key2231, 2), (key1986, 2), (key2313, -2), (key2300, -2), (key2007, -2), (key1990, 6), (key2256, -2), (key2235, -2), (key1990, -2)]

theorem rawRowCheck16757 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form2 = rawRow16757 := by decide +kernel

def row16757 : Integer.Sparse Key := [(key1990, 4), (key2007, -4), (key2235, -4), (key2300, 4)]

theorem rowCheck16757 : row16757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16757 := by decide +kernel

theorem rowEval16757 (x : Key → ℝ) : Integer.Sparse.eval row16757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16757, Integer.Sparse.eval_collectBalanced, rawRowCheck16757]

def rawRow16758 : Integer.Sparse Key := [(key2231, -2), (key2300, -2), (key2300, -2), (key2235, 6), (key2231, -2), (key2300, -2), (key2300, -2), (key1986, 2), (key2007, 2), (key1986, 2), (key2313, 2), (key2007, 2), (key2313, 2), (key1990, -2), (key1990, -2), (key2256, -2), (key2235, 6), (key1990, -2), (key1990, -2), (key2256, -2)]

theorem rawRowCheck16758 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form2 = rawRow16758 := by decide +kernel

def row16758 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

theorem rowCheck16758 : row16758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16758 := by decide +kernel

theorem rowEval16758 (x : Key → ℝ) : Integer.Sparse.eval row16758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck16758, Integer.Sparse.eval_collectBalanced, rawRowCheck16758]

def rawRow16759 : Integer.Sparse Key := [(key2300, -2), (key2231, -2), (key2300, -2), (key2235, 6), (key2300, -2), (key2231, -2), (key2300, -2), (key2007, 2), (key1986, 2), (key2313, 2), (key1986, 2), (key2313, 2), (key2007, 2), (key1990, -2), (key2256, -2), (key1990, -2), (key2235, 6), (key1990, -2), (key2256, -2), (key1990, -2)]

theorem rawRowCheck16759 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form2 = rawRow16759 := by decide +kernel

def row16759 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

theorem rowCheck16759 : row16759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16759 := by decide +kernel

theorem rowEval16759 (x : Key → ℝ) : Integer.Sparse.eval row16759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16759, Integer.Sparse.eval_collectBalanced, rawRowCheck16759]

def rawRow16760 : Integer.Sparse Key := [(key2300, -2), (key2300, -2), (key2231, -2), (key2235, 6), (key2300, -2), (key2300, -2), (key2231, -2), (key2313, 2), (key2313, 2), (key2007, 2), (key2007, 2), (key1986, 2), (key1986, 2), (key2256, -2), (key1990, -2), (key1990, -2), (key2235, 6), (key2256, -2), (key1990, -2), (key1990, -2)]

theorem rawRowCheck16760 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form2 = rawRow16760 := by decide +kernel

def row16760 : Integer.Sparse Key := [(key1986, 4), (key1990, -8), (key2007, 4), (key2231, -4), (key2235, 12), (key2256, -4), (key2300, -8), (key2313, 4)]

theorem rowCheck16760 : row16760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16760 := by decide +kernel

theorem rowEval16760 (x : Key → ℝ) : Integer.Sparse.eval row16760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck16760, Integer.Sparse.eval_collectBalanced, rawRowCheck16760]

def rawRow16761 : Integer.Sparse Key := [(key2029, 6), (key2059, -2), (key2059, -2), (key2067, -2), (key2029, 6), (key2148, -2), (key2148, -2), (key2164, -2), (key2059, -2), (key2059, -2), (key2067, -2), (key2148, -2), (key2148, -2), (key2164, -2), (key2241, 2), (key2244, 2), (key2241, 2), (key2251, 2), (key2244, 2), (key2251, 2)]

theorem rawRowCheck16761 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form3 = rawRow16761 := by decide +kernel

def row16761 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

theorem rowCheck16761 : row16761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16761 := by decide +kernel

theorem rowEval16761 (x : Key → ℝ) : Integer.Sparse.eval row16761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16761, Integer.Sparse.eval_collectBalanced, rawRowCheck16761]

def rawRow16762 : Integer.Sparse Key := [(key2029, 6), (key2059, -2), (key2067, -2), (key2059, -2), (key2029, 6), (key2148, -2), (key2164, -2), (key2148, -2), (key2059, -2), (key2067, -2), (key2059, -2), (key2148, -2), (key2164, -2), (key2148, -2), (key2244, 2), (key2241, 2), (key2251, 2), (key2241, 2), (key2251, 2), (key2244, 2)]

theorem rawRowCheck16762 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form3 = rawRow16762 := by decide +kernel

def row16762 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

theorem rowCheck16762 : row16762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16762 := by decide +kernel

theorem rowEval16762 (x : Key → ℝ) : Integer.Sparse.eval row16762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16762, Integer.Sparse.eval_collectBalanced, rawRowCheck16762]

def rawRow16763 : Integer.Sparse Key := [(key2029, 6), (key2067, -2), (key2059, -2), (key2059, -2), (key2029, 6), (key2164, -2), (key2148, -2), (key2148, -2), (key2067, -2), (key2059, -2), (key2059, -2), (key2164, -2), (key2148, -2), (key2148, -2), (key2251, 2), (key2251, 2), (key2244, 2), (key2244, 2), (key2241, 2), (key2241, 2)]

theorem rawRowCheck16763 : GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form3 = rawRow16763 := by decide +kernel

def row16763 : Integer.Sparse Key := [(key2029, 12), (key2059, -8), (key2067, -4), (key2148, -8), (key2164, -4), (key2241, 4), (key2244, 4), (key2251, 4)]

theorem rowCheck16763 : row16763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16763 := by decide +kernel

theorem rowEval16763 (x : Key → ℝ) : Integer.Sparse.eval row16763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16763, Integer.Sparse.eval_collectBalanced, rawRowCheck16763]

def rawRow16764 : Integer.Sparse Key := [(key2059, 6), (key2029, -2), (key2059, -2), (key2067, -2), (key2148, 6), (key2029, -2), (key2148, -2), (key2164, -2), (key2148, -2), (key2241, -2), (key2244, -2), (key2059, -2), (key2241, -2), (key2251, -2), (key2059, 2), (key2067, 2), (key2148, 2), (key2164, 2), (key2244, 2), (key2251, 2)]

theorem rawRowCheck16764 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form3 = rawRow16764 := by decide +kernel

def row16764 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16764 : row16764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16764 := by decide +kernel

theorem rowEval16764 (x : Key → ℝ) : Integer.Sparse.eval row16764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16764, Integer.Sparse.eval_collectBalanced, rawRowCheck16764]

def rawRow16765 : Integer.Sparse Key := [(key2059, 6), (key2029, -2), (key2067, -2), (key2059, -2), (key2148, 6), (key2029, -2), (key2164, -2), (key2148, -2), (key2148, -2), (key2244, -2), (key2241, -2), (key2059, -2), (key2251, -2), (key2241, -2), (key2067, 2), (key2059, 2), (key2164, 2), (key2148, 2), (key2251, 2), (key2244, 2)]

theorem rawRowCheck16765 : GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form3 = rawRow16765 := by decide +kernel

def row16765 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16765 : row16765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16765 := by decide +kernel

theorem rowEval16765 (x : Key → ℝ) : Integer.Sparse.eval row16765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16765, Integer.Sparse.eval_collectBalanced, rawRowCheck16765]

def rawRow16766 : Integer.Sparse Key := [(key2059, 6), (key2059, -2), (key2029, -2), (key2067, -2), (key2148, 6), (key2148, -2), (key2029, -2), (key2164, -2), (key2241, -2), (key2148, -2), (key2244, -2), (key2241, -2), (key2059, -2), (key2251, -2), (key2148, 2), (key2244, 2), (key2059, 2), (key2251, 2), (key2067, 2), (key2164, 2)]

theorem rawRowCheck16766 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form3 = rawRow16766 := by decide +kernel

def row16766 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16766 : row16766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16766 := by decide +kernel

theorem rowEval16766 (x : Key → ℝ) : Integer.Sparse.eval row16766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck16766, Integer.Sparse.eval_collectBalanced, rawRowCheck16766]

def rawRow16767 : Integer.Sparse Key := [(key2059, 6), (key2059, -2), (key2067, -2), (key2029, -2), (key2148, 6), (key2148, -2), (key2164, -2), (key2029, -2), (key2241, -2), (key2244, -2), (key2148, -2), (key2241, -2), (key2251, -2), (key2059, -2), (key2244, 2), (key2148, 2), (key2251, 2), (key2059, 2), (key2164, 2), (key2067, 2)]

theorem rawRowCheck16767 : GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form3 = rawRow16767 := by decide +kernel

def row16767 : Integer.Sparse Key := [(key2029, -4), (key2059, 4), (key2148, 4), (key2241, -4)]

theorem rowCheck16767 : row16767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16767 := by decide +kernel

theorem rowEval16767 (x : Key → ℝ) : Integer.Sparse.eval row16767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, 0, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck16767, Integer.Sparse.eval_collectBalanced, rawRowCheck16767]

end MUB6.Certificate.GramRows

end OAI
