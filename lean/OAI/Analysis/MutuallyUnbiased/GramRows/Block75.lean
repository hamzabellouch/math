import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
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

def rawRow6528 : Integer.Sparse Key := [(key2642, -1), (key2654, -1), (key2640, 2), (key2642, -1), (key2654, -1), (key2619, 2), (key2649, 2), (key2616, -1), (key2632, -1), (key2640, 2), (key2616, -1), (key2632, -1), (key2729, 1), (key2748, 1), (key2726, -2), (key2729, 1), (key2748, 1), (key2674, -2), (key2738, -2), (key2671, 1), (key2706, 1), (key2726, -2), (key2671, 1), (key2706, 1), (key2832, -1), (key2905, -1), (key2829, 1), (key2870, 1), (key2796, 1), (key2898, 1), (key2794, -1), (key2860, -1), (key2832, -1), (key2905, -1), (key2796, 1), (key2898, 1), (key2829, 1), (key2870, 1), (key2794, -1), (key2860, -1)]

theorem rawRowCheck6528 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form2 = rawRow6528 := by decide +kernel

def row6528 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

theorem rowCheck6528 : row6528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6528 := by decide +kernel

theorem rowEval6528 (x : Key → ℝ) : Integer.Sparse.eval row6528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6528, Integer.Sparse.eval_collectBalanced, rawRowCheck6528]

def rawRow6529 : Integer.Sparse Key := [(key2654, -1), (key2642, -1), (key2640, 2), (key2654, -1), (key2642, -1), (key2649, 2), (key2619, 2), (key2632, -1), (key2616, -1), (key2640, 2), (key2632, -1), (key2616, -1), (key2748, 1), (key2729, 1), (key2726, -2), (key2748, 1), (key2729, 1), (key2738, -2), (key2674, -2), (key2706, 1), (key2671, 1), (key2726, -2), (key2706, 1), (key2671, 1), (key2905, -1), (key2832, -1), (key2870, 1), (key2829, 1), (key2898, 1), (key2796, 1), (key2860, -1), (key2794, -1), (key2905, -1), (key2832, -1), (key2898, 1), (key2796, 1), (key2870, 1), (key2829, 1), (key2860, -1), (key2794, -1)]

theorem rawRowCheck6529 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form2 = rawRow6529 := by decide +kernel

def row6529 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

theorem rowCheck6529 : row6529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6529 := by decide +kernel

theorem rowEval6529 (x : Key → ℝ) : Integer.Sparse.eval row6529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6529, Integer.Sparse.eval_collectBalanced, rawRowCheck6529]

def rawRow6530 : Integer.Sparse Key := [(key2729, -1), (key2748, -1), (key2726, 2), (key2883, -1), (key2913, -1), (key2832, 2), (key2905, 2), (key2829, -1), (key2870, -1), (key2992, 2), (key2961, -1), (key2984, -1), (key2642, 1), (key2654, 1), (key2640, -2), (key2883, 1), (key2913, 1), (key2796, -2), (key2898, -2), (key2794, 1), (key2860, 1), (key2992, -2), (key2944, 1), (key2977, 1), (key2619, -1), (key2649, -1), (key2616, 1), (key2632, 1), (key2674, 1), (key2738, 1), (key2671, -1), (key2706, -1), (key2832, -1), (key2905, -1), (key2796, 1), (key2898, 1), (key2961, 1), (key2984, 1), (key2944, -1), (key2977, -1)]

theorem rawRowCheck6530 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form2 = rawRow6530 := by decide +kernel

def row6530 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6530 : row6530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6530 := by decide +kernel

theorem rowEval6530 (x : Key → ℝ) : Integer.Sparse.eval row6530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6530, Integer.Sparse.eval_collectBalanced, rawRowCheck6530]

def rawRow6531 : Integer.Sparse Key := [(key2748, -1), (key2729, -1), (key2726, 2), (key2913, -1), (key2883, -1), (key2905, 2), (key2832, 2), (key2870, -1), (key2829, -1), (key2992, 2), (key2984, -1), (key2961, -1), (key2654, 1), (key2642, 1), (key2640, -2), (key2913, 1), (key2883, 1), (key2898, -2), (key2796, -2), (key2860, 1), (key2794, 1), (key2992, -2), (key2977, 1), (key2944, 1), (key2649, -1), (key2619, -1), (key2632, 1), (key2616, 1), (key2738, 1), (key2674, 1), (key2706, -1), (key2671, -1), (key2905, -1), (key2832, -1), (key2898, 1), (key2796, 1), (key2984, 1), (key2961, 1), (key2977, -1), (key2944, -1)]

theorem rawRowCheck6531 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form2 = rawRow6531 := by decide +kernel

def row6531 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6531 : row6531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6531 := by decide +kernel

theorem rowEval6531 (x : Key → ℝ) : Integer.Sparse.eval row6531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6531, Integer.Sparse.eval_collectBalanced, rawRowCheck6531]

def rawRow6532 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2832, 2), (key2870, -1), (key2984, -1), (key2726, 2), (key2992, 2), (key2729, -1), (key2883, -1), (key2905, 2), (key2748, -1), (key2913, -1), (key2794, 1), (key2944, 1), (key2796, -2), (key2860, 1), (key2977, 1), (key2640, -2), (key2992, -2), (key2642, 1), (key2883, 1), (key2898, -2), (key2654, 1), (key2913, 1), (key2671, -1), (key2944, -1), (key2674, 1), (key2796, 1), (key2616, 1), (key2961, 1), (key2619, -1), (key2832, -1), (key2706, -1), (key2977, -1), (key2632, 1), (key2984, 1), (key2738, 1), (key2898, 1), (key2649, -1), (key2905, -1)]

theorem rawRowCheck6532 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form2 = rawRow6532 := by decide +kernel

def row6532 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6532 : row6532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6532 := by decide +kernel

theorem rowEval6532 (x : Key → ℝ) : Integer.Sparse.eval row6532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6532, Integer.Sparse.eval_collectBalanced, rawRowCheck6532]

def rawRow6533 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2832, 2), (key2984, -1), (key2870, -1), (key2992, 2), (key2726, 2), (key2883, -1), (key2729, -1), (key2905, 2), (key2913, -1), (key2748, -1), (key2944, 1), (key2794, 1), (key2796, -2), (key2977, 1), (key2860, 1), (key2992, -2), (key2640, -2), (key2883, 1), (key2642, 1), (key2898, -2), (key2913, 1), (key2654, 1), (key2944, -1), (key2671, -1), (key2796, 1), (key2674, 1), (key2961, 1), (key2616, 1), (key2832, -1), (key2619, -1), (key2977, -1), (key2706, -1), (key2984, 1), (key2632, 1), (key2898, 1), (key2738, 1), (key2905, -1), (key2649, -1)]

theorem rawRowCheck6533 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form2 = rawRow6533 := by decide +kernel

def row6533 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6533 : row6533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6533 := by decide +kernel

theorem rowEval6533 (x : Key → ℝ) : Integer.Sparse.eval row6533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6533, Integer.Sparse.eval_collectBalanced, rawRowCheck6533]

def rawRow6534 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2905, 2), (key2829, -1), (key2961, -1), (key2726, 2), (key2992, 2), (key2748, -1), (key2913, -1), (key2832, 2), (key2729, -1), (key2883, -1), (key2860, 1), (key2977, 1), (key2898, -2), (key2794, 1), (key2944, 1), (key2640, -2), (key2992, -2), (key2654, 1), (key2913, 1), (key2796, -2), (key2642, 1), (key2883, 1), (key2706, -1), (key2977, -1), (key2738, 1), (key2898, 1), (key2632, 1), (key2984, 1), (key2649, -1), (key2905, -1), (key2671, -1), (key2944, -1), (key2616, 1), (key2961, 1), (key2674, 1), (key2796, 1), (key2619, -1), (key2832, -1)]

theorem rawRowCheck6534 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form2 = rawRow6534 := by decide +kernel

def row6534 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6534 : row6534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6534 := by decide +kernel

theorem rowEval6534 (x : Key → ℝ) : Integer.Sparse.eval row6534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6534, Integer.Sparse.eval_collectBalanced, rawRowCheck6534]

def rawRow6535 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2905, 2), (key2961, -1), (key2829, -1), (key2992, 2), (key2726, 2), (key2913, -1), (key2748, -1), (key2832, 2), (key2883, -1), (key2729, -1), (key2977, 1), (key2860, 1), (key2898, -2), (key2944, 1), (key2794, 1), (key2992, -2), (key2640, -2), (key2913, 1), (key2654, 1), (key2796, -2), (key2883, 1), (key2642, 1), (key2977, -1), (key2706, -1), (key2898, 1), (key2738, 1), (key2984, 1), (key2632, 1), (key2905, -1), (key2649, -1), (key2944, -1), (key2671, -1), (key2961, 1), (key2616, 1), (key2796, 1), (key2674, 1), (key2832, -1), (key2619, -1)]

theorem rawRowCheck6535 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form2 = rawRow6535 := by decide +kernel

def row6535 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6535 : row6535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6535 := by decide +kernel

theorem rowEval6535 (x : Key → ℝ) : Integer.Sparse.eval row6535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6535, Integer.Sparse.eval_collectBalanced, rawRowCheck6535]

def rawRow6536 : Integer.Sparse Key := [(key2883, -1), (key2913, -1), (key2992, 2), (key2729, -1), (key2748, -1), (key2832, 2), (key2905, 2), (key2961, -1), (key2984, -1), (key2726, 2), (key2829, -1), (key2870, -1), (key2883, 1), (key2913, 1), (key2992, -2), (key2642, 1), (key2654, 1), (key2796, -2), (key2898, -2), (key2944, 1), (key2977, 1), (key2640, -2), (key2794, 1), (key2860, 1), (key2832, -1), (key2905, -1), (key2961, 1), (key2984, 1), (key2796, 1), (key2898, 1), (key2944, -1), (key2977, -1), (key2619, -1), (key2649, -1), (key2674, 1), (key2738, 1), (key2616, 1), (key2632, 1), (key2671, -1), (key2706, -1)]

theorem rawRowCheck6536 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form2 = rawRow6536 := by decide +kernel

def row6536 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6536 : row6536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6536 := by decide +kernel

theorem rowEval6536 (x : Key → ℝ) : Integer.Sparse.eval row6536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6536, Integer.Sparse.eval_collectBalanced, rawRowCheck6536]

def rawRow6537 : Integer.Sparse Key := [(key2913, -1), (key2883, -1), (key2992, 2), (key2748, -1), (key2729, -1), (key2905, 2), (key2832, 2), (key2984, -1), (key2961, -1), (key2726, 2), (key2870, -1), (key2829, -1), (key2913, 1), (key2883, 1), (key2992, -2), (key2654, 1), (key2642, 1), (key2898, -2), (key2796, -2), (key2977, 1), (key2944, 1), (key2640, -2), (key2860, 1), (key2794, 1), (key2905, -1), (key2832, -1), (key2984, 1), (key2961, 1), (key2898, 1), (key2796, 1), (key2977, -1), (key2944, -1), (key2649, -1), (key2619, -1), (key2738, 1), (key2674, 1), (key2632, 1), (key2616, 1), (key2706, -1), (key2671, -1)]

theorem rawRowCheck6537 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form2 = rawRow6537 := by decide +kernel

def row6537 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6537 : row6537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6537 := by decide +kernel

theorem rowEval6537 (x : Key → ℝ) : Integer.Sparse.eval row6537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6537, Integer.Sparse.eval_collectBalanced, rawRowCheck6537]

def rawRow6538 : Integer.Sparse Key := [(key1004, -4), (key1008, 2), (key1008, 2), (key1021, 2), (key1021, 2), (key1023, -4), (key1039, 2), (key1043, -1), (key1043, -1), (key1117, 2), (key1195, -1), (key1195, -1), (key1129, -1), (key1129, -1), (key1201, -1), (key1201, -1), (key1202, 2), (key1202, 2), (key1078, -1), (key1078, -1), (key1081, 2), (key1157, -1), (key1157, -1), (key1214, 2), (key1214, 2), (key1216, -1), (key1216, -1), (key1176, 2), (key1225, -1), (key1225, -1)]

theorem rawRowCheck6538 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form3 = rawRow6538 := by decide +kernel

def row6538 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

theorem rowCheck6538 : row6538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6538 := by decide +kernel

theorem rowEval6538 (x : Key → ℝ) : Integer.Sparse.eval row6538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6538, Integer.Sparse.eval_collectBalanced, rawRowCheck6538]

def rawRow6539 : Integer.Sparse Key := [(key1008, -4), (key1004, 2), (key1008, 2), (key1021, 2), (key1023, 2), (key1021, -4), (key1043, 2), (key1039, -1), (key1043, -1), (key1195, 2), (key1117, -1), (key1195, -1), (key1201, -1), (key1202, -1), (key1129, -1), (key1202, -1), (key1129, 2), (key1201, 2), (key1078, -1), (key1081, -1), (key1078, 2), (key1214, -1), (key1216, -1), (key1157, 2), (key1216, 2), (key1157, -1), (key1214, -1), (key1225, 2), (key1176, -1), (key1225, -1)]

theorem rawRowCheck6539 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form3 = rawRow6539 := by decide +kernel

def row6539 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6539 : row6539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6539 := by decide +kernel

theorem rowEval6539 (x : Key → ℝ) : Integer.Sparse.eval row6539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6539, Integer.Sparse.eval_collectBalanced, rawRowCheck6539]

def rawRow6540 : Integer.Sparse Key := [(key1008, -4), (key1008, 2), (key1004, 2), (key1023, 2), (key1021, 2), (key1021, -4), (key1043, 2), (key1043, -1), (key1039, -1), (key1195, 2), (key1195, -1), (key1117, -1), (key1202, -1), (key1201, -1), (key1202, -1), (key1129, -1), (key1201, 2), (key1129, 2), (key1081, -1), (key1078, -1), (key1078, 2), (key1216, -1), (key1214, -1), (key1216, 2), (key1157, 2), (key1214, -1), (key1157, -1), (key1225, 2), (key1225, -1), (key1176, -1)]

theorem rawRowCheck6540 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form3 = rawRow6540 := by decide +kernel

def row6540 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6540 : row6540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6540 := by decide +kernel

theorem rowEval6540 (x : Key → ℝ) : Integer.Sparse.eval row6540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6540, Integer.Sparse.eval_collectBalanced, rawRowCheck6540]

def rawRow6541 : Integer.Sparse Key := [(key1004, -4), (key1021, 2), (key1021, 2), (key1008, 2), (key1008, 2), (key1023, -4), (key1117, 2), (key1129, -1), (key1129, -1), (key1039, 2), (key1201, -1), (key1201, -1), (key1043, -1), (key1043, -1), (key1195, -1), (key1195, -1), (key1202, 2), (key1202, 2), (key1157, -1), (key1157, -1), (key1176, 2), (key1078, -1), (key1078, -1), (key1214, 2), (key1214, 2), (key1225, -1), (key1225, -1), (key1081, 2), (key1216, -1), (key1216, -1)]

theorem rawRowCheck6541 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form3 = rawRow6541 := by decide +kernel

def row6541 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

theorem rowCheck6541 : row6541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6541 := by decide +kernel

theorem rowEval6541 (x : Key → ℝ) : Integer.Sparse.eval row6541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6541, Integer.Sparse.eval_collectBalanced, rawRowCheck6541]

def rawRow6542 : Integer.Sparse Key := [(key1021, -4), (key1004, 2), (key1021, 2), (key1008, 2), (key1023, 2), (key1008, -4), (key1129, 2), (key1117, -1), (key1129, -1), (key1201, 2), (key1039, -1), (key1201, -1), (key1195, -1), (key1202, -1), (key1043, -1), (key1202, -1), (key1043, 2), (key1195, 2), (key1157, -1), (key1176, -1), (key1157, 2), (key1214, -1), (key1225, -1), (key1078, 2), (key1225, 2), (key1078, -1), (key1214, -1), (key1216, 2), (key1081, -1), (key1216, -1)]

theorem rawRowCheck6542 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form3 = rawRow6542 := by decide +kernel

def row6542 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6542 : row6542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6542 := by decide +kernel

theorem rowEval6542 (x : Key → ℝ) : Integer.Sparse.eval row6542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6542, Integer.Sparse.eval_collectBalanced, rawRowCheck6542]

def rawRow6543 : Integer.Sparse Key := [(key1021, -4), (key1021, 2), (key1004, 2), (key1023, 2), (key1008, 2), (key1008, -4), (key1129, 2), (key1129, -1), (key1117, -1), (key1201, 2), (key1201, -1), (key1039, -1), (key1202, -1), (key1195, -1), (key1202, -1), (key1043, -1), (key1195, 2), (key1043, 2), (key1176, -1), (key1157, -1), (key1157, 2), (key1225, -1), (key1214, -1), (key1225, 2), (key1078, 2), (key1214, -1), (key1078, -1), (key1216, 2), (key1216, -1), (key1081, -1)]

theorem rawRowCheck6543 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form3 = rawRow6543 := by decide +kernel

def row6543 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6543 : row6543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6543 := by decide +kernel

theorem rowEval6543 (x : Key → ℝ) : Integer.Sparse.eval row6543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6543, Integer.Sparse.eval_collectBalanced, rawRowCheck6543]

def rawRow6544 : Integer.Sparse Key := [(key1008, -4), (key1021, 2), (key1023, 2), (key1004, 2), (key1008, 2), (key1021, -4), (key1195, 2), (key1201, -1), (key1202, -1), (key1043, 2), (key1129, -1), (key1202, -1), (key1039, -1), (key1043, -1), (key1117, -1), (key1195, -1), (key1129, 2), (key1201, 2), (key1214, -1), (key1216, -1), (key1225, 2), (key1078, -1), (key1081, -1), (key1157, 2), (key1216, 2), (key1176, -1), (key1225, -1), (key1078, 2), (key1157, -1), (key1214, -1)]

theorem rawRowCheck6544 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form3 = rawRow6544 := by decide +kernel

def row6544 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6544 : row6544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6544 := by decide +kernel

theorem rowEval6544 (x : Key → ℝ) : Integer.Sparse.eval row6544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6544, Integer.Sparse.eval_collectBalanced, rawRowCheck6544]

def rawRow6545 : Integer.Sparse Key := [(key1008, -4), (key1023, 2), (key1021, 2), (key1008, 2), (key1004, 2), (key1021, -4), (key1195, 2), (key1202, -1), (key1201, -1), (key1043, 2), (key1202, -1), (key1129, -1), (key1043, -1), (key1039, -1), (key1195, -1), (key1117, -1), (key1201, 2), (key1129, 2), (key1216, -1), (key1214, -1), (key1225, 2), (key1081, -1), (key1078, -1), (key1216, 2), (key1157, 2), (key1225, -1), (key1176, -1), (key1078, 2), (key1214, -1), (key1157, -1)]

theorem rawRowCheck6545 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form3 = rawRow6545 := by decide +kernel

def row6545 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6545 : row6545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6545 := by decide +kernel

theorem rowEval6545 (x : Key → ℝ) : Integer.Sparse.eval row6545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6545, Integer.Sparse.eval_collectBalanced, rawRowCheck6545]

def rawRow6546 : Integer.Sparse Key := [(key1021, -4), (key1008, 2), (key1023, 2), (key1004, 2), (key1021, 2), (key1008, -4), (key1201, 2), (key1195, -1), (key1202, -1), (key1129, 2), (key1043, -1), (key1202, -1), (key1117, -1), (key1129, -1), (key1039, -1), (key1201, -1), (key1043, 2), (key1195, 2), (key1214, -1), (key1225, -1), (key1216, 2), (key1157, -1), (key1176, -1), (key1078, 2), (key1225, 2), (key1081, -1), (key1216, -1), (key1157, 2), (key1078, -1), (key1214, -1)]

theorem rawRowCheck6546 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form3 = rawRow6546 := by decide +kernel

def row6546 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6546 : row6546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6546 := by decide +kernel

theorem rowEval6546 (x : Key → ℝ) : Integer.Sparse.eval row6546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6546, Integer.Sparse.eval_collectBalanced, rawRowCheck6546]

def rawRow6547 : Integer.Sparse Key := [(key1021, -4), (key1023, 2), (key1008, 2), (key1021, 2), (key1004, 2), (key1008, -4), (key1201, 2), (key1202, -1), (key1195, -1), (key1129, 2), (key1202, -1), (key1043, -1), (key1129, -1), (key1117, -1), (key1201, -1), (key1039, -1), (key1195, 2), (key1043, 2), (key1225, -1), (key1214, -1), (key1216, 2), (key1176, -1), (key1157, -1), (key1225, 2), (key1078, 2), (key1216, -1), (key1081, -1), (key1157, 2), (key1214, -1), (key1078, -1)]

theorem rawRowCheck6547 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form3 = rawRow6547 := by decide +kernel

def row6547 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6547 : row6547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6547 := by decide +kernel

theorem rowEval6547 (x : Key → ℝ) : Integer.Sparse.eval row6547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6547, Integer.Sparse.eval_collectBalanced, rawRowCheck6547]

def rawRow6548 : Integer.Sparse Key := [(key1023, -4), (key1008, 2), (key1021, 2), (key1008, 2), (key1021, 2), (key1004, -4), (key1202, 2), (key1195, -1), (key1201, -1), (key1202, 2), (key1043, -1), (key1129, -1), (key1195, -1), (key1201, -1), (key1043, -1), (key1129, -1), (key1039, 2), (key1117, 2), (key1216, -1), (key1225, -1), (key1214, 2), (key1216, -1), (key1225, -1), (key1081, 2), (key1176, 2), (key1078, -1), (key1157, -1), (key1214, 2), (key1078, -1), (key1157, -1)]

theorem rawRowCheck6548 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6548 := by decide +kernel

def row6548 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

theorem rowCheck6548 : row6548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6548 := by decide +kernel

theorem rowEval6548 (x : Key → ℝ) : Integer.Sparse.eval row6548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6548, Integer.Sparse.eval_collectBalanced, rawRowCheck6548]

def rawRow6549 : Integer.Sparse Key := [(key1023, -4), (key1021, 2), (key1008, 2), (key1021, 2), (key1008, 2), (key1004, -4), (key1202, 2), (key1201, -1), (key1195, -1), (key1202, 2), (key1129, -1), (key1043, -1), (key1201, -1), (key1195, -1), (key1129, -1), (key1043, -1), (key1117, 2), (key1039, 2), (key1225, -1), (key1216, -1), (key1214, 2), (key1225, -1), (key1216, -1), (key1176, 2), (key1081, 2), (key1157, -1), (key1078, -1), (key1214, 2), (key1157, -1), (key1078, -1)]

theorem rawRowCheck6549 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6549 := by decide +kernel

def row6549 : Integer.Sparse Key := [(key1004, -4), (key1008, 4), (key1021, 4), (key1023, -4), (key1039, 2), (key1043, -2), (key1078, -2), (key1081, 2), (key1117, 2), (key1129, -2), (key1157, -2), (key1176, 2), (key1195, -2), (key1201, -2), (key1202, 4), (key1214, 4), (key1216, -2), (key1225, -2)]

theorem rowCheck6549 : row6549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6549 := by decide +kernel

theorem rowEval6549 (x : Key → ℝ) : Integer.Sparse.eval row6549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6549, Integer.Sparse.eval_collectBalanced, rawRowCheck6549]

def rawRow6550 : Integer.Sparse Key := [(key1202, -4), (key1195, 2), (key1201, 2), (key1216, 2), (key1225, 2), (key1214, -4), (key1023, 2), (key1008, -1), (key1021, -1), (key1202, 2), (key1043, -1), (key1129, -1), (key1216, -1), (key1225, -1), (key1081, -1), (key1176, -1), (key1078, 2), (key1157, 2), (key1008, -1), (key1021, -1), (key1004, 2), (key1195, -1), (key1201, -1), (key1043, 2), (key1129, 2), (key1039, -1), (key1117, -1), (key1214, 2), (key1078, -1), (key1157, -1)]

theorem rawRowCheck6550 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form3 = rawRow6550 := by decide +kernel

def row6550 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6550 : row6550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6550 := by decide +kernel

theorem rowEval6550 (x : Key → ℝ) : Integer.Sparse.eval row6550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6550, Integer.Sparse.eval_collectBalanced, rawRowCheck6550]

def rawRow6551 : Integer.Sparse Key := [(key1202, -4), (key1201, 2), (key1195, 2), (key1225, 2), (key1216, 2), (key1214, -4), (key1023, 2), (key1021, -1), (key1008, -1), (key1202, 2), (key1129, -1), (key1043, -1), (key1225, -1), (key1216, -1), (key1176, -1), (key1081, -1), (key1157, 2), (key1078, 2), (key1021, -1), (key1008, -1), (key1004, 2), (key1201, -1), (key1195, -1), (key1129, 2), (key1043, 2), (key1117, -1), (key1039, -1), (key1214, 2), (key1157, -1), (key1078, -1)]

theorem rawRowCheck6551 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form3 = rawRow6551 := by decide +kernel

def row6551 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6551 : row6551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6551 := by decide +kernel

theorem rowEval6551 (x : Key → ℝ) : Integer.Sparse.eval row6551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6551, Integer.Sparse.eval_collectBalanced, rawRowCheck6551]

def rawRow6552 : Integer.Sparse Key := [(key1214, -4), (key1195, 2), (key1216, 2), (key1201, 2), (key1225, 2), (key1202, -4), (key1078, 2), (key1043, -1), (key1081, -1), (key1157, 2), (key1008, -1), (key1216, -1), (key1129, -1), (key1176, -1), (key1021, -1), (key1225, -1), (key1023, 2), (key1202, 2), (key1039, -1), (key1078, -1), (key1043, 2), (key1117, -1), (key1157, -1), (key1004, 2), (key1214, 2), (key1008, -1), (key1195, -1), (key1129, 2), (key1021, -1), (key1201, -1)]

theorem rawRowCheck6552 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form3 = rawRow6552 := by decide +kernel

def row6552 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6552 : row6552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6552 := by decide +kernel

theorem rowEval6552 (x : Key → ℝ) : Integer.Sparse.eval row6552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6552, Integer.Sparse.eval_collectBalanced, rawRowCheck6552]

def rawRow6553 : Integer.Sparse Key := [(key1214, -4), (key1216, 2), (key1195, 2), (key1225, 2), (key1201, 2), (key1202, -4), (key1078, 2), (key1081, -1), (key1043, -1), (key1157, 2), (key1216, -1), (key1008, -1), (key1176, -1), (key1129, -1), (key1225, -1), (key1021, -1), (key1202, 2), (key1023, 2), (key1078, -1), (key1039, -1), (key1043, 2), (key1157, -1), (key1117, -1), (key1214, 2), (key1004, 2), (key1195, -1), (key1008, -1), (key1129, 2), (key1201, -1), (key1021, -1)]

theorem rawRowCheck6553 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form3 = rawRow6553 := by decide +kernel

def row6553 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6553 : row6553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6553 := by decide +kernel

theorem rowEval6553 (x : Key → ℝ) : Integer.Sparse.eval row6553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6553, Integer.Sparse.eval_collectBalanced, rawRowCheck6553]

def rawRow6554 : Integer.Sparse Key := [(key1214, -4), (key1201, 2), (key1225, 2), (key1195, 2), (key1216, 2), (key1202, -4), (key1157, 2), (key1129, -1), (key1176, -1), (key1078, 2), (key1021, -1), (key1225, -1), (key1043, -1), (key1081, -1), (key1008, -1), (key1216, -1), (key1023, 2), (key1202, 2), (key1117, -1), (key1157, -1), (key1129, 2), (key1039, -1), (key1078, -1), (key1004, 2), (key1214, 2), (key1021, -1), (key1201, -1), (key1043, 2), (key1008, -1), (key1195, -1)]

theorem rawRowCheck6554 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form3 = rawRow6554 := by decide +kernel

def row6554 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6554 : row6554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6554 := by decide +kernel

theorem rowEval6554 (x : Key → ℝ) : Integer.Sparse.eval row6554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6554, Integer.Sparse.eval_collectBalanced, rawRowCheck6554]

def rawRow6555 : Integer.Sparse Key := [(key1214, -4), (key1225, 2), (key1201, 2), (key1216, 2), (key1195, 2), (key1202, -4), (key1157, 2), (key1176, -1), (key1129, -1), (key1078, 2), (key1225, -1), (key1021, -1), (key1081, -1), (key1043, -1), (key1216, -1), (key1008, -1), (key1202, 2), (key1023, 2), (key1157, -1), (key1117, -1), (key1129, 2), (key1078, -1), (key1039, -1), (key1214, 2), (key1004, 2), (key1201, -1), (key1021, -1), (key1043, 2), (key1195, -1), (key1008, -1)]

theorem rawRowCheck6555 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form3 = rawRow6555 := by decide +kernel

def row6555 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6555 : row6555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6555 := by decide +kernel

theorem rowEval6555 (x : Key → ℝ) : Integer.Sparse.eval row6555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6555, Integer.Sparse.eval_collectBalanced, rawRowCheck6555]

def rawRow6556 : Integer.Sparse Key := [(key1202, -4), (key1216, 2), (key1225, 2), (key1195, 2), (key1201, 2), (key1214, -4), (key1202, 2), (key1216, -1), (key1225, -1), (key1023, 2), (key1081, -1), (key1176, -1), (key1008, -1), (key1021, -1), (key1043, -1), (key1129, -1), (key1078, 2), (key1157, 2), (key1195, -1), (key1201, -1), (key1214, 2), (key1008, -1), (key1021, -1), (key1043, 2), (key1129, 2), (key1078, -1), (key1157, -1), (key1004, 2), (key1039, -1), (key1117, -1)]

theorem rawRowCheck6556 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form3 = rawRow6556 := by decide +kernel

def row6556 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6556 : row6556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6556 := by decide +kernel

theorem rowEval6556 (x : Key → ℝ) : Integer.Sparse.eval row6556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6556, Integer.Sparse.eval_collectBalanced, rawRowCheck6556]

def rawRow6557 : Integer.Sparse Key := [(key1202, -4), (key1225, 2), (key1216, 2), (key1201, 2), (key1195, 2), (key1214, -4), (key1202, 2), (key1225, -1), (key1216, -1), (key1023, 2), (key1176, -1), (key1081, -1), (key1021, -1), (key1008, -1), (key1129, -1), (key1043, -1), (key1157, 2), (key1078, 2), (key1201, -1), (key1195, -1), (key1214, 2), (key1021, -1), (key1008, -1), (key1129, 2), (key1043, 2), (key1157, -1), (key1078, -1), (key1004, 2), (key1117, -1), (key1039, -1)]

theorem rawRowCheck6557 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form3 = rawRow6557 := by decide +kernel

def row6557 : Integer.Sparse Key := [(key1004, 2), (key1008, -2), (key1021, -2), (key1023, 2), (key1039, -1), (key1043, 1), (key1078, 1), (key1081, -1), (key1117, -1), (key1129, 1), (key1157, 1), (key1176, -1), (key1195, 1), (key1201, 1), (key1202, -2), (key1214, -2), (key1216, 1), (key1225, 1)]

theorem rowCheck6557 : row6557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6557 := by decide +kernel

theorem rowEval6557 (x : Key → ℝ) : Integer.Sparse.eval row6557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6557, Integer.Sparse.eval_collectBalanced, rawRowCheck6557]

def rawRow6558 : Integer.Sparse Key := [(key2379, -4), (key2382, 2), (key2382, 2), (key2393, 2), (key2393, 2), (key2395, -4), (key2771, 2), (key2774, -1), (key2774, -1), (key2848, 2), (key2882, -1), (key2882, -1), (key2891, -1), (key2891, -1), (key2912, -1), (key2912, -1), (key2914, 2), (key2914, 2), (key2933, -1), (key2933, -1), (key2934, 2), (key2970, -1), (key2970, -1), (key2991, 2), (key2991, 2), (key2993, -1), (key2993, -1), (key2996, 2), (key3003, -1), (key3003, -1)]

theorem rawRowCheck6558 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form4 = rawRow6558 := by decide +kernel

def row6558 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

theorem rowCheck6558 : row6558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6558 := by decide +kernel

theorem rowEval6558 (x : Key → ℝ) : Integer.Sparse.eval row6558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6558, Integer.Sparse.eval_collectBalanced, rawRowCheck6558]

def rawRow6559 : Integer.Sparse Key := [(key2382, -4), (key2379, 2), (key2382, 2), (key2393, 2), (key2395, 2), (key2393, -4), (key2774, 2), (key2771, -1), (key2774, -1), (key2882, 2), (key2848, -1), (key2882, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2914, -1), (key2891, 2), (key2912, 2), (key2933, -1), (key2934, -1), (key2933, 2), (key2991, -1), (key2993, -1), (key2970, 2), (key2993, 2), (key2970, -1), (key2991, -1), (key3003, 2), (key2996, -1), (key3003, -1)]

theorem rawRowCheck6559 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form4 = rawRow6559 := by decide +kernel

def row6559 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6559 : row6559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6559 := by decide +kernel

theorem rowEval6559 (x : Key → ℝ) : Integer.Sparse.eval row6559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6559, Integer.Sparse.eval_collectBalanced, rawRowCheck6559]

def rawRow6560 : Integer.Sparse Key := [(key2382, -4), (key2382, 2), (key2379, 2), (key2395, 2), (key2393, 2), (key2393, -4), (key2774, 2), (key2774, -1), (key2771, -1), (key2882, 2), (key2882, -1), (key2848, -1), (key2914, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2912, 2), (key2891, 2), (key2934, -1), (key2933, -1), (key2933, 2), (key2993, -1), (key2991, -1), (key2993, 2), (key2970, 2), (key2991, -1), (key2970, -1), (key3003, 2), (key3003, -1), (key2996, -1)]

theorem rawRowCheck6560 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form4 = rawRow6560 := by decide +kernel

def row6560 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6560 : row6560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6560 := by decide +kernel

theorem rowEval6560 (x : Key → ℝ) : Integer.Sparse.eval row6560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6560, Integer.Sparse.eval_collectBalanced, rawRowCheck6560]

def rawRow6561 : Integer.Sparse Key := [(key2379, -4), (key2393, 2), (key2393, 2), (key2382, 2), (key2382, 2), (key2395, -4), (key2848, 2), (key2891, -1), (key2891, -1), (key2771, 2), (key2912, -1), (key2912, -1), (key2774, -1), (key2774, -1), (key2882, -1), (key2882, -1), (key2914, 2), (key2914, 2), (key2970, -1), (key2970, -1), (key2996, 2), (key2933, -1), (key2933, -1), (key2991, 2), (key2991, 2), (key3003, -1), (key3003, -1), (key2934, 2), (key2993, -1), (key2993, -1)]

theorem rawRowCheck6561 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form4 = rawRow6561 := by decide +kernel

def row6561 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

theorem rowCheck6561 : row6561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6561 := by decide +kernel

theorem rowEval6561 (x : Key → ℝ) : Integer.Sparse.eval row6561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6561, Integer.Sparse.eval_collectBalanced, rawRowCheck6561]

def rawRow6562 : Integer.Sparse Key := [(key2393, -4), (key2379, 2), (key2393, 2), (key2382, 2), (key2395, 2), (key2382, -4), (key2891, 2), (key2848, -1), (key2891, -1), (key2912, 2), (key2771, -1), (key2912, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2914, -1), (key2774, 2), (key2882, 2), (key2970, -1), (key2996, -1), (key2970, 2), (key2991, -1), (key3003, -1), (key2933, 2), (key3003, 2), (key2933, -1), (key2991, -1), (key2993, 2), (key2934, -1), (key2993, -1)]

theorem rawRowCheck6562 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form4 = rawRow6562 := by decide +kernel

def row6562 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6562 : row6562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6562 := by decide +kernel

theorem rowEval6562 (x : Key → ℝ) : Integer.Sparse.eval row6562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6562, Integer.Sparse.eval_collectBalanced, rawRowCheck6562]

def rawRow6563 : Integer.Sparse Key := [(key2393, -4), (key2393, 2), (key2379, 2), (key2395, 2), (key2382, 2), (key2382, -4), (key2891, 2), (key2891, -1), (key2848, -1), (key2912, 2), (key2912, -1), (key2771, -1), (key2914, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2882, 2), (key2774, 2), (key2996, -1), (key2970, -1), (key2970, 2), (key3003, -1), (key2991, -1), (key3003, 2), (key2933, 2), (key2991, -1), (key2933, -1), (key2993, 2), (key2993, -1), (key2934, -1)]

theorem rawRowCheck6563 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form4 = rawRow6563 := by decide +kernel

def row6563 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6563 : row6563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6563 := by decide +kernel

theorem rowEval6563 (x : Key → ℝ) : Integer.Sparse.eval row6563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6563, Integer.Sparse.eval_collectBalanced, rawRowCheck6563]

def rawRow6564 : Integer.Sparse Key := [(key2382, -4), (key2393, 2), (key2395, 2), (key2379, 2), (key2382, 2), (key2393, -4), (key2882, 2), (key2912, -1), (key2914, -1), (key2774, 2), (key2891, -1), (key2914, -1), (key2771, -1), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, 2), (key2991, -1), (key2993, -1), (key3003, 2), (key2933, -1), (key2934, -1), (key2970, 2), (key2993, 2), (key2996, -1), (key3003, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

theorem rawRowCheck6564 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow6564 := by decide +kernel

def row6564 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6564 : row6564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6564 := by decide +kernel

theorem rowEval6564 (x : Key → ℝ) : Integer.Sparse.eval row6564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6564, Integer.Sparse.eval_collectBalanced, rawRowCheck6564]

def rawRow6565 : Integer.Sparse Key := [(key2382, -4), (key2395, 2), (key2393, 2), (key2382, 2), (key2379, 2), (key2393, -4), (key2882, 2), (key2914, -1), (key2912, -1), (key2774, 2), (key2914, -1), (key2891, -1), (key2774, -1), (key2771, -1), (key2882, -1), (key2848, -1), (key2912, 2), (key2891, 2), (key2993, -1), (key2991, -1), (key3003, 2), (key2934, -1), (key2933, -1), (key2993, 2), (key2970, 2), (key3003, -1), (key2996, -1), (key2933, 2), (key2991, -1), (key2970, -1)]

theorem rawRowCheck6565 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow6565 := by decide +kernel

def row6565 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6565 : row6565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6565 := by decide +kernel

theorem rowEval6565 (x : Key → ℝ) : Integer.Sparse.eval row6565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6565, Integer.Sparse.eval_collectBalanced, rawRowCheck6565]

def rawRow6566 : Integer.Sparse Key := [(key2393, -4), (key2382, 2), (key2395, 2), (key2379, 2), (key2393, 2), (key2382, -4), (key2912, 2), (key2882, -1), (key2914, -1), (key2891, 2), (key2774, -1), (key2914, -1), (key2848, -1), (key2891, -1), (key2771, -1), (key2912, -1), (key2774, 2), (key2882, 2), (key2991, -1), (key3003, -1), (key2993, 2), (key2970, -1), (key2996, -1), (key2933, 2), (key3003, 2), (key2934, -1), (key2993, -1), (key2970, 2), (key2933, -1), (key2991, -1)]

theorem rawRowCheck6566 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow6566 := by decide +kernel

def row6566 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6566 : row6566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6566 := by decide +kernel

theorem rowEval6566 (x : Key → ℝ) : Integer.Sparse.eval row6566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6566, Integer.Sparse.eval_collectBalanced, rawRowCheck6566]

def rawRow6567 : Integer.Sparse Key := [(key2393, -4), (key2395, 2), (key2382, 2), (key2393, 2), (key2379, 2), (key2382, -4), (key2912, 2), (key2914, -1), (key2882, -1), (key2891, 2), (key2914, -1), (key2774, -1), (key2891, -1), (key2848, -1), (key2912, -1), (key2771, -1), (key2882, 2), (key2774, 2), (key3003, -1), (key2991, -1), (key2993, 2), (key2996, -1), (key2970, -1), (key3003, 2), (key2933, 2), (key2993, -1), (key2934, -1), (key2970, 2), (key2991, -1), (key2933, -1)]

theorem rawRowCheck6567 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow6567 := by decide +kernel

def row6567 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

theorem rowCheck6567 : row6567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6567 := by decide +kernel

theorem rowEval6567 (x : Key → ℝ) : Integer.Sparse.eval row6567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6567, Integer.Sparse.eval_collectBalanced, rawRowCheck6567]

def rawRow6568 : Integer.Sparse Key := [(key2395, -4), (key2382, 2), (key2393, 2), (key2382, 2), (key2393, 2), (key2379, -4), (key2914, 2), (key2882, -1), (key2912, -1), (key2914, 2), (key2774, -1), (key2891, -1), (key2882, -1), (key2912, -1), (key2774, -1), (key2891, -1), (key2771, 2), (key2848, 2), (key2993, -1), (key3003, -1), (key2991, 2), (key2993, -1), (key3003, -1), (key2934, 2), (key2996, 2), (key2933, -1), (key2970, -1), (key2991, 2), (key2933, -1), (key2970, -1)]

theorem rawRowCheck6568 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6568 := by decide +kernel

def row6568 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

theorem rowCheck6568 : row6568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6568 := by decide +kernel

theorem rowEval6568 (x : Key → ℝ) : Integer.Sparse.eval row6568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6568, Integer.Sparse.eval_collectBalanced, rawRowCheck6568]

def rawRow6569 : Integer.Sparse Key := [(key2395, -4), (key2393, 2), (key2382, 2), (key2393, 2), (key2382, 2), (key2379, -4), (key2914, 2), (key2912, -1), (key2882, -1), (key2914, 2), (key2891, -1), (key2774, -1), (key2912, -1), (key2882, -1), (key2891, -1), (key2774, -1), (key2848, 2), (key2771, 2), (key3003, -1), (key2993, -1), (key2991, 2), (key3003, -1), (key2993, -1), (key2996, 2), (key2934, 2), (key2970, -1), (key2933, -1), (key2991, 2), (key2970, -1), (key2933, -1)]

theorem rawRowCheck6569 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6569 := by decide +kernel

def row6569 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

theorem rowCheck6569 : row6569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6569 := by decide +kernel

theorem rowEval6569 (x : Key → ℝ) : Integer.Sparse.eval row6569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6569, Integer.Sparse.eval_collectBalanced, rawRowCheck6569]

def rawRow6570 : Integer.Sparse Key := [(key2545, -4), (key2539, 2), (key2544, 2), (key2557, 2), (key2565, 2), (key2555, -4), (key2395, 2), (key2382, -1), (key2393, -1), (key2545, 2), (key2410, -1), (key2483, -1), (key2557, -1), (key2565, -1), (key2445, -1), (key2526, -1), (key2441, 2), (key2507, 2), (key2382, -1), (key2393, -1), (key2379, 2), (key2882, -1), (key2912, -1), (key2774, 2), (key2891, 2), (key2771, -1), (key2848, -1), (key2991, 2), (key2933, -1), (key2970, -1)]

theorem rawRowCheck6570 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form4 = rawRow6570 := by decide +kernel

def row6570 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, -1), (key2441, 2), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2771, -1), (key2774, 2), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2933, -1), (key2970, -1), (key2991, 2)]

theorem rowCheck6570 : row6570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6570 := by decide +kernel

theorem rowEval6570 (x : Key → ℝ) : Integer.Sparse.eval row6570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6570, Integer.Sparse.eval_collectBalanced, rawRowCheck6570]

def rawRow6571 : Integer.Sparse Key := [(key2545, -4), (key2544, 2), (key2539, 2), (key2565, 2), (key2557, 2), (key2555, -4), (key2395, 2), (key2393, -1), (key2382, -1), (key2545, 2), (key2483, -1), (key2410, -1), (key2565, -1), (key2557, -1), (key2526, -1), (key2445, -1), (key2507, 2), (key2441, 2), (key2393, -1), (key2382, -1), (key2379, 2), (key2912, -1), (key2882, -1), (key2891, 2), (key2774, 2), (key2848, -1), (key2771, -1), (key2991, 2), (key2970, -1), (key2933, -1)]

theorem rawRowCheck6571 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form4 = rawRow6571 := by decide +kernel

def row6571 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, -1), (key2441, 2), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2771, -1), (key2774, 2), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2933, -1), (key2970, -1), (key2991, 2)]

theorem rowCheck6571 : row6571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6571 := by decide +kernel

theorem rowEval6571 (x : Key → ℝ) : Integer.Sparse.eval row6571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6571, Integer.Sparse.eval_collectBalanced, rawRowCheck6571]

def rawRow6572 : Integer.Sparse Key := [(key2555, -4), (key2539, 2), (key2557, 2), (key2544, 2), (key2565, 2), (key2545, -4), (key2441, 2), (key2410, -1), (key2445, -1), (key2507, 2), (key2382, -1), (key2557, -1), (key2483, -1), (key2526, -1), (key2393, -1), (key2565, -1), (key2395, 2), (key2545, 2), (key2407, -1), (key2441, -1), (key2410, 2), (key2848, -1), (key2970, -1), (key2592, 2), (key2991, 2), (key2595, -1), (key2882, -1), (key2891, 2), (key2602, -1), (key2912, -1)]

theorem rawRowCheck6572 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form4 = rawRow6572 := by decide +kernel

def row6572 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2970, -1), (key2991, 2)]

theorem rowCheck6572 : row6572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6572 := by decide +kernel

theorem rowEval6572 (x : Key → ℝ) : Integer.Sparse.eval row6572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6572, Integer.Sparse.eval_collectBalanced, rawRowCheck6572]

def rawRow6573 : Integer.Sparse Key := [(key2555, -4), (key2557, 2), (key2539, 2), (key2565, 2), (key2544, 2), (key2545, -4), (key2441, 2), (key2445, -1), (key2410, -1), (key2507, 2), (key2557, -1), (key2382, -1), (key2526, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2545, 2), (key2395, 2), (key2441, -1), (key2407, -1), (key2410, 2), (key2970, -1), (key2848, -1), (key2991, 2), (key2592, 2), (key2882, -1), (key2595, -1), (key2891, 2), (key2912, -1), (key2602, -1)]

theorem rawRowCheck6573 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form4 = rawRow6573 := by decide +kernel

def row6573 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2970, -1), (key2991, 2)]

theorem rowCheck6573 : row6573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6573 := by decide +kernel

theorem rowEval6573 (x : Key → ℝ) : Integer.Sparse.eval row6573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6573, Integer.Sparse.eval_collectBalanced, rawRowCheck6573]

def rawRow6574 : Integer.Sparse Key := [(key2555, -4), (key2544, 2), (key2565, 2), (key2539, 2), (key2557, 2), (key2545, -4), (key2507, 2), (key2483, -1), (key2526, -1), (key2441, 2), (key2393, -1), (key2565, -1), (key2410, -1), (key2445, -1), (key2382, -1), (key2557, -1), (key2395, 2), (key2545, 2), (key2473, -1), (key2507, -1), (key2483, 2), (key2407, -1), (key2441, -1), (key2592, 2), (key2991, 2), (key2602, -1), (key2912, -1), (key2774, 2), (key2595, -1), (key2882, -1)]

theorem rawRowCheck6574 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form4 = rawRow6574 := by decide +kernel

def row6574 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, -1), (key2441, 1), (key2445, -1), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2912, -1), (key2991, 2)]

theorem rowCheck6574 : row6574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6574 := by decide +kernel

theorem rowEval6574 (x : Key → ℝ) : Integer.Sparse.eval row6574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6574, Integer.Sparse.eval_collectBalanced, rawRowCheck6574]

def rawRow6575 : Integer.Sparse Key := [(key2555, -4), (key2565, 2), (key2544, 2), (key2557, 2), (key2539, 2), (key2545, -4), (key2507, 2), (key2526, -1), (key2483, -1), (key2441, 2), (key2565, -1), (key2393, -1), (key2445, -1), (key2410, -1), (key2557, -1), (key2382, -1), (key2545, 2), (key2395, 2), (key2507, -1), (key2473, -1), (key2483, 2), (key2441, -1), (key2407, -1), (key2991, 2), (key2592, 2), (key2912, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2595, -1)]

theorem rawRowCheck6575 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form4 = rawRow6575 := by decide +kernel

def row6575 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, -1), (key2441, 1), (key2445, -1), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2912, -1), (key2991, 2)]

theorem rowCheck6575 : row6575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6575 := by decide +kernel

theorem rowEval6575 (x : Key → ℝ) : Integer.Sparse.eval row6575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6575, Integer.Sparse.eval_collectBalanced, rawRowCheck6575]

def rawRow6576 : Integer.Sparse Key := [(key2545, -4), (key2557, 2), (key2565, 2), (key2539, 2), (key2544, 2), (key2555, -4), (key2545, 2), (key2557, -1), (key2565, -1), (key2395, 2), (key2445, -1), (key2526, -1), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, 2), (key2507, 2), (key2539, -1), (key2544, -1), (key2555, 2), (key2382, -1), (key2393, -1), (key2410, 2), (key2483, 2), (key2441, -1), (key2507, -1), (key2379, 2), (key2771, -1), (key2848, -1)]

theorem rawRowCheck6576 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form4 = rawRow6576 := by decide +kernel

def row6576 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, 1), (key2545, -2), (key2555, -2), (key2557, 1), (key2565, 1), (key2771, -1), (key2848, -1)]

theorem rowCheck6576 : row6576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6576 := by decide +kernel

theorem rowEval6576 (x : Key → ℝ) : Integer.Sparse.eval row6576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6576, Integer.Sparse.eval_collectBalanced, rawRowCheck6576]

def rawRow6577 : Integer.Sparse Key := [(key2545, -4), (key2565, 2), (key2557, 2), (key2544, 2), (key2539, 2), (key2555, -4), (key2545, 2), (key2565, -1), (key2557, -1), (key2395, 2), (key2526, -1), (key2445, -1), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, 2), (key2441, 2), (key2544, -1), (key2539, -1), (key2555, 2), (key2393, -1), (key2382, -1), (key2483, 2), (key2410, 2), (key2507, -1), (key2441, -1), (key2379, 2), (key2848, -1), (key2771, -1)]

theorem rawRowCheck6577 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form4 = rawRow6577 := by decide +kernel

def row6577 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, 1), (key2545, -2), (key2555, -2), (key2557, 1), (key2565, 1), (key2771, -1), (key2848, -1)]

theorem rowCheck6577 : row6577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6577 := by decide +kernel

theorem rowEval6577 (x : Key → ℝ) : Integer.Sparse.eval row6577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6577, Integer.Sparse.eval_collectBalanced, rawRowCheck6577]

def rawRow6578 : Integer.Sparse Key := [(key2672, -2), (key2675, 1), (key2675, 1), (key2707, -2), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2749, 1), (key2749, 1), (key2751, -2), (key2751, -2), (key2787, 2), (key2797, -1), (key2797, -1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, 2), (key2915, 2), (key2940, -1), (key2940, -1), (key2945, 1), (key2945, 1), (key2952, -1), (key2952, -1), (key2964, 1), (key2964, 1), (key2978, 1), (key2978, 1), (key2994, -1), (key2994, -1), (key3001, 1), (key3001, 1), (key3004, -1), (key3004, -1)]

theorem rawRowCheck6578 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form5 = rawRow6578 := by decide +kernel

def row6578 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

theorem rowCheck6578 : row6578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6578 := by decide +kernel

theorem rowEval6578 (x : Key → ℝ) : Integer.Sparse.eval row6578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6578, Integer.Sparse.eval_collectBalanced, rawRowCheck6578]

def rawRow6579 : Integer.Sparse Key := [(key2675, -2), (key2672, 1), (key2675, 1), (key2730, -2), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2751, 1), (key2739, -2), (key2749, -2), (key2797, 2), (key2787, -1), (key2797, -1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, 2), (key2906, 2), (key2945, -1), (key2946, -1), (key2940, 1), (key2946, 1), (key2962, -1), (key2964, -1), (key2952, 1), (key2962, 1), (key2985, 1), (key2994, 1), (key2978, -1), (key2985, -1), (key2999, 1), (key3004, 1), (key2999, -1), (key3001, -1)]

theorem rawRowCheck6579 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form5 = rawRow6579 := by decide +kernel

def row6579 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6579 : row6579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6579 := by decide +kernel

theorem rowEval6579 (x : Key → ℝ) : Integer.Sparse.eval row6579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6579, Integer.Sparse.eval_collectBalanced, rawRowCheck6579]

def rawRow6580 : Integer.Sparse Key := [(key2675, -2), (key2675, 1), (key2672, 1), (key2730, -2), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2749, -2), (key2739, -2), (key2797, 2), (key2797, -1), (key2787, -1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, 2), (key2899, 2), (key2946, -1), (key2945, -1), (key2946, 1), (key2940, 1), (key2964, -1), (key2962, -1), (key2962, 1), (key2952, 1), (key2994, 1), (key2985, 1), (key2985, -1), (key2978, -1), (key3004, 1), (key2999, 1), (key3001, -1), (key2999, -1)]

theorem rawRowCheck6580 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form5 = rawRow6580 := by decide +kernel

def row6580 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6580 : row6580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6580 := by decide +kernel

theorem rowEval6580 (x : Key → ℝ) : Integer.Sparse.eval row6580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6580, Integer.Sparse.eval_collectBalanced, rawRowCheck6580]

def rawRow6581 : Integer.Sparse Key := [(key2707, -2), (key2739, 1), (key2739, 1), (key2672, -2), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2730, 1), (key2730, 1), (key2751, -2), (key2751, -2), (key2810, 2), (key2899, -1), (key2899, -1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, 2), (key2915, 2), (key2952, -1), (key2952, -1), (key2978, 1), (key2978, 1), (key2940, -1), (key2940, -1), (key3001, 1), (key3001, 1), (key2945, 1), (key2945, 1), (key3004, -1), (key3004, -1), (key2964, 1), (key2964, 1), (key2994, -1), (key2994, -1)]

theorem rawRowCheck6581 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form5 = rawRow6581 := by decide +kernel

def row6581 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

theorem rowCheck6581 : row6581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6581 := by decide +kernel

theorem rowEval6581 (x : Key → ℝ) : Integer.Sparse.eval row6581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6581, Integer.Sparse.eval_collectBalanced, rawRowCheck6581]

def rawRow6582 : Integer.Sparse Key := [(key2739, -2), (key2707, 1), (key2739, 1), (key2749, -2), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, -2), (key2730, -2), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, 2), (key2833, 2), (key2978, -1), (key2999, -1), (key2952, 1), (key2999, 1), (key2985, -1), (key3001, -1), (key2940, 1), (key2985, 1), (key2962, 1), (key3004, 1), (key2945, -1), (key2962, -1), (key2946, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

theorem rawRowCheck6582 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form5 = rawRow6582 := by decide +kernel

def row6582 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6582 : row6582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6582 := by decide +kernel

theorem rowEval6582 (x : Key → ℝ) : Integer.Sparse.eval row6582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6582, Integer.Sparse.eval_collectBalanced, rawRowCheck6582]

def rawRow6583 : Integer.Sparse Key := [(key2739, -2), (key2739, 1), (key2707, 1), (key2749, -2), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2730, -2), (key2675, -2), (key2899, 2), (key2899, -1), (key2810, -1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, 2), (key2797, 2), (key2999, -1), (key2978, -1), (key2999, 1), (key2952, 1), (key3001, -1), (key2985, -1), (key2985, 1), (key2940, 1), (key3004, 1), (key2962, 1), (key2962, -1), (key2945, -1), (key2994, 1), (key2946, 1), (key2964, -1), (key2946, -1)]

theorem rawRowCheck6583 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form5 = rawRow6583 := by decide +kernel

def row6583 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6583 : row6583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6583 := by decide +kernel

theorem rowEval6583 (x : Key → ℝ) : Integer.Sparse.eval row6583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6583, Integer.Sparse.eval_collectBalanced, rawRowCheck6583]

def rawRow6584 : Integer.Sparse Key := [(key2730, -2), (key2749, 1), (key2751, 1), (key2675, -2), (key2739, 1), (key2751, 1), (key2672, 1), (key2675, 1), (key2707, 1), (key2730, 1), (key2739, -2), (key2749, -2), (key2833, 2), (key2906, -1), (key2915, -1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, 2), (key2906, 2), (key2962, -1), (key2964, -1), (key2985, 1), (key2994, 1), (key2945, -1), (key2946, -1), (key2999, 1), (key3004, 1), (key2940, 1), (key2946, 1), (key2999, -1), (key3001, -1), (key2952, 1), (key2962, 1), (key2978, -1), (key2985, -1)]

theorem rawRowCheck6584 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form5 = rawRow6584 := by decide +kernel

def row6584 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6584 : row6584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6584 := by decide +kernel

theorem rowEval6584 (x : Key → ℝ) : Integer.Sparse.eval row6584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6584, Integer.Sparse.eval_collectBalanced, rawRowCheck6584]

def rawRow6585 : Integer.Sparse Key := [(key2730, -2), (key2751, 1), (key2749, 1), (key2675, -2), (key2751, 1), (key2739, 1), (key2675, 1), (key2672, 1), (key2730, 1), (key2707, 1), (key2749, -2), (key2739, -2), (key2833, 2), (key2915, -1), (key2906, -1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, 2), (key2899, 2), (key2964, -1), (key2962, -1), (key2994, 1), (key2985, 1), (key2946, -1), (key2945, -1), (key3004, 1), (key2999, 1), (key2946, 1), (key2940, 1), (key3001, -1), (key2999, -1), (key2962, 1), (key2952, 1), (key2985, -1), (key2978, -1)]

theorem rawRowCheck6585 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form5 = rawRow6585 := by decide +kernel

def row6585 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6585 : row6585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6585 := by decide +kernel

theorem rowEval6585 (x : Key → ℝ) : Integer.Sparse.eval row6585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6585, Integer.Sparse.eval_collectBalanced, rawRowCheck6585]

def rawRow6586 : Integer.Sparse Key := [(key2749, -2), (key2730, 1), (key2751, 1), (key2739, -2), (key2675, 1), (key2751, 1), (key2707, 1), (key2739, 1), (key2672, 1), (key2749, 1), (key2675, -2), (key2730, -2), (key2906, 2), (key2833, -1), (key2915, -1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, 2), (key2833, 2), (key2985, -1), (key3001, -1), (key2962, 1), (key3004, 1), (key2978, -1), (key2999, -1), (key2946, 1), (key2994, 1), (key2952, 1), (key2999, 1), (key2946, -1), (key2964, -1), (key2940, 1), (key2985, 1), (key2945, -1), (key2962, -1)]

theorem rawRowCheck6586 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form5 = rawRow6586 := by decide +kernel

def row6586 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6586 : row6586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6586 := by decide +kernel

theorem rowEval6586 (x : Key → ℝ) : Integer.Sparse.eval row6586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6586, Integer.Sparse.eval_collectBalanced, rawRowCheck6586]

def rawRow6587 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2730, 1), (key2739, -2), (key2751, 1), (key2675, 1), (key2739, 1), (key2707, 1), (key2749, 1), (key2672, 1), (key2730, -2), (key2675, -2), (key2906, 2), (key2915, -1), (key2833, -1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, 2), (key2797, 2), (key3001, -1), (key2985, -1), (key3004, 1), (key2962, 1), (key2999, -1), (key2978, -1), (key2994, 1), (key2946, 1), (key2999, 1), (key2952, 1), (key2964, -1), (key2946, -1), (key2985, 1), (key2940, 1), (key2962, -1), (key2945, -1)]

theorem rawRowCheck6587 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form5 = rawRow6587 := by decide +kernel

def row6587 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, -1), (key2739, -1), (key2749, -1), (key2751, 2), (key2787, -1), (key2797, 1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, 1), (key2915, -2), (key2940, 1), (key2945, -1), (key2952, 1), (key2964, -1), (key2978, -1), (key2994, 1), (key3001, -1), (key3004, 1)]

theorem rowCheck6587 : row6587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6587 := by decide +kernel

theorem rowEval6587 (x : Key → ℝ) : Integer.Sparse.eval row6587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6587, Integer.Sparse.eval_collectBalanced, rawRowCheck6587]

def rawRow6588 : Integer.Sparse Key := [(key2751, -2), (key2730, 1), (key2749, 1), (key2751, -2), (key2675, 1), (key2739, 1), (key2730, 1), (key2749, 1), (key2675, 1), (key2739, 1), (key2672, -2), (key2707, -2), (key2915, 2), (key2833, -1), (key2906, -1), (key2915, 2), (key2797, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, 2), (key2810, 2), (key2994, -1), (key3004, -1), (key2964, 1), (key3001, 1), (key2994, -1), (key3004, -1), (key2945, 1), (key2978, 1), (key2964, 1), (key3001, 1), (key2940, -1), (key2952, -1), (key2945, 1), (key2978, 1), (key2940, -1), (key2952, -1)]

theorem rawRowCheck6588 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form5 = rawRow6588 := by decide +kernel

def row6588 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

theorem rowCheck6588 : row6588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6588 := by decide +kernel

theorem rowEval6588 (x : Key → ℝ) : Integer.Sparse.eval row6588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6588, Integer.Sparse.eval_collectBalanced, rawRowCheck6588]

def rawRow6589 : Integer.Sparse Key := [(key2751, -2), (key2749, 1), (key2730, 1), (key2751, -2), (key2739, 1), (key2675, 1), (key2749, 1), (key2730, 1), (key2739, 1), (key2675, 1), (key2707, -2), (key2672, -2), (key2915, 2), (key2906, -1), (key2833, -1), (key2915, 2), (key2899, -1), (key2797, -1), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, 2), (key2787, 2), (key3004, -1), (key2994, -1), (key3001, 1), (key2964, 1), (key3004, -1), (key2994, -1), (key2978, 1), (key2945, 1), (key3001, 1), (key2964, 1), (key2952, -1), (key2940, -1), (key2978, 1), (key2945, 1), (key2952, -1), (key2940, -1)]

theorem rawRowCheck6589 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form5 = rawRow6589 := by decide +kernel

def row6589 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2707, -2), (key2730, 2), (key2739, 2), (key2749, 2), (key2751, -4), (key2787, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, -2), (key2906, -2), (key2915, 4), (key2940, -2), (key2945, 2), (key2952, -2), (key2964, 2), (key2978, 2), (key2994, -2), (key3001, 2), (key3004, -2)]

theorem rowCheck6589 : row6589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6589 := by decide +kernel

theorem rowEval6589 (x : Key → ℝ) : Integer.Sparse.eval row6589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6589, Integer.Sparse.eval_collectBalanced, rawRowCheck6589]

def rawRow6590 : Integer.Sparse Key := [(key2656, -2), (key2650, 1), (key2655, 1), (key2999, -2), (key2739, 1), (key2899, 1), (key3001, 1), (key3004, 1), (key2751, 1), (key2915, 1), (key2749, -2), (key2906, -2), (key2656, 2), (key2620, -1), (key2643, -1), (key2946, 2), (key2675, -1), (key2797, -1), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, 2), (key2833, 2), (key2650, -1), (key2655, -1), (key2620, 1), (key2643, 1), (key2730, -1), (key2749, -1), (key2672, 1), (key2707, 1), (key2833, 1), (key2906, 1), (key2787, -1), (key2810, -1), (key2945, 1), (key2978, 1), (key2940, -1), (key2952, -1)]

theorem rawRowCheck6590 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form5 = rawRow6590 := by decide +kernel

def row6590 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -3), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 3), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2946, 2), (key2952, -1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6590 : row6590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6590 := by decide +kernel

theorem rowEval6590 (x : Key → ℝ) : Integer.Sparse.eval row6590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6590, Integer.Sparse.eval_collectBalanced, rawRowCheck6590]

def rawRow6591 : Integer.Sparse Key := [(key2656, -2), (key2655, 1), (key2650, 1), (key2999, -2), (key2899, 1), (key2739, 1), (key3004, 1), (key3001, 1), (key2915, 1), (key2751, 1), (key2906, -2), (key2749, -2), (key2656, 2), (key2643, -1), (key2620, -1), (key2946, 2), (key2797, -1), (key2675, -1), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, 2), (key2730, 2), (key2655, -1), (key2650, -1), (key2643, 1), (key2620, 1), (key2749, -1), (key2730, -1), (key2707, 1), (key2672, 1), (key2906, 1), (key2833, 1), (key2810, -1), (key2787, -1), (key2978, 1), (key2945, 1), (key2952, -1), (key2940, -1)]

theorem rawRowCheck6591 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form5 = rawRow6591 := by decide +kernel

def row6591 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -3), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 3), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, 1), (key2946, 2), (key2952, -1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6591 : row6591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6591 := by decide +kernel

theorem rowEval6591 (x : Key → ℝ) : Integer.Sparse.eval row6591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6591, Integer.Sparse.eval_collectBalanced, rawRowCheck6591]

def rawRow6592 : Integer.Sparse Key := [(key2749, -2), (key2739, 1), (key2751, 1), (key2906, -2), (key2650, 1), (key3001, 1), (key2899, 1), (key2915, 1), (key2655, 1), (key3004, 1), (key2656, -2), (key2999, -2), (key2730, 2), (key2675, -1), (key2751, -1), (key2833, 2), (key2620, -1), (key2964, -1), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, 2), (key2946, 2), (key2707, -1), (key2730, -1), (key2672, 1), (key2749, 1), (key2810, -1), (key2833, -1), (key2620, 1), (key2833, 1), (key2707, 1), (key2978, 1), (key2643, -1), (key2730, -1), (key2650, 1), (key2906, 1), (key2655, -1), (key2749, -1)]

theorem rawRowCheck6592 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form5 = rawRow6592 := by decide +kernel

def row6592 : Integer.Sparse Key := [(key2643, -2), (key2650, 2), (key2672, 1), (key2675, -1), (key2739, 1), (key2749, -2), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6592 : row6592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6592 := by decide +kernel

theorem rowEval6592 (x : Key → ℝ) : Integer.Sparse.eval row6592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6592, Integer.Sparse.eval_collectBalanced, rawRowCheck6592]

def rawRow6593 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2739, 1), (key2906, -2), (key3001, 1), (key2650, 1), (key2915, 1), (key2899, 1), (key3004, 1), (key2655, 1), (key2999, -2), (key2656, -2), (key2730, 2), (key2751, -1), (key2675, -1), (key2833, 2), (key2964, -1), (key2620, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, 2), (key2656, 2), (key2730, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2833, -1), (key2810, -1), (key2833, 1), (key2620, 1), (key2978, 1), (key2707, 1), (key2730, -1), (key2643, -1), (key2906, 1), (key2650, 1), (key2749, -1), (key2655, -1)]

theorem rawRowCheck6593 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form5 = rawRow6593 := by decide +kernel

def row6593 : Integer.Sparse Key := [(key2643, -2), (key2650, 2), (key2672, 1), (key2675, -1), (key2739, 1), (key2749, -2), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6593 : row6593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6593 := by decide +kernel

theorem rowEval6593 (x : Key → ℝ) : Integer.Sparse.eval row6593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6593, Integer.Sparse.eval_collectBalanced, rawRowCheck6593]

def rawRow6594 : Integer.Sparse Key := [(key2906, -2), (key2899, 1), (key2915, 1), (key2749, -2), (key2655, 1), (key3004, 1), (key2739, 1), (key2751, 1), (key2650, 1), (key3001, 1), (key2656, -2), (key2999, -2), (key2833, 2), (key2797, -1), (key2915, -1), (key2730, 2), (key2643, -1), (key2994, -1), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, 2), (key2946, 2), (key2810, -1), (key2833, -1), (key2787, 1), (key2906, 1), (key2707, -1), (key2730, -1), (key2643, 1), (key2978, 1), (key2672, 1), (key2749, 1), (key2655, -1), (key2749, -1), (key2620, 1), (key2833, 1), (key2643, -1), (key2730, -1)]

theorem rawRowCheck6594 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form5 = rawRow6594 := by decide +kernel

def row6594 : Integer.Sparse Key := [(key2643, -1), (key2650, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2739, 1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6594 : row6594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6594 := by decide +kernel

theorem rowEval6594 (x : Key → ℝ) : Integer.Sparse.eval row6594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6594, Integer.Sparse.eval_collectBalanced, rawRowCheck6594]

def rawRow6595 : Integer.Sparse Key := [(key2906, -2), (key2915, 1), (key2899, 1), (key2749, -2), (key3004, 1), (key2655, 1), (key2751, 1), (key2739, 1), (key3001, 1), (key2650, 1), (key2999, -2), (key2656, -2), (key2833, 2), (key2915, -1), (key2797, -1), (key2730, 2), (key2994, -1), (key2643, -1), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, 2), (key2656, 2), (key2833, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key2730, -1), (key2707, -1), (key2978, 1), (key2643, 1), (key2749, 1), (key2672, 1), (key2749, -1), (key2655, -1), (key2833, 1), (key2620, 1), (key2730, -1), (key2643, -1)]

theorem rawRowCheck6595 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form5 = rawRow6595 := by decide +kernel

def row6595 : Integer.Sparse Key := [(key2643, -1), (key2650, 1), (key2672, 1), (key2675, -1), (key2707, -1), (key2739, 1), (key2749, -2), (key2787, 1), (key2797, -1), (key2810, -1), (key2833, 2), (key2899, 1), (key2906, -1), (key2946, 2), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6595 : row6595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6595 := by decide +kernel

theorem rowEval6595 (x : Key → ℝ) : Integer.Sparse.eval row6595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6595, Integer.Sparse.eval_collectBalanced, rawRowCheck6595]

def rawRow6596 : Integer.Sparse Key := [(key2999, -2), (key3001, 1), (key3004, 1), (key2656, -2), (key2751, 1), (key2915, 1), (key2650, 1), (key2655, 1), (key2739, 1), (key2899, 1), (key2749, -2), (key2906, -2), (key2946, 2), (key2964, -1), (key2994, -1), (key2656, 2), (key2751, -1), (key2915, -1), (key2620, -1), (key2643, -1), (key2675, -1), (key2797, -1), (key2730, 2), (key2833, 2), (key2940, -1), (key2945, -1), (key2952, 1), (key2978, 1), (key2650, -1), (key2655, -1), (key2749, 1), (key2906, 1), (key2620, 1), (key2643, 1), (key2730, -1), (key2833, -1), (key2672, 1), (key2707, 1), (key2787, -1), (key2810, -1)]

theorem rawRowCheck6596 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form5 = rawRow6596 := by decide +kernel

def row6596 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, -1), (key2946, 2), (key2952, 1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6596 : row6596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6596 := by decide +kernel

theorem rowEval6596 (x : Key → ℝ) : Integer.Sparse.eval row6596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6596, Integer.Sparse.eval_collectBalanced, rawRowCheck6596]

def rawRow6597 : Integer.Sparse Key := [(key2999, -2), (key3004, 1), (key3001, 1), (key2656, -2), (key2915, 1), (key2751, 1), (key2655, 1), (key2650, 1), (key2899, 1), (key2739, 1), (key2906, -2), (key2749, -2), (key2946, 2), (key2994, -1), (key2964, -1), (key2656, 2), (key2915, -1), (key2751, -1), (key2643, -1), (key2620, -1), (key2797, -1), (key2675, -1), (key2833, 2), (key2730, 2), (key2945, -1), (key2940, -1), (key2978, 1), (key2952, 1), (key2655, -1), (key2650, -1), (key2906, 1), (key2749, 1), (key2643, 1), (key2620, 1), (key2833, -1), (key2730, -1), (key2707, 1), (key2672, 1), (key2810, -1), (key2787, -1)]

theorem rawRowCheck6597 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form5 = rawRow6597 := by decide +kernel

def row6597 : Integer.Sparse Key := [(key2672, 1), (key2675, -1), (key2707, 1), (key2730, 1), (key2739, 1), (key2749, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -1), (key2940, -1), (key2945, -1), (key2946, 2), (key2952, 1), (key2964, -1), (key2978, 1), (key2994, -1), (key2999, -2), (key3001, 1), (key3004, 1)]

theorem rowCheck6597 : row6597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6597 := by decide +kernel

theorem rowEval6597 (x : Key → ℝ) : Integer.Sparse.eval row6597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6597, Integer.Sparse.eval_collectBalanced, rawRowCheck6597]

def rawRow6598 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1302, 2), (key1316, -1), (key1316, -1), (key1337, 2), (key1337, 2), (key1339, -1), (key1339, -1), (key1329, 2), (key1345, -1), (key1345, -1), (key1391, 1), (key1391, 1), (key1397, -2), (key1546, 1), (key1546, 1), (key1772, -2), (key1772, -2), (key1774, 1), (key1774, 1), (key1559, -2), (key1780, 1), (key1780, 1), (key1455, -1), (key1455, -1), (key1457, 1), (key1457, 1), (key1788, 1), (key1788, 1), (key1790, -1), (key1790, -1), (key1655, -1), (key1655, -1), (key1813, 1), (key1813, 1), (key1659, 1), (key1659, 1), (key1817, -1), (key1817, -1)]

theorem rawRowCheck6598 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form6 = rawRow6598 := by decide +kernel

def row6598 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

theorem rowCheck6598 : row6598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6598 := by decide +kernel

theorem rowEval6598 (x : Key → ℝ) : Integer.Sparse.eval row6598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6598, Integer.Sparse.eval_collectBalanced, rawRowCheck6598]

def rawRow6599 : Integer.Sparse Key := [(key1296, -1), (key1302, -1), (key1296, 2), (key1337, -1), (key1339, -1), (key1316, 2), (key1339, 2), (key1316, -1), (key1337, -1), (key1345, 2), (key1329, -1), (key1345, -1), (key1391, 1), (key1397, 1), (key1391, -2), (key1772, 1), (key1774, 1), (key1546, -2), (key1774, -2), (key1546, 1), (key1772, 1), (key1780, -2), (key1559, 1), (key1780, 1), (key1424, -1), (key1457, -1), (key1424, 1), (key1455, 1), (key1573, 1), (key1790, 1), (key1573, -1), (key1788, -1), (key1813, -1), (key1839, -1), (key1655, 1), (key1839, 1), (key1817, 1), (key1841, 1), (key1659, -1), (key1841, -1)]

theorem rawRowCheck6599 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form6 = rawRow6599 := by decide +kernel

def row6599 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6599 : row6599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6599 := by decide +kernel

theorem rowEval6599 (x : Key → ℝ) : Integer.Sparse.eval row6599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6599, Integer.Sparse.eval_collectBalanced, rawRowCheck6599]

def rawRow6600 : Integer.Sparse Key := [(key1302, -1), (key1296, -1), (key1296, 2), (key1339, -1), (key1337, -1), (key1339, 2), (key1316, 2), (key1337, -1), (key1316, -1), (key1345, 2), (key1345, -1), (key1329, -1), (key1397, 1), (key1391, 1), (key1391, -2), (key1774, 1), (key1772, 1), (key1774, -2), (key1546, -2), (key1772, 1), (key1546, 1), (key1780, -2), (key1780, 1), (key1559, 1), (key1457, -1), (key1424, -1), (key1455, 1), (key1424, 1), (key1790, 1), (key1573, 1), (key1788, -1), (key1573, -1), (key1839, -1), (key1813, -1), (key1839, 1), (key1655, 1), (key1841, 1), (key1817, 1), (key1841, -1), (key1659, -1)]

theorem rawRowCheck6600 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form6 = rawRow6600 := by decide +kernel

def row6600 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6600 : row6600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6600 := by decide +kernel

theorem rowEval6600 (x : Key → ℝ) : Integer.Sparse.eval row6600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6600, Integer.Sparse.eval_collectBalanced, rawRowCheck6600]

def rawRow6601 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1329, 2), (key1296, -1), (key1296, -1), (key1337, 2), (key1337, 2), (key1345, -1), (key1345, -1), (key1302, 2), (key1339, -1), (key1339, -1), (key1546, 1), (key1546, 1), (key1559, -2), (key1391, 1), (key1391, 1), (key1772, -2), (key1772, -2), (key1780, 1), (key1780, 1), (key1397, -2), (key1774, 1), (key1774, 1), (key1655, -1), (key1655, -1), (key1659, 1), (key1659, 1), (key1813, 1), (key1813, 1), (key1817, -1), (key1817, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1457, 1), (key1457, 1), (key1790, -1), (key1790, -1)]

theorem rawRowCheck6601 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form6 = rawRow6601 := by decide +kernel

def row6601 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

theorem rowCheck6601 : row6601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6601 := by decide +kernel

theorem rowEval6601 (x : Key → ℝ) : Integer.Sparse.eval row6601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6601, Integer.Sparse.eval_collectBalanced, rawRowCheck6601]

def rawRow6602 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1316, 2), (key1337, -1), (key1345, -1), (key1296, 2), (key1345, 2), (key1296, -1), (key1337, -1), (key1339, 2), (key1302, -1), (key1339, -1), (key1546, 1), (key1559, 1), (key1546, -2), (key1772, 1), (key1780, 1), (key1391, -2), (key1780, -2), (key1391, 1), (key1772, 1), (key1774, -2), (key1397, 1), (key1774, 1), (key1573, -1), (key1659, -1), (key1573, 1), (key1655, 1), (key1424, 1), (key1817, 1), (key1424, -1), (key1813, -1), (key1788, -1), (key1841, -1), (key1455, 1), (key1841, 1), (key1790, 1), (key1839, 1), (key1457, -1), (key1839, -1)]

theorem rawRowCheck6602 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form6 = rawRow6602 := by decide +kernel

def row6602 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6602 : row6602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6602 := by decide +kernel

theorem rowEval6602 (x : Key → ℝ) : Integer.Sparse.eval row6602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6602, Integer.Sparse.eval_collectBalanced, rawRowCheck6602]

def rawRow6603 : Integer.Sparse Key := [(key1329, -1), (key1316, -1), (key1316, 2), (key1345, -1), (key1337, -1), (key1345, 2), (key1296, 2), (key1337, -1), (key1296, -1), (key1339, 2), (key1339, -1), (key1302, -1), (key1559, 1), (key1546, 1), (key1546, -2), (key1780, 1), (key1772, 1), (key1780, -2), (key1391, -2), (key1772, 1), (key1391, 1), (key1774, -2), (key1774, 1), (key1397, 1), (key1659, -1), (key1573, -1), (key1655, 1), (key1573, 1), (key1817, 1), (key1424, 1), (key1813, -1), (key1424, -1), (key1841, -1), (key1788, -1), (key1841, 1), (key1455, 1), (key1839, 1), (key1790, 1), (key1839, -1), (key1457, -1)]

theorem rawRowCheck6603 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form6 = rawRow6603 := by decide +kernel

def row6603 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6603 : row6603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6603 := by decide +kernel

theorem rowEval6603 (x : Key → ℝ) : Integer.Sparse.eval row6603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6603, Integer.Sparse.eval_collectBalanced, rawRowCheck6603]

def rawRow6604 : Integer.Sparse Key := [(key1337, -1), (key1339, -1), (key1345, 2), (key1296, -1), (key1302, -1), (key1316, 2), (key1339, 2), (key1329, -1), (key1345, -1), (key1296, 2), (key1316, -1), (key1337, -1), (key1772, 1), (key1774, 1), (key1780, -2), (key1391, 1), (key1397, 1), (key1546, -2), (key1774, -2), (key1559, 1), (key1780, 1), (key1391, -2), (key1546, 1), (key1772, 1), (key1813, -1), (key1839, -1), (key1817, 1), (key1841, 1), (key1655, 1), (key1839, 1), (key1659, -1), (key1841, -1), (key1424, -1), (key1457, -1), (key1573, 1), (key1790, 1), (key1424, 1), (key1455, 1), (key1573, -1), (key1788, -1)]

theorem rawRowCheck6604 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6604 := by decide +kernel

def row6604 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6604 : row6604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6604 := by decide +kernel

theorem rowEval6604 (x : Key → ℝ) : Integer.Sparse.eval row6604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6604, Integer.Sparse.eval_collectBalanced, rawRowCheck6604]

def rawRow6605 : Integer.Sparse Key := [(key1339, -1), (key1337, -1), (key1345, 2), (key1302, -1), (key1296, -1), (key1339, 2), (key1316, 2), (key1345, -1), (key1329, -1), (key1296, 2), (key1337, -1), (key1316, -1), (key1774, 1), (key1772, 1), (key1780, -2), (key1397, 1), (key1391, 1), (key1774, -2), (key1546, -2), (key1780, 1), (key1559, 1), (key1391, -2), (key1772, 1), (key1546, 1), (key1839, -1), (key1813, -1), (key1841, 1), (key1817, 1), (key1839, 1), (key1655, 1), (key1841, -1), (key1659, -1), (key1457, -1), (key1424, -1), (key1790, 1), (key1573, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

theorem rawRowCheck6605 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6605 := by decide +kernel

def row6605 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6605 : row6605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6605 := by decide +kernel

theorem rowEval6605 (x : Key → ℝ) : Integer.Sparse.eval row6605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6605, Integer.Sparse.eval_collectBalanced, rawRowCheck6605]

def rawRow6606 : Integer.Sparse Key := [(key1337, -1), (key1345, -1), (key1339, 2), (key1316, -1), (key1329, -1), (key1296, 2), (key1345, 2), (key1302, -1), (key1339, -1), (key1316, 2), (key1296, -1), (key1337, -1), (key1772, 1), (key1780, 1), (key1774, -2), (key1546, 1), (key1559, 1), (key1391, -2), (key1780, -2), (key1397, 1), (key1774, 1), (key1546, -2), (key1391, 1), (key1772, 1), (key1788, -1), (key1841, -1), (key1790, 1), (key1839, 1), (key1455, 1), (key1841, 1), (key1457, -1), (key1839, -1), (key1573, -1), (key1659, -1), (key1424, 1), (key1817, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

theorem rawRowCheck6606 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form6 = rawRow6606 := by decide +kernel

def row6606 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6606 : row6606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6606 := by decide +kernel

theorem rowEval6606 (x : Key → ℝ) : Integer.Sparse.eval row6606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6606, Integer.Sparse.eval_collectBalanced, rawRowCheck6606]

def rawRow6607 : Integer.Sparse Key := [(key1345, -1), (key1337, -1), (key1339, 2), (key1329, -1), (key1316, -1), (key1345, 2), (key1296, 2), (key1339, -1), (key1302, -1), (key1316, 2), (key1337, -1), (key1296, -1), (key1780, 1), (key1772, 1), (key1774, -2), (key1559, 1), (key1546, 1), (key1780, -2), (key1391, -2), (key1774, 1), (key1397, 1), (key1546, -2), (key1772, 1), (key1391, 1), (key1841, -1), (key1788, -1), (key1839, 1), (key1790, 1), (key1841, 1), (key1455, 1), (key1839, -1), (key1457, -1), (key1659, -1), (key1573, -1), (key1817, 1), (key1424, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

theorem rawRowCheck6607 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form6 = rawRow6607 := by decide +kernel

def row6607 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6607 : row6607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6607 := by decide +kernel

theorem rowEval6607 (x : Key → ℝ) : Integer.Sparse.eval row6607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6607, Integer.Sparse.eval_collectBalanced, rawRowCheck6607]

def rawRow6608 : Integer.Sparse Key := [(key1339, -1), (key1345, -1), (key1337, 2), (key1339, -1), (key1345, -1), (key1302, 2), (key1329, 2), (key1296, -1), (key1316, -1), (key1337, 2), (key1296, -1), (key1316, -1), (key1774, 1), (key1780, 1), (key1772, -2), (key1774, 1), (key1780, 1), (key1397, -2), (key1559, -2), (key1391, 1), (key1546, 1), (key1772, -2), (key1391, 1), (key1546, 1), (key1790, -1), (key1817, -1), (key1788, 1), (key1813, 1), (key1457, 1), (key1659, 1), (key1455, -1), (key1655, -1), (key1790, -1), (key1817, -1), (key1457, 1), (key1659, 1), (key1788, 1), (key1813, 1), (key1455, -1), (key1655, -1)]

theorem rawRowCheck6608 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6608 := by decide +kernel

def row6608 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

theorem rowCheck6608 : row6608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6608 := by decide +kernel

theorem rowEval6608 (x : Key → ℝ) : Integer.Sparse.eval row6608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6608, Integer.Sparse.eval_collectBalanced, rawRowCheck6608]

def rawRow6609 : Integer.Sparse Key := [(key1345, -1), (key1339, -1), (key1337, 2), (key1345, -1), (key1339, -1), (key1329, 2), (key1302, 2), (key1316, -1), (key1296, -1), (key1337, 2), (key1316, -1), (key1296, -1), (key1780, 1), (key1774, 1), (key1772, -2), (key1780, 1), (key1774, 1), (key1559, -2), (key1397, -2), (key1546, 1), (key1391, 1), (key1772, -2), (key1546, 1), (key1391, 1), (key1817, -1), (key1790, -1), (key1813, 1), (key1788, 1), (key1659, 1), (key1457, 1), (key1655, -1), (key1455, -1), (key1817, -1), (key1790, -1), (key1659, 1), (key1457, 1), (key1813, 1), (key1788, 1), (key1655, -1), (key1455, -1)]

theorem rawRowCheck6609 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6609 := by decide +kernel

def row6609 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, -2), (key1329, 2), (key1337, 4), (key1339, -2), (key1345, -2), (key1391, 2), (key1397, -2), (key1455, -2), (key1457, 2), (key1546, 2), (key1559, -2), (key1655, -2), (key1659, 2), (key1772, -4), (key1774, 2), (key1780, 2), (key1788, 2), (key1790, -2), (key1813, 2), (key1817, -2)]

theorem rowCheck6609 : row6609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6609 := by decide +kernel

theorem rowEval6609 (x : Key → ℝ) : Integer.Sparse.eval row6609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6609, Integer.Sparse.eval_collectBalanced, rawRowCheck6609]

def rawRow6610 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1559, 2), (key1573, -1), (key1573, -1), (key1655, 2), (key1655, 2), (key1659, -1), (key1659, -1), (key1596, 2), (key1667, -1), (key1667, -1), (key1316, 1), (key1316, 1), (key1329, -2), (key1424, 1), (key1424, 1), (key1813, -2), (key1813, -2), (key1817, 1), (key1817, 1), (key1447, -2), (key1825, 1), (key1825, 1), (key1337, -1), (key1337, -1), (key1345, 1), (key1345, 1), (key1772, 1), (key1772, 1), (key1780, -1), (key1780, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1466, 1), (key1466, 1), (key1798, -1), (key1798, -1)]

theorem rawRowCheck6610 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form6 = rawRow6610 := by decide +kernel

def row6610 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

theorem rowCheck6610 : row6610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6610 := by decide +kernel

theorem rowEval6610 (x : Key → ℝ) : Integer.Sparse.eval row6610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6610, Integer.Sparse.eval_collectBalanced, rawRowCheck6610]

def rawRow6611 : Integer.Sparse Key := [(key1546, -1), (key1559, -1), (key1546, 2), (key1655, -1), (key1659, -1), (key1573, 2), (key1659, 2), (key1573, -1), (key1655, -1), (key1667, 2), (key1596, -1), (key1667, -1), (key1316, 1), (key1329, 1), (key1316, -2), (key1813, 1), (key1817, 1), (key1424, -2), (key1817, -2), (key1424, 1), (key1813, 1), (key1825, -2), (key1447, 1), (key1825, 1), (key1296, -1), (key1345, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1780, 1), (key1391, -1), (key1772, -1), (key1788, -1), (key1841, -1), (key1455, 1), (key1841, 1), (key1798, 1), (key1844, 1), (key1466, -1), (key1844, -1)]

theorem rawRowCheck6611 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form6 = rawRow6611 := by decide +kernel

def row6611 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6611 : row6611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6611 := by decide +kernel

theorem rowEval6611 (x : Key → ℝ) : Integer.Sparse.eval row6611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6611, Integer.Sparse.eval_collectBalanced, rawRowCheck6611]

def rawRow6612 : Integer.Sparse Key := [(key1559, -1), (key1546, -1), (key1546, 2), (key1659, -1), (key1655, -1), (key1659, 2), (key1573, 2), (key1655, -1), (key1573, -1), (key1667, 2), (key1667, -1), (key1596, -1), (key1329, 1), (key1316, 1), (key1316, -2), (key1817, 1), (key1813, 1), (key1817, -2), (key1424, -2), (key1813, 1), (key1424, 1), (key1825, -2), (key1825, 1), (key1447, 1), (key1345, -1), (key1296, -1), (key1337, 1), (key1296, 1), (key1780, 1), (key1391, 1), (key1772, -1), (key1391, -1), (key1841, -1), (key1788, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1798, 1), (key1844, -1), (key1466, -1)]

theorem rawRowCheck6612 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form6 = rawRow6612 := by decide +kernel

def row6612 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6612 : row6612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6612 := by decide +kernel

theorem rowEval6612 (x : Key → ℝ) : Integer.Sparse.eval row6612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6612, Integer.Sparse.eval_collectBalanced, rawRowCheck6612]

def rawRow6613 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1596, 2), (key1546, -1), (key1546, -1), (key1655, 2), (key1655, 2), (key1667, -1), (key1667, -1), (key1559, 2), (key1659, -1), (key1659, -1), (key1424, 1), (key1424, 1), (key1447, -2), (key1316, 1), (key1316, 1), (key1813, -2), (key1813, -2), (key1825, 1), (key1825, 1), (key1329, -2), (key1817, 1), (key1817, 1), (key1455, -1), (key1455, -1), (key1466, 1), (key1466, 1), (key1788, 1), (key1788, 1), (key1798, -1), (key1798, -1), (key1337, -1), (key1337, -1), (key1772, 1), (key1772, 1), (key1345, 1), (key1345, 1), (key1780, -1), (key1780, -1)]

theorem rawRowCheck6613 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form6 = rawRow6613 := by decide +kernel

def row6613 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

theorem rowCheck6613 : row6613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6613 := by decide +kernel

theorem rowEval6613 (x : Key → ℝ) : Integer.Sparse.eval row6613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6613, Integer.Sparse.eval_collectBalanced, rawRowCheck6613]

def rawRow6614 : Integer.Sparse Key := [(key1573, -1), (key1596, -1), (key1573, 2), (key1655, -1), (key1667, -1), (key1546, 2), (key1667, 2), (key1546, -1), (key1655, -1), (key1659, 2), (key1559, -1), (key1659, -1), (key1424, 1), (key1447, 1), (key1424, -2), (key1813, 1), (key1825, 1), (key1316, -2), (key1825, -2), (key1316, 1), (key1813, 1), (key1817, -2), (key1329, 1), (key1817, 1), (key1391, -1), (key1466, -1), (key1391, 1), (key1455, 1), (key1296, 1), (key1798, 1), (key1296, -1), (key1788, -1), (key1772, -1), (key1844, -1), (key1337, 1), (key1844, 1), (key1780, 1), (key1841, 1), (key1345, -1), (key1841, -1)]

theorem rawRowCheck6614 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form6 = rawRow6614 := by decide +kernel

def row6614 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6614 : row6614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6614 := by decide +kernel

theorem rowEval6614 (x : Key → ℝ) : Integer.Sparse.eval row6614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6614, Integer.Sparse.eval_collectBalanced, rawRowCheck6614]

def rawRow6615 : Integer.Sparse Key := [(key1596, -1), (key1573, -1), (key1573, 2), (key1667, -1), (key1655, -1), (key1667, 2), (key1546, 2), (key1655, -1), (key1546, -1), (key1659, 2), (key1659, -1), (key1559, -1), (key1447, 1), (key1424, 1), (key1424, -2), (key1825, 1), (key1813, 1), (key1825, -2), (key1316, -2), (key1813, 1), (key1316, 1), (key1817, -2), (key1817, 1), (key1329, 1), (key1466, -1), (key1391, -1), (key1455, 1), (key1391, 1), (key1798, 1), (key1296, 1), (key1788, -1), (key1296, -1), (key1844, -1), (key1772, -1), (key1844, 1), (key1337, 1), (key1841, 1), (key1780, 1), (key1841, -1), (key1345, -1)]

theorem rawRowCheck6615 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form6 = rawRow6615 := by decide +kernel

def row6615 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6615 : row6615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6615 := by decide +kernel

theorem rowEval6615 (x : Key → ℝ) : Integer.Sparse.eval row6615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6615, Integer.Sparse.eval_collectBalanced, rawRowCheck6615]

def rawRow6616 : Integer.Sparse Key := [(key1655, -1), (key1659, -1), (key1667, 2), (key1546, -1), (key1559, -1), (key1573, 2), (key1659, 2), (key1596, -1), (key1667, -1), (key1546, 2), (key1573, -1), (key1655, -1), (key1813, 1), (key1817, 1), (key1825, -2), (key1316, 1), (key1329, 1), (key1424, -2), (key1817, -2), (key1447, 1), (key1825, 1), (key1316, -2), (key1424, 1), (key1813, 1), (key1788, -1), (key1841, -1), (key1798, 1), (key1844, 1), (key1455, 1), (key1841, 1), (key1466, -1), (key1844, -1), (key1296, -1), (key1345, -1), (key1391, 1), (key1780, 1), (key1296, 1), (key1337, 1), (key1391, -1), (key1772, -1)]

theorem rawRowCheck6616 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form6 = rawRow6616 := by decide +kernel

def row6616 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6616 : row6616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6616 := by decide +kernel

theorem rowEval6616 (x : Key → ℝ) : Integer.Sparse.eval row6616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6616, Integer.Sparse.eval_collectBalanced, rawRowCheck6616]

def rawRow6617 : Integer.Sparse Key := [(key1659, -1), (key1655, -1), (key1667, 2), (key1559, -1), (key1546, -1), (key1659, 2), (key1573, 2), (key1667, -1), (key1596, -1), (key1546, 2), (key1655, -1), (key1573, -1), (key1817, 1), (key1813, 1), (key1825, -2), (key1329, 1), (key1316, 1), (key1817, -2), (key1424, -2), (key1825, 1), (key1447, 1), (key1316, -2), (key1813, 1), (key1424, 1), (key1841, -1), (key1788, -1), (key1844, 1), (key1798, 1), (key1841, 1), (key1455, 1), (key1844, -1), (key1466, -1), (key1345, -1), (key1296, -1), (key1780, 1), (key1391, 1), (key1337, 1), (key1296, 1), (key1772, -1), (key1391, -1)]

theorem rawRowCheck6617 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form6 = rawRow6617 := by decide +kernel

def row6617 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6617 : row6617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6617 := by decide +kernel

theorem rowEval6617 (x : Key → ℝ) : Integer.Sparse.eval row6617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6617, Integer.Sparse.eval_collectBalanced, rawRowCheck6617]

def rawRow6618 : Integer.Sparse Key := [(key1655, -1), (key1667, -1), (key1659, 2), (key1573, -1), (key1596, -1), (key1546, 2), (key1667, 2), (key1559, -1), (key1659, -1), (key1573, 2), (key1546, -1), (key1655, -1), (key1813, 1), (key1825, 1), (key1817, -2), (key1424, 1), (key1447, 1), (key1316, -2), (key1825, -2), (key1329, 1), (key1817, 1), (key1424, -2), (key1316, 1), (key1813, 1), (key1772, -1), (key1844, -1), (key1780, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, -1), (key1841, -1), (key1391, -1), (key1466, -1), (key1296, 1), (key1798, 1), (key1391, 1), (key1455, 1), (key1296, -1), (key1788, -1)]

theorem rawRowCheck6618 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form6 = rawRow6618 := by decide +kernel

def row6618 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6618 : row6618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6618 := by decide +kernel

theorem rowEval6618 (x : Key → ℝ) : Integer.Sparse.eval row6618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6618, Integer.Sparse.eval_collectBalanced, rawRowCheck6618]

def rawRow6619 : Integer.Sparse Key := [(key1667, -1), (key1655, -1), (key1659, 2), (key1596, -1), (key1573, -1), (key1667, 2), (key1546, 2), (key1659, -1), (key1559, -1), (key1573, 2), (key1655, -1), (key1546, -1), (key1825, 1), (key1813, 1), (key1817, -2), (key1447, 1), (key1424, 1), (key1825, -2), (key1316, -2), (key1817, 1), (key1329, 1), (key1424, -2), (key1813, 1), (key1316, 1), (key1844, -1), (key1772, -1), (key1841, 1), (key1780, 1), (key1844, 1), (key1337, 1), (key1841, -1), (key1345, -1), (key1466, -1), (key1391, -1), (key1798, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, -1), (key1296, -1)]

theorem rawRowCheck6619 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form6 = rawRow6619 := by decide +kernel

def row6619 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6619 : row6619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6619 := by decide +kernel

theorem rowEval6619 (x : Key → ℝ) : Integer.Sparse.eval row6619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6619, Integer.Sparse.eval_collectBalanced, rawRowCheck6619]

def rawRow6620 : Integer.Sparse Key := [(key1659, -1), (key1667, -1), (key1655, 2), (key1659, -1), (key1667, -1), (key1559, 2), (key1596, 2), (key1546, -1), (key1573, -1), (key1655, 2), (key1546, -1), (key1573, -1), (key1817, 1), (key1825, 1), (key1813, -2), (key1817, 1), (key1825, 1), (key1329, -2), (key1447, -2), (key1316, 1), (key1424, 1), (key1813, -2), (key1316, 1), (key1424, 1), (key1780, -1), (key1798, -1), (key1772, 1), (key1788, 1), (key1345, 1), (key1466, 1), (key1337, -1), (key1455, -1), (key1780, -1), (key1798, -1), (key1345, 1), (key1466, 1), (key1772, 1), (key1788, 1), (key1337, -1), (key1455, -1)]

theorem rawRowCheck6620 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form6 = rawRow6620 := by decide +kernel

def row6620 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

theorem rowCheck6620 : row6620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6620 := by decide +kernel

theorem rowEval6620 (x : Key → ℝ) : Integer.Sparse.eval row6620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6620, Integer.Sparse.eval_collectBalanced, rawRowCheck6620]

def rawRow6621 : Integer.Sparse Key := [(key1667, -1), (key1659, -1), (key1655, 2), (key1667, -1), (key1659, -1), (key1596, 2), (key1559, 2), (key1573, -1), (key1546, -1), (key1655, 2), (key1573, -1), (key1546, -1), (key1825, 1), (key1817, 1), (key1813, -2), (key1825, 1), (key1817, 1), (key1447, -2), (key1329, -2), (key1424, 1), (key1316, 1), (key1813, -2), (key1424, 1), (key1316, 1), (key1798, -1), (key1780, -1), (key1788, 1), (key1772, 1), (key1466, 1), (key1345, 1), (key1455, -1), (key1337, -1), (key1798, -1), (key1780, -1), (key1466, 1), (key1345, 1), (key1788, 1), (key1772, 1), (key1455, -1), (key1337, -1)]

theorem rawRowCheck6621 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form6 = rawRow6621 := by decide +kernel

def row6621 : Integer.Sparse Key := [(key1316, 2), (key1329, -2), (key1337, -2), (key1345, 2), (key1424, 2), (key1447, -2), (key1455, -2), (key1466, 2), (key1546, -2), (key1559, 2), (key1573, -2), (key1596, 2), (key1655, 4), (key1659, -2), (key1667, -2), (key1772, 2), (key1780, -2), (key1788, 2), (key1798, -2), (key1813, -4), (key1817, 2), (key1825, 2)]

theorem rowCheck6621 : row6621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6621 := by decide +kernel

theorem rowEval6621 (x : Key → ℝ) : Integer.Sparse.eval row6621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6621, Integer.Sparse.eval_collectBalanced, rawRowCheck6621]

def rawRow6622 : Integer.Sparse Key := [(key1772, -1), (key1774, -1), (key1780, 2), (key1788, -1), (key1790, -1), (key1813, 2), (key1839, 2), (key1817, -1), (key1841, -1), (key1798, 2), (key1825, -1), (key1844, -1), (key1337, 1), (key1339, 1), (key1345, -2), (key1455, 1), (key1457, 1), (key1655, -2), (key1839, -2), (key1659, 1), (key1841, 1), (key1466, -2), (key1667, 1), (key1844, 1), (key1316, -1), (key1339, -1), (key1329, 1), (key1345, 1), (key1546, 1), (key1774, 1), (key1559, -1), (key1780, -1), (key1424, -1), (key1457, -1), (key1573, 1), (key1790, 1), (key1447, 1), (key1466, 1), (key1596, -1), (key1798, -1)]

theorem rawRowCheck6622 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form6 = rawRow6622 := by decide +kernel

def row6622 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6622 : row6622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6622 := by decide +kernel

theorem rowEval6622 (x : Key → ℝ) : Integer.Sparse.eval row6622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6622, Integer.Sparse.eval_collectBalanced, rawRowCheck6622]

def rawRow6623 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1780, 2), (key1790, -1), (key1788, -1), (key1839, 2), (key1813, 2), (key1841, -1), (key1817, -1), (key1798, 2), (key1844, -1), (key1825, -1), (key1339, 1), (key1337, 1), (key1345, -2), (key1457, 1), (key1455, 1), (key1839, -2), (key1655, -2), (key1841, 1), (key1659, 1), (key1466, -2), (key1844, 1), (key1667, 1), (key1339, -1), (key1316, -1), (key1345, 1), (key1329, 1), (key1774, 1), (key1546, 1), (key1780, -1), (key1559, -1), (key1457, -1), (key1424, -1), (key1790, 1), (key1573, 1), (key1466, 1), (key1447, 1), (key1798, -1), (key1596, -1)]

theorem rawRowCheck6623 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form6 = rawRow6623 := by decide +kernel

def row6623 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6623 : row6623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6623 := by decide +kernel

theorem rowEval6623 (x : Key → ℝ) : Integer.Sparse.eval row6623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6623, Integer.Sparse.eval_collectBalanced, rawRowCheck6623]

def rawRow6624 : Integer.Sparse Key := [(key1774, -1), (key1780, -1), (key1772, 2), (key1839, -1), (key1841, -1), (key1790, 2), (key1817, 2), (key1788, -1), (key1813, -1), (key1844, 2), (key1798, -1), (key1825, -1), (key1339, 1), (key1345, 1), (key1337, -2), (key1839, 1), (key1841, 1), (key1457, -2), (key1659, -2), (key1455, 1), (key1655, 1), (key1844, -2), (key1466, 1), (key1667, 1), (key1302, -1), (key1329, -1), (key1296, 1), (key1316, 1), (key1397, 1), (key1559, 1), (key1391, -1), (key1546, -1), (key1790, -1), (key1817, -1), (key1457, 1), (key1659, 1), (key1798, 1), (key1825, 1), (key1466, -1), (key1667, -1)]

theorem rawRowCheck6624 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form6 = rawRow6624 := by decide +kernel

def row6624 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6624 : row6624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6624 := by decide +kernel

theorem rowEval6624 (x : Key → ℝ) : Integer.Sparse.eval row6624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6624, Integer.Sparse.eval_collectBalanced, rawRowCheck6624]

def rawRow6625 : Integer.Sparse Key := [(key1780, -1), (key1774, -1), (key1772, 2), (key1841, -1), (key1839, -1), (key1817, 2), (key1790, 2), (key1813, -1), (key1788, -1), (key1844, 2), (key1825, -1), (key1798, -1), (key1345, 1), (key1339, 1), (key1337, -2), (key1841, 1), (key1839, 1), (key1659, -2), (key1457, -2), (key1655, 1), (key1455, 1), (key1844, -2), (key1667, 1), (key1466, 1), (key1329, -1), (key1302, -1), (key1316, 1), (key1296, 1), (key1559, 1), (key1397, 1), (key1546, -1), (key1391, -1), (key1817, -1), (key1790, -1), (key1659, 1), (key1457, 1), (key1825, 1), (key1798, 1), (key1667, -1), (key1466, -1)]

theorem rawRowCheck6625 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form6 = rawRow6625 := by decide +kernel

def row6625 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6625 : row6625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6625 := by decide +kernel

theorem rowEval6625 (x : Key → ℝ) : Integer.Sparse.eval row6625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6625, Integer.Sparse.eval_collectBalanced, rawRowCheck6625]

def rawRow6626 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1798, 2), (key1772, -1), (key1774, -1), (key1813, 2), (key1839, 2), (key1825, -1), (key1844, -1), (key1780, 2), (key1817, -1), (key1841, -1), (key1455, 1), (key1457, 1), (key1466, -2), (key1337, 1), (key1339, 1), (key1655, -2), (key1839, -2), (key1667, 1), (key1844, 1), (key1345, -2), (key1659, 1), (key1841, 1), (key1424, -1), (key1457, -1), (key1447, 1), (key1466, 1), (key1573, 1), (key1790, 1), (key1596, -1), (key1798, -1), (key1316, -1), (key1339, -1), (key1546, 1), (key1774, 1), (key1329, 1), (key1345, 1), (key1559, -1), (key1780, -1)]

theorem rawRowCheck6626 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form6 = rawRow6626 := by decide +kernel

def row6626 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6626 : row6626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6626 := by decide +kernel

theorem rowEval6626 (x : Key → ℝ) : Integer.Sparse.eval row6626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6626, Integer.Sparse.eval_collectBalanced, rawRowCheck6626]

def rawRow6627 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1798, 2), (key1774, -1), (key1772, -1), (key1839, 2), (key1813, 2), (key1844, -1), (key1825, -1), (key1780, 2), (key1841, -1), (key1817, -1), (key1457, 1), (key1455, 1), (key1466, -2), (key1339, 1), (key1337, 1), (key1839, -2), (key1655, -2), (key1844, 1), (key1667, 1), (key1345, -2), (key1841, 1), (key1659, 1), (key1457, -1), (key1424, -1), (key1466, 1), (key1447, 1), (key1790, 1), (key1573, 1), (key1798, -1), (key1596, -1), (key1339, -1), (key1316, -1), (key1774, 1), (key1546, 1), (key1345, 1), (key1329, 1), (key1780, -1), (key1559, -1)]

theorem rawRowCheck6627 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form6 = rawRow6627 := by decide +kernel

def row6627 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6627 : row6627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6627 := by decide +kernel

theorem rowEval6627 (x : Key → ℝ) : Integer.Sparse.eval row6627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6627, Integer.Sparse.eval_collectBalanced, rawRowCheck6627]

def rawRow6628 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1790, 2), (key1813, -1), (key1825, -1), (key1772, 2), (key1844, 2), (key1774, -1), (key1839, -1), (key1817, 2), (key1780, -1), (key1841, -1), (key1455, 1), (key1466, 1), (key1457, -2), (key1655, 1), (key1667, 1), (key1337, -2), (key1844, -2), (key1339, 1), (key1839, 1), (key1659, -2), (key1345, 1), (key1841, 1), (key1391, -1), (key1466, -1), (key1397, 1), (key1457, 1), (key1296, 1), (key1798, 1), (key1302, -1), (key1790, -1), (key1546, -1), (key1667, -1), (key1316, 1), (key1825, 1), (key1559, 1), (key1659, 1), (key1329, -1), (key1817, -1)]

theorem rawRowCheck6628 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form6 = rawRow6628 := by decide +kernel

def row6628 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6628 : row6628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6628 := by decide +kernel

theorem rowEval6628 (x : Key → ℝ) : Integer.Sparse.eval row6628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6628, Integer.Sparse.eval_collectBalanced, rawRowCheck6628]

def rawRow6629 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1790, 2), (key1825, -1), (key1813, -1), (key1844, 2), (key1772, 2), (key1839, -1), (key1774, -1), (key1817, 2), (key1841, -1), (key1780, -1), (key1466, 1), (key1455, 1), (key1457, -2), (key1667, 1), (key1655, 1), (key1844, -2), (key1337, -2), (key1839, 1), (key1339, 1), (key1659, -2), (key1841, 1), (key1345, 1), (key1466, -1), (key1391, -1), (key1457, 1), (key1397, 1), (key1798, 1), (key1296, 1), (key1790, -1), (key1302, -1), (key1667, -1), (key1546, -1), (key1825, 1), (key1316, 1), (key1659, 1), (key1559, 1), (key1817, -1), (key1329, -1)]

theorem rawRowCheck6629 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form6 = rawRow6629 := by decide +kernel

def row6629 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6629 : row6629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6629 := by decide +kernel

theorem rowEval6629 (x : Key → ℝ) : Integer.Sparse.eval row6629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6629, Integer.Sparse.eval_collectBalanced, rawRowCheck6629]

def rawRow6630 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1817, 2), (key1788, -1), (key1798, -1), (key1772, 2), (key1844, 2), (key1780, -1), (key1841, -1), (key1790, 2), (key1774, -1), (key1839, -1), (key1655, 1), (key1667, 1), (key1659, -2), (key1455, 1), (key1466, 1), (key1337, -2), (key1844, -2), (key1345, 1), (key1841, 1), (key1457, -2), (key1339, 1), (key1839, 1), (key1546, -1), (key1667, -1), (key1559, 1), (key1659, 1), (key1316, 1), (key1825, 1), (key1329, -1), (key1817, -1), (key1391, -1), (key1466, -1), (key1296, 1), (key1798, 1), (key1397, 1), (key1457, 1), (key1302, -1), (key1790, -1)]

theorem rawRowCheck6630 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form6 = rawRow6630 := by decide +kernel

def row6630 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6630 : row6630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6630 := by decide +kernel

theorem rowEval6630 (x : Key → ℝ) : Integer.Sparse.eval row6630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6630, Integer.Sparse.eval_collectBalanced, rawRowCheck6630]

def rawRow6631 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1817, 2), (key1798, -1), (key1788, -1), (key1844, 2), (key1772, 2), (key1841, -1), (key1780, -1), (key1790, 2), (key1839, -1), (key1774, -1), (key1667, 1), (key1655, 1), (key1659, -2), (key1466, 1), (key1455, 1), (key1844, -2), (key1337, -2), (key1841, 1), (key1345, 1), (key1457, -2), (key1839, 1), (key1339, 1), (key1667, -1), (key1546, -1), (key1659, 1), (key1559, 1), (key1825, 1), (key1316, 1), (key1817, -1), (key1329, -1), (key1466, -1), (key1391, -1), (key1798, 1), (key1296, 1), (key1457, 1), (key1397, 1), (key1790, -1), (key1302, -1)]

theorem rawRowCheck6631 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form6 = rawRow6631 := by decide +kernel

def row6631 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6631 : row6631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6631 := by decide +kernel

theorem rowEval6631 (x : Key → ℝ) : Integer.Sparse.eval row6631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6631, Integer.Sparse.eval_collectBalanced, rawRowCheck6631]

def rawRow6632 : Integer.Sparse Key := [(key1817, -1), (key1825, -1), (key1813, 2), (key1841, -1), (key1844, -1), (key1780, 2), (key1798, 2), (key1772, -1), (key1788, -1), (key1839, 2), (key1774, -1), (key1790, -1), (key1659, 1), (key1667, 1), (key1655, -2), (key1841, 1), (key1844, 1), (key1345, -2), (key1466, -2), (key1337, 1), (key1455, 1), (key1839, -2), (key1339, 1), (key1457, 1), (key1559, -1), (key1596, -1), (key1546, 1), (key1573, 1), (key1329, 1), (key1447, 1), (key1316, -1), (key1424, -1), (key1780, -1), (key1798, -1), (key1345, 1), (key1466, 1), (key1774, 1), (key1790, 1), (key1339, -1), (key1457, -1)]

theorem rawRowCheck6632 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form6 = rawRow6632 := by decide +kernel

def row6632 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6632 : row6632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6632 := by decide +kernel

theorem rowEval6632 (x : Key → ℝ) : Integer.Sparse.eval row6632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6632, Integer.Sparse.eval_collectBalanced, rawRowCheck6632]

def rawRow6633 : Integer.Sparse Key := [(key1825, -1), (key1817, -1), (key1813, 2), (key1844, -1), (key1841, -1), (key1798, 2), (key1780, 2), (key1788, -1), (key1772, -1), (key1839, 2), (key1790, -1), (key1774, -1), (key1667, 1), (key1659, 1), (key1655, -2), (key1844, 1), (key1841, 1), (key1466, -2), (key1345, -2), (key1455, 1), (key1337, 1), (key1839, -2), (key1457, 1), (key1339, 1), (key1596, -1), (key1559, -1), (key1573, 1), (key1546, 1), (key1447, 1), (key1329, 1), (key1424, -1), (key1316, -1), (key1798, -1), (key1780, -1), (key1466, 1), (key1345, 1), (key1790, 1), (key1774, 1), (key1457, -1), (key1339, -1)]

theorem rawRowCheck6633 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form6 = rawRow6633 := by decide +kernel

def row6633 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6633 : row6633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6633 := by decide +kernel

theorem rowEval6633 (x : Key → ℝ) : Integer.Sparse.eval row6633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6633, Integer.Sparse.eval_collectBalanced, rawRowCheck6633]

def rawRow6634 : Integer.Sparse Key := [(key1839, -1), (key1841, -1), (key1844, 2), (key1774, -1), (key1780, -1), (key1790, 2), (key1817, 2), (key1798, -1), (key1825, -1), (key1772, 2), (key1788, -1), (key1813, -1), (key1839, 1), (key1841, 1), (key1844, -2), (key1339, 1), (key1345, 1), (key1457, -2), (key1659, -2), (key1466, 1), (key1667, 1), (key1337, -2), (key1455, 1), (key1655, 1), (key1790, -1), (key1817, -1), (key1798, 1), (key1825, 1), (key1457, 1), (key1659, 1), (key1466, -1), (key1667, -1), (key1302, -1), (key1329, -1), (key1397, 1), (key1559, 1), (key1296, 1), (key1316, 1), (key1391, -1), (key1546, -1)]

theorem rawRowCheck6634 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form6 = rawRow6634 := by decide +kernel

def row6634 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6634 : row6634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6634 := by decide +kernel

theorem rowEval6634 (x : Key → ℝ) : Integer.Sparse.eval row6634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6634, Integer.Sparse.eval_collectBalanced, rawRowCheck6634]

def rawRow6635 : Integer.Sparse Key := [(key1841, -1), (key1839, -1), (key1844, 2), (key1780, -1), (key1774, -1), (key1817, 2), (key1790, 2), (key1825, -1), (key1798, -1), (key1772, 2), (key1813, -1), (key1788, -1), (key1841, 1), (key1839, 1), (key1844, -2), (key1345, 1), (key1339, 1), (key1659, -2), (key1457, -2), (key1667, 1), (key1466, 1), (key1337, -2), (key1655, 1), (key1455, 1), (key1817, -1), (key1790, -1), (key1825, 1), (key1798, 1), (key1659, 1), (key1457, 1), (key1667, -1), (key1466, -1), (key1329, -1), (key1302, -1), (key1559, 1), (key1397, 1), (key1316, 1), (key1296, 1), (key1546, -1), (key1391, -1)]

theorem rawRowCheck6635 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form6 = rawRow6635 := by decide +kernel

def row6635 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, 1), (key1329, -1), (key1337, -2), (key1339, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, 1), (key1659, -1), (key1772, 2), (key1774, -1), (key1780, -1), (key1788, -1), (key1790, 1), (key1813, -1), (key1817, 1)]

theorem rowCheck6635 : row6635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6635 := by decide +kernel

theorem rowEval6635 (x : Key → ℝ) : Integer.Sparse.eval row6635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6635, Integer.Sparse.eval_collectBalanced, rawRowCheck6635]

def rawRow6636 : Integer.Sparse Key := [(key1841, -1), (key1844, -1), (key1839, 2), (key1817, -1), (key1825, -1), (key1780, 2), (key1798, 2), (key1774, -1), (key1790, -1), (key1813, 2), (key1772, -1), (key1788, -1), (key1841, 1), (key1844, 1), (key1839, -2), (key1659, 1), (key1667, 1), (key1345, -2), (key1466, -2), (key1339, 1), (key1457, 1), (key1655, -2), (key1337, 1), (key1455, 1), (key1780, -1), (key1798, -1), (key1774, 1), (key1790, 1), (key1345, 1), (key1466, 1), (key1339, -1), (key1457, -1), (key1559, -1), (key1596, -1), (key1329, 1), (key1447, 1), (key1546, 1), (key1573, 1), (key1316, -1), (key1424, -1)]

theorem rawRowCheck6636 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form6 = rawRow6636 := by decide +kernel

def row6636 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6636 : row6636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6636 := by decide +kernel

theorem rowEval6636 (x : Key → ℝ) : Integer.Sparse.eval row6636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6636, Integer.Sparse.eval_collectBalanced, rawRowCheck6636]

def rawRow6637 : Integer.Sparse Key := [(key1844, -1), (key1841, -1), (key1839, 2), (key1825, -1), (key1817, -1), (key1798, 2), (key1780, 2), (key1790, -1), (key1774, -1), (key1813, 2), (key1788, -1), (key1772, -1), (key1844, 1), (key1841, 1), (key1839, -2), (key1667, 1), (key1659, 1), (key1466, -2), (key1345, -2), (key1457, 1), (key1339, 1), (key1655, -2), (key1455, 1), (key1337, 1), (key1798, -1), (key1780, -1), (key1790, 1), (key1774, 1), (key1466, 1), (key1345, 1), (key1457, -1), (key1339, -1), (key1596, -1), (key1559, -1), (key1447, 1), (key1329, 1), (key1573, 1), (key1546, 1), (key1424, -1), (key1316, -1)]

theorem rawRowCheck6637 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form6 = rawRow6637 := by decide +kernel

def row6637 : Integer.Sparse Key := [(key1316, -1), (key1329, 1), (key1337, 1), (key1345, -1), (key1424, -1), (key1447, 1), (key1455, 1), (key1466, -1), (key1546, 1), (key1559, -1), (key1573, 1), (key1596, -1), (key1655, -2), (key1659, 1), (key1667, 1), (key1772, -1), (key1780, 1), (key1788, -1), (key1798, 1), (key1813, 2), (key1817, -1), (key1825, -1)]

theorem rowCheck6637 : row6637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6637 := by decide +kernel

theorem rowEval6637 (x : Key → ℝ) : Integer.Sparse.eval row6637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6637, Integer.Sparse.eval_collectBalanced, rawRowCheck6637]

def rawRow6638 : Integer.Sparse Key := [(key2671, 1), (key2671, 1), (key2676, -2), (key2706, 1), (key2706, 1), (key2726, -2), (key2726, -2), (key2732, 1), (key2732, 1), (key2753, -2), (key2758, 1), (key2758, 1), (key2786, -1), (key2786, -1), (key2798, 1), (key2798, 1), (key2809, -1), (key2809, -1), (key2829, 1), (key2829, 1), (key2870, 1), (key2870, 1), (key2885, -1), (key2885, -1), (key2920, 1), (key2920, 1), (key2927, -1), (key2927, -1), (key3008, 2), (key3010, -1), (key3010, -1), (key3012, 2), (key3017, -1), (key3017, -1), (key3023, -1), (key3023, -1), (key3026, -1), (key3026, -1), (key3030, 2), (key3030, 2)]

theorem rawRowCheck6638 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form7 = rawRow6638 := by decide +kernel

def row6638 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck6638 : row6638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6638 := by decide +kernel

theorem rowEval6638 (x : Key → ℝ) : Integer.Sparse.eval row6638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6638, Integer.Sparse.eval_collectBalanced, rawRowCheck6638]

def rawRow6639 : Integer.Sparse Key := [(key2671, 1), (key2676, 1), (key2671, -2), (key2726, 1), (key2732, 1), (key2706, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2758, -2), (key2753, 1), (key2758, 1), (key2794, -1), (key2798, -1), (key2786, 1), (key2794, 1), (key2829, -1), (key2835, -1), (key2809, 1), (key2835, 1), (key2860, 1), (key2885, 1), (key2860, -1), (key2870, -1), (key2923, 1), (key2927, 1), (key2920, -1), (key2923, -1), (key3010, 2), (key3008, -1), (key3010, -1), (key3017, 2), (key3012, -1), (key3017, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3030, -1), (key3023, 2), (key3026, 2)]

theorem rawRowCheck6639 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form7 = rawRow6639 := by decide +kernel

def row6639 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6639 : row6639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6639 := by decide +kernel

theorem rowEval6639 (x : Key → ℝ) : Integer.Sparse.eval row6639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6639, Integer.Sparse.eval_collectBalanced, rawRowCheck6639]

def rawRow6640 : Integer.Sparse Key := [(key2676, 1), (key2671, 1), (key2671, -2), (key2732, 1), (key2726, 1), (key2732, -2), (key2706, -2), (key2726, 1), (key2706, 1), (key2758, -2), (key2758, 1), (key2753, 1), (key2798, -1), (key2794, -1), (key2794, 1), (key2786, 1), (key2835, -1), (key2829, -1), (key2835, 1), (key2809, 1), (key2885, 1), (key2860, 1), (key2870, -1), (key2860, -1), (key2927, 1), (key2923, 1), (key2923, -1), (key2920, -1), (key3010, 2), (key3010, -1), (key3008, -1), (key3017, 2), (key3017, -1), (key3012, -1), (key3030, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3026, 2), (key3023, 2)]

theorem rawRowCheck6640 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form7 = rawRow6640 := by decide +kernel

def row6640 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6640 : row6640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6640 := by decide +kernel

theorem rowEval6640 (x : Key → ℝ) : Integer.Sparse.eval row6640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6640, Integer.Sparse.eval_collectBalanced, rawRowCheck6640]

def rawRow6641 : Integer.Sparse Key := [(key2706, 1), (key2706, 1), (key2753, -2), (key2671, 1), (key2671, 1), (key2726, -2), (key2726, -2), (key2758, 1), (key2758, 1), (key2676, -2), (key2732, 1), (key2732, 1), (key2809, -1), (key2809, -1), (key2920, 1), (key2920, 1), (key2786, -1), (key2786, -1), (key2870, 1), (key2870, 1), (key2829, 1), (key2829, 1), (key2927, -1), (key2927, -1), (key2798, 1), (key2798, 1), (key2885, -1), (key2885, -1), (key3012, 2), (key3023, -1), (key3023, -1), (key3008, 2), (key3026, -1), (key3026, -1), (key3010, -1), (key3010, -1), (key3017, -1), (key3017, -1), (key3030, 2), (key3030, 2)]

theorem rawRowCheck6641 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form7 = rawRow6641 := by decide +kernel

def row6641 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck6641 : row6641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6641 := by decide +kernel

theorem rowEval6641 (x : Key → ℝ) : Integer.Sparse.eval row6641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6641, Integer.Sparse.eval_collectBalanced, rawRowCheck6641]

def rawRow6642 : Integer.Sparse Key := [(key2706, 1), (key2753, 1), (key2706, -2), (key2726, 1), (key2758, 1), (key2671, -2), (key2758, -2), (key2671, 1), (key2726, 1), (key2732, -2), (key2676, 1), (key2732, 1), (key2860, -1), (key2920, -1), (key2809, 1), (key2860, 1), (key2870, -1), (key2923, -1), (key2786, 1), (key2923, 1), (key2794, 1), (key2927, 1), (key2794, -1), (key2829, -1), (key2835, 1), (key2885, 1), (key2798, -1), (key2835, -1), (key3023, 2), (key3012, -1), (key3023, -1), (key3026, 2), (key3008, -1), (key3026, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3030, -1), (key3010, 2), (key3017, 2)]

theorem rawRowCheck6642 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form7 = rawRow6642 := by decide +kernel

def row6642 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6642 : row6642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6642 := by decide +kernel

theorem rowEval6642 (x : Key → ℝ) : Integer.Sparse.eval row6642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6642, Integer.Sparse.eval_collectBalanced, rawRowCheck6642]

def rawRow6643 : Integer.Sparse Key := [(key2753, 1), (key2706, 1), (key2706, -2), (key2758, 1), (key2726, 1), (key2758, -2), (key2671, -2), (key2726, 1), (key2671, 1), (key2732, -2), (key2732, 1), (key2676, 1), (key2920, -1), (key2860, -1), (key2860, 1), (key2809, 1), (key2923, -1), (key2870, -1), (key2923, 1), (key2786, 1), (key2927, 1), (key2794, 1), (key2829, -1), (key2794, -1), (key2885, 1), (key2835, 1), (key2835, -1), (key2798, -1), (key3023, 2), (key3023, -1), (key3012, -1), (key3026, 2), (key3026, -1), (key3008, -1), (key3030, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3017, 2), (key3010, 2)]

theorem rawRowCheck6643 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form7 = rawRow6643 := by decide +kernel

def row6643 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6643 : row6643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6643 := by decide +kernel

theorem rowEval6643 (x : Key → ℝ) : Integer.Sparse.eval row6643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6643, Integer.Sparse.eval_collectBalanced, rawRowCheck6643]

def rawRow6644 : Integer.Sparse Key := [(key2726, 1), (key2732, 1), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, -2), (key2732, -2), (key2753, 1), (key2758, 1), (key2671, -2), (key2706, 1), (key2726, 1), (key2829, -1), (key2835, -1), (key2923, 1), (key2927, 1), (key2794, -1), (key2798, -1), (key2860, 1), (key2885, 1), (key2809, 1), (key2835, 1), (key2920, -1), (key2923, -1), (key2786, 1), (key2794, 1), (key2860, -1), (key2870, -1), (key3017, 2), (key3026, -1), (key3030, -1), (key3010, 2), (key3023, -1), (key3030, -1), (key3008, -1), (key3010, -1), (key3012, -1), (key3017, -1), (key3023, 2), (key3026, 2)]

theorem rawRowCheck6644 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form7 = rawRow6644 := by decide +kernel

def row6644 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6644 : row6644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6644 := by decide +kernel

theorem rowEval6644 (x : Key → ℝ) : Integer.Sparse.eval row6644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6644, Integer.Sparse.eval_collectBalanced, rawRowCheck6644]

def rawRow6645 : Integer.Sparse Key := [(key2732, 1), (key2726, 1), (key2758, -2), (key2676, 1), (key2671, 1), (key2732, -2), (key2706, -2), (key2758, 1), (key2753, 1), (key2671, -2), (key2726, 1), (key2706, 1), (key2835, -1), (key2829, -1), (key2927, 1), (key2923, 1), (key2798, -1), (key2794, -1), (key2885, 1), (key2860, 1), (key2835, 1), (key2809, 1), (key2923, -1), (key2920, -1), (key2794, 1), (key2786, 1), (key2870, -1), (key2860, -1), (key3017, 2), (key3030, -1), (key3026, -1), (key3010, 2), (key3030, -1), (key3023, -1), (key3010, -1), (key3008, -1), (key3017, -1), (key3012, -1), (key3026, 2), (key3023, 2)]

theorem rawRowCheck6645 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form7 = rawRow6645 := by decide +kernel

def row6645 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6645 : row6645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6645 := by decide +kernel

theorem rowEval6645 (x : Key → ℝ) : Integer.Sparse.eval row6645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6645, Integer.Sparse.eval_collectBalanced, rawRowCheck6645]

def rawRow6646 : Integer.Sparse Key := [(key2726, 1), (key2758, 1), (key2732, -2), (key2706, 1), (key2753, 1), (key2671, -2), (key2758, -2), (key2676, 1), (key2732, 1), (key2706, -2), (key2671, 1), (key2726, 1), (key2870, -1), (key2923, -1), (key2835, 1), (key2885, 1), (key2860, -1), (key2920, -1), (key2794, 1), (key2927, 1), (key2786, 1), (key2923, 1), (key2798, -1), (key2835, -1), (key2809, 1), (key2860, 1), (key2794, -1), (key2829, -1), (key3026, 2), (key3017, -1), (key3030, -1), (key3023, 2), (key3010, -1), (key3030, -1), (key3012, -1), (key3023, -1), (key3008, -1), (key3026, -1), (key3010, 2), (key3017, 2)]

theorem rawRowCheck6646 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form7 = rawRow6646 := by decide +kernel

def row6646 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6646 : row6646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6646 := by decide +kernel

theorem rowEval6646 (x : Key → ℝ) : Integer.Sparse.eval row6646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6646, Integer.Sparse.eval_collectBalanced, rawRowCheck6646]

def rawRow6647 : Integer.Sparse Key := [(key2758, 1), (key2726, 1), (key2732, -2), (key2753, 1), (key2706, 1), (key2758, -2), (key2671, -2), (key2732, 1), (key2676, 1), (key2706, -2), (key2726, 1), (key2671, 1), (key2923, -1), (key2870, -1), (key2885, 1), (key2835, 1), (key2920, -1), (key2860, -1), (key2927, 1), (key2794, 1), (key2923, 1), (key2786, 1), (key2835, -1), (key2798, -1), (key2860, 1), (key2809, 1), (key2829, -1), (key2794, -1), (key3026, 2), (key3030, -1), (key3017, -1), (key3023, 2), (key3030, -1), (key3010, -1), (key3023, -1), (key3012, -1), (key3026, -1), (key3008, -1), (key3017, 2), (key3010, 2)]

theorem rawRowCheck6647 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form7 = rawRow6647 := by decide +kernel

def row6647 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6647 : row6647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6647 := by decide +kernel

theorem rowEval6647 (x : Key → ℝ) : Integer.Sparse.eval row6647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6647, Integer.Sparse.eval_collectBalanced, rawRowCheck6647]

def rawRow6648 : Integer.Sparse Key := [(key2732, 1), (key2758, 1), (key2726, -2), (key2732, 1), (key2758, 1), (key2676, -2), (key2753, -2), (key2671, 1), (key2706, 1), (key2726, -2), (key2671, 1), (key2706, 1), (key2885, -1), (key2927, -1), (key2829, 1), (key2870, 1), (key2885, -1), (key2927, -1), (key2798, 1), (key2920, 1), (key2798, 1), (key2920, 1), (key2786, -1), (key2809, -1), (key2829, 1), (key2870, 1), (key2786, -1), (key2809, -1), (key3030, 2), (key3017, -1), (key3026, -1), (key3030, 2), (key3010, -1), (key3023, -1), (key3017, -1), (key3026, -1), (key3010, -1), (key3023, -1), (key3008, 2), (key3012, 2)]

theorem rawRowCheck6648 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form7 = rawRow6648 := by decide +kernel

def row6648 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck6648 : row6648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6648 := by decide +kernel

theorem rowEval6648 (x : Key → ℝ) : Integer.Sparse.eval row6648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6648, Integer.Sparse.eval_collectBalanced, rawRowCheck6648]

def rawRow6649 : Integer.Sparse Key := [(key2758, 1), (key2732, 1), (key2726, -2), (key2758, 1), (key2732, 1), (key2753, -2), (key2676, -2), (key2706, 1), (key2671, 1), (key2726, -2), (key2706, 1), (key2671, 1), (key2927, -1), (key2885, -1), (key2870, 1), (key2829, 1), (key2927, -1), (key2885, -1), (key2920, 1), (key2798, 1), (key2920, 1), (key2798, 1), (key2809, -1), (key2786, -1), (key2870, 1), (key2829, 1), (key2809, -1), (key2786, -1), (key3030, 2), (key3026, -1), (key3017, -1), (key3030, 2), (key3023, -1), (key3010, -1), (key3026, -1), (key3017, -1), (key3023, -1), (key3010, -1), (key3012, 2), (key3008, 2)]

theorem rawRowCheck6649 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form7 = rawRow6649 := by decide +kernel

def row6649 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck6649 : row6649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6649 := by decide +kernel

theorem rowEval6649 (x : Key → ℝ) : Integer.Sparse.eval row6649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6649, Integer.Sparse.eval_collectBalanced, rawRowCheck6649]

def rawRow6650 : Integer.Sparse Key := [(key2628, 1), (key2628, 1), (key2641, -2), (key2702, 1), (key2702, 1), (key2972, -2), (key2972, -2), (key2976, 1), (key2976, 1), (key2728, -2), (key2983, 1), (key2983, 1), (key2612, -1), (key2616, -1), (key2660, 1), (key2660, 1), (key2671, -1), (key2671, -1), (key2726, 1), (key2726, 1), (key2829, 1), (key2829, 1), (key2927, -1), (key2927, -1), (key3010, 1), (key3010, 1), (key3030, -1), (key3030, -1), (key2621, 2), (key2644, -1), (key2644, -1), (key2676, 2), (key2732, -1), (key2732, -1), (key2798, -1), (key2798, -1), (key2835, -1), (key2835, -1), (key2885, 2), (key2885, 2)]

theorem rawRowCheck6650 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form7 = rawRow6650 := by decide +kernel

def row6650 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2732, -2), (key2798, -2), (key2829, 2), (key2835, -2), (key2885, 4), (key2927, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3010, 2), (key3030, -2)]

theorem rowCheck6650 : row6650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6650 := by decide +kernel

theorem rowEval6650 (x : Key → ℝ) : Integer.Sparse.eval row6650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6650, Integer.Sparse.eval_collectBalanced, rawRowCheck6650]

def rawRow6651 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2628, -2), (key2972, 1), (key2976, 1), (key2702, -2), (key2976, -2), (key2702, 1), (key2972, 1), (key2983, -2), (key2728, 1), (key2983, 1), (key2646, -1), (key2653, -1), (key2616, 1), (key2640, 1), (key2726, -1), (key2758, -1), (key2671, 1), (key2758, 1), (key2794, 1), (key2927, 1), (key2794, -1), (key2829, -1), (key3017, 1), (key3030, 1), (key3010, -1), (key3017, -1), (key2644, 2), (key2621, -1), (key2644, -1), (key2732, 2), (key2676, -1), (key2732, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2885, -1), (key2798, 2), (key2835, 2)]

theorem rawRowCheck6651 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form7 = rawRow6651 := by decide +kernel

def row6651 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2927, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3030, 1)]

theorem rowCheck6651 : row6651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6651 := by decide +kernel

theorem rowEval6651 (x : Key → ℝ) : Integer.Sparse.eval row6651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6651, Integer.Sparse.eval_collectBalanced, rawRowCheck6651]

def rawRow6652 : Integer.Sparse Key := [(key2641, 1), (key2628, 1), (key2628, -2), (key2976, 1), (key2972, 1), (key2976, -2), (key2702, -2), (key2972, 1), (key2702, 1), (key2983, -2), (key2983, 1), (key2728, 1), (key2653, -1), (key2646, -1), (key2640, 1), (key2616, 1), (key2758, -1), (key2726, -1), (key2758, 1), (key2671, 1), (key2927, 1), (key2794, 1), (key2829, -1), (key2794, -1), (key3030, 1), (key3017, 1), (key3017, -1), (key3010, -1), (key2644, 2), (key2644, -1), (key2621, -1), (key2732, 2), (key2732, -1), (key2676, -1), (key2885, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2835, 2), (key2798, 2)]

theorem rawRowCheck6652 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form7 = rawRow6652 := by decide +kernel

def row6652 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2671, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2798, 1), (key2829, -1), (key2835, 1), (key2885, -2), (key2927, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3030, 1)]

theorem rowCheck6652 : row6652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6652 := by decide +kernel

theorem rowEval6652 (x : Key → ℝ) : Integer.Sparse.eval row6652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6652, Integer.Sparse.eval_collectBalanced, rawRowCheck6652]

def rawRow6653 : Integer.Sparse Key := [(key2702, 1), (key2702, 1), (key2728, -2), (key2628, 1), (key2628, 1), (key2972, -2), (key2972, -2), (key2983, 1), (key2983, 1), (key2641, -2), (key2976, 1), (key2976, 1), (key2667, -1), (key2667, -1), (key2747, 1), (key2747, 1), (key2612, -1), (key2616, -1), (key2829, 1), (key2829, 1), (key2726, 1), (key2726, 1), (key3030, -1), (key3030, -1), (key2660, 1), (key2660, 1), (key2927, -1), (key2927, -1), (key2676, 2), (key2798, -1), (key2798, -1), (key2621, 2), (key2835, -1), (key2835, -1), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, 2), (key2885, 2)]

theorem rawRowCheck6653 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form7 = rawRow6653 := by decide +kernel

def row6653 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, 2), (key2641, -2), (key2644, -2), (key2660, 2), (key2667, -2), (key2676, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2732, -2), (key2747, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2885, 4), (key2927, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3030, -2)]

theorem rowCheck6653 : row6653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6653 := by decide +kernel

theorem rowEval6653 (x : Key → ℝ) : Integer.Sparse.eval row6653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6653, Integer.Sparse.eval_collectBalanced, rawRowCheck6653]

def rawRow6654 : Integer.Sparse Key := [(key2702, 1), (key2728, 1), (key2702, -2), (key2972, 1), (key2983, 1), (key2628, -2), (key2983, -2), (key2628, 1), (key2972, 1), (key2976, -2), (key2641, 1), (key2976, 1), (key2735, -1), (key2747, -1), (key2667, 1), (key2735, 1), (key2948, -1), (key2960, -1), (key2612, 1), (key2960, 1), (key2640, 1), (key3030, 1), (key2640, -1), (key2726, -1), (key2758, 1), (key2927, 1), (key2660, -1), (key2758, -1), (key2798, 2), (key2676, -1), (key2798, -1), (key2835, 2), (key2621, -1), (key2835, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, 2), (key2732, 2)]

theorem rawRowCheck6654 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form7 = rawRow6654 := by decide +kernel

def row6654 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2747, -1), (key2798, 1), (key2835, 1), (key2885, -2), (key2927, 1), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key3030, 1)]

theorem rowCheck6654 : row6654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6654 := by decide +kernel

theorem rowEval6654 (x : Key → ℝ) : Integer.Sparse.eval row6654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6654, Integer.Sparse.eval_collectBalanced, rawRowCheck6654]

def rawRow6655 : Integer.Sparse Key := [(key2728, 1), (key2702, 1), (key2702, -2), (key2983, 1), (key2972, 1), (key2983, -2), (key2628, -2), (key2972, 1), (key2628, 1), (key2976, -2), (key2976, 1), (key2641, 1), (key2747, -1), (key2735, -1), (key2735, 1), (key2667, 1), (key2960, -1), (key2948, -1), (key2960, 1), (key2612, 1), (key3030, 1), (key2640, 1), (key2726, -1), (key2640, -1), (key2927, 1), (key2758, 1), (key2758, -1), (key2660, -1), (key2798, 2), (key2798, -1), (key2676, -1), (key2835, 2), (key2835, -1), (key2621, -1), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, 2), (key2644, 2)]

theorem rawRowCheck6655 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form7 = rawRow6655 := by decide +kernel

def row6655 : Integer.Sparse Key := [(key2612, 1), (key2621, -1), (key2628, -1), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, 1), (key2676, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2732, 1), (key2747, -1), (key2798, 1), (key2835, 1), (key2885, -2), (key2927, 1), (key2948, -1), (key2972, 2), (key2976, -1), (key2983, -1), (key3030, 1)]

theorem rowCheck6655 : row6655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6655 := by decide +kernel

theorem rowEval6655 (x : Key → ℝ) : Integer.Sparse.eval row6655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6655, Integer.Sparse.eval_collectBalanced, rawRowCheck6655]

end MUB6.Certificate.GramRows

end OAI
