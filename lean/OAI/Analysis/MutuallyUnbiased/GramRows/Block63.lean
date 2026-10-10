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

def rawRow4992 : Integer.Sparse Key := [(key2671, -2), (key2671, -2), (key2674, -2), (key2786, 1), (key2786, 1), (key2794, 1), (key2794, 1), (key2796, 1), (key2796, 1), (key2616, 2), (key2616, 2), (key2619, 2), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2832, -1), (key2832, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2642, -1), (key2642, -1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2729, 1), (key2729, 1)]

theorem rawRowCheck4992 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form12 = rawRow4992 := by decide +kernel

def row4992 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

theorem rowCheck4992 : row4992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4992 := by decide +kernel

theorem rowEval4992 (x : Key → ℝ) : Integer.Sparse.eval row4992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4992, Integer.Sparse.eval_collectBalanced, rawRowCheck4992]

def rawRow4993 : Integer.Sparse Key := [(key2671, -2), (key2674, -2), (key2671, -2), (key2794, 1), (key2796, 1), (key2786, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2616, 2), (key2619, 2), (key2616, 2), (key2829, -1), (key2832, -1), (key2809, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2640, -1), (key2642, -1), (key2632, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2726, 1), (key2729, 1), (key2706, 1), (key2729, 1), (key2706, 1), (key2726, 1)]

theorem rawRowCheck4993 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form12 = rawRow4993 := by decide +kernel

def row4993 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

theorem rowCheck4993 : row4993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4993 := by decide +kernel

theorem rowEval4993 (x : Key → ℝ) : Integer.Sparse.eval row4993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4993, Integer.Sparse.eval_collectBalanced, rawRowCheck4993]

def rawRow4994 : Integer.Sparse Key := [(key2674, -2), (key2671, -2), (key2671, -2), (key2796, 1), (key2794, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2786, 1), (key2619, 2), (key2616, 2), (key2616, 2), (key2832, -1), (key2829, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2642, -1), (key2640, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2632, -1), (key2729, 1), (key2726, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2706, 1)]

theorem rawRowCheck4994 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form12 = rawRow4994 := by decide +kernel

def row4994 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

theorem rowCheck4994 : row4994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4994 := by decide +kernel

theorem rowEval4994 (x : Key → ℝ) : Integer.Sparse.eval row4994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4994, Integer.Sparse.eval_collectBalanced, rawRowCheck4994]

def rawRow4995 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2671, 1), (key2671, 1), (key2794, 1), (key2794, 1), (key2944, 1), (key2944, 1), (key2809, 2), (key2809, 2), (key2951, 2), (key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1)]

theorem rawRowCheck4995 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form12 = rawRow4995 := by decide +kernel

def row4995 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck4995 : row4995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4995 := by decide +kernel

theorem rowEval4995 (x : Key → ℝ) : Integer.Sparse.eval row4995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4995, Integer.Sparse.eval_collectBalanced, rawRowCheck4995]

def rawRow4996 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2794, 1), (key2944, 1), (key2671, 1), (key2944, 1), (key2671, 1), (key2794, 1), (key2809, 2), (key2951, 2), (key2809, 2), (key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1)]

theorem rawRowCheck4996 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form12 = rawRow4996 := by decide +kernel

def row4996 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck4996 : row4996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4996 := by decide +kernel

theorem rowEval4996 (x : Key → ℝ) : Integer.Sparse.eval row4996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4996, Integer.Sparse.eval_collectBalanced, rawRowCheck4996]

def rawRow4997 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2944, 1), (key2794, 1), (key2944, 1), (key2671, 1), (key2794, 1), (key2671, 1), (key2951, 2), (key2809, 2), (key2809, 2), (key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1)]

theorem rawRowCheck4997 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form12 = rawRow4997 := by decide +kernel

def row4997 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck4997 : row4997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4997 := by decide +kernel

theorem rowEval4997 (x : Key → ℝ) : Integer.Sparse.eval row4997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4997, Integer.Sparse.eval_collectBalanced, rawRowCheck4997]

def rawRow4998 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1), (key2898, 1), (key2898, 1), (key2632, 2), (key2632, 2), (key2649, 2), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2905, -1), (key2905, -1), (key2616, -1), (key2616, -1), (key2640, -1), (key2640, -1), (key2654, -1), (key2654, -1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2748, 1), (key2748, 1)]

theorem rawRowCheck4998 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form12 = rawRow4998 := by decide +kernel

def row4998 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

theorem rowCheck4998 : row4998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4998 := by decide +kernel

theorem rowEval4998 (x : Key → ℝ) : Integer.Sparse.eval row4998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4998, Integer.Sparse.eval_collectBalanced, rawRowCheck4998]

def rawRow4999 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2860, 1), (key2898, 1), (key2809, 1), (key2898, 1), (key2809, 1), (key2860, 1), (key2632, 2), (key2649, 2), (key2632, 2), (key2870, -1), (key2905, -1), (key2786, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2640, -1), (key2654, -1), (key2616, -1), (key2654, -1), (key2616, -1), (key2640, -1), (key2726, 1), (key2748, 1), (key2671, 1), (key2748, 1), (key2671, 1), (key2726, 1)]

theorem rawRowCheck4999 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form12 = rawRow4999 := by decide +kernel

def row4999 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

theorem rowCheck4999 : row4999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4999 := by decide +kernel

theorem rowEval4999 (x : Key → ℝ) : Integer.Sparse.eval row4999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck4999, Integer.Sparse.eval_collectBalanced, rawRowCheck4999]

def rawRow5000 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2898, 1), (key2860, 1), (key2898, 1), (key2809, 1), (key2860, 1), (key2809, 1), (key2649, 2), (key2632, 2), (key2632, 2), (key2905, -1), (key2870, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2786, -1), (key2654, -1), (key2640, -1), (key2654, -1), (key2616, -1), (key2640, -1), (key2616, -1), (key2748, 1), (key2726, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2671, 1)]

theorem rawRowCheck5000 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form12 = rawRow5000 := by decide +kernel

def row5000 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

theorem rowCheck5000 : row5000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5000 := by decide +kernel

theorem rowEval5000 (x : Key → ℝ) : Integer.Sparse.eval row5000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5000, Integer.Sparse.eval_collectBalanced, rawRowCheck5000]

def rawRow5001 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key2977, 1), (key2977, 1), (key2786, 2), (key2786, 2), (key2939, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1)]

theorem rawRowCheck5001 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form12 = rawRow5001 := by decide +kernel

def row5001 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5001 : row5001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5001 := by decide +kernel

theorem rowEval5001 (x : Key → ℝ) : Integer.Sparse.eval row5001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5001, Integer.Sparse.eval_collectBalanced, rawRowCheck5001]

def rawRow5002 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2860, 1), (key2977, 1), (key2706, 1), (key2977, 1), (key2706, 1), (key2860, 1), (key2786, 2), (key2939, 2), (key2786, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1)]

theorem rawRowCheck5002 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form12 = rawRow5002 := by decide +kernel

def row5002 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5002 : row5002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5002 := by decide +kernel

theorem rowEval5002 (x : Key → ℝ) : Integer.Sparse.eval row5002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form12) x := by
  rw [rowCheck5002, Integer.Sparse.eval_collectBalanced, rawRowCheck5002]

def rawRow5003 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2977, 1), (key2860, 1), (key2977, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1)]

theorem rawRowCheck5003 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form12 = rawRow5003 := by decide +kernel

def row5003 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5003 : row5003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5003 := by decide +kernel

theorem rowEval5003 (x : Key → ℝ) : Integer.Sparse.eval row5003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck5003, Integer.Sparse.eval_collectBalanced, rawRowCheck5003]

def rawRow5004 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2082, -2), (key2087, 6), (key2175, 2), (key2175, 2), (key2179, 2), (key2281, -2), (key2330, -2), (key2330, -2), (key2189, -6), (key2289, 2), (key2333, 2), (key2333, 2)]

theorem rawRowCheck5004 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form13 = rawRow5004 := by decide +kernel

def row5004 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

theorem rowCheck5004 : row5004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5004 := by decide +kernel

theorem rowEval5004 (x : Key → ℝ) : Integer.Sparse.eval row5004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5004, Integer.Sparse.eval_collectBalanced, rawRowCheck5004]

def rawRow5005 : Integer.Sparse Key := [(key2078, -2), (key2082, -2), (key2078, -2), (key2087, 6), (key2175, 2), (key2179, 2), (key2175, 2), (key2330, -2), (key2281, -2), (key2330, -2), (key2189, -6), (key2333, 2), (key2289, 2), (key2333, 2)]

theorem rawRowCheck5005 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form13 = rawRow5005 := by decide +kernel

def row5005 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

theorem rowCheck5005 : row5005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5005 := by decide +kernel

theorem rowEval5005 (x : Key → ℝ) : Integer.Sparse.eval row5005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5005, Integer.Sparse.eval_collectBalanced, rawRowCheck5005]

def rawRow5006 : Integer.Sparse Key := [(key2082, -2), (key2078, -2), (key2078, -2), (key2087, 6), (key2179, 2), (key2175, 2), (key2175, 2), (key2330, -2), (key2330, -2), (key2281, -2), (key2189, -6), (key2333, 2), (key2333, 2), (key2289, 2)]

theorem rawRowCheck5006 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form13 = rawRow5006 := by decide +kernel

def row5006 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

theorem rowCheck5006 : row5006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5006 := by decide +kernel

theorem rowEval5006 (x : Key → ℝ) : Integer.Sparse.eval row5006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck5006, Integer.Sparse.eval_collectBalanced, rawRowCheck5006]

def rawRow5007 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2087, -2), (key2082, 6), (key2275, 2), (key2275, 2), (key2281, 2), (key2179, -2), (key2328, -2), (key2328, -2), (key2289, -6), (key2189, 2), (key2333, 2), (key2333, 2)]

theorem rawRowCheck5007 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form13 = rawRow5007 := by decide +kernel

def row5007 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

theorem rowCheck5007 : row5007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5007 := by decide +kernel

theorem rowEval5007 (x : Key → ℝ) : Integer.Sparse.eval row5007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5007, Integer.Sparse.eval_collectBalanced, rawRowCheck5007]

def rawRow5008 : Integer.Sparse Key := [(key2078, -2), (key2087, -2), (key2078, -2), (key2082, 6), (key2275, 2), (key2281, 2), (key2275, 2), (key2328, -2), (key2179, -2), (key2328, -2), (key2289, -6), (key2333, 2), (key2189, 2), (key2333, 2)]

theorem rawRowCheck5008 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form13 = rawRow5008 := by decide +kernel

def row5008 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

theorem rowCheck5008 : row5008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5008 := by decide +kernel

theorem rowEval5008 (x : Key → ℝ) : Integer.Sparse.eval row5008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5008, Integer.Sparse.eval_collectBalanced, rawRowCheck5008]

def rawRow5009 : Integer.Sparse Key := [(key2087, -2), (key2078, -2), (key2078, -2), (key2082, 6), (key2281, 2), (key2275, 2), (key2275, 2), (key2328, -2), (key2328, -2), (key2179, -2), (key2289, -6), (key2333, 2), (key2333, 2), (key2189, 2)]

theorem rawRowCheck5009 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form13 = rawRow5009 := by decide +kernel

def row5009 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

theorem rowCheck5009 : row5009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5009 := by decide +kernel

theorem rowEval5009 (x : Key → ℝ) : Integer.Sparse.eval row5009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5009, Integer.Sparse.eval_collectBalanced, rawRowCheck5009]

def rawRow5010 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2179, -2), (key2189, 6), (key2078, 2), (key2078, 2), (key2082, 2), (key2289, -2), (key2333, -2), (key2333, -2), (key2087, -6), (key2281, 2), (key2330, 2), (key2330, 2)]

theorem rawRowCheck5010 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form13 = rawRow5010 := by decide +kernel

def row5010 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

theorem rowCheck5010 : row5010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5010 := by decide +kernel

theorem rowEval5010 (x : Key → ℝ) : Integer.Sparse.eval row5010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5010, Integer.Sparse.eval_collectBalanced, rawRowCheck5010]

def rawRow5011 : Integer.Sparse Key := [(key2175, -2), (key2179, -2), (key2175, -2), (key2189, 6), (key2078, 2), (key2082, 2), (key2078, 2), (key2333, -2), (key2289, -2), (key2333, -2), (key2087, -6), (key2330, 2), (key2281, 2), (key2330, 2)]

theorem rawRowCheck5011 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form13 = rawRow5011 := by decide +kernel

def row5011 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

theorem rowCheck5011 : row5011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5011 := by decide +kernel

theorem rowEval5011 (x : Key → ℝ) : Integer.Sparse.eval row5011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5011, Integer.Sparse.eval_collectBalanced, rawRowCheck5011]

def rawRow5012 : Integer.Sparse Key := [(key2179, -2), (key2175, -2), (key2175, -2), (key2189, 6), (key2082, 2), (key2078, 2), (key2078, 2), (key2333, -2), (key2333, -2), (key2289, -2), (key2087, -6), (key2330, 2), (key2330, 2), (key2281, 2)]

theorem rawRowCheck5012 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form13 = rawRow5012 := by decide +kernel

def row5012 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

theorem rowCheck5012 : row5012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5012 := by decide +kernel

theorem rowEval5012 (x : Key → ℝ) : Integer.Sparse.eval row5012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck5012, Integer.Sparse.eval_collectBalanced, rawRowCheck5012]

def rawRow5013 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2189, -2), (key2179, 6), (key2275, 2), (key2275, 2), (key2289, 2), (key2082, -2), (key2328, -2), (key2328, -2), (key2281, -6), (key2087, 2), (key2330, 2), (key2330, 2)]

theorem rawRowCheck5013 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form13 = rawRow5013 := by decide +kernel

def row5013 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

theorem rowCheck5013 : row5013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5013 := by decide +kernel

theorem rowEval5013 (x : Key → ℝ) : Integer.Sparse.eval row5013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5013, Integer.Sparse.eval_collectBalanced, rawRowCheck5013]

def rawRow5014 : Integer.Sparse Key := [(key2175, -2), (key2189, -2), (key2175, -2), (key2179, 6), (key2275, 2), (key2289, 2), (key2275, 2), (key2328, -2), (key2082, -2), (key2328, -2), (key2281, -6), (key2330, 2), (key2087, 2), (key2330, 2)]

theorem rawRowCheck5014 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form13 = rawRow5014 := by decide +kernel

def row5014 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

theorem rowCheck5014 : row5014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5014 := by decide +kernel

theorem rowEval5014 (x : Key → ℝ) : Integer.Sparse.eval row5014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5014, Integer.Sparse.eval_collectBalanced, rawRowCheck5014]

def rawRow5015 : Integer.Sparse Key := [(key2189, -2), (key2175, -2), (key2175, -2), (key2179, 6), (key2289, 2), (key2275, 2), (key2275, 2), (key2328, -2), (key2328, -2), (key2082, -2), (key2281, -6), (key2330, 2), (key2330, 2), (key2087, 2)]

theorem rawRowCheck5015 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form13 = rawRow5015 := by decide +kernel

def row5015 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

theorem rowCheck5015 : row5015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5015 := by decide +kernel

theorem rowEval5015 (x : Key → ℝ) : Integer.Sparse.eval row5015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck5015, Integer.Sparse.eval_collectBalanced, rawRowCheck5015]

def rawRow5016 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2281, -2), (key2289, 6), (key2078, 2), (key2078, 2), (key2087, 2), (key2189, -2), (key2333, -2), (key2333, -2), (key2082, -6), (key2179, 2), (key2328, 2), (key2328, 2)]

theorem rawRowCheck5016 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form13 = rawRow5016 := by decide +kernel

def row5016 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

theorem rowCheck5016 : row5016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5016 := by decide +kernel

theorem rowEval5016 (x : Key → ℝ) : Integer.Sparse.eval row5016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5016, Integer.Sparse.eval_collectBalanced, rawRowCheck5016]

def rawRow5017 : Integer.Sparse Key := [(key2275, -2), (key2281, -2), (key2275, -2), (key2289, 6), (key2078, 2), (key2087, 2), (key2078, 2), (key2333, -2), (key2189, -2), (key2333, -2), (key2082, -6), (key2328, 2), (key2179, 2), (key2328, 2)]

theorem rawRowCheck5017 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form13 = rawRow5017 := by decide +kernel

def row5017 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

theorem rowCheck5017 : row5017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5017 := by decide +kernel

theorem rowEval5017 (x : Key → ℝ) : Integer.Sparse.eval row5017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5017, Integer.Sparse.eval_collectBalanced, rawRowCheck5017]

def rawRow5018 : Integer.Sparse Key := [(key2281, -2), (key2275, -2), (key2275, -2), (key2289, 6), (key2087, 2), (key2078, 2), (key2078, 2), (key2333, -2), (key2333, -2), (key2189, -2), (key2082, -6), (key2328, 2), (key2328, 2), (key2179, 2)]

theorem rawRowCheck5018 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form13 = rawRow5018 := by decide +kernel

def row5018 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

theorem rowCheck5018 : row5018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5018 := by decide +kernel

theorem rowEval5018 (x : Key → ℝ) : Integer.Sparse.eval row5018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5018, Integer.Sparse.eval_collectBalanced, rawRowCheck5018]

def rawRow5019 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2289, -2), (key2281, 6), (key2175, 2), (key2175, 2), (key2189, 2), (key2087, -2), (key2330, -2), (key2330, -2), (key2179, -6), (key2082, 2), (key2328, 2), (key2328, 2)]

theorem rawRowCheck5019 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form13 = rawRow5019 := by decide +kernel

def row5019 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

theorem rowCheck5019 : row5019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5019 := by decide +kernel

theorem rowEval5019 (x : Key → ℝ) : Integer.Sparse.eval row5019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5019, Integer.Sparse.eval_collectBalanced, rawRowCheck5019]

def rawRow5020 : Integer.Sparse Key := [(key2275, -2), (key2289, -2), (key2275, -2), (key2281, 6), (key2175, 2), (key2189, 2), (key2175, 2), (key2330, -2), (key2087, -2), (key2330, -2), (key2179, -6), (key2328, 2), (key2082, 2), (key2328, 2)]

theorem rawRowCheck5020 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form13 = rawRow5020 := by decide +kernel

def row5020 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

theorem rowCheck5020 : row5020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5020 := by decide +kernel

theorem rowEval5020 (x : Key → ℝ) : Integer.Sparse.eval row5020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck5020, Integer.Sparse.eval_collectBalanced, rawRowCheck5020]

def rawRow5021 : Integer.Sparse Key := [(key2289, -2), (key2275, -2), (key2275, -2), (key2281, 6), (key2189, 2), (key2175, 2), (key2175, 2), (key2330, -2), (key2330, -2), (key2087, -2), (key2179, -6), (key2328, 2), (key2328, 2), (key2082, 2)]

theorem rawRowCheck5021 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form13 = rawRow5021 := by decide +kernel

def row5021 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

theorem rowCheck5021 : row5021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5021 := by decide +kernel

theorem rowEval5021 (x : Key → ℝ) : Integer.Sparse.eval row5021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck5021, Integer.Sparse.eval_collectBalanced, rawRowCheck5021]

def rawRow5022 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2382, -2), (key2393, 2), (key2393, 2), (key2395, 2), (key2771, 2), (key2774, 2), (key2774, 2), (key2891, -1), (key2891, -1), (key2912, -1), (key2912, -1), (key2914, -1), (key2914, -1), (key2933, -2), (key2933, -2), (key2934, -2), (key2970, 1), (key2970, 1), (key2991, 1), (key2991, 1), (key2993, 1), (key2993, 1)]

theorem rawRowCheck5022 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form14 = rawRow5022 := by decide +kernel

def row5022 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

theorem rowCheck5022 : row5022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5022 := by decide +kernel

theorem rowEval5022 (x : Key → ℝ) : Integer.Sparse.eval row5022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5022, Integer.Sparse.eval_collectBalanced, rawRowCheck5022]

def rawRow5023 : Integer.Sparse Key := [(key2382, -2), (key2379, -2), (key2382, -2), (key2393, 2), (key2395, 2), (key2393, 2), (key2774, 2), (key2771, 2), (key2774, 2), (key2912, -1), (key2914, -1), (key2891, -1), (key2914, -1), (key2891, -1), (key2912, -1), (key2933, -2), (key2934, -2), (key2933, -2), (key2991, 1), (key2993, 1), (key2970, 1), (key2993, 1), (key2970, 1), (key2991, 1)]

theorem rawRowCheck5023 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form14 = rawRow5023 := by decide +kernel

def row5023 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

theorem rowCheck5023 : row5023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5023 := by decide +kernel

theorem rowEval5023 (x : Key → ℝ) : Integer.Sparse.eval row5023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5023, Integer.Sparse.eval_collectBalanced, rawRowCheck5023]

def rawRow5024 : Integer.Sparse Key := [(key2382, -2), (key2382, -2), (key2379, -2), (key2395, 2), (key2393, 2), (key2393, 2), (key2774, 2), (key2774, 2), (key2771, 2), (key2914, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2912, -1), (key2891, -1), (key2934, -2), (key2933, -2), (key2933, -2), (key2993, 1), (key2991, 1), (key2993, 1), (key2970, 1), (key2991, 1), (key2970, 1)]

theorem rawRowCheck5024 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form14 = rawRow5024 := by decide +kernel

def row5024 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

theorem rowCheck5024 : row5024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5024 := by decide +kernel

theorem rowEval5024 (x : Key → ℝ) : Integer.Sparse.eval row5024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck5024, Integer.Sparse.eval_collectBalanced, rawRowCheck5024]

def rawRow5025 : Integer.Sparse Key := [(key2379, -2), (key2393, -2), (key2393, -2), (key2382, 2), (key2382, 2), (key2395, 2), (key2848, 2), (key2891, 2), (key2891, 2), (key2774, -1), (key2774, -1), (key2882, -1), (key2882, -1), (key2914, -1), (key2914, -1), (key2970, -2), (key2970, -2), (key2996, -2), (key2933, 1), (key2933, 1), (key2991, 1), (key2991, 1), (key3003, 1), (key3003, 1)]

theorem rawRowCheck5025 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form14 = rawRow5025 := by decide +kernel

def row5025 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

theorem rowCheck5025 : row5025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5025 := by decide +kernel

theorem rowEval5025 (x : Key → ℝ) : Integer.Sparse.eval row5025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5025, Integer.Sparse.eval_collectBalanced, rawRowCheck5025]

def rawRow5026 : Integer.Sparse Key := [(key2393, -2), (key2379, -2), (key2393, -2), (key2382, 2), (key2395, 2), (key2382, 2), (key2891, 2), (key2848, 2), (key2891, 2), (key2882, -1), (key2914, -1), (key2774, -1), (key2914, -1), (key2774, -1), (key2882, -1), (key2970, -2), (key2996, -2), (key2970, -2), (key2991, 1), (key3003, 1), (key2933, 1), (key3003, 1), (key2933, 1), (key2991, 1)]

theorem rawRowCheck5026 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form14 = rawRow5026 := by decide +kernel

def row5026 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

theorem rowCheck5026 : row5026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5026 := by decide +kernel

theorem rowEval5026 (x : Key → ℝ) : Integer.Sparse.eval row5026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5026, Integer.Sparse.eval_collectBalanced, rawRowCheck5026]

def rawRow5027 : Integer.Sparse Key := [(key2393, -2), (key2393, -2), (key2379, -2), (key2395, 2), (key2382, 2), (key2382, 2), (key2891, 2), (key2891, 2), (key2848, 2), (key2914, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2882, -1), (key2774, -1), (key2996, -2), (key2970, -2), (key2970, -2), (key3003, 1), (key2991, 1), (key3003, 1), (key2933, 1), (key2991, 1), (key2933, 1)]

theorem rawRowCheck5027 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form14 = rawRow5027 := by decide +kernel

def row5027 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

theorem rowCheck5027 : row5027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5027 := by decide +kernel

theorem rowEval5027 (x : Key → ℝ) : Integer.Sparse.eval row5027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5027, Integer.Sparse.eval_collectBalanced, rawRowCheck5027]

def rawRow5028 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2410, -2), (key2441, 2), (key2441, 2), (key2445, 2), (key2592, 2), (key2595, 2), (key2595, 2), (key2970, -1), (key2970, -1), (key2991, -1), (key2991, -1), (key2993, -1), (key2993, -1), (key2602, -2), (key2602, -2), (key2603, -2), (key2891, 1), (key2891, 1), (key2912, 1), (key2912, 1), (key2914, 1), (key2914, 1)]

theorem rawRowCheck5028 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form14 = rawRow5028 := by decide +kernel

def row5028 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck5028 : row5028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5028 := by decide +kernel

theorem rowEval5028 (x : Key → ℝ) : Integer.Sparse.eval row5028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5028, Integer.Sparse.eval_collectBalanced, rawRowCheck5028]

def rawRow5029 : Integer.Sparse Key := [(key2410, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, 2), (key2441, 2), (key2595, 2), (key2592, 2), (key2595, 2), (key2991, -1), (key2993, -1), (key2970, -1), (key2993, -1), (key2970, -1), (key2991, -1), (key2602, -2), (key2603, -2), (key2602, -2), (key2912, 1), (key2914, 1), (key2891, 1), (key2914, 1), (key2891, 1), (key2912, 1)]

theorem rawRowCheck5029 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form14 = rawRow5029 := by decide +kernel

def row5029 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck5029 : row5029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5029 := by decide +kernel

theorem rowEval5029 (x : Key → ℝ) : Integer.Sparse.eval row5029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5029, Integer.Sparse.eval_collectBalanced, rawRowCheck5029]

def rawRow5030 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2407, -2), (key2445, 2), (key2441, 2), (key2441, 2), (key2595, 2), (key2595, 2), (key2592, 2), (key2993, -1), (key2991, -1), (key2993, -1), (key2970, -1), (key2991, -1), (key2970, -1), (key2603, -2), (key2602, -2), (key2602, -2), (key2914, 1), (key2912, 1), (key2914, 1), (key2891, 1), (key2912, 1), (key2891, 1)]

theorem rawRowCheck5030 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form14 = rawRow5030 := by decide +kernel

def row5030 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck5030 : row5030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5030 := by decide +kernel

theorem rowEval5030 (x : Key → ℝ) : Integer.Sparse.eval row5030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck5030, Integer.Sparse.eval_collectBalanced, rawRowCheck5030]

def rawRow5031 : Integer.Sparse Key := [(key2407, -2), (key2441, -2), (key2441, -2), (key2410, 2), (key2410, 2), (key2445, 2), (key2848, 2), (key2970, 2), (key2970, 2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, 1), (key2602, 1), (key2912, 1), (key2912, 1), (key3003, 1), (key3003, 1)]

theorem rawRowCheck5031 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form14 = rawRow5031 := by decide +kernel

def row5031 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

theorem rowCheck5031 : row5031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5031 := by decide +kernel

theorem rowEval5031 (x : Key → ℝ) : Integer.Sparse.eval row5031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5031, Integer.Sparse.eval_collectBalanced, rawRowCheck5031]

def rawRow5032 : Integer.Sparse Key := [(key2441, -2), (key2407, -2), (key2441, -2), (key2410, 2), (key2445, 2), (key2410, 2), (key2970, 2), (key2848, 2), (key2970, 2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, 1), (key3003, 1), (key2602, 1), (key3003, 1), (key2602, 1), (key2912, 1)]

theorem rawRowCheck5032 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form14 = rawRow5032 := by decide +kernel

def row5032 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

theorem rowCheck5032 : row5032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5032 := by decide +kernel

theorem rowEval5032 (x : Key → ℝ) : Integer.Sparse.eval row5032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5032, Integer.Sparse.eval_collectBalanced, rawRowCheck5032]

def rawRow5033 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2407, -2), (key2445, 2), (key2410, 2), (key2410, 2), (key2970, 2), (key2970, 2), (key2848, 2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, 1), (key2912, 1), (key3003, 1), (key2602, 1), (key2912, 1), (key2602, 1)]

theorem rawRowCheck5033 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form14 = rawRow5033 := by decide +kernel

def row5033 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

theorem rowCheck5033 : row5033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5033 := by decide +kernel

theorem rowEval5033 (x : Key → ℝ) : Integer.Sparse.eval row5033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck5033, Integer.Sparse.eval_collectBalanced, rawRowCheck5033]

def rawRow5034 : Integer.Sparse Key := [(key2473, -2), (key2483, -2), (key2483, -2), (key2507, 2), (key2507, 2), (key2526, 2), (key2379, 2), (key2393, 2), (key2393, 2), (key2933, -1), (key2933, -1), (key2991, -1), (key2991, -1), (key3003, -1), (key3003, -1), (key2595, -2), (key2595, -2), (key2603, -2), (key2774, 1), (key2774, 1), (key2882, 1), (key2882, 1), (key2914, 1), (key2914, 1)]

theorem rawRowCheck5034 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form14 = rawRow5034 := by decide +kernel

def row5034 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

theorem rowCheck5034 : row5034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5034 := by decide +kernel

theorem rowEval5034 (x : Key → ℝ) : Integer.Sparse.eval row5034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5034, Integer.Sparse.eval_collectBalanced, rawRowCheck5034]

def rawRow5035 : Integer.Sparse Key := [(key2483, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2507, 2), (key2393, 2), (key2379, 2), (key2393, 2), (key2991, -1), (key3003, -1), (key2933, -1), (key3003, -1), (key2933, -1), (key2991, -1), (key2595, -2), (key2603, -2), (key2595, -2), (key2882, 1), (key2914, 1), (key2774, 1), (key2914, 1), (key2774, 1), (key2882, 1)]

theorem rawRowCheck5035 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form14 = rawRow5035 := by decide +kernel

def row5035 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

theorem rowCheck5035 : row5035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5035 := by decide +kernel

theorem rowEval5035 (x : Key → ℝ) : Integer.Sparse.eval row5035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5035, Integer.Sparse.eval_collectBalanced, rawRowCheck5035]

def rawRow5036 : Integer.Sparse Key := [(key2483, -2), (key2483, -2), (key2473, -2), (key2526, 2), (key2507, 2), (key2507, 2), (key2393, 2), (key2393, 2), (key2379, 2), (key3003, -1), (key2991, -1), (key3003, -1), (key2933, -1), (key2991, -1), (key2933, -1), (key2603, -2), (key2595, -2), (key2595, -2), (key2914, 1), (key2882, 1), (key2914, 1), (key2774, 1), (key2882, 1), (key2774, 1)]

theorem rawRowCheck5036 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form14 = rawRow5036 := by decide +kernel

def row5036 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

theorem rowCheck5036 : row5036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5036 := by decide +kernel

theorem rowEval5036 (x : Key → ℝ) : Integer.Sparse.eval row5036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5036, Integer.Sparse.eval_collectBalanced, rawRowCheck5036]

def rawRow5037 : Integer.Sparse Key := [(key2473, -2), (key2507, -2), (key2507, -2), (key2483, 2), (key2483, 2), (key2526, 2), (key2407, 2), (key2441, 2), (key2441, 2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, 1), (key2595, 1), (key2882, 1), (key2882, 1), (key2993, 1), (key2993, 1)]

theorem rawRowCheck5037 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form14 = rawRow5037 := by decide +kernel

def row5037 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

theorem rowCheck5037 : row5037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5037 := by decide +kernel

theorem rowEval5037 (x : Key → ℝ) : Integer.Sparse.eval row5037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5037, Integer.Sparse.eval_collectBalanced, rawRowCheck5037]

def rawRow5038 : Integer.Sparse Key := [(key2507, -2), (key2473, -2), (key2507, -2), (key2483, 2), (key2526, 2), (key2483, 2), (key2441, 2), (key2407, 2), (key2441, 2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, 1), (key2993, 1), (key2595, 1), (key2993, 1), (key2595, 1), (key2882, 1)]

theorem rawRowCheck5038 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form14 = rawRow5038 := by decide +kernel

def row5038 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

theorem rowCheck5038 : row5038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5038 := by decide +kernel

theorem rowEval5038 (x : Key → ℝ) : Integer.Sparse.eval row5038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck5038, Integer.Sparse.eval_collectBalanced, rawRowCheck5038]

def rawRow5039 : Integer.Sparse Key := [(key2507, -2), (key2507, -2), (key2473, -2), (key2526, 2), (key2483, 2), (key2483, 2), (key2441, 2), (key2441, 2), (key2407, 2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, 1), (key2882, 1), (key2993, 1), (key2595, 1), (key2882, 1), (key2595, 1)]

theorem rawRowCheck5039 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form14 = rawRow5039 := by decide +kernel

def row5039 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

theorem rowCheck5039 : row5039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5039 := by decide +kernel

theorem rowEval5039 (x : Key → ℝ) : Integer.Sparse.eval row5039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck5039, Integer.Sparse.eval_collectBalanced, rawRowCheck5039]

def rawRow5040 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2732, -1), (key2732, -1), (key2753, 2), (key2758, 2), (key2758, 2), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2835, 1), (key2835, 1), (key2920, -1), (key2920, -1), (key2923, -1), (key2923, -1), (key2927, -1), (key2927, -1), (key3012, -2), (key3017, -2), (key3017, -2), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1)]

theorem rawRowCheck5040 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form15 = rawRow5040 := by decide +kernel

def row5040 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck5040 : row5040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5040 := by decide +kernel

theorem rowEval5040 (x : Key → ℝ) : Integer.Sparse.eval row5040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5040, Integer.Sparse.eval_collectBalanced, rawRowCheck5040]

def rawRow5041 : Integer.Sparse Key := [(key2726, -1), (key2732, -1), (key2706, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2758, 2), (key2753, 2), (key2758, 2), (key2829, 1), (key2835, 1), (key2809, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2923, -1), (key2927, -1), (key2920, -1), (key2927, -1), (key2920, -1), (key2923, -1), (key3017, -2), (key3012, -2), (key3017, -2), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1)]

theorem rawRowCheck5041 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form15 = rawRow5041 := by decide +kernel

def row5041 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck5041 : row5041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5041 := by decide +kernel

theorem rowEval5041 (x : Key → ℝ) : Integer.Sparse.eval row5041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5041, Integer.Sparse.eval_collectBalanced, rawRowCheck5041]

def rawRow5042 : Integer.Sparse Key := [(key2732, -1), (key2726, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2758, 2), (key2758, 2), (key2753, 2), (key2835, 1), (key2829, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2809, 1), (key2927, -1), (key2923, -1), (key2927, -1), (key2920, -1), (key2923, -1), (key2920, -1), (key3017, -2), (key3017, -2), (key3012, -2), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1)]

theorem rawRowCheck5042 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form15 = rawRow5042 := by decide +kernel

def row5042 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

theorem rowCheck5042 : row5042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5042 := by decide +kernel

theorem rowEval5042 (x : Key → ℝ) : Integer.Sparse.eval row5042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck5042, Integer.Sparse.eval_collectBalanced, rawRowCheck5042]

def rawRow5043 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2758, -1), (key2758, -1), (key2676, 2), (key2732, 2), (key2732, 2), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2923, 1), (key2923, 1), (key2798, -1), (key2798, -1), (key2835, -1), (key2835, -1), (key2885, -1), (key2885, -1), (key3008, -2), (key3026, -2), (key3026, -2), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1)]

theorem rawRowCheck5043 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form15 = rawRow5043 := by decide +kernel

def row5043 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

theorem rowCheck5043 : row5043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5043 := by decide +kernel

theorem rowEval5043 (x : Key → ℝ) : Integer.Sparse.eval row5043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5043, Integer.Sparse.eval_collectBalanced, rawRowCheck5043]

def rawRow5044 : Integer.Sparse Key := [(key2726, -1), (key2758, -1), (key2671, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2732, 2), (key2676, 2), (key2732, 2), (key2870, 1), (key2923, 1), (key2786, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2835, -1), (key2885, -1), (key2798, -1), (key2885, -1), (key2798, -1), (key2835, -1), (key3026, -2), (key3008, -2), (key3026, -2), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1)]

theorem rawRowCheck5044 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form15 = rawRow5044 := by decide +kernel

def row5044 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

theorem rowCheck5044 : row5044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5044 := by decide +kernel

theorem rowEval5044 (x : Key → ℝ) : Integer.Sparse.eval row5044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5044, Integer.Sparse.eval_collectBalanced, rawRowCheck5044]

def rawRow5045 : Integer.Sparse Key := [(key2758, -1), (key2726, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2732, 2), (key2732, 2), (key2676, 2), (key2923, 1), (key2870, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2786, 1), (key2885, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2835, -1), (key2798, -1), (key3026, -2), (key3026, -2), (key3008, -2), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1)]

theorem rawRowCheck5045 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form15 = rawRow5045 := by decide +kernel

def row5045 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

theorem rowCheck5045 : row5045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5045 := by decide +kernel

theorem rowEval5045 (x : Key → ℝ) : Integer.Sparse.eval row5045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5045, Integer.Sparse.eval_collectBalanced, rawRowCheck5045]

def rawRow5046 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2835, -1), (key2835, -1), (key3012, 2), (key3017, 2), (key3017, 2), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key3023, -1), (key3023, -1), (key3026, -1), (key3026, -1), (key3030, -1), (key3030, -1), (key2753, -2), (key2758, -2), (key2758, -2), (key2920, 1), (key2920, 1), (key2923, 1), (key2923, 1), (key2927, 1), (key2927, 1)]

theorem rawRowCheck5046 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form15 = rawRow5046 := by decide +kernel

def row5046 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

theorem rowCheck5046 : row5046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5046 := by decide +kernel

theorem rowEval5046 (x : Key → ℝ) : Integer.Sparse.eval row5046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5046, Integer.Sparse.eval_collectBalanced, rawRowCheck5046]

def rawRow5047 : Integer.Sparse Key := [(key2829, -1), (key2835, -1), (key2809, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key3017, 2), (key3012, 2), (key3017, 2), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key3026, -1), (key3030, -1), (key3023, -1), (key3030, -1), (key3023, -1), (key3026, -1), (key2758, -2), (key2753, -2), (key2758, -2), (key2923, 1), (key2927, 1), (key2920, 1), (key2927, 1), (key2920, 1), (key2923, 1)]

theorem rawRowCheck5047 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form15 = rawRow5047 := by decide +kernel

def row5047 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

theorem rowCheck5047 : row5047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5047 := by decide +kernel

theorem rowEval5047 (x : Key → ℝ) : Integer.Sparse.eval row5047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5047, Integer.Sparse.eval_collectBalanced, rawRowCheck5047]

def rawRow5048 : Integer.Sparse Key := [(key2835, -1), (key2829, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key3017, 2), (key3017, 2), (key3012, 2), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key3030, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3026, -1), (key3023, -1), (key2758, -2), (key2758, -2), (key2753, -2), (key2927, 1), (key2923, 1), (key2927, 1), (key2920, 1), (key2923, 1), (key2920, 1)]

theorem rawRowCheck5048 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form15 = rawRow5048 := by decide +kernel

def row5048 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

theorem rowCheck5048 : row5048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5048 := by decide +kernel

theorem rowEval5048 (x : Key → ℝ) : Integer.Sparse.eval row5048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck5048, Integer.Sparse.eval_collectBalanced, rawRowCheck5048]

def rawRow5049 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1), (key2658, -2), (key2923, -2), (key2923, -2), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1)]

theorem rawRowCheck5049 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form15 = rawRow5049 := by decide +kernel

def row5049 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key3017, -2), (key3026, 2)]

theorem rowCheck5049 : row5049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5049 := by decide +kernel

theorem rowEval5049 (x : Key → ℝ) : Integer.Sparse.eval row5049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5049, Integer.Sparse.eval_collectBalanced, rawRowCheck5049]

def rawRow5050 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2923, -2), (key2658, -2), (key2923, -2), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1)]

theorem rawRowCheck5050 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form15 = rawRow5050 := by decide +kernel

def row5050 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -1), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key2948, -1), (key2960, -2), (key3026, 2)]

theorem rowCheck5050 : row5050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5050 := by decide +kernel

theorem rowEval5050 (x : Key → ℝ) : Integer.Sparse.eval row5050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5050, Integer.Sparse.eval_collectBalanced, rawRowCheck5050]

def rawRow5051 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1), (key2923, -2), (key2923, -2), (key2658, -2), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1)]

theorem rawRowCheck5051 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form15 = rawRow5051 := by decide +kernel

def row5051 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -1), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key2948, -1), (key2960, -2), (key3026, 2)]

theorem rowCheck5051 : row5051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5051 := by decide +kernel

theorem rowEval5051 (x : Key → ℝ) : Integer.Sparse.eval row5051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck5051, Integer.Sparse.eval_collectBalanced, rawRowCheck5051]

def rawRow5052 : Integer.Sparse Key := [(key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2976, -1), (key2976, -1), (key2728, 2), (key2983, 2), (key2983, 2), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key3010, -1), (key3010, -1), (key3017, -1), (key3017, -1), (key3030, -1), (key3030, -1), (key2676, -2), (key2732, -2), (key2732, -2), (key2798, 1), (key2798, 1), (key2835, 1), (key2835, 1), (key2885, 1), (key2885, 1)]

theorem rawRowCheck5052 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form15 = rawRow5052 := by decide +kernel

def row5052 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

theorem rowCheck5052 : row5052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5052 := by decide +kernel

theorem rowEval5052 (x : Key → ℝ) : Integer.Sparse.eval row5052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5052, Integer.Sparse.eval_collectBalanced, rawRowCheck5052]

def rawRow5053 : Integer.Sparse Key := [(key2972, -1), (key2976, -1), (key2702, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2983, 2), (key2728, 2), (key2983, 2), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key3017, -1), (key3030, -1), (key3010, -1), (key3030, -1), (key3010, -1), (key3017, -1), (key2732, -2), (key2676, -2), (key2732, -2), (key2835, 1), (key2885, 1), (key2798, 1), (key2885, 1), (key2798, 1), (key2835, 1)]

theorem rawRowCheck5053 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form15 = rawRow5053 := by decide +kernel

def row5053 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

theorem rowCheck5053 : row5053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5053 := by decide +kernel

theorem rowEval5053 (x : Key → ℝ) : Integer.Sparse.eval row5053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5053, Integer.Sparse.eval_collectBalanced, rawRowCheck5053]

def rawRow5054 : Integer.Sparse Key := [(key2976, -1), (key2972, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2702, -1), (key2983, 2), (key2983, 2), (key2728, 2), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key3030, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3017, -1), (key3010, -1), (key2732, -2), (key2732, -2), (key2676, -2), (key2885, 1), (key2835, 1), (key2885, 1), (key2798, 1), (key2835, 1), (key2798, 1)]

theorem rawRowCheck5054 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form15 = rawRow5054 := by decide +kernel

def row5054 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

theorem rowCheck5054 : row5054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5054 := by decide +kernel

theorem rowEval5054 (x : Key → ℝ) : Integer.Sparse.eval row5054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5054, Integer.Sparse.eval_collectBalanced, rawRowCheck5054]

def rawRow5055 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, 2), (key2976, 2), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1), (key2621, -2), (key2835, -2), (key2835, -2), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1)]

theorem rawRowCheck5055 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form15 = rawRow5055 := by decide +kernel

def row5055 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 2), (key2835, -4), (key2885, 2), (key2927, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3017, 2)]

theorem rowCheck5055 : row5055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5055 := by decide +kernel

theorem rowEval5055 (x : Key → ℝ) : Integer.Sparse.eval row5055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5055, Integer.Sparse.eval_collectBalanced, rawRowCheck5055]

def rawRow5056 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2976, 2), (key2641, 2), (key2976, 2), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2835, -2), (key2621, -2), (key2835, -2), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1)]

theorem rawRowCheck5056 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form15 = rawRow5056 := by decide +kernel

def row5056 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 1), (key2835, -4), (key2885, 2), (key2927, -2), (key2948, 1), (key2960, 2), (key2972, -2), (key2976, 4), (key2983, -2)]

theorem rowCheck5056 : row5056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5056 := by decide +kernel

theorem rowEval5056 (x : Key → ℝ) : Integer.Sparse.eval row5056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck5056, Integer.Sparse.eval_collectBalanced, rawRowCheck5056]

def rawRow5057 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2976, 2), (key2976, 2), (key2641, 2), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1), (key2835, -2), (key2835, -2), (key2621, -2), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1)]

theorem rawRowCheck5057 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form15 = rawRow5057 := by decide +kernel

def row5057 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 1), (key2835, -4), (key2885, 2), (key2927, -2), (key2948, 1), (key2960, 2), (key2972, -2), (key2976, 4), (key2983, -2)]

theorem rowCheck5057 : row5057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5057 := by decide +kernel

theorem rowEval5057 (x : Key → ℝ) : Integer.Sparse.eval row5057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck5057, Integer.Sparse.eval_collectBalanced, rawRowCheck5057]

def rawRow5058 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2649, 2), (key2654, 2), (key2654, 2), (key2671, 2), (key2671, 2), (key2674, 2), (key2738, -2), (key2748, -2), (key2748, -2), (key2939, -2), (key2944, -2), (key2944, -2), (key2951, 2), (key2961, 2), (key2961, 2)]

theorem rawRowCheck5058 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form16 = rawRow5058 := by decide +kernel

def row5058 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

theorem rowCheck5058 : row5058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5058 := by decide +kernel

theorem rowEval5058 (x : Key → ℝ) : Integer.Sparse.eval row5058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5058, Integer.Sparse.eval_collectBalanced, rawRowCheck5058]

def rawRow5059 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2654, 2), (key2649, 2), (key2654, 2), (key2671, 2), (key2674, 2), (key2671, 2), (key2748, -2), (key2738, -2), (key2748, -2), (key2944, -2), (key2939, -2), (key2944, -2), (key2961, 2), (key2951, 2), (key2961, 2)]

theorem rawRowCheck5059 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form16 = rawRow5059 := by decide +kernel

def row5059 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

theorem rowCheck5059 : row5059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5059 := by decide +kernel

theorem rowEval5059 (x : Key → ℝ) : Integer.Sparse.eval row5059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5059, Integer.Sparse.eval_collectBalanced, rawRowCheck5059]

def rawRow5060 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2654, 2), (key2654, 2), (key2649, 2), (key2674, 2), (key2671, 2), (key2671, 2), (key2748, -2), (key2748, -2), (key2738, -2), (key2944, -2), (key2944, -2), (key2939, -2), (key2961, 2), (key2961, 2), (key2951, 2)]

theorem rawRowCheck5060 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form16 = rawRow5060 := by decide +kernel

def row5060 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

theorem rowCheck5060 : row5060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5060 := by decide +kernel

theorem rowEval5060 (x : Key → ℝ) : Integer.Sparse.eval row5060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck5060, Integer.Sparse.eval_collectBalanced, rawRowCheck5060]

def rawRow5061 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2619, 2), (key2642, 2), (key2642, 2), (key2706, 2), (key2706, 2), (key2738, 2), (key2674, -2), (key2729, -2), (key2729, -2), (key2951, -2), (key2977, -2), (key2977, -2), (key2939, 2), (key2984, 2), (key2984, 2)]

theorem rawRowCheck5061 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form16 = rawRow5061 := by decide +kernel

def row5061 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

theorem rowCheck5061 : row5061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5061 := by decide +kernel

theorem rowEval5061 (x : Key → ℝ) : Integer.Sparse.eval row5061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5061, Integer.Sparse.eval_collectBalanced, rawRowCheck5061]

def rawRow5062 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2642, 2), (key2619, 2), (key2642, 2), (key2706, 2), (key2738, 2), (key2706, 2), (key2729, -2), (key2674, -2), (key2729, -2), (key2977, -2), (key2951, -2), (key2977, -2), (key2984, 2), (key2939, 2), (key2984, 2)]

theorem rawRowCheck5062 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form16 = rawRow5062 := by decide +kernel

def row5062 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

theorem rowCheck5062 : row5062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5062 := by decide +kernel

theorem rowEval5062 (x : Key → ℝ) : Integer.Sparse.eval row5062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5062, Integer.Sparse.eval_collectBalanced, rawRowCheck5062]

def rawRow5063 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2642, 2), (key2642, 2), (key2619, 2), (key2738, 2), (key2706, 2), (key2706, 2), (key2729, -2), (key2729, -2), (key2674, -2), (key2977, -2), (key2977, -2), (key2951, -2), (key2984, 2), (key2984, 2), (key2939, 2)]

theorem rawRowCheck5063 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form16 = rawRow5063 := by decide +kernel

def row5063 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

theorem rowCheck5063 : row5063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5063 := by decide +kernel

theorem rowEval5063 (x : Key → ℝ) : Integer.Sparse.eval row5063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5063, Integer.Sparse.eval_collectBalanced, rawRowCheck5063]

def rawRow5064 : Integer.Sparse Key := [(key2671, -2), (key2671, -2), (key2674, -2), (key2939, 2), (key2944, 2), (key2944, 2), (key2616, 2), (key2616, 2), (key2619, 2), (key2951, -2), (key2961, -2), (key2961, -2), (key2649, -2), (key2654, -2), (key2654, -2), (key2738, 2), (key2748, 2), (key2748, 2)]

theorem rawRowCheck5064 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form16 = rawRow5064 := by decide +kernel

def row5064 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

theorem rowCheck5064 : row5064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5064 := by decide +kernel

theorem rowEval5064 (x : Key → ℝ) : Integer.Sparse.eval row5064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5064, Integer.Sparse.eval_collectBalanced, rawRowCheck5064]

def rawRow5065 : Integer.Sparse Key := [(key2671, -2), (key2674, -2), (key2671, -2), (key2944, 2), (key2939, 2), (key2944, 2), (key2616, 2), (key2619, 2), (key2616, 2), (key2961, -2), (key2951, -2), (key2961, -2), (key2654, -2), (key2649, -2), (key2654, -2), (key2748, 2), (key2738, 2), (key2748, 2)]

theorem rawRowCheck5065 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form16 = rawRow5065 := by decide +kernel

def row5065 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

theorem rowCheck5065 : row5065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5065 := by decide +kernel

theorem rowEval5065 (x : Key → ℝ) : Integer.Sparse.eval row5065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5065, Integer.Sparse.eval_collectBalanced, rawRowCheck5065]

def rawRow5066 : Integer.Sparse Key := [(key2674, -2), (key2671, -2), (key2671, -2), (key2944, 2), (key2944, 2), (key2939, 2), (key2619, 2), (key2616, 2), (key2616, 2), (key2961, -2), (key2961, -2), (key2951, -2), (key2654, -2), (key2654, -2), (key2649, -2), (key2748, 2), (key2748, 2), (key2738, 2)]

theorem rawRowCheck5066 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form16 = rawRow5066 := by decide +kernel

def row5066 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

theorem rowCheck5066 : row5066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5066 := by decide +kernel

theorem rowEval5066 (x : Key → ℝ) : Integer.Sparse.eval row5066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck5066, Integer.Sparse.eval_collectBalanced, rawRowCheck5066]

def rawRow5067 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2674, 2), (key2796, 2), (key2796, 2), (key2809, 2), (key2809, 2), (key2951, 2), (key2619, -2), (key2832, -2), (key2832, -2), (key2738, -2), (key2898, -2), (key2898, -2), (key2649, 2), (key2905, 2), (key2905, 2)]

theorem rawRowCheck5067 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form16 = rawRow5067 := by decide +kernel

def row5067 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

theorem rowCheck5067 : row5067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5067 := by decide +kernel

theorem rowEval5067 (x : Key → ℝ) : Integer.Sparse.eval row5067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5067, Integer.Sparse.eval_collectBalanced, rawRowCheck5067]

def rawRow5068 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2796, 2), (key2674, 2), (key2796, 2), (key2809, 2), (key2951, 2), (key2809, 2), (key2832, -2), (key2619, -2), (key2832, -2), (key2898, -2), (key2738, -2), (key2898, -2), (key2905, 2), (key2649, 2), (key2905, 2)]

theorem rawRowCheck5068 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form16 = rawRow5068 := by decide +kernel

def row5068 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

theorem rowCheck5068 : row5068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5068 := by decide +kernel

theorem rowEval5068 (x : Key → ℝ) : Integer.Sparse.eval row5068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5068, Integer.Sparse.eval_collectBalanced, rawRowCheck5068]

def rawRow5069 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2796, 2), (key2796, 2), (key2674, 2), (key2951, 2), (key2809, 2), (key2809, 2), (key2832, -2), (key2832, -2), (key2619, -2), (key2898, -2), (key2898, -2), (key2738, -2), (key2905, 2), (key2905, 2), (key2649, 2)]

theorem rawRowCheck5069 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form16 = rawRow5069 := by decide +kernel

def row5069 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

theorem rowCheck5069 : row5069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5069 := by decide +kernel

theorem rowEval5069 (x : Key → ℝ) : Integer.Sparse.eval row5069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck5069, Integer.Sparse.eval_collectBalanced, rawRowCheck5069]

def rawRow5070 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2951, 2), (key2977, 2), (key2977, 2), (key2632, 2), (key2632, 2), (key2649, 2), (key2939, -2), (key2984, -2), (key2984, -2), (key2619, -2), (key2642, -2), (key2642, -2), (key2674, 2), (key2729, 2), (key2729, 2)]

theorem rawRowCheck5070 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form16 = rawRow5070 := by decide +kernel

def row5070 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

theorem rowCheck5070 : row5070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5070 := by decide +kernel

theorem rowEval5070 (x : Key → ℝ) : Integer.Sparse.eval row5070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5070, Integer.Sparse.eval_collectBalanced, rawRowCheck5070]

def rawRow5071 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2977, 2), (key2951, 2), (key2977, 2), (key2632, 2), (key2649, 2), (key2632, 2), (key2984, -2), (key2939, -2), (key2984, -2), (key2642, -2), (key2619, -2), (key2642, -2), (key2729, 2), (key2674, 2), (key2729, 2)]

theorem rawRowCheck5071 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form16 = rawRow5071 := by decide +kernel

def row5071 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

theorem rowCheck5071 : row5071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5071 := by decide +kernel

theorem rowEval5071 (x : Key → ℝ) : Integer.Sparse.eval row5071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5071, Integer.Sparse.eval_collectBalanced, rawRowCheck5071]

def rawRow5072 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2977, 2), (key2977, 2), (key2951, 2), (key2649, 2), (key2632, 2), (key2632, 2), (key2984, -2), (key2984, -2), (key2939, -2), (key2642, -2), (key2642, -2), (key2619, -2), (key2729, 2), (key2729, 2), (key2674, 2)]

theorem rawRowCheck5072 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form16 = rawRow5072 := by decide +kernel

def row5072 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

theorem rowCheck5072 : row5072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5072 := by decide +kernel

theorem rowEval5072 (x : Key → ℝ) : Integer.Sparse.eval row5072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5072, Integer.Sparse.eval_collectBalanced, rawRowCheck5072]

def rawRow5073 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2738, 2), (key2898, 2), (key2898, 2), (key2786, 2), (key2786, 2), (key2939, 2), (key2649, -2), (key2905, -2), (key2905, -2), (key2674, -2), (key2796, -2), (key2796, -2), (key2619, 2), (key2832, 2), (key2832, 2)]

theorem rawRowCheck5073 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form16 = rawRow5073 := by decide +kernel

def row5073 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

theorem rowCheck5073 : row5073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5073 := by decide +kernel

theorem rowEval5073 (x : Key → ℝ) : Integer.Sparse.eval row5073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5073, Integer.Sparse.eval_collectBalanced, rawRowCheck5073]

def rawRow5074 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2898, 2), (key2738, 2), (key2898, 2), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, -2), (key2649, -2), (key2905, -2), (key2796, -2), (key2674, -2), (key2796, -2), (key2832, 2), (key2619, 2), (key2832, 2)]

theorem rawRowCheck5074 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form16 = rawRow5074 := by decide +kernel

def row5074 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

theorem rowCheck5074 : row5074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5074 := by decide +kernel

theorem rowEval5074 (x : Key → ℝ) : Integer.Sparse.eval row5074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck5074, Integer.Sparse.eval_collectBalanced, rawRowCheck5074]

def rawRow5075 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2898, 2), (key2898, 2), (key2738, 2), (key2939, 2), (key2786, 2), (key2786, 2), (key2905, -2), (key2905, -2), (key2649, -2), (key2796, -2), (key2796, -2), (key2674, -2), (key2832, 2), (key2832, 2), (key2619, 2)]

theorem rawRowCheck5075 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form16 = rawRow5075 := by decide +kernel

def row5075 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

theorem rowCheck5075 : row5075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5075 := by decide +kernel

theorem rowEval5075 (x : Key → ℝ) : Integer.Sparse.eval row5075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck5075, Integer.Sparse.eval_collectBalanced, rawRowCheck5075]

def rawRow5076 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1774, -1), (key1774, -1), (key1559, 2), (key1780, 2), (key1780, 2), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1790, 1), (key1790, 1), (key1659, -1), (key1659, -1), (key1817, -1), (key1817, -1), (key1841, -1), (key1841, -1), (key1596, -2), (key1798, -2), (key1798, -2), (key1667, 1), (key1667, 1), (key1825, 1), (key1825, 1), (key1844, 1), (key1844, 1)]

theorem rawRowCheck5076 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form17 = rawRow5076 := by decide +kernel

def row5076 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

theorem rowCheck5076 : row5076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5076 := by decide +kernel

theorem rowEval5076 (x : Key → ℝ) : Integer.Sparse.eval row5076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5076, Integer.Sparse.eval_collectBalanced, rawRowCheck5076]

def rawRow5077 : Integer.Sparse Key := [(key1772, -1), (key1774, -1), (key1546, -1), (key1774, -1), (key1546, -1), (key1772, -1), (key1780, 2), (key1559, 2), (key1780, 2), (key1788, 1), (key1790, 1), (key1573, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1817, -1), (key1841, -1), (key1659, -1), (key1841, -1), (key1659, -1), (key1817, -1), (key1798, -2), (key1596, -2), (key1798, -2), (key1825, 1), (key1844, 1), (key1667, 1), (key1844, 1), (key1667, 1), (key1825, 1)]

theorem rawRowCheck5077 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form17 = rawRow5077 := by decide +kernel

def row5077 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

theorem rowCheck5077 : row5077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5077 := by decide +kernel

theorem rowEval5077 (x : Key → ℝ) : Integer.Sparse.eval row5077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5077, Integer.Sparse.eval_collectBalanced, rawRowCheck5077]

def rawRow5078 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1774, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1780, 2), (key1780, 2), (key1559, 2), (key1790, 1), (key1788, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1573, 1), (key1841, -1), (key1817, -1), (key1841, -1), (key1659, -1), (key1817, -1), (key1659, -1), (key1798, -2), (key1798, -2), (key1596, -2), (key1844, 1), (key1825, 1), (key1844, 1), (key1667, 1), (key1825, 1), (key1667, 1)]

theorem rawRowCheck5078 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form17 = rawRow5078 := by decide +kernel

def row5078 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

theorem rowCheck5078 : row5078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5078 := by decide +kernel

theorem rowEval5078 (x : Key → ℝ) : Integer.Sparse.eval row5078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck5078, Integer.Sparse.eval_collectBalanced, rawRowCheck5078]

def rawRow5079 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1780, -1), (key1780, -1), (key1397, 2), (key1774, 2), (key1774, 2), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1817, 1), (key1817, 1), (key1457, -1), (key1457, -1), (key1790, -1), (key1790, -1), (key1839, -1), (key1839, -1), (key1447, -2), (key1825, -2), (key1825, -2), (key1466, 1), (key1466, 1), (key1798, 1), (key1798, 1), (key1844, 1), (key1844, 1)]

theorem rawRowCheck5079 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form17 = rawRow5079 := by decide +kernel

def row5079 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

theorem rowCheck5079 : row5079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5079 := by decide +kernel

theorem rowEval5079 (x : Key → ℝ) : Integer.Sparse.eval row5079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5079, Integer.Sparse.eval_collectBalanced, rawRowCheck5079]

def rawRow5080 : Integer.Sparse Key := [(key1772, -1), (key1780, -1), (key1391, -1), (key1780, -1), (key1391, -1), (key1772, -1), (key1774, 2), (key1397, 2), (key1774, 2), (key1813, 1), (key1817, 1), (key1424, 1), (key1817, 1), (key1424, 1), (key1813, 1), (key1790, -1), (key1839, -1), (key1457, -1), (key1839, -1), (key1457, -1), (key1790, -1), (key1825, -2), (key1447, -2), (key1825, -2), (key1798, 1), (key1844, 1), (key1466, 1), (key1844, 1), (key1466, 1), (key1798, 1)]

theorem rawRowCheck5080 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form17 = rawRow5080 := by decide +kernel

def row5080 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

theorem rowCheck5080 : row5080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5080 := by decide +kernel

theorem rowEval5080 (x : Key → ℝ) : Integer.Sparse.eval row5080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5080, Integer.Sparse.eval_collectBalanced, rawRowCheck5080]

def rawRow5081 : Integer.Sparse Key := [(key1780, -1), (key1772, -1), (key1780, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1774, 2), (key1774, 2), (key1397, 2), (key1817, 1), (key1813, 1), (key1817, 1), (key1424, 1), (key1813, 1), (key1424, 1), (key1839, -1), (key1790, -1), (key1839, -1), (key1457, -1), (key1790, -1), (key1457, -1), (key1825, -2), (key1825, -2), (key1447, -2), (key1844, 1), (key1798, 1), (key1844, 1), (key1466, 1), (key1798, 1), (key1466, 1)]

theorem rawRowCheck5081 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form17 = rawRow5081 := by decide +kernel

def row5081 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

theorem rowCheck5081 : row5081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5081 := by decide +kernel

theorem rowEval5081 (x : Key → ℝ) : Integer.Sparse.eval row5081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5081, Integer.Sparse.eval_collectBalanced, rawRowCheck5081]

def rawRow5082 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1790, -1), (key1790, -1), (key1596, 2), (key1798, 2), (key1798, 2), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1774, 1), (key1774, 1), (key1667, -1), (key1667, -1), (key1825, -1), (key1825, -1), (key1844, -1), (key1844, -1), (key1559, -2), (key1780, -2), (key1780, -2), (key1659, 1), (key1659, 1), (key1817, 1), (key1817, 1), (key1841, 1), (key1841, 1)]

theorem rawRowCheck5082 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form17 = rawRow5082 := by decide +kernel

def row5082 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

theorem rowCheck5082 : row5082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5082 := by decide +kernel

theorem rowEval5082 (x : Key → ℝ) : Integer.Sparse.eval row5082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5082, Integer.Sparse.eval_collectBalanced, rawRowCheck5082]

def rawRow5083 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1573, -1), (key1790, -1), (key1573, -1), (key1788, -1), (key1798, 2), (key1596, 2), (key1798, 2), (key1772, 1), (key1774, 1), (key1546, 1), (key1774, 1), (key1546, 1), (key1772, 1), (key1825, -1), (key1844, -1), (key1667, -1), (key1844, -1), (key1667, -1), (key1825, -1), (key1780, -2), (key1559, -2), (key1780, -2), (key1817, 1), (key1841, 1), (key1659, 1), (key1841, 1), (key1659, 1), (key1817, 1)]

theorem rawRowCheck5083 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form17 = rawRow5083 := by decide +kernel

def row5083 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

theorem rowCheck5083 : row5083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5083 := by decide +kernel

theorem rowEval5083 (x : Key → ℝ) : Integer.Sparse.eval row5083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5083, Integer.Sparse.eval_collectBalanced, rawRowCheck5083]

def rawRow5084 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1790, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1798, 2), (key1798, 2), (key1596, 2), (key1774, 1), (key1772, 1), (key1774, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1844, -1), (key1825, -1), (key1844, -1), (key1667, -1), (key1825, -1), (key1667, -1), (key1780, -2), (key1780, -2), (key1559, -2), (key1841, 1), (key1817, 1), (key1841, 1), (key1659, 1), (key1817, 1), (key1659, 1)]

theorem rawRowCheck5084 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form17 = rawRow5084 := by decide +kernel

def row5084 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

theorem rowCheck5084 : row5084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5084 := by decide +kernel

theorem rowEval5084 (x : Key → ℝ) : Integer.Sparse.eval row5084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck5084, Integer.Sparse.eval_collectBalanced, rawRowCheck5084]

def rawRow5085 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1798, -1), (key1798, -1), (key1302, 2), (key1790, 2), (key1790, 2), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1825, 1), (key1825, 1), (key1339, -1), (key1339, -1), (key1774, -1), (key1774, -1), (key1839, -1), (key1839, -1), (key1329, -2), (key1817, -2), (key1817, -2), (key1345, 1), (key1345, 1), (key1780, 1), (key1780, 1), (key1841, 1), (key1841, 1)]

theorem rawRowCheck5085 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form17 = rawRow5085 := by decide +kernel

def row5085 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck5085 : row5085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5085 := by decide +kernel

theorem rowEval5085 (x : Key → ℝ) : Integer.Sparse.eval row5085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5085, Integer.Sparse.eval_collectBalanced, rawRowCheck5085]

def rawRow5086 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1296, -1), (key1798, -1), (key1296, -1), (key1788, -1), (key1790, 2), (key1302, 2), (key1790, 2), (key1813, 1), (key1825, 1), (key1316, 1), (key1825, 1), (key1316, 1), (key1813, 1), (key1774, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1774, -1), (key1817, -2), (key1329, -2), (key1817, -2), (key1780, 1), (key1841, 1), (key1345, 1), (key1841, 1), (key1345, 1), (key1780, 1)]

theorem rawRowCheck5086 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form17 = rawRow5086 := by decide +kernel

def row5086 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck5086 : row5086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5086 := by decide +kernel

theorem rowEval5086 (x : Key → ℝ) : Integer.Sparse.eval row5086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5086, Integer.Sparse.eval_collectBalanced, rawRowCheck5086]

def rawRow5087 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1798, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1790, 2), (key1790, 2), (key1302, 2), (key1825, 1), (key1813, 1), (key1825, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1839, -1), (key1774, -1), (key1839, -1), (key1339, -1), (key1774, -1), (key1339, -1), (key1817, -2), (key1817, -2), (key1329, -2), (key1841, 1), (key1780, 1), (key1841, 1), (key1345, 1), (key1780, 1), (key1345, 1)]

theorem rawRowCheck5087 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form17 = rawRow5087 := by decide +kernel

def row5087 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

theorem rowCheck5087 : row5087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5087 := by decide +kernel

theorem rowEval5087 (x : Key → ℝ) : Integer.Sparse.eval row5087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck5087, Integer.Sparse.eval_collectBalanced, rawRowCheck5087]

def rawRow5088 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1817, -1), (key1817, -1), (key1447, 2), (key1825, 2), (key1825, 2), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1780, 1), (key1780, 1), (key1466, -1), (key1466, -1), (key1798, -1), (key1798, -1), (key1844, -1), (key1844, -1), (key1397, -2), (key1774, -2), (key1774, -2), (key1457, 1), (key1457, 1), (key1790, 1), (key1790, 1), (key1839, 1), (key1839, 1)]

theorem rawRowCheck5088 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form17 = rawRow5088 := by decide +kernel

def row5088 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

theorem rowCheck5088 : row5088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5088 := by decide +kernel

theorem rowEval5088 (x : Key → ℝ) : Integer.Sparse.eval row5088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5088, Integer.Sparse.eval_collectBalanced, rawRowCheck5088]

def rawRow5089 : Integer.Sparse Key := [(key1813, -1), (key1817, -1), (key1424, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1825, 2), (key1447, 2), (key1825, 2), (key1772, 1), (key1780, 1), (key1391, 1), (key1780, 1), (key1391, 1), (key1772, 1), (key1798, -1), (key1844, -1), (key1466, -1), (key1844, -1), (key1466, -1), (key1798, -1), (key1774, -2), (key1397, -2), (key1774, -2), (key1790, 1), (key1839, 1), (key1457, 1), (key1839, 1), (key1457, 1), (key1790, 1)]

theorem rawRowCheck5089 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form17 = rawRow5089 := by decide +kernel

def row5089 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

theorem rowCheck5089 : row5089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5089 := by decide +kernel

theorem rowEval5089 (x : Key → ℝ) : Integer.Sparse.eval row5089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5089, Integer.Sparse.eval_collectBalanced, rawRowCheck5089]

def rawRow5090 : Integer.Sparse Key := [(key1817, -1), (key1813, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1825, 2), (key1825, 2), (key1447, 2), (key1780, 1), (key1772, 1), (key1780, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1844, -1), (key1798, -1), (key1844, -1), (key1466, -1), (key1798, -1), (key1466, -1), (key1774, -2), (key1774, -2), (key1397, -2), (key1839, 1), (key1790, 1), (key1839, 1), (key1457, 1), (key1790, 1), (key1457, 1)]

theorem rawRowCheck5090 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form17 = rawRow5090 := by decide +kernel

def row5090 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

theorem rowCheck5090 : row5090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5090 := by decide +kernel

theorem rowEval5090 (x : Key → ℝ) : Integer.Sparse.eval row5090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5090, Integer.Sparse.eval_collectBalanced, rawRowCheck5090]

def rawRow5091 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1825, -1), (key1825, -1), (key1329, 2), (key1817, 2), (key1817, 2), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1798, 1), (key1798, 1), (key1345, -1), (key1345, -1), (key1780, -1), (key1780, -1), (key1841, -1), (key1841, -1), (key1302, -2), (key1790, -2), (key1790, -2), (key1339, 1), (key1339, 1), (key1774, 1), (key1774, 1), (key1839, 1), (key1839, 1)]

theorem rawRowCheck5091 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form17 = rawRow5091 := by decide +kernel

def row5091 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

theorem rowCheck5091 : row5091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5091 := by decide +kernel

theorem rowEval5091 (x : Key → ℝ) : Integer.Sparse.eval row5091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5091, Integer.Sparse.eval_collectBalanced, rawRowCheck5091]

def rawRow5092 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1316, -1), (key1825, -1), (key1316, -1), (key1813, -1), (key1817, 2), (key1329, 2), (key1817, 2), (key1788, 1), (key1798, 1), (key1296, 1), (key1798, 1), (key1296, 1), (key1788, 1), (key1780, -1), (key1841, -1), (key1345, -1), (key1841, -1), (key1345, -1), (key1780, -1), (key1790, -2), (key1302, -2), (key1790, -2), (key1774, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1774, 1)]

theorem rawRowCheck5092 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form17 = rawRow5092 := by decide +kernel

def row5092 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

theorem rowCheck5092 : row5092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5092 := by decide +kernel

theorem rowEval5092 (x : Key → ℝ) : Integer.Sparse.eval row5092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck5092, Integer.Sparse.eval_collectBalanced, rawRowCheck5092]

def rawRow5093 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1825, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1817, 2), (key1817, 2), (key1329, 2), (key1798, 1), (key1788, 1), (key1798, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1841, -1), (key1780, -1), (key1841, -1), (key1345, -1), (key1780, -1), (key1345, -1), (key1790, -2), (key1790, -2), (key1302, -2), (key1839, 1), (key1774, 1), (key1839, 1), (key1339, 1), (key1774, 1), (key1339, 1)]

theorem rawRowCheck5093 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form17 = rawRow5093 := by decide +kernel

def row5093 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

theorem rowCheck5093 : row5093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5093 := by decide +kernel

theorem rowEval5093 (x : Key → ℝ) : Integer.Sparse.eval row5093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck5093, Integer.Sparse.eval_collectBalanced, rawRowCheck5093]

def rawRow5094 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2729, -1), (key2729, -1), (key2738, 2), (key2748, 2), (key2748, 2), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2832, 1), (key2832, 1), (key2898, -1), (key2898, -1), (key2905, -1), (key2905, -1), (key2913, -1), (key2913, -1), (key2951, -2), (key2961, -2), (key2961, -2), (key2977, 1), (key2977, 1), (key2984, 1), (key2984, 1), (key2992, 1), (key2992, 1)]

theorem rawRowCheck5094 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form18 = rawRow5094 := by decide +kernel

def row5094 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

theorem rowCheck5094 : row5094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5094 := by decide +kernel

theorem rowEval5094 (x : Key → ℝ) : Integer.Sparse.eval row5094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5094, Integer.Sparse.eval_collectBalanced, rawRowCheck5094]

def rawRow5095 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2706, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2748, 2), (key2738, 2), (key2748, 2), (key2829, 1), (key2832, 1), (key2809, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2905, -1), (key2913, -1), (key2898, -1), (key2913, -1), (key2898, -1), (key2905, -1), (key2961, -2), (key2951, -2), (key2961, -2), (key2984, 1), (key2992, 1), (key2977, 1), (key2992, 1), (key2977, 1), (key2984, 1)]

theorem rawRowCheck5095 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form18 = rawRow5095 := by decide +kernel

def row5095 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

theorem rowCheck5095 : row5095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5095 := by decide +kernel

theorem rowEval5095 (x : Key → ℝ) : Integer.Sparse.eval row5095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5095, Integer.Sparse.eval_collectBalanced, rawRowCheck5095]

def rawRow5096 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2748, 2), (key2748, 2), (key2738, 2), (key2832, 1), (key2829, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2809, 1), (key2913, -1), (key2905, -1), (key2913, -1), (key2898, -1), (key2905, -1), (key2898, -1), (key2961, -2), (key2961, -2), (key2951, -2), (key2992, 1), (key2984, 1), (key2992, 1), (key2977, 1), (key2984, 1), (key2977, 1)]

theorem rawRowCheck5096 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form18 = rawRow5096 := by decide +kernel

def row5096 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

theorem rowCheck5096 : row5096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5096 := by decide +kernel

theorem rowEval5096 (x : Key → ℝ) : Integer.Sparse.eval row5096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck5096, Integer.Sparse.eval_collectBalanced, rawRowCheck5096]

def rawRow5097 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2748, -1), (key2748, -1), (key2674, 2), (key2729, 2), (key2729, 2), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2905, 1), (key2905, 1), (key2796, -1), (key2796, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2939, -2), (key2984, -2), (key2984, -2), (key2944, 1), (key2944, 1), (key2961, 1), (key2961, 1), (key2992, 1), (key2992, 1)]

theorem rawRowCheck5097 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form18 = rawRow5097 := by decide +kernel

def row5097 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

theorem rowCheck5097 : row5097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5097 := by decide +kernel

theorem rowEval5097 (x : Key → ℝ) : Integer.Sparse.eval row5097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5097, Integer.Sparse.eval_collectBalanced, rawRowCheck5097]

def rawRow5098 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2671, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2729, 2), (key2674, 2), (key2729, 2), (key2870, 1), (key2905, 1), (key2786, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2832, -1), (key2883, -1), (key2796, -1), (key2883, -1), (key2796, -1), (key2832, -1), (key2984, -2), (key2939, -2), (key2984, -2), (key2961, 1), (key2992, 1), (key2944, 1), (key2992, 1), (key2944, 1), (key2961, 1)]

theorem rawRowCheck5098 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form18 = rawRow5098 := by decide +kernel

def row5098 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

theorem rowCheck5098 : row5098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5098 := by decide +kernel

theorem rowEval5098 (x : Key → ℝ) : Integer.Sparse.eval row5098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5098, Integer.Sparse.eval_collectBalanced, rawRowCheck5098]

def rawRow5099 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2729, 2), (key2729, 2), (key2674, 2), (key2905, 1), (key2870, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2786, 1), (key2883, -1), (key2832, -1), (key2883, -1), (key2796, -1), (key2832, -1), (key2796, -1), (key2984, -2), (key2984, -2), (key2939, -2), (key2992, 1), (key2961, 1), (key2992, 1), (key2944, 1), (key2961, 1), (key2944, 1)]

theorem rawRowCheck5099 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form18 = rawRow5099 := by decide +kernel

def row5099 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

theorem rowCheck5099 : row5099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5099 := by decide +kernel

theorem rowEval5099 (x : Key → ℝ) : Integer.Sparse.eval row5099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5099, Integer.Sparse.eval_collectBalanced, rawRowCheck5099]

def rawRow5100 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2832, -1), (key2832, -1), (key2951, 2), (key2961, 2), (key2961, 2), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2729, 1), (key2729, 1), (key2977, -1), (key2977, -1), (key2984, -1), (key2984, -1), (key2992, -1), (key2992, -1), (key2738, -2), (key2748, -2), (key2748, -2), (key2898, 1), (key2898, 1), (key2905, 1), (key2905, 1), (key2913, 1), (key2913, 1)]

theorem rawRowCheck5100 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form18 = rawRow5100 := by decide +kernel

def row5100 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

theorem rowCheck5100 : row5100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5100 := by decide +kernel

theorem rowEval5100 (x : Key → ℝ) : Integer.Sparse.eval row5100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5100, Integer.Sparse.eval_collectBalanced, rawRowCheck5100]

def rawRow5101 : Integer.Sparse Key := [(key2829, -1), (key2832, -1), (key2809, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2961, 2), (key2951, 2), (key2961, 2), (key2726, 1), (key2729, 1), (key2706, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2984, -1), (key2992, -1), (key2977, -1), (key2992, -1), (key2977, -1), (key2984, -1), (key2748, -2), (key2738, -2), (key2748, -2), (key2905, 1), (key2913, 1), (key2898, 1), (key2913, 1), (key2898, 1), (key2905, 1)]

theorem rawRowCheck5101 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form18 = rawRow5101 := by decide +kernel

def row5101 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

theorem rowCheck5101 : row5101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5101 := by decide +kernel

theorem rowEval5101 (x : Key → ℝ) : Integer.Sparse.eval row5101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5101, Integer.Sparse.eval_collectBalanced, rawRowCheck5101]

def rawRow5102 : Integer.Sparse Key := [(key2832, -1), (key2829, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2961, 2), (key2961, 2), (key2951, 2), (key2729, 1), (key2726, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2992, -1), (key2984, -1), (key2992, -1), (key2977, -1), (key2984, -1), (key2977, -1), (key2748, -2), (key2748, -2), (key2738, -2), (key2913, 1), (key2905, 1), (key2913, 1), (key2898, 1), (key2905, 1), (key2898, 1)]

theorem rawRowCheck5102 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form18 = rawRow5102 := by decide +kernel

def row5102 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

theorem rowCheck5102 : row5102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5102 := by decide +kernel

theorem rowEval5102 (x : Key → ℝ) : Integer.Sparse.eval row5102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck5102, Integer.Sparse.eval_collectBalanced, rawRowCheck5102]

def rawRow5103 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1), (key2649, -2), (key2905, -2), (key2905, -2), (key2654, 1), (key2654, 1), (key2748, 1), (key2748, 1), (key2913, 1), (key2913, 1)]

theorem rawRowCheck5103 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form18 = rawRow5103 := by decide +kernel

def row5103 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

theorem rowCheck5103 : row5103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5103 := by decide +kernel

theorem rowEval5103 (x : Key → ℝ) : Integer.Sparse.eval row5103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5103, Integer.Sparse.eval_collectBalanced, rawRowCheck5103]

def rawRow5104 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2905, -2), (key2649, -2), (key2905, -2), (key2748, 1), (key2913, 1), (key2654, 1), (key2913, 1), (key2654, 1), (key2748, 1)]

theorem rawRowCheck5104 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form18 = rawRow5104 := by decide +kernel

def row5104 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

theorem rowCheck5104 : row5104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5104 := by decide +kernel

theorem rowEval5104 (x : Key → ℝ) : Integer.Sparse.eval row5104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5104, Integer.Sparse.eval_collectBalanced, rawRowCheck5104]

def rawRow5105 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1), (key2905, -2), (key2905, -2), (key2649, -2), (key2913, 1), (key2748, 1), (key2913, 1), (key2654, 1), (key2748, 1), (key2654, 1)]

theorem rawRowCheck5105 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form18 = rawRow5105 := by decide +kernel

def row5105 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

theorem rowCheck5105 : row5105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5105 := by decide +kernel

theorem rowEval5105 (x : Key → ℝ) : Integer.Sparse.eval row5105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck5105, Integer.Sparse.eval_collectBalanced, rawRowCheck5105]

def rawRow5106 : Integer.Sparse Key := [(key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2905, -1), (key2905, -1), (key2939, 2), (key2984, 2), (key2984, 2), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2748, 1), (key2748, 1), (key2944, -1), (key2944, -1), (key2961, -1), (key2961, -1), (key2992, -1), (key2992, -1), (key2674, -2), (key2729, -2), (key2729, -2), (key2796, 1), (key2796, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

theorem rawRowCheck5106 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form18 = rawRow5106 := by decide +kernel

def row5106 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

theorem rowCheck5106 : row5106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5106 := by decide +kernel

theorem rowEval5106 (x : Key → ℝ) : Integer.Sparse.eval row5106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5106, Integer.Sparse.eval_collectBalanced, rawRowCheck5106]

def rawRow5107 : Integer.Sparse Key := [(key2870, -1), (key2905, -1), (key2786, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2984, 2), (key2939, 2), (key2984, 2), (key2726, 1), (key2748, 1), (key2671, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2961, -1), (key2992, -1), (key2944, -1), (key2992, -1), (key2944, -1), (key2961, -1), (key2729, -2), (key2674, -2), (key2729, -2), (key2832, 1), (key2883, 1), (key2796, 1), (key2883, 1), (key2796, 1), (key2832, 1)]

theorem rawRowCheck5107 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form18 = rawRow5107 := by decide +kernel

def row5107 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

theorem rowCheck5107 : row5107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5107 := by decide +kernel

theorem rowEval5107 (x : Key → ℝ) : Integer.Sparse.eval row5107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5107, Integer.Sparse.eval_collectBalanced, rawRowCheck5107]

def rawRow5108 : Integer.Sparse Key := [(key2905, -1), (key2870, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2786, -1), (key2984, 2), (key2984, 2), (key2939, 2), (key2748, 1), (key2726, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2992, -1), (key2961, -1), (key2992, -1), (key2944, -1), (key2961, -1), (key2944, -1), (key2729, -2), (key2729, -2), (key2674, -2), (key2883, 1), (key2832, 1), (key2883, 1), (key2796, 1), (key2832, 1), (key2796, 1)]

theorem rawRowCheck5108 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form18 = rawRow5108 := by decide +kernel

def row5108 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

theorem rowCheck5108 : row5108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5108 := by decide +kernel

theorem rowEval5108 (x : Key → ℝ) : Integer.Sparse.eval row5108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5108, Integer.Sparse.eval_collectBalanced, rawRowCheck5108]

def rawRow5109 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1), (key2619, -2), (key2832, -2), (key2832, -2), (key2642, 1), (key2642, 1), (key2729, 1), (key2729, 1), (key2883, 1), (key2883, 1)]

theorem rawRowCheck5109 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form18 = rawRow5109 := by decide +kernel

def row5109 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

theorem rowCheck5109 : row5109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5109 := by decide +kernel

theorem rowEval5109 (x : Key → ℝ) : Integer.Sparse.eval row5109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5109, Integer.Sparse.eval_collectBalanced, rawRowCheck5109]

def rawRow5110 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2832, -2), (key2619, -2), (key2832, -2), (key2729, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2729, 1)]

theorem rawRowCheck5110 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form18 = rawRow5110 := by decide +kernel

def row5110 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

theorem rowCheck5110 : row5110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5110 := by decide +kernel

theorem rowEval5110 (x : Key → ℝ) : Integer.Sparse.eval row5110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck5110, Integer.Sparse.eval_collectBalanced, rawRowCheck5110]

def rawRow5111 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1), (key2832, -2), (key2832, -2), (key2619, -2), (key2883, 1), (key2729, 1), (key2883, 1), (key2642, 1), (key2729, 1), (key2642, 1)]

theorem rawRowCheck5111 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form18 = rawRow5111 := by decide +kernel

def row5111 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

theorem rowCheck5111 : row5111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5111 := by decide +kernel

theorem rowEval5111 (x : Key → ℝ) : Integer.Sparse.eval row5111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck5111, Integer.Sparse.eval_collectBalanced, rawRowCheck5111]

def rawRow5112 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1370, -2), (key1379, 6), (key1492, 2), (key1492, 2), (key1496, 2), (key1728, -2), (key1870, -2), (key1870, -2), (key1519, -6), (key1747, 2), (key1880, 2), (key1880, 2)]

theorem rawRowCheck5112 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form19 = rawRow5112 := by decide +kernel

def row5112 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

theorem rowCheck5112 : row5112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5112 := by decide +kernel

theorem rowEval5112 (x : Key → ℝ) : Integer.Sparse.eval row5112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5112, Integer.Sparse.eval_collectBalanced, rawRowCheck5112]

def rawRow5113 : Integer.Sparse Key := [(key1366, -2), (key1370, -2), (key1366, -2), (key1379, 6), (key1492, 2), (key1496, 2), (key1492, 2), (key1870, -2), (key1728, -2), (key1870, -2), (key1519, -6), (key1880, 2), (key1747, 2), (key1880, 2)]

theorem rawRowCheck5113 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form19 = rawRow5113 := by decide +kernel

def row5113 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

theorem rowCheck5113 : row5113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5113 := by decide +kernel

theorem rowEval5113 (x : Key → ℝ) : Integer.Sparse.eval row5113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5113, Integer.Sparse.eval_collectBalanced, rawRowCheck5113]

def rawRow5114 : Integer.Sparse Key := [(key1370, -2), (key1366, -2), (key1366, -2), (key1379, 6), (key1496, 2), (key1492, 2), (key1492, 2), (key1870, -2), (key1870, -2), (key1728, -2), (key1519, -6), (key1880, 2), (key1880, 2), (key1747, 2)]

theorem rawRowCheck5114 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form19 = rawRow5114 := by decide +kernel

def row5114 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

theorem rowCheck5114 : row5114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5114 := by decide +kernel

theorem rowEval5114 (x : Key → ℝ) : Integer.Sparse.eval row5114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck5114, Integer.Sparse.eval_collectBalanced, rawRowCheck5114]

def rawRow5115 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1379, -2), (key1370, 6), (key1718, 2), (key1718, 2), (key1728, 2), (key1496, -2), (key1865, -2), (key1865, -2), (key1747, -6), (key1519, 2), (key1880, 2), (key1880, 2)]

theorem rawRowCheck5115 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form19 = rawRow5115 := by decide +kernel

def row5115 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

theorem rowCheck5115 : row5115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5115 := by decide +kernel

theorem rowEval5115 (x : Key → ℝ) : Integer.Sparse.eval row5115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5115, Integer.Sparse.eval_collectBalanced, rawRowCheck5115]

def rawRow5116 : Integer.Sparse Key := [(key1366, -2), (key1379, -2), (key1366, -2), (key1370, 6), (key1718, 2), (key1728, 2), (key1718, 2), (key1865, -2), (key1496, -2), (key1865, -2), (key1747, -6), (key1880, 2), (key1519, 2), (key1880, 2)]

theorem rawRowCheck5116 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form19 = rawRow5116 := by decide +kernel

def row5116 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

theorem rowCheck5116 : row5116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5116 := by decide +kernel

theorem rowEval5116 (x : Key → ℝ) : Integer.Sparse.eval row5116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5116, Integer.Sparse.eval_collectBalanced, rawRowCheck5116]

def rawRow5117 : Integer.Sparse Key := [(key1379, -2), (key1366, -2), (key1366, -2), (key1370, 6), (key1728, 2), (key1718, 2), (key1718, 2), (key1865, -2), (key1865, -2), (key1496, -2), (key1747, -6), (key1880, 2), (key1880, 2), (key1519, 2)]

theorem rawRowCheck5117 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form19 = rawRow5117 := by decide +kernel

def row5117 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

theorem rowCheck5117 : row5117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5117 := by decide +kernel

theorem rowEval5117 (x : Key → ℝ) : Integer.Sparse.eval row5117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5117, Integer.Sparse.eval_collectBalanced, rawRowCheck5117]

def rawRow5118 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1496, -2), (key1519, 6), (key1366, 2), (key1366, 2), (key1370, 2), (key1747, -2), (key1880, -2), (key1880, -2), (key1379, -6), (key1728, 2), (key1870, 2), (key1870, 2)]

theorem rawRowCheck5118 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form19 = rawRow5118 := by decide +kernel

def row5118 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

theorem rowCheck5118 : row5118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5118 := by decide +kernel

theorem rowEval5118 (x : Key → ℝ) : Integer.Sparse.eval row5118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5118, Integer.Sparse.eval_collectBalanced, rawRowCheck5118]

def rawRow5119 : Integer.Sparse Key := [(key1492, -2), (key1496, -2), (key1492, -2), (key1519, 6), (key1366, 2), (key1370, 2), (key1366, 2), (key1880, -2), (key1747, -2), (key1880, -2), (key1379, -6), (key1870, 2), (key1728, 2), (key1870, 2)]

theorem rawRowCheck5119 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form19 = rawRow5119 := by decide +kernel

def row5119 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

theorem rowCheck5119 : row5119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5119 := by decide +kernel

theorem rowEval5119 (x : Key → ℝ) : Integer.Sparse.eval row5119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck5119, Integer.Sparse.eval_collectBalanced, rawRowCheck5119]

end MUB6.Certificate.GramRows

end OAI
