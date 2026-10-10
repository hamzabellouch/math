import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17024 : Integer.Sparse Key := [(key801, 4), (key811, 4), (key803, 4), (key871, -2), (key876, -2), (key801, -2), (key934, -2), (key803, -2), (key931, -2), (key801, -2), (key811, -2), (key776, -2), (key839, -2), (key778, -2), (key811, -2), (key801, 4), (key934, 4), (key811, 4)]

theorem rawRowCheck17024 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form17 = rawRow17024 := by decide +kernel

def row17024 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17024 : row17024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17024 := by decide +kernel

theorem rowEval17024 (x : Key → ℝ) : Integer.Sparse.eval row17024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17024, Integer.Sparse.eval_collectBalanced, rawRowCheck17024]

def rawRow17025 : Integer.Sparse Key := [(key811, 4), (key801, 4), (key803, 4), (key876, -2), (key871, -2), (key934, -2), (key801, -2), (key931, -2), (key803, -2), (key811, -2), (key801, -2), (key839, -2), (key776, -2), (key811, -2), (key778, -2), (key934, 4), (key801, 4), (key811, 4)]

theorem rawRowCheck17025 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form17 = rawRow17025 := by decide +kernel

def row17025 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 4), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17025 : row17025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17025 := by decide +kernel

theorem rowEval17025 (x : Key → ℝ) : Integer.Sparse.eval row17025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 0, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17025, Integer.Sparse.eval_collectBalanced, rawRowCheck17025]

def rawRow17026 : Integer.Sparse Key := [(key803, 4), (key811, 4), (key801, 4), (key931, -2), (key934, -2), (key803, -2), (key876, -2), (key801, -2), (key871, -2), (key836, -2), (key839, -2), (key778, -2), (key811, -2), (key776, -2), (key801, -2), (key811, 4), (key934, 4), (key801, 4)]

theorem rawRowCheck17026 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form17 = rawRow17026 := by decide +kernel

def row17026 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17026 : row17026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17026 := by decide +kernel

theorem rowEval17026 (x : Key → ℝ) : Integer.Sparse.eval row17026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17026, Integer.Sparse.eval_collectBalanced, rawRowCheck17026]

def rawRow17027 : Integer.Sparse Key := [(key811, 4), (key803, 4), (key801, 4), (key934, -2), (key931, -2), (key876, -2), (key803, -2), (key871, -2), (key801, -2), (key839, -2), (key836, -2), (key811, -2), (key778, -2), (key801, -2), (key776, -2), (key934, 4), (key811, 4), (key801, 4)]

theorem rawRowCheck17027 : GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form17 = rawRow17027 := by decide +kernel

def row17027 : Integer.Sparse Key := [(key776, -2), (key778, -2), (key801, 4), (key803, 2), (key811, 6), (key836, -2), (key839, -2), (key871, -2), (key876, -2), (key931, -2), (key934, 2)]

theorem rowCheck17027 : row17027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17027 := by decide +kernel

theorem rowEval17027 (x : Key → ℝ) : Integer.Sparse.eval row17027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -1, 2, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17027, Integer.Sparse.eval_collectBalanced, rawRowCheck17027]

def rawRow17028 : Integer.Sparse Key := [(key871, 4), (key876, 4), (key876, 4), (key801, -2), (key811, -2), (key801, -2), (key934, -2), (key811, -2), (key934, -2), (key801, -2), (key811, -2), (key801, -2), (key934, -2), (key811, -2), (key934, -2), (key776, 4), (key839, 4), (key839, 4)]

theorem rawRowCheck17028 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form17 = rawRow17028 := by decide +kernel

def row17028 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

theorem rowCheck17028 : row17028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17028 := by decide +kernel

theorem rowEval17028 (x : Key → ℝ) : Integer.Sparse.eval row17028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17028, Integer.Sparse.eval_collectBalanced, rawRowCheck17028]

def rawRow17029 : Integer.Sparse Key := [(key876, 4), (key871, 4), (key876, 4), (key811, -2), (key801, -2), (key934, -2), (key801, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key934, -2), (key801, -2), (key934, -2), (key811, -2), (key839, 4), (key776, 4), (key839, 4)]

theorem rawRowCheck17029 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form17 = rawRow17029 := by decide +kernel

def row17029 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

theorem rowCheck17029 : row17029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17029 := by decide +kernel

theorem rowEval17029 (x : Key → ℝ) : Integer.Sparse.eval row17029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -1, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17029, Integer.Sparse.eval_collectBalanced, rawRowCheck17029]

def rawRow17030 : Integer.Sparse Key := [(key876, 4), (key876, 4), (key871, 4), (key934, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key801, -2), (key934, -2), (key934, -2), (key811, -2), (key811, -2), (key801, -2), (key801, -2), (key839, 4), (key839, 4), (key776, 4)]

theorem rawRowCheck17030 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form17 = rawRow17030 := by decide +kernel

def row17030 : Integer.Sparse Key := [(key776, 4), (key801, -8), (key811, -8), (key839, 8), (key871, 4), (key876, 8), (key934, -8)]

theorem rowCheck17030 : row17030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17030 := by decide +kernel

theorem rowEval17030 (x : Key → ℝ) : Integer.Sparse.eval row17030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17030, Integer.Sparse.eval_collectBalanced, rawRowCheck17030]

def rawRow17031 : Integer.Sparse Key := [(key1976, 4), (key2218, 4), (key2224, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, -2), (key2266, -2), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, -2), (key2266, -2), (key1997, 4), (key2262, 4), (key2266, 4)]

theorem rawRowCheck17031 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form0 = rawRow17031 := by decide +kernel

def row17031 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

theorem rowCheck17031 : row17031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17031 := by decide +kernel

theorem rowEval17031 (x : Key → ℝ) : Integer.Sparse.eval row17031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17031, Integer.Sparse.eval_collectBalanced, rawRowCheck17031]

def rawRow17032 : Integer.Sparse Key := [(key1976, 4), (key2224, 4), (key2218, 4), (key1983, -2), (key1981, -2), (key2224, -2), (key2218, -2), (key2266, -2), (key2262, -2), (key1983, -2), (key1981, -2), (key2224, -2), (key2218, -2), (key2266, -2), (key2262, -2), (key1997, 4), (key2266, 4), (key2262, 4)]

theorem rawRowCheck17032 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form0 = rawRow17032 := by decide +kernel

def row17032 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

theorem rowCheck17032 : row17032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17032 := by decide +kernel

theorem rowEval17032 (x : Key → ℝ) : Integer.Sparse.eval row17032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17032, Integer.Sparse.eval_collectBalanced, rawRowCheck17032]

def rawRow17033 : Integer.Sparse Key := [(key2218, 4), (key1976, 4), (key2224, 4), (key2218, -2), (key2262, -2), (key1981, -2), (key2266, -2), (key1983, -2), (key2224, -2), (key2218, -2), (key2262, -2), (key1981, -2), (key2266, -2), (key1983, -2), (key2224, -2), (key2262, 4), (key1997, 4), (key2266, 4)]

theorem rawRowCheck17033 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form0 = rawRow17033 := by decide +kernel

def row17033 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

theorem rowCheck17033 : row17033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17033 := by decide +kernel

theorem rowEval17033 (x : Key → ℝ) : Integer.Sparse.eval row17033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17033, Integer.Sparse.eval_collectBalanced, rawRowCheck17033]

def rawRow17034 : Integer.Sparse Key := [(key2218, 4), (key2224, 4), (key1976, 4), (key2262, -2), (key2218, -2), (key2266, -2), (key1981, -2), (key2224, -2), (key1983, -2), (key2262, -2), (key2218, -2), (key2266, -2), (key1981, -2), (key2224, -2), (key1983, -2), (key2262, 4), (key2266, 4), (key1997, 4)]

theorem rawRowCheck17034 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form0 = rawRow17034 := by decide +kernel

def row17034 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

theorem rowCheck17034 : row17034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17034 := by decide +kernel

theorem rowEval17034 (x : Key → ℝ) : Integer.Sparse.eval row17034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17034, Integer.Sparse.eval_collectBalanced, rawRowCheck17034]

def rawRow17035 : Integer.Sparse Key := [(key2224, 4), (key1976, 4), (key2218, 4), (key2224, -2), (key2266, -2), (key1983, -2), (key2262, -2), (key1981, -2), (key2218, -2), (key2224, -2), (key2266, -2), (key1983, -2), (key2262, -2), (key1981, -2), (key2218, -2), (key2266, 4), (key1997, 4), (key2262, 4)]

theorem rawRowCheck17035 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form0 = rawRow17035 := by decide +kernel

def row17035 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

theorem rowCheck17035 : row17035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17035 := by decide +kernel

theorem rowEval17035 (x : Key → ℝ) : Integer.Sparse.eval row17035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17035, Integer.Sparse.eval_collectBalanced, rawRowCheck17035]

def rawRow17036 : Integer.Sparse Key := [(key2224, 4), (key2218, 4), (key1976, 4), (key2266, -2), (key2224, -2), (key2262, -2), (key1983, -2), (key2218, -2), (key1981, -2), (key2266, -2), (key2224, -2), (key2262, -2), (key1983, -2), (key2218, -2), (key1981, -2), (key2266, 4), (key2262, 4), (key1997, 4)]

theorem rawRowCheck17036 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form0 = rawRow17036 := by decide +kernel

def row17036 : Integer.Sparse Key := [(key1976, 4), (key1981, -4), (key1983, -4), (key1997, 4)]

theorem rowCheck17036 : row17036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17036 := by decide +kernel

theorem rowEval17036 (x : Key → ℝ) : Integer.Sparse.eval row17036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17036, Integer.Sparse.eval_collectBalanced, rawRowCheck17036]

def rawRow17037 : Integer.Sparse Key := [(key1981, 4), (key1981, 4), (key2266, 4), (key1976, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key2224, -2), (key1981, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key2266, -2), (key1983, 4), (key1983, 4), (key2224, 4)]

theorem rawRowCheck17037 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form0 = rawRow17037 := by decide +kernel

def row17037 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17037 : row17037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17037 := by decide +kernel

theorem rowEval17037 (x : Key → ℝ) : Integer.Sparse.eval row17037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17037, Integer.Sparse.eval_collectBalanced, rawRowCheck17037]

def rawRow17038 : Integer.Sparse Key := [(key1981, 4), (key2266, 4), (key1981, 4), (key1983, -2), (key1976, -2), (key2224, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key1983, 4), (key2224, 4), (key1983, 4)]

theorem rawRowCheck17038 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form0 = rawRow17038 := by decide +kernel

def row17038 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17038 : row17038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17038 := by decide +kernel

theorem rowEval17038 (x : Key → ℝ) : Integer.Sparse.eval row17038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17038, Integer.Sparse.eval_collectBalanced, rawRowCheck17038]

def rawRow17039 : Integer.Sparse Key := [(key2266, 4), (key1981, 4), (key1981, 4), (key2224, -2), (key2224, -2), (key1983, -2), (key1983, -2), (key1976, -2), (key1976, -2), (key2266, -2), (key2266, -2), (key1997, -2), (key1997, -2), (key1981, -2), (key1981, -2), (key2224, 4), (key1983, 4), (key1983, 4)]

theorem rawRowCheck17039 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form0 = rawRow17039 := by decide +kernel

def row17039 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17039 : row17039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17039 := by decide +kernel

theorem rowEval17039 (x : Key → ℝ) : Integer.Sparse.eval row17039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17039, Integer.Sparse.eval_collectBalanced, rawRowCheck17039]

def rawRow17040 : Integer.Sparse Key := [(key1983, 4), (key1983, 4), (key2262, 4), (key1976, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key2218, -2), (key1983, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key2262, -2), (key1981, 4), (key1981, 4), (key2218, 4)]

theorem rawRowCheck17040 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17040 := by decide +kernel

def row17040 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17040 : row17040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17040 := by decide +kernel

theorem rowEval17040 (x : Key → ℝ) : Integer.Sparse.eval row17040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17040, Integer.Sparse.eval_collectBalanced, rawRowCheck17040]

def rawRow17041 : Integer.Sparse Key := [(key1983, 4), (key2262, 4), (key1983, 4), (key1981, -2), (key1976, -2), (key2218, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key1981, 4), (key2218, 4), (key1981, 4)]

theorem rawRowCheck17041 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17041 := by decide +kernel

def row17041 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17041 : row17041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17041 := by decide +kernel

theorem rowEval17041 (x : Key → ℝ) : Integer.Sparse.eval row17041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17041, Integer.Sparse.eval_collectBalanced, rawRowCheck17041]

def rawRow17042 : Integer.Sparse Key := [(key2262, 4), (key1983, 4), (key1983, 4), (key2218, -2), (key2218, -2), (key1981, -2), (key1981, -2), (key1976, -2), (key1976, -2), (key2262, -2), (key2262, -2), (key1997, -2), (key1997, -2), (key1983, -2), (key1983, -2), (key2218, 4), (key1981, 4), (key1981, 4)]

theorem rawRowCheck17042 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form0 = rawRow17042 := by decide +kernel

def row17042 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17042 : row17042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17042 := by decide +kernel

theorem rowEval17042 (x : Key → ℝ) : Integer.Sparse.eval row17042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17042, Integer.Sparse.eval_collectBalanced, rawRowCheck17042]

def rawRow17043 : Integer.Sparse Key := [(key1981, 4), (key1981, 4), (key2266, 4), (key1981, -2), (key1997, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key2266, -2), (key1976, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key2224, -2), (key1983, 4), (key1983, 4), (key2224, 4)]

theorem rawRowCheck17043 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form0 = rawRow17043 := by decide +kernel

def row17043 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17043 : row17043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17043 := by decide +kernel

theorem rowEval17043 (x : Key → ℝ) : Integer.Sparse.eval row17043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17043, Integer.Sparse.eval_collectBalanced, rawRowCheck17043]

def rawRow17044 : Integer.Sparse Key := [(key1981, 4), (key2266, 4), (key1981, 4), (key1997, -2), (key1981, -2), (key2266, -2), (key1981, -2), (key2266, -2), (key1997, -2), (key1983, -2), (key1976, -2), (key2224, -2), (key1976, -2), (key2224, -2), (key1983, -2), (key1983, 4), (key2224, 4), (key1983, 4)]

theorem rawRowCheck17044 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form0 = rawRow17044 := by decide +kernel

def row17044 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17044 : row17044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17044 := by decide +kernel

theorem rowEval17044 (x : Key → ℝ) : Integer.Sparse.eval row17044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17044, Integer.Sparse.eval_collectBalanced, rawRowCheck17044]

def rawRow17045 : Integer.Sparse Key := [(key2266, 4), (key1981, 4), (key1981, 4), (key2266, -2), (key2266, -2), (key1997, -2), (key1997, -2), (key1981, -2), (key1981, -2), (key2224, -2), (key2224, -2), (key1983, -2), (key1983, -2), (key1976, -2), (key1976, -2), (key2224, 4), (key1983, 4), (key1983, 4)]

theorem rawRowCheck17045 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form0 = rawRow17045 := by decide +kernel

def row17045 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17045 : row17045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17045 := by decide +kernel

theorem rowEval17045 (x : Key → ℝ) : Integer.Sparse.eval row17045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17045, Integer.Sparse.eval_collectBalanced, rawRowCheck17045]

def rawRow17046 : Integer.Sparse Key := [(key1997, 4), (key1997, 4), (key1997, 4), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1976, 4), (key1976, 4), (key1976, 4)]

theorem rawRowCheck17046 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form0 = rawRow17046 := by decide +kernel

def row17046 : Integer.Sparse Key := [(key1976, 12), (key1981, -12), (key1983, -12), (key1997, 12)]

theorem rowCheck17046 : row17046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17046 := by decide +kernel

theorem rowEval17046 (x : Key → ℝ) : Integer.Sparse.eval row17046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17046, Integer.Sparse.eval_collectBalanced, rawRowCheck17046]

def rawRow17047 : Integer.Sparse Key := [(key1983, 4), (key1983, 4), (key2262, 4), (key1983, -2), (key1997, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key2262, -2), (key1976, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key2218, -2), (key1981, 4), (key1981, 4), (key2218, 4)]

theorem rawRowCheck17047 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form0 = rawRow17047 := by decide +kernel

def row17047 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17047 : row17047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17047 := by decide +kernel

theorem rowEval17047 (x : Key → ℝ) : Integer.Sparse.eval row17047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17047, Integer.Sparse.eval_collectBalanced, rawRowCheck17047]

def rawRow17048 : Integer.Sparse Key := [(key1983, 4), (key2262, 4), (key1983, 4), (key1997, -2), (key1983, -2), (key2262, -2), (key1983, -2), (key2262, -2), (key1997, -2), (key1981, -2), (key1976, -2), (key2218, -2), (key1976, -2), (key2218, -2), (key1981, -2), (key1981, 4), (key2218, 4), (key1981, 4)]

theorem rawRowCheck17048 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form0 = rawRow17048 := by decide +kernel

def row17048 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17048 : row17048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17048 := by decide +kernel

theorem rowEval17048 (x : Key → ℝ) : Integer.Sparse.eval row17048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17048, Integer.Sparse.eval_collectBalanced, rawRowCheck17048]

def rawRow17049 : Integer.Sparse Key := [(key2262, 4), (key1983, 4), (key1983, 4), (key2262, -2), (key2262, -2), (key1997, -2), (key1997, -2), (key1983, -2), (key1983, -2), (key2218, -2), (key2218, -2), (key1981, -2), (key1981, -2), (key1976, -2), (key1976, -2), (key2218, 4), (key1981, 4), (key1981, 4)]

theorem rawRowCheck17049 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form0 = rawRow17049 := by decide +kernel

def row17049 : Integer.Sparse Key := [(key1976, -4), (key1981, 4), (key1983, 4), (key1997, -4)]

theorem rowCheck17049 : row17049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17049 := by decide +kernel

theorem rowEval17049 (x : Key → ℝ) : Integer.Sparse.eval row17049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17049, Integer.Sparse.eval_collectBalanced, rawRowCheck17049]

def rawRow17050 : Integer.Sparse Key := [(key1997, 4), (key1997, 4), (key1997, 4), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1983, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1981, -2), (key1976, 4), (key1976, 4), (key1976, 4)]

theorem rawRowCheck17050 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form0 = rawRow17050 := by decide +kernel

def row17050 : Integer.Sparse Key := [(key1976, 12), (key1981, -12), (key1983, -12), (key1997, 12)]

theorem rowCheck17050 : row17050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17050 := by decide +kernel

theorem rowEval17050 (x : Key → ℝ) : Integer.Sparse.eval row17050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17050, Integer.Sparse.eval_collectBalanced, rawRowCheck17050]

def rawRow17051 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, -2), (key63, 6), (key693, -2), (key697, -2), (key701, -2), (key693, 2), (key697, 2), (key845, 2), (key848, 2), (key854, 2), (key855, 2), (key701, -2), (key854, -2), (key855, -2), (key701, 6), (key701, -2), (key854, -2), (key855, -2)]

theorem rawRowCheck17051 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form1 = rawRow17051 := by decide +kernel

def row17051 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

theorem rowCheck17051 : row17051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17051 := by decide +kernel

theorem rowEval17051 (x : Key → ℝ) : Integer.Sparse.eval row17051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17051, Integer.Sparse.eval_collectBalanced, rawRowCheck17051]

def rawRow17052 : Integer.Sparse Key := [(key56, -2), (key54, -2), (key63, -2), (key63, 6), (key697, -2), (key693, -2), (key701, -2), (key697, 2), (key693, 2), (key848, 2), (key845, 2), (key855, 2), (key854, 2), (key701, -2), (key855, -2), (key854, -2), (key701, 6), (key701, -2), (key855, -2), (key854, -2)]

theorem rawRowCheck17052 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form1 = rawRow17052 := by decide +kernel

def row17052 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

theorem rowCheck17052 : row17052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17052 := by decide +kernel

theorem rowEval17052 (x : Key → ℝ) : Integer.Sparse.eval row17052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17052, Integer.Sparse.eval_collectBalanced, rawRowCheck17052]

def rawRow17053 : Integer.Sparse Key := [(key54, -2), (key63, -2), (key56, -2), (key63, 6), (key693, -2), (key701, -2), (key697, -2), (key845, 2), (key854, 2), (key693, 2), (key855, 2), (key697, 2), (key848, 2), (key854, -2), (key701, -2), (key855, -2), (key701, 6), (key854, -2), (key701, -2), (key855, -2)]

theorem rawRowCheck17053 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form1 = rawRow17053 := by decide +kernel

def row17053 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

theorem rowCheck17053 : row17053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17053 := by decide +kernel

theorem rowEval17053 (x : Key → ℝ) : Integer.Sparse.eval row17053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17053, Integer.Sparse.eval_collectBalanced, rawRowCheck17053]

def rawRow17054 : Integer.Sparse Key := [(key63, -2), (key54, -2), (key56, -2), (key63, 6), (key701, -2), (key693, -2), (key697, -2), (key854, 2), (key845, 2), (key855, 2), (key693, 2), (key848, 2), (key697, 2), (key854, -2), (key855, -2), (key701, -2), (key701, 6), (key854, -2), (key855, -2), (key701, -2)]

theorem rawRowCheck17054 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form1 = rawRow17054 := by decide +kernel

def row17054 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

theorem rowCheck17054 : row17054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17054 := by decide +kernel

theorem rowEval17054 (x : Key → ℝ) : Integer.Sparse.eval row17054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17054, Integer.Sparse.eval_collectBalanced, rawRowCheck17054]

def rawRow17055 : Integer.Sparse Key := [(key56, -2), (key63, -2), (key54, -2), (key63, 6), (key697, -2), (key701, -2), (key693, -2), (key848, 2), (key855, 2), (key697, 2), (key854, 2), (key693, 2), (key845, 2), (key855, -2), (key701, -2), (key854, -2), (key701, 6), (key855, -2), (key701, -2), (key854, -2)]

theorem rawRowCheck17055 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form1 = rawRow17055 := by decide +kernel

def row17055 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

theorem rowCheck17055 : row17055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17055 := by decide +kernel

theorem rowEval17055 (x : Key → ℝ) : Integer.Sparse.eval row17055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17055, Integer.Sparse.eval_collectBalanced, rawRowCheck17055]

def rawRow17056 : Integer.Sparse Key := [(key63, -2), (key56, -2), (key54, -2), (key63, 6), (key701, -2), (key697, -2), (key693, -2), (key855, 2), (key848, 2), (key854, 2), (key697, 2), (key845, 2), (key693, 2), (key855, -2), (key854, -2), (key701, -2), (key701, 6), (key855, -2), (key854, -2), (key701, -2)]

theorem rawRowCheck17056 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form1 = rawRow17056 := by decide +kernel

def row17056 : Integer.Sparse Key := [(key54, -2), (key56, -2), (key63, 4), (key845, 2), (key848, 2), (key854, -2), (key855, -2)]

theorem rowCheck17056 : row17056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17056 := by decide +kernel

theorem rowEval17056 (x : Key → ℝ) : Integer.Sparse.eval row17056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17056, Integer.Sparse.eval_collectBalanced, rawRowCheck17056]

def rawRow17057 : Integer.Sparse Key := [(key54, -2), (key63, -2), (key63, -2), (key56, 6), (key845, -2), (key854, -2), (key854, -2), (key693, 2), (key701, 2), (key693, 2), (key855, 2), (key701, 2), (key855, 2), (key697, -2), (key697, -2), (key848, -2), (key854, 6), (key701, -2), (key701, -2), (key855, -2)]

theorem rawRowCheck17057 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form1 = rawRow17057 := by decide +kernel

def row17057 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

theorem rowCheck17057 : row17057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17057 := by decide +kernel

theorem rowEval17057 (x : Key → ℝ) : Integer.Sparse.eval row17057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17057, Integer.Sparse.eval_collectBalanced, rawRowCheck17057]

def rawRow17058 : Integer.Sparse Key := [(key63, -2), (key54, -2), (key63, -2), (key56, 6), (key854, -2), (key845, -2), (key854, -2), (key701, 2), (key693, 2), (key855, 2), (key693, 2), (key855, 2), (key701, 2), (key697, -2), (key848, -2), (key697, -2), (key854, 6), (key701, -2), (key855, -2), (key701, -2)]

theorem rawRowCheck17058 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form1 = rawRow17058 := by decide +kernel

def row17058 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

theorem rowCheck17058 : row17058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17058 := by decide +kernel

theorem rowEval17058 (x : Key → ℝ) : Integer.Sparse.eval row17058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17058, Integer.Sparse.eval_collectBalanced, rawRowCheck17058]

def rawRow17059 : Integer.Sparse Key := [(key63, -2), (key63, -2), (key54, -2), (key56, 6), (key854, -2), (key854, -2), (key845, -2), (key855, 2), (key855, 2), (key701, 2), (key701, 2), (key693, 2), (key693, 2), (key848, -2), (key697, -2), (key697, -2), (key854, 6), (key855, -2), (key701, -2), (key701, -2)]

theorem rawRowCheck17059 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form1 = rawRow17059 := by decide +kernel

def row17059 : Integer.Sparse Key := [(key54, -2), (key56, 6), (key63, -4), (key693, 4), (key697, -4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

theorem rowCheck17059 : row17059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17059 := by decide +kernel

theorem rowEval17059 (x : Key → ℝ) : Integer.Sparse.eval row17059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17059, Integer.Sparse.eval_collectBalanced, rawRowCheck17059]

def rawRow17060 : Integer.Sparse Key := [(key56, -2), (key63, -2), (key63, -2), (key54, 6), (key848, -2), (key855, -2), (key855, -2), (key697, 2), (key701, 2), (key697, 2), (key854, 2), (key701, 2), (key854, 2), (key693, -2), (key693, -2), (key845, -2), (key855, 6), (key701, -2), (key701, -2), (key854, -2)]

theorem rawRowCheck17060 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form1 = rawRow17060 := by decide +kernel

def row17060 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

theorem rowCheck17060 : row17060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17060 := by decide +kernel

theorem rowEval17060 (x : Key → ℝ) : Integer.Sparse.eval row17060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17060, Integer.Sparse.eval_collectBalanced, rawRowCheck17060]

def rawRow17061 : Integer.Sparse Key := [(key63, -2), (key56, -2), (key63, -2), (key54, 6), (key855, -2), (key848, -2), (key855, -2), (key701, 2), (key697, 2), (key854, 2), (key697, 2), (key854, 2), (key701, 2), (key693, -2), (key845, -2), (key693, -2), (key855, 6), (key701, -2), (key854, -2), (key701, -2)]

theorem rawRowCheck17061 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form1 = rawRow17061 := by decide +kernel

def row17061 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

theorem rowCheck17061 : row17061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17061 := by decide +kernel

theorem rowEval17061 (x : Key → ℝ) : Integer.Sparse.eval row17061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17061, Integer.Sparse.eval_collectBalanced, rawRowCheck17061]

def rawRow17062 : Integer.Sparse Key := [(key63, -2), (key63, -2), (key56, -2), (key54, 6), (key855, -2), (key855, -2), (key848, -2), (key854, 2), (key854, 2), (key701, 2), (key701, 2), (key697, 2), (key697, 2), (key845, -2), (key693, -2), (key693, -2), (key855, 6), (key854, -2), (key701, -2), (key701, -2)]

theorem rawRowCheck17062 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form1 = rawRow17062 := by decide +kernel

def row17062 : Integer.Sparse Key := [(key54, 6), (key56, -2), (key63, -4), (key693, -4), (key697, 4), (key845, -2), (key848, -2), (key854, 2), (key855, 2)]

theorem rowCheck17062 : row17062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17062 := by decide +kernel

theorem rowEval17062 (x : Key → ℝ) : Integer.Sparse.eval row17062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17062, Integer.Sparse.eval_collectBalanced, rawRowCheck17062]

def rawRow17063 : Integer.Sparse Key := [(key122, -2), (key128, -2), (key128, -2), (key128, 6), (key54, -2), (key63, -2), (key63, -2), (key693, 2), (key701, 2), (key693, 2), (key855, 2), (key701, 2), (key855, 2), (key701, -2), (key701, -2), (key855, -2), (key697, 6), (key697, -2), (key697, -2), (key848, -2)]

theorem rawRowCheck17063 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form1 = rawRow17063 := by decide +kernel

def row17063 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

theorem rowCheck17063 : row17063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17063 := by decide +kernel

theorem rowEval17063 (x : Key → ℝ) : Integer.Sparse.eval row17063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck17063, Integer.Sparse.eval_collectBalanced, rawRowCheck17063]

def rawRow17064 : Integer.Sparse Key := [(key128, -2), (key122, -2), (key128, -2), (key128, 6), (key63, -2), (key54, -2), (key63, -2), (key701, 2), (key693, 2), (key855, 2), (key693, 2), (key855, 2), (key701, 2), (key701, -2), (key855, -2), (key701, -2), (key697, 6), (key697, -2), (key848, -2), (key697, -2)]

theorem rawRowCheck17064 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form1 = rawRow17064 := by decide +kernel

def row17064 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

theorem rowCheck17064 : row17064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17064 := by decide +kernel

theorem rowEval17064 (x : Key → ℝ) : Integer.Sparse.eval row17064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17064, Integer.Sparse.eval_collectBalanced, rawRowCheck17064]

def rawRow17065 : Integer.Sparse Key := [(key128, -2), (key128, -2), (key122, -2), (key128, 6), (key63, -2), (key63, -2), (key54, -2), (key855, 2), (key855, 2), (key701, 2), (key701, 2), (key693, 2), (key693, 2), (key855, -2), (key701, -2), (key701, -2), (key697, 6), (key848, -2), (key697, -2), (key697, -2)]

theorem rawRowCheck17065 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form1 = rawRow17065 := by decide +kernel

def row17065 : Integer.Sparse Key := [(key54, -2), (key63, -4), (key122, -2), (key128, 2), (key693, 4), (key697, 2), (key848, -2), (key855, 2)]

theorem rowCheck17065 : row17065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17065 := by decide +kernel

theorem rowEval17065 (x : Key → ℝ) : Integer.Sparse.eval row17065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17065, Integer.Sparse.eval_collectBalanced, rawRowCheck17065]

def rawRow17066 : Integer.Sparse Key := [(key128, -2), (key128, -2), (key128, -2), (key122, 6), (key199, -2), (key199, -2), (key199, -2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key54, -2), (key693, -2), (key693, -2), (key848, 6), (key697, -2), (key697, -2), (key697, -2)]

theorem rawRowCheck17066 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form1 = rawRow17066 := by decide +kernel

def row17066 : Integer.Sparse Key := [(key54, -2), (key63, 12), (key122, 6), (key128, -6), (key199, -6), (key693, -4), (key697, -6), (key848, 6)]

theorem rowCheck17066 : row17066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17066 := by decide +kernel

theorem rowEval17066 (x : Key → ℝ) : Integer.Sparse.eval row17066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17066, Integer.Sparse.eval_collectBalanced, rawRowCheck17066]

def rawRow17067 : Integer.Sparse Key := [(key198, -2), (key199, -2), (key199, -2), (key199, 6), (key56, -2), (key63, -2), (key63, -2), (key56, 2), (key63, 2), (key56, 2), (key128, 2), (key63, 2), (key128, 2), (key63, -2), (key63, -2), (key128, -2), (key54, 6), (key693, -2), (key693, -2), (key845, -2)]

theorem rawRowCheck17067 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form1 = rawRow17067 := by decide +kernel

def row17067 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

theorem rowCheck17067 : row17067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17067 := by decide +kernel

theorem rowEval17067 (x : Key → ℝ) : Integer.Sparse.eval row17067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17067, Integer.Sparse.eval_collectBalanced, rawRowCheck17067]

def rawRow17068 : Integer.Sparse Key := [(key199, -2), (key198, -2), (key199, -2), (key199, 6), (key63, -2), (key56, -2), (key63, -2), (key63, 2), (key56, 2), (key128, 2), (key56, 2), (key128, 2), (key63, 2), (key63, -2), (key128, -2), (key63, -2), (key54, 6), (key693, -2), (key845, -2), (key693, -2)]

theorem rawRowCheck17068 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form1 = rawRow17068 := by decide +kernel

def row17068 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

theorem rowCheck17068 : row17068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17068 := by decide +kernel

theorem rowEval17068 (x : Key → ℝ) : Integer.Sparse.eval row17068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17068, Integer.Sparse.eval_collectBalanced, rawRowCheck17068]

def rawRow17069 : Integer.Sparse Key := [(key199, -2), (key199, -2), (key198, -2), (key199, 6), (key63, -2), (key63, -2), (key56, -2), (key128, 2), (key128, 2), (key63, 2), (key63, 2), (key56, 2), (key56, 2), (key128, -2), (key63, -2), (key63, -2), (key54, 6), (key845, -2), (key693, -2), (key693, -2)]

theorem rawRowCheck17069 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form1 = rawRow17069 := by decide +kernel

def row17069 : Integer.Sparse Key := [(key54, 6), (key56, 2), (key63, -4), (key128, 2), (key198, -2), (key199, 2), (key693, -4), (key845, -2)]

theorem rowCheck17069 : row17069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17069 := by decide +kernel

theorem rowEval17069 (x : Key → ℝ) : Integer.Sparse.eval row17069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17069, Integer.Sparse.eval_collectBalanced, rawRowCheck17069]

def rawRow17070 : Integer.Sparse Key := [(key199, -2), (key199, -2), (key199, -2), (key198, 6), (key128, -2), (key128, -2), (key128, -2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key63, 2), (key56, -2), (key56, -2), (key56, -2), (key122, 6), (key54, -2), (key693, -2), (key693, -2)]

theorem rawRowCheck17070 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form1 = rawRow17070 := by decide +kernel

def row17070 : Integer.Sparse Key := [(key54, -2), (key56, -6), (key63, 12), (key122, 6), (key128, -6), (key198, 6), (key199, -6), (key693, -4)]

theorem rowCheck17070 : row17070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17070 := by decide +kernel

theorem rowEval17070 (x : Key → ℝ) : Integer.Sparse.eval row17070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17070, Integer.Sparse.eval_collectBalanced, rawRowCheck17070]

def rawRow17071 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, -2), (key1985, 6), (key1973, -2), (key1978, -2), (key1985, -2), (key1973, 2), (key1978, 2), (key2209, 2), (key2215, 2), (key2226, 2), (key2230, 2), (key1985, -2), (key2226, -2), (key2230, -2), (key1985, 6), (key1985, -2), (key2226, -2), (key2230, -2)]

theorem rawRowCheck17071 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form2 = rawRow17071 := by decide +kernel

def row17071 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

theorem rowCheck17071 : row17071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17071 := by decide +kernel

theorem rowEval17071 (x : Key → ℝ) : Integer.Sparse.eval row17071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17071, Integer.Sparse.eval_collectBalanced, rawRowCheck17071]

def rawRow17072 : Integer.Sparse Key := [(key1978, -2), (key1973, -2), (key1985, -2), (key1985, 6), (key1978, -2), (key1973, -2), (key1985, -2), (key1978, 2), (key1973, 2), (key2215, 2), (key2209, 2), (key2230, 2), (key2226, 2), (key1985, -2), (key2230, -2), (key2226, -2), (key1985, 6), (key1985, -2), (key2230, -2), (key2226, -2)]

theorem rawRowCheck17072 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form2 = rawRow17072 := by decide +kernel

def row17072 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

theorem rowCheck17072 : row17072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17072 := by decide +kernel

theorem rowEval17072 (x : Key → ℝ) : Integer.Sparse.eval row17072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17072, Integer.Sparse.eval_collectBalanced, rawRowCheck17072]

def rawRow17073 : Integer.Sparse Key := [(key1973, -2), (key1985, -2), (key1978, -2), (key1985, 6), (key1973, -2), (key1985, -2), (key1978, -2), (key2209, 2), (key2226, 2), (key1973, 2), (key2230, 2), (key1978, 2), (key2215, 2), (key2226, -2), (key1985, -2), (key2230, -2), (key1985, 6), (key2226, -2), (key1985, -2), (key2230, -2)]

theorem rawRowCheck17073 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form2 = rawRow17073 := by decide +kernel

def row17073 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

theorem rowCheck17073 : row17073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17073 := by decide +kernel

theorem rowEval17073 (x : Key → ℝ) : Integer.Sparse.eval row17073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17073, Integer.Sparse.eval_collectBalanced, rawRowCheck17073]

def rawRow17074 : Integer.Sparse Key := [(key1985, -2), (key1973, -2), (key1978, -2), (key1985, 6), (key1985, -2), (key1973, -2), (key1978, -2), (key2226, 2), (key2209, 2), (key2230, 2), (key1973, 2), (key2215, 2), (key1978, 2), (key2226, -2), (key2230, -2), (key1985, -2), (key1985, 6), (key2226, -2), (key2230, -2), (key1985, -2)]

theorem rawRowCheck17074 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form2 = rawRow17074 := by decide +kernel

def row17074 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

theorem rowCheck17074 : row17074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17074 := by decide +kernel

theorem rowEval17074 (x : Key → ℝ) : Integer.Sparse.eval row17074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17074, Integer.Sparse.eval_collectBalanced, rawRowCheck17074]

def rawRow17075 : Integer.Sparse Key := [(key1978, -2), (key1985, -2), (key1973, -2), (key1985, 6), (key1978, -2), (key1985, -2), (key1973, -2), (key2215, 2), (key2230, 2), (key1978, 2), (key2226, 2), (key1973, 2), (key2209, 2), (key2230, -2), (key1985, -2), (key2226, -2), (key1985, 6), (key2230, -2), (key1985, -2), (key2226, -2)]

theorem rawRowCheck17075 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form2 = rawRow17075 := by decide +kernel

def row17075 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

theorem rowCheck17075 : row17075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17075 := by decide +kernel

theorem rowEval17075 (x : Key → ℝ) : Integer.Sparse.eval row17075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17075, Integer.Sparse.eval_collectBalanced, rawRowCheck17075]

def rawRow17076 : Integer.Sparse Key := [(key1985, -2), (key1978, -2), (key1973, -2), (key1985, 6), (key1985, -2), (key1978, -2), (key1973, -2), (key2230, 2), (key2215, 2), (key2226, 2), (key1978, 2), (key2209, 2), (key1973, 2), (key2230, -2), (key2226, -2), (key1985, -2), (key1985, 6), (key2230, -2), (key2226, -2), (key1985, -2)]

theorem rawRowCheck17076 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form2 = rawRow17076 := by decide +kernel

def row17076 : Integer.Sparse Key := [(key1973, -2), (key1978, -2), (key1985, 4), (key2209, 2), (key2215, 2), (key2226, -2), (key2230, -2)]

theorem rowCheck17076 : row17076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17076 := by decide +kernel

theorem rowEval17076 (x : Key → ℝ) : Integer.Sparse.eval row17076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17076, Integer.Sparse.eval_collectBalanced, rawRowCheck17076]

def rawRow17077 : Integer.Sparse Key := [(key1973, -2), (key1985, -2), (key1985, -2), (key1978, 6), (key2209, -2), (key2226, -2), (key2226, -2), (key1973, 2), (key1985, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key2230, 2), (key1978, -2), (key1978, -2), (key2215, -2), (key2226, 6), (key1985, -2), (key1985, -2), (key2230, -2)]

theorem rawRowCheck17077 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form2 = rawRow17077 := by decide +kernel

def row17077 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17077 : row17077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17077 := by decide +kernel

theorem rowEval17077 (x : Key → ℝ) : Integer.Sparse.eval row17077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17077, Integer.Sparse.eval_collectBalanced, rawRowCheck17077]

def rawRow17078 : Integer.Sparse Key := [(key1985, -2), (key1973, -2), (key1985, -2), (key1978, 6), (key2226, -2), (key2209, -2), (key2226, -2), (key1985, 2), (key1973, 2), (key2230, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key1978, -2), (key2215, -2), (key1978, -2), (key2226, 6), (key1985, -2), (key2230, -2), (key1985, -2)]

theorem rawRowCheck17078 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form2 = rawRow17078 := by decide +kernel

def row17078 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17078 : row17078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17078 := by decide +kernel

theorem rowEval17078 (x : Key → ℝ) : Integer.Sparse.eval row17078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17078, Integer.Sparse.eval_collectBalanced, rawRowCheck17078]

def rawRow17079 : Integer.Sparse Key := [(key1985, -2), (key1985, -2), (key1973, -2), (key1978, 6), (key2226, -2), (key2226, -2), (key2209, -2), (key2230, 2), (key2230, 2), (key1985, 2), (key1985, 2), (key1973, 2), (key1973, 2), (key2215, -2), (key1978, -2), (key1978, -2), (key2226, 6), (key2230, -2), (key1985, -2), (key1985, -2)]

theorem rawRowCheck17079 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form2 = rawRow17079 := by decide +kernel

def row17079 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17079 : row17079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17079 := by decide +kernel

theorem rowEval17079 (x : Key → ℝ) : Integer.Sparse.eval row17079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17079, Integer.Sparse.eval_collectBalanced, rawRowCheck17079]

def rawRow17080 : Integer.Sparse Key := [(key1978, -2), (key1985, -2), (key1985, -2), (key1973, 6), (key2215, -2), (key2230, -2), (key2230, -2), (key1978, 2), (key1985, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key2226, 2), (key1973, -2), (key1973, -2), (key2209, -2), (key2230, 6), (key1985, -2), (key1985, -2), (key2226, -2)]

theorem rawRowCheck17080 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form2 = rawRow17080 := by decide +kernel

def row17080 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17080 : row17080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17080 := by decide +kernel

theorem rowEval17080 (x : Key → ℝ) : Integer.Sparse.eval row17080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17080, Integer.Sparse.eval_collectBalanced, rawRowCheck17080]

def rawRow17081 : Integer.Sparse Key := [(key1985, -2), (key1978, -2), (key1985, -2), (key1973, 6), (key2230, -2), (key2215, -2), (key2230, -2), (key1985, 2), (key1978, 2), (key2226, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key1973, -2), (key2209, -2), (key1973, -2), (key2230, 6), (key1985, -2), (key2226, -2), (key1985, -2)]

theorem rawRowCheck17081 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form2 = rawRow17081 := by decide +kernel

def row17081 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17081 : row17081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17081 := by decide +kernel

theorem rowEval17081 (x : Key → ℝ) : Integer.Sparse.eval row17081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17081, Integer.Sparse.eval_collectBalanced, rawRowCheck17081]

def rawRow17082 : Integer.Sparse Key := [(key1985, -2), (key1985, -2), (key1978, -2), (key1973, 6), (key2230, -2), (key2230, -2), (key2215, -2), (key2226, 2), (key2226, 2), (key1985, 2), (key1985, 2), (key1978, 2), (key1978, 2), (key2209, -2), (key1973, -2), (key1973, -2), (key2230, 6), (key2226, -2), (key1985, -2), (key1985, -2)]

theorem rawRowCheck17082 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form2 = rawRow17082 := by decide +kernel

def row17082 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17082 : row17082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17082 := by decide +kernel

theorem rowEval17082 (x : Key → ℝ) : Integer.Sparse.eval row17082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17082, Integer.Sparse.eval_collectBalanced, rawRowCheck17082]

def rawRow17083 : Integer.Sparse Key := [(key2209, -2), (key2226, -2), (key2226, -2), (key2226, 6), (key1973, -2), (key1985, -2), (key1985, -2), (key1973, 2), (key1985, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key2230, 2), (key1985, -2), (key1985, -2), (key2230, -2), (key1978, 6), (key1978, -2), (key1978, -2), (key2215, -2)]

theorem rawRowCheck17083 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form2 = rawRow17083 := by decide +kernel

def row17083 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17083 : row17083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17083 := by decide +kernel

theorem rowEval17083 (x : Key → ℝ) : Integer.Sparse.eval row17083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck17083, Integer.Sparse.eval_collectBalanced, rawRowCheck17083]

def rawRow17084 : Integer.Sparse Key := [(key2226, -2), (key2209, -2), (key2226, -2), (key2226, 6), (key1985, -2), (key1973, -2), (key1985, -2), (key1985, 2), (key1973, 2), (key2230, 2), (key1973, 2), (key2230, 2), (key1985, 2), (key1985, -2), (key2230, -2), (key1985, -2), (key1978, 6), (key1978, -2), (key2215, -2), (key1978, -2)]

theorem rawRowCheck17084 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form2 = rawRow17084 := by decide +kernel

def row17084 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17084 : row17084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17084 := by decide +kernel

theorem rowEval17084 (x : Key → ℝ) : Integer.Sparse.eval row17084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17084, Integer.Sparse.eval_collectBalanced, rawRowCheck17084]

def rawRow17085 : Integer.Sparse Key := [(key2226, -2), (key2226, -2), (key2209, -2), (key2226, 6), (key1985, -2), (key1985, -2), (key1973, -2), (key2230, 2), (key2230, 2), (key1985, 2), (key1985, 2), (key1973, 2), (key1973, 2), (key2230, -2), (key1985, -2), (key1985, -2), (key1978, 6), (key2215, -2), (key1978, -2), (key1978, -2)]

theorem rawRowCheck17085 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form2 = rawRow17085 := by decide +kernel

def row17085 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17085 : row17085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17085 := by decide +kernel

theorem rowEval17085 (x : Key → ℝ) : Integer.Sparse.eval row17085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17085, Integer.Sparse.eval_collectBalanced, rawRowCheck17085]

def rawRow17086 : Integer.Sparse Key := [(key2226, -2), (key2226, -2), (key2226, -2), (key2209, 6), (key2230, -2), (key2230, -2), (key2230, -2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1973, -2), (key1973, -2), (key1973, -2), (key2215, 6), (key1978, -2), (key1978, -2), (key1978, -2)]

theorem rawRowCheck17086 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form2 = rawRow17086 := by decide +kernel

def row17086 : Integer.Sparse Key := [(key1973, -6), (key1978, -6), (key1985, 12), (key2209, 6), (key2215, 6), (key2226, -6), (key2230, -6)]

theorem rowCheck17086 : row17086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17086 := by decide +kernel

theorem rowEval17086 (x : Key → ℝ) : Integer.Sparse.eval row17086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17086, Integer.Sparse.eval_collectBalanced, rawRowCheck17086]

def rawRow17087 : Integer.Sparse Key := [(key2215, -2), (key2230, -2), (key2230, -2), (key2230, 6), (key1978, -2), (key1985, -2), (key1985, -2), (key1978, 2), (key1985, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key2226, 2), (key1985, -2), (key1985, -2), (key2226, -2), (key1973, 6), (key1973, -2), (key1973, -2), (key2209, -2)]

theorem rawRowCheck17087 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form2 = rawRow17087 := by decide +kernel

def row17087 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17087 : row17087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17087 := by decide +kernel

theorem rowEval17087 (x : Key → ℝ) : Integer.Sparse.eval row17087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17087, Integer.Sparse.eval_collectBalanced, rawRowCheck17087]

def rawRow17088 : Integer.Sparse Key := [(key2230, -2), (key2215, -2), (key2230, -2), (key2230, 6), (key1985, -2), (key1978, -2), (key1985, -2), (key1985, 2), (key1978, 2), (key2226, 2), (key1978, 2), (key2226, 2), (key1985, 2), (key1985, -2), (key2226, -2), (key1985, -2), (key1973, 6), (key1973, -2), (key2209, -2), (key1973, -2)]

theorem rawRowCheck17088 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form2 = rawRow17088 := by decide +kernel

def row17088 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17088 : row17088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17088 := by decide +kernel

theorem rowEval17088 (x : Key → ℝ) : Integer.Sparse.eval row17088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17088, Integer.Sparse.eval_collectBalanced, rawRowCheck17088]

def rawRow17089 : Integer.Sparse Key := [(key2230, -2), (key2230, -2), (key2215, -2), (key2230, 6), (key1985, -2), (key1985, -2), (key1978, -2), (key2226, 2), (key2226, 2), (key1985, 2), (key1985, 2), (key1978, 2), (key1978, 2), (key2226, -2), (key1985, -2), (key1985, -2), (key1973, 6), (key2209, -2), (key1973, -2), (key1973, -2)]

theorem rawRowCheck17089 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form2 = rawRow17089 := by decide +kernel

def row17089 : Integer.Sparse Key := [(key1973, 2), (key1978, 2), (key1985, -4), (key2209, -2), (key2215, -2), (key2226, 2), (key2230, 2)]

theorem rowCheck17089 : row17089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17089 := by decide +kernel

theorem rowEval17089 (x : Key → ℝ) : Integer.Sparse.eval row17089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17089, Integer.Sparse.eval_collectBalanced, rawRowCheck17089]

def rawRow17090 : Integer.Sparse Key := [(key2230, -2), (key2230, -2), (key2230, -2), (key2215, 6), (key2226, -2), (key2226, -2), (key2226, -2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1985, 2), (key1978, -2), (key1978, -2), (key1978, -2), (key2209, 6), (key1973, -2), (key1973, -2), (key1973, -2)]

theorem rawRowCheck17090 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form2 = rawRow17090 := by decide +kernel

def row17090 : Integer.Sparse Key := [(key1973, -6), (key1978, -6), (key1985, 12), (key2209, 6), (key2215, 6), (key2226, -6), (key2230, -6)]

theorem rowCheck17090 : row17090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17090 := by decide +kernel

theorem rowEval17090 (x : Key → ℝ) : Integer.Sparse.eval row17090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17090, Integer.Sparse.eval_collectBalanced, rawRowCheck17090]

def rawRow17091 : Integer.Sparse Key := [(key2015, 6), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, 6), (key2015, -2), (key2129, -2), (key2132, -2), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, 2), (key2213, 2)]

theorem rawRowCheck17091 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form3 = rawRow17091 := by decide +kernel

def row17091 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

theorem rowCheck17091 : row17091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17091 := by decide +kernel

theorem rowEval17091 (x : Key → ℝ) : Integer.Sparse.eval row17091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17091, Integer.Sparse.eval_collectBalanced, rawRowCheck17091]

def rawRow17092 : Integer.Sparse Key := [(key2015, 6), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, 6), (key2015, -2), (key2132, -2), (key2129, -2), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2045, 2), (key2044, 2), (key2132, 2), (key2129, 2), (key2213, 2), (key2212, 2)]

theorem rawRowCheck17092 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form3 = rawRow17092 := by decide +kernel

def row17092 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

theorem rowCheck17092 : row17092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17092 := by decide +kernel

theorem rowEval17092 (x : Key → ℝ) : Integer.Sparse.eval row17092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17092, Integer.Sparse.eval_collectBalanced, rawRowCheck17092]

def rawRow17093 : Integer.Sparse Key := [(key2015, 6), (key2044, -2), (key2015, -2), (key2045, -2), (key2015, 6), (key2129, -2), (key2015, -2), (key2132, -2), (key2044, -2), (key2015, -2), (key2045, -2), (key2129, -2), (key2015, -2), (key2132, -2), (key2129, 2), (key2212, 2), (key2044, 2), (key2213, 2), (key2045, 2), (key2132, 2)]

theorem rawRowCheck17093 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form3 = rawRow17093 := by decide +kernel

def row17093 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

theorem rowCheck17093 : row17093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17093 := by decide +kernel

theorem rowEval17093 (x : Key → ℝ) : Integer.Sparse.eval row17093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17093, Integer.Sparse.eval_collectBalanced, rawRowCheck17093]

def rawRow17094 : Integer.Sparse Key := [(key2015, 6), (key2044, -2), (key2045, -2), (key2015, -2), (key2015, 6), (key2129, -2), (key2132, -2), (key2015, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2015, -2), (key2212, 2), (key2129, 2), (key2213, 2), (key2044, 2), (key2132, 2), (key2045, 2)]

theorem rawRowCheck17094 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form3 = rawRow17094 := by decide +kernel

def row17094 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

theorem rowCheck17094 : row17094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17094 := by decide +kernel

theorem rowEval17094 (x : Key → ℝ) : Integer.Sparse.eval row17094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17094, Integer.Sparse.eval_collectBalanced, rawRowCheck17094]

def rawRow17095 : Integer.Sparse Key := [(key2015, 6), (key2045, -2), (key2015, -2), (key2044, -2), (key2015, 6), (key2132, -2), (key2015, -2), (key2129, -2), (key2045, -2), (key2015, -2), (key2044, -2), (key2132, -2), (key2015, -2), (key2129, -2), (key2132, 2), (key2213, 2), (key2045, 2), (key2212, 2), (key2044, 2), (key2129, 2)]

theorem rawRowCheck17095 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form3 = rawRow17095 := by decide +kernel

def row17095 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

theorem rowCheck17095 : row17095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17095 := by decide +kernel

theorem rowEval17095 (x : Key → ℝ) : Integer.Sparse.eval row17095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17095, Integer.Sparse.eval_collectBalanced, rawRowCheck17095]

def rawRow17096 : Integer.Sparse Key := [(key2015, 6), (key2045, -2), (key2044, -2), (key2015, -2), (key2015, 6), (key2132, -2), (key2129, -2), (key2015, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2015, -2), (key2213, 2), (key2132, 2), (key2212, 2), (key2045, 2), (key2129, 2), (key2044, 2)]

theorem rawRowCheck17096 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form3 = rawRow17096 := by decide +kernel

def row17096 : Integer.Sparse Key := [(key2015, 4), (key2044, -2), (key2045, -2), (key2129, -2), (key2132, -2), (key2212, 2), (key2213, 2)]

theorem rowCheck17096 : row17096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17096 := by decide +kernel

theorem rowEval17096 (x : Key → ℝ) : Integer.Sparse.eval row17096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17096, Integer.Sparse.eval_collectBalanced, rawRowCheck17096]

def rawRow17097 : Integer.Sparse Key := [(key2044, 6), (key2015, -2), (key2015, -2), (key2045, -2), (key2129, 6), (key2015, -2), (key2015, -2), (key2132, -2), (key2129, -2), (key2129, -2), (key2212, -2), (key2044, -2), (key2044, -2), (key2213, -2), (key2015, 2), (key2045, 2), (key2015, 2), (key2132, 2), (key2045, 2), (key2132, 2)]

theorem rawRowCheck17097 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form3 = rawRow17097 := by decide +kernel

def row17097 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17097 : row17097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17097 := by decide +kernel

theorem rowEval17097 (x : Key → ℝ) : Integer.Sparse.eval row17097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17097, Integer.Sparse.eval_collectBalanced, rawRowCheck17097]

def rawRow17098 : Integer.Sparse Key := [(key2044, 6), (key2015, -2), (key2045, -2), (key2015, -2), (key2129, 6), (key2015, -2), (key2132, -2), (key2015, -2), (key2129, -2), (key2212, -2), (key2129, -2), (key2044, -2), (key2213, -2), (key2044, -2), (key2045, 2), (key2015, 2), (key2132, 2), (key2015, 2), (key2132, 2), (key2045, 2)]

theorem rawRowCheck17098 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form3 = rawRow17098 := by decide +kernel

def row17098 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17098 : row17098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17098 := by decide +kernel

theorem rowEval17098 (x : Key → ℝ) : Integer.Sparse.eval row17098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17098, Integer.Sparse.eval_collectBalanced, rawRowCheck17098]

def rawRow17099 : Integer.Sparse Key := [(key2044, 6), (key2045, -2), (key2015, -2), (key2015, -2), (key2129, 6), (key2132, -2), (key2015, -2), (key2015, -2), (key2212, -2), (key2129, -2), (key2129, -2), (key2213, -2), (key2044, -2), (key2044, -2), (key2132, 2), (key2132, 2), (key2045, 2), (key2045, 2), (key2015, 2), (key2015, 2)]

theorem rawRowCheck17099 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form3 = rawRow17099 := by decide +kernel

def row17099 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17099 : row17099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17099 := by decide +kernel

theorem rowEval17099 (x : Key → ℝ) : Integer.Sparse.eval row17099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17099, Integer.Sparse.eval_collectBalanced, rawRowCheck17099]

def rawRow17100 : Integer.Sparse Key := [(key2045, 6), (key2015, -2), (key2015, -2), (key2044, -2), (key2132, 6), (key2015, -2), (key2015, -2), (key2129, -2), (key2132, -2), (key2132, -2), (key2213, -2), (key2045, -2), (key2045, -2), (key2212, -2), (key2015, 2), (key2044, 2), (key2015, 2), (key2129, 2), (key2044, 2), (key2129, 2)]

theorem rawRowCheck17100 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form3 = rawRow17100 := by decide +kernel

def row17100 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17100 : row17100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17100 := by decide +kernel

theorem rowEval17100 (x : Key → ℝ) : Integer.Sparse.eval row17100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17100, Integer.Sparse.eval_collectBalanced, rawRowCheck17100]

def rawRow17101 : Integer.Sparse Key := [(key2045, 6), (key2015, -2), (key2044, -2), (key2015, -2), (key2132, 6), (key2015, -2), (key2129, -2), (key2015, -2), (key2132, -2), (key2213, -2), (key2132, -2), (key2045, -2), (key2212, -2), (key2045, -2), (key2044, 2), (key2015, 2), (key2129, 2), (key2015, 2), (key2129, 2), (key2044, 2)]

theorem rawRowCheck17101 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form3 = rawRow17101 := by decide +kernel

def row17101 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17101 : row17101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17101 := by decide +kernel

theorem rowEval17101 (x : Key → ℝ) : Integer.Sparse.eval row17101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17101, Integer.Sparse.eval_collectBalanced, rawRowCheck17101]

def rawRow17102 : Integer.Sparse Key := [(key2045, 6), (key2044, -2), (key2015, -2), (key2015, -2), (key2132, 6), (key2129, -2), (key2015, -2), (key2015, -2), (key2213, -2), (key2132, -2), (key2132, -2), (key2212, -2), (key2045, -2), (key2045, -2), (key2129, 2), (key2129, 2), (key2044, 2), (key2044, 2), (key2015, 2), (key2015, 2)]

theorem rawRowCheck17102 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form3 = rawRow17102 := by decide +kernel

def row17102 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17102 : row17102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17102 := by decide +kernel

theorem rowEval17102 (x : Key → ℝ) : Integer.Sparse.eval row17102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17102, Integer.Sparse.eval_collectBalanced, rawRowCheck17102]

def rawRow17103 : Integer.Sparse Key := [(key2129, 6), (key2129, -2), (key2129, -2), (key2212, -2), (key2044, 6), (key2044, -2), (key2044, -2), (key2213, -2), (key2015, -2), (key2015, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, 2), (key2045, 2), (key2015, 2), (key2132, 2), (key2045, 2), (key2132, 2)]

theorem rawRowCheck17103 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form3 = rawRow17103 := by decide +kernel

def row17103 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17103 : row17103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17103 := by decide +kernel

theorem rowEval17103 (x : Key → ℝ) : Integer.Sparse.eval row17103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck17103, Integer.Sparse.eval_collectBalanced, rawRowCheck17103]

def rawRow17104 : Integer.Sparse Key := [(key2129, 6), (key2129, -2), (key2212, -2), (key2129, -2), (key2044, 6), (key2044, -2), (key2213, -2), (key2044, -2), (key2015, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, -2), (key2045, 2), (key2015, 2), (key2132, 2), (key2015, 2), (key2132, 2), (key2045, 2)]

theorem rawRowCheck17104 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form3 = rawRow17104 := by decide +kernel

def row17104 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17104 : row17104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17104 := by decide +kernel

theorem rowEval17104 (x : Key → ℝ) : Integer.Sparse.eval row17104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17104, Integer.Sparse.eval_collectBalanced, rawRowCheck17104]

def rawRow17105 : Integer.Sparse Key := [(key2129, 6), (key2212, -2), (key2129, -2), (key2129, -2), (key2044, 6), (key2213, -2), (key2044, -2), (key2044, -2), (key2045, -2), (key2015, -2), (key2015, -2), (key2132, -2), (key2015, -2), (key2015, -2), (key2132, 2), (key2132, 2), (key2045, 2), (key2045, 2), (key2015, 2), (key2015, 2)]

theorem rawRowCheck17105 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form3 = rawRow17105 := by decide +kernel

def row17105 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17105 : row17105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17105 := by decide +kernel

theorem rowEval17105 (x : Key → ℝ) : Integer.Sparse.eval row17105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17105, Integer.Sparse.eval_collectBalanced, rawRowCheck17105]

def rawRow17106 : Integer.Sparse Key := [(key2212, 6), (key2129, -2), (key2129, -2), (key2129, -2), (key2213, 6), (key2044, -2), (key2044, -2), (key2044, -2), (key2132, -2), (key2132, -2), (key2132, -2), (key2045, -2), (key2045, -2), (key2045, -2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2)]

theorem rawRowCheck17106 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form3 = rawRow17106 := by decide +kernel

def row17106 : Integer.Sparse Key := [(key2015, 12), (key2044, -6), (key2045, -6), (key2129, -6), (key2132, -6), (key2212, 6), (key2213, 6)]

theorem rowCheck17106 : row17106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17106 := by decide +kernel

theorem rowEval17106 (x : Key → ℝ) : Integer.Sparse.eval row17106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17106, Integer.Sparse.eval_collectBalanced, rawRowCheck17106]

def rawRow17107 : Integer.Sparse Key := [(key2132, 6), (key2132, -2), (key2132, -2), (key2213, -2), (key2045, 6), (key2045, -2), (key2045, -2), (key2212, -2), (key2015, -2), (key2015, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, 2), (key2044, 2), (key2015, 2), (key2129, 2), (key2044, 2), (key2129, 2)]

theorem rawRowCheck17107 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form3 = rawRow17107 := by decide +kernel

def row17107 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17107 : row17107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17107 := by decide +kernel

theorem rowEval17107 (x : Key → ℝ) : Integer.Sparse.eval row17107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17107, Integer.Sparse.eval_collectBalanced, rawRowCheck17107]

def rawRow17108 : Integer.Sparse Key := [(key2132, 6), (key2132, -2), (key2213, -2), (key2132, -2), (key2045, 6), (key2045, -2), (key2212, -2), (key2045, -2), (key2015, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, -2), (key2044, 2), (key2015, 2), (key2129, 2), (key2015, 2), (key2129, 2), (key2044, 2)]

theorem rawRowCheck17108 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form3 = rawRow17108 := by decide +kernel

def row17108 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17108 : row17108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17108 := by decide +kernel

theorem rowEval17108 (x : Key → ℝ) : Integer.Sparse.eval row17108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17108, Integer.Sparse.eval_collectBalanced, rawRowCheck17108]

def rawRow17109 : Integer.Sparse Key := [(key2132, 6), (key2213, -2), (key2132, -2), (key2132, -2), (key2045, 6), (key2212, -2), (key2045, -2), (key2045, -2), (key2044, -2), (key2015, -2), (key2015, -2), (key2129, -2), (key2015, -2), (key2015, -2), (key2129, 2), (key2129, 2), (key2044, 2), (key2044, 2), (key2015, 2), (key2015, 2)]

theorem rawRowCheck17109 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form3 = rawRow17109 := by decide +kernel

def row17109 : Integer.Sparse Key := [(key2015, -4), (key2044, 2), (key2045, 2), (key2129, 2), (key2132, 2), (key2212, -2), (key2213, -2)]

theorem rowCheck17109 : row17109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17109 := by decide +kernel

theorem rowEval17109 (x : Key → ℝ) : Integer.Sparse.eval row17109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17109, Integer.Sparse.eval_collectBalanced, rawRowCheck17109]

def rawRow17110 : Integer.Sparse Key := [(key2213, 6), (key2132, -2), (key2132, -2), (key2132, -2), (key2212, 6), (key2045, -2), (key2045, -2), (key2045, -2), (key2129, -2), (key2129, -2), (key2129, -2), (key2044, -2), (key2044, -2), (key2044, -2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2), (key2015, 2)]

theorem rawRowCheck17110 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form3 = rawRow17110 := by decide +kernel

def row17110 : Integer.Sparse Key := [(key2015, 12), (key2044, -6), (key2045, -6), (key2129, -6), (key2132, -6), (key2212, 6), (key2213, 6)]

theorem rowCheck17110 : row17110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17110 := by decide +kernel

theorem rowEval17110 (x : Key → ℝ) : Integer.Sparse.eval row17110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17110, Integer.Sparse.eval_collectBalanced, rawRowCheck17110]

def rawRow17111 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, -2), (key699, 6), (key694, -2), (key696, -2), (key699, -2), (key694, 2), (key696, 2), (key846, 2), (key847, 2), (key850, 2), (key852, 2), (key699, -2), (key850, -2), (key852, -2), (key699, 6), (key699, -2), (key850, -2), (key852, -2)]

theorem rawRowCheck17111 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form4 = rawRow17111 := by decide +kernel

def row17111 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

theorem rowCheck17111 : row17111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17111 := by decide +kernel

theorem rowEval17111 (x : Key → ℝ) : Integer.Sparse.eval row17111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17111, Integer.Sparse.eval_collectBalanced, rawRowCheck17111]

def rawRow17112 : Integer.Sparse Key := [(key696, -2), (key694, -2), (key699, -2), (key699, 6), (key696, -2), (key694, -2), (key699, -2), (key696, 2), (key694, 2), (key847, 2), (key846, 2), (key852, 2), (key850, 2), (key699, -2), (key852, -2), (key850, -2), (key699, 6), (key699, -2), (key852, -2), (key850, -2)]

theorem rawRowCheck17112 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form4 = rawRow17112 := by decide +kernel

def row17112 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

theorem rowCheck17112 : row17112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17112 := by decide +kernel

theorem rowEval17112 (x : Key → ℝ) : Integer.Sparse.eval row17112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17112, Integer.Sparse.eval_collectBalanced, rawRowCheck17112]

def rawRow17113 : Integer.Sparse Key := [(key694, -2), (key699, -2), (key696, -2), (key699, 6), (key694, -2), (key699, -2), (key696, -2), (key846, 2), (key850, 2), (key694, 2), (key852, 2), (key696, 2), (key847, 2), (key850, -2), (key699, -2), (key852, -2), (key699, 6), (key850, -2), (key699, -2), (key852, -2)]

theorem rawRowCheck17113 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form4 = rawRow17113 := by decide +kernel

def row17113 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

theorem rowCheck17113 : row17113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17113 := by decide +kernel

theorem rowEval17113 (x : Key → ℝ) : Integer.Sparse.eval row17113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17113, Integer.Sparse.eval_collectBalanced, rawRowCheck17113]

def rawRow17114 : Integer.Sparse Key := [(key699, -2), (key694, -2), (key696, -2), (key699, 6), (key699, -2), (key694, -2), (key696, -2), (key850, 2), (key846, 2), (key852, 2), (key694, 2), (key847, 2), (key696, 2), (key850, -2), (key852, -2), (key699, -2), (key699, 6), (key850, -2), (key852, -2), (key699, -2)]

theorem rawRowCheck17114 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form4 = rawRow17114 := by decide +kernel

def row17114 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

theorem rowCheck17114 : row17114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17114 := by decide +kernel

theorem rowEval17114 (x : Key → ℝ) : Integer.Sparse.eval row17114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17114, Integer.Sparse.eval_collectBalanced, rawRowCheck17114]

def rawRow17115 : Integer.Sparse Key := [(key696, -2), (key699, -2), (key694, -2), (key699, 6), (key696, -2), (key699, -2), (key694, -2), (key847, 2), (key852, 2), (key696, 2), (key850, 2), (key694, 2), (key846, 2), (key852, -2), (key699, -2), (key850, -2), (key699, 6), (key852, -2), (key699, -2), (key850, -2)]

theorem rawRowCheck17115 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form4 = rawRow17115 := by decide +kernel

def row17115 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

theorem rowCheck17115 : row17115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17115 := by decide +kernel

theorem rowEval17115 (x : Key → ℝ) : Integer.Sparse.eval row17115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17115, Integer.Sparse.eval_collectBalanced, rawRowCheck17115]

def rawRow17116 : Integer.Sparse Key := [(key699, -2), (key696, -2), (key694, -2), (key699, 6), (key699, -2), (key696, -2), (key694, -2), (key852, 2), (key847, 2), (key850, 2), (key696, 2), (key846, 2), (key694, 2), (key852, -2), (key850, -2), (key699, -2), (key699, 6), (key852, -2), (key850, -2), (key699, -2)]

theorem rawRowCheck17116 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form4 = rawRow17116 := by decide +kernel

def row17116 : Integer.Sparse Key := [(key694, -2), (key696, -2), (key699, 4), (key846, 2), (key847, 2), (key850, -2), (key852, -2)]

theorem rowCheck17116 : row17116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17116 := by decide +kernel

theorem rowEval17116 (x : Key → ℝ) : Integer.Sparse.eval row17116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17116, Integer.Sparse.eval_collectBalanced, rawRowCheck17116]

def rawRow17117 : Integer.Sparse Key := [(key694, -2), (key699, -2), (key699, -2), (key696, 6), (key846, -2), (key850, -2), (key850, -2), (key694, 2), (key699, 2), (key694, 2), (key852, 2), (key699, 2), (key852, 2), (key696, -2), (key696, -2), (key847, -2), (key850, 6), (key699, -2), (key699, -2), (key852, -2)]

theorem rawRowCheck17117 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form4 = rawRow17117 := by decide +kernel

def row17117 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17117 : row17117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17117 := by decide +kernel

theorem rowEval17117 (x : Key → ℝ) : Integer.Sparse.eval row17117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17117, Integer.Sparse.eval_collectBalanced, rawRowCheck17117]

def rawRow17118 : Integer.Sparse Key := [(key699, -2), (key694, -2), (key699, -2), (key696, 6), (key850, -2), (key846, -2), (key850, -2), (key699, 2), (key694, 2), (key852, 2), (key694, 2), (key852, 2), (key699, 2), (key696, -2), (key847, -2), (key696, -2), (key850, 6), (key699, -2), (key852, -2), (key699, -2)]

theorem rawRowCheck17118 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form4 = rawRow17118 := by decide +kernel

def row17118 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17118 : row17118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17118 := by decide +kernel

theorem rowEval17118 (x : Key → ℝ) : Integer.Sparse.eval row17118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17118, Integer.Sparse.eval_collectBalanced, rawRowCheck17118]

def rawRow17119 : Integer.Sparse Key := [(key699, -2), (key699, -2), (key694, -2), (key696, 6), (key850, -2), (key850, -2), (key846, -2), (key852, 2), (key852, 2), (key699, 2), (key699, 2), (key694, 2), (key694, 2), (key847, -2), (key696, -2), (key696, -2), (key850, 6), (key852, -2), (key699, -2), (key699, -2)]

theorem rawRowCheck17119 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form4 = rawRow17119 := by decide +kernel

def row17119 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17119 : row17119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17119 := by decide +kernel

theorem rowEval17119 (x : Key → ℝ) : Integer.Sparse.eval row17119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17119, Integer.Sparse.eval_collectBalanced, rawRowCheck17119]

def rawRow17120 : Integer.Sparse Key := [(key696, -2), (key699, -2), (key699, -2), (key694, 6), (key847, -2), (key852, -2), (key852, -2), (key696, 2), (key699, 2), (key696, 2), (key850, 2), (key699, 2), (key850, 2), (key694, -2), (key694, -2), (key846, -2), (key852, 6), (key699, -2), (key699, -2), (key850, -2)]

theorem rawRowCheck17120 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form4 = rawRow17120 := by decide +kernel

def row17120 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17120 : row17120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17120 := by decide +kernel

theorem rowEval17120 (x : Key → ℝ) : Integer.Sparse.eval row17120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17120, Integer.Sparse.eval_collectBalanced, rawRowCheck17120]

def rawRow17121 : Integer.Sparse Key := [(key699, -2), (key696, -2), (key699, -2), (key694, 6), (key852, -2), (key847, -2), (key852, -2), (key699, 2), (key696, 2), (key850, 2), (key696, 2), (key850, 2), (key699, 2), (key694, -2), (key846, -2), (key694, -2), (key852, 6), (key699, -2), (key850, -2), (key699, -2)]

theorem rawRowCheck17121 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form4 = rawRow17121 := by decide +kernel

def row17121 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17121 : row17121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17121 := by decide +kernel

theorem rowEval17121 (x : Key → ℝ) : Integer.Sparse.eval row17121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17121, Integer.Sparse.eval_collectBalanced, rawRowCheck17121]

def rawRow17122 : Integer.Sparse Key := [(key699, -2), (key699, -2), (key696, -2), (key694, 6), (key852, -2), (key852, -2), (key847, -2), (key850, 2), (key850, 2), (key699, 2), (key699, 2), (key696, 2), (key696, 2), (key846, -2), (key694, -2), (key694, -2), (key852, 6), (key850, -2), (key699, -2), (key699, -2)]

theorem rawRowCheck17122 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form4 = rawRow17122 := by decide +kernel

def row17122 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17122 : row17122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17122 := by decide +kernel

theorem rowEval17122 (x : Key → ℝ) : Integer.Sparse.eval row17122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17122, Integer.Sparse.eval_collectBalanced, rawRowCheck17122]

def rawRow17123 : Integer.Sparse Key := [(key846, -2), (key850, -2), (key850, -2), (key850, 6), (key694, -2), (key699, -2), (key699, -2), (key694, 2), (key699, 2), (key694, 2), (key852, 2), (key699, 2), (key852, 2), (key699, -2), (key699, -2), (key852, -2), (key696, 6), (key696, -2), (key696, -2), (key847, -2)]

theorem rawRowCheck17123 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form4 = rawRow17123 := by decide +kernel

def row17123 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17123 : row17123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17123 := by decide +kernel

theorem rowEval17123 (x : Key → ℝ) : Integer.Sparse.eval row17123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck17123, Integer.Sparse.eval_collectBalanced, rawRowCheck17123]

def rawRow17124 : Integer.Sparse Key := [(key850, -2), (key846, -2), (key850, -2), (key850, 6), (key699, -2), (key694, -2), (key699, -2), (key699, 2), (key694, 2), (key852, 2), (key694, 2), (key852, 2), (key699, 2), (key699, -2), (key852, -2), (key699, -2), (key696, 6), (key696, -2), (key847, -2), (key696, -2)]

theorem rawRowCheck17124 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form4 = rawRow17124 := by decide +kernel

def row17124 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17124 : row17124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17124 := by decide +kernel

theorem rowEval17124 (x : Key → ℝ) : Integer.Sparse.eval row17124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17124, Integer.Sparse.eval_collectBalanced, rawRowCheck17124]

def rawRow17125 : Integer.Sparse Key := [(key850, -2), (key850, -2), (key846, -2), (key850, 6), (key699, -2), (key699, -2), (key694, -2), (key852, 2), (key852, 2), (key699, 2), (key699, 2), (key694, 2), (key694, 2), (key852, -2), (key699, -2), (key699, -2), (key696, 6), (key847, -2), (key696, -2), (key696, -2)]

theorem rawRowCheck17125 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form4 = rawRow17125 := by decide +kernel

def row17125 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17125 : row17125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17125 := by decide +kernel

theorem rowEval17125 (x : Key → ℝ) : Integer.Sparse.eval row17125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17125, Integer.Sparse.eval_collectBalanced, rawRowCheck17125]

def rawRow17126 : Integer.Sparse Key := [(key850, -2), (key850, -2), (key850, -2), (key846, 6), (key852, -2), (key852, -2), (key852, -2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key694, -2), (key694, -2), (key694, -2), (key847, 6), (key696, -2), (key696, -2), (key696, -2)]

theorem rawRowCheck17126 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form4 = rawRow17126 := by decide +kernel

def row17126 : Integer.Sparse Key := [(key694, -6), (key696, -6), (key699, 12), (key846, 6), (key847, 6), (key850, -6), (key852, -6)]

theorem rowCheck17126 : row17126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17126 := by decide +kernel

theorem rowEval17126 (x : Key → ℝ) : Integer.Sparse.eval row17126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17126, Integer.Sparse.eval_collectBalanced, rawRowCheck17126]

def rawRow17127 : Integer.Sparse Key := [(key847, -2), (key852, -2), (key852, -2), (key852, 6), (key696, -2), (key699, -2), (key699, -2), (key696, 2), (key699, 2), (key696, 2), (key850, 2), (key699, 2), (key850, 2), (key699, -2), (key699, -2), (key850, -2), (key694, 6), (key694, -2), (key694, -2), (key846, -2)]

theorem rawRowCheck17127 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form4 = rawRow17127 := by decide +kernel

def row17127 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17127 : row17127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17127 := by decide +kernel

theorem rowEval17127 (x : Key → ℝ) : Integer.Sparse.eval row17127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17127, Integer.Sparse.eval_collectBalanced, rawRowCheck17127]

def rawRow17128 : Integer.Sparse Key := [(key852, -2), (key847, -2), (key852, -2), (key852, 6), (key699, -2), (key696, -2), (key699, -2), (key699, 2), (key696, 2), (key850, 2), (key696, 2), (key850, 2), (key699, 2), (key699, -2), (key850, -2), (key699, -2), (key694, 6), (key694, -2), (key846, -2), (key694, -2)]

theorem rawRowCheck17128 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form4 = rawRow17128 := by decide +kernel

def row17128 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17128 : row17128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17128 := by decide +kernel

theorem rowEval17128 (x : Key → ℝ) : Integer.Sparse.eval row17128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17128, Integer.Sparse.eval_collectBalanced, rawRowCheck17128]

def rawRow17129 : Integer.Sparse Key := [(key852, -2), (key852, -2), (key847, -2), (key852, 6), (key699, -2), (key699, -2), (key696, -2), (key850, 2), (key850, 2), (key699, 2), (key699, 2), (key696, 2), (key696, 2), (key850, -2), (key699, -2), (key699, -2), (key694, 6), (key846, -2), (key694, -2), (key694, -2)]

theorem rawRowCheck17129 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form4 = rawRow17129 := by decide +kernel

def row17129 : Integer.Sparse Key := [(key694, 2), (key696, 2), (key699, -4), (key846, -2), (key847, -2), (key850, 2), (key852, 2)]

theorem rowCheck17129 : row17129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17129 := by decide +kernel

theorem rowEval17129 (x : Key → ℝ) : Integer.Sparse.eval row17129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17129, Integer.Sparse.eval_collectBalanced, rawRowCheck17129]

def rawRow17130 : Integer.Sparse Key := [(key852, -2), (key852, -2), (key852, -2), (key847, 6), (key850, -2), (key850, -2), (key850, -2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key699, 2), (key696, -2), (key696, -2), (key696, -2), (key846, 6), (key694, -2), (key694, -2), (key694, -2)]

theorem rawRowCheck17130 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form4 = rawRow17130 := by decide +kernel

def row17130 : Integer.Sparse Key := [(key694, -6), (key696, -6), (key699, 12), (key846, 6), (key847, 6), (key850, -6), (key852, -6)]

theorem rowCheck17130 : row17130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17130 := by decide +kernel

theorem rowEval17130 (x : Key → ℝ) : Integer.Sparse.eval row17130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17130, Integer.Sparse.eval_collectBalanced, rawRowCheck17130]

def rawRow17131 : Integer.Sparse Key := [(key695, 4), (key849, 4), (key853, 4), (key698, -2), (key700, -2), (key849, -2), (key853, -2), (key888, -2), (key889, -2), (key698, -2), (key700, -2), (key849, -2), (key853, -2), (key888, -2), (key889, -2), (key712, 4), (key888, 4), (key889, 4)]

theorem rawRowCheck17131 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form5 = rawRow17131 := by decide +kernel

def row17131 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

theorem rowCheck17131 : row17131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17131 := by decide +kernel

theorem rowEval17131 (x : Key → ℝ) : Integer.Sparse.eval row17131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17131, Integer.Sparse.eval_collectBalanced, rawRowCheck17131]

def rawRow17132 : Integer.Sparse Key := [(key695, 4), (key853, 4), (key849, 4), (key700, -2), (key698, -2), (key853, -2), (key849, -2), (key889, -2), (key888, -2), (key700, -2), (key698, -2), (key853, -2), (key849, -2), (key889, -2), (key888, -2), (key712, 4), (key889, 4), (key888, 4)]

theorem rawRowCheck17132 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form5 = rawRow17132 := by decide +kernel

def row17132 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

theorem rowCheck17132 : row17132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17132 := by decide +kernel

theorem rowEval17132 (x : Key → ℝ) : Integer.Sparse.eval row17132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17132, Integer.Sparse.eval_collectBalanced, rawRowCheck17132]

def rawRow17133 : Integer.Sparse Key := [(key849, 4), (key695, 4), (key853, 4), (key849, -2), (key888, -2), (key698, -2), (key889, -2), (key700, -2), (key853, -2), (key849, -2), (key888, -2), (key698, -2), (key889, -2), (key700, -2), (key853, -2), (key888, 4), (key712, 4), (key889, 4)]

theorem rawRowCheck17133 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form5 = rawRow17133 := by decide +kernel

def row17133 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

theorem rowCheck17133 : row17133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17133 := by decide +kernel

theorem rowEval17133 (x : Key → ℝ) : Integer.Sparse.eval row17133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17133, Integer.Sparse.eval_collectBalanced, rawRowCheck17133]

def rawRow17134 : Integer.Sparse Key := [(key849, 4), (key853, 4), (key695, 4), (key888, -2), (key849, -2), (key889, -2), (key698, -2), (key853, -2), (key700, -2), (key888, -2), (key849, -2), (key889, -2), (key698, -2), (key853, -2), (key700, -2), (key888, 4), (key889, 4), (key712, 4)]

theorem rawRowCheck17134 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form5 = rawRow17134 := by decide +kernel

def row17134 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

theorem rowCheck17134 : row17134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17134 := by decide +kernel

theorem rowEval17134 (x : Key → ℝ) : Integer.Sparse.eval row17134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17134, Integer.Sparse.eval_collectBalanced, rawRowCheck17134]

def rawRow17135 : Integer.Sparse Key := [(key853, 4), (key695, 4), (key849, 4), (key853, -2), (key889, -2), (key700, -2), (key888, -2), (key698, -2), (key849, -2), (key853, -2), (key889, -2), (key700, -2), (key888, -2), (key698, -2), (key849, -2), (key889, 4), (key712, 4), (key888, 4)]

theorem rawRowCheck17135 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form5 = rawRow17135 := by decide +kernel

def row17135 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

theorem rowCheck17135 : row17135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17135 := by decide +kernel

theorem rowEval17135 (x : Key → ℝ) : Integer.Sparse.eval row17135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17135, Integer.Sparse.eval_collectBalanced, rawRowCheck17135]

def rawRow17136 : Integer.Sparse Key := [(key853, 4), (key849, 4), (key695, 4), (key889, -2), (key853, -2), (key888, -2), (key700, -2), (key849, -2), (key698, -2), (key889, -2), (key853, -2), (key888, -2), (key700, -2), (key849, -2), (key698, -2), (key889, 4), (key888, 4), (key712, 4)]

theorem rawRowCheck17136 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form5 = rawRow17136 := by decide +kernel

def row17136 : Integer.Sparse Key := [(key695, 4), (key698, -4), (key700, -4), (key712, 4)]

theorem rowCheck17136 : row17136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17136 := by decide +kernel

theorem rowEval17136 (x : Key → ℝ) : Integer.Sparse.eval row17136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17136, Integer.Sparse.eval_collectBalanced, rawRowCheck17136]

def rawRow17137 : Integer.Sparse Key := [(key698, 4), (key698, 4), (key889, 4), (key695, -2), (key700, -2), (key695, -2), (key853, -2), (key700, -2), (key853, -2), (key698, -2), (key712, -2), (key698, -2), (key889, -2), (key712, -2), (key889, -2), (key700, 4), (key700, 4), (key853, 4)]

theorem rawRowCheck17137 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form5 = rawRow17137 := by decide +kernel

def row17137 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17137 : row17137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17137 := by decide +kernel

theorem rowEval17137 (x : Key → ℝ) : Integer.Sparse.eval row17137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17137, Integer.Sparse.eval_collectBalanced, rawRowCheck17137]

def rawRow17138 : Integer.Sparse Key := [(key698, 4), (key889, 4), (key698, 4), (key700, -2), (key695, -2), (key853, -2), (key695, -2), (key853, -2), (key700, -2), (key712, -2), (key698, -2), (key889, -2), (key698, -2), (key889, -2), (key712, -2), (key700, 4), (key853, 4), (key700, 4)]

theorem rawRowCheck17138 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form5 = rawRow17138 := by decide +kernel

def row17138 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17138 : row17138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17138 := by decide +kernel

theorem rowEval17138 (x : Key → ℝ) : Integer.Sparse.eval row17138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17138, Integer.Sparse.eval_collectBalanced, rawRowCheck17138]

def rawRow17139 : Integer.Sparse Key := [(key889, 4), (key698, 4), (key698, 4), (key853, -2), (key853, -2), (key700, -2), (key700, -2), (key695, -2), (key695, -2), (key889, -2), (key889, -2), (key712, -2), (key712, -2), (key698, -2), (key698, -2), (key853, 4), (key700, 4), (key700, 4)]

theorem rawRowCheck17139 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form5 = rawRow17139 := by decide +kernel

def row17139 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17139 : row17139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17139 := by decide +kernel

theorem rowEval17139 (x : Key → ℝ) : Integer.Sparse.eval row17139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17139, Integer.Sparse.eval_collectBalanced, rawRowCheck17139]

def rawRow17140 : Integer.Sparse Key := [(key700, 4), (key700, 4), (key888, 4), (key695, -2), (key698, -2), (key695, -2), (key849, -2), (key698, -2), (key849, -2), (key700, -2), (key712, -2), (key700, -2), (key888, -2), (key712, -2), (key888, -2), (key698, 4), (key698, 4), (key849, 4)]

theorem rawRowCheck17140 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form5 = rawRow17140 := by decide +kernel

def row17140 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17140 : row17140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17140 := by decide +kernel

theorem rowEval17140 (x : Key → ℝ) : Integer.Sparse.eval row17140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17140, Integer.Sparse.eval_collectBalanced, rawRowCheck17140]

def rawRow17141 : Integer.Sparse Key := [(key700, 4), (key888, 4), (key700, 4), (key698, -2), (key695, -2), (key849, -2), (key695, -2), (key849, -2), (key698, -2), (key712, -2), (key700, -2), (key888, -2), (key700, -2), (key888, -2), (key712, -2), (key698, 4), (key849, 4), (key698, 4)]

theorem rawRowCheck17141 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form5 = rawRow17141 := by decide +kernel

def row17141 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17141 : row17141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17141 := by decide +kernel

theorem rowEval17141 (x : Key → ℝ) : Integer.Sparse.eval row17141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17141, Integer.Sparse.eval_collectBalanced, rawRowCheck17141]

def rawRow17142 : Integer.Sparse Key := [(key888, 4), (key700, 4), (key700, 4), (key849, -2), (key849, -2), (key698, -2), (key698, -2), (key695, -2), (key695, -2), (key888, -2), (key888, -2), (key712, -2), (key712, -2), (key700, -2), (key700, -2), (key849, 4), (key698, 4), (key698, 4)]

theorem rawRowCheck17142 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form5 = rawRow17142 := by decide +kernel

def row17142 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17142 : row17142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17142 := by decide +kernel

theorem rowEval17142 (x : Key → ℝ) : Integer.Sparse.eval row17142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17142, Integer.Sparse.eval_collectBalanced, rawRowCheck17142]

def rawRow17143 : Integer.Sparse Key := [(key698, 4), (key698, 4), (key889, 4), (key698, -2), (key712, -2), (key698, -2), (key889, -2), (key712, -2), (key889, -2), (key695, -2), (key700, -2), (key695, -2), (key853, -2), (key700, -2), (key853, -2), (key700, 4), (key700, 4), (key853, 4)]

theorem rawRowCheck17143 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form5 = rawRow17143 := by decide +kernel

def row17143 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17143 : row17143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17143 := by decide +kernel

theorem rowEval17143 (x : Key → ℝ) : Integer.Sparse.eval row17143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck17143, Integer.Sparse.eval_collectBalanced, rawRowCheck17143]

def rawRow17144 : Integer.Sparse Key := [(key698, 4), (key889, 4), (key698, 4), (key712, -2), (key698, -2), (key889, -2), (key698, -2), (key889, -2), (key712, -2), (key700, -2), (key695, -2), (key853, -2), (key695, -2), (key853, -2), (key700, -2), (key700, 4), (key853, 4), (key700, 4)]

theorem rawRowCheck17144 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form5 = rawRow17144 := by decide +kernel

def row17144 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17144 : row17144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17144 := by decide +kernel

theorem rowEval17144 (x : Key → ℝ) : Integer.Sparse.eval row17144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17144, Integer.Sparse.eval_collectBalanced, rawRowCheck17144]

def rawRow17145 : Integer.Sparse Key := [(key889, 4), (key698, 4), (key698, 4), (key889, -2), (key889, -2), (key712, -2), (key712, -2), (key698, -2), (key698, -2), (key853, -2), (key853, -2), (key700, -2), (key700, -2), (key695, -2), (key695, -2), (key853, 4), (key700, 4), (key700, 4)]

theorem rawRowCheck17145 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form5 = rawRow17145 := by decide +kernel

def row17145 : Integer.Sparse Key := [(key695, -4), (key698, 4), (key700, 4), (key712, -4)]

theorem rowCheck17145 : row17145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17145 := by decide +kernel

theorem rowEval17145 (x : Key → ℝ) : Integer.Sparse.eval row17145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17145, Integer.Sparse.eval_collectBalanced, rawRowCheck17145]

def rawRow17146 : Integer.Sparse Key := [(key82, 4), (key82, 4), (key82, 4), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key700, -2), (key695, 4), (key695, 4), (key695, 4)]

theorem rawRowCheck17146 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form5 = rawRow17146 := by decide +kernel

def row17146 : Integer.Sparse Key := [(key65, -12), (key82, 12), (key695, 12), (key700, -12)]

theorem rowCheck17146 : row17146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17146 := by decide +kernel

theorem rowEval17146 (x : Key → ℝ) : Integer.Sparse.eval row17146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17146, Integer.Sparse.eval_collectBalanced, rawRowCheck17146]

def rawRow17147 : Integer.Sparse Key := [(key68, 4), (key68, 4), (key145, 4), (key68, -2), (key82, -2), (key68, -2), (key145, -2), (key82, -2), (key145, -2), (key58, -2), (key65, -2), (key58, -2), (key130, -2), (key65, -2), (key130, -2), (key65, 4), (key65, 4), (key130, 4)]

theorem rawRowCheck17147 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form5 = rawRow17147 := by decide +kernel

def row17147 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

theorem rowCheck17147 : row17147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17147 := by decide +kernel

theorem rowEval17147 (x : Key → ℝ) : Integer.Sparse.eval row17147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17147, Integer.Sparse.eval_collectBalanced, rawRowCheck17147]

def rawRow17148 : Integer.Sparse Key := [(key68, 4), (key145, 4), (key68, 4), (key82, -2), (key68, -2), (key145, -2), (key68, -2), (key145, -2), (key82, -2), (key65, -2), (key58, -2), (key130, -2), (key58, -2), (key130, -2), (key65, -2), (key65, 4), (key130, 4), (key65, 4)]

theorem rawRowCheck17148 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form5 = rawRow17148 := by decide +kernel

def row17148 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

theorem rowCheck17148 : row17148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17148 := by decide +kernel

theorem rowEval17148 (x : Key → ℝ) : Integer.Sparse.eval row17148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17148, Integer.Sparse.eval_collectBalanced, rawRowCheck17148]

def rawRow17149 : Integer.Sparse Key := [(key145, 4), (key68, 4), (key68, 4), (key145, -2), (key145, -2), (key82, -2), (key82, -2), (key68, -2), (key68, -2), (key130, -2), (key130, -2), (key65, -2), (key65, -2), (key58, -2), (key58, -2), (key130, 4), (key65, 4), (key65, 4)]

theorem rawRowCheck17149 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form5 = rawRow17149 := by decide +kernel

def row17149 : Integer.Sparse Key := [(key58, -4), (key65, 4), (key68, 4), (key82, -4)]

theorem rowCheck17149 : row17149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17149 := by decide +kernel

theorem rowEval17149 (x : Key → ℝ) : Integer.Sparse.eval row17149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17149, Integer.Sparse.eval_collectBalanced, rawRowCheck17149]

def rawRow17150 : Integer.Sparse Key := [(key82, 4), (key82, 4), (key82, 4), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key68, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key65, -2), (key58, 4), (key58, 4), (key58, 4)]

theorem rawRowCheck17150 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form5 = rawRow17150 := by decide +kernel

def row17150 : Integer.Sparse Key := [(key58, 12), (key65, -12), (key68, -12), (key82, 12)]

theorem rowCheck17150 : row17150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17150 := by decide +kernel

theorem rowEval17150 (x : Key → ℝ) : Integer.Sparse.eval row17150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17150, Integer.Sparse.eval_collectBalanced, rawRowCheck17150]

def rawRow17151 : Integer.Sparse Key := [(key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2026, 2), (key2144, 2), (key2145, 2), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2042, 2), (key2047, 2), (key2127, 2), (key2134, 2), (key2228, 2), (key2229, 2), (key2055, -1), (key2056, -1), (key2144, -1), (key2145, -1), (key2228, -1), (key2229, -1), (key2026, 2), (key2144, 2), (key2145, 2), (key2055, -1), (key2056, -1), (key2144, -1), (key2145, -1), (key2228, -1), (key2229, -1)]

theorem rawRowCheck17151 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form6 = rawRow17151 := by decide +kernel

def row17151 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

theorem rowCheck17151 : row17151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17151 := by decide +kernel

theorem rowEval17151 (x : Key → ℝ) : Integer.Sparse.eval row17151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck17151, Integer.Sparse.eval_collectBalanced, rawRowCheck17151]

end MUB6.Certificate.GramRows

end OAI
