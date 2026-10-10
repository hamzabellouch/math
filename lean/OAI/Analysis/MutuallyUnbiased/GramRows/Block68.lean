import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
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

def rawRow5632 : Integer.Sparse Key := [(key2365, -4), (key2367, 2), (key2365, 2), (key2365, 2), (key2362, 2), (key2365, -4), (key2521, 2), (key2525, -1), (key2521, -1), (key2460, 2), (key2525, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, 2), (key2460, 2), (key2564, -1), (key2562, -1), (key2564, 2), (key2533, -1), (key2532, -1), (key2564, 2), (key2532, 2), (key2564, -1), (key2533, -1), (key2532, 2), (key2562, -1), (key2532, -1)]

theorem rawRowCheck5632 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow5632 := by decide +kernel

def row5632 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5632 : row5632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5632 := by decide +kernel

theorem rowEval5632 (x : Key → ℝ) : Integer.Sparse.eval row5632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5632, Integer.Sparse.eval_collectBalanced, rawRowCheck5632]

def rawRow5633 : Integer.Sparse Key := [(key2367, -4), (key2365, 2), (key2365, 2), (key2365, 2), (key2365, 2), (key2362, -4), (key2525, 2), (key2521, -1), (key2521, -1), (key2525, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, 2), (key2457, 2), (key2564, -1), (key2564, -1), (key2562, 2), (key2564, -1), (key2564, -1), (key2533, 2), (key2533, 2), (key2532, -1), (key2532, -1), (key2562, 2), (key2532, -1), (key2532, -1)]

theorem rawRowCheck5633 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow5633 := by decide +kernel

def row5633 : Integer.Sparse Key := [(key2362, -4), (key2365, 8), (key2367, -4), (key2457, 4), (key2460, -4), (key2521, -4), (key2525, 4), (key2532, -4), (key2533, 4), (key2562, 4), (key2564, -4)]

theorem rowCheck5633 : row5633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5633 := by decide +kernel

theorem rowEval5633 (x : Key → ℝ) : Integer.Sparse.eval row5633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5633, Integer.Sparse.eval_collectBalanced, rawRowCheck5633]

def rawRow5634 : Integer.Sparse Key := [(key2457, -4), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2525, -4), (key2362, 2), (key2365, -1), (key2365, -1), (key2457, 2), (key2521, -1), (key2521, -1), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, 2), (key2564, 2), (key2365, -1), (key2365, -1), (key2367, 2), (key2460, -1), (key2460, -1), (key2521, 2), (key2521, 2), (key2525, -1), (key2525, -1), (key2533, 2), (key2564, -1), (key2564, -1)]

theorem rawRowCheck5634 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form4 = rawRow5634 := by decide +kernel

def row5634 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

theorem rowCheck5634 : row5634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5634 := by decide +kernel

theorem rowEval5634 (x : Key → ℝ) : Integer.Sparse.eval row5634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5634, Integer.Sparse.eval_collectBalanced, rawRowCheck5634]

def rawRow5635 : Integer.Sparse Key := [(key2460, -4), (key2457, 2), (key2460, 2), (key2521, 2), (key2525, 2), (key2521, -4), (key2365, 2), (key2362, -1), (key2365, -1), (key2521, 2), (key2457, -1), (key2521, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, 2), (key2562, 2), (key2365, -1), (key2367, -1), (key2365, 2), (key2521, -1), (key2525, -1), (key2460, 2), (key2525, 2), (key2460, -1), (key2521, -1), (key2564, 2), (key2533, -1), (key2564, -1)]

theorem rawRowCheck5635 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form4 = rawRow5635 := by decide +kernel

def row5635 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -3), (key2525, 3), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5635 : row5635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5635 := by decide +kernel

theorem rowEval5635 (x : Key → ℝ) : Integer.Sparse.eval row5635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5635, Integer.Sparse.eval_collectBalanced, rawRowCheck5635]

def rawRow5636 : Integer.Sparse Key := [(key2460, -4), (key2460, 2), (key2457, 2), (key2525, 2), (key2521, 2), (key2521, -4), (key2365, 2), (key2365, -1), (key2362, -1), (key2521, 2), (key2521, -1), (key2457, -1), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, 2), (key2532, 2), (key2367, -1), (key2365, -1), (key2365, 2), (key2525, -1), (key2521, -1), (key2525, 2), (key2460, 2), (key2521, -1), (key2460, -1), (key2564, 2), (key2564, -1), (key2533, -1)]

theorem rawRowCheck5636 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form4 = rawRow5636 := by decide +kernel

def row5636 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -3), (key2525, 3), (key2532, 1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5636 : row5636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5636 := by decide +kernel

theorem rowEval5636 (x : Key → ℝ) : Integer.Sparse.eval row5636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5636, Integer.Sparse.eval_collectBalanced, rawRowCheck5636]

def rawRow5637 : Integer.Sparse Key := [(key2457, -4), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2525, -4), (key2457, 2), (key2521, -1), (key2521, -1), (key2362, 2), (key2562, -1), (key2562, -1), (key2365, -1), (key2365, -1), (key2521, -1), (key2521, -1), (key2564, 2), (key2564, 2), (key2460, -1), (key2460, -1), (key2533, 2), (key2365, -1), (key2365, -1), (key2521, 2), (key2521, 2), (key2564, -1), (key2564, -1), (key2367, 2), (key2525, -1), (key2525, -1)]

theorem rawRowCheck5637 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form4 = rawRow5637 := by decide +kernel

def row5637 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -6), (key2533, 2), (key2562, -2), (key2564, 2)]

theorem rowCheck5637 : row5637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5637 := by decide +kernel

theorem rowEval5637 (x : Key → ℝ) : Integer.Sparse.eval row5637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5637, Integer.Sparse.eval_collectBalanced, rawRowCheck5637]

def rawRow5638 : Integer.Sparse Key := [(key2521, -4), (key2457, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -4), (key2521, 2), (key2457, -1), (key2521, -1), (key2562, 2), (key2362, -1), (key2562, -1), (key2521, -1), (key2564, -1), (key2365, -1), (key2564, -1), (key2365, 2), (key2521, 2), (key2460, -1), (key2533, -1), (key2460, 2), (key2521, -1), (key2564, -1), (key2365, 2), (key2564, 2), (key2365, -1), (key2521, -1), (key2525, 2), (key2367, -1), (key2525, -1)]

theorem rawRowCheck5638 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form4 = rawRow5638 := by decide +kernel

def row5638 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -2), (key2525, 3), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5638 : row5638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5638 := by decide +kernel

theorem rowEval5638 (x : Key → ℝ) : Integer.Sparse.eval row5638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5638, Integer.Sparse.eval_collectBalanced, rawRowCheck5638]

def rawRow5639 : Integer.Sparse Key := [(key2521, -4), (key2521, 2), (key2457, 2), (key2525, 2), (key2460, 2), (key2460, -4), (key2521, 2), (key2521, -1), (key2457, -1), (key2562, 2), (key2562, -1), (key2362, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2365, -1), (key2521, 2), (key2365, 2), (key2533, -1), (key2460, -1), (key2460, 2), (key2564, -1), (key2521, -1), (key2564, 2), (key2365, 2), (key2521, -1), (key2365, -1), (key2525, 2), (key2525, -1), (key2367, -1)]

theorem rawRowCheck5639 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form4 = rawRow5639 := by decide +kernel

def row5639 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -2), (key2525, 3), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5639 : row5639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5639 := by decide +kernel

theorem rowEval5639 (x : Key → ℝ) : Integer.Sparse.eval row5639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5639, Integer.Sparse.eval_collectBalanced, rawRowCheck5639]

def rawRow5640 : Integer.Sparse Key := [(key2460, -4), (key2521, 2), (key2525, 2), (key2457, 2), (key2460, 2), (key2521, -4), (key2532, 2), (key2562, -1), (key2564, -1), (key2365, 2), (key2521, -1), (key2564, -1), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, 2), (key2562, 2), (key2521, -1), (key2525, -1), (key2564, 2), (key2365, -1), (key2367, -1), (key2460, 2), (key2525, 2), (key2533, -1), (key2564, -1), (key2365, 2), (key2460, -1), (key2521, -1)]

theorem rawRowCheck5640 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form4 = rawRow5640 := by decide +kernel

def row5640 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -6), (key2525, 3), (key2532, 4), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5640 : row5640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5640 := by decide +kernel

theorem rowEval5640 (x : Key → ℝ) : Integer.Sparse.eval row5640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5640, Integer.Sparse.eval_collectBalanced, rawRowCheck5640]

def rawRow5641 : Integer.Sparse Key := [(key2460, -4), (key2525, 2), (key2521, 2), (key2460, 2), (key2457, 2), (key2521, -4), (key2532, 2), (key2564, -1), (key2562, -1), (key2365, 2), (key2564, -1), (key2521, -1), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, 2), (key2532, 2), (key2525, -1), (key2521, -1), (key2564, 2), (key2367, -1), (key2365, -1), (key2525, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2365, 2), (key2521, -1), (key2460, -1)]

theorem rawRowCheck5641 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form4 = rawRow5641 := by decide +kernel

def row5641 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -6), (key2525, 3), (key2532, 4), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5641 : row5641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5641 := by decide +kernel

theorem rowEval5641 (x : Key → ℝ) : Integer.Sparse.eval row5641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5641, Integer.Sparse.eval_collectBalanced, rawRowCheck5641]

def rawRow5642 : Integer.Sparse Key := [(key2521, -4), (key2460, 2), (key2525, 2), (key2457, 2), (key2521, 2), (key2460, -4), (key2562, 2), (key2532, -1), (key2564, -1), (key2521, 2), (key2365, -1), (key2564, -1), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, 2), (key2521, 2), (key2521, -1), (key2564, -1), (key2525, 2), (key2460, -1), (key2533, -1), (key2365, 2), (key2564, 2), (key2367, -1), (key2525, -1), (key2460, 2), (key2365, -1), (key2521, -1)]

theorem rawRowCheck5642 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form4 = rawRow5642 := by decide +kernel

def row5642 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 3), (key2532, -1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5642 : row5642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5642 := by decide +kernel

theorem rowEval5642 (x : Key → ℝ) : Integer.Sparse.eval row5642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5642, Integer.Sparse.eval_collectBalanced, rawRowCheck5642]

def rawRow5643 : Integer.Sparse Key := [(key2521, -4), (key2525, 2), (key2460, 2), (key2521, 2), (key2457, 2), (key2460, -4), (key2562, 2), (key2564, -1), (key2532, -1), (key2521, 2), (key2564, -1), (key2365, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, 2), (key2365, 2), (key2564, -1), (key2521, -1), (key2525, 2), (key2533, -1), (key2460, -1), (key2564, 2), (key2365, 2), (key2525, -1), (key2367, -1), (key2460, 2), (key2521, -1), (key2365, -1)]

theorem rawRowCheck5643 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form4 = rawRow5643 := by decide +kernel

def row5643 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 3), (key2532, -1), (key2533, -1), (key2562, 1), (key2564, -1)]

theorem rowCheck5643 : row5643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5643 := by decide +kernel

theorem rowEval5643 (x : Key → ℝ) : Integer.Sparse.eval row5643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5643, Integer.Sparse.eval_collectBalanced, rawRowCheck5643]

def rawRow5644 : Integer.Sparse Key := [(key2525, -4), (key2460, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2457, -4), (key2564, 2), (key2532, -1), (key2562, -1), (key2564, 2), (key2365, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, 2), (key2457, 2), (key2525, -1), (key2564, -1), (key2521, 2), (key2525, -1), (key2564, -1), (key2367, 2), (key2533, 2), (key2365, -1), (key2460, -1), (key2521, 2), (key2365, -1), (key2460, -1)]

theorem rawRowCheck5644 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form4 = rawRow5644 := by decide +kernel

def row5644 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

theorem rowCheck5644 : row5644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5644 := by decide +kernel

theorem rowEval5644 (x : Key → ℝ) : Integer.Sparse.eval row5644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5644, Integer.Sparse.eval_collectBalanced, rawRowCheck5644]

def rawRow5645 : Integer.Sparse Key := [(key2525, -4), (key2521, 2), (key2460, 2), (key2521, 2), (key2460, 2), (key2457, -4), (key2564, 2), (key2562, -1), (key2532, -1), (key2564, 2), (key2521, -1), (key2365, -1), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, 2), (key2362, 2), (key2564, -1), (key2525, -1), (key2521, 2), (key2564, -1), (key2525, -1), (key2533, 2), (key2367, 2), (key2460, -1), (key2365, -1), (key2521, 2), (key2460, -1), (key2365, -1)]

theorem rawRowCheck5645 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form4 = rawRow5645 := by decide +kernel

def row5645 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -6), (key2532, -2), (key2533, 2), (key2562, -2), (key2564, 2)]

theorem rowCheck5645 : row5645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5645 := by decide +kernel

theorem rowEval5645 (x : Key → ℝ) : Integer.Sparse.eval row5645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5645, Integer.Sparse.eval_collectBalanced, rawRowCheck5645]

def rawRow5646 : Integer.Sparse Key := [(key2532, -4), (key2532, 2), (key2533, 2), (key2562, 2), (key2564, 2), (key2564, -4), (key2365, 2), (key2365, -1), (key2367, -1), (key2460, 2), (key2460, -1), (key2533, -1), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2365, 2), (key2457, -1), (key2460, -1), (key2457, 2), (key2521, 2), (key2460, -1), (key2521, -1), (key2532, 2), (key2532, -1), (key2562, -1)]

theorem rawRowCheck5646 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form4 = rawRow5646 := by decide +kernel

def row5646 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5646 : row5646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5646 := by decide +kernel

theorem rowEval5646 (x : Key → ℝ) : Integer.Sparse.eval row5646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5646, Integer.Sparse.eval_collectBalanced, rawRowCheck5646]

def rawRow5647 : Integer.Sparse Key := [(key2532, -4), (key2533, 2), (key2532, 2), (key2564, 2), (key2562, 2), (key2564, -4), (key2365, 2), (key2367, -1), (key2365, -1), (key2460, 2), (key2533, -1), (key2460, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, 2), (key2525, 2), (key2365, -1), (key2362, -1), (key2365, 2), (key2460, -1), (key2457, -1), (key2521, 2), (key2457, 2), (key2521, -1), (key2460, -1), (key2532, 2), (key2562, -1), (key2532, -1)]

theorem rawRowCheck5647 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form4 = rawRow5647 := by decide +kernel

def row5647 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5647 : row5647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5647 := by decide +kernel

theorem rowEval5647 (x : Key → ℝ) : Integer.Sparse.eval row5647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5647, Integer.Sparse.eval_collectBalanced, rawRowCheck5647]

def rawRow5648 : Integer.Sparse Key := [(key2533, -4), (key2532, 2), (key2532, 2), (key2564, 2), (key2564, 2), (key2562, -4), (key2367, 2), (key2365, -1), (key2365, -1), (key2533, 2), (key2460, -1), (key2460, -1), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, 2), (key2521, 2), (key2365, -1), (key2365, -1), (key2362, 2), (key2521, -1), (key2521, -1), (key2460, 2), (key2460, 2), (key2457, -1), (key2457, -1), (key2562, 2), (key2532, -1), (key2532, -1)]

theorem rawRowCheck5648 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form4 = rawRow5648 := by decide +kernel

def row5648 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5648 : row5648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5648 := by decide +kernel

theorem rowEval5648 (x : Key → ℝ) : Integer.Sparse.eval row5648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5648, Integer.Sparse.eval_collectBalanced, rawRowCheck5648]

def rawRow5649 : Integer.Sparse Key := [(key2532, -4), (key2562, 2), (key2564, 2), (key2532, 2), (key2533, 2), (key2564, -4), (key2460, 2), (key2521, -1), (key2525, -1), (key2365, 2), (key2521, -1), (key2564, -1), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, 2), (key2564, 2), (key2457, -1), (key2460, -1), (key2521, 2), (key2362, -1), (key2365, -1), (key2457, 2), (key2521, 2), (key2532, -1), (key2562, -1), (key2365, 2), (key2460, -1), (key2521, -1)]

theorem rawRowCheck5649 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form4 = rawRow5649 := by decide +kernel

def row5649 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5649 : row5649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5649 := by decide +kernel

theorem rowEval5649 (x : Key → ℝ) : Integer.Sparse.eval row5649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5649, Integer.Sparse.eval_collectBalanced, rawRowCheck5649]

def rawRow5650 : Integer.Sparse Key := [(key2532, -4), (key2564, 2), (key2562, 2), (key2533, 2), (key2532, 2), (key2564, -4), (key2460, 2), (key2525, -1), (key2521, -1), (key2365, 2), (key2564, -1), (key2521, -1), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, 2), (key2525, 2), (key2460, -1), (key2457, -1), (key2521, 2), (key2365, -1), (key2362, -1), (key2521, 2), (key2457, 2), (key2562, -1), (key2532, -1), (key2365, 2), (key2521, -1), (key2460, -1)]

theorem rawRowCheck5650 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form4 = rawRow5650 := by decide +kernel

def row5650 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5650 : row5650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5650 := by decide +kernel

theorem rowEval5650 (x : Key → ℝ) : Integer.Sparse.eval row5650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5650, Integer.Sparse.eval_collectBalanced, rawRowCheck5650]

def rawRow5651 : Integer.Sparse Key := [(key2562, -4), (key2532, 2), (key2564, 2), (key2532, 2), (key2564, 2), (key2533, -4), (key2521, 2), (key2460, -1), (key2525, -1), (key2521, 2), (key2365, -1), (key2564, -1), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, 2), (key2533, 2), (key2457, -1), (key2521, -1), (key2460, 2), (key2457, -1), (key2521, -1), (key2362, 2), (key2562, 2), (key2365, -1), (key2521, -1), (key2460, 2), (key2365, -1), (key2521, -1)]

theorem rawRowCheck5651 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form4 = rawRow5651 := by decide +kernel

def row5651 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2525, -2), (key2532, 4), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5651 : row5651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5651 := by decide +kernel

theorem rowEval5651 (x : Key → ℝ) : Integer.Sparse.eval row5651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck5651, Integer.Sparse.eval_collectBalanced, rawRowCheck5651]

def rawRow5652 : Integer.Sparse Key := [(key2562, -4), (key2564, 2), (key2532, 2), (key2564, 2), (key2532, 2), (key2533, -4), (key2521, 2), (key2525, -1), (key2460, -1), (key2521, 2), (key2564, -1), (key2365, -1), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, 2), (key2367, 2), (key2521, -1), (key2457, -1), (key2460, 2), (key2521, -1), (key2457, -1), (key2562, 2), (key2362, 2), (key2521, -1), (key2365, -1), (key2460, 2), (key2521, -1), (key2365, -1)]

theorem rawRowCheck5652 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form4 = rawRow5652 := by decide +kernel

def row5652 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2525, -2), (key2532, 4), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5652 : row5652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5652 := by decide +kernel

theorem rowEval5652 (x : Key → ℝ) : Integer.Sparse.eval row5652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5652, Integer.Sparse.eval_collectBalanced, rawRowCheck5652]

def rawRow5653 : Integer.Sparse Key := [(key2564, -4), (key2532, 2), (key2562, 2), (key2533, 2), (key2564, 2), (key2532, -4), (key2525, 2), (key2460, -1), (key2521, -1), (key2564, 2), (key2365, -1), (key2521, -1), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, 2), (key2460, 2), (key2460, -1), (key2521, -1), (key2457, 2), (key2532, -1), (key2562, -1), (key2365, 2), (key2521, 2), (key2362, -1), (key2457, -1), (key2521, 2), (key2365, -1), (key2460, -1)]

theorem rawRowCheck5653 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form4 = rawRow5653 := by decide +kernel

def row5653 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5653 : row5653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5653 := by decide +kernel

theorem rowEval5653 (x : Key → ℝ) : Integer.Sparse.eval row5653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5653, Integer.Sparse.eval_collectBalanced, rawRowCheck5653]

def rawRow5654 : Integer.Sparse Key := [(key2564, -4), (key2562, 2), (key2532, 2), (key2564, 2), (key2533, 2), (key2532, -4), (key2525, 2), (key2521, -1), (key2460, -1), (key2564, 2), (key2521, -1), (key2365, -1), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, 2), (key2365, 2), (key2521, -1), (key2460, -1), (key2457, 2), (key2562, -1), (key2532, -1), (key2521, 2), (key2365, 2), (key2457, -1), (key2362, -1), (key2521, 2), (key2460, -1), (key2365, -1)]

theorem rawRowCheck5654 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form4 = rawRow5654 := by decide +kernel

def row5654 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, 1), (key2525, 1), (key2532, -3), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5654 : row5654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5654 := by decide +kernel

theorem rowEval5654 (x : Key → ℝ) : Integer.Sparse.eval row5654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5654, Integer.Sparse.eval_collectBalanced, rawRowCheck5654]

def rawRow5655 : Integer.Sparse Key := [(key2533, -4), (key2564, 2), (key2564, 2), (key2532, 2), (key2532, 2), (key2562, -4), (key2533, 2), (key2564, -1), (key2564, -1), (key2367, 2), (key2525, -1), (key2525, -1), (key2365, -1), (key2365, -1), (key2460, -1), (key2460, -1), (key2521, 2), (key2521, 2), (key2532, -1), (key2532, -1), (key2562, 2), (key2365, -1), (key2365, -1), (key2460, 2), (key2460, 2), (key2521, -1), (key2521, -1), (key2362, 2), (key2457, -1), (key2457, -1)]

theorem rawRowCheck5655 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form4 = rawRow5655 := by decide +kernel

def row5655 : Integer.Sparse Key := [(key2362, 2), (key2365, -4), (key2367, 2), (key2457, -2), (key2460, 2), (key2521, 2), (key2525, -2), (key2532, 2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck5655 : row5655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5655 := by decide +kernel

theorem rowEval5655 (x : Key → ℝ) : Integer.Sparse.eval row5655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5655, Integer.Sparse.eval_collectBalanced, rawRowCheck5655]

def rawRow5656 : Integer.Sparse Key := [(key2564, -4), (key2533, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -4), (key2564, 2), (key2533, -1), (key2564, -1), (key2525, 2), (key2367, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2521, -1), (key2365, 2), (key2460, 2), (key2532, -1), (key2562, -1), (key2532, 2), (key2460, -1), (key2521, -1), (key2365, 2), (key2521, 2), (key2365, -1), (key2460, -1), (key2457, 2), (key2362, -1), (key2457, -1)]

theorem rawRowCheck5656 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form4 = rawRow5656 := by decide +kernel

def row5656 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5656 : row5656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5656 := by decide +kernel

theorem rowEval5656 (x : Key → ℝ) : Integer.Sparse.eval row5656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck5656, Integer.Sparse.eval_collectBalanced, rawRowCheck5656]

def rawRow5657 : Integer.Sparse Key := [(key2564, -4), (key2564, 2), (key2533, 2), (key2562, 2), (key2532, 2), (key2532, -4), (key2564, 2), (key2564, -1), (key2533, -1), (key2525, 2), (key2525, -1), (key2367, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2365, -1), (key2460, 2), (key2365, 2), (key2562, -1), (key2532, -1), (key2532, 2), (key2521, -1), (key2460, -1), (key2521, 2), (key2365, 2), (key2460, -1), (key2365, -1), (key2457, 2), (key2457, -1), (key2362, -1)]

theorem rawRowCheck5657 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form4 = rawRow5657 := by decide +kernel

def row5657 : Integer.Sparse Key := [(key2362, -1), (key2365, 2), (key2367, -1), (key2457, 1), (key2460, -1), (key2521, -1), (key2525, 1), (key2532, -1), (key2533, 1), (key2562, 1), (key2564, -1)]

theorem rowCheck5657 : row5657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5657 := by decide +kernel

theorem rowEval5657 (x : Key → ℝ) : Integer.Sparse.eval row5657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form4) x := by
  rw [rowCheck5657, Integer.Sparse.eval_collectBalanced, rawRowCheck5657]

def rawRow5658 : Integer.Sparse Key := [(key2667, -1), (key2667, -1), (key2673, 2), (key2702, -1), (key2702, -1), (key2735, 2), (key2735, 2), (key2737, -1), (key2737, -1), (key2728, 2), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2621, -2), (key2809, 1), (key2809, 1), (key2829, -2), (key2829, -2), (key2835, 1), (key2835, 1), (key3012, -2), (key3017, 1), (key3017, 1), (key2640, -1), (key2640, -1), (key2644, 1), (key2644, 1), (key2726, 1), (key2726, 1), (key2732, -1), (key2732, -1), (key2860, -1), (key2860, -1), (key2870, 1), (key2870, 1), (key3023, 1), (key3023, 1), (key3026, -1), (key3026, -1)]

theorem rawRowCheck5658 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form0 = rawRow5658 := by decide +kernel

def row5658 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2809, 2), (key2829, -4), (key2835, 2), (key2860, -2), (key2870, 2), (key3012, -2), (key3017, 2), (key3023, 2), (key3026, -2)]

theorem rowCheck5658 : row5658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5658 := by decide +kernel

theorem rowEval5658 (x : Key → ℝ) : Integer.Sparse.eval row5658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5658, Integer.Sparse.eval_collectBalanced, rawRowCheck5658]

def rawRow5659 : Integer.Sparse Key := [(key2667, -1), (key2673, -1), (key2667, 2), (key2735, -1), (key2737, -1), (key2702, 2), (key2737, 2), (key2702, -1), (key2735, -1), (key2747, 2), (key2728, -1), (key2747, -1), (key2612, 1), (key2618, 1), (key2616, -2), (key2829, 1), (key2835, 1), (key2809, -2), (key2835, -2), (key2809, 1), (key2829, 1), (key3017, -2), (key3012, 1), (key3017, 1), (key2632, -1), (key2644, -1), (key2632, 1), (key2640, 1), (key2706, 1), (key2732, 1), (key2706, -1), (key2726, -1), (key2870, -1), (key2885, -1), (key2860, 1), (key2885, 1), (key3026, 1), (key3030, 1), (key3023, -1), (key3030, -1)]

theorem rawRowCheck5659 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form0 = rawRow5659 := by decide +kernel

def row5659 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2860, 1), (key2870, -1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5659 : row5659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5659 := by decide +kernel

theorem rowEval5659 (x : Key → ℝ) : Integer.Sparse.eval row5659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5659, Integer.Sparse.eval_collectBalanced, rawRowCheck5659]

def rawRow5660 : Integer.Sparse Key := [(key2673, -1), (key2667, -1), (key2667, 2), (key2737, -1), (key2735, -1), (key2737, 2), (key2702, 2), (key2735, -1), (key2702, -1), (key2747, 2), (key2747, -1), (key2728, -1), (key2618, 1), (key2612, 1), (key2616, -2), (key2835, 1), (key2829, 1), (key2835, -2), (key2809, -2), (key2829, 1), (key2809, 1), (key3017, -2), (key3017, 1), (key3012, 1), (key2644, -1), (key2632, -1), (key2640, 1), (key2632, 1), (key2732, 1), (key2706, 1), (key2726, -1), (key2706, -1), (key2885, -1), (key2870, -1), (key2885, 1), (key2860, 1), (key3030, 1), (key3026, 1), (key3030, -1), (key3023, -1)]

theorem rawRowCheck5660 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form0 = rawRow5660 := by decide +kernel

def row5660 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2860, 1), (key2870, -1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5660 : row5660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5660 := by decide +kernel

theorem rowEval5660 (x : Key → ℝ) : Integer.Sparse.eval row5660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5660, Integer.Sparse.eval_collectBalanced, rawRowCheck5660]

def rawRow5661 : Integer.Sparse Key := [(key2702, -1), (key2702, -1), (key2728, 2), (key2667, -1), (key2667, -1), (key2735, 2), (key2735, 2), (key2747, -1), (key2747, -1), (key2673, 2), (key2737, -1), (key2737, -1), (key2805, 1), (key2805, 1), (key2831, -2), (key2612, 1), (key2616, 1), (key2829, -2), (key2829, -2), (key3017, 1), (key3017, 1), (key2621, -2), (key2835, 1), (key2835, 1), (key2860, -1), (key2860, -1), (key3023, 1), (key3023, 1), (key2870, 1), (key2870, 1), (key3026, -1), (key3026, -1), (key2640, -1), (key2640, -1), (key2726, 1), (key2726, 1), (key2644, 1), (key2644, 1), (key2732, -1), (key2732, -1)]

theorem rawRowCheck5661 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form0 = rawRow5661 := by decide +kernel

def row5661 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 2), (key2829, -4), (key2831, -2), (key2835, 2), (key2860, -2), (key2870, 2), (key3017, 2), (key3023, 2), (key3026, -2)]

theorem rowCheck5661 : row5661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5661 := by decide +kernel

theorem rowEval5661 (x : Key → ℝ) : Integer.Sparse.eval row5661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5661, Integer.Sparse.eval_collectBalanced, rawRowCheck5661]

def rawRow5662 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2702, 2), (key2735, -1), (key2747, -1), (key2667, 2), (key2747, 2), (key2667, -1), (key2735, -1), (key2737, 2), (key2673, -1), (key2737, -1), (key2805, 1), (key2831, 1), (key2805, -2), (key2948, 1), (key2960, 1), (key2612, -2), (key2960, -2), (key2616, 1), (key2829, 1), (key2835, -2), (key2621, 1), (key2835, 1), (key2706, -1), (key3023, -1), (key2706, 1), (key2860, 1), (key2632, 1), (key3026, 1), (key2632, -1), (key2870, -1), (key2726, -1), (key3030, -1), (key2640, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2644, -1), (key2885, -1)]

theorem rawRowCheck5662 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form0 = rawRow5662 := by decide +kernel

def row5662 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2621, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2829, 1), (key2831, 1), (key2835, -1), (key2860, 1), (key2870, -1), (key2948, 1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5662 : row5662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5662 := by decide +kernel

theorem rowEval5662 (x : Key → ℝ) : Integer.Sparse.eval row5662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5662, Integer.Sparse.eval_collectBalanced, rawRowCheck5662]

def rawRow5663 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2702, 2), (key2747, -1), (key2735, -1), (key2747, 2), (key2667, 2), (key2735, -1), (key2667, -1), (key2737, 2), (key2737, -1), (key2673, -1), (key2831, 1), (key2805, 1), (key2805, -2), (key2960, 1), (key2948, 1), (key2960, -2), (key2612, -2), (key2829, 1), (key2616, 1), (key2835, -2), (key2835, 1), (key2621, 1), (key3023, -1), (key2706, -1), (key2860, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key2870, -1), (key2632, -1), (key3030, -1), (key2726, -1), (key3030, 1), (key2640, 1), (key2885, 1), (key2732, 1), (key2885, -1), (key2644, -1)]

theorem rawRowCheck5663 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form0 = rawRow5663 := by decide +kernel

def row5663 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2621, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2829, 1), (key2831, 1), (key2835, -1), (key2860, 1), (key2870, -1), (key2948, 1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5663 : row5663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5663 := by decide +kernel

theorem rowEval5663 (x : Key → ℝ) : Integer.Sparse.eval row5663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5663, Integer.Sparse.eval_collectBalanced, rawRowCheck5663]

def rawRow5664 : Integer.Sparse Key := [(key2735, -1), (key2737, -1), (key2747, 2), (key2667, -1), (key2673, -1), (key2702, 2), (key2737, 2), (key2728, -1), (key2747, -1), (key2667, 2), (key2702, -1), (key2735, -1), (key2948, 1), (key2950, 1), (key2960, -2), (key2612, 1), (key2618, 1), (key2805, -2), (key2950, -2), (key2831, 1), (key2960, 1), (key2616, -2), (key2809, 1), (key2829, 1), (key2870, -1), (key2885, -1), (key3026, 1), (key3030, 1), (key2860, 1), (key2885, 1), (key3023, -1), (key3030, -1), (key2632, -1), (key2644, -1), (key2706, 1), (key2732, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2726, -1)]

theorem rawRowCheck5664 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form0 = rawRow5664 := by decide +kernel

def row5664 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5664 : row5664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5664 := by decide +kernel

theorem rowEval5664 (x : Key → ℝ) : Integer.Sparse.eval row5664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5664, Integer.Sparse.eval_collectBalanced, rawRowCheck5664]

def rawRow5665 : Integer.Sparse Key := [(key2737, -1), (key2735, -1), (key2747, 2), (key2673, -1), (key2667, -1), (key2737, 2), (key2702, 2), (key2747, -1), (key2728, -1), (key2667, 2), (key2735, -1), (key2702, -1), (key2950, 1), (key2948, 1), (key2960, -2), (key2618, 1), (key2612, 1), (key2950, -2), (key2805, -2), (key2960, 1), (key2831, 1), (key2616, -2), (key2829, 1), (key2809, 1), (key2885, -1), (key2870, -1), (key3030, 1), (key3026, 1), (key2885, 1), (key2860, 1), (key3030, -1), (key3023, -1), (key2644, -1), (key2632, -1), (key2732, 1), (key2706, 1), (key2640, 1), (key2632, 1), (key2726, -1), (key2706, -1)]

theorem rawRowCheck5665 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form0 = rawRow5665 := by decide +kernel

def row5665 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5665 : row5665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5665 := by decide +kernel

theorem rowEval5665 (x : Key → ℝ) : Integer.Sparse.eval row5665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5665, Integer.Sparse.eval_collectBalanced, rawRowCheck5665]

def rawRow5666 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2737, 2), (key2702, -1), (key2728, -1), (key2667, 2), (key2747, 2), (key2673, -1), (key2737, -1), (key2702, 2), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2950, -2), (key2805, 1), (key2831, 1), (key2612, -2), (key2960, -2), (key2618, 1), (key2950, 1), (key2809, -2), (key2616, 1), (key2829, 1), (key2726, -1), (key3030, -1), (key2732, 1), (key2885, 1), (key2640, 1), (key3030, 1), (key2644, -1), (key2885, -1), (key2706, -1), (key3023, -1), (key2632, 1), (key3026, 1), (key2706, 1), (key2860, 1), (key2632, -1), (key2870, -1)]

theorem rawRowCheck5666 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form0 = rawRow5666 := by decide +kernel

def row5666 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5666 : row5666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5666 := by decide +kernel

theorem rowEval5666 (x : Key → ℝ) : Integer.Sparse.eval row5666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5666, Integer.Sparse.eval_collectBalanced, rawRowCheck5666]

def rawRow5667 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key2737, 2), (key2728, -1), (key2702, -1), (key2747, 2), (key2667, 2), (key2737, -1), (key2673, -1), (key2702, 2), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2950, -2), (key2831, 1), (key2805, 1), (key2960, -2), (key2612, -2), (key2950, 1), (key2618, 1), (key2809, -2), (key2829, 1), (key2616, 1), (key3030, -1), (key2726, -1), (key2885, 1), (key2732, 1), (key3030, 1), (key2640, 1), (key2885, -1), (key2644, -1), (key3023, -1), (key2706, -1), (key3026, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, -1), (key2632, -1)]

theorem rawRowCheck5667 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form0 = rawRow5667 := by decide +kernel

def row5667 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

theorem rowCheck5667 : row5667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5667 := by decide +kernel

theorem rowEval5667 (x : Key → ℝ) : Integer.Sparse.eval row5667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5667, Integer.Sparse.eval_collectBalanced, rawRowCheck5667]

def rawRow5668 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2673, 2), (key2728, 2), (key2667, -1), (key2702, -1), (key2735, 2), (key2667, -1), (key2702, -1), (key2950, 1), (key2960, 1), (key2948, -2), (key2950, 1), (key2960, 1), (key2618, -2), (key2831, -2), (key2612, 1), (key2805, 1), (key2829, -2), (key2616, 1), (key2809, 1), (key2732, -1), (key3026, -1), (key2726, 1), (key2870, 1), (key2644, 1), (key3023, 1), (key2640, -1), (key2860, -1), (key2732, -1), (key3026, -1), (key2644, 1), (key3023, 1), (key2726, 1), (key2870, 1), (key2640, -1), (key2860, -1)]

theorem rawRowCheck5668 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form0 = rawRow5668 := by decide +kernel

def row5668 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2618, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -2), (key2831, -2), (key2860, -2), (key2870, 2), (key2948, -2), (key2950, 2), (key2960, 2), (key3023, 2), (key3026, -2)]

theorem rowCheck5668 : row5668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5668 := by decide +kernel

theorem rowEval5668 (x : Key → ℝ) : Integer.Sparse.eval row5668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5668, Integer.Sparse.eval_collectBalanced, rawRowCheck5668]

def rawRow5669 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2735, 2), (key2747, -1), (key2737, -1), (key2728, 2), (key2673, 2), (key2702, -1), (key2667, -1), (key2735, 2), (key2702, -1), (key2667, -1), (key2960, 1), (key2950, 1), (key2948, -2), (key2960, 1), (key2950, 1), (key2831, -2), (key2618, -2), (key2805, 1), (key2612, 1), (key2829, -2), (key2809, 1), (key2616, 1), (key3026, -1), (key2732, -1), (key2870, 1), (key2726, 1), (key3023, 1), (key2644, 1), (key2860, -1), (key2640, -1), (key3026, -1), (key2732, -1), (key3023, 1), (key2644, 1), (key2870, 1), (key2726, 1), (key2860, -1), (key2640, -1)]

theorem rawRowCheck5669 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form0 = rawRow5669 := by decide +kernel

def row5669 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2618, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -2), (key2831, -2), (key2860, -2), (key2870, 2), (key2948, -2), (key2950, 2), (key2960, 2), (key3023, 2), (key3026, -2)]

theorem rowCheck5669 : row5669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5669 := by decide +kernel

theorem rowEval5669 (x : Key → ℝ) : Integer.Sparse.eval row5669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5669, Integer.Sparse.eval_collectBalanced, rawRowCheck5669]

def rawRow5670 : Integer.Sparse Key := [(key2782, -1), (key2782, -1), (key2795, 2), (key2805, -1), (key2805, -1), (key2893, 2), (key2893, 2), (key2897, -1), (key2897, -1), (key2831, 2), (key2904, -1), (key2904, -1), (key2628, 1), (key2628, 1), (key2641, -2), (key2702, 1), (key2702, 1), (key2972, -2), (key2972, -2), (key2976, 1), (key2976, 1), (key2728, -2), (key2983, 1), (key2983, 1), (key2640, -1), (key2640, -1), (key2660, 1), (key2660, 1), (key2726, 1), (key2726, 1), (key2758, -1), (key2758, -1), (key2794, -1), (key2794, -1), (key2829, 1), (key2829, 1), (key3010, 1), (key3010, 1), (key3017, -1), (key3017, -1)]

theorem rawRowCheck5670 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form0 = rawRow5670 := by decide +kernel

def row5670 : Integer.Sparse Key := [(key2628, 2), (key2640, -2), (key2641, -2), (key2660, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2758, -2), (key2782, -2), (key2794, -2), (key2795, 2), (key2805, -2), (key2829, 2), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3010, 2), (key3017, -2)]

theorem rowCheck5670 : row5670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5670 := by decide +kernel

theorem rowEval5670 (x : Key → ℝ) : Integer.Sparse.eval row5670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5670, Integer.Sparse.eval_collectBalanced, rawRowCheck5670]

def rawRow5671 : Integer.Sparse Key := [(key2782, -1), (key2795, -1), (key2782, 2), (key2893, -1), (key2897, -1), (key2805, 2), (key2897, 2), (key2805, -1), (key2893, -1), (key2904, 2), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2628, -2), (key2972, 1), (key2976, 1), (key2702, -2), (key2976, -2), (key2702, 1), (key2972, 1), (key2983, -2), (key2728, 1), (key2983, 1), (key2612, -1), (key2653, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2758, 1), (key2671, -1), (key2726, -1), (key2829, -1), (key2927, -1), (key2794, 1), (key2927, 1), (key3017, 1), (key3030, 1), (key3010, -1), (key3030, -1)]

theorem rawRowCheck5671 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form0 = rawRow5671 := by decide +kernel

def row5671 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2758, 1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, 1)]

theorem rowCheck5671 : row5671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5671 := by decide +kernel

theorem rowEval5671 (x : Key → ℝ) : Integer.Sparse.eval row5671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5671, Integer.Sparse.eval_collectBalanced, rawRowCheck5671]

def rawRow5672 : Integer.Sparse Key := [(key2795, -1), (key2782, -1), (key2782, 2), (key2897, -1), (key2893, -1), (key2897, 2), (key2805, 2), (key2893, -1), (key2805, -1), (key2904, 2), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2628, -2), (key2976, 1), (key2972, 1), (key2976, -2), (key2702, -2), (key2972, 1), (key2702, 1), (key2983, -2), (key2983, 1), (key2728, 1), (key2653, -1), (key2612, -1), (key2640, 1), (key2616, 1), (key2758, 1), (key2671, 1), (key2726, -1), (key2671, -1), (key2927, -1), (key2829, -1), (key2927, 1), (key2794, 1), (key3030, 1), (key3017, 1), (key3030, -1), (key3010, -1)]

theorem rawRowCheck5672 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form0 = rawRow5672 := by decide +kernel

def row5672 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2758, 1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, 1)]

theorem rowCheck5672 : row5672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5672 := by decide +kernel

theorem rowEval5672 (x : Key → ℝ) : Integer.Sparse.eval row5672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5672, Integer.Sparse.eval_collectBalanced, rawRowCheck5672]

def rawRow5673 : Integer.Sparse Key := [(key2805, -1), (key2805, -1), (key2831, 2), (key2782, -1), (key2782, -1), (key2893, 2), (key2893, 2), (key2904, -1), (key2904, -1), (key2795, 2), (key2897, -1), (key2897, -1), (key2702, 1), (key2702, 1), (key2728, -2), (key2628, 1), (key2628, 1), (key2972, -2), (key2972, -2), (key2983, 1), (key2983, 1), (key2641, -2), (key2976, 1), (key2976, 1), (key2735, -1), (key2735, -1), (key2747, 1), (key2747, 1), (key2829, 1), (key2829, 1), (key3017, -1), (key3017, -1), (key2640, -1), (key2640, -1), (key2726, 1), (key2726, 1), (key2660, 1), (key2660, 1), (key2758, -1), (key2758, -1)]

theorem rawRowCheck5673 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form0 = rawRow5673 := by decide +kernel

def row5673 : Integer.Sparse Key := [(key2628, 2), (key2640, -2), (key2641, -2), (key2660, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2735, -2), (key2747, 2), (key2758, -2), (key2782, -2), (key2795, 2), (key2805, -2), (key2829, 2), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3017, -2)]

theorem rowCheck5673 : row5673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5673 := by decide +kernel

theorem rowEval5673 (x : Key → ℝ) : Integer.Sparse.eval row5673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5673, Integer.Sparse.eval_collectBalanced, rawRowCheck5673]

def rawRow5674 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2805, 2), (key2893, -1), (key2904, -1), (key2782, 2), (key2904, 2), (key2782, -1), (key2893, -1), (key2897, 2), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2702, -2), (key2972, 1), (key2983, 1), (key2628, -2), (key2983, -2), (key2628, 1), (key2972, 1), (key2976, -2), (key2641, 1), (key2976, 1), (key2667, -1), (key2747, -1), (key2667, 1), (key2735, 1), (key2612, 1), (key2960, 1), (key2616, -1), (key2829, -1), (key2726, -1), (key3030, -1), (key2640, 1), (key3030, 1), (key2758, 1), (key2927, 1), (key2660, -1), (key2927, -1)]

theorem rawRowCheck5674 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form0 = rawRow5674 := by decide +kernel

def row5674 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2660, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2758, 1), (key2782, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5674 : row5674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5674 := by decide +kernel

theorem rowEval5674 (x : Key → ℝ) : Integer.Sparse.eval row5674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5674, Integer.Sparse.eval_collectBalanced, rawRowCheck5674]

def rawRow5675 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2805, 2), (key2904, -1), (key2893, -1), (key2904, 2), (key2782, 2), (key2893, -1), (key2782, -1), (key2897, 2), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2702, -2), (key2983, 1), (key2972, 1), (key2983, -2), (key2628, -2), (key2972, 1), (key2628, 1), (key2976, -2), (key2976, 1), (key2641, 1), (key2747, -1), (key2667, -1), (key2735, 1), (key2667, 1), (key2960, 1), (key2612, 1), (key2829, -1), (key2616, -1), (key3030, -1), (key2726, -1), (key3030, 1), (key2640, 1), (key2927, 1), (key2758, 1), (key2927, -1), (key2660, -1)]

theorem rawRowCheck5675 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form0 = rawRow5675 := by decide +kernel

def row5675 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2660, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2758, 1), (key2782, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5675 : row5675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5675 := by decide +kernel

theorem rowEval5675 (x : Key → ℝ) : Integer.Sparse.eval row5675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5675, Integer.Sparse.eval_collectBalanced, rawRowCheck5675]

def rawRow5676 : Integer.Sparse Key := [(key2893, -1), (key2897, -1), (key2904, 2), (key2782, -1), (key2795, -1), (key2805, 2), (key2897, 2), (key2831, -1), (key2904, -1), (key2782, 2), (key2805, -1), (key2893, -1), (key2972, 1), (key2976, 1), (key2983, -2), (key2628, 1), (key2641, 1), (key2702, -2), (key2976, -2), (key2728, 1), (key2983, 1), (key2628, -2), (key2702, 1), (key2972, 1), (key2948, -1), (key2998, -1), (key2960, 1), (key3000, 1), (key2735, 1), (key2998, 1), (key2747, -1), (key3000, -1), (key2612, -1), (key2653, -1), (key2667, 1), (key2943, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2726, -1)]

theorem rawRowCheck5676 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form0 = rawRow5676 := by decide +kernel

def row5676 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2667, 1), (key2671, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5676 : row5676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5676 := by decide +kernel

theorem rowEval5676 (x : Key → ℝ) : Integer.Sparse.eval row5676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5676, Integer.Sparse.eval_collectBalanced, rawRowCheck5676]

def rawRow5677 : Integer.Sparse Key := [(key2897, -1), (key2893, -1), (key2904, 2), (key2795, -1), (key2782, -1), (key2897, 2), (key2805, 2), (key2904, -1), (key2831, -1), (key2782, 2), (key2893, -1), (key2805, -1), (key2976, 1), (key2972, 1), (key2983, -2), (key2641, 1), (key2628, 1), (key2976, -2), (key2702, -2), (key2983, 1), (key2728, 1), (key2628, -2), (key2972, 1), (key2702, 1), (key2998, -1), (key2948, -1), (key3000, 1), (key2960, 1), (key2998, 1), (key2735, 1), (key3000, -1), (key2747, -1), (key2653, -1), (key2612, -1), (key2943, 1), (key2667, 1), (key2640, 1), (key2616, 1), (key2726, -1), (key2671, -1)]

theorem rawRowCheck5677 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form0 = rawRow5677 := by decide +kernel

def row5677 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2667, 1), (key2671, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5677 : row5677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5677 := by decide +kernel

theorem rowEval5677 (x : Key → ℝ) : Integer.Sparse.eval row5677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5677, Integer.Sparse.eval_collectBalanced, rawRowCheck5677]

def rawRow5678 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2897, 2), (key2805, -1), (key2831, -1), (key2782, 2), (key2904, 2), (key2795, -1), (key2897, -1), (key2805, 2), (key2782, -1), (key2893, -1), (key2972, 1), (key2983, 1), (key2976, -2), (key2702, 1), (key2728, 1), (key2628, -2), (key2983, -2), (key2641, 1), (key2976, 1), (key2702, -2), (key2628, 1), (key2972, 1), (key2936, -1), (key3000, -1), (key2943, 1), (key2998, 1), (key2646, 1), (key3000, 1), (key2653, -1), (key2998, -1), (key2667, -1), (key2747, -1), (key2612, 1), (key2960, 1), (key2671, 1), (key2794, 1), (key2616, -1), (key2829, -1)]

theorem rawRowCheck5678 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form0 = rawRow5678 := by decide +kernel

def row5678 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2667, -1), (key2671, 1), (key2702, -1), (key2728, 1), (key2747, -1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5678 : row5678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5678 := by decide +kernel

theorem rowEval5678 (x : Key → ℝ) : Integer.Sparse.eval row5678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5678, Integer.Sparse.eval_collectBalanced, rawRowCheck5678]

def rawRow5679 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key2897, 2), (key2831, -1), (key2805, -1), (key2904, 2), (key2782, 2), (key2897, -1), (key2795, -1), (key2805, 2), (key2893, -1), (key2782, -1), (key2983, 1), (key2972, 1), (key2976, -2), (key2728, 1), (key2702, 1), (key2983, -2), (key2628, -2), (key2976, 1), (key2641, 1), (key2702, -2), (key2972, 1), (key2628, 1), (key3000, -1), (key2936, -1), (key2998, 1), (key2943, 1), (key3000, 1), (key2646, 1), (key2998, -1), (key2653, -1), (key2747, -1), (key2667, -1), (key2960, 1), (key2612, 1), (key2794, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

theorem rawRowCheck5679 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form0 = rawRow5679 := by decide +kernel

def row5679 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2667, -1), (key2671, 1), (key2702, -1), (key2728, 1), (key2747, -1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5679 : row5679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5679 := by decide +kernel

theorem rowEval5679 (x : Key → ℝ) : Integer.Sparse.eval row5679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5679, Integer.Sparse.eval_collectBalanced, rawRowCheck5679]

def rawRow5680 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2893, 2), (key2897, -1), (key2904, -1), (key2795, 2), (key2831, 2), (key2782, -1), (key2805, -1), (key2893, 2), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2641, -2), (key2728, -2), (key2628, 1), (key2702, 1), (key2972, -2), (key2628, 1), (key2702, 1), (key2943, -1), (key2960, -1), (key2936, 1), (key2948, 1), (key2653, 1), (key2747, 1), (key2646, -1), (key2735, -1), (key2943, -1), (key2960, -1), (key2653, 1), (key2747, 1), (key2726, 1), (key2829, 1), (key2640, -1), (key2794, -1)]

theorem rawRowCheck5680 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form0 = rawRow5680 := by decide +kernel

def row5680 : Integer.Sparse Key := [(key2628, 2), (key2640, -1), (key2641, -2), (key2646, -1), (key2653, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2735, -1), (key2747, 2), (key2782, -2), (key2794, -1), (key2795, 2), (key2805, -2), (key2829, 1), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2936, 1), (key2943, -2), (key2948, 1), (key2960, -2), (key2972, -4), (key2976, 2), (key2983, 2)]

theorem rowCheck5680 : row5680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5680 := by decide +kernel

theorem rowEval5680 (x : Key → ℝ) : Integer.Sparse.eval row5680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5680, Integer.Sparse.eval_collectBalanced, rawRowCheck5680]

def rawRow5681 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2893, 2), (key2904, -1), (key2897, -1), (key2831, 2), (key2795, 2), (key2805, -1), (key2782, -1), (key2893, 2), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2972, -2), (key2983, 1), (key2976, 1), (key2728, -2), (key2641, -2), (key2702, 1), (key2628, 1), (key2972, -2), (key2702, 1), (key2628, 1), (key2960, -1), (key2943, -1), (key2948, 1), (key2936, 1), (key2747, 1), (key2653, 1), (key2735, -1), (key2646, -1), (key2960, -1), (key2943, -1), (key2747, 1), (key2653, 1), (key2829, 1), (key2726, 1), (key2794, -1), (key2640, -1)]

theorem rawRowCheck5681 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form0 = rawRow5681 := by decide +kernel

def row5681 : Integer.Sparse Key := [(key2628, 2), (key2640, -1), (key2641, -2), (key2646, -1), (key2653, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2735, -1), (key2747, 2), (key2782, -2), (key2794, -1), (key2795, 2), (key2805, -2), (key2829, 1), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2936, 1), (key2943, -2), (key2948, 1), (key2960, -2), (key2972, -4), (key2976, 2), (key2983, 2)]

theorem rowCheck5681 : row5681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5681 := by decide +kernel

theorem rowEval5681 (x : Key → ℝ) : Integer.Sparse.eval row5681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5681, Integer.Sparse.eval_collectBalanced, rawRowCheck5681]

def rawRow5682 : Integer.Sparse Key := [(key2936, -1), (key2938, -1), (key2943, 2), (key2948, -1), (key2950, -1), (key2972, 2), (key2997, 2), (key2976, -1), (key2998, -1), (key2960, 2), (key2983, -1), (key3000, -1), (key2646, 1), (key2648, 1), (key2653, -2), (key2735, 1), (key2737, 1), (key2893, -2), (key2997, -2), (key2897, 1), (key2998, 1), (key2747, -2), (key2904, 1), (key3000, 1), (key2628, -1), (key2648, -1), (key2641, 1), (key2653, 1), (key2782, 1), (key2938, 1), (key2795, -1), (key2943, -1), (key2702, -1), (key2737, -1), (key2805, 1), (key2950, 1), (key2728, 1), (key2747, 1), (key2831, -1), (key2960, -1)]

theorem rawRowCheck5682 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form0 = rawRow5682 := by decide +kernel

def row5682 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5682 : row5682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5682 := by decide +kernel

theorem rowEval5682 (x : Key → ℝ) : Integer.Sparse.eval row5682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5682, Integer.Sparse.eval_collectBalanced, rawRowCheck5682]

def rawRow5683 : Integer.Sparse Key := [(key2938, -1), (key2936, -1), (key2943, 2), (key2950, -1), (key2948, -1), (key2997, 2), (key2972, 2), (key2998, -1), (key2976, -1), (key2960, 2), (key3000, -1), (key2983, -1), (key2648, 1), (key2646, 1), (key2653, -2), (key2737, 1), (key2735, 1), (key2997, -2), (key2893, -2), (key2998, 1), (key2897, 1), (key2747, -2), (key3000, 1), (key2904, 1), (key2648, -1), (key2628, -1), (key2653, 1), (key2641, 1), (key2938, 1), (key2782, 1), (key2943, -1), (key2795, -1), (key2737, -1), (key2702, -1), (key2950, 1), (key2805, 1), (key2747, 1), (key2728, 1), (key2960, -1), (key2831, -1)]

theorem rawRowCheck5683 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form0 = rawRow5683 := by decide +kernel

def row5683 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5683 : row5683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5683 := by decide +kernel

theorem rowEval5683 (x : Key → ℝ) : Integer.Sparse.eval row5683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5683, Integer.Sparse.eval_collectBalanced, rawRowCheck5683]

def rawRow5684 : Integer.Sparse Key := [(key2936, -1), (key2943, -1), (key2938, 2), (key2972, -1), (key2976, -1), (key2948, 2), (key2998, 2), (key2950, -1), (key2997, -1), (key2983, 2), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2648, -2), (key2893, 1), (key2897, 1), (key2735, -2), (key2998, -2), (key2737, 1), (key2997, 1), (key2904, -2), (key2747, 1), (key3000, 1), (key2612, -1), (key2653, -1), (key2618, 1), (key2648, 1), (key2667, 1), (key2943, 1), (key2673, -1), (key2938, -1), (key2805, -1), (key2897, -1), (key2702, 1), (key2976, 1), (key2831, 1), (key2904, 1), (key2728, -1), (key2983, -1)]

theorem rawRowCheck5684 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form0 = rawRow5684 := by decide +kernel

def row5684 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5684 : row5684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5684 := by decide +kernel

theorem rowEval5684 (x : Key → ℝ) : Integer.Sparse.eval row5684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5684, Integer.Sparse.eval_collectBalanced, rawRowCheck5684]

def rawRow5685 : Integer.Sparse Key := [(key2943, -1), (key2936, -1), (key2938, 2), (key2976, -1), (key2972, -1), (key2998, 2), (key2948, 2), (key2997, -1), (key2950, -1), (key2983, 2), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2648, -2), (key2897, 1), (key2893, 1), (key2998, -2), (key2735, -2), (key2997, 1), (key2737, 1), (key2904, -2), (key3000, 1), (key2747, 1), (key2653, -1), (key2612, -1), (key2648, 1), (key2618, 1), (key2943, 1), (key2667, 1), (key2938, -1), (key2673, -1), (key2897, -1), (key2805, -1), (key2976, 1), (key2702, 1), (key2904, 1), (key2831, 1), (key2983, -1), (key2728, -1)]

theorem rawRowCheck5685 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form0 = rawRow5685 := by decide +kernel

def row5685 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5685 : row5685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5685 := by decide +kernel

theorem rowEval5685 (x : Key → ℝ) : Integer.Sparse.eval row5685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5685, Integer.Sparse.eval_collectBalanced, rawRowCheck5685]

def rawRow5686 : Integer.Sparse Key := [(key2948, -1), (key2950, -1), (key2960, 2), (key2936, -1), (key2938, -1), (key2972, 2), (key2997, 2), (key2983, -1), (key3000, -1), (key2943, 2), (key2976, -1), (key2998, -1), (key2735, 1), (key2737, 1), (key2747, -2), (key2646, 1), (key2648, 1), (key2893, -2), (key2997, -2), (key2904, 1), (key3000, 1), (key2653, -2), (key2897, 1), (key2998, 1), (key2702, -1), (key2737, -1), (key2728, 1), (key2747, 1), (key2805, 1), (key2950, 1), (key2831, -1), (key2960, -1), (key2628, -1), (key2648, -1), (key2782, 1), (key2938, 1), (key2641, 1), (key2653, 1), (key2795, -1), (key2943, -1)]

theorem rawRowCheck5686 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form0 = rawRow5686 := by decide +kernel

def row5686 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5686 : row5686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5686 := by decide +kernel

theorem rowEval5686 (x : Key → ℝ) : Integer.Sparse.eval row5686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5686, Integer.Sparse.eval_collectBalanced, rawRowCheck5686]

def rawRow5687 : Integer.Sparse Key := [(key2950, -1), (key2948, -1), (key2960, 2), (key2938, -1), (key2936, -1), (key2997, 2), (key2972, 2), (key3000, -1), (key2983, -1), (key2943, 2), (key2998, -1), (key2976, -1), (key2737, 1), (key2735, 1), (key2747, -2), (key2648, 1), (key2646, 1), (key2997, -2), (key2893, -2), (key3000, 1), (key2904, 1), (key2653, -2), (key2998, 1), (key2897, 1), (key2737, -1), (key2702, -1), (key2747, 1), (key2728, 1), (key2950, 1), (key2805, 1), (key2960, -1), (key2831, -1), (key2648, -1), (key2628, -1), (key2938, 1), (key2782, 1), (key2653, 1), (key2641, 1), (key2943, -1), (key2795, -1)]

theorem rawRowCheck5687 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form0 = rawRow5687 := by decide +kernel

def row5687 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5687 : row5687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5687 := by decide +kernel

theorem rowEval5687 (x : Key → ℝ) : Integer.Sparse.eval row5687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5687, Integer.Sparse.eval_collectBalanced, rawRowCheck5687]

def rawRow5688 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2948, 2), (key2997, -1), (key3000, -1), (key2938, 2), (key2983, 2), (key2936, -1), (key2972, -1), (key2998, 2), (key2943, -1), (key2976, -1), (key2737, 1), (key2747, 1), (key2735, -2), (key2997, 1), (key3000, 1), (key2648, -2), (key2904, -2), (key2646, 1), (key2893, 1), (key2998, -2), (key2653, 1), (key2897, 1), (key2673, -1), (key2728, -1), (key2667, 1), (key2702, 1), (key2618, 1), (key2831, 1), (key2612, -1), (key2805, -1), (key2938, -1), (key2983, -1), (key2648, 1), (key2904, 1), (key2943, 1), (key2976, 1), (key2653, -1), (key2897, -1)]

theorem rawRowCheck5688 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form0 = rawRow5688 := by decide +kernel

def row5688 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5688 : row5688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5688 := by decide +kernel

theorem rowEval5688 (x : Key → ℝ) : Integer.Sparse.eval row5688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5688, Integer.Sparse.eval_collectBalanced, rawRowCheck5688]

def rawRow5689 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2948, 2), (key3000, -1), (key2997, -1), (key2983, 2), (key2938, 2), (key2972, -1), (key2936, -1), (key2998, 2), (key2976, -1), (key2943, -1), (key2747, 1), (key2737, 1), (key2735, -2), (key3000, 1), (key2997, 1), (key2904, -2), (key2648, -2), (key2893, 1), (key2646, 1), (key2998, -2), (key2897, 1), (key2653, 1), (key2728, -1), (key2673, -1), (key2702, 1), (key2667, 1), (key2831, 1), (key2618, 1), (key2805, -1), (key2612, -1), (key2983, -1), (key2938, -1), (key2904, 1), (key2648, 1), (key2976, 1), (key2943, 1), (key2897, -1), (key2653, -1)]

theorem rawRowCheck5689 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form0 = rawRow5689 := by decide +kernel

def row5689 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5689 : row5689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5689 := by decide +kernel

theorem rowEval5689 (x : Key → ℝ) : Integer.Sparse.eval row5689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5689, Integer.Sparse.eval_collectBalanced, rawRowCheck5689]

def rawRow5690 : Integer.Sparse Key := [(key2972, -1), (key2976, -1), (key2983, 2), (key2936, -1), (key2943, -1), (key2948, 2), (key2998, 2), (key2960, -1), (key3000, -1), (key2938, 2), (key2950, -1), (key2997, -1), (key2893, 1), (key2897, 1), (key2904, -2), (key2646, 1), (key2653, 1), (key2735, -2), (key2998, -2), (key2747, 1), (key3000, 1), (key2648, -2), (key2737, 1), (key2997, 1), (key2805, -1), (key2897, -1), (key2831, 1), (key2904, 1), (key2702, 1), (key2976, 1), (key2728, -1), (key2983, -1), (key2612, -1), (key2653, -1), (key2667, 1), (key2943, 1), (key2618, 1), (key2648, 1), (key2673, -1), (key2938, -1)]

theorem rawRowCheck5690 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form0 = rawRow5690 := by decide +kernel

def row5690 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5690 : row5690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5690 := by decide +kernel

theorem rowEval5690 (x : Key → ℝ) : Integer.Sparse.eval row5690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5690, Integer.Sparse.eval_collectBalanced, rawRowCheck5690]

def rawRow5691 : Integer.Sparse Key := [(key2976, -1), (key2972, -1), (key2983, 2), (key2943, -1), (key2936, -1), (key2998, 2), (key2948, 2), (key3000, -1), (key2960, -1), (key2938, 2), (key2997, -1), (key2950, -1), (key2897, 1), (key2893, 1), (key2904, -2), (key2653, 1), (key2646, 1), (key2998, -2), (key2735, -2), (key3000, 1), (key2747, 1), (key2648, -2), (key2997, 1), (key2737, 1), (key2897, -1), (key2805, -1), (key2904, 1), (key2831, 1), (key2976, 1), (key2702, 1), (key2983, -1), (key2728, -1), (key2653, -1), (key2612, -1), (key2943, 1), (key2667, 1), (key2648, 1), (key2618, 1), (key2938, -1), (key2673, -1)]

theorem rawRowCheck5691 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form0 = rawRow5691 := by decide +kernel

def row5691 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5691 : row5691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5691 := by decide +kernel

theorem rowEval5691 (x : Key → ℝ) : Integer.Sparse.eval row5691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5691, Integer.Sparse.eval_collectBalanced, rawRowCheck5691]

def rawRow5692 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2972, 2), (key2998, -1), (key3000, -1), (key2943, 2), (key2960, 2), (key2936, -1), (key2948, -1), (key2997, 2), (key2938, -1), (key2950, -1), (key2897, 1), (key2904, 1), (key2893, -2), (key2998, 1), (key3000, 1), (key2653, -2), (key2747, -2), (key2646, 1), (key2735, 1), (key2997, -2), (key2648, 1), (key2737, 1), (key2795, -1), (key2831, -1), (key2782, 1), (key2805, 1), (key2641, 1), (key2728, 1), (key2628, -1), (key2702, -1), (key2943, -1), (key2960, -1), (key2653, 1), (key2747, 1), (key2938, 1), (key2950, 1), (key2648, -1), (key2737, -1)]

theorem rawRowCheck5692 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form0 = rawRow5692 := by decide +kernel

def row5692 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5692 : row5692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5692 := by decide +kernel

theorem rowEval5692 (x : Key → ℝ) : Integer.Sparse.eval row5692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5692, Integer.Sparse.eval_collectBalanced, rawRowCheck5692]

def rawRow5693 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2972, 2), (key3000, -1), (key2998, -1), (key2960, 2), (key2943, 2), (key2948, -1), (key2936, -1), (key2997, 2), (key2950, -1), (key2938, -1), (key2904, 1), (key2897, 1), (key2893, -2), (key3000, 1), (key2998, 1), (key2747, -2), (key2653, -2), (key2735, 1), (key2646, 1), (key2997, -2), (key2737, 1), (key2648, 1), (key2831, -1), (key2795, -1), (key2805, 1), (key2782, 1), (key2728, 1), (key2641, 1), (key2702, -1), (key2628, -1), (key2960, -1), (key2943, -1), (key2747, 1), (key2653, 1), (key2950, 1), (key2938, 1), (key2737, -1), (key2648, -1)]

theorem rawRowCheck5693 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form0 = rawRow5693 := by decide +kernel

def row5693 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5693 : row5693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5693 := by decide +kernel

theorem rowEval5693 (x : Key → ℝ) : Integer.Sparse.eval row5693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5693, Integer.Sparse.eval_collectBalanced, rawRowCheck5693]

def rawRow5694 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2998, 2), (key2950, -1), (key2960, -1), (key2938, 2), (key2983, 2), (key2943, -1), (key2976, -1), (key2948, 2), (key2936, -1), (key2972, -1), (key2997, 1), (key3000, 1), (key2998, -2), (key2737, 1), (key2747, 1), (key2648, -2), (key2904, -2), (key2653, 1), (key2897, 1), (key2735, -2), (key2646, 1), (key2893, 1), (key2938, -1), (key2983, -1), (key2943, 1), (key2976, 1), (key2648, 1), (key2904, 1), (key2653, -1), (key2897, -1), (key2673, -1), (key2728, -1), (key2618, 1), (key2831, 1), (key2667, 1), (key2702, 1), (key2612, -1), (key2805, -1)]

theorem rawRowCheck5694 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form0 = rawRow5694 := by decide +kernel

def row5694 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5694 : row5694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5694 := by decide +kernel

theorem rowEval5694 (x : Key → ℝ) : Integer.Sparse.eval row5694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5694, Integer.Sparse.eval_collectBalanced, rawRowCheck5694]

def rawRow5695 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2998, 2), (key2960, -1), (key2950, -1), (key2983, 2), (key2938, 2), (key2976, -1), (key2943, -1), (key2948, 2), (key2972, -1), (key2936, -1), (key3000, 1), (key2997, 1), (key2998, -2), (key2747, 1), (key2737, 1), (key2904, -2), (key2648, -2), (key2897, 1), (key2653, 1), (key2735, -2), (key2893, 1), (key2646, 1), (key2983, -1), (key2938, -1), (key2976, 1), (key2943, 1), (key2904, 1), (key2648, 1), (key2897, -1), (key2653, -1), (key2728, -1), (key2673, -1), (key2831, 1), (key2618, 1), (key2702, 1), (key2667, 1), (key2805, -1), (key2612, -1)]

theorem rawRowCheck5695 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form0 = rawRow5695 := by decide +kernel

def row5695 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

theorem rowCheck5695 : row5695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5695 := by decide +kernel

theorem rowEval5695 (x : Key → ℝ) : Integer.Sparse.eval row5695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5695, Integer.Sparse.eval_collectBalanced, rawRowCheck5695]

def rawRow5696 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2997, 2), (key2976, -1), (key2983, -1), (key2943, 2), (key2960, 2), (key2938, -1), (key2950, -1), (key2972, 2), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2997, -2), (key2897, 1), (key2904, 1), (key2653, -2), (key2747, -2), (key2648, 1), (key2737, 1), (key2893, -2), (key2646, 1), (key2735, 1), (key2943, -1), (key2960, -1), (key2938, 1), (key2950, 1), (key2653, 1), (key2747, 1), (key2648, -1), (key2737, -1), (key2795, -1), (key2831, -1), (key2641, 1), (key2728, 1), (key2782, 1), (key2805, 1), (key2628, -1), (key2702, -1)]

theorem rawRowCheck5696 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form0 = rawRow5696 := by decide +kernel

def row5696 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5696 : row5696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5696 := by decide +kernel

theorem rowEval5696 (x : Key → ℝ) : Integer.Sparse.eval row5696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5696, Integer.Sparse.eval_collectBalanced, rawRowCheck5696]

def rawRow5697 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2997, 2), (key2983, -1), (key2976, -1), (key2960, 2), (key2943, 2), (key2950, -1), (key2938, -1), (key2972, 2), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2997, -2), (key2904, 1), (key2897, 1), (key2747, -2), (key2653, -2), (key2737, 1), (key2648, 1), (key2893, -2), (key2735, 1), (key2646, 1), (key2960, -1), (key2943, -1), (key2950, 1), (key2938, 1), (key2747, 1), (key2653, 1), (key2737, -1), (key2648, -1), (key2831, -1), (key2795, -1), (key2728, 1), (key2641, 1), (key2805, 1), (key2782, 1), (key2702, -1), (key2628, -1)]

theorem rawRowCheck5697 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form0 = rawRow5697 := by decide +kernel

def row5697 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

theorem rowCheck5697 : row5697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5697 := by decide +kernel

theorem rowEval5697 (x : Key → ℝ) : Integer.Sparse.eval row5697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5697, Integer.Sparse.eval_collectBalanced, rawRowCheck5697]

def rawRow5698 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1398, 2), (key1424, -1), (key1424, -1), (key1455, 2), (key1455, 2), (key1458, -1), (key1458, -1), (key1448, 2), (key1467, -1), (key1467, -1), (key1296, 1), (key1296, 1), (key1303, -2), (key1573, 1), (key1573, 1), (key1788, -2), (key1788, -2), (key1791, 1), (key1791, 1), (key1597, -2), (key1799, 1), (key1799, 1), (key1337, -1), (key1337, -1), (key1340, 1), (key1340, 1), (key1772, 1), (key1772, 1), (key1775, -1), (key1775, -1), (key1655, -1), (key1655, -1), (key1813, 1), (key1813, 1), (key1668, 1), (key1668, 1), (key1826, -1), (key1826, -1)]

theorem rawRowCheck5698 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5698 := by decide +kernel

def row5698 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

theorem rowCheck5698 : row5698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5698 := by decide +kernel

theorem rowEval5698 (x : Key → ℝ) : Integer.Sparse.eval row5698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5698, Integer.Sparse.eval_collectBalanced, rawRowCheck5698]

def rawRow5699 : Integer.Sparse Key := [(key1391, -1), (key1398, -1), (key1391, 2), (key1455, -1), (key1458, -1), (key1424, 2), (key1458, 2), (key1424, -1), (key1455, -1), (key1467, 2), (key1448, -1), (key1467, -1), (key1296, 1), (key1303, 1), (key1296, -2), (key1788, 1), (key1791, 1), (key1573, -2), (key1791, -2), (key1573, 1), (key1788, 1), (key1799, -2), (key1597, 1), (key1799, 1), (key1316, -1), (key1340, -1), (key1316, 1), (key1337, 1), (key1546, 1), (key1775, 1), (key1546, -1), (key1772, -1), (key1813, -1), (key1840, -1), (key1655, 1), (key1840, 1), (key1826, 1), (key1845, 1), (key1668, -1), (key1845, -1)]

theorem rawRowCheck5699 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5699 := by decide +kernel

def row5699 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5699 : row5699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5699 := by decide +kernel

theorem rowEval5699 (x : Key → ℝ) : Integer.Sparse.eval row5699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5699, Integer.Sparse.eval_collectBalanced, rawRowCheck5699]

def rawRow5700 : Integer.Sparse Key := [(key1398, -1), (key1391, -1), (key1391, 2), (key1458, -1), (key1455, -1), (key1458, 2), (key1424, 2), (key1455, -1), (key1424, -1), (key1467, 2), (key1467, -1), (key1448, -1), (key1303, 1), (key1296, 1), (key1296, -2), (key1791, 1), (key1788, 1), (key1791, -2), (key1573, -2), (key1788, 1), (key1573, 1), (key1799, -2), (key1799, 1), (key1597, 1), (key1340, -1), (key1316, -1), (key1337, 1), (key1316, 1), (key1775, 1), (key1546, 1), (key1772, -1), (key1546, -1), (key1840, -1), (key1813, -1), (key1840, 1), (key1655, 1), (key1845, 1), (key1826, 1), (key1845, -1), (key1668, -1)]

theorem rawRowCheck5700 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5700 := by decide +kernel

def row5700 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5700 : row5700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5700 := by decide +kernel

theorem rowEval5700 (x : Key → ℝ) : Integer.Sparse.eval row5700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5700, Integer.Sparse.eval_collectBalanced, rawRowCheck5700]

def rawRow5701 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1448, 2), (key1391, -1), (key1391, -1), (key1455, 2), (key1455, 2), (key1467, -1), (key1467, -1), (key1398, 2), (key1458, -1), (key1458, -1), (key1573, 1), (key1573, 1), (key1597, -2), (key1296, 1), (key1296, 1), (key1788, -2), (key1788, -2), (key1799, 1), (key1799, 1), (key1303, -2), (key1791, 1), (key1791, 1), (key1655, -1), (key1655, -1), (key1668, 1), (key1668, 1), (key1813, 1), (key1813, 1), (key1826, -1), (key1826, -1), (key1337, -1), (key1337, -1), (key1772, 1), (key1772, 1), (key1340, 1), (key1340, 1), (key1775, -1), (key1775, -1)]

theorem rawRowCheck5701 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form1 = rawRow5701 := by decide +kernel

def row5701 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

theorem rowCheck5701 : row5701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5701 := by decide +kernel

theorem rowEval5701 (x : Key → ℝ) : Integer.Sparse.eval row5701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5701, Integer.Sparse.eval_collectBalanced, rawRowCheck5701]

def rawRow5702 : Integer.Sparse Key := [(key1424, -1), (key1448, -1), (key1424, 2), (key1455, -1), (key1467, -1), (key1391, 2), (key1467, 2), (key1391, -1), (key1455, -1), (key1458, 2), (key1398, -1), (key1458, -1), (key1573, 1), (key1597, 1), (key1573, -2), (key1788, 1), (key1799, 1), (key1296, -2), (key1799, -2), (key1296, 1), (key1788, 1), (key1791, -2), (key1303, 1), (key1791, 1), (key1546, -1), (key1668, -1), (key1546, 1), (key1655, 1), (key1316, 1), (key1826, 1), (key1316, -1), (key1813, -1), (key1772, -1), (key1845, -1), (key1337, 1), (key1845, 1), (key1775, 1), (key1840, 1), (key1340, -1), (key1840, -1)]

theorem rawRowCheck5702 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form1 = rawRow5702 := by decide +kernel

def row5702 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5702 : row5702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5702 := by decide +kernel

theorem rowEval5702 (x : Key → ℝ) : Integer.Sparse.eval row5702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5702, Integer.Sparse.eval_collectBalanced, rawRowCheck5702]

def rawRow5703 : Integer.Sparse Key := [(key1448, -1), (key1424, -1), (key1424, 2), (key1467, -1), (key1455, -1), (key1467, 2), (key1391, 2), (key1455, -1), (key1391, -1), (key1458, 2), (key1458, -1), (key1398, -1), (key1597, 1), (key1573, 1), (key1573, -2), (key1799, 1), (key1788, 1), (key1799, -2), (key1296, -2), (key1788, 1), (key1296, 1), (key1791, -2), (key1791, 1), (key1303, 1), (key1668, -1), (key1546, -1), (key1655, 1), (key1546, 1), (key1826, 1), (key1316, 1), (key1813, -1), (key1316, -1), (key1845, -1), (key1772, -1), (key1845, 1), (key1337, 1), (key1840, 1), (key1775, 1), (key1840, -1), (key1340, -1)]

theorem rawRowCheck5703 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form1 = rawRow5703 := by decide +kernel

def row5703 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5703 : row5703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5703 := by decide +kernel

theorem rowEval5703 (x : Key → ℝ) : Integer.Sparse.eval row5703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5703, Integer.Sparse.eval_collectBalanced, rawRowCheck5703]

def rawRow5704 : Integer.Sparse Key := [(key1455, -1), (key1458, -1), (key1467, 2), (key1391, -1), (key1398, -1), (key1424, 2), (key1458, 2), (key1448, -1), (key1467, -1), (key1391, 2), (key1424, -1), (key1455, -1), (key1788, 1), (key1791, 1), (key1799, -2), (key1296, 1), (key1303, 1), (key1573, -2), (key1791, -2), (key1597, 1), (key1799, 1), (key1296, -2), (key1573, 1), (key1788, 1), (key1813, -1), (key1840, -1), (key1826, 1), (key1845, 1), (key1655, 1), (key1840, 1), (key1668, -1), (key1845, -1), (key1316, -1), (key1340, -1), (key1546, 1), (key1775, 1), (key1316, 1), (key1337, 1), (key1546, -1), (key1772, -1)]

theorem rawRowCheck5704 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form1 = rawRow5704 := by decide +kernel

def row5704 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5704 : row5704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5704 := by decide +kernel

theorem rowEval5704 (x : Key → ℝ) : Integer.Sparse.eval row5704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5704, Integer.Sparse.eval_collectBalanced, rawRowCheck5704]

def rawRow5705 : Integer.Sparse Key := [(key1458, -1), (key1455, -1), (key1467, 2), (key1398, -1), (key1391, -1), (key1458, 2), (key1424, 2), (key1467, -1), (key1448, -1), (key1391, 2), (key1455, -1), (key1424, -1), (key1791, 1), (key1788, 1), (key1799, -2), (key1303, 1), (key1296, 1), (key1791, -2), (key1573, -2), (key1799, 1), (key1597, 1), (key1296, -2), (key1788, 1), (key1573, 1), (key1840, -1), (key1813, -1), (key1845, 1), (key1826, 1), (key1840, 1), (key1655, 1), (key1845, -1), (key1668, -1), (key1340, -1), (key1316, -1), (key1775, 1), (key1546, 1), (key1337, 1), (key1316, 1), (key1772, -1), (key1546, -1)]

theorem rawRowCheck5705 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form1 = rawRow5705 := by decide +kernel

def row5705 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5705 : row5705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5705 := by decide +kernel

theorem rowEval5705 (x : Key → ℝ) : Integer.Sparse.eval row5705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5705, Integer.Sparse.eval_collectBalanced, rawRowCheck5705]

def rawRow5706 : Integer.Sparse Key := [(key1455, -1), (key1467, -1), (key1458, 2), (key1424, -1), (key1448, -1), (key1391, 2), (key1467, 2), (key1398, -1), (key1458, -1), (key1424, 2), (key1391, -1), (key1455, -1), (key1788, 1), (key1799, 1), (key1791, -2), (key1573, 1), (key1597, 1), (key1296, -2), (key1799, -2), (key1303, 1), (key1791, 1), (key1573, -2), (key1296, 1), (key1788, 1), (key1772, -1), (key1845, -1), (key1775, 1), (key1840, 1), (key1337, 1), (key1845, 1), (key1340, -1), (key1840, -1), (key1546, -1), (key1668, -1), (key1316, 1), (key1826, 1), (key1546, 1), (key1655, 1), (key1316, -1), (key1813, -1)]

theorem rawRowCheck5706 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form1 = rawRow5706 := by decide +kernel

def row5706 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5706 : row5706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5706 := by decide +kernel

theorem rowEval5706 (x : Key → ℝ) : Integer.Sparse.eval row5706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5706, Integer.Sparse.eval_collectBalanced, rawRowCheck5706]

def rawRow5707 : Integer.Sparse Key := [(key1467, -1), (key1455, -1), (key1458, 2), (key1448, -1), (key1424, -1), (key1467, 2), (key1391, 2), (key1458, -1), (key1398, -1), (key1424, 2), (key1455, -1), (key1391, -1), (key1799, 1), (key1788, 1), (key1791, -2), (key1597, 1), (key1573, 1), (key1799, -2), (key1296, -2), (key1791, 1), (key1303, 1), (key1573, -2), (key1788, 1), (key1296, 1), (key1845, -1), (key1772, -1), (key1840, 1), (key1775, 1), (key1845, 1), (key1337, 1), (key1840, -1), (key1340, -1), (key1668, -1), (key1546, -1), (key1826, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, -1), (key1316, -1)]

theorem rawRowCheck5707 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form1 = rawRow5707 := by decide +kernel

def row5707 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5707 : row5707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5707 := by decide +kernel

theorem rowEval5707 (x : Key → ℝ) : Integer.Sparse.eval row5707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5707, Integer.Sparse.eval_collectBalanced, rawRowCheck5707]

def rawRow5708 : Integer.Sparse Key := [(key1458, -1), (key1467, -1), (key1455, 2), (key1458, -1), (key1467, -1), (key1398, 2), (key1448, 2), (key1391, -1), (key1424, -1), (key1455, 2), (key1391, -1), (key1424, -1), (key1791, 1), (key1799, 1), (key1788, -2), (key1791, 1), (key1799, 1), (key1303, -2), (key1597, -2), (key1296, 1), (key1573, 1), (key1788, -2), (key1296, 1), (key1573, 1), (key1775, -1), (key1826, -1), (key1772, 1), (key1813, 1), (key1340, 1), (key1668, 1), (key1337, -1), (key1655, -1), (key1775, -1), (key1826, -1), (key1340, 1), (key1668, 1), (key1772, 1), (key1813, 1), (key1337, -1), (key1655, -1)]

theorem rawRowCheck5708 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form1 = rawRow5708 := by decide +kernel

def row5708 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

theorem rowCheck5708 : row5708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5708 := by decide +kernel

theorem rowEval5708 (x : Key → ℝ) : Integer.Sparse.eval row5708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5708, Integer.Sparse.eval_collectBalanced, rawRowCheck5708]

def rawRow5709 : Integer.Sparse Key := [(key1467, -1), (key1458, -1), (key1455, 2), (key1467, -1), (key1458, -1), (key1448, 2), (key1398, 2), (key1424, -1), (key1391, -1), (key1455, 2), (key1424, -1), (key1391, -1), (key1799, 1), (key1791, 1), (key1788, -2), (key1799, 1), (key1791, 1), (key1597, -2), (key1303, -2), (key1573, 1), (key1296, 1), (key1788, -2), (key1573, 1), (key1296, 1), (key1826, -1), (key1775, -1), (key1813, 1), (key1772, 1), (key1668, 1), (key1340, 1), (key1655, -1), (key1337, -1), (key1826, -1), (key1775, -1), (key1668, 1), (key1340, 1), (key1813, 1), (key1772, 1), (key1655, -1), (key1337, -1)]

theorem rawRowCheck5709 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form1 = rawRow5709 := by decide +kernel

def row5709 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1337, -2), (key1340, 2), (key1391, -2), (key1398, 2), (key1424, -2), (key1448, 2), (key1455, 4), (key1458, -2), (key1467, -2), (key1573, 2), (key1597, -2), (key1655, -2), (key1668, 2), (key1772, 2), (key1775, -2), (key1788, -4), (key1791, 2), (key1799, 2), (key1813, 2), (key1826, -2)]

theorem rowCheck5709 : row5709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5709 := by decide +kernel

theorem rowEval5709 (x : Key → ℝ) : Integer.Sparse.eval row5709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5709, Integer.Sparse.eval_collectBalanced, rawRowCheck5709]

def rawRow5710 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1560, 2), (key1573, -1), (key1573, -1), (key1655, 2), (key1655, 2), (key1660, -1), (key1660, -1), (key1597, 2), (key1668, -1), (key1668, -1), (key1316, 1), (key1316, 1), (key1330, -2), (key1424, 1), (key1424, 1), (key1813, -2), (key1813, -2), (key1818, 1), (key1818, 1), (key1448, -2), (key1826, 1), (key1826, 1), (key1337, -1), (key1337, -1), (key1346, 1), (key1346, 1), (key1772, 1), (key1772, 1), (key1781, -1), (key1781, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1467, 1), (key1467, 1), (key1799, -1), (key1799, -1)]

theorem rawRowCheck5710 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form1 = rawRow5710 := by decide +kernel

def row5710 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

theorem rowCheck5710 : row5710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5710 := by decide +kernel

theorem rowEval5710 (x : Key → ℝ) : Integer.Sparse.eval row5710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5710, Integer.Sparse.eval_collectBalanced, rawRowCheck5710]

def rawRow5711 : Integer.Sparse Key := [(key1546, -1), (key1560, -1), (key1546, 2), (key1655, -1), (key1660, -1), (key1573, 2), (key1660, 2), (key1573, -1), (key1655, -1), (key1668, 2), (key1597, -1), (key1668, -1), (key1316, 1), (key1330, 1), (key1316, -2), (key1813, 1), (key1818, 1), (key1424, -2), (key1818, -2), (key1424, 1), (key1813, 1), (key1826, -2), (key1448, 1), (key1826, 1), (key1296, -1), (key1346, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1781, 1), (key1391, -1), (key1772, -1), (key1788, -1), (key1842, -1), (key1455, 1), (key1842, 1), (key1799, 1), (key1845, 1), (key1467, -1), (key1845, -1)]

theorem rawRowCheck5711 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form1 = rawRow5711 := by decide +kernel

def row5711 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5711 : row5711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5711 := by decide +kernel

theorem rowEval5711 (x : Key → ℝ) : Integer.Sparse.eval row5711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5711, Integer.Sparse.eval_collectBalanced, rawRowCheck5711]

def rawRow5712 : Integer.Sparse Key := [(key1560, -1), (key1546, -1), (key1546, 2), (key1660, -1), (key1655, -1), (key1660, 2), (key1573, 2), (key1655, -1), (key1573, -1), (key1668, 2), (key1668, -1), (key1597, -1), (key1330, 1), (key1316, 1), (key1316, -2), (key1818, 1), (key1813, 1), (key1818, -2), (key1424, -2), (key1813, 1), (key1424, 1), (key1826, -2), (key1826, 1), (key1448, 1), (key1346, -1), (key1296, -1), (key1337, 1), (key1296, 1), (key1781, 1), (key1391, 1), (key1772, -1), (key1391, -1), (key1842, -1), (key1788, -1), (key1842, 1), (key1455, 1), (key1845, 1), (key1799, 1), (key1845, -1), (key1467, -1)]

theorem rawRowCheck5712 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form1 = rawRow5712 := by decide +kernel

def row5712 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5712 : row5712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5712 := by decide +kernel

theorem rowEval5712 (x : Key → ℝ) : Integer.Sparse.eval row5712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5712, Integer.Sparse.eval_collectBalanced, rawRowCheck5712]

def rawRow5713 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1597, 2), (key1546, -1), (key1546, -1), (key1655, 2), (key1655, 2), (key1668, -1), (key1668, -1), (key1560, 2), (key1660, -1), (key1660, -1), (key1424, 1), (key1424, 1), (key1448, -2), (key1316, 1), (key1316, 1), (key1813, -2), (key1813, -2), (key1826, 1), (key1826, 1), (key1330, -2), (key1818, 1), (key1818, 1), (key1455, -1), (key1455, -1), (key1467, 1), (key1467, 1), (key1788, 1), (key1788, 1), (key1799, -1), (key1799, -1), (key1337, -1), (key1337, -1), (key1772, 1), (key1772, 1), (key1346, 1), (key1346, 1), (key1781, -1), (key1781, -1)]

theorem rawRowCheck5713 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form1 = rawRow5713 := by decide +kernel

def row5713 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

theorem rowCheck5713 : row5713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5713 := by decide +kernel

theorem rowEval5713 (x : Key → ℝ) : Integer.Sparse.eval row5713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5713, Integer.Sparse.eval_collectBalanced, rawRowCheck5713]

def rawRow5714 : Integer.Sparse Key := [(key1573, -1), (key1597, -1), (key1573, 2), (key1655, -1), (key1668, -1), (key1546, 2), (key1668, 2), (key1546, -1), (key1655, -1), (key1660, 2), (key1560, -1), (key1660, -1), (key1424, 1), (key1448, 1), (key1424, -2), (key1813, 1), (key1826, 1), (key1316, -2), (key1826, -2), (key1316, 1), (key1813, 1), (key1818, -2), (key1330, 1), (key1818, 1), (key1391, -1), (key1467, -1), (key1391, 1), (key1455, 1), (key1296, 1), (key1799, 1), (key1296, -1), (key1788, -1), (key1772, -1), (key1845, -1), (key1337, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1346, -1), (key1842, -1)]

theorem rawRowCheck5714 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form1 = rawRow5714 := by decide +kernel

def row5714 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5714 : row5714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5714 := by decide +kernel

theorem rowEval5714 (x : Key → ℝ) : Integer.Sparse.eval row5714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5714, Integer.Sparse.eval_collectBalanced, rawRowCheck5714]

def rawRow5715 : Integer.Sparse Key := [(key1597, -1), (key1573, -1), (key1573, 2), (key1668, -1), (key1655, -1), (key1668, 2), (key1546, 2), (key1655, -1), (key1546, -1), (key1660, 2), (key1660, -1), (key1560, -1), (key1448, 1), (key1424, 1), (key1424, -2), (key1826, 1), (key1813, 1), (key1826, -2), (key1316, -2), (key1813, 1), (key1316, 1), (key1818, -2), (key1818, 1), (key1330, 1), (key1467, -1), (key1391, -1), (key1455, 1), (key1391, 1), (key1799, 1), (key1296, 1), (key1788, -1), (key1296, -1), (key1845, -1), (key1772, -1), (key1845, 1), (key1337, 1), (key1842, 1), (key1781, 1), (key1842, -1), (key1346, -1)]

theorem rawRowCheck5715 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form1 = rawRow5715 := by decide +kernel

def row5715 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5715 : row5715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5715 := by decide +kernel

theorem rowEval5715 (x : Key → ℝ) : Integer.Sparse.eval row5715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5715, Integer.Sparse.eval_collectBalanced, rawRowCheck5715]

def rawRow5716 : Integer.Sparse Key := [(key1655, -1), (key1660, -1), (key1668, 2), (key1546, -1), (key1560, -1), (key1573, 2), (key1660, 2), (key1597, -1), (key1668, -1), (key1546, 2), (key1573, -1), (key1655, -1), (key1813, 1), (key1818, 1), (key1826, -2), (key1316, 1), (key1330, 1), (key1424, -2), (key1818, -2), (key1448, 1), (key1826, 1), (key1316, -2), (key1424, 1), (key1813, 1), (key1788, -1), (key1842, -1), (key1799, 1), (key1845, 1), (key1455, 1), (key1842, 1), (key1467, -1), (key1845, -1), (key1296, -1), (key1346, -1), (key1391, 1), (key1781, 1), (key1296, 1), (key1337, 1), (key1391, -1), (key1772, -1)]

theorem rawRowCheck5716 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form1 = rawRow5716 := by decide +kernel

def row5716 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5716 : row5716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5716 := by decide +kernel

theorem rowEval5716 (x : Key → ℝ) : Integer.Sparse.eval row5716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5716, Integer.Sparse.eval_collectBalanced, rawRowCheck5716]

def rawRow5717 : Integer.Sparse Key := [(key1660, -1), (key1655, -1), (key1668, 2), (key1560, -1), (key1546, -1), (key1660, 2), (key1573, 2), (key1668, -1), (key1597, -1), (key1546, 2), (key1655, -1), (key1573, -1), (key1818, 1), (key1813, 1), (key1826, -2), (key1330, 1), (key1316, 1), (key1818, -2), (key1424, -2), (key1826, 1), (key1448, 1), (key1316, -2), (key1813, 1), (key1424, 1), (key1842, -1), (key1788, -1), (key1845, 1), (key1799, 1), (key1842, 1), (key1455, 1), (key1845, -1), (key1467, -1), (key1346, -1), (key1296, -1), (key1781, 1), (key1391, 1), (key1337, 1), (key1296, 1), (key1772, -1), (key1391, -1)]

theorem rawRowCheck5717 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form1 = rawRow5717 := by decide +kernel

def row5717 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5717 : row5717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5717 := by decide +kernel

theorem rowEval5717 (x : Key → ℝ) : Integer.Sparse.eval row5717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5717, Integer.Sparse.eval_collectBalanced, rawRowCheck5717]

def rawRow5718 : Integer.Sparse Key := [(key1655, -1), (key1668, -1), (key1660, 2), (key1573, -1), (key1597, -1), (key1546, 2), (key1668, 2), (key1560, -1), (key1660, -1), (key1573, 2), (key1546, -1), (key1655, -1), (key1813, 1), (key1826, 1), (key1818, -2), (key1424, 1), (key1448, 1), (key1316, -2), (key1826, -2), (key1330, 1), (key1818, 1), (key1424, -2), (key1316, 1), (key1813, 1), (key1772, -1), (key1845, -1), (key1781, 1), (key1842, 1), (key1337, 1), (key1845, 1), (key1346, -1), (key1842, -1), (key1391, -1), (key1467, -1), (key1296, 1), (key1799, 1), (key1391, 1), (key1455, 1), (key1296, -1), (key1788, -1)]

theorem rawRowCheck5718 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form1 = rawRow5718 := by decide +kernel

def row5718 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5718 : row5718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5718 := by decide +kernel

theorem rowEval5718 (x : Key → ℝ) : Integer.Sparse.eval row5718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5718, Integer.Sparse.eval_collectBalanced, rawRowCheck5718]

def rawRow5719 : Integer.Sparse Key := [(key1668, -1), (key1655, -1), (key1660, 2), (key1597, -1), (key1573, -1), (key1668, 2), (key1546, 2), (key1660, -1), (key1560, -1), (key1573, 2), (key1655, -1), (key1546, -1), (key1826, 1), (key1813, 1), (key1818, -2), (key1448, 1), (key1424, 1), (key1826, -2), (key1316, -2), (key1818, 1), (key1330, 1), (key1424, -2), (key1813, 1), (key1316, 1), (key1845, -1), (key1772, -1), (key1842, 1), (key1781, 1), (key1845, 1), (key1337, 1), (key1842, -1), (key1346, -1), (key1467, -1), (key1391, -1), (key1799, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, -1), (key1296, -1)]

theorem rawRowCheck5719 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form1 = rawRow5719 := by decide +kernel

def row5719 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5719 : row5719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5719 := by decide +kernel

theorem rowEval5719 (x : Key → ℝ) : Integer.Sparse.eval row5719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5719, Integer.Sparse.eval_collectBalanced, rawRowCheck5719]

def rawRow5720 : Integer.Sparse Key := [(key1660, -1), (key1668, -1), (key1655, 2), (key1660, -1), (key1668, -1), (key1560, 2), (key1597, 2), (key1546, -1), (key1573, -1), (key1655, 2), (key1546, -1), (key1573, -1), (key1818, 1), (key1826, 1), (key1813, -2), (key1818, 1), (key1826, 1), (key1330, -2), (key1448, -2), (key1316, 1), (key1424, 1), (key1813, -2), (key1316, 1), (key1424, 1), (key1781, -1), (key1799, -1), (key1772, 1), (key1788, 1), (key1346, 1), (key1467, 1), (key1337, -1), (key1455, -1), (key1781, -1), (key1799, -1), (key1346, 1), (key1467, 1), (key1772, 1), (key1788, 1), (key1337, -1), (key1455, -1)]

theorem rawRowCheck5720 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form1 = rawRow5720 := by decide +kernel

def row5720 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

theorem rowCheck5720 : row5720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5720 := by decide +kernel

theorem rowEval5720 (x : Key → ℝ) : Integer.Sparse.eval row5720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5720, Integer.Sparse.eval_collectBalanced, rawRowCheck5720]

def rawRow5721 : Integer.Sparse Key := [(key1668, -1), (key1660, -1), (key1655, 2), (key1668, -1), (key1660, -1), (key1597, 2), (key1560, 2), (key1573, -1), (key1546, -1), (key1655, 2), (key1573, -1), (key1546, -1), (key1826, 1), (key1818, 1), (key1813, -2), (key1826, 1), (key1818, 1), (key1448, -2), (key1330, -2), (key1424, 1), (key1316, 1), (key1813, -2), (key1424, 1), (key1316, 1), (key1799, -1), (key1781, -1), (key1788, 1), (key1772, 1), (key1467, 1), (key1346, 1), (key1455, -1), (key1337, -1), (key1799, -1), (key1781, -1), (key1467, 1), (key1346, 1), (key1788, 1), (key1772, 1), (key1455, -1), (key1337, -1)]

theorem rawRowCheck5721 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form1 = rawRow5721 := by decide +kernel

def row5721 : Integer.Sparse Key := [(key1316, 2), (key1330, -2), (key1337, -2), (key1346, 2), (key1424, 2), (key1448, -2), (key1455, -2), (key1467, 2), (key1546, -2), (key1560, 2), (key1573, -2), (key1597, 2), (key1655, 4), (key1660, -2), (key1668, -2), (key1772, 2), (key1781, -2), (key1788, 2), (key1799, -2), (key1813, -4), (key1818, 2), (key1826, 2)]

theorem rowCheck5721 : row5721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5721 := by decide +kernel

theorem rowEval5721 (x : Key → ℝ) : Integer.Sparse.eval row5721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5721, Integer.Sparse.eval_collectBalanced, rawRowCheck5721]

def rawRow5722 : Integer.Sparse Key := [(key1772, -1), (key1775, -1), (key1781, 2), (key1788, -1), (key1791, -1), (key1813, 2), (key1840, 2), (key1818, -1), (key1842, -1), (key1799, 2), (key1826, -1), (key1845, -1), (key1337, 1), (key1340, 1), (key1346, -2), (key1455, 1), (key1458, 1), (key1655, -2), (key1840, -2), (key1660, 1), (key1842, 1), (key1467, -2), (key1668, 1), (key1845, 1), (key1316, -1), (key1340, -1), (key1330, 1), (key1346, 1), (key1546, 1), (key1775, 1), (key1560, -1), (key1781, -1), (key1424, -1), (key1458, -1), (key1573, 1), (key1791, 1), (key1448, 1), (key1467, 1), (key1597, -1), (key1799, -1)]

theorem rawRowCheck5722 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form1 = rawRow5722 := by decide +kernel

def row5722 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5722 : row5722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5722 := by decide +kernel

theorem rowEval5722 (x : Key → ℝ) : Integer.Sparse.eval row5722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5722, Integer.Sparse.eval_collectBalanced, rawRowCheck5722]

def rawRow5723 : Integer.Sparse Key := [(key1775, -1), (key1772, -1), (key1781, 2), (key1791, -1), (key1788, -1), (key1840, 2), (key1813, 2), (key1842, -1), (key1818, -1), (key1799, 2), (key1845, -1), (key1826, -1), (key1340, 1), (key1337, 1), (key1346, -2), (key1458, 1), (key1455, 1), (key1840, -2), (key1655, -2), (key1842, 1), (key1660, 1), (key1467, -2), (key1845, 1), (key1668, 1), (key1340, -1), (key1316, -1), (key1346, 1), (key1330, 1), (key1775, 1), (key1546, 1), (key1781, -1), (key1560, -1), (key1458, -1), (key1424, -1), (key1791, 1), (key1573, 1), (key1467, 1), (key1448, 1), (key1799, -1), (key1597, -1)]

theorem rawRowCheck5723 : GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form1 = rawRow5723 := by decide +kernel

def row5723 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5723 : row5723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5723 := by decide +kernel

theorem rowEval5723 (x : Key → ℝ) : Integer.Sparse.eval row5723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5723, Integer.Sparse.eval_collectBalanced, rawRowCheck5723]

def rawRow5724 : Integer.Sparse Key := [(key1772, -1), (key1781, -1), (key1775, 2), (key1813, -1), (key1818, -1), (key1788, 2), (key1842, 2), (key1791, -1), (key1840, -1), (key1826, 2), (key1799, -1), (key1845, -1), (key1337, 1), (key1346, 1), (key1340, -2), (key1655, 1), (key1660, 1), (key1455, -2), (key1842, -2), (key1458, 1), (key1840, 1), (key1668, -2), (key1467, 1), (key1845, 1), (key1296, -1), (key1346, -1), (key1303, 1), (key1340, 1), (key1391, 1), (key1781, 1), (key1398, -1), (key1775, -1), (key1573, -1), (key1660, -1), (key1424, 1), (key1818, 1), (key1597, 1), (key1668, 1), (key1448, -1), (key1826, -1)]

theorem rawRowCheck5724 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form1 = rawRow5724 := by decide +kernel

def row5724 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5724 : row5724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5724 := by decide +kernel

theorem rowEval5724 (x : Key → ℝ) : Integer.Sparse.eval row5724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5724, Integer.Sparse.eval_collectBalanced, rawRowCheck5724]

def rawRow5725 : Integer.Sparse Key := [(key1781, -1), (key1772, -1), (key1775, 2), (key1818, -1), (key1813, -1), (key1842, 2), (key1788, 2), (key1840, -1), (key1791, -1), (key1826, 2), (key1845, -1), (key1799, -1), (key1346, 1), (key1337, 1), (key1340, -2), (key1660, 1), (key1655, 1), (key1842, -2), (key1455, -2), (key1840, 1), (key1458, 1), (key1668, -2), (key1845, 1), (key1467, 1), (key1346, -1), (key1296, -1), (key1340, 1), (key1303, 1), (key1781, 1), (key1391, 1), (key1775, -1), (key1398, -1), (key1660, -1), (key1573, -1), (key1818, 1), (key1424, 1), (key1668, 1), (key1597, 1), (key1826, -1), (key1448, -1)]

theorem rawRowCheck5725 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form1 = rawRow5725 := by decide +kernel

def row5725 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5725 : row5725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5725 := by decide +kernel

theorem rowEval5725 (x : Key → ℝ) : Integer.Sparse.eval row5725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5725, Integer.Sparse.eval_collectBalanced, rawRowCheck5725]

def rawRow5726 : Integer.Sparse Key := [(key1788, -1), (key1791, -1), (key1799, 2), (key1772, -1), (key1775, -1), (key1813, 2), (key1840, 2), (key1826, -1), (key1845, -1), (key1781, 2), (key1818, -1), (key1842, -1), (key1455, 1), (key1458, 1), (key1467, -2), (key1337, 1), (key1340, 1), (key1655, -2), (key1840, -2), (key1668, 1), (key1845, 1), (key1346, -2), (key1660, 1), (key1842, 1), (key1424, -1), (key1458, -1), (key1448, 1), (key1467, 1), (key1573, 1), (key1791, 1), (key1597, -1), (key1799, -1), (key1316, -1), (key1340, -1), (key1546, 1), (key1775, 1), (key1330, 1), (key1346, 1), (key1560, -1), (key1781, -1)]

theorem rawRowCheck5726 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form1 = rawRow5726 := by decide +kernel

def row5726 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5726 : row5726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5726 := by decide +kernel

theorem rowEval5726 (x : Key → ℝ) : Integer.Sparse.eval row5726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5726, Integer.Sparse.eval_collectBalanced, rawRowCheck5726]

def rawRow5727 : Integer.Sparse Key := [(key1791, -1), (key1788, -1), (key1799, 2), (key1775, -1), (key1772, -1), (key1840, 2), (key1813, 2), (key1845, -1), (key1826, -1), (key1781, 2), (key1842, -1), (key1818, -1), (key1458, 1), (key1455, 1), (key1467, -2), (key1340, 1), (key1337, 1), (key1840, -2), (key1655, -2), (key1845, 1), (key1668, 1), (key1346, -2), (key1842, 1), (key1660, 1), (key1458, -1), (key1424, -1), (key1467, 1), (key1448, 1), (key1791, 1), (key1573, 1), (key1799, -1), (key1597, -1), (key1340, -1), (key1316, -1), (key1775, 1), (key1546, 1), (key1346, 1), (key1330, 1), (key1781, -1), (key1560, -1)]

theorem rawRowCheck5727 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form1 = rawRow5727 := by decide +kernel

def row5727 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5727 : row5727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5727 := by decide +kernel

theorem rowEval5727 (x : Key → ℝ) : Integer.Sparse.eval row5727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5727, Integer.Sparse.eval_collectBalanced, rawRowCheck5727]

def rawRow5728 : Integer.Sparse Key := [(key1791, -1), (key1799, -1), (key1788, 2), (key1840, -1), (key1845, -1), (key1775, 2), (key1826, 2), (key1772, -1), (key1813, -1), (key1842, 2), (key1781, -1), (key1818, -1), (key1458, 1), (key1467, 1), (key1455, -2), (key1840, 1), (key1845, 1), (key1340, -2), (key1668, -2), (key1337, 1), (key1655, 1), (key1842, -2), (key1346, 1), (key1660, 1), (key1398, -1), (key1448, -1), (key1391, 1), (key1424, 1), (key1303, 1), (key1597, 1), (key1296, -1), (key1573, -1), (key1775, -1), (key1826, -1), (key1340, 1), (key1668, 1), (key1781, 1), (key1818, 1), (key1346, -1), (key1660, -1)]

theorem rawRowCheck5728 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form1 = rawRow5728 := by decide +kernel

def row5728 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5728 : row5728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5728 := by decide +kernel

theorem rowEval5728 (x : Key → ℝ) : Integer.Sparse.eval row5728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5728, Integer.Sparse.eval_collectBalanced, rawRowCheck5728]

def rawRow5729 : Integer.Sparse Key := [(key1799, -1), (key1791, -1), (key1788, 2), (key1845, -1), (key1840, -1), (key1826, 2), (key1775, 2), (key1813, -1), (key1772, -1), (key1842, 2), (key1818, -1), (key1781, -1), (key1467, 1), (key1458, 1), (key1455, -2), (key1845, 1), (key1840, 1), (key1668, -2), (key1340, -2), (key1655, 1), (key1337, 1), (key1842, -2), (key1660, 1), (key1346, 1), (key1448, -1), (key1398, -1), (key1424, 1), (key1391, 1), (key1597, 1), (key1303, 1), (key1573, -1), (key1296, -1), (key1826, -1), (key1775, -1), (key1668, 1), (key1340, 1), (key1818, 1), (key1781, 1), (key1660, -1), (key1346, -1)]

theorem rawRowCheck5729 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form1 = rawRow5729 := by decide +kernel

def row5729 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5729 : row5729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5729 := by decide +kernel

theorem rowEval5729 (x : Key → ℝ) : Integer.Sparse.eval row5729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5729, Integer.Sparse.eval_collectBalanced, rawRowCheck5729]

def rawRow5730 : Integer.Sparse Key := [(key1813, -1), (key1818, -1), (key1826, 2), (key1772, -1), (key1781, -1), (key1788, 2), (key1842, 2), (key1799, -1), (key1845, -1), (key1775, 2), (key1791, -1), (key1840, -1), (key1655, 1), (key1660, 1), (key1668, -2), (key1337, 1), (key1346, 1), (key1455, -2), (key1842, -2), (key1467, 1), (key1845, 1), (key1340, -2), (key1458, 1), (key1840, 1), (key1573, -1), (key1660, -1), (key1597, 1), (key1668, 1), (key1424, 1), (key1818, 1), (key1448, -1), (key1826, -1), (key1296, -1), (key1346, -1), (key1391, 1), (key1781, 1), (key1303, 1), (key1340, 1), (key1398, -1), (key1775, -1)]

theorem rawRowCheck5730 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form1 = rawRow5730 := by decide +kernel

def row5730 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5730 : row5730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5730 := by decide +kernel

theorem rowEval5730 (x : Key → ℝ) : Integer.Sparse.eval row5730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5730, Integer.Sparse.eval_collectBalanced, rawRowCheck5730]

def rawRow5731 : Integer.Sparse Key := [(key1818, -1), (key1813, -1), (key1826, 2), (key1781, -1), (key1772, -1), (key1842, 2), (key1788, 2), (key1845, -1), (key1799, -1), (key1775, 2), (key1840, -1), (key1791, -1), (key1660, 1), (key1655, 1), (key1668, -2), (key1346, 1), (key1337, 1), (key1842, -2), (key1455, -2), (key1845, 1), (key1467, 1), (key1340, -2), (key1840, 1), (key1458, 1), (key1660, -1), (key1573, -1), (key1668, 1), (key1597, 1), (key1818, 1), (key1424, 1), (key1826, -1), (key1448, -1), (key1346, -1), (key1296, -1), (key1781, 1), (key1391, 1), (key1340, 1), (key1303, 1), (key1775, -1), (key1398, -1)]

theorem rawRowCheck5731 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form1 = rawRow5731 := by decide +kernel

def row5731 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5731 : row5731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5731 := by decide +kernel

theorem rowEval5731 (x : Key → ℝ) : Integer.Sparse.eval row5731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5731, Integer.Sparse.eval_collectBalanced, rawRowCheck5731]

def rawRow5732 : Integer.Sparse Key := [(key1818, -1), (key1826, -1), (key1813, 2), (key1842, -1), (key1845, -1), (key1781, 2), (key1799, 2), (key1772, -1), (key1788, -1), (key1840, 2), (key1775, -1), (key1791, -1), (key1660, 1), (key1668, 1), (key1655, -2), (key1842, 1), (key1845, 1), (key1346, -2), (key1467, -2), (key1337, 1), (key1455, 1), (key1840, -2), (key1340, 1), (key1458, 1), (key1560, -1), (key1597, -1), (key1546, 1), (key1573, 1), (key1330, 1), (key1448, 1), (key1316, -1), (key1424, -1), (key1781, -1), (key1799, -1), (key1346, 1), (key1467, 1), (key1775, 1), (key1791, 1), (key1340, -1), (key1458, -1)]

theorem rawRowCheck5732 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form1 = rawRow5732 := by decide +kernel

def row5732 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5732 : row5732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5732 := by decide +kernel

theorem rowEval5732 (x : Key → ℝ) : Integer.Sparse.eval row5732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5732, Integer.Sparse.eval_collectBalanced, rawRowCheck5732]

def rawRow5733 : Integer.Sparse Key := [(key1826, -1), (key1818, -1), (key1813, 2), (key1845, -1), (key1842, -1), (key1799, 2), (key1781, 2), (key1788, -1), (key1772, -1), (key1840, 2), (key1791, -1), (key1775, -1), (key1668, 1), (key1660, 1), (key1655, -2), (key1845, 1), (key1842, 1), (key1467, -2), (key1346, -2), (key1455, 1), (key1337, 1), (key1840, -2), (key1458, 1), (key1340, 1), (key1597, -1), (key1560, -1), (key1573, 1), (key1546, 1), (key1448, 1), (key1330, 1), (key1424, -1), (key1316, -1), (key1799, -1), (key1781, -1), (key1467, 1), (key1346, 1), (key1791, 1), (key1775, 1), (key1458, -1), (key1340, -1)]

theorem rawRowCheck5733 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form1 = rawRow5733 := by decide +kernel

def row5733 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5733 : row5733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5733 := by decide +kernel

theorem rowEval5733 (x : Key → ℝ) : Integer.Sparse.eval row5733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5733, Integer.Sparse.eval_collectBalanced, rawRowCheck5733]

def rawRow5734 : Integer.Sparse Key := [(key1840, -1), (key1845, -1), (key1842, 2), (key1791, -1), (key1799, -1), (key1775, 2), (key1826, 2), (key1781, -1), (key1818, -1), (key1788, 2), (key1772, -1), (key1813, -1), (key1840, 1), (key1845, 1), (key1842, -2), (key1458, 1), (key1467, 1), (key1340, -2), (key1668, -2), (key1346, 1), (key1660, 1), (key1455, -2), (key1337, 1), (key1655, 1), (key1775, -1), (key1826, -1), (key1781, 1), (key1818, 1), (key1340, 1), (key1668, 1), (key1346, -1), (key1660, -1), (key1398, -1), (key1448, -1), (key1303, 1), (key1597, 1), (key1391, 1), (key1424, 1), (key1296, -1), (key1573, -1)]

theorem rawRowCheck5734 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form1 = rawRow5734 := by decide +kernel

def row5734 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5734 : row5734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5734 := by decide +kernel

theorem rowEval5734 (x : Key → ℝ) : Integer.Sparse.eval row5734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5734, Integer.Sparse.eval_collectBalanced, rawRowCheck5734]

def rawRow5735 : Integer.Sparse Key := [(key1845, -1), (key1840, -1), (key1842, 2), (key1799, -1), (key1791, -1), (key1826, 2), (key1775, 2), (key1818, -1), (key1781, -1), (key1788, 2), (key1813, -1), (key1772, -1), (key1845, 1), (key1840, 1), (key1842, -2), (key1467, 1), (key1458, 1), (key1668, -2), (key1340, -2), (key1660, 1), (key1346, 1), (key1455, -2), (key1655, 1), (key1337, 1), (key1826, -1), (key1775, -1), (key1818, 1), (key1781, 1), (key1668, 1), (key1340, 1), (key1660, -1), (key1346, -1), (key1448, -1), (key1398, -1), (key1597, 1), (key1303, 1), (key1424, 1), (key1391, 1), (key1573, -1), (key1296, -1)]

theorem rawRowCheck5735 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form1 = rawRow5735 := by decide +kernel

def row5735 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1337, 1), (key1340, -1), (key1391, 1), (key1398, -1), (key1424, 1), (key1448, -1), (key1455, -2), (key1458, 1), (key1467, 1), (key1573, -1), (key1597, 1), (key1655, 1), (key1668, -1), (key1772, -1), (key1775, 1), (key1788, 2), (key1791, -1), (key1799, -1), (key1813, -1), (key1826, 1)]

theorem rowCheck5735 : row5735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5735 := by decide +kernel

theorem rowEval5735 (x : Key → ℝ) : Integer.Sparse.eval row5735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5735, Integer.Sparse.eval_collectBalanced, rawRowCheck5735]

def rawRow5736 : Integer.Sparse Key := [(key1842, -1), (key1845, -1), (key1840, 2), (key1818, -1), (key1826, -1), (key1781, 2), (key1799, 2), (key1775, -1), (key1791, -1), (key1813, 2), (key1772, -1), (key1788, -1), (key1842, 1), (key1845, 1), (key1840, -2), (key1660, 1), (key1668, 1), (key1346, -2), (key1467, -2), (key1340, 1), (key1458, 1), (key1655, -2), (key1337, 1), (key1455, 1), (key1781, -1), (key1799, -1), (key1775, 1), (key1791, 1), (key1346, 1), (key1467, 1), (key1340, -1), (key1458, -1), (key1560, -1), (key1597, -1), (key1330, 1), (key1448, 1), (key1546, 1), (key1573, 1), (key1316, -1), (key1424, -1)]

theorem rawRowCheck5736 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form1 = rawRow5736 := by decide +kernel

def row5736 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5736 : row5736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5736 := by decide +kernel

theorem rowEval5736 (x : Key → ℝ) : Integer.Sparse.eval row5736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5736, Integer.Sparse.eval_collectBalanced, rawRowCheck5736]

def rawRow5737 : Integer.Sparse Key := [(key1845, -1), (key1842, -1), (key1840, 2), (key1826, -1), (key1818, -1), (key1799, 2), (key1781, 2), (key1791, -1), (key1775, -1), (key1813, 2), (key1788, -1), (key1772, -1), (key1845, 1), (key1842, 1), (key1840, -2), (key1668, 1), (key1660, 1), (key1467, -2), (key1346, -2), (key1458, 1), (key1340, 1), (key1655, -2), (key1455, 1), (key1337, 1), (key1799, -1), (key1781, -1), (key1791, 1), (key1775, 1), (key1467, 1), (key1346, 1), (key1458, -1), (key1340, -1), (key1597, -1), (key1560, -1), (key1448, 1), (key1330, 1), (key1573, 1), (key1546, 1), (key1424, -1), (key1316, -1)]

theorem rawRowCheck5737 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form1 = rawRow5737 := by decide +kernel

def row5737 : Integer.Sparse Key := [(key1316, -1), (key1330, 1), (key1337, 1), (key1346, -1), (key1424, -1), (key1448, 1), (key1455, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, 1), (key1597, -1), (key1655, -2), (key1660, 1), (key1668, 1), (key1772, -1), (key1781, 1), (key1788, -1), (key1799, 1), (key1813, 2), (key1818, -1), (key1826, -1)]

theorem rowCheck5737 : row5737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5737 := by decide +kernel

theorem rowEval5737 (x : Key → ℝ) : Integer.Sparse.eval row5737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5737, Integer.Sparse.eval_collectBalanced, rawRowCheck5737]

def rawRow5738 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2674, 2), (key2786, -1), (key2786, -1), (key2794, 2), (key2794, 2), (key2796, -1), (key2796, -1), (key2939, 2), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2619, -2), (key2809, 1), (key2809, 1), (key2829, -2), (key2829, -2), (key2832, 1), (key2832, 1), (key2951, -2), (key2961, 1), (key2961, 1), (key2640, -1), (key2640, -1), (key2642, 1), (key2642, 1), (key2726, 1), (key2726, 1), (key2729, -1), (key2729, -1), (key2860, -1), (key2860, -1), (key2870, 1), (key2870, 1), (key2977, 1), (key2977, 1), (key2984, -1), (key2984, -1)]

theorem rawRowCheck5738 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form2 = rawRow5738 := by decide +kernel

def row5738 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5738 : row5738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5738 := by decide +kernel

theorem rowEval5738 (x : Key → ℝ) : Integer.Sparse.eval row5738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5738, Integer.Sparse.eval_collectBalanced, rawRowCheck5738]

def rawRow5739 : Integer.Sparse Key := [(key2671, -1), (key2674, -1), (key2671, 2), (key2794, -1), (key2796, -1), (key2786, 2), (key2796, 2), (key2786, -1), (key2794, -1), (key2944, 2), (key2939, -1), (key2944, -1), (key2616, 1), (key2619, 1), (key2616, -2), (key2829, 1), (key2832, 1), (key2809, -2), (key2832, -2), (key2809, 1), (key2829, 1), (key2961, -2), (key2951, 1), (key2961, 1), (key2632, -1), (key2642, -1), (key2632, 1), (key2640, 1), (key2706, 1), (key2729, 1), (key2706, -1), (key2726, -1), (key2870, -1), (key2883, -1), (key2860, 1), (key2883, 1), (key2984, 1), (key2992, 1), (key2977, -1), (key2992, -1)]

theorem rawRowCheck5739 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form2 = rawRow5739 := by decide +kernel

def row5739 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5739 : row5739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5739 := by decide +kernel

theorem rowEval5739 (x : Key → ℝ) : Integer.Sparse.eval row5739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5739, Integer.Sparse.eval_collectBalanced, rawRowCheck5739]

def rawRow5740 : Integer.Sparse Key := [(key2674, -1), (key2671, -1), (key2671, 2), (key2796, -1), (key2794, -1), (key2796, 2), (key2786, 2), (key2794, -1), (key2786, -1), (key2944, 2), (key2944, -1), (key2939, -1), (key2619, 1), (key2616, 1), (key2616, -2), (key2832, 1), (key2829, 1), (key2832, -2), (key2809, -2), (key2829, 1), (key2809, 1), (key2961, -2), (key2961, 1), (key2951, 1), (key2642, -1), (key2632, -1), (key2640, 1), (key2632, 1), (key2729, 1), (key2706, 1), (key2726, -1), (key2706, -1), (key2883, -1), (key2870, -1), (key2883, 1), (key2860, 1), (key2992, 1), (key2984, 1), (key2992, -1), (key2977, -1)]

theorem rawRowCheck5740 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form2 = rawRow5740 := by decide +kernel

def row5740 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5740 : row5740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5740 := by decide +kernel

theorem rowEval5740 (x : Key → ℝ) : Integer.Sparse.eval row5740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5740, Integer.Sparse.eval_collectBalanced, rawRowCheck5740]

def rawRow5741 : Integer.Sparse Key := [(key2786, -1), (key2786, -1), (key2939, 2), (key2671, -1), (key2671, -1), (key2794, 2), (key2794, 2), (key2944, -1), (key2944, -1), (key2674, 2), (key2796, -1), (key2796, -1), (key2809, 1), (key2809, 1), (key2951, -2), (key2616, 1), (key2616, 1), (key2829, -2), (key2829, -2), (key2961, 1), (key2961, 1), (key2619, -2), (key2832, 1), (key2832, 1), (key2860, -1), (key2860, -1), (key2977, 1), (key2977, 1), (key2870, 1), (key2870, 1), (key2984, -1), (key2984, -1), (key2640, -1), (key2640, -1), (key2726, 1), (key2726, 1), (key2642, 1), (key2642, 1), (key2729, -1), (key2729, -1)]

theorem rawRowCheck5741 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form2 = rawRow5741 := by decide +kernel

def row5741 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5741 : row5741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5741 := by decide +kernel

theorem rowEval5741 (x : Key → ℝ) : Integer.Sparse.eval row5741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5741, Integer.Sparse.eval_collectBalanced, rawRowCheck5741]

def rawRow5742 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2786, 2), (key2794, -1), (key2944, -1), (key2671, 2), (key2944, 2), (key2671, -1), (key2794, -1), (key2796, 2), (key2674, -1), (key2796, -1), (key2809, 1), (key2951, 1), (key2809, -2), (key2829, 1), (key2961, 1), (key2616, -2), (key2961, -2), (key2616, 1), (key2829, 1), (key2832, -2), (key2619, 1), (key2832, 1), (key2706, -1), (key2977, -1), (key2706, 1), (key2860, 1), (key2632, 1), (key2984, 1), (key2632, -1), (key2870, -1), (key2726, -1), (key2992, -1), (key2640, 1), (key2992, 1), (key2729, 1), (key2883, 1), (key2642, -1), (key2883, -1)]

theorem rawRowCheck5742 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form2 = rawRow5742 := by decide +kernel

def row5742 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5742 : row5742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5742 := by decide +kernel

theorem rowEval5742 (x : Key → ℝ) : Integer.Sparse.eval row5742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5742, Integer.Sparse.eval_collectBalanced, rawRowCheck5742]

def rawRow5743 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2786, 2), (key2944, -1), (key2794, -1), (key2944, 2), (key2671, 2), (key2794, -1), (key2671, -1), (key2796, 2), (key2796, -1), (key2674, -1), (key2951, 1), (key2809, 1), (key2809, -2), (key2961, 1), (key2829, 1), (key2961, -2), (key2616, -2), (key2829, 1), (key2616, 1), (key2832, -2), (key2832, 1), (key2619, 1), (key2977, -1), (key2706, -1), (key2860, 1), (key2706, 1), (key2984, 1), (key2632, 1), (key2870, -1), (key2632, -1), (key2992, -1), (key2726, -1), (key2992, 1), (key2640, 1), (key2883, 1), (key2729, 1), (key2883, -1), (key2642, -1)]

theorem rawRowCheck5743 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form2 = rawRow5743 := by decide +kernel

def row5743 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5743 : row5743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5743 := by decide +kernel

theorem rowEval5743 (x : Key → ℝ) : Integer.Sparse.eval row5743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5743, Integer.Sparse.eval_collectBalanced, rawRowCheck5743]

def rawRow5744 : Integer.Sparse Key := [(key2794, -1), (key2796, -1), (key2944, 2), (key2671, -1), (key2674, -1), (key2786, 2), (key2796, 2), (key2939, -1), (key2944, -1), (key2671, 2), (key2786, -1), (key2794, -1), (key2829, 1), (key2832, 1), (key2961, -2), (key2616, 1), (key2619, 1), (key2809, -2), (key2832, -2), (key2951, 1), (key2961, 1), (key2616, -2), (key2809, 1), (key2829, 1), (key2870, -1), (key2883, -1), (key2984, 1), (key2992, 1), (key2860, 1), (key2883, 1), (key2977, -1), (key2992, -1), (key2632, -1), (key2642, -1), (key2706, 1), (key2729, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2726, -1)]

theorem rawRowCheck5744 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form2 = rawRow5744 := by decide +kernel

def row5744 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5744 : row5744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5744 := by decide +kernel

theorem rowEval5744 (x : Key → ℝ) : Integer.Sparse.eval row5744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5744, Integer.Sparse.eval_collectBalanced, rawRowCheck5744]

def rawRow5745 : Integer.Sparse Key := [(key2796, -1), (key2794, -1), (key2944, 2), (key2674, -1), (key2671, -1), (key2796, 2), (key2786, 2), (key2944, -1), (key2939, -1), (key2671, 2), (key2794, -1), (key2786, -1), (key2832, 1), (key2829, 1), (key2961, -2), (key2619, 1), (key2616, 1), (key2832, -2), (key2809, -2), (key2961, 1), (key2951, 1), (key2616, -2), (key2829, 1), (key2809, 1), (key2883, -1), (key2870, -1), (key2992, 1), (key2984, 1), (key2883, 1), (key2860, 1), (key2992, -1), (key2977, -1), (key2642, -1), (key2632, -1), (key2729, 1), (key2706, 1), (key2640, 1), (key2632, 1), (key2726, -1), (key2706, -1)]

theorem rawRowCheck5745 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form2 = rawRow5745 := by decide +kernel

def row5745 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5745 : row5745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5745 := by decide +kernel

theorem rowEval5745 (x : Key → ℝ) : Integer.Sparse.eval row5745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5745, Integer.Sparse.eval_collectBalanced, rawRowCheck5745]

def rawRow5746 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2796, 2), (key2786, -1), (key2939, -1), (key2671, 2), (key2944, 2), (key2674, -1), (key2796, -1), (key2786, 2), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2832, -2), (key2809, 1), (key2951, 1), (key2616, -2), (key2961, -2), (key2619, 1), (key2832, 1), (key2809, -2), (key2616, 1), (key2829, 1), (key2726, -1), (key2992, -1), (key2729, 1), (key2883, 1), (key2640, 1), (key2992, 1), (key2642, -1), (key2883, -1), (key2706, -1), (key2977, -1), (key2632, 1), (key2984, 1), (key2706, 1), (key2860, 1), (key2632, -1), (key2870, -1)]

theorem rawRowCheck5746 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form2 = rawRow5746 := by decide +kernel

def row5746 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5746 : row5746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5746 := by decide +kernel

theorem rowEval5746 (x : Key → ℝ) : Integer.Sparse.eval row5746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5746, Integer.Sparse.eval_collectBalanced, rawRowCheck5746]

def rawRow5747 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2796, 2), (key2939, -1), (key2786, -1), (key2944, 2), (key2671, 2), (key2796, -1), (key2674, -1), (key2786, 2), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2832, -2), (key2951, 1), (key2809, 1), (key2961, -2), (key2616, -2), (key2832, 1), (key2619, 1), (key2809, -2), (key2829, 1), (key2616, 1), (key2992, -1), (key2726, -1), (key2883, 1), (key2729, 1), (key2992, 1), (key2640, 1), (key2883, -1), (key2642, -1), (key2977, -1), (key2706, -1), (key2984, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, -1), (key2632, -1)]

theorem rawRowCheck5747 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form2 = rawRow5747 := by decide +kernel

def row5747 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck5747 : row5747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5747 := by decide +kernel

theorem rowEval5747 (x : Key → ℝ) : Integer.Sparse.eval row5747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5747, Integer.Sparse.eval_collectBalanced, rawRowCheck5747]

def rawRow5748 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2794, 2), (key2796, -1), (key2944, -1), (key2674, 2), (key2939, 2), (key2671, -1), (key2786, -1), (key2794, 2), (key2671, -1), (key2786, -1), (key2832, 1), (key2961, 1), (key2829, -2), (key2832, 1), (key2961, 1), (key2619, -2), (key2951, -2), (key2616, 1), (key2809, 1), (key2829, -2), (key2616, 1), (key2809, 1), (key2729, -1), (key2984, -1), (key2726, 1), (key2870, 1), (key2642, 1), (key2977, 1), (key2640, -1), (key2860, -1), (key2729, -1), (key2984, -1), (key2642, 1), (key2977, 1), (key2726, 1), (key2870, 1), (key2640, -1), (key2860, -1)]

theorem rawRowCheck5748 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form2 = rawRow5748 := by decide +kernel

def row5748 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5748 : row5748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5748 := by decide +kernel

theorem rowEval5748 (x : Key → ℝ) : Integer.Sparse.eval row5748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5748, Integer.Sparse.eval_collectBalanced, rawRowCheck5748]

def rawRow5749 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2794, 2), (key2944, -1), (key2796, -1), (key2939, 2), (key2674, 2), (key2786, -1), (key2671, -1), (key2794, 2), (key2786, -1), (key2671, -1), (key2961, 1), (key2832, 1), (key2829, -2), (key2961, 1), (key2832, 1), (key2951, -2), (key2619, -2), (key2809, 1), (key2616, 1), (key2829, -2), (key2809, 1), (key2616, 1), (key2984, -1), (key2729, -1), (key2870, 1), (key2726, 1), (key2977, 1), (key2642, 1), (key2860, -1), (key2640, -1), (key2984, -1), (key2729, -1), (key2977, 1), (key2642, 1), (key2870, 1), (key2726, 1), (key2860, -1), (key2640, -1)]

theorem rawRowCheck5749 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form2 = rawRow5749 := by decide +kernel

def row5749 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck5749 : row5749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5749 := by decide +kernel

theorem rowEval5749 (x : Key → ℝ) : Integer.Sparse.eval row5749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5749, Integer.Sparse.eval_collectBalanced, rawRowCheck5749]

def rawRow5750 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2738, 2), (key2809, -1), (key2809, -1), (key2860, 2), (key2860, 2), (key2898, -1), (key2898, -1), (key2951, 2), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2649, -2), (key2786, 1), (key2786, 1), (key2870, -2), (key2870, -2), (key2905, 1), (key2905, 1), (key2939, -2), (key2984, 1), (key2984, 1), (key2640, -1), (key2640, -1), (key2654, 1), (key2654, 1), (key2726, 1), (key2726, 1), (key2748, -1), (key2748, -1), (key2794, -1), (key2794, -1), (key2829, 1), (key2829, 1), (key2944, 1), (key2944, 1), (key2961, -1), (key2961, -1)]

theorem rawRowCheck5750 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form2 = rawRow5750 := by decide +kernel

def row5750 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck5750 : row5750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5750 := by decide +kernel

theorem rowEval5750 (x : Key → ℝ) : Integer.Sparse.eval row5750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5750, Integer.Sparse.eval_collectBalanced, rawRowCheck5750]

def rawRow5751 : Integer.Sparse Key := [(key2706, -1), (key2738, -1), (key2706, 2), (key2860, -1), (key2898, -1), (key2809, 2), (key2898, 2), (key2809, -1), (key2860, -1), (key2977, 2), (key2951, -1), (key2977, -1), (key2632, 1), (key2649, 1), (key2632, -2), (key2870, 1), (key2905, 1), (key2786, -2), (key2905, -2), (key2786, 1), (key2870, 1), (key2984, -2), (key2939, 1), (key2984, 1), (key2616, -1), (key2654, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2748, 1), (key2671, -1), (key2726, -1), (key2829, -1), (key2913, -1), (key2794, 1), (key2913, 1), (key2961, 1), (key2992, 1), (key2944, -1), (key2992, -1)]

theorem rawRowCheck5751 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form2 = rawRow5751 := by decide +kernel

def row5751 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5751 : row5751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5751 := by decide +kernel

theorem rowEval5751 (x : Key → ℝ) : Integer.Sparse.eval row5751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5751, Integer.Sparse.eval_collectBalanced, rawRowCheck5751]

def rawRow5752 : Integer.Sparse Key := [(key2738, -1), (key2706, -1), (key2706, 2), (key2898, -1), (key2860, -1), (key2898, 2), (key2809, 2), (key2860, -1), (key2809, -1), (key2977, 2), (key2977, -1), (key2951, -1), (key2649, 1), (key2632, 1), (key2632, -2), (key2905, 1), (key2870, 1), (key2905, -2), (key2786, -2), (key2870, 1), (key2786, 1), (key2984, -2), (key2984, 1), (key2939, 1), (key2654, -1), (key2616, -1), (key2640, 1), (key2616, 1), (key2748, 1), (key2671, 1), (key2726, -1), (key2671, -1), (key2913, -1), (key2829, -1), (key2913, 1), (key2794, 1), (key2992, 1), (key2961, 1), (key2992, -1), (key2944, -1)]

theorem rawRowCheck5752 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form2 = rawRow5752 := by decide +kernel

def row5752 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5752 : row5752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5752 := by decide +kernel

theorem rowEval5752 (x : Key → ℝ) : Integer.Sparse.eval row5752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5752, Integer.Sparse.eval_collectBalanced, rawRowCheck5752]

def rawRow5753 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2951, 2), (key2706, -1), (key2706, -1), (key2860, 2), (key2860, 2), (key2977, -1), (key2977, -1), (key2738, 2), (key2898, -1), (key2898, -1), (key2786, 1), (key2786, 1), (key2939, -2), (key2632, 1), (key2632, 1), (key2870, -2), (key2870, -2), (key2984, 1), (key2984, 1), (key2649, -2), (key2905, 1), (key2905, 1), (key2794, -1), (key2794, -1), (key2944, 1), (key2944, 1), (key2829, 1), (key2829, 1), (key2961, -1), (key2961, -1), (key2640, -1), (key2640, -1), (key2726, 1), (key2726, 1), (key2654, 1), (key2654, 1), (key2748, -1), (key2748, -1)]

theorem rawRowCheck5753 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form2 = rawRow5753 := by decide +kernel

def row5753 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck5753 : row5753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5753 := by decide +kernel

theorem rowEval5753 (x : Key → ℝ) : Integer.Sparse.eval row5753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5753, Integer.Sparse.eval_collectBalanced, rawRowCheck5753]

def rawRow5754 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2809, 2), (key2860, -1), (key2977, -1), (key2706, 2), (key2977, 2), (key2706, -1), (key2860, -1), (key2898, 2), (key2738, -1), (key2898, -1), (key2786, 1), (key2939, 1), (key2786, -2), (key2870, 1), (key2984, 1), (key2632, -2), (key2984, -2), (key2632, 1), (key2870, 1), (key2905, -2), (key2649, 1), (key2905, 1), (key2671, -1), (key2944, -1), (key2671, 1), (key2794, 1), (key2616, 1), (key2961, 1), (key2616, -1), (key2829, -1), (key2726, -1), (key2992, -1), (key2640, 1), (key2992, 1), (key2748, 1), (key2913, 1), (key2654, -1), (key2913, -1)]

theorem rawRowCheck5754 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form2 = rawRow5754 := by decide +kernel

def row5754 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5754 : row5754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5754 := by decide +kernel

theorem rowEval5754 (x : Key → ℝ) : Integer.Sparse.eval row5754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5754, Integer.Sparse.eval_collectBalanced, rawRowCheck5754]

def rawRow5755 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2809, 2), (key2977, -1), (key2860, -1), (key2977, 2), (key2706, 2), (key2860, -1), (key2706, -1), (key2898, 2), (key2898, -1), (key2738, -1), (key2939, 1), (key2786, 1), (key2786, -2), (key2984, 1), (key2870, 1), (key2984, -2), (key2632, -2), (key2870, 1), (key2632, 1), (key2905, -2), (key2905, 1), (key2649, 1), (key2944, -1), (key2671, -1), (key2794, 1), (key2671, 1), (key2961, 1), (key2616, 1), (key2829, -1), (key2616, -1), (key2992, -1), (key2726, -1), (key2992, 1), (key2640, 1), (key2913, 1), (key2748, 1), (key2913, -1), (key2654, -1)]

theorem rawRowCheck5755 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form2 = rawRow5755 := by decide +kernel

def row5755 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5755 : row5755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5755 := by decide +kernel

theorem rowEval5755 (x : Key → ℝ) : Integer.Sparse.eval row5755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5755, Integer.Sparse.eval_collectBalanced, rawRowCheck5755]

def rawRow5756 : Integer.Sparse Key := [(key2860, -1), (key2898, -1), (key2977, 2), (key2706, -1), (key2738, -1), (key2809, 2), (key2898, 2), (key2951, -1), (key2977, -1), (key2706, 2), (key2809, -1), (key2860, -1), (key2870, 1), (key2905, 1), (key2984, -2), (key2632, 1), (key2649, 1), (key2786, -2), (key2905, -2), (key2939, 1), (key2984, 1), (key2632, -2), (key2786, 1), (key2870, 1), (key2829, -1), (key2913, -1), (key2961, 1), (key2992, 1), (key2794, 1), (key2913, 1), (key2944, -1), (key2992, -1), (key2616, -1), (key2654, -1), (key2671, 1), (key2748, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2726, -1)]

theorem rawRowCheck5756 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form2 = rawRow5756 := by decide +kernel

def row5756 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5756 : row5756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5756 := by decide +kernel

theorem rowEval5756 (x : Key → ℝ) : Integer.Sparse.eval row5756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5756, Integer.Sparse.eval_collectBalanced, rawRowCheck5756]

def rawRow5757 : Integer.Sparse Key := [(key2898, -1), (key2860, -1), (key2977, 2), (key2738, -1), (key2706, -1), (key2898, 2), (key2809, 2), (key2977, -1), (key2951, -1), (key2706, 2), (key2860, -1), (key2809, -1), (key2905, 1), (key2870, 1), (key2984, -2), (key2649, 1), (key2632, 1), (key2905, -2), (key2786, -2), (key2984, 1), (key2939, 1), (key2632, -2), (key2870, 1), (key2786, 1), (key2913, -1), (key2829, -1), (key2992, 1), (key2961, 1), (key2913, 1), (key2794, 1), (key2992, -1), (key2944, -1), (key2654, -1), (key2616, -1), (key2748, 1), (key2671, 1), (key2640, 1), (key2616, 1), (key2726, -1), (key2671, -1)]

theorem rawRowCheck5757 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form2 = rawRow5757 := by decide +kernel

def row5757 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5757 : row5757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5757 := by decide +kernel

theorem rowEval5757 (x : Key → ℝ) : Integer.Sparse.eval row5757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5757, Integer.Sparse.eval_collectBalanced, rawRowCheck5757]

def rawRow5758 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2898, 2), (key2809, -1), (key2951, -1), (key2706, 2), (key2977, 2), (key2738, -1), (key2898, -1), (key2809, 2), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2905, -2), (key2786, 1), (key2939, 1), (key2632, -2), (key2984, -2), (key2649, 1), (key2905, 1), (key2786, -2), (key2632, 1), (key2870, 1), (key2726, -1), (key2992, -1), (key2748, 1), (key2913, 1), (key2640, 1), (key2992, 1), (key2654, -1), (key2913, -1), (key2671, -1), (key2944, -1), (key2616, 1), (key2961, 1), (key2671, 1), (key2794, 1), (key2616, -1), (key2829, -1)]

theorem rawRowCheck5758 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form2 = rawRow5758 := by decide +kernel

def row5758 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5758 : row5758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5758 := by decide +kernel

theorem rowEval5758 (x : Key → ℝ) : Integer.Sparse.eval row5758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5758, Integer.Sparse.eval_collectBalanced, rawRowCheck5758]

def rawRow5759 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2898, 2), (key2951, -1), (key2809, -1), (key2977, 2), (key2706, 2), (key2898, -1), (key2738, -1), (key2809, 2), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2905, -2), (key2939, 1), (key2786, 1), (key2984, -2), (key2632, -2), (key2905, 1), (key2649, 1), (key2786, -2), (key2870, 1), (key2632, 1), (key2992, -1), (key2726, -1), (key2913, 1), (key2748, 1), (key2992, 1), (key2640, 1), (key2913, -1), (key2654, -1), (key2944, -1), (key2671, -1), (key2961, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

theorem rawRowCheck5759 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form2 = rawRow5759 := by decide +kernel

def row5759 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck5759 : row5759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5759 := by decide +kernel

theorem rowEval5759 (x : Key → ℝ) : Integer.Sparse.eval row5759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5759, Integer.Sparse.eval_collectBalanced, rawRowCheck5759]

end MUB6.Certificate.GramRows

end OAI
