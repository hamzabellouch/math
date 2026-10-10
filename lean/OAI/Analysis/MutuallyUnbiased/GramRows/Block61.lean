import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4736 : Integer.Sparse Key := [(key1742, -2), (key1878, -2), (key1742, -2), (key1742, 1), (key1878, 1), (key1514, 1), (key1878, 1), (key1514, 1), (key1742, 1), (key1724, 2), (key1868, 2), (key1724, 2), (key1724, -1), (key1868, -1), (key1375, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1717, -1), (key1862, -1), (key1491, -1), (key1862, -1), (key1491, -1), (key1717, -1), (key1717, 1), (key1862, 1), (key1365, 1), (key1862, 1), (key1365, 1), (key1717, 1)]

theorem rawRowCheck4736 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form12 = rawRow4736 := by decide +kernel

def row4736 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

theorem rowCheck4736 : row4736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4736 := by decide +kernel

theorem rowEval4736 (x : Key → ℝ) : Integer.Sparse.eval row4736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form12) x := by
  rw [rowCheck4736, Integer.Sparse.eval_collectBalanced, rawRowCheck4736]

def rawRow4737 : Integer.Sparse Key := [(key1878, -2), (key1742, -2), (key1742, -2), (key1878, 1), (key1742, 1), (key1878, 1), (key1514, 1), (key1742, 1), (key1514, 1), (key1868, 2), (key1724, 2), (key1724, 2), (key1868, -1), (key1724, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1375, -1), (key1862, -1), (key1717, -1), (key1862, -1), (key1491, -1), (key1717, -1), (key1491, -1), (key1862, 1), (key1717, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1365, 1)]

theorem rawRowCheck4737 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form12 = rawRow4737 := by decide +kernel

def row4737 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

theorem rowCheck4737 : row4737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4737 := by decide +kernel

theorem rowEval4737 (x : Key → ℝ) : Integer.Sparse.eval row4737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form12) x := by
  rw [rowCheck4737, Integer.Sparse.eval_collectBalanced, rawRowCheck4737]

def rawRow4738 : Integer.Sparse Key := [(key741, -2), (key742, -2), (key742, -2), (key742, 6), (key900, 2), (key901, 2), (key901, 2), (key901, -2), (key901, -2), (key951, -2), (key913, -6), (key913, 2), (key913, 2), (key954, 2)]

theorem rawRowCheck4738 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form13 = rawRow4738 := by decide +kernel

def row4738 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

theorem rowCheck4738 : row4738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4738 := by decide +kernel

theorem rowEval4738 (x : Key → ℝ) : Integer.Sparse.eval row4738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4738, Integer.Sparse.eval_collectBalanced, rawRowCheck4738]

def rawRow4739 : Integer.Sparse Key := [(key742, -2), (key741, -2), (key742, -2), (key742, 6), (key901, 2), (key900, 2), (key901, 2), (key901, -2), (key951, -2), (key901, -2), (key913, -6), (key913, 2), (key954, 2), (key913, 2)]

theorem rawRowCheck4739 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form13 = rawRow4739 := by decide +kernel

def row4739 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

theorem rowCheck4739 : row4739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4739 := by decide +kernel

theorem rowEval4739 (x : Key → ℝ) : Integer.Sparse.eval row4739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4739, Integer.Sparse.eval_collectBalanced, rawRowCheck4739]

def rawRow4740 : Integer.Sparse Key := [(key742, -2), (key742, -2), (key741, -2), (key742, 6), (key901, 2), (key901, 2), (key900, 2), (key951, -2), (key901, -2), (key901, -2), (key913, -6), (key954, 2), (key913, 2), (key913, 2)]

theorem rawRowCheck4740 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form13 = rawRow4740 := by decide +kernel

def row4740 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

theorem rowCheck4740 : row4740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4740 := by decide +kernel

theorem rowEval4740 (x : Key → ℝ) : Integer.Sparse.eval row4740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4740, Integer.Sparse.eval_collectBalanced, rawRowCheck4740]

def rawRow4741 : Integer.Sparse Key := [(key742, -2), (key742, -2), (key742, -2), (key741, 6), (key951, 2), (key951, 2), (key951, 2), (key900, -2), (key900, -2), (key900, -2), (key954, -6), (key913, 2), (key913, 2), (key913, 2)]

theorem rawRowCheck4741 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form13 = rawRow4741 := by decide +kernel

def row4741 : Integer.Sparse Key := [(key741, 6), (key742, -6), (key900, -6), (key913, 6), (key951, 6), (key954, -6)]

theorem rowCheck4741 : row4741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4741 := by decide +kernel

theorem rowEval4741 (x : Key → ℝ) : Integer.Sparse.eval row4741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4741, Integer.Sparse.eval_collectBalanced, rawRowCheck4741]

def rawRow4742 : Integer.Sparse Key := [(key900, -2), (key901, -2), (key901, -2), (key913, 6), (key741, 2), (key742, 2), (key742, 2), (key913, -2), (key913, -2), (key954, -2), (key742, -6), (key901, 2), (key901, 2), (key951, 2)]

theorem rawRowCheck4742 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form13 = rawRow4742 := by decide +kernel

def row4742 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

theorem rowCheck4742 : row4742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4742 := by decide +kernel

theorem rowEval4742 (x : Key → ℝ) : Integer.Sparse.eval row4742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4742, Integer.Sparse.eval_collectBalanced, rawRowCheck4742]

def rawRow4743 : Integer.Sparse Key := [(key901, -2), (key900, -2), (key901, -2), (key913, 6), (key742, 2), (key741, 2), (key742, 2), (key913, -2), (key954, -2), (key913, -2), (key742, -6), (key901, 2), (key951, 2), (key901, 2)]

theorem rawRowCheck4743 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form13 = rawRow4743 := by decide +kernel

def row4743 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

theorem rowCheck4743 : row4743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4743 := by decide +kernel

theorem rowEval4743 (x : Key → ℝ) : Integer.Sparse.eval row4743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4743, Integer.Sparse.eval_collectBalanced, rawRowCheck4743]

def rawRow4744 : Integer.Sparse Key := [(key901, -2), (key901, -2), (key900, -2), (key913, 6), (key742, 2), (key742, 2), (key741, 2), (key954, -2), (key913, -2), (key913, -2), (key742, -6), (key951, 2), (key901, 2), (key901, 2)]

theorem rawRowCheck4744 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form13 = rawRow4744 := by decide +kernel

def row4744 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

theorem rowCheck4744 : row4744 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4744 := by decide +kernel

theorem rowEval4744 (x : Key → ℝ) : Integer.Sparse.eval row4744 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4744, Integer.Sparse.eval_collectBalanced, rawRowCheck4744]

def rawRow4745 : Integer.Sparse Key := [(key901, -2), (key901, -2), (key913, -2), (key900, 6), (key951, 2), (key951, 2), (key954, 2), (key741, -2), (key900, -2), (key900, -2), (key951, -6), (key742, 2), (key901, 2), (key901, 2)]

theorem rawRowCheck4745 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow4745 := by decide +kernel

def row4745 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

theorem rowCheck4745 : row4745 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4745 := by decide +kernel

theorem rowEval4745 (x : Key → ℝ) : Integer.Sparse.eval row4745 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4745, Integer.Sparse.eval_collectBalanced, rawRowCheck4745]

def rawRow4746 : Integer.Sparse Key := [(key901, -2), (key913, -2), (key901, -2), (key900, 6), (key951, 2), (key954, 2), (key951, 2), (key900, -2), (key741, -2), (key900, -2), (key951, -6), (key901, 2), (key742, 2), (key901, 2)]

theorem rawRowCheck4746 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow4746 := by decide +kernel

def row4746 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

theorem rowCheck4746 : row4746 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4746 := by decide +kernel

theorem rowEval4746 (x : Key → ℝ) : Integer.Sparse.eval row4746 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4746, Integer.Sparse.eval_collectBalanced, rawRowCheck4746]

def rawRow4747 : Integer.Sparse Key := [(key913, -2), (key901, -2), (key901, -2), (key900, 6), (key954, 2), (key951, 2), (key951, 2), (key900, -2), (key900, -2), (key741, -2), (key951, -6), (key901, 2), (key901, 2), (key742, 2)]

theorem rawRowCheck4747 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow4747 := by decide +kernel

def row4747 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

theorem rowCheck4747 : row4747 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4747 := by decide +kernel

theorem rowEval4747 (x : Key → ℝ) : Integer.Sparse.eval row4747 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4747, Integer.Sparse.eval_collectBalanced, rawRowCheck4747]

def rawRow4748 : Integer.Sparse Key := [(key951, -2), (key951, -2), (key951, -2), (key954, 6), (key742, 2), (key742, 2), (key742, 2), (key913, -2), (key913, -2), (key913, -2), (key741, -6), (key900, 2), (key900, 2), (key900, 2)]

theorem rawRowCheck4748 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form13 = rawRow4748 := by decide +kernel

def row4748 : Integer.Sparse Key := [(key741, -6), (key742, 6), (key900, 6), (key913, -6), (key951, -6), (key954, 6)]

theorem rowCheck4748 : row4748 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4748 := by decide +kernel

theorem rowEval4748 (x : Key → ℝ) : Integer.Sparse.eval row4748 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4748, Integer.Sparse.eval_collectBalanced, rawRowCheck4748]

def rawRow4749 : Integer.Sparse Key := [(key951, -2), (key951, -2), (key954, -2), (key951, 6), (key901, 2), (key901, 2), (key913, 2), (key742, -2), (key901, -2), (key901, -2), (key900, -6), (key741, 2), (key900, 2), (key900, 2)]

theorem rawRowCheck4749 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form13 = rawRow4749 := by decide +kernel

def row4749 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

theorem rowCheck4749 : row4749 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4749 := by decide +kernel

theorem rowEval4749 (x : Key → ℝ) : Integer.Sparse.eval row4749 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4749, Integer.Sparse.eval_collectBalanced, rawRowCheck4749]

def rawRow4750 : Integer.Sparse Key := [(key951, -2), (key954, -2), (key951, -2), (key951, 6), (key901, 2), (key913, 2), (key901, 2), (key901, -2), (key742, -2), (key901, -2), (key900, -6), (key900, 2), (key741, 2), (key900, 2)]

theorem rawRowCheck4750 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form13 = rawRow4750 := by decide +kernel

def row4750 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

theorem rowCheck4750 : row4750 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4750 := by decide +kernel

theorem rowEval4750 (x : Key → ℝ) : Integer.Sparse.eval row4750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4750, Integer.Sparse.eval_collectBalanced, rawRowCheck4750]

def rawRow4751 : Integer.Sparse Key := [(key954, -2), (key951, -2), (key951, -2), (key951, 6), (key913, 2), (key901, 2), (key901, 2), (key901, -2), (key901, -2), (key742, -2), (key900, -6), (key900, 2), (key900, 2), (key741, 2)]

theorem rawRowCheck4751 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form13 = rawRow4751 := by decide +kernel

def row4751 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

theorem rowCheck4751 : row4751 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4751 := by decide +kernel

theorem rowEval4751 (x : Key → ℝ) : Integer.Sparse.eval row4751 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4751, Integer.Sparse.eval_collectBalanced, rawRowCheck4751]

def rawRow4752 : Integer.Sparse Key := [(key1280, -2), (key1280, -2), (key1284, -2), (key1280, 2), (key1284, 2), (key1284, 2), (key1703, 2), (key1703, 2), (key1707, 2), (key1703, -1), (key1707, -1), (key1703, -1), (key1757, -1), (key1707, -1), (key1757, -1), (key1854, -2), (key1856, -2), (key1856, -2), (key1854, 1), (key1856, 1), (key1854, 1), (key1887, 1), (key1856, 1), (key1887, 1)]

theorem rawRowCheck4752 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form14 = rawRow4752 := by decide +kernel

def row4752 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

theorem rowCheck4752 : row4752 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4752 := by decide +kernel

theorem rowEval4752 (x : Key → ℝ) : Integer.Sparse.eval row4752 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4752, Integer.Sparse.eval_collectBalanced, rawRowCheck4752]

def rawRow4753 : Integer.Sparse Key := [(key1280, -2), (key1284, -2), (key1280, -2), (key1284, 2), (key1280, 2), (key1284, 2), (key1703, 2), (key1707, 2), (key1703, 2), (key1707, -1), (key1703, -1), (key1757, -1), (key1703, -1), (key1757, -1), (key1707, -1), (key1856, -2), (key1854, -2), (key1856, -2), (key1856, 1), (key1854, 1), (key1887, 1), (key1854, 1), (key1887, 1), (key1856, 1)]

theorem rawRowCheck4753 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form14 = rawRow4753 := by decide +kernel

def row4753 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

theorem rowCheck4753 : row4753 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4753 := by decide +kernel

theorem rowEval4753 (x : Key → ℝ) : Integer.Sparse.eval row4753 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4753, Integer.Sparse.eval_collectBalanced, rawRowCheck4753]

def rawRow4754 : Integer.Sparse Key := [(key1284, -2), (key1280, -2), (key1280, -2), (key1284, 2), (key1284, 2), (key1280, 2), (key1707, 2), (key1703, 2), (key1703, 2), (key1757, -1), (key1757, -1), (key1707, -1), (key1707, -1), (key1703, -1), (key1703, -1), (key1856, -2), (key1856, -2), (key1854, -2), (key1887, 1), (key1887, 1), (key1856, 1), (key1856, 1), (key1854, 1), (key1854, 1)]

theorem rawRowCheck4754 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form14 = rawRow4754 := by decide +kernel

def row4754 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

theorem rowCheck4754 : row4754 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4754 := by decide +kernel

theorem rowEval4754 (x : Key → ℝ) : Integer.Sparse.eval row4754 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4754, Integer.Sparse.eval_collectBalanced, rawRowCheck4754]

def rawRow4755 : Integer.Sparse Key := [(key1284, -2), (key1284, -2), (key1284, -2), (key1280, 2), (key1280, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1757, 2), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1887, -2), (key1887, -2), (key1887, -2), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1)]

theorem rawRowCheck4755 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form14 = rawRow4755 := by decide +kernel

def row4755 : Integer.Sparse Key := [(key1280, 6), (key1284, -6), (key1703, -6), (key1757, 6), (key1856, 6), (key1887, -6)]

theorem rowCheck4755 : row4755 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4755 := by decide +kernel

theorem rowEval4755 (x : Key → ℝ) : Integer.Sparse.eval row4755 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4755, Integer.Sparse.eval_collectBalanced, rawRowCheck4755]

def rawRow4756 : Integer.Sparse Key := [(key1703, -2), (key1703, -2), (key1707, -2), (key1854, 2), (key1856, 2), (key1856, 2), (key1280, 2), (key1280, 2), (key1284, 2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1280, -2), (key1284, -2), (key1284, -2), (key1703, 1), (key1707, 1), (key1703, 1), (key1757, 1), (key1707, 1), (key1757, 1)]

theorem rawRowCheck4756 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form14 = rawRow4756 := by decide +kernel

def row4756 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

theorem rowCheck4756 : row4756 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4756 := by decide +kernel

theorem rowEval4756 (x : Key → ℝ) : Integer.Sparse.eval row4756 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4756, Integer.Sparse.eval_collectBalanced, rawRowCheck4756]

def rawRow4757 : Integer.Sparse Key := [(key1703, -2), (key1707, -2), (key1703, -2), (key1856, 2), (key1854, 2), (key1856, 2), (key1280, 2), (key1284, 2), (key1280, 2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1284, -2), (key1280, -2), (key1284, -2), (key1707, 1), (key1703, 1), (key1757, 1), (key1703, 1), (key1757, 1), (key1707, 1)]

theorem rawRowCheck4757 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form14 = rawRow4757 := by decide +kernel

def row4757 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

theorem rowCheck4757 : row4757 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4757 := by decide +kernel

theorem rowEval4757 (x : Key → ℝ) : Integer.Sparse.eval row4757 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4757, Integer.Sparse.eval_collectBalanced, rawRowCheck4757]

def rawRow4758 : Integer.Sparse Key := [(key1707, -2), (key1703, -2), (key1703, -2), (key1856, 2), (key1856, 2), (key1854, 2), (key1284, 2), (key1280, 2), (key1280, 2), (key1887, -1), (key1887, -1), (key1856, -1), (key1856, -1), (key1854, -1), (key1854, -1), (key1284, -2), (key1284, -2), (key1280, -2), (key1757, 1), (key1757, 1), (key1707, 1), (key1707, 1), (key1703, 1), (key1703, 1)]

theorem rawRowCheck4758 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form14 = rawRow4758 := by decide +kernel

def row4758 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

theorem rowCheck4758 : row4758 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4758 := by decide +kernel

theorem rowEval4758 (x : Key → ℝ) : Integer.Sparse.eval row4758 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4758, Integer.Sparse.eval_collectBalanced, rawRowCheck4758]

def rawRow4759 : Integer.Sparse Key := [(key1707, -2), (key1856, -2), (key1856, -2), (key1703, 2), (key1703, 2), (key1854, 2), (key1757, 2), (key1887, 2), (key1887, 2), (key1280, -1), (key1280, -1), (key1703, -1), (key1703, -1), (key1854, -1), (key1854, -1), (key1757, -2), (key1757, -2), (key1887, -2), (key1284, 1), (key1284, 1), (key1707, 1), (key1707, 1), (key1856, 1), (key1856, 1)]

theorem rawRowCheck4759 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4759 := by decide +kernel

def row4759 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

theorem rowCheck4759 : row4759 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4759 := by decide +kernel

theorem rowEval4759 (x : Key → ℝ) : Integer.Sparse.eval row4759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4759, Integer.Sparse.eval_collectBalanced, rawRowCheck4759]

def rawRow4760 : Integer.Sparse Key := [(key1856, -2), (key1707, -2), (key1856, -2), (key1703, 2), (key1854, 2), (key1703, 2), (key1887, 2), (key1757, 2), (key1887, 2), (key1703, -1), (key1854, -1), (key1280, -1), (key1854, -1), (key1280, -1), (key1703, -1), (key1757, -2), (key1887, -2), (key1757, -2), (key1707, 1), (key1856, 1), (key1284, 1), (key1856, 1), (key1284, 1), (key1707, 1)]

theorem rawRowCheck4760 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4760 := by decide +kernel

def row4760 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

theorem rowCheck4760 : row4760 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4760 := by decide +kernel

theorem rowEval4760 (x : Key → ℝ) : Integer.Sparse.eval row4760 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4760, Integer.Sparse.eval_collectBalanced, rawRowCheck4760]

def rawRow4761 : Integer.Sparse Key := [(key1856, -2), (key1856, -2), (key1707, -2), (key1854, 2), (key1703, 2), (key1703, 2), (key1887, 2), (key1887, 2), (key1757, 2), (key1854, -1), (key1703, -1), (key1854, -1), (key1280, -1), (key1703, -1), (key1280, -1), (key1887, -2), (key1757, -2), (key1757, -2), (key1856, 1), (key1707, 1), (key1856, 1), (key1284, 1), (key1707, 1), (key1284, 1)]

theorem rawRowCheck4761 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4761 := by decide +kernel

def row4761 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

theorem rowCheck4761 : row4761 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4761 := by decide +kernel

theorem rowEval4761 (x : Key → ℝ) : Integer.Sparse.eval row4761 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4761, Integer.Sparse.eval_collectBalanced, rawRowCheck4761]

def rawRow4762 : Integer.Sparse Key := [(key1757, -2), (key1757, -2), (key1757, -2), (key1887, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1284, 2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1280, -2), (key1280, -2), (key1280, -2), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1)]

theorem rawRowCheck4762 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form14 = rawRow4762 := by decide +kernel

def row4762 : Integer.Sparse Key := [(key1280, -6), (key1284, 6), (key1703, 6), (key1757, -6), (key1856, -6), (key1887, 6)]

theorem rowCheck4762 : row4762 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4762 := by decide +kernel

theorem rowEval4762 (x : Key → ℝ) : Integer.Sparse.eval row4762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4762, Integer.Sparse.eval_collectBalanced, rawRowCheck4762]

def rawRow4763 : Integer.Sparse Key := [(key1757, -2), (key1887, -2), (key1887, -2), (key1757, 2), (key1757, 2), (key1887, 2), (key1707, 2), (key1856, 2), (key1856, 2), (key1284, -1), (key1284, -1), (key1707, -1), (key1707, -1), (key1856, -1), (key1856, -1), (key1703, -2), (key1703, -2), (key1854, -2), (key1280, 1), (key1280, 1), (key1703, 1), (key1703, 1), (key1854, 1), (key1854, 1)]

theorem rawRowCheck4763 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4763 := by decide +kernel

def row4763 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

theorem rowCheck4763 : row4763 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4763 := by decide +kernel

theorem rowEval4763 (x : Key → ℝ) : Integer.Sparse.eval row4763 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4763, Integer.Sparse.eval_collectBalanced, rawRowCheck4763]

def rawRow4764 : Integer.Sparse Key := [(key1887, -2), (key1757, -2), (key1887, -2), (key1757, 2), (key1887, 2), (key1757, 2), (key1856, 2), (key1707, 2), (key1856, 2), (key1707, -1), (key1856, -1), (key1284, -1), (key1856, -1), (key1284, -1), (key1707, -1), (key1703, -2), (key1854, -2), (key1703, -2), (key1703, 1), (key1854, 1), (key1280, 1), (key1854, 1), (key1280, 1), (key1703, 1)]

theorem rawRowCheck4764 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4764 := by decide +kernel

def row4764 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

theorem rowCheck4764 : row4764 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4764 := by decide +kernel

theorem rowEval4764 (x : Key → ℝ) : Integer.Sparse.eval row4764 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4764, Integer.Sparse.eval_collectBalanced, rawRowCheck4764]

def rawRow4765 : Integer.Sparse Key := [(key1887, -2), (key1887, -2), (key1757, -2), (key1887, 2), (key1757, 2), (key1757, 2), (key1856, 2), (key1856, 2), (key1707, 2), (key1856, -1), (key1707, -1), (key1856, -1), (key1284, -1), (key1707, -1), (key1284, -1), (key1854, -2), (key1703, -2), (key1703, -2), (key1854, 1), (key1703, 1), (key1854, 1), (key1280, 1), (key1703, 1), (key1280, 1)]

theorem rawRowCheck4765 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4765 := by decide +kernel

def row4765 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

theorem rowCheck4765 : row4765 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4765 := by decide +kernel

theorem rowEval4765 (x : Key → ℝ) : Integer.Sparse.eval row4765 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4765, Integer.Sparse.eval_collectBalanced, rawRowCheck4765]

def rawRow4766 : Integer.Sparse Key := [(key1488, -1), (key1493, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1515, -1), (key1493, 2), (key1493, 2), (key1515, 2), (key1714, 1), (key1719, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1743, 1), (key1719, -1), (key1725, -1), (key1719, -1), (key1743, -1), (key1725, -1), (key1743, -1), (key1938, -2), (key1938, -2), (key1950, -2), (key1938, 1), (key1941, 1), (key1938, 1), (key1950, 1), (key1941, 1), (key1950, 1)]

theorem rawRowCheck4766 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form15 = rawRow4766 := by decide +kernel

def row4766 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

theorem rowCheck4766 : row4766 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4766 := by decide +kernel

theorem rowEval4766 (x : Key → ℝ) : Integer.Sparse.eval row4766 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4766, Integer.Sparse.eval_collectBalanced, rawRowCheck4766]

def rawRow4767 : Integer.Sparse Key := [(key1493, -1), (key1488, -1), (key1515, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1493, 2), (key1515, 2), (key1493, 2), (key1719, 1), (key1714, 1), (key1743, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1725, -1), (key1719, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1725, -1), (key1938, -2), (key1950, -2), (key1938, -2), (key1941, 1), (key1938, 1), (key1950, 1), (key1938, 1), (key1950, 1), (key1941, 1)]

theorem rawRowCheck4767 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form15 = rawRow4767 := by decide +kernel

def row4767 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

theorem rowCheck4767 : row4767 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4767 := by decide +kernel

theorem rowEval4767 (x : Key → ℝ) : Integer.Sparse.eval row4767 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4767, Integer.Sparse.eval_collectBalanced, rawRowCheck4767]

def rawRow4768 : Integer.Sparse Key := [(key1515, -1), (key1515, -1), (key1493, -1), (key1493, -1), (key1488, -1), (key1488, -1), (key1515, 2), (key1493, 2), (key1493, 2), (key1743, 1), (key1743, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1), (key1743, -1), (key1743, -1), (key1725, -1), (key1725, -1), (key1719, -1), (key1719, -1), (key1950, -2), (key1938, -2), (key1938, -2), (key1950, 1), (key1950, 1), (key1941, 1), (key1941, 1), (key1938, 1), (key1938, 1)]

theorem rawRowCheck4768 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form15 = rawRow4768 := by decide +kernel

def row4768 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

theorem rowCheck4768 : row4768 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4768 := by decide +kernel

theorem rowEval4768 (x : Key → ℝ) : Integer.Sparse.eval row4768 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4768, Integer.Sparse.eval_collectBalanced, rawRowCheck4768]

def rawRow4769 : Integer.Sparse Key := [(key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1488, 2), (key1488, 2), (key1488, 2), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1941, -2), (key1941, -2), (key1941, -2), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1)]

theorem rawRowCheck4769 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form15 = rawRow4769 := by decide +kernel

def row4769 : Integer.Sparse Key := [(key1488, 6), (key1493, -6), (key1714, -6), (key1725, 6), (key1938, 6), (key1941, -6)]

theorem rowCheck4769 : row4769 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4769 := by decide +kernel

theorem rowEval4769 (x : Key → ℝ) : Integer.Sparse.eval row4769 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4769, Integer.Sparse.eval_collectBalanced, rawRowCheck4769]

def rawRow4770 : Integer.Sparse Key := [(key1714, -1), (key1719, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1488, 1), (key1493, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1515, 1), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1), (key1493, -2), (key1493, -2), (key1515, -2), (key1719, 1), (key1725, 1), (key1719, 1), (key1743, 1), (key1725, 1), (key1743, 1)]

theorem rawRowCheck4770 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form15 = rawRow4770 := by decide +kernel

def row4770 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

theorem rowCheck4770 : row4770 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4770 := by decide +kernel

theorem rowEval4770 (x : Key → ℝ) : Integer.Sparse.eval row4770 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4770, Integer.Sparse.eval_collectBalanced, rawRowCheck4770]

def rawRow4771 : Integer.Sparse Key := [(key1719, -1), (key1714, -1), (key1743, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1493, 1), (key1488, 1), (key1515, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1493, -2), (key1515, -2), (key1493, -2), (key1725, 1), (key1719, 1), (key1743, 1), (key1719, 1), (key1743, 1), (key1725, 1)]

theorem rawRowCheck4771 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form15 = rawRow4771 := by decide +kernel

def row4771 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

theorem rowCheck4771 : row4771 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4771 := by decide +kernel

theorem rowEval4771 (x : Key → ℝ) : Integer.Sparse.eval row4771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4771, Integer.Sparse.eval_collectBalanced, rawRowCheck4771]

def rawRow4772 : Integer.Sparse Key := [(key1743, -1), (key1743, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1515, 1), (key1515, 1), (key1493, 1), (key1493, 1), (key1488, 1), (key1488, 1), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1), (key1515, -2), (key1493, -2), (key1493, -2), (key1743, 1), (key1743, 1), (key1725, 1), (key1725, 1), (key1719, 1), (key1719, 1)]

theorem rawRowCheck4772 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form15 = rawRow4772 := by decide +kernel

def row4772 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

theorem rowCheck4772 : row4772 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4772 := by decide +kernel

theorem rowEval4772 (x : Key → ℝ) : Integer.Sparse.eval row4772 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4772, Integer.Sparse.eval_collectBalanced, rawRowCheck4772]

def rawRow4773 : Integer.Sparse Key := [(key1367, -1), (key1367, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1362, 2), (key1714, 2), (key1714, 2), (key1376, 1), (key1376, 1), (key1725, 1), (key1725, 1), (key1941, 1), (key1941, 1), (key1362, -1), (key1362, -1), (key1488, -1), (key1488, -1), (key1714, -1), (key1714, -1), (key1376, -2), (key1725, -2), (key1725, -2), (key1367, 1), (key1367, 1), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1)]

theorem rawRowCheck4773 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow4773 := by decide +kernel

def row4773 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

theorem rowCheck4773 : row4773 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4773 := by decide +kernel

theorem rowEval4773 (x : Key → ℝ) : Integer.Sparse.eval row4773 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4773, Integer.Sparse.eval_collectBalanced, rawRowCheck4773]

def rawRow4774 : Integer.Sparse Key := [(key1719, -1), (key1938, -1), (key1367, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1714, 2), (key1362, 2), (key1714, 2), (key1725, 1), (key1941, 1), (key1376, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1488, -1), (key1714, -1), (key1362, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1725, -2), (key1376, -2), (key1725, -2), (key1493, 1), (key1719, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1493, 1)]

theorem rawRowCheck4774 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow4774 := by decide +kernel

def row4774 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

theorem rowCheck4774 : row4774 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4774 := by decide +kernel

theorem rowEval4774 (x : Key → ℝ) : Integer.Sparse.eval row4774 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4774, Integer.Sparse.eval_collectBalanced, rawRowCheck4774]

def rawRow4775 : Integer.Sparse Key := [(key1938, -1), (key1719, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1714, 2), (key1714, 2), (key1362, 2), (key1941, 1), (key1725, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1376, 1), (key1714, -1), (key1488, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1362, -1), (key1725, -2), (key1725, -2), (key1376, -2), (key1719, 1), (key1493, 1), (key1719, 1), (key1367, 1), (key1493, 1), (key1367, 1)]

theorem rawRowCheck4775 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow4775 := by decide +kernel

def row4775 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

theorem rowCheck4775 : row4775 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4775 := by decide +kernel

theorem rowEval4775 (x : Key → ℝ) : Integer.Sparse.eval row4775 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4775, Integer.Sparse.eval_collectBalanced, rawRowCheck4775]

def rawRow4776 : Integer.Sparse Key := [(key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1488, -2), (key1488, -2), (key1488, -2), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1)]

theorem rawRowCheck4776 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form15 = rawRow4776 := by decide +kernel

def row4776 : Integer.Sparse Key := [(key1488, -6), (key1493, 6), (key1714, 6), (key1725, -6), (key1938, -6), (key1941, 6)]

theorem rowCheck4776 : row4776 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4776 := by decide +kernel

theorem rowEval4776 (x : Key → ℝ) : Integer.Sparse.eval row4776 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4776, Integer.Sparse.eval_collectBalanced, rawRowCheck4776]

def rawRow4777 : Integer.Sparse Key := [(key1376, -1), (key1376, -1), (key1725, -1), (key1725, -1), (key1941, -1), (key1941, -1), (key1376, 2), (key1725, 2), (key1725, 2), (key1367, 1), (key1367, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1), (key1367, -1), (key1367, -1), (key1493, -1), (key1493, -1), (key1719, -1), (key1719, -1), (key1362, -2), (key1714, -2), (key1714, -2), (key1362, 1), (key1362, 1), (key1488, 1), (key1488, 1), (key1714, 1), (key1714, 1)]

theorem rawRowCheck4777 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form15 = rawRow4777 := by decide +kernel

def row4777 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

theorem rowCheck4777 : row4777 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4777 := by decide +kernel

theorem rowEval4777 (x : Key → ℝ) : Integer.Sparse.eval row4777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4777, Integer.Sparse.eval_collectBalanced, rawRowCheck4777]

def rawRow4778 : Integer.Sparse Key := [(key1725, -1), (key1941, -1), (key1376, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1725, 2), (key1376, 2), (key1725, 2), (key1719, 1), (key1938, 1), (key1367, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1493, -1), (key1719, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1493, -1), (key1714, -2), (key1362, -2), (key1714, -2), (key1488, 1), (key1714, 1), (key1362, 1), (key1714, 1), (key1362, 1), (key1488, 1)]

theorem rawRowCheck4778 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form15 = rawRow4778 := by decide +kernel

def row4778 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

theorem rowCheck4778 : row4778 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4778 := by decide +kernel

theorem rowEval4778 (x : Key → ℝ) : Integer.Sparse.eval row4778 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4778, Integer.Sparse.eval_collectBalanced, rawRowCheck4778]

def rawRow4779 : Integer.Sparse Key := [(key1941, -1), (key1725, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1376, -1), (key1725, 2), (key1725, 2), (key1376, 2), (key1938, 1), (key1719, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1367, 1), (key1719, -1), (key1493, -1), (key1719, -1), (key1367, -1), (key1493, -1), (key1367, -1), (key1714, -2), (key1714, -2), (key1362, -2), (key1714, 1), (key1488, 1), (key1714, 1), (key1362, 1), (key1488, 1), (key1362, 1)]

theorem rawRowCheck4779 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form15 = rawRow4779 := by decide +kernel

def row4779 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

theorem rowCheck4779 : row4779 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4779 := by decide +kernel

theorem rowEval4779 (x : Key → ℝ) : Integer.Sparse.eval row4779 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4779, Integer.Sparse.eval_collectBalanced, rawRowCheck4779]

def rawRow4780 : Integer.Sparse Key := [(key1362, -2), (key1365, -2), (key1365, -2), (key1365, 2), (key1365, 2), (key1375, 2), (key1488, 2), (key1491, 2), (key1491, 2), (key1491, -2), (key1491, -2), (key1514, -2), (key1862, -2), (key1862, -2), (key1868, -2), (key1862, 2), (key1862, 2), (key1878, 2)]

theorem rawRowCheck4780 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form16 = rawRow4780 := by decide +kernel

def row4780 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

theorem rowCheck4780 : row4780 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4780 := by decide +kernel

theorem rowEval4780 (x : Key → ℝ) : Integer.Sparse.eval row4780 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4780, Integer.Sparse.eval_collectBalanced, rawRowCheck4780]

def rawRow4781 : Integer.Sparse Key := [(key1365, -2), (key1362, -2), (key1365, -2), (key1365, 2), (key1375, 2), (key1365, 2), (key1491, 2), (key1488, 2), (key1491, 2), (key1491, -2), (key1514, -2), (key1491, -2), (key1862, -2), (key1868, -2), (key1862, -2), (key1862, 2), (key1878, 2), (key1862, 2)]

theorem rawRowCheck4781 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form16 = rawRow4781 := by decide +kernel

def row4781 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

theorem rowCheck4781 : row4781 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4781 := by decide +kernel

theorem rowEval4781 (x : Key → ℝ) : Integer.Sparse.eval row4781 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4781, Integer.Sparse.eval_collectBalanced, rawRowCheck4781]

def rawRow4782 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1362, -2), (key1375, 2), (key1365, 2), (key1365, 2), (key1491, 2), (key1491, 2), (key1488, 2), (key1514, -2), (key1491, -2), (key1491, -2), (key1868, -2), (key1862, -2), (key1862, -2), (key1878, 2), (key1862, 2), (key1862, 2)]

theorem rawRowCheck4782 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form16 = rawRow4782 := by decide +kernel

def row4782 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

theorem rowCheck4782 : row4782 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4782 := by decide +kernel

theorem rowEval4782 (x : Key → ℝ) : Integer.Sparse.eval row4782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4782, Integer.Sparse.eval_collectBalanced, rawRowCheck4782]

def rawRow4783 : Integer.Sparse Key := [(key1375, -2), (key1375, -2), (key1375, -2), (key1362, 2), (key1362, 2), (key1362, 2), (key1514, 2), (key1514, 2), (key1514, 2), (key1488, -2), (key1488, -2), (key1488, -2), (key1878, -2), (key1878, -2), (key1878, -2), (key1868, 2), (key1868, 2), (key1868, 2)]

theorem rawRowCheck4783 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form16 = rawRow4783 := by decide +kernel

def row4783 : Integer.Sparse Key := [(key1362, 6), (key1375, -6), (key1488, -6), (key1514, 6), (key1868, 6), (key1878, -6)]

theorem rowCheck4783 : row4783 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4783 := by decide +kernel

theorem rowEval4783 (x : Key → ℝ) : Integer.Sparse.eval row4783 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4783, Integer.Sparse.eval_collectBalanced, rawRowCheck4783]

def rawRow4784 : Integer.Sparse Key := [(key1488, -2), (key1491, -2), (key1491, -2), (key1862, 2), (key1862, 2), (key1868, 2), (key1362, 2), (key1365, 2), (key1365, 2), (key1862, -2), (key1862, -2), (key1878, -2), (key1365, -2), (key1365, -2), (key1375, -2), (key1491, 2), (key1491, 2), (key1514, 2)]

theorem rawRowCheck4784 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form16 = rawRow4784 := by decide +kernel

def row4784 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

theorem rowCheck4784 : row4784 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4784 := by decide +kernel

theorem rowEval4784 (x : Key → ℝ) : Integer.Sparse.eval row4784 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4784, Integer.Sparse.eval_collectBalanced, rawRowCheck4784]

def rawRow4785 : Integer.Sparse Key := [(key1491, -2), (key1488, -2), (key1491, -2), (key1862, 2), (key1868, 2), (key1862, 2), (key1365, 2), (key1362, 2), (key1365, 2), (key1862, -2), (key1878, -2), (key1862, -2), (key1365, -2), (key1375, -2), (key1365, -2), (key1491, 2), (key1514, 2), (key1491, 2)]

theorem rawRowCheck4785 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form16 = rawRow4785 := by decide +kernel

def row4785 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

theorem rowCheck4785 : row4785 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4785 := by decide +kernel

theorem rowEval4785 (x : Key → ℝ) : Integer.Sparse.eval row4785 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4785, Integer.Sparse.eval_collectBalanced, rawRowCheck4785]

def rawRow4786 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1488, -2), (key1868, 2), (key1862, 2), (key1862, 2), (key1365, 2), (key1365, 2), (key1362, 2), (key1878, -2), (key1862, -2), (key1862, -2), (key1375, -2), (key1365, -2), (key1365, -2), (key1514, 2), (key1491, 2), (key1491, 2)]

theorem rawRowCheck4786 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form16 = rawRow4786 := by decide +kernel

def row4786 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

theorem rowCheck4786 : row4786 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4786 := by decide +kernel

theorem rowEval4786 (x : Key → ℝ) : Integer.Sparse.eval row4786 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4786, Integer.Sparse.eval_collectBalanced, rawRowCheck4786]

def rawRow4787 : Integer.Sparse Key := [(key1724, -2), (key1724, -2), (key1868, -2), (key1488, 2), (key1714, 2), (key1714, 2), (key1742, 2), (key1742, 2), (key1878, 2), (key1362, -2), (key1714, -2), (key1714, -2), (key1514, -2), (key1742, -2), (key1742, -2), (key1375, 2), (key1724, 2), (key1724, 2)]

theorem rawRowCheck4787 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4787 := by decide +kernel

def row4787 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

theorem rowCheck4787 : row4787 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4787 := by decide +kernel

theorem rowEval4787 (x : Key → ℝ) : Integer.Sparse.eval row4787 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4787, Integer.Sparse.eval_collectBalanced, rawRowCheck4787]

def rawRow4788 : Integer.Sparse Key := [(key1724, -2), (key1868, -2), (key1724, -2), (key1714, 2), (key1488, 2), (key1714, 2), (key1742, 2), (key1878, 2), (key1742, 2), (key1714, -2), (key1362, -2), (key1714, -2), (key1742, -2), (key1514, -2), (key1742, -2), (key1724, 2), (key1375, 2), (key1724, 2)]

theorem rawRowCheck4788 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4788 := by decide +kernel

def row4788 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

theorem rowCheck4788 : row4788 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4788 := by decide +kernel

theorem rowEval4788 (x : Key → ℝ) : Integer.Sparse.eval row4788 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4788, Integer.Sparse.eval_collectBalanced, rawRowCheck4788]

def rawRow4789 : Integer.Sparse Key := [(key1868, -2), (key1724, -2), (key1724, -2), (key1714, 2), (key1714, 2), (key1488, 2), (key1878, 2), (key1742, 2), (key1742, 2), (key1714, -2), (key1714, -2), (key1362, -2), (key1742, -2), (key1742, -2), (key1514, -2), (key1724, 2), (key1724, 2), (key1375, 2)]

theorem rawRowCheck4789 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4789 := by decide +kernel

def row4789 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

theorem rowCheck4789 : row4789 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4789 := by decide +kernel

theorem rowEval4789 (x : Key → ℝ) : Integer.Sparse.eval row4789 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4789, Integer.Sparse.eval_collectBalanced, rawRowCheck4789]

def rawRow4790 : Integer.Sparse Key := [(key1514, -2), (key1514, -2), (key1514, -2), (key1878, 2), (key1878, 2), (key1878, 2), (key1375, 2), (key1375, 2), (key1375, 2), (key1868, -2), (key1868, -2), (key1868, -2), (key1362, -2), (key1362, -2), (key1362, -2), (key1488, 2), (key1488, 2), (key1488, 2)]

theorem rawRowCheck4790 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form16 = rawRow4790 := by decide +kernel

def row4790 : Integer.Sparse Key := [(key1362, -6), (key1375, 6), (key1488, 6), (key1514, -6), (key1868, -6), (key1878, 6)]

theorem rowCheck4790 : row4790 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4790 := by decide +kernel

theorem rowEval4790 (x : Key → ℝ) : Integer.Sparse.eval row4790 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4790, Integer.Sparse.eval_collectBalanced, rawRowCheck4790]

def rawRow4791 : Integer.Sparse Key := [(key1742, -2), (key1742, -2), (key1878, -2), (key1514, 2), (key1742, 2), (key1742, 2), (key1724, 2), (key1724, 2), (key1868, 2), (key1375, -2), (key1724, -2), (key1724, -2), (key1488, -2), (key1714, -2), (key1714, -2), (key1362, 2), (key1714, 2), (key1714, 2)]

theorem rawRowCheck4791 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4791 := by decide +kernel

def row4791 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

theorem rowCheck4791 : row4791 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4791 := by decide +kernel

theorem rowEval4791 (x : Key → ℝ) : Integer.Sparse.eval row4791 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4791, Integer.Sparse.eval_collectBalanced, rawRowCheck4791]

def rawRow4792 : Integer.Sparse Key := [(key1742, -2), (key1878, -2), (key1742, -2), (key1742, 2), (key1514, 2), (key1742, 2), (key1724, 2), (key1868, 2), (key1724, 2), (key1724, -2), (key1375, -2), (key1724, -2), (key1714, -2), (key1488, -2), (key1714, -2), (key1714, 2), (key1362, 2), (key1714, 2)]

theorem rawRowCheck4792 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4792 := by decide +kernel

def row4792 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

theorem rowCheck4792 : row4792 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4792 := by decide +kernel

theorem rowEval4792 (x : Key → ℝ) : Integer.Sparse.eval row4792 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4792, Integer.Sparse.eval_collectBalanced, rawRowCheck4792]

def rawRow4793 : Integer.Sparse Key := [(key1878, -2), (key1742, -2), (key1742, -2), (key1742, 2), (key1742, 2), (key1514, 2), (key1868, 2), (key1724, 2), (key1724, 2), (key1724, -2), (key1724, -2), (key1375, -2), (key1714, -2), (key1714, -2), (key1488, -2), (key1714, 2), (key1714, 2), (key1362, 2)]

theorem rawRowCheck4793 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4793 := by decide +kernel

def row4793 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

theorem rowCheck4793 : row4793 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4793 := by decide +kernel

theorem rowEval4793 (x : Key → ℝ) : Integer.Sparse.eval row4793 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4793, Integer.Sparse.eval_collectBalanced, rawRowCheck4793]

def rawRow4794 : Integer.Sparse Key := [(key351, -1), (key353, -1), (key351, -1), (key370, -1), (key353, -1), (key370, -1), (key353, 2), (key353, 2), (key370, 2), (key508, 1), (key510, 1), (key508, 1), (key542, 1), (key510, 1), (key542, 1), (key510, -1), (key521, -1), (key510, -1), (key542, -1), (key521, -1), (key542, -1), (key628, -2), (key628, -2), (key641, -2), (key628, 1), (key630, 1), (key628, 1), (key641, 1), (key630, 1), (key641, 1)]

theorem rawRowCheck4794 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form17 = rawRow4794 := by decide +kernel

def row4794 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

theorem rowCheck4794 : row4794 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4794 := by decide +kernel

theorem rowEval4794 (x : Key → ℝ) : Integer.Sparse.eval row4794 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4794, Integer.Sparse.eval_collectBalanced, rawRowCheck4794]

def rawRow4795 : Integer.Sparse Key := [(key353, -1), (key351, -1), (key370, -1), (key351, -1), (key370, -1), (key353, -1), (key353, 2), (key370, 2), (key353, 2), (key510, 1), (key508, 1), (key542, 1), (key508, 1), (key542, 1), (key510, 1), (key521, -1), (key510, -1), (key542, -1), (key510, -1), (key542, -1), (key521, -1), (key628, -2), (key641, -2), (key628, -2), (key630, 1), (key628, 1), (key641, 1), (key628, 1), (key641, 1), (key630, 1)]

theorem rawRowCheck4795 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form17 = rawRow4795 := by decide +kernel

def row4795 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

theorem rowCheck4795 : row4795 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4795 := by decide +kernel

theorem rowEval4795 (x : Key → ℝ) : Integer.Sparse.eval row4795 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4795, Integer.Sparse.eval_collectBalanced, rawRowCheck4795]

def rawRow4796 : Integer.Sparse Key := [(key370, -1), (key370, -1), (key353, -1), (key353, -1), (key351, -1), (key351, -1), (key370, 2), (key353, 2), (key353, 2), (key542, 1), (key542, 1), (key510, 1), (key510, 1), (key508, 1), (key508, 1), (key542, -1), (key542, -1), (key521, -1), (key521, -1), (key510, -1), (key510, -1), (key641, -2), (key628, -2), (key628, -2), (key641, 1), (key641, 1), (key630, 1), (key630, 1), (key628, 1), (key628, 1)]

theorem rawRowCheck4796 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form17 = rawRow4796 := by decide +kernel

def row4796 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

theorem rowCheck4796 : row4796 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4796 := by decide +kernel

theorem rowEval4796 (x : Key → ℝ) : Integer.Sparse.eval row4796 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4796, Integer.Sparse.eval_collectBalanced, rawRowCheck4796]

def rawRow4797 : Integer.Sparse Key := [(key353, -1), (key353, -1), (key353, -1), (key353, -1), (key353, -1), (key353, -1), (key351, 2), (key351, 2), (key351, 2), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key630, -2), (key630, -2), (key630, -2), (key628, 1), (key628, 1), (key628, 1), (key628, 1), (key628, 1), (key628, 1)]

theorem rawRowCheck4797 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form17 = rawRow4797 := by decide +kernel

def row4797 : Integer.Sparse Key := [(key351, 6), (key353, -6), (key508, -6), (key521, 6), (key628, 6), (key630, -6)]

theorem rowCheck4797 : row4797 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4797 := by decide +kernel

theorem rowEval4797 (x : Key → ℝ) : Integer.Sparse.eval row4797 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4797, Integer.Sparse.eval_collectBalanced, rawRowCheck4797]

def rawRow4798 : Integer.Sparse Key := [(key508, -1), (key510, -1), (key508, -1), (key542, -1), (key510, -1), (key542, -1), (key628, 2), (key628, 2), (key641, 2), (key351, 1), (key353, 1), (key351, 1), (key370, 1), (key353, 1), (key370, 1), (key628, -1), (key630, -1), (key628, -1), (key641, -1), (key630, -1), (key641, -1), (key353, -2), (key353, -2), (key370, -2), (key510, 1), (key521, 1), (key510, 1), (key542, 1), (key521, 1), (key542, 1)]

theorem rawRowCheck4798 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form17 = rawRow4798 := by decide +kernel

def row4798 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

theorem rowCheck4798 : row4798 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4798 := by decide +kernel

theorem rowEval4798 (x : Key → ℝ) : Integer.Sparse.eval row4798 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4798, Integer.Sparse.eval_collectBalanced, rawRowCheck4798]

def rawRow4799 : Integer.Sparse Key := [(key510, -1), (key508, -1), (key542, -1), (key508, -1), (key542, -1), (key510, -1), (key628, 2), (key641, 2), (key628, 2), (key353, 1), (key351, 1), (key370, 1), (key351, 1), (key370, 1), (key353, 1), (key630, -1), (key628, -1), (key641, -1), (key628, -1), (key641, -1), (key630, -1), (key353, -2), (key370, -2), (key353, -2), (key521, 1), (key510, 1), (key542, 1), (key510, 1), (key542, 1), (key521, 1)]

theorem rawRowCheck4799 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form17 = rawRow4799 := by decide +kernel

def row4799 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

theorem rowCheck4799 : row4799 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4799 := by decide +kernel

theorem rowEval4799 (x : Key → ℝ) : Integer.Sparse.eval row4799 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4799, Integer.Sparse.eval_collectBalanced, rawRowCheck4799]

def rawRow4800 : Integer.Sparse Key := [(key542, -1), (key542, -1), (key510, -1), (key510, -1), (key508, -1), (key508, -1), (key641, 2), (key628, 2), (key628, 2), (key370, 1), (key370, 1), (key353, 1), (key353, 1), (key351, 1), (key351, 1), (key641, -1), (key641, -1), (key630, -1), (key630, -1), (key628, -1), (key628, -1), (key370, -2), (key353, -2), (key353, -2), (key542, 1), (key542, 1), (key521, 1), (key521, 1), (key510, 1), (key510, 1)]

theorem rawRowCheck4800 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form17 = rawRow4800 := by decide +kernel

def row4800 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

theorem rowCheck4800 : row4800 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4800 := by decide +kernel

theorem rowEval4800 (x : Key → ℝ) : Integer.Sparse.eval row4800 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4800, Integer.Sparse.eval_collectBalanced, rawRowCheck4800]

def rawRow4801 : Integer.Sparse Key := [(key284, -1), (key284, -1), (key510, -1), (key510, -1), (key628, -1), (key628, -1), (key282, 2), (key508, 2), (key508, 2), (key293, 1), (key293, 1), (key521, 1), (key521, 1), (key630, 1), (key630, 1), (key282, -1), (key282, -1), (key351, -1), (key351, -1), (key508, -1), (key508, -1), (key293, -2), (key521, -2), (key521, -2), (key284, 1), (key284, 1), (key353, 1), (key353, 1), (key510, 1), (key510, 1)]

theorem rawRowCheck4801 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4801 := by decide +kernel

def row4801 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

theorem rowCheck4801 : row4801 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4801 := by decide +kernel

theorem rowEval4801 (x : Key → ℝ) : Integer.Sparse.eval row4801 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4801, Integer.Sparse.eval_collectBalanced, rawRowCheck4801]

def rawRow4802 : Integer.Sparse Key := [(key510, -1), (key628, -1), (key284, -1), (key628, -1), (key284, -1), (key510, -1), (key508, 2), (key282, 2), (key508, 2), (key521, 1), (key630, 1), (key293, 1), (key630, 1), (key293, 1), (key521, 1), (key351, -1), (key508, -1), (key282, -1), (key508, -1), (key282, -1), (key351, -1), (key521, -2), (key293, -2), (key521, -2), (key353, 1), (key510, 1), (key284, 1), (key510, 1), (key284, 1), (key353, 1)]

theorem rawRowCheck4802 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4802 := by decide +kernel

def row4802 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

theorem rowCheck4802 : row4802 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4802 := by decide +kernel

theorem rowEval4802 (x : Key → ℝ) : Integer.Sparse.eval row4802 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4802, Integer.Sparse.eval_collectBalanced, rawRowCheck4802]

def rawRow4803 : Integer.Sparse Key := [(key628, -1), (key510, -1), (key628, -1), (key284, -1), (key510, -1), (key284, -1), (key508, 2), (key508, 2), (key282, 2), (key630, 1), (key521, 1), (key630, 1), (key293, 1), (key521, 1), (key293, 1), (key508, -1), (key351, -1), (key508, -1), (key282, -1), (key351, -1), (key282, -1), (key521, -2), (key521, -2), (key293, -2), (key510, 1), (key353, 1), (key510, 1), (key284, 1), (key353, 1), (key284, 1)]

theorem rawRowCheck4803 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4803 := by decide +kernel

def row4803 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

theorem rowCheck4803 : row4803 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4803 := by decide +kernel

theorem rowEval4803 (x : Key → ℝ) : Integer.Sparse.eval row4803 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4803, Integer.Sparse.eval_collectBalanced, rawRowCheck4803]

def rawRow4804 : Integer.Sparse Key := [(key521, -1), (key521, -1), (key521, -1), (key521, -1), (key521, -1), (key521, -1), (key630, 2), (key630, 2), (key630, 2), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key351, -2), (key351, -2), (key351, -2), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1)]

theorem rawRowCheck4804 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form17 = rawRow4804 := by decide +kernel

def row4804 : Integer.Sparse Key := [(key351, -6), (key353, 6), (key508, 6), (key521, -6), (key628, -6), (key630, 6)]

theorem rowCheck4804 : row4804 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4804 := by decide +kernel

theorem rowEval4804 (x : Key → ℝ) : Integer.Sparse.eval row4804 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4804, Integer.Sparse.eval_collectBalanced, rawRowCheck4804]

def rawRow4805 : Integer.Sparse Key := [(key293, -1), (key293, -1), (key521, -1), (key521, -1), (key630, -1), (key630, -1), (key293, 2), (key521, 2), (key521, 2), (key284, 1), (key284, 1), (key510, 1), (key510, 1), (key628, 1), (key628, 1), (key284, -1), (key284, -1), (key353, -1), (key353, -1), (key510, -1), (key510, -1), (key282, -2), (key508, -2), (key508, -2), (key282, 1), (key282, 1), (key351, 1), (key351, 1), (key508, 1), (key508, 1)]

theorem rawRowCheck4805 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4805 := by decide +kernel

def row4805 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

theorem rowCheck4805 : row4805 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4805 := by decide +kernel

theorem rowEval4805 (x : Key → ℝ) : Integer.Sparse.eval row4805 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4805, Integer.Sparse.eval_collectBalanced, rawRowCheck4805]

def rawRow4806 : Integer.Sparse Key := [(key521, -1), (key630, -1), (key293, -1), (key630, -1), (key293, -1), (key521, -1), (key521, 2), (key293, 2), (key521, 2), (key510, 1), (key628, 1), (key284, 1), (key628, 1), (key284, 1), (key510, 1), (key353, -1), (key510, -1), (key284, -1), (key510, -1), (key284, -1), (key353, -1), (key508, -2), (key282, -2), (key508, -2), (key351, 1), (key508, 1), (key282, 1), (key508, 1), (key282, 1), (key351, 1)]

theorem rawRowCheck4806 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4806 := by decide +kernel

def row4806 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

theorem rowCheck4806 : row4806 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4806 := by decide +kernel

theorem rowEval4806 (x : Key → ℝ) : Integer.Sparse.eval row4806 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4806, Integer.Sparse.eval_collectBalanced, rawRowCheck4806]

def rawRow4807 : Integer.Sparse Key := [(key630, -1), (key521, -1), (key630, -1), (key293, -1), (key521, -1), (key293, -1), (key521, 2), (key521, 2), (key293, 2), (key628, 1), (key510, 1), (key628, 1), (key284, 1), (key510, 1), (key284, 1), (key510, -1), (key353, -1), (key510, -1), (key284, -1), (key353, -1), (key284, -1), (key508, -2), (key508, -2), (key282, -2), (key508, 1), (key351, 1), (key508, 1), (key282, 1), (key351, 1), (key282, 1)]

theorem rawRowCheck4807 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4807 := by decide +kernel

def row4807 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

theorem rowCheck4807 : row4807 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4807 := by decide +kernel

theorem rowEval4807 (x : Key → ℝ) : Integer.Sparse.eval row4807 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4807, Integer.Sparse.eval_collectBalanced, rawRowCheck4807]

def rawRow4808 : Integer.Sparse Key := [(key1488, -1), (key1491, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1514, -1), (key1491, 2), (key1491, 2), (key1514, 2), (key1714, 1), (key1717, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1742, 1), (key1717, -1), (key1724, -1), (key1717, -1), (key1742, -1), (key1724, -1), (key1742, -1), (key1862, -2), (key1862, -2), (key1878, -2), (key1862, 1), (key1868, 1), (key1862, 1), (key1878, 1), (key1868, 1), (key1878, 1)]

theorem rawRowCheck4808 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form18 = rawRow4808 := by decide +kernel

def row4808 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

theorem rowCheck4808 : row4808 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4808 := by decide +kernel

theorem rowEval4808 (x : Key → ℝ) : Integer.Sparse.eval row4808 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4808, Integer.Sparse.eval_collectBalanced, rawRowCheck4808]

def rawRow4809 : Integer.Sparse Key := [(key1491, -1), (key1488, -1), (key1514, -1), (key1488, -1), (key1514, -1), (key1491, -1), (key1491, 2), (key1514, 2), (key1491, 2), (key1717, 1), (key1714, 1), (key1742, 1), (key1714, 1), (key1742, 1), (key1717, 1), (key1724, -1), (key1717, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1724, -1), (key1862, -2), (key1878, -2), (key1862, -2), (key1868, 1), (key1862, 1), (key1878, 1), (key1862, 1), (key1878, 1), (key1868, 1)]

theorem rawRowCheck4809 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form18 = rawRow4809 := by decide +kernel

def row4809 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

theorem rowCheck4809 : row4809 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4809 := by decide +kernel

theorem rowEval4809 (x : Key → ℝ) : Integer.Sparse.eval row4809 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4809, Integer.Sparse.eval_collectBalanced, rawRowCheck4809]

def rawRow4810 : Integer.Sparse Key := [(key1514, -1), (key1514, -1), (key1491, -1), (key1491, -1), (key1488, -1), (key1488, -1), (key1514, 2), (key1491, 2), (key1491, 2), (key1742, 1), (key1742, 1), (key1717, 1), (key1717, 1), (key1714, 1), (key1714, 1), (key1742, -1), (key1742, -1), (key1724, -1), (key1724, -1), (key1717, -1), (key1717, -1), (key1878, -2), (key1862, -2), (key1862, -2), (key1878, 1), (key1878, 1), (key1868, 1), (key1868, 1), (key1862, 1), (key1862, 1)]

theorem rawRowCheck4810 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form18 = rawRow4810 := by decide +kernel

def row4810 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

theorem rowCheck4810 : row4810 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4810 := by decide +kernel

theorem rowEval4810 (x : Key → ℝ) : Integer.Sparse.eval row4810 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4810, Integer.Sparse.eval_collectBalanced, rawRowCheck4810]

def rawRow4811 : Integer.Sparse Key := [(key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1488, 2), (key1488, 2), (key1488, 2), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1868, -2), (key1868, -2), (key1868, -2), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1)]

theorem rawRowCheck4811 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form18 = rawRow4811 := by decide +kernel

def row4811 : Integer.Sparse Key := [(key1488, 6), (key1491, -6), (key1714, -6), (key1724, 6), (key1862, 6), (key1868, -6)]

theorem rowCheck4811 : row4811 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4811 := by decide +kernel

theorem rowEval4811 (x : Key → ℝ) : Integer.Sparse.eval row4811 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4811, Integer.Sparse.eval_collectBalanced, rawRowCheck4811]

def rawRow4812 : Integer.Sparse Key := [(key1714, -1), (key1717, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1742, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1488, 1), (key1491, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1514, 1), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1), (key1491, -2), (key1491, -2), (key1514, -2), (key1717, 1), (key1724, 1), (key1717, 1), (key1742, 1), (key1724, 1), (key1742, 1)]

theorem rawRowCheck4812 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form18 = rawRow4812 := by decide +kernel

def row4812 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

theorem rowCheck4812 : row4812 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4812 := by decide +kernel

theorem rowEval4812 (x : Key → ℝ) : Integer.Sparse.eval row4812 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4812, Integer.Sparse.eval_collectBalanced, rawRowCheck4812]

def rawRow4813 : Integer.Sparse Key := [(key1717, -1), (key1714, -1), (key1742, -1), (key1714, -1), (key1742, -1), (key1717, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1491, 1), (key1488, 1), (key1514, 1), (key1488, 1), (key1514, 1), (key1491, 1), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1491, -2), (key1514, -2), (key1491, -2), (key1724, 1), (key1717, 1), (key1742, 1), (key1717, 1), (key1742, 1), (key1724, 1)]

theorem rawRowCheck4813 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form18 = rawRow4813 := by decide +kernel

def row4813 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

theorem rowCheck4813 : row4813 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4813 := by decide +kernel

theorem rowEval4813 (x : Key → ℝ) : Integer.Sparse.eval row4813 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4813, Integer.Sparse.eval_collectBalanced, rawRowCheck4813]

def rawRow4814 : Integer.Sparse Key := [(key1742, -1), (key1742, -1), (key1717, -1), (key1717, -1), (key1714, -1), (key1714, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1514, 1), (key1514, 1), (key1491, 1), (key1491, 1), (key1488, 1), (key1488, 1), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1), (key1514, -2), (key1491, -2), (key1491, -2), (key1742, 1), (key1742, 1), (key1724, 1), (key1724, 1), (key1717, 1), (key1717, 1)]

theorem rawRowCheck4814 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form18 = rawRow4814 := by decide +kernel

def row4814 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

theorem rowCheck4814 : row4814 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4814 := by decide +kernel

theorem rowEval4814 (x : Key → ℝ) : Integer.Sparse.eval row4814 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4814, Integer.Sparse.eval_collectBalanced, rawRowCheck4814]

def rawRow4815 : Integer.Sparse Key := [(key1365, -1), (key1365, -1), (key1717, -1), (key1717, -1), (key1862, -1), (key1862, -1), (key1362, 2), (key1714, 2), (key1714, 2), (key1375, 1), (key1375, 1), (key1724, 1), (key1724, 1), (key1868, 1), (key1868, 1), (key1362, -1), (key1362, -1), (key1488, -1), (key1488, -1), (key1714, -1), (key1714, -1), (key1375, -2), (key1724, -2), (key1724, -2), (key1365, 1), (key1365, 1), (key1491, 1), (key1491, 1), (key1717, 1), (key1717, 1)]

theorem rawRowCheck4815 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form18 = rawRow4815 := by decide +kernel

def row4815 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

theorem rowCheck4815 : row4815 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4815 := by decide +kernel

theorem rowEval4815 (x : Key → ℝ) : Integer.Sparse.eval row4815 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4815, Integer.Sparse.eval_collectBalanced, rawRowCheck4815]

def rawRow4816 : Integer.Sparse Key := [(key1717, -1), (key1862, -1), (key1365, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1714, 2), (key1362, 2), (key1714, 2), (key1724, 1), (key1868, 1), (key1375, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1488, -1), (key1714, -1), (key1362, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1724, -2), (key1375, -2), (key1724, -2), (key1491, 1), (key1717, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1491, 1)]

theorem rawRowCheck4816 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form18 = rawRow4816 := by decide +kernel

def row4816 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

theorem rowCheck4816 : row4816 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4816 := by decide +kernel

theorem rowEval4816 (x : Key → ℝ) : Integer.Sparse.eval row4816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4816, Integer.Sparse.eval_collectBalanced, rawRowCheck4816]

def rawRow4817 : Integer.Sparse Key := [(key1862, -1), (key1717, -1), (key1862, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1714, 2), (key1714, 2), (key1362, 2), (key1868, 1), (key1724, 1), (key1868, 1), (key1375, 1), (key1724, 1), (key1375, 1), (key1714, -1), (key1488, -1), (key1714, -1), (key1362, -1), (key1488, -1), (key1362, -1), (key1724, -2), (key1724, -2), (key1375, -2), (key1717, 1), (key1491, 1), (key1717, 1), (key1365, 1), (key1491, 1), (key1365, 1)]

theorem rawRowCheck4817 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form18 = rawRow4817 := by decide +kernel

def row4817 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

theorem rowCheck4817 : row4817 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4817 := by decide +kernel

theorem rowEval4817 (x : Key → ℝ) : Integer.Sparse.eval row4817 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4817, Integer.Sparse.eval_collectBalanced, rawRowCheck4817]

def rawRow4818 : Integer.Sparse Key := [(key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1488, -2), (key1488, -2), (key1488, -2), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1)]

theorem rawRowCheck4818 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form18 = rawRow4818 := by decide +kernel

def row4818 : Integer.Sparse Key := [(key1488, -6), (key1491, 6), (key1714, 6), (key1724, -6), (key1862, -6), (key1868, 6)]

theorem rowCheck4818 : row4818 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4818 := by decide +kernel

theorem rowEval4818 (x : Key → ℝ) : Integer.Sparse.eval row4818 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4818, Integer.Sparse.eval_collectBalanced, rawRowCheck4818]

def rawRow4819 : Integer.Sparse Key := [(key1375, -1), (key1375, -1), (key1724, -1), (key1724, -1), (key1868, -1), (key1868, -1), (key1375, 2), (key1724, 2), (key1724, 2), (key1365, 1), (key1365, 1), (key1717, 1), (key1717, 1), (key1862, 1), (key1862, 1), (key1365, -1), (key1365, -1), (key1491, -1), (key1491, -1), (key1717, -1), (key1717, -1), (key1362, -2), (key1714, -2), (key1714, -2), (key1362, 1), (key1362, 1), (key1488, 1), (key1488, 1), (key1714, 1), (key1714, 1)]

theorem rawRowCheck4819 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form18 = rawRow4819 := by decide +kernel

def row4819 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

theorem rowCheck4819 : row4819 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4819 := by decide +kernel

theorem rowEval4819 (x : Key → ℝ) : Integer.Sparse.eval row4819 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4819, Integer.Sparse.eval_collectBalanced, rawRowCheck4819]

def rawRow4820 : Integer.Sparse Key := [(key1724, -1), (key1868, -1), (key1375, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1724, 2), (key1375, 2), (key1724, 2), (key1717, 1), (key1862, 1), (key1365, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1491, -1), (key1717, -1), (key1365, -1), (key1717, -1), (key1365, -1), (key1491, -1), (key1714, -2), (key1362, -2), (key1714, -2), (key1488, 1), (key1714, 1), (key1362, 1), (key1714, 1), (key1362, 1), (key1488, 1)]

theorem rawRowCheck4820 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form18 = rawRow4820 := by decide +kernel

def row4820 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

theorem rowCheck4820 : row4820 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4820 := by decide +kernel

theorem rowEval4820 (x : Key → ℝ) : Integer.Sparse.eval row4820 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4820, Integer.Sparse.eval_collectBalanced, rawRowCheck4820]

def rawRow4821 : Integer.Sparse Key := [(key1868, -1), (key1724, -1), (key1868, -1), (key1375, -1), (key1724, -1), (key1375, -1), (key1724, 2), (key1724, 2), (key1375, 2), (key1862, 1), (key1717, 1), (key1862, 1), (key1365, 1), (key1717, 1), (key1365, 1), (key1717, -1), (key1491, -1), (key1717, -1), (key1365, -1), (key1491, -1), (key1365, -1), (key1714, -2), (key1714, -2), (key1362, -2), (key1714, 1), (key1488, 1), (key1714, 1), (key1362, 1), (key1488, 1), (key1362, 1)]

theorem rawRowCheck4821 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form18 = rawRow4821 := by decide +kernel

def row4821 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

theorem rowCheck4821 : row4821 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4821 := by decide +kernel

theorem rowEval4821 (x : Key → ℝ) : Integer.Sparse.eval row4821 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4821, Integer.Sparse.eval_collectBalanced, rawRowCheck4821]

def rawRow4822 : Integer.Sparse Key := [(key291, -2), (key294, -2), (key294, -2), (key294, 6), (key518, 2), (key522, 2), (key522, 2), (key522, -2), (key522, -2), (key553, -2), (key631, -6), (key631, 2), (key631, 2), (key647, 2)]

theorem rawRowCheck4822 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form19 = rawRow4822 := by decide +kernel

def row4822 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

theorem rowCheck4822 : row4822 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4822 := by decide +kernel

theorem rowEval4822 (x : Key → ℝ) : Integer.Sparse.eval row4822 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck4822, Integer.Sparse.eval_collectBalanced, rawRowCheck4822]

def rawRow4823 : Integer.Sparse Key := [(key294, -2), (key291, -2), (key294, -2), (key294, 6), (key522, 2), (key518, 2), (key522, 2), (key522, -2), (key553, -2), (key522, -2), (key631, -6), (key631, 2), (key647, 2), (key631, 2)]

theorem rawRowCheck4823 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form19 = rawRow4823 := by decide +kernel

def row4823 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

theorem rowCheck4823 : row4823 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4823 := by decide +kernel

theorem rowEval4823 (x : Key → ℝ) : Integer.Sparse.eval row4823 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4823, Integer.Sparse.eval_collectBalanced, rawRowCheck4823]

def rawRow4824 : Integer.Sparse Key := [(key294, -2), (key294, -2), (key291, -2), (key294, 6), (key522, 2), (key522, 2), (key518, 2), (key553, -2), (key522, -2), (key522, -2), (key631, -6), (key647, 2), (key631, 2), (key631, 2)]

theorem rawRowCheck4824 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form19 = rawRow4824 := by decide +kernel

def row4824 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

theorem rowCheck4824 : row4824 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4824 := by decide +kernel

theorem rowEval4824 (x : Key → ℝ) : Integer.Sparse.eval row4824 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4824, Integer.Sparse.eval_collectBalanced, rawRowCheck4824]

def rawRow4825 : Integer.Sparse Key := [(key294, -2), (key294, -2), (key294, -2), (key291, 6), (key553, 2), (key553, 2), (key553, 2), (key518, -2), (key518, -2), (key518, -2), (key647, -6), (key631, 2), (key631, 2), (key631, 2)]

theorem rawRowCheck4825 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form19 = rawRow4825 := by decide +kernel

def row4825 : Integer.Sparse Key := [(key291, 6), (key294, -6), (key518, -6), (key553, 6), (key631, 6), (key647, -6)]

theorem rowCheck4825 : row4825 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4825 := by decide +kernel

theorem rowEval4825 (x : Key → ℝ) : Integer.Sparse.eval row4825 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4825, Integer.Sparse.eval_collectBalanced, rawRowCheck4825]

def rawRow4826 : Integer.Sparse Key := [(key518, -2), (key522, -2), (key522, -2), (key553, 6), (key291, 2), (key294, 2), (key294, 2), (key631, -2), (key631, -2), (key647, -2), (key294, -6), (key522, 2), (key522, 2), (key553, 2)]

theorem rawRowCheck4826 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form19 = rawRow4826 := by decide +kernel

def row4826 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

theorem rowCheck4826 : row4826 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4826 := by decide +kernel

theorem rowEval4826 (x : Key → ℝ) : Integer.Sparse.eval row4826 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form19) x := by
  rw [rowCheck4826, Integer.Sparse.eval_collectBalanced, rawRowCheck4826]

def rawRow4827 : Integer.Sparse Key := [(key522, -2), (key518, -2), (key522, -2), (key553, 6), (key294, 2), (key291, 2), (key294, 2), (key631, -2), (key647, -2), (key631, -2), (key294, -6), (key522, 2), (key553, 2), (key522, 2)]

theorem rawRowCheck4827 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form19 = rawRow4827 := by decide +kernel

def row4827 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

theorem rowCheck4827 : row4827 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4827 := by decide +kernel

theorem rowEval4827 (x : Key → ℝ) : Integer.Sparse.eval row4827 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4827, Integer.Sparse.eval_collectBalanced, rawRowCheck4827]

def rawRow4828 : Integer.Sparse Key := [(key522, -2), (key522, -2), (key518, -2), (key553, 6), (key294, 2), (key294, 2), (key291, 2), (key647, -2), (key631, -2), (key631, -2), (key294, -6), (key553, 2), (key522, 2), (key522, 2)]

theorem rawRowCheck4828 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form19 = rawRow4828 := by decide +kernel

def row4828 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

theorem rowCheck4828 : row4828 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4828 := by decide +kernel

theorem rowEval4828 (x : Key → ℝ) : Integer.Sparse.eval row4828 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4828, Integer.Sparse.eval_collectBalanced, rawRowCheck4828]

def rawRow4829 : Integer.Sparse Key := [(key522, -2), (key522, -2), (key553, -2), (key518, 6), (key631, 2), (key631, 2), (key647, 2), (key291, -2), (key518, -2), (key518, -2), (key553, -6), (key294, 2), (key522, 2), (key522, 2)]

theorem rawRowCheck4829 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form19 = rawRow4829 := by decide +kernel

def row4829 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

theorem rowCheck4829 : row4829 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4829 := by decide +kernel

theorem rowEval4829 (x : Key → ℝ) : Integer.Sparse.eval row4829 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4829, Integer.Sparse.eval_collectBalanced, rawRowCheck4829]

def rawRow4830 : Integer.Sparse Key := [(key522, -2), (key553, -2), (key522, -2), (key518, 6), (key631, 2), (key647, 2), (key631, 2), (key518, -2), (key291, -2), (key518, -2), (key553, -6), (key522, 2), (key294, 2), (key522, 2)]

theorem rawRowCheck4830 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form19 = rawRow4830 := by decide +kernel

def row4830 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

theorem rowCheck4830 : row4830 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4830 := by decide +kernel

theorem rowEval4830 (x : Key → ℝ) : Integer.Sparse.eval row4830 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4830, Integer.Sparse.eval_collectBalanced, rawRowCheck4830]

def rawRow4831 : Integer.Sparse Key := [(key553, -2), (key522, -2), (key522, -2), (key518, 6), (key647, 2), (key631, 2), (key631, 2), (key518, -2), (key518, -2), (key291, -2), (key553, -6), (key522, 2), (key522, 2), (key294, 2)]

theorem rawRowCheck4831 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form19 = rawRow4831 := by decide +kernel

def row4831 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

theorem rowCheck4831 : row4831 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4831 := by decide +kernel

theorem rowEval4831 (x : Key → ℝ) : Integer.Sparse.eval row4831 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form19) x := by
  rw [rowCheck4831, Integer.Sparse.eval_collectBalanced, rawRowCheck4831]

def rawRow4832 : Integer.Sparse Key := [(key631, -2), (key631, -2), (key631, -2), (key647, 6), (key294, 2), (key294, 2), (key294, 2), (key553, -2), (key553, -2), (key553, -2), (key291, -6), (key518, 2), (key518, 2), (key518, 2)]

theorem rawRowCheck4832 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form19 = rawRow4832 := by decide +kernel

def row4832 : Integer.Sparse Key := [(key291, -6), (key294, 6), (key518, 6), (key553, -6), (key631, -6), (key647, 6)]

theorem rowCheck4832 : row4832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4832 := by decide +kernel

theorem rowEval4832 (x : Key → ℝ) : Integer.Sparse.eval row4832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4832, Integer.Sparse.eval_collectBalanced, rawRowCheck4832]

def rawRow4833 : Integer.Sparse Key := [(key631, -2), (key631, -2), (key647, -2), (key631, 6), (key522, 2), (key522, 2), (key553, 2), (key294, -2), (key522, -2), (key522, -2), (key518, -6), (key291, 2), (key518, 2), (key518, 2)]

theorem rawRowCheck4833 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form19 = rawRow4833 := by decide +kernel

def row4833 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

theorem rowCheck4833 : row4833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4833 := by decide +kernel

theorem rowEval4833 (x : Key → ℝ) : Integer.Sparse.eval row4833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4833, Integer.Sparse.eval_collectBalanced, rawRowCheck4833]

def rawRow4834 : Integer.Sparse Key := [(key631, -2), (key647, -2), (key631, -2), (key631, 6), (key522, 2), (key553, 2), (key522, 2), (key522, -2), (key294, -2), (key522, -2), (key518, -6), (key518, 2), (key291, 2), (key518, 2)]

theorem rawRowCheck4834 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form19 = rawRow4834 := by decide +kernel

def row4834 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

theorem rowCheck4834 : row4834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4834 := by decide +kernel

theorem rowEval4834 (x : Key → ℝ) : Integer.Sparse.eval row4834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form19) x := by
  rw [rowCheck4834, Integer.Sparse.eval_collectBalanced, rawRowCheck4834]

def rawRow4835 : Integer.Sparse Key := [(key647, -2), (key631, -2), (key631, -2), (key631, 6), (key553, 2), (key522, 2), (key522, 2), (key522, -2), (key522, -2), (key294, -2), (key518, -6), (key518, 2), (key518, 2), (key291, 2)]

theorem rawRowCheck4835 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form19 = rawRow4835 := by decide +kernel

def row4835 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

theorem rowCheck4835 : row4835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4835 := by decide +kernel

theorem rowEval4835 (x : Key → ℝ) : Integer.Sparse.eval row4835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form19) x := by
  rw [rowCheck4835, Integer.Sparse.eval_collectBalanced, rawRowCheck4835]

def rawRow4836 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2739, 1), (key2739, 1), (key2749, 1), (key2749, 1), (key2751, 1), (key2751, 1), (key2810, 2), (key2833, 2), (key2833, 2), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, -1), (key2915, -1), (key2952, -1), (key2952, -1), (key2962, -1), (key2962, -1), (key2964, -1), (key2964, -1), (key2978, 1), (key2978, 1), (key2985, 1), (key2985, 1), (key2994, 1), (key2994, 1)]

theorem rawRowCheck4836 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form0 = rawRow4836 := by decide +kernel

def row4836 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

theorem rowCheck4836 : row4836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4836 := by decide +kernel

theorem rowEval4836 (x : Key → ℝ) : Integer.Sparse.eval row4836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4836, Integer.Sparse.eval_collectBalanced, rawRowCheck4836]

def rawRow4837 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2749, 1), (key2751, 1), (key2739, 1), (key2751, 1), (key2739, 1), (key2749, 1), (key2833, 2), (key2810, 2), (key2833, 2), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2962, -1), (key2964, -1), (key2952, -1), (key2964, -1), (key2952, -1), (key2962, -1), (key2985, 1), (key2994, 1), (key2978, 1), (key2994, 1), (key2978, 1), (key2985, 1)]

theorem rawRowCheck4837 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form0 = rawRow4837 := by decide +kernel

def row4837 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

theorem rowCheck4837 : row4837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4837 := by decide +kernel

theorem rowEval4837 (x : Key → ℝ) : Integer.Sparse.eval row4837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4837, Integer.Sparse.eval_collectBalanced, rawRowCheck4837]

def rawRow4838 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2751, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2749, 1), (key2739, 1), (key2833, 2), (key2833, 2), (key2810, 2), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, -1), (key2899, -1), (key2964, -1), (key2962, -1), (key2964, -1), (key2952, -1), (key2962, -1), (key2952, -1), (key2994, 1), (key2985, 1), (key2994, 1), (key2978, 1), (key2985, 1), (key2978, 1)]

theorem rawRowCheck4838 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form0 = rawRow4838 := by decide +kernel

def row4838 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

theorem rowCheck4838 : row4838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4838 := by decide +kernel

theorem rowEval4838 (x : Key → ℝ) : Integer.Sparse.eval row4838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4838, Integer.Sparse.eval_collectBalanced, rawRowCheck4838]

def rawRow4839 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2952, 1), (key2952, 1), (key2962, 1), (key2962, 1), (key2964, 1), (key2964, 1), (key2707, 2), (key2730, 2), (key2730, 2), (key2978, -1), (key2978, -1), (key2985, -1), (key2985, -1), (key2994, -1), (key2994, -1), (key2739, -1), (key2739, -1), (key2749, -1), (key2749, -1), (key2751, -1), (key2751, -1), (key2899, 1), (key2899, 1), (key2906, 1), (key2906, 1), (key2915, 1), (key2915, 1)]

theorem rawRowCheck4839 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form0 = rawRow4839 := by decide +kernel

def row4839 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

theorem rowCheck4839 : row4839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4839 := by decide +kernel

theorem rowEval4839 (x : Key → ℝ) : Integer.Sparse.eval row4839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4839, Integer.Sparse.eval_collectBalanced, rawRowCheck4839]

def rawRow4840 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2962, 1), (key2964, 1), (key2952, 1), (key2964, 1), (key2952, 1), (key2962, 1), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, -1), (key2994, -1), (key2978, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2749, -1), (key2751, -1), (key2739, -1), (key2751, -1), (key2739, -1), (key2749, -1), (key2906, 1), (key2915, 1), (key2899, 1), (key2915, 1), (key2899, 1), (key2906, 1)]

theorem rawRowCheck4840 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form0 = rawRow4840 := by decide +kernel

def row4840 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

theorem rowCheck4840 : row4840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4840 := by decide +kernel

theorem rowEval4840 (x : Key → ℝ) : Integer.Sparse.eval row4840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4840, Integer.Sparse.eval_collectBalanced, rawRowCheck4840]

def rawRow4841 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2964, 1), (key2962, 1), (key2964, 1), (key2952, 1), (key2962, 1), (key2952, 1), (key2730, 2), (key2730, 2), (key2707, 2), (key2994, -1), (key2985, -1), (key2994, -1), (key2978, -1), (key2985, -1), (key2978, -1), (key2751, -1), (key2749, -1), (key2751, -1), (key2739, -1), (key2749, -1), (key2739, -1), (key2915, 1), (key2906, 1), (key2915, 1), (key2899, 1), (key2906, 1), (key2899, 1)]

theorem rawRowCheck4841 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form0 = rawRow4841 := by decide +kernel

def row4841 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

theorem rowCheck4841 : row4841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4841 := by decide +kernel

theorem rowEval4841 (x : Key → ℝ) : Integer.Sparse.eval row4841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4841, Integer.Sparse.eval_collectBalanced, rawRowCheck4841]

def rawRow4842 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 2), (key1335, 2), (key1389, 6), (key1544, -2), (key1770, -2), (key1770, -2), (key1422, -2), (key1453, -2), (key1453, -2), (key1571, 2), (key1786, 2), (key1786, 2)]

theorem rawRowCheck4842 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form1 = rawRow4842 := by decide +kernel

def row4842 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

theorem rowCheck4842 : row4842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4842 := by decide +kernel

theorem rowEval4842 (x : Key → ℝ) : Integer.Sparse.eval row4842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4842, Integer.Sparse.eval_collectBalanced, rawRowCheck4842]

def rawRow4843 : Integer.Sparse Key := [(key1294, -6), (key1335, 2), (key1314, 2), (key1335, 2), (key1389, 6), (key1770, -2), (key1544, -2), (key1770, -2), (key1453, -2), (key1422, -2), (key1453, -2), (key1786, 2), (key1571, 2), (key1786, 2)]

theorem rawRowCheck4843 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form1 = rawRow4843 := by decide +kernel

def row4843 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

theorem rowCheck4843 : row4843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4843 := by decide +kernel

theorem rowEval4843 (x : Key → ℝ) : Integer.Sparse.eval row4843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4843, Integer.Sparse.eval_collectBalanced, rawRowCheck4843]

def rawRow4844 : Integer.Sparse Key := [(key1294, -6), (key1335, 2), (key1335, 2), (key1314, 2), (key1389, 6), (key1770, -2), (key1770, -2), (key1544, -2), (key1453, -2), (key1453, -2), (key1422, -2), (key1786, 2), (key1786, 2), (key1571, 2)]

theorem rawRowCheck4844 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form1 = rawRow4844 := by decide +kernel

def row4844 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

theorem rowCheck4844 : row4844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4844 := by decide +kernel

theorem rowEval4844 (x : Key → ℝ) : Integer.Sparse.eval row4844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4844, Integer.Sparse.eval_collectBalanced, rawRowCheck4844]

def rawRow4845 : Integer.Sparse Key := [(key1389, -6), (key1422, 2), (key1453, 2), (key1453, 2), (key1294, 6), (key1571, -2), (key1786, -2), (key1786, -2), (key1314, -2), (key1335, -2), (key1335, -2), (key1544, 2), (key1770, 2), (key1770, 2)]

theorem rawRowCheck4845 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form1 = rawRow4845 := by decide +kernel

def row4845 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

theorem rowCheck4845 : row4845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4845 := by decide +kernel

theorem rowEval4845 (x : Key → ℝ) : Integer.Sparse.eval row4845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4845, Integer.Sparse.eval_collectBalanced, rawRowCheck4845]

def rawRow4846 : Integer.Sparse Key := [(key1389, -6), (key1453, 2), (key1422, 2), (key1453, 2), (key1294, 6), (key1786, -2), (key1571, -2), (key1786, -2), (key1335, -2), (key1314, -2), (key1335, -2), (key1770, 2), (key1544, 2), (key1770, 2)]

theorem rawRowCheck4846 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form1 = rawRow4846 := by decide +kernel

def row4846 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

theorem rowCheck4846 : row4846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4846 := by decide +kernel

theorem rowEval4846 (x : Key → ℝ) : Integer.Sparse.eval row4846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4846, Integer.Sparse.eval_collectBalanced, rawRowCheck4846]

def rawRow4847 : Integer.Sparse Key := [(key1389, -6), (key1453, 2), (key1453, 2), (key1422, 2), (key1294, 6), (key1786, -2), (key1786, -2), (key1571, -2), (key1335, -2), (key1335, -2), (key1314, -2), (key1770, 2), (key1770, 2), (key1544, 2)]

theorem rawRowCheck4847 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form1 = rawRow4847 := by decide +kernel

def row4847 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

theorem rowCheck4847 : row4847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4847 := by decide +kernel

theorem rowEval4847 (x : Key → ℝ) : Integer.Sparse.eval row4847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4847, Integer.Sparse.eval_collectBalanced, rawRowCheck4847]

def rawRow4848 : Integer.Sparse Key := [(key1422, -6), (key1389, 2), (key1453, 2), (key1453, 2), (key1571, 6), (key1294, -2), (key1786, -2), (key1786, -2), (key1544, -2), (key1653, -2), (key1653, -2), (key1314, 2), (key1811, 2), (key1811, 2)]

theorem rawRowCheck4848 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form1 = rawRow4848 := by decide +kernel

def row4848 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

theorem rowCheck4848 : row4848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4848 := by decide +kernel

theorem rowEval4848 (x : Key → ℝ) : Integer.Sparse.eval row4848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4848, Integer.Sparse.eval_collectBalanced, rawRowCheck4848]

def rawRow4849 : Integer.Sparse Key := [(key1422, -6), (key1453, 2), (key1389, 2), (key1453, 2), (key1571, 6), (key1786, -2), (key1294, -2), (key1786, -2), (key1653, -2), (key1544, -2), (key1653, -2), (key1811, 2), (key1314, 2), (key1811, 2)]

theorem rawRowCheck4849 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form1 = rawRow4849 := by decide +kernel

def row4849 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

theorem rowCheck4849 : row4849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4849 := by decide +kernel

theorem rowEval4849 (x : Key → ℝ) : Integer.Sparse.eval row4849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4849, Integer.Sparse.eval_collectBalanced, rawRowCheck4849]

def rawRow4850 : Integer.Sparse Key := [(key1422, -6), (key1453, 2), (key1453, 2), (key1389, 2), (key1571, 6), (key1786, -2), (key1786, -2), (key1294, -2), (key1653, -2), (key1653, -2), (key1544, -2), (key1811, 2), (key1811, 2), (key1314, 2)]

theorem rawRowCheck4850 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form1 = rawRow4850 := by decide +kernel

def row4850 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

theorem rowCheck4850 : row4850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4850 := by decide +kernel

theorem rowEval4850 (x : Key → ℝ) : Integer.Sparse.eval row4850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4850, Integer.Sparse.eval_collectBalanced, rawRowCheck4850]

def rawRow4851 : Integer.Sparse Key := [(key1571, -6), (key1544, 2), (key1653, 2), (key1653, 2), (key1422, 6), (key1314, -2), (key1811, -2), (key1811, -2), (key1389, -2), (key1453, -2), (key1453, -2), (key1294, 2), (key1786, 2), (key1786, 2)]

theorem rawRowCheck4851 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form1 = rawRow4851 := by decide +kernel

def row4851 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

theorem rowCheck4851 : row4851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4851 := by decide +kernel

theorem rowEval4851 (x : Key → ℝ) : Integer.Sparse.eval row4851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4851, Integer.Sparse.eval_collectBalanced, rawRowCheck4851]

def rawRow4852 : Integer.Sparse Key := [(key1571, -6), (key1653, 2), (key1544, 2), (key1653, 2), (key1422, 6), (key1811, -2), (key1314, -2), (key1811, -2), (key1453, -2), (key1389, -2), (key1453, -2), (key1786, 2), (key1294, 2), (key1786, 2)]

theorem rawRowCheck4852 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form1 = rawRow4852 := by decide +kernel

def row4852 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

theorem rowCheck4852 : row4852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4852 := by decide +kernel

theorem rowEval4852 (x : Key → ℝ) : Integer.Sparse.eval row4852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4852, Integer.Sparse.eval_collectBalanced, rawRowCheck4852]

def rawRow4853 : Integer.Sparse Key := [(key1571, -6), (key1653, 2), (key1653, 2), (key1544, 2), (key1422, 6), (key1811, -2), (key1811, -2), (key1314, -2), (key1453, -2), (key1453, -2), (key1389, -2), (key1786, 2), (key1786, 2), (key1294, 2)]

theorem rawRowCheck4853 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form1 = rawRow4853 := by decide +kernel

def row4853 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

theorem rowCheck4853 : row4853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4853 := by decide +kernel

theorem rowEval4853 (x : Key → ℝ) : Integer.Sparse.eval row4853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4853, Integer.Sparse.eval_collectBalanced, rawRowCheck4853]

def rawRow4854 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2671, 2), (key2671, 2), (key2676, 2), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2732, -1), (key2732, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2798, -1), (key2798, -1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2835, 1), (key2835, 1)]

theorem rawRowCheck4854 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form2 = rawRow4854 := by decide +kernel

def row4854 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

theorem rowCheck4854 : row4854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4854 := by decide +kernel

theorem rowEval4854 (x : Key → ℝ) : Integer.Sparse.eval row4854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4854, Integer.Sparse.eval_collectBalanced, rawRowCheck4854]

def rawRow4855 : Integer.Sparse Key := [(key2612, -2), (key2618, -2), (key2616, -2), (key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2671, 2), (key2676, 2), (key2671, 2), (key2726, -1), (key2732, -1), (key2706, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2794, -1), (key2798, -1), (key2786, -1), (key2798, -1), (key2786, -1), (key2794, -1), (key2829, 1), (key2835, 1), (key2809, 1), (key2835, 1), (key2809, 1), (key2829, 1)]

theorem rawRowCheck4855 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form2 = rawRow4855 := by decide +kernel

def row4855 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

theorem rowCheck4855 : row4855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4855 := by decide +kernel

theorem rowEval4855 (x : Key → ℝ) : Integer.Sparse.eval row4855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4855, Integer.Sparse.eval_collectBalanced, rawRowCheck4855]

def rawRow4856 : Integer.Sparse Key := [(key2618, -2), (key2612, -2), (key2616, -2), (key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2676, 2), (key2671, 2), (key2671, 2), (key2732, -1), (key2726, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2798, -1), (key2794, -1), (key2798, -1), (key2786, -1), (key2794, -1), (key2786, -1), (key2835, 1), (key2829, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2809, 1)]

theorem rawRowCheck4856 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form2 = rawRow4856 := by decide +kernel

def row4856 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

theorem rowCheck4856 : row4856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4856 := by decide +kernel

theorem rowEval4856 (x : Key → ℝ) : Integer.Sparse.eval row4856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4856, Integer.Sparse.eval_collectBalanced, rawRowCheck4856]

def rawRow4857 : Integer.Sparse Key := [(key2667, -2), (key2667, -2), (key2673, -2), (key2702, 1), (key2702, 1), (key2735, 1), (key2735, 1), (key2737, 1), (key2737, 1), (key2612, 2), (key2616, 2), (key2621, 2), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2835, -1), (key2835, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2644, -1), (key2644, -1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1)]

theorem rawRowCheck4857 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form2 = rawRow4857 := by decide +kernel

def row4857 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

theorem rowCheck4857 : row4857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4857 := by decide +kernel

theorem rowEval4857 (x : Key → ℝ) : Integer.Sparse.eval row4857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4857, Integer.Sparse.eval_collectBalanced, rawRowCheck4857]

def rawRow4858 : Integer.Sparse Key := [(key2667, -2), (key2673, -2), (key2667, -2), (key2735, 1), (key2737, 1), (key2702, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2612, 2), (key2618, 2), (key2616, 2), (key2829, -1), (key2835, -1), (key2809, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2640, -1), (key2644, -1), (key2632, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1)]

theorem rawRowCheck4858 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form2 = rawRow4858 := by decide +kernel

def row4858 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

theorem rowCheck4858 : row4858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4858 := by decide +kernel

theorem rowEval4858 (x : Key → ℝ) : Integer.Sparse.eval row4858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4858, Integer.Sparse.eval_collectBalanced, rawRowCheck4858]

def rawRow4859 : Integer.Sparse Key := [(key2673, -2), (key2667, -2), (key2667, -2), (key2737, 1), (key2735, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2702, 1), (key2618, 2), (key2612, 2), (key2616, 2), (key2835, -1), (key2829, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2644, -1), (key2640, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2632, -1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1)]

theorem rawRowCheck4859 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form2 = rawRow4859 := by decide +kernel

def row4859 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

theorem rowCheck4859 : row4859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4859 := by decide +kernel

theorem rowEval4859 (x : Key → ℝ) : Integer.Sparse.eval row4859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4859, Integer.Sparse.eval_collectBalanced, rawRowCheck4859]

def rawRow4860 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1)]

theorem rawRowCheck4860 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form2 = rawRow4860 := by decide +kernel

def row4860 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -2), (key2831, 2), (key2860, -2), (key2870, 2), (key3017, -2), (key3023, -2), (key3026, 2)]

theorem rowCheck4860 : row4860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4860 := by decide +kernel

theorem rowEval4860 (x : Key → ℝ) : Integer.Sparse.eval row4860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4860, Integer.Sparse.eval_collectBalanced, rawRowCheck4860]

def rawRow4861 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1)]

theorem rawRowCheck4861 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form2 = rawRow4861 := by decide +kernel

def row4861 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, 2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, 2)]

theorem rowCheck4861 : row4861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4861 := by decide +kernel

theorem rowEval4861 (x : Key → ℝ) : Integer.Sparse.eval row4861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4861, Integer.Sparse.eval_collectBalanced, rawRowCheck4861]

def rawRow4862 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1)]

theorem rawRowCheck4862 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form2 = rawRow4862 := by decide +kernel

def row4862 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, 2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, 2)]

theorem rowCheck4862 : row4862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4862 := by decide +kernel

theorem rowEval4862 (x : Key → ℝ) : Integer.Sparse.eval row4862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4862, Integer.Sparse.eval_collectBalanced, rawRowCheck4862]

def rawRow4863 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2782, 1), (key2782, 1), (key2893, 1), (key2893, 1), (key2904, 1), (key2904, 1), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1)]

theorem rawRowCheck4863 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form2 = rawRow4863 := by decide +kernel

def row4863 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 2), (key2831, -2), (key2893, 2), (key2904, 2), (key2972, -2), (key2983, -2), (key3017, 2)]

theorem rowCheck4863 : row4863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4863 := by decide +kernel

theorem rowEval4863 (x : Key → ℝ) : Integer.Sparse.eval row4863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4863, Integer.Sparse.eval_collectBalanced, rawRowCheck4863]

end MUB6.Certificate.GramRows

end OAI
