import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8832 : Integer.Sparse Key := [(key2559, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2449, -6), (key2449, -6), (key2449, -6), (key2354, -6)]

theorem rawRowCheck8832 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11 = rawRow8832 := by decide +kernel

def row8832 : Integer.Sparse Key := [(key2354, -6), (key2449, -18), (key2514, 18), (key2559, 6)]

theorem rowCheck8832 : row8832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8832 := by decide +kernel

theorem rowEval8832 (x : Key → ℝ) : Integer.Sparse.eval row8832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck8832, Integer.Sparse.eval_collectBalanced, rawRowCheck8832]

def rawRow8833 : Integer.Sparse Key := [(key2353, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2566, -6), (key2566, -6), (key2566, -6), (key2578, -6)]

theorem rawRowCheck8833 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12 = rawRow8833 := by decide +kernel

def row8833 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

theorem rowCheck8833 : row8833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8833 := by decide +kernel

theorem rowEval8833 (x : Key → ℝ) : Integer.Sparse.eval row8833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block3.form12) x := by
  rw [rowCheck8833, Integer.Sparse.eval_collectBalanced, rawRowCheck8833]

def rawRow8834 : Integer.Sparse Key := [(key2359, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2566, -6), (key2566, -6), (key2578, -6), (key2566, -6)]

theorem rawRowCheck8834 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12 = rawRow8834 := by decide +kernel

def row8834 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

theorem rowCheck8834 : row8834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8834 := by decide +kernel

theorem rowEval8834 (x : Key → ℝ) : Integer.Sparse.eval row8834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8834, Integer.Sparse.eval_collectBalanced, rawRowCheck8834]

def rawRow8835 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2566, -6), (key2578, -6), (key2566, -6), (key2566, -6)]

theorem rawRowCheck8835 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12 = rawRow8835 := by decide +kernel

def row8835 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

theorem rowCheck8835 : row8835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8835 := by decide +kernel

theorem rowEval8835 (x : Key → ℝ) : Integer.Sparse.eval row8835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8835, Integer.Sparse.eval_collectBalanced, rawRowCheck8835]

def rawRow8836 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2578, -6), (key2566, -6), (key2566, -6), (key2566, -6)]

theorem rawRowCheck8836 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow8836 := by decide +kernel

def row8836 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2566, -18), (key2578, -6)]

theorem rowCheck8836 : row8836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8836 := by decide +kernel

theorem rowEval8836 (x : Key → ℝ) : Integer.Sparse.eval row8836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8836, Integer.Sparse.eval_collectBalanced, rawRowCheck8836]

def rawRow8837 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2353, -6), (key2448, -6), (key2448, -6), (key2448, -6)]

theorem rawRowCheck8837 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12 = rawRow8837 := by decide +kernel

def row8837 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

theorem rowCheck8837 : row8837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8837 := by decide +kernel

theorem rowEval8837 (x : Key → ℝ) : Integer.Sparse.eval row8837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8837, Integer.Sparse.eval_collectBalanced, rawRowCheck8837]

def rawRow8838 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2448, -6), (key2353, -6), (key2448, -6), (key2448, -6)]

theorem rawRowCheck8838 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12 = rawRow8838 := by decide +kernel

def row8838 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

theorem rowCheck8838 : row8838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8838 := by decide +kernel

theorem rowEval8838 (x : Key → ℝ) : Integer.Sparse.eval row8838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8838, Integer.Sparse.eval_collectBalanced, rawRowCheck8838]

def rawRow8839 : Integer.Sparse Key := [(key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2448, -6), (key2448, -6), (key2353, -6), (key2448, -6)]

theorem rawRowCheck8839 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12 = rawRow8839 := by decide +kernel

def row8839 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

theorem rowCheck8839 : row8839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8839 := by decide +kernel

theorem rowEval8839 (x : Key → ℝ) : Integer.Sparse.eval row8839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck8839, Integer.Sparse.eval_collectBalanced, rawRowCheck8839]

def rawRow8840 : Integer.Sparse Key := [(key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2448, -6), (key2448, -6), (key2448, -6), (key2353, -6)]

theorem rawRowCheck8840 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12 = rawRow8840 := by decide +kernel

def row8840 : Integer.Sparse Key := [(key2353, -6), (key2448, -18), (key2566, 18), (key2578, 6)]

theorem rowCheck8840 : row8840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8840 := by decide +kernel

theorem rowEval8840 (x : Key → ℝ) : Integer.Sparse.eval row8840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck8840, Integer.Sparse.eval_collectBalanced, rawRowCheck8840]

def rawRow8841 : Integer.Sparse Key := [(key2268, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2294, 2), (key2272, 2), (key2294, 2), (key2323, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2336, -2)]

theorem rawRowCheck8841 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form0 = rawRow8841 := by decide +kernel

def row8841 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

theorem rowCheck8841 : row8841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8841 := by decide +kernel

theorem rowEval8841 (x : Key → ℝ) : Integer.Sparse.eval row8841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8841, Integer.Sparse.eval_collectBalanced, rawRowCheck8841]

def rawRow8842 : Integer.Sparse Key := [(key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2294, 2), (key2272, 2), (key2324, -2), (key2323, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2336, -2), (key2324, -2)]

theorem rawRowCheck8842 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form0 = rawRow8842 := by decide +kernel

def row8842 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

theorem rowCheck8842 : row8842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8842 := by decide +kernel

theorem rowEval8842 (x : Key → ℝ) : Integer.Sparse.eval row8842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8842, Integer.Sparse.eval_collectBalanced, rawRowCheck8842]

def rawRow8843 : Integer.Sparse Key := [(key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2294, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2324, -2)]

theorem rawRowCheck8843 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form0 = rawRow8843 := by decide +kernel

def row8843 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

theorem rowCheck8843 : row8843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8843 := by decide +kernel

theorem rowEval8843 (x : Key → ℝ) : Integer.Sparse.eval row8843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8843, Integer.Sparse.eval_collectBalanced, rawRowCheck8843]

def rawRow8844 : Integer.Sparse Key := [(key2294, 2), (key2294, 2), (key2294, 2), (key2272, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2336, -2), (key2336, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2323, -2), (key2323, -2)]

theorem rawRowCheck8844 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow8844 := by decide +kernel

def row8844 : Integer.Sparse Key := [(key2268, 12), (key2272, 6), (key2294, 6), (key2323, -6), (key2324, -12), (key2336, -6)]

theorem rowCheck8844 : row8844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8844 := by decide +kernel

theorem rowEval8844 (x : Key → ℝ) : Integer.Sparse.eval row8844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8844, Integer.Sparse.eval_collectBalanced, rawRowCheck8844]

def rawRow8845 : Integer.Sparse Key := [(key1999, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2323, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2336, 2), (key1999, -2), (key2003, -2), (key2003, -2), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2324, -2), (key2324, -2), (key2336, -2)]

theorem rawRowCheck8845 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form0 = rawRow8845 := by decide +kernel

def row8845 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8845 : row8845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8845 := by decide +kernel

theorem rowEval8845 (x : Key → ℝ) : Integer.Sparse.eval row8845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8845, Integer.Sparse.eval_collectBalanced, rawRowCheck8845]

def rawRow8846 : Integer.Sparse Key := [(key1999, 2), (key2003, 2), (key1999, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2003, -2), (key1999, -2), (key2003, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2324, -2), (key2336, -2), (key2324, -2)]

theorem rawRowCheck8846 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form0 = rawRow8846 := by decide +kernel

def row8846 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8846 : row8846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8846 := by decide +kernel

theorem rowEval8846 (x : Key → ℝ) : Integer.Sparse.eval row8846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8846, Integer.Sparse.eval_collectBalanced, rawRowCheck8846]

def rawRow8847 : Integer.Sparse Key := [(key2003, 2), (key1999, 2), (key1999, 2), (key2294, 2), (key2268, 2), (key2268, 2), (key2336, 2), (key2336, 2), (key2324, 2), (key2324, 2), (key2323, 2), (key2323, 2), (key2003, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2324, -2)]

theorem rawRowCheck8847 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form0 = rawRow8847 := by decide +kernel

def row8847 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8847 : row8847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8847 := by decide +kernel

theorem rowEval8847 (x : Key → ℝ) : Integer.Sparse.eval row8847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8847, Integer.Sparse.eval_collectBalanced, rawRowCheck8847]

def rawRow8848 : Integer.Sparse Key := [(key2268, 2), (key2323, 2), (key2324, 2), (key1999, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2294, 2), (key2324, 2), (key2336, 2), (key2268, -2), (key2272, -2), (key2324, -2), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key2003, -2), (key2272, -2), (key2294, -2)]

theorem rawRowCheck8848 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form0 = rawRow8848 := by decide +kernel

def row8848 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8848 : row8848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8848 := by decide +kernel

theorem rowEval8848 (x : Key → ℝ) : Integer.Sparse.eval row8848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8848, Integer.Sparse.eval_collectBalanced, rawRowCheck8848]

def rawRow8849 : Integer.Sparse Key := [(key2268, 2), (key2324, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2323, 2), (key2003, 2), (key1999, 2), (key2294, 2), (key2268, 2), (key2336, 2), (key2324, 2), (key2272, -2), (key2268, -2), (key2324, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2003, -2), (key2294, -2), (key2272, -2)]

theorem rawRowCheck8849 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form0 = rawRow8849 := by decide +kernel

def row8849 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8849 : row8849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8849 := by decide +kernel

theorem rowEval8849 (x : Key → ℝ) : Integer.Sparse.eval row8849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8849, Integer.Sparse.eval_collectBalanced, rawRowCheck8849]

def rawRow8850 : Integer.Sparse Key := [(key2323, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2268, 2), (key2324, 2), (key1999, 2), (key2336, 2), (key2003, 2), (key2294, 2), (key2268, -2), (key2324, -2), (key2272, -2), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2272, -2), (key2003, -2), (key2294, -2)]

theorem rawRowCheck8850 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form0 = rawRow8850 := by decide +kernel

def row8850 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8850 : row8850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8850 := by decide +kernel

theorem rowEval8850 (x : Key → ℝ) : Integer.Sparse.eval row8850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8850, Integer.Sparse.eval_collectBalanced, rawRowCheck8850]

def rawRow8851 : Integer.Sparse Key := [(key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2324, 2), (key2268, 2), (key2336, 2), (key1999, 2), (key2294, 2), (key2003, 2), (key2324, -2), (key2268, -2), (key2272, -2), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, -2), (key2294, -2), (key2003, -2)]

theorem rawRowCheck8851 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form0 = rawRow8851 := by decide +kernel

def row8851 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8851 : row8851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8851 := by decide +kernel

theorem rowEval8851 (x : Key → ℝ) : Integer.Sparse.eval row8851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8851, Integer.Sparse.eval_collectBalanced, rawRowCheck8851]

def rawRow8852 : Integer.Sparse Key := [(key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key2294, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key1999, 2), (key2268, 2), (key2272, -2), (key2324, -2), (key2268, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2294, -2), (key2003, -2), (key2272, -2)]

theorem rawRowCheck8852 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form0 = rawRow8852 := by decide +kernel

def row8852 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8852 : row8852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8852 := by decide +kernel

theorem rowEval8852 (x : Key → ℝ) : Integer.Sparse.eval row8852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8852, Integer.Sparse.eval_collectBalanced, rawRowCheck8852]

def rawRow8853 : Integer.Sparse Key := [(key2324, 2), (key2323, 2), (key2268, 2), (key2336, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2294, 2), (key2324, 2), (key2003, 2), (key2268, 2), (key1999, 2), (key2324, -2), (key2272, -2), (key2268, -2), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, -2), (key2272, -2), (key2003, -2)]

theorem rawRowCheck8853 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form0 = rawRow8853 := by decide +kernel

def row8853 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8853 : row8853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8853 := by decide +kernel

theorem rowEval8853 (x : Key → ℝ) : Integer.Sparse.eval row8853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8853, Integer.Sparse.eval_collectBalanced, rawRowCheck8853]

def rawRow8854 : Integer.Sparse Key := [(key2294, 2), (key2336, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2324, 2), (key1999, 2), (key1999, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2294, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2003, -2), (key2272, -2), (key2272, -2), (key2324, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2268, -2)]

theorem rawRowCheck8854 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8854 := by decide +kernel

def row8854 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8854 : row8854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8854 := by decide +kernel

theorem rowEval8854 (x : Key → ℝ) : Integer.Sparse.eval row8854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8854, Integer.Sparse.eval_collectBalanced, rawRowCheck8854]

def rawRow8855 : Integer.Sparse Key := [(key2336, 2), (key2294, 2), (key2336, 2), (key2324, 2), (key2003, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2323, 2), (key1999, 2), (key2268, 2), (key2294, -2), (key2336, -2), (key2294, -2), (key2272, -2), (key2324, -2), (key2003, -2), (key2324, -2), (key2003, -2), (key2272, -2), (key2268, -2), (key1999, -2), (key2268, -2)]

theorem rawRowCheck8855 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8855 := by decide +kernel

def row8855 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8855 : row8855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8855 := by decide +kernel

theorem rowEval8855 (x : Key → ℝ) : Integer.Sparse.eval row8855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8855, Integer.Sparse.eval_collectBalanced, rawRowCheck8855]

def rawRow8856 : Integer.Sparse Key := [(key2336, 2), (key2336, 2), (key2294, 2), (key2324, 2), (key2324, 2), (key2003, 2), (key2323, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2268, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2294, -2), (key2324, -2), (key2272, -2), (key2324, -2), (key2003, -2), (key2272, -2), (key2003, -2), (key2268, -2), (key2268, -2), (key1999, -2)]

theorem rawRowCheck8856 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8856 := by decide +kernel

def row8856 : Integer.Sparse Key := [(key1999, 2), (key2003, -2), (key2272, -4), (key2294, -2), (key2323, 4), (key2336, 2)]

theorem rowCheck8856 : row8856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8856 := by decide +kernel

theorem rowEval8856 (x : Key → ℝ) : Integer.Sparse.eval row8856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8856, Integer.Sparse.eval_collectBalanced, rawRowCheck8856]

def rawRow8857 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key942, 6), (key942, 6), (key946, 6)]

theorem rawRowCheck8857 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form1 = rawRow8857 := by decide +kernel

def row8857 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

theorem rowCheck8857 : row8857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8857 := by decide +kernel

theorem rowEval8857 (x : Key → ℝ) : Integer.Sparse.eval row8857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8857, Integer.Sparse.eval_collectBalanced, rawRowCheck8857]

def rawRow8858 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key942, 6), (key946, 6), (key942, 6)]

theorem rawRowCheck8858 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form1 = rawRow8858 := by decide +kernel

def row8858 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

theorem rowCheck8858 : row8858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8858 := by decide +kernel

theorem rowEval8858 (x : Key → ℝ) : Integer.Sparse.eval row8858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8858, Integer.Sparse.eval_collectBalanced, rawRowCheck8858]

def rawRow8859 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key946, 6), (key942, 6), (key942, 6)]

theorem rawRowCheck8859 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form1 = rawRow8859 := by decide +kernel

def row8859 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

theorem rowCheck8859 : row8859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8859 := by decide +kernel

theorem rowEval8859 (x : Key → ℝ) : Integer.Sparse.eval row8859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8859, Integer.Sparse.eval_collectBalanced, rawRowCheck8859]

def rawRow8860 : Integer.Sparse Key := [(key724, -24), (key946, 6), (key942, 6), (key942, 6), (key942, 6)]

theorem rawRowCheck8860 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow8860 := by decide +kernel

def row8860 : Integer.Sparse Key := [(key724, -24), (key942, 18), (key946, 6)]

theorem rowCheck8860 : row8860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8860 := by decide +kernel

theorem rowEval8860 (x : Key → ℝ) : Integer.Sparse.eval row8860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8860, Integer.Sparse.eval_collectBalanced, rawRowCheck8860]

def rawRow8861 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key942, 6), (key942, 6), (key946, 6)]

theorem rawRowCheck8861 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form1 = rawRow8861 := by decide +kernel

def row8861 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8861 : row8861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8861 := by decide +kernel

theorem rowEval8861 (x : Key → ℝ) : Integer.Sparse.eval row8861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8861, Integer.Sparse.eval_collectBalanced, rawRowCheck8861]

def rawRow8862 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key942, 6), (key946, 6), (key942, 6)]

theorem rawRowCheck8862 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form1 = rawRow8862 := by decide +kernel

def row8862 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8862 : row8862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8862 := by decide +kernel

theorem rowEval8862 (x : Key → ℝ) : Integer.Sparse.eval row8862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8862, Integer.Sparse.eval_collectBalanced, rawRowCheck8862]

def rawRow8863 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key946, 6), (key942, 6), (key942, 6)]

theorem rawRowCheck8863 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form1 = rawRow8863 := by decide +kernel

def row8863 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8863 : row8863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8863 := by decide +kernel

theorem rowEval8863 (x : Key → ℝ) : Integer.Sparse.eval row8863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8863, Integer.Sparse.eval_collectBalanced, rawRowCheck8863]

def rawRow8864 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key724, 6), (key942, 6), (key946, 6)]

theorem rawRowCheck8864 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form1 = rawRow8864 := by decide +kernel

def row8864 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8864 : row8864 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8864 := by decide +kernel

theorem rowEval8864 (x : Key → ℝ) : Integer.Sparse.eval row8864 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8864, Integer.Sparse.eval_collectBalanced, rawRowCheck8864]

def rawRow8865 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key724, 6), (key946, 6), (key942, 6)]

theorem rawRowCheck8865 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form1 = rawRow8865 := by decide +kernel

def row8865 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8865 : row8865 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8865 := by decide +kernel

theorem rowEval8865 (x : Key → ℝ) : Integer.Sparse.eval row8865 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8865, Integer.Sparse.eval_collectBalanced, rawRowCheck8865]

def rawRow8866 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key942, 6), (key724, 6), (key946, 6)]

theorem rawRowCheck8866 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form1 = rawRow8866 := by decide +kernel

def row8866 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8866 : row8866 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8866 := by decide +kernel

theorem rowEval8866 (x : Key → ℝ) : Integer.Sparse.eval row8866 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8866, Integer.Sparse.eval_collectBalanced, rawRowCheck8866]

def rawRow8867 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key942, 6), (key946, 6), (key724, 6)]

theorem rawRowCheck8867 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form1 = rawRow8867 := by decide +kernel

def row8867 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8867 : row8867 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8867 := by decide +kernel

theorem rowEval8867 (x : Key → ℝ) : Integer.Sparse.eval row8867 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8867, Integer.Sparse.eval_collectBalanced, rawRowCheck8867]

def rawRow8868 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key946, 6), (key724, 6), (key942, 6)]

theorem rawRowCheck8868 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form1 = rawRow8868 := by decide +kernel

def row8868 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8868 : row8868 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8868 := by decide +kernel

theorem rowEval8868 (x : Key → ℝ) : Integer.Sparse.eval row8868 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8868, Integer.Sparse.eval_collectBalanced, rawRowCheck8868]

def rawRow8869 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key946, 6), (key942, 6), (key724, 6)]

theorem rawRowCheck8869 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form1 = rawRow8869 := by decide +kernel

def row8869 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8869 : row8869 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8869 := by decide +kernel

theorem rowEval8869 (x : Key → ℝ) : Integer.Sparse.eval row8869 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8869, Integer.Sparse.eval_collectBalanced, rawRowCheck8869]

def rawRow8870 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key724, 6), (key942, 6), (key942, 6)]

theorem rawRowCheck8870 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow8870 := by decide +kernel

def row8870 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8870 : row8870 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8870 := by decide +kernel

theorem rowEval8870 (x : Key → ℝ) : Integer.Sparse.eval row8870 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8870, Integer.Sparse.eval_collectBalanced, rawRowCheck8870]

def rawRow8871 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key942, 6), (key724, 6), (key942, 6)]

theorem rawRowCheck8871 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow8871 := by decide +kernel

def row8871 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8871 : row8871 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8871 := by decide +kernel

theorem rowEval8871 (x : Key → ℝ) : Integer.Sparse.eval row8871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8871, Integer.Sparse.eval_collectBalanced, rawRowCheck8871]

def rawRow8872 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key942, 6), (key942, 6), (key724, 6)]

theorem rawRowCheck8872 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow8872 := by decide +kernel

def row8872 : Integer.Sparse Key := [(key724, 6), (key942, -12), (key946, 6)]

theorem rowCheck8872 : row8872 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8872 := by decide +kernel

theorem rowEval8872 (x : Key → ℝ) : Integer.Sparse.eval row8872 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8872, Integer.Sparse.eval_collectBalanced, rawRowCheck8872]

def rawRow8873 : Integer.Sparse Key := [(key713, -6), (key715, -6), (key715, -6), (key715, -6), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key892, 2), (key890, 2), (key914, 2), (key892, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2)]

theorem rawRowCheck8873 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8873 := by decide +kernel

def row8873 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

theorem rowCheck8873 : row8873 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8873 := by decide +kernel

theorem rowEval8873 (x : Key → ℝ) : Integer.Sparse.eval row8873 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8873, Integer.Sparse.eval_collectBalanced, rawRowCheck8873]

def rawRow8874 : Integer.Sparse Key := [(key715, -6), (key713, -6), (key715, -6), (key715, -6), (key892, 2), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key914, 2), (key890, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key892, 2)]

theorem rawRowCheck8874 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8874 := by decide +kernel

def row8874 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

theorem rowCheck8874 : row8874 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8874 := by decide +kernel

theorem rowEval8874 (x : Key → ℝ) : Integer.Sparse.eval row8874 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8874, Integer.Sparse.eval_collectBalanced, rawRowCheck8874]

def rawRow8875 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key713, -6), (key715, -6), (key892, 2), (key892, 2), (key890, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key914, 2), (key892, 2), (key892, 2)]

theorem rawRowCheck8875 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8875 := by decide +kernel

def row8875 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

theorem rowCheck8875 : row8875 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8875 := by decide +kernel

theorem rowEval8875 (x : Key → ℝ) : Integer.Sparse.eval row8875 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8875, Integer.Sparse.eval_collectBalanced, rawRowCheck8875]

def rawRow8876 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key715, -6), (key713, -6), (key914, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key890, 2)]

theorem rawRowCheck8876 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow8876 := by decide +kernel

def row8876 : Integer.Sparse Key := [(key713, -6), (key715, -18), (key890, 6), (key892, 12), (key914, 6)]

theorem rowCheck8876 : row8876 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8876 := by decide +kernel

theorem rowEval8876 (x : Key → ℝ) : Integer.Sparse.eval row8876 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8876, Integer.Sparse.eval_collectBalanced, rawRowCheck8876]

def rawRow8877 : Integer.Sparse Key := [(key890, -6), (key892, -6), (key892, -6), (key959, -6), (key713, 2), (key715, 2), (key715, 2), (key890, 2), (key892, 2), (key890, 2), (key914, 2), (key892, 2), (key914, 2), (key959, 2), (key959, 2), (key966, 2)]

theorem rawRowCheck8877 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8877 := by decide +kernel

def row8877 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8877 : row8877 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8877 := by decide +kernel

theorem rowEval8877 (x : Key → ℝ) : Integer.Sparse.eval row8877 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8877, Integer.Sparse.eval_collectBalanced, rawRowCheck8877]

def rawRow8878 : Integer.Sparse Key := [(key892, -6), (key890, -6), (key892, -6), (key959, -6), (key715, 2), (key713, 2), (key715, 2), (key892, 2), (key890, 2), (key914, 2), (key890, 2), (key914, 2), (key892, 2), (key959, 2), (key966, 2), (key959, 2)]

theorem rawRowCheck8878 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8878 := by decide +kernel

def row8878 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8878 : row8878 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8878 := by decide +kernel

theorem rowEval8878 (x : Key → ℝ) : Integer.Sparse.eval row8878 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8878, Integer.Sparse.eval_collectBalanced, rawRowCheck8878]

def rawRow8879 : Integer.Sparse Key := [(key892, -6), (key892, -6), (key890, -6), (key959, -6), (key715, 2), (key715, 2), (key713, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key966, 2), (key959, 2), (key959, 2)]

theorem rawRowCheck8879 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8879 := by decide +kernel

def row8879 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8879 : row8879 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8879 := by decide +kernel

theorem rowEval8879 (x : Key → ℝ) : Integer.Sparse.eval row8879 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8879, Integer.Sparse.eval_collectBalanced, rawRowCheck8879]

def rawRow8880 : Integer.Sparse Key := [(key890, -6), (key892, -6), (key959, -6), (key892, -6), (key890, 2), (key892, 2), (key959, 2), (key713, 2), (key715, 2), (key890, 2), (key914, 2), (key959, 2), (key966, 2), (key715, 2), (key892, 2), (key914, 2)]

theorem rawRowCheck8880 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form2 = rawRow8880 := by decide +kernel

def row8880 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8880 : row8880 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8880 := by decide +kernel

theorem rowEval8880 (x : Key → ℝ) : Integer.Sparse.eval row8880 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8880, Integer.Sparse.eval_collectBalanced, rawRowCheck8880]

def rawRow8881 : Integer.Sparse Key := [(key892, -6), (key890, -6), (key959, -6), (key892, -6), (key892, 2), (key890, 2), (key959, 2), (key715, 2), (key713, 2), (key914, 2), (key890, 2), (key966, 2), (key959, 2), (key715, 2), (key914, 2), (key892, 2)]

theorem rawRowCheck8881 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form2 = rawRow8881 := by decide +kernel

def row8881 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8881 : row8881 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8881 := by decide +kernel

theorem rowEval8881 (x : Key → ℝ) : Integer.Sparse.eval row8881 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8881, Integer.Sparse.eval_collectBalanced, rawRowCheck8881]

def rawRow8882 : Integer.Sparse Key := [(key890, -6), (key959, -6), (key892, -6), (key892, -6), (key890, 2), (key959, 2), (key892, 2), (key890, 2), (key959, 2), (key713, 2), (key966, 2), (key715, 2), (key914, 2), (key892, 2), (key715, 2), (key914, 2)]

theorem rawRowCheck8882 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form2 = rawRow8882 := by decide +kernel

def row8882 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8882 : row8882 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8882 := by decide +kernel

theorem rowEval8882 (x : Key → ℝ) : Integer.Sparse.eval row8882 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8882, Integer.Sparse.eval_collectBalanced, rawRowCheck8882]

def rawRow8883 : Integer.Sparse Key := [(key959, -6), (key890, -6), (key892, -6), (key892, -6), (key959, 2), (key890, 2), (key892, 2), (key959, 2), (key890, 2), (key966, 2), (key713, 2), (key914, 2), (key715, 2), (key892, 2), (key914, 2), (key715, 2)]

theorem rawRowCheck8883 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form2 = rawRow8883 := by decide +kernel

def row8883 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8883 : row8883 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8883 := by decide +kernel

theorem rowEval8883 (x : Key → ℝ) : Integer.Sparse.eval row8883 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8883, Integer.Sparse.eval_collectBalanced, rawRowCheck8883]

def rawRow8884 : Integer.Sparse Key := [(key892, -6), (key959, -6), (key890, -6), (key892, -6), (key892, 2), (key959, 2), (key890, 2), (key914, 2), (key966, 2), (key715, 2), (key959, 2), (key713, 2), (key890, 2), (key914, 2), (key715, 2), (key892, 2)]

theorem rawRowCheck8884 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form2 = rawRow8884 := by decide +kernel

def row8884 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8884 : row8884 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8884 := by decide +kernel

theorem rowEval8884 (x : Key → ℝ) : Integer.Sparse.eval row8884 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8884, Integer.Sparse.eval_collectBalanced, rawRowCheck8884]

def rawRow8885 : Integer.Sparse Key := [(key959, -6), (key892, -6), (key890, -6), (key892, -6), (key959, 2), (key892, 2), (key890, 2), (key966, 2), (key914, 2), (key959, 2), (key715, 2), (key890, 2), (key713, 2), (key914, 2), (key892, 2), (key715, 2)]

theorem rawRowCheck8885 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form2 = rawRow8885 := by decide +kernel

def row8885 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8885 : row8885 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8885 := by decide +kernel

theorem rowEval8885 (x : Key → ℝ) : Integer.Sparse.eval row8885 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8885, Integer.Sparse.eval_collectBalanced, rawRowCheck8885]

def rawRow8886 : Integer.Sparse Key := [(key892, -6), (key892, -6), (key959, -6), (key890, -6), (key914, 2), (key914, 2), (key966, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key959, 2), (key959, 2), (key713, 2), (key890, 2), (key890, 2)]

theorem rawRowCheck8886 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow8886 := by decide +kernel

def row8886 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8886 : row8886 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8886 := by decide +kernel

theorem rowEval8886 (x : Key → ℝ) : Integer.Sparse.eval row8886 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8886, Integer.Sparse.eval_collectBalanced, rawRowCheck8886]

def rawRow8887 : Integer.Sparse Key := [(key892, -6), (key959, -6), (key892, -6), (key890, -6), (key914, 2), (key966, 2), (key914, 2), (key892, 2), (key959, 2), (key715, 2), (key959, 2), (key715, 2), (key892, 2), (key890, 2), (key713, 2), (key890, 2)]

theorem rawRowCheck8887 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow8887 := by decide +kernel

def row8887 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8887 : row8887 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8887 := by decide +kernel

theorem rowEval8887 (x : Key → ℝ) : Integer.Sparse.eval row8887 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8887, Integer.Sparse.eval_collectBalanced, rawRowCheck8887]

def rawRow8888 : Integer.Sparse Key := [(key959, -6), (key892, -6), (key892, -6), (key890, -6), (key966, 2), (key914, 2), (key914, 2), (key959, 2), (key892, 2), (key959, 2), (key715, 2), (key892, 2), (key715, 2), (key890, 2), (key890, 2), (key713, 2)]

theorem rawRowCheck8888 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow8888 := by decide +kernel

def row8888 : Integer.Sparse Key := [(key713, 2), (key715, 4), (key890, -2), (key892, -8), (key914, 4), (key959, -2), (key966, 2)]

theorem rowCheck8888 : row8888 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8888 := by decide +kernel

theorem rowEval8888 (x : Key → ℝ) : Integer.Sparse.eval row8888 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8888, Integer.Sparse.eval_collectBalanced, rawRowCheck8888]

def rawRow8889 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2203, -6), (key2206, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2318, 2), (key2321, 2)]

theorem rawRowCheck8889 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8889 := by decide +kernel

def row8889 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

theorem rowCheck8889 : row8889 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8889 := by decide +kernel

theorem rowEval8889 (x : Key → ℝ) : Integer.Sparse.eval row8889 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8889, Integer.Sparse.eval_collectBalanced, rawRowCheck8889]

def rawRow8890 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2206, -6), (key2203, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2318, 2)]

theorem rawRowCheck8890 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8890 := by decide +kernel

def row8890 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

theorem rowCheck8890 : row8890 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8890 := by decide +kernel

theorem rowEval8890 (x : Key → ℝ) : Integer.Sparse.eval row8890 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8890, Integer.Sparse.eval_collectBalanced, rawRowCheck8890]

def rawRow8891 : Integer.Sparse Key := [(key2203, -6), (key2206, -6), (key2203, -6), (key2203, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck8891 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8891 := by decide +kernel

def row8891 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

theorem rowCheck8891 : row8891 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8891 := by decide +kernel

theorem rowEval8891 (x : Key → ℝ) : Integer.Sparse.eval row8891 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8891, Integer.Sparse.eval_collectBalanced, rawRowCheck8891]

def rawRow8892 : Integer.Sparse Key := [(key2206, -6), (key2203, -6), (key2203, -6), (key2203, -6), (key2321, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck8892 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow8892 := by decide +kernel

def row8892 : Integer.Sparse Key := [(key2203, -18), (key2206, -6), (key2317, 12), (key2318, 6), (key2321, 6)]

theorem rowCheck8892 : row8892 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8892 := by decide +kernel

theorem rowEval8892 (x : Key → ℝ) : Integer.Sparse.eval row8892 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8892, Integer.Sparse.eval_collectBalanced, rawRowCheck8892]

def rawRow8893 : Integer.Sparse Key := [(key2098, -6), (key2317, -6), (key2317, -6), (key2321, -6), (key2098, 2), (key2098, 2), (key2099, 2), (key2203, 2), (key2203, 2), (key2206, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2318, 2), (key2321, 2)]

theorem rawRowCheck8893 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8893 := by decide +kernel

def row8893 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8893 : row8893 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8893 := by decide +kernel

theorem rowEval8893 (x : Key → ℝ) : Integer.Sparse.eval row8893 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8893, Integer.Sparse.eval_collectBalanced, rawRowCheck8893]

def rawRow8894 : Integer.Sparse Key := [(key2098, -6), (key2317, -6), (key2321, -6), (key2317, -6), (key2098, 2), (key2099, 2), (key2098, 2), (key2203, 2), (key2206, 2), (key2203, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2318, 2)]

theorem rawRowCheck8894 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8894 := by decide +kernel

def row8894 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8894 : row8894 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8894 := by decide +kernel

theorem rowEval8894 (x : Key → ℝ) : Integer.Sparse.eval row8894 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8894, Integer.Sparse.eval_collectBalanced, rawRowCheck8894]

def rawRow8895 : Integer.Sparse Key := [(key2098, -6), (key2321, -6), (key2317, -6), (key2317, -6), (key2099, 2), (key2098, 2), (key2098, 2), (key2206, 2), (key2203, 2), (key2203, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck8895 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8895 := by decide +kernel

def row8895 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8895 : row8895 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8895 := by decide +kernel

theorem rowEval8895 (x : Key → ℝ) : Integer.Sparse.eval row8895 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8895, Integer.Sparse.eval_collectBalanced, rawRowCheck8895]

def rawRow8896 : Integer.Sparse Key := [(key2317, -6), (key2098, -6), (key2317, -6), (key2321, -6), (key2203, 2), (key2317, 2), (key2318, 2), (key2098, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2099, 2), (key2203, 2), (key2206, 2), (key2318, 2), (key2321, 2)]

theorem rawRowCheck8896 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form3 = rawRow8896 := by decide +kernel

def row8896 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8896 : row8896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8896 := by decide +kernel

theorem rowEval8896 (x : Key → ℝ) : Integer.Sparse.eval row8896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8896, Integer.Sparse.eval_collectBalanced, rawRowCheck8896]

def rawRow8897 : Integer.Sparse Key := [(key2317, -6), (key2098, -6), (key2321, -6), (key2317, -6), (key2203, 2), (key2318, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2317, 2), (key2099, 2), (key2098, 2), (key2206, 2), (key2203, 2), (key2321, 2), (key2318, 2)]

theorem rawRowCheck8897 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form3 = rawRow8897 := by decide +kernel

def row8897 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8897 : row8897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8897 := by decide +kernel

theorem rowEval8897 (x : Key → ℝ) : Integer.Sparse.eval row8897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8897, Integer.Sparse.eval_collectBalanced, rawRowCheck8897]

def rawRow8898 : Integer.Sparse Key := [(key2317, -6), (key2317, -6), (key2098, -6), (key2321, -6), (key2317, 2), (key2203, 2), (key2318, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2203, 2), (key2318, 2), (key2098, 2), (key2321, 2), (key2099, 2), (key2206, 2)]

theorem rawRowCheck8898 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form3 = rawRow8898 := by decide +kernel

def row8898 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8898 : row8898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8898 := by decide +kernel

theorem rowEval8898 (x : Key → ℝ) : Integer.Sparse.eval row8898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8898, Integer.Sparse.eval_collectBalanced, rawRowCheck8898]

def rawRow8899 : Integer.Sparse Key := [(key2317, -6), (key2317, -6), (key2321, -6), (key2098, -6), (key2317, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2318, 2), (key2203, 2), (key2321, 2), (key2098, 2), (key2206, 2), (key2099, 2)]

theorem rawRowCheck8899 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form3 = rawRow8899 := by decide +kernel

def row8899 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8899 : row8899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8899 := by decide +kernel

theorem rowEval8899 (x : Key → ℝ) : Integer.Sparse.eval row8899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8899, Integer.Sparse.eval_collectBalanced, rawRowCheck8899]

def rawRow8900 : Integer.Sparse Key := [(key2317, -6), (key2321, -6), (key2098, -6), (key2317, -6), (key2318, 2), (key2203, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2206, 2), (key2321, 2), (key2099, 2), (key2318, 2), (key2098, 2), (key2203, 2)]

theorem rawRowCheck8900 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form3 = rawRow8900 := by decide +kernel

def row8900 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8900 : row8900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8900 := by decide +kernel

theorem rowEval8900 (x : Key → ℝ) : Integer.Sparse.eval row8900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8900, Integer.Sparse.eval_collectBalanced, rawRowCheck8900]

def rawRow8901 : Integer.Sparse Key := [(key2317, -6), (key2321, -6), (key2317, -6), (key2098, -6), (key2318, 2), (key2317, 2), (key2203, 2), (key2321, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2206, 2), (key2318, 2), (key2099, 2), (key2203, 2), (key2098, 2)]

theorem rawRowCheck8901 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form3 = rawRow8901 := by decide +kernel

def row8901 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8901 : row8901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8901 := by decide +kernel

theorem rowEval8901 (x : Key → ℝ) : Integer.Sparse.eval row8901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8901, Integer.Sparse.eval_collectBalanced, rawRowCheck8901]

def rawRow8902 : Integer.Sparse Key := [(key2321, -6), (key2098, -6), (key2317, -6), (key2317, -6), (key2206, 2), (key2321, 2), (key2321, 2), (key2099, 2), (key2318, 2), (key2318, 2), (key2098, 2), (key2098, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck8902 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow8902 := by decide +kernel

def row8902 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8902 : row8902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8902 := by decide +kernel

theorem rowEval8902 (x : Key → ℝ) : Integer.Sparse.eval row8902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8902, Integer.Sparse.eval_collectBalanced, rawRowCheck8902]

def rawRow8903 : Integer.Sparse Key := [(key2321, -6), (key2317, -6), (key2098, -6), (key2317, -6), (key2321, 2), (key2206, 2), (key2321, 2), (key2318, 2), (key2099, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2098, 2), (key2317, 2), (key2098, 2), (key2203, 2)]

theorem rawRowCheck8903 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow8903 := by decide +kernel

def row8903 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8903 : row8903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8903 := by decide +kernel

theorem rowEval8903 (x : Key → ℝ) : Integer.Sparse.eval row8903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8903, Integer.Sparse.eval_collectBalanced, rawRowCheck8903]

def rawRow8904 : Integer.Sparse Key := [(key2321, -6), (key2317, -6), (key2317, -6), (key2098, -6), (key2321, 2), (key2321, 2), (key2206, 2), (key2318, 2), (key2318, 2), (key2099, 2), (key2317, 2), (key2203, 2), (key2317, 2), (key2098, 2), (key2203, 2), (key2098, 2)]

theorem rawRowCheck8904 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow8904 := by decide +kernel

def row8904 : Integer.Sparse Key := [(key2098, -2), (key2099, 2), (key2203, 4), (key2206, 2), (key2317, -8), (key2318, 4), (key2321, -2)]

theorem rowCheck8904 : row8904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8904 := by decide +kernel

theorem rowEval8904 (x : Key → ℝ) : Integer.Sparse.eval row8904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8904, Integer.Sparse.eval_collectBalanced, rawRowCheck8904]

def rawRow8905 : Integer.Sparse Key := [(key1998, -6), (key2000, -6), (key2000, -6), (key2000, -6), (key2267, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2292, 2)]

theorem rawRowCheck8905 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8905 := by decide +kernel

def row8905 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

theorem rowCheck8905 : row8905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8905 := by decide +kernel

theorem rowEval8905 (x : Key → ℝ) : Integer.Sparse.eval row8905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8905, Integer.Sparse.eval_collectBalanced, rawRowCheck8905]

def rawRow8906 : Integer.Sparse Key := [(key2000, -6), (key1998, -6), (key2000, -6), (key2000, -6), (key2269, 2), (key2267, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2292, 2), (key2269, 2)]

theorem rawRowCheck8906 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8906 := by decide +kernel

def row8906 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

theorem rowCheck8906 : row8906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8906 := by decide +kernel

theorem rowEval8906 (x : Key → ℝ) : Integer.Sparse.eval row8906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8906, Integer.Sparse.eval_collectBalanced, rawRowCheck8906]

def rawRow8907 : Integer.Sparse Key := [(key2000, -6), (key2000, -6), (key1998, -6), (key2000, -6), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2269, 2)]

theorem rawRowCheck8907 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8907 := by decide +kernel

def row8907 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

theorem rowCheck8907 : row8907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8907 := by decide +kernel

theorem rowEval8907 (x : Key → ℝ) : Integer.Sparse.eval row8907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8907, Integer.Sparse.eval_collectBalanced, rawRowCheck8907]

def rawRow8908 : Integer.Sparse Key := [(key2000, -6), (key2000, -6), (key2000, -6), (key1998, -6), (key2292, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2267, 2)]

theorem rawRowCheck8908 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow8908 := by decide +kernel

def row8908 : Integer.Sparse Key := [(key1998, -6), (key2000, -18), (key2267, 6), (key2269, 12), (key2292, 6)]

theorem rowCheck8908 : row8908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8908 := by decide +kernel

theorem rowEval8908 (x : Key → ℝ) : Integer.Sparse.eval row8908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8908, Integer.Sparse.eval_collectBalanced, rawRowCheck8908]

def rawRow8909 : Integer.Sparse Key := [(key2267, -6), (key2269, -6), (key2269, -6), (key2340, -6), (key1998, 2), (key2000, 2), (key2000, 2), (key2267, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2292, 2), (key2340, 2), (key2340, 2), (key2349, 2)]

theorem rawRowCheck8909 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8909 := by decide +kernel

def row8909 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8909 : row8909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8909 := by decide +kernel

theorem rowEval8909 (x : Key → ℝ) : Integer.Sparse.eval row8909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8909, Integer.Sparse.eval_collectBalanced, rawRowCheck8909]

def rawRow8910 : Integer.Sparse Key := [(key2269, -6), (key2267, -6), (key2269, -6), (key2340, -6), (key2000, 2), (key1998, 2), (key2000, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2340, 2), (key2349, 2), (key2340, 2)]

theorem rawRowCheck8910 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8910 := by decide +kernel

def row8910 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8910 : row8910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8910 := by decide +kernel

theorem rowEval8910 (x : Key → ℝ) : Integer.Sparse.eval row8910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8910, Integer.Sparse.eval_collectBalanced, rawRowCheck8910]

def rawRow8911 : Integer.Sparse Key := [(key2269, -6), (key2269, -6), (key2267, -6), (key2340, -6), (key2000, 2), (key2000, 2), (key1998, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2349, 2), (key2340, 2), (key2340, 2)]

theorem rawRowCheck8911 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8911 := by decide +kernel

def row8911 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8911 : row8911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8911 := by decide +kernel

theorem rowEval8911 (x : Key → ℝ) : Integer.Sparse.eval row8911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8911, Integer.Sparse.eval_collectBalanced, rawRowCheck8911]

def rawRow8912 : Integer.Sparse Key := [(key2267, -6), (key2269, -6), (key2340, -6), (key2269, -6), (key2267, 2), (key2269, 2), (key2340, 2), (key1998, 2), (key2000, 2), (key2267, 2), (key2292, 2), (key2340, 2), (key2349, 2), (key2000, 2), (key2269, 2), (key2292, 2)]

theorem rawRowCheck8912 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form4 = rawRow8912 := by decide +kernel

def row8912 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8912 : row8912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8912 := by decide +kernel

theorem rowEval8912 (x : Key → ℝ) : Integer.Sparse.eval row8912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8912, Integer.Sparse.eval_collectBalanced, rawRowCheck8912]

def rawRow8913 : Integer.Sparse Key := [(key2269, -6), (key2267, -6), (key2340, -6), (key2269, -6), (key2269, 2), (key2267, 2), (key2340, 2), (key2000, 2), (key1998, 2), (key2292, 2), (key2267, 2), (key2349, 2), (key2340, 2), (key2000, 2), (key2292, 2), (key2269, 2)]

theorem rawRowCheck8913 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form4 = rawRow8913 := by decide +kernel

def row8913 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8913 : row8913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8913 := by decide +kernel

theorem rowEval8913 (x : Key → ℝ) : Integer.Sparse.eval row8913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8913, Integer.Sparse.eval_collectBalanced, rawRowCheck8913]

def rawRow8914 : Integer.Sparse Key := [(key2267, -6), (key2340, -6), (key2269, -6), (key2269, -6), (key2267, 2), (key2340, 2), (key2269, 2), (key2267, 2), (key2340, 2), (key1998, 2), (key2349, 2), (key2000, 2), (key2292, 2), (key2269, 2), (key2000, 2), (key2292, 2)]

theorem rawRowCheck8914 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form4 = rawRow8914 := by decide +kernel

def row8914 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8914 : row8914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8914 := by decide +kernel

theorem rowEval8914 (x : Key → ℝ) : Integer.Sparse.eval row8914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8914, Integer.Sparse.eval_collectBalanced, rawRowCheck8914]

def rawRow8915 : Integer.Sparse Key := [(key2340, -6), (key2267, -6), (key2269, -6), (key2269, -6), (key2340, 2), (key2267, 2), (key2269, 2), (key2340, 2), (key2267, 2), (key2349, 2), (key1998, 2), (key2292, 2), (key2000, 2), (key2269, 2), (key2292, 2), (key2000, 2)]

theorem rawRowCheck8915 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form4 = rawRow8915 := by decide +kernel

def row8915 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8915 : row8915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8915 := by decide +kernel

theorem rowEval8915 (x : Key → ℝ) : Integer.Sparse.eval row8915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8915, Integer.Sparse.eval_collectBalanced, rawRowCheck8915]

def rawRow8916 : Integer.Sparse Key := [(key2269, -6), (key2340, -6), (key2267, -6), (key2269, -6), (key2269, 2), (key2340, 2), (key2267, 2), (key2292, 2), (key2349, 2), (key2000, 2), (key2340, 2), (key1998, 2), (key2267, 2), (key2292, 2), (key2000, 2), (key2269, 2)]

theorem rawRowCheck8916 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form4 = rawRow8916 := by decide +kernel

def row8916 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8916 : row8916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8916 := by decide +kernel

theorem rowEval8916 (x : Key → ℝ) : Integer.Sparse.eval row8916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8916, Integer.Sparse.eval_collectBalanced, rawRowCheck8916]

def rawRow8917 : Integer.Sparse Key := [(key2340, -6), (key2269, -6), (key2267, -6), (key2269, -6), (key2340, 2), (key2269, 2), (key2267, 2), (key2349, 2), (key2292, 2), (key2340, 2), (key2000, 2), (key2267, 2), (key1998, 2), (key2292, 2), (key2269, 2), (key2000, 2)]

theorem rawRowCheck8917 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form4 = rawRow8917 := by decide +kernel

def row8917 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8917 : row8917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8917 := by decide +kernel

theorem rowEval8917 (x : Key → ℝ) : Integer.Sparse.eval row8917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8917, Integer.Sparse.eval_collectBalanced, rawRowCheck8917]

def rawRow8918 : Integer.Sparse Key := [(key2269, -6), (key2269, -6), (key2340, -6), (key2267, -6), (key2292, 2), (key2292, 2), (key2349, 2), (key2000, 2), (key2000, 2), (key2269, 2), (key2269, 2), (key2340, 2), (key2340, 2), (key1998, 2), (key2267, 2), (key2267, 2)]

theorem rawRowCheck8918 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8918 := by decide +kernel

def row8918 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8918 : row8918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8918 := by decide +kernel

theorem rowEval8918 (x : Key → ℝ) : Integer.Sparse.eval row8918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8918, Integer.Sparse.eval_collectBalanced, rawRowCheck8918]

def rawRow8919 : Integer.Sparse Key := [(key2269, -6), (key2340, -6), (key2269, -6), (key2267, -6), (key2292, 2), (key2349, 2), (key2292, 2), (key2269, 2), (key2340, 2), (key2000, 2), (key2340, 2), (key2000, 2), (key2269, 2), (key2267, 2), (key1998, 2), (key2267, 2)]

theorem rawRowCheck8919 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8919 := by decide +kernel

def row8919 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8919 : row8919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8919 := by decide +kernel

theorem rowEval8919 (x : Key → ℝ) : Integer.Sparse.eval row8919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8919, Integer.Sparse.eval_collectBalanced, rawRowCheck8919]

def rawRow8920 : Integer.Sparse Key := [(key2340, -6), (key2269, -6), (key2269, -6), (key2267, -6), (key2349, 2), (key2292, 2), (key2292, 2), (key2340, 2), (key2269, 2), (key2340, 2), (key2000, 2), (key2269, 2), (key2000, 2), (key2267, 2), (key2267, 2), (key1998, 2)]

theorem rawRowCheck8920 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8920 := by decide +kernel

def row8920 : Integer.Sparse Key := [(key1998, 2), (key2000, 4), (key2267, -2), (key2269, -8), (key2292, 4), (key2340, -2), (key2349, 2)]

theorem rowCheck8920 : row8920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8920 := by decide +kernel

theorem rowEval8920 (x : Key → ℝ) : Integer.Sparse.eval row8920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8920, Integer.Sparse.eval_collectBalanced, rawRowCheck8920]

def rawRow8921 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2287, 1)]

theorem rawRowCheck8921 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8921 := by decide +kernel

def row8921 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

theorem rowCheck8921 : row8921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8921 := by decide +kernel

theorem rowEval8921 (x : Key → ℝ) : Integer.Sparse.eval row8921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8921, Integer.Sparse.eval_collectBalanced, rawRowCheck8921]

def rawRow8922 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2279, 1)]

theorem rawRowCheck8922 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8922 := by decide +kernel

def row8922 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

theorem rowCheck8922 : row8922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8922 := by decide +kernel

theorem rowEval8922 (x : Key → ℝ) : Integer.Sparse.eval row8922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8922, Integer.Sparse.eval_collectBalanced, rawRowCheck8922]

def rawRow8923 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1)]

theorem rawRowCheck8923 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8923 := by decide +kernel

def row8923 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

theorem rowCheck8923 : row8923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8923 := by decide +kernel

theorem rowEval8923 (x : Key → ℝ) : Integer.Sparse.eval row8923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8923, Integer.Sparse.eval_collectBalanced, rawRowCheck8923]

def rawRow8924 : Integer.Sparse Key := [(key2187, -2), (key2187, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2174, -2), (key2174, -2), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1)]

theorem rawRowCheck8924 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow8924 := by decide +kernel

def row8924 : Integer.Sparse Key := [(key2174, -6), (key2176, -12), (key2187, -6), (key2274, 6), (key2276, 6), (key2279, 6), (key2287, 6)]

theorem rowCheck8924 : row8924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8924 := by decide +kernel

theorem rowEval8924 (x : Key → ℝ) : Integer.Sparse.eval row8924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8924, Integer.Sparse.eval_collectBalanced, rawRowCheck8924]

def rawRow8925 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2274, -2), (key2276, -2), (key2274, -2), (key2287, -2), (key2276, -2), (key2287, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2347, 1)]

theorem rawRowCheck8925 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8925 := by decide +kernel

def row8925 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8925 : row8925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8925 := by decide +kernel

theorem rowEval8925 (x : Key → ℝ) : Integer.Sparse.eval row8925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8925, Integer.Sparse.eval_collectBalanced, rawRowCheck8925]

def rawRow8926 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2276, -2), (key2274, -2), (key2287, -2), (key2274, -2), (key2287, -2), (key2276, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2341, 1), (key2347, 1), (key2343, 1)]

theorem rawRowCheck8926 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8926 := by decide +kernel

def row8926 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8926 : row8926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8926 := by decide +kernel

theorem rowEval8926 (x : Key → ℝ) : Integer.Sparse.eval row8926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8926, Integer.Sparse.eval_collectBalanced, rawRowCheck8926]

def rawRow8927 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2287, -2), (key2287, -2), (key2276, -2), (key2276, -2), (key2274, -2), (key2274, -2), (key2347, -2), (key2341, -2), (key2341, -2), (key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2347, 1), (key2347, 1), (key2343, 1), (key2343, 1), (key2341, 1), (key2341, 1)]

theorem rawRowCheck8927 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8927 := by decide +kernel

def row8927 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8927 : row8927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8927 := by decide +kernel

theorem rowEval8927 (x : Key → ℝ) : Integer.Sparse.eval row8927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8927, Integer.Sparse.eval_collectBalanced, rawRowCheck8927]

def rawRow8928 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2341, -2), (key2077, -2), (key2079, -2), (key2274, -2), (key2287, -2), (key2341, -2), (key2347, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2174, 1), (key2176, 1), (key2274, 1), (key2279, 1), (key2341, 1), (key2343, 1), (key2077, 1), (key2079, 1), (key2274, 1), (key2287, 1), (key2341, 1), (key2347, 1), (key2077, 1), (key2085, 1), (key2174, 1), (key2187, 1), (key2343, 1), (key2347, 1), (key2079, 1), (key2085, 1), (key2176, 1), (key2187, 1), (key2279, 1), (key2287, 1)]

theorem rawRowCheck8928 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form5 = rawRow8928 := by decide +kernel

def row8928 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8928 : row8928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8928 := by decide +kernel

theorem rowEval8928 (x : Key → ℝ) : Integer.Sparse.eval row8928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8928, Integer.Sparse.eval_collectBalanced, rawRowCheck8928]

def rawRow8929 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2341, -2), (key2079, -2), (key2077, -2), (key2287, -2), (key2274, -2), (key2347, -2), (key2341, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2176, 1), (key2174, 1), (key2279, 1), (key2274, 1), (key2343, 1), (key2341, 1), (key2079, 1), (key2077, 1), (key2287, 1), (key2274, 1), (key2347, 1), (key2341, 1), (key2085, 1), (key2077, 1), (key2187, 1), (key2174, 1), (key2347, 1), (key2343, 1), (key2085, 1), (key2079, 1), (key2187, 1), (key2176, 1), (key2287, 1), (key2279, 1)]

theorem rawRowCheck8929 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form5 = rawRow8929 := by decide +kernel

def row8929 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8929 : row8929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8929 := by decide +kernel

theorem rowEval8929 (x : Key → ℝ) : Integer.Sparse.eval row8929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8929, Integer.Sparse.eval_collectBalanced, rawRowCheck8929]

def rawRow8930 : Integer.Sparse Key := [(key2274, -2), (key2341, -2), (key2276, -2), (key2274, -2), (key2341, -2), (key2077, -2), (key2347, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2274, 1), (key2341, 1), (key2174, 1), (key2343, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2341, 1), (key2077, 1), (key2347, 1), (key2079, 1), (key2287, 1), (key2174, 1), (key2343, 1), (key2077, 1), (key2347, 1), (key2085, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2079, 1), (key2287, 1), (key2085, 1), (key2187, 1)]

theorem rawRowCheck8930 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form5 = rawRow8930 := by decide +kernel

def row8930 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8930 : row8930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8930 := by decide +kernel

theorem rowEval8930 (x : Key → ℝ) : Integer.Sparse.eval row8930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8930, Integer.Sparse.eval_collectBalanced, rawRowCheck8930]

def rawRow8931 : Integer.Sparse Key := [(key2341, -2), (key2274, -2), (key2276, -2), (key2341, -2), (key2274, -2), (key2347, -2), (key2077, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2341, 1), (key2274, 1), (key2343, 1), (key2174, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2274, 1), (key2347, 1), (key2077, 1), (key2287, 1), (key2079, 1), (key2343, 1), (key2174, 1), (key2347, 1), (key2077, 1), (key2187, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2287, 1), (key2079, 1), (key2187, 1), (key2085, 1)]

theorem rawRowCheck8931 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form5 = rawRow8931 := by decide +kernel

def row8931 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8931 : row8931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8931 := by decide +kernel

theorem rowEval8931 (x : Key → ℝ) : Integer.Sparse.eval row8931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8931, Integer.Sparse.eval_collectBalanced, rawRowCheck8931]

def rawRow8932 : Integer.Sparse Key := [(key2276, -2), (key2341, -2), (key2274, -2), (key2287, -2), (key2347, -2), (key2079, -2), (key2341, -2), (key2077, -2), (key2274, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2279, 1), (key2343, 1), (key2176, 1), (key2341, 1), (key2174, 1), (key2274, 1), (key2287, 1), (key2347, 1), (key2079, 1), (key2341, 1), (key2077, 1), (key2274, 1), (key2187, 1), (key2347, 1), (key2085, 1), (key2343, 1), (key2077, 1), (key2174, 1), (key2187, 1), (key2287, 1), (key2085, 1), (key2279, 1), (key2079, 1), (key2176, 1)]

theorem rawRowCheck8932 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form5 = rawRow8932 := by decide +kernel

def row8932 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8932 : row8932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8932 := by decide +kernel

theorem rowEval8932 (x : Key → ℝ) : Integer.Sparse.eval row8932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8932, Integer.Sparse.eval_collectBalanced, rawRowCheck8932]

def rawRow8933 : Integer.Sparse Key := [(key2341, -2), (key2276, -2), (key2274, -2), (key2347, -2), (key2287, -2), (key2341, -2), (key2079, -2), (key2274, -2), (key2077, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2343, 1), (key2279, 1), (key2341, 1), (key2176, 1), (key2274, 1), (key2174, 1), (key2347, 1), (key2287, 1), (key2341, 1), (key2079, 1), (key2274, 1), (key2077, 1), (key2347, 1), (key2187, 1), (key2343, 1), (key2085, 1), (key2174, 1), (key2077, 1), (key2287, 1), (key2187, 1), (key2279, 1), (key2085, 1), (key2176, 1), (key2079, 1)]

theorem rawRowCheck8933 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form5 = rawRow8933 := by decide +kernel

def row8933 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8933 : row8933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8933 := by decide +kernel

theorem rowEval8933 (x : Key → ℝ) : Integer.Sparse.eval row8933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8933, Integer.Sparse.eval_collectBalanced, rawRowCheck8933]

def rawRow8934 : Integer.Sparse Key := [(key2287, -2), (key2287, -2), (key2347, -2), (key2079, -2), (key2079, -2), (key2276, -2), (key2276, -2), (key2341, -2), (key2341, -2), (key2077, -2), (key2274, -2), (key2274, -2), (key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1), (key2079, 1), (key2079, 1), (key2176, 1), (key2176, 1), (key2341, 1), (key2341, 1), (key2077, 1), (key2077, 1), (key2174, 1), (key2174, 1), (key2274, 1), (key2274, 1)]

theorem rawRowCheck8934 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form5 = rawRow8934 := by decide +kernel

def row8934 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8934 : row8934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8934 := by decide +kernel

theorem rowEval8934 (x : Key → ℝ) : Integer.Sparse.eval row8934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8934, Integer.Sparse.eval_collectBalanced, rawRowCheck8934]

def rawRow8935 : Integer.Sparse Key := [(key2287, -2), (key2347, -2), (key2287, -2), (key2276, -2), (key2341, -2), (key2079, -2), (key2341, -2), (key2079, -2), (key2276, -2), (key2274, -2), (key2077, -2), (key2274, -2), (key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2274, 1), (key2077, 1), (key2174, 1)]

theorem rawRowCheck8935 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form5 = rawRow8935 := by decide +kernel

def row8935 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8935 : row8935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8935 := by decide +kernel

theorem rowEval8935 (x : Key → ℝ) : Integer.Sparse.eval row8935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8935, Integer.Sparse.eval_collectBalanced, rawRowCheck8935]

def rawRow8936 : Integer.Sparse Key := [(key2347, -2), (key2287, -2), (key2287, -2), (key2341, -2), (key2276, -2), (key2341, -2), (key2079, -2), (key2276, -2), (key2079, -2), (key2274, -2), (key2274, -2), (key2077, -2), (key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2079, 1), (key2274, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2077, 1)]

theorem rawRowCheck8936 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form5 = rawRow8936 := by decide +kernel

def row8936 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, 2), (key2176, 2), (key2187, 2), (key2274, -2), (key2276, -4), (key2279, 2), (key2287, -2), (key2341, -2), (key2343, 2)]

theorem rowCheck8936 : row8936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8936 := by decide +kernel

theorem rowEval8936 (x : Key → ℝ) : Integer.Sparse.eval row8936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8936, Integer.Sparse.eval_collectBalanced, rawRowCheck8936]

def rawRow8937 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2316, 6), (key2316, 6), (key2322, 6)]

theorem rawRowCheck8937 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8937 := by decide +kernel

def row8937 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

theorem rowCheck8937 : row8937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8937 := by decide +kernel

theorem rowEval8937 (x : Key → ℝ) : Integer.Sparse.eval row8937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8937, Integer.Sparse.eval_collectBalanced, rawRowCheck8937]

def rawRow8938 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2316, 6), (key2322, 6), (key2316, 6)]

theorem rawRowCheck8938 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8938 := by decide +kernel

def row8938 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

theorem rowCheck8938 : row8938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8938 := by decide +kernel

theorem rowEval8938 (x : Key → ℝ) : Integer.Sparse.eval row8938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8938, Integer.Sparse.eval_collectBalanced, rawRowCheck8938]

def rawRow8939 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2322, 6), (key2316, 6), (key2316, 6)]

theorem rawRowCheck8939 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8939 := by decide +kernel

def row8939 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

theorem rowCheck8939 : row8939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8939 := by decide +kernel

theorem rowEval8939 (x : Key → ℝ) : Integer.Sparse.eval row8939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8939, Integer.Sparse.eval_collectBalanced, rawRowCheck8939]

def rawRow8940 : Integer.Sparse Key := [(key2009, -24), (key2322, 6), (key2316, 6), (key2316, 6), (key2316, 6)]

theorem rawRowCheck8940 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow8940 := by decide +kernel

def row8940 : Integer.Sparse Key := [(key2009, -24), (key2316, 18), (key2322, 6)]

theorem rowCheck8940 : row8940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8940 := by decide +kernel

theorem rowEval8940 (x : Key → ℝ) : Integer.Sparse.eval row8940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8940, Integer.Sparse.eval_collectBalanced, rawRowCheck8940]

def rawRow8941 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2316, 6), (key2316, 6), (key2322, 6)]

theorem rawRowCheck8941 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8941 := by decide +kernel

def row8941 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8941 : row8941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8941 := by decide +kernel

theorem rowEval8941 (x : Key → ℝ) : Integer.Sparse.eval row8941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8941, Integer.Sparse.eval_collectBalanced, rawRowCheck8941]

def rawRow8942 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2316, 6), (key2322, 6), (key2316, 6)]

theorem rawRowCheck8942 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8942 := by decide +kernel

def row8942 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8942 : row8942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8942 := by decide +kernel

theorem rowEval8942 (x : Key → ℝ) : Integer.Sparse.eval row8942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8942, Integer.Sparse.eval_collectBalanced, rawRowCheck8942]

def rawRow8943 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2322, 6), (key2316, 6), (key2316, 6)]

theorem rawRowCheck8943 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8943 := by decide +kernel

def row8943 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8943 : row8943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8943 := by decide +kernel

theorem rowEval8943 (x : Key → ℝ) : Integer.Sparse.eval row8943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8943, Integer.Sparse.eval_collectBalanced, rawRowCheck8943]

def rawRow8944 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2009, 6), (key2316, 6), (key2322, 6)]

theorem rawRowCheck8944 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form6 = rawRow8944 := by decide +kernel

def row8944 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8944 : row8944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8944 := by decide +kernel

theorem rowEval8944 (x : Key → ℝ) : Integer.Sparse.eval row8944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8944, Integer.Sparse.eval_collectBalanced, rawRowCheck8944]

def rawRow8945 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2009, 6), (key2322, 6), (key2316, 6)]

theorem rawRowCheck8945 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form6 = rawRow8945 := by decide +kernel

def row8945 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8945 : row8945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8945 := by decide +kernel

theorem rowEval8945 (x : Key → ℝ) : Integer.Sparse.eval row8945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8945, Integer.Sparse.eval_collectBalanced, rawRowCheck8945]

def rawRow8946 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2316, 6), (key2009, 6), (key2322, 6)]

theorem rawRowCheck8946 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form6 = rawRow8946 := by decide +kernel

def row8946 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8946 : row8946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8946 := by decide +kernel

theorem rowEval8946 (x : Key → ℝ) : Integer.Sparse.eval row8946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8946, Integer.Sparse.eval_collectBalanced, rawRowCheck8946]

def rawRow8947 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2316, 6), (key2322, 6), (key2009, 6)]

theorem rawRowCheck8947 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form6 = rawRow8947 := by decide +kernel

def row8947 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8947 : row8947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8947 := by decide +kernel

theorem rowEval8947 (x : Key → ℝ) : Integer.Sparse.eval row8947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8947, Integer.Sparse.eval_collectBalanced, rawRowCheck8947]

def rawRow8948 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2322, 6), (key2009, 6), (key2316, 6)]

theorem rawRowCheck8948 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form6 = rawRow8948 := by decide +kernel

def row8948 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8948 : row8948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8948 := by decide +kernel

theorem rowEval8948 (x : Key → ℝ) : Integer.Sparse.eval row8948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8948, Integer.Sparse.eval_collectBalanced, rawRowCheck8948]

def rawRow8949 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2322, 6), (key2316, 6), (key2009, 6)]

theorem rawRowCheck8949 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form6 = rawRow8949 := by decide +kernel

def row8949 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8949 : row8949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8949 := by decide +kernel

theorem rowEval8949 (x : Key → ℝ) : Integer.Sparse.eval row8949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8949, Integer.Sparse.eval_collectBalanced, rawRowCheck8949]

def rawRow8950 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2009, 6), (key2316, 6), (key2316, 6)]

theorem rawRowCheck8950 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form6 = rawRow8950 := by decide +kernel

def row8950 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8950 : row8950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8950 := by decide +kernel

theorem rowEval8950 (x : Key → ℝ) : Integer.Sparse.eval row8950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8950, Integer.Sparse.eval_collectBalanced, rawRowCheck8950]

def rawRow8951 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2316, 6), (key2009, 6), (key2316, 6)]

theorem rawRowCheck8951 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form6 = rawRow8951 := by decide +kernel

def row8951 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8951 : row8951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8951 := by decide +kernel

theorem rowEval8951 (x : Key → ℝ) : Integer.Sparse.eval row8951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8951, Integer.Sparse.eval_collectBalanced, rawRowCheck8951]

def rawRow8952 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2316, 6), (key2316, 6), (key2009, 6)]

theorem rawRowCheck8952 : GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form6 = rawRow8952 := by decide +kernel

def row8952 : Integer.Sparse Key := [(key2009, 6), (key2316, -12), (key2322, 6)]

theorem rowCheck8952 : row8952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8952 := by decide +kernel

theorem rowEval8952 (x : Key → ℝ) : Integer.Sparse.eval row8952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 2, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8952, Integer.Sparse.eval_collectBalanced, rawRowCheck8952]

def rawRow8953 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2085, -2), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2187, 2)]

theorem rawRowCheck8953 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8953 := by decide +kernel

def row8953 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

theorem rowCheck8953 : row8953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8953 := by decide +kernel

theorem rowEval8953 (x : Key → ℝ) : Integer.Sparse.eval row8953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8953, Integer.Sparse.eval_collectBalanced, rawRowCheck8953]

def rawRow8954 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2085, -2), (key2079, -2), (key2176, 2), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2187, 2), (key2176, 2)]

theorem rawRowCheck8954 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8954 := by decide +kernel

def row8954 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

theorem rowCheck8954 : row8954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8954 := by decide +kernel

theorem rowEval8954 (x : Key → ℝ) : Integer.Sparse.eval row8954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8954, Integer.Sparse.eval_collectBalanced, rawRowCheck8954]

def rawRow8955 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2176, 2)]

theorem rawRowCheck8955 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8955 := by decide +kernel

def row8955 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

theorem rowCheck8955 : row8955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8955 := by decide +kernel

theorem rowEval8955 (x : Key → ℝ) : Integer.Sparse.eval row8955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8955, Integer.Sparse.eval_collectBalanced, rawRowCheck8955]

def rawRow8956 : Integer.Sparse Key := [(key2085, -2), (key2085, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2077, -2), (key2077, -2), (key2187, 2), (key2187, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2174, 2), (key2174, 2)]

theorem rawRowCheck8956 : GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow8956 := by decide +kernel

def row8956 : Integer.Sparse Key := [(key2077, -6), (key2079, -12), (key2085, -6), (key2174, 6), (key2176, 12), (key2187, 6)]

theorem rowCheck8956 : row8956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8956 := by decide +kernel

theorem rowEval8956 (x : Key → ℝ) : Integer.Sparse.eval row8956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8956, Integer.Sparse.eval_collectBalanced, rawRowCheck8956]

def rawRow8957 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2274, -2), (key2276, -2), (key2274, -2), (key2279, -2), (key2276, -2), (key2279, -2), (key2341, -2), (key2341, -2), (key2343, -2), (key2077, 2), (key2079, 2), (key2079, 2), (key2274, 2), (key2276, 2), (key2274, 2), (key2287, 2), (key2276, 2), (key2287, 2), (key2341, 2), (key2341, 2), (key2347, 2)]

theorem rawRowCheck8957 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8957 := by decide +kernel

def row8957 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8957 : row8957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8957 := by decide +kernel

theorem rowEval8957 (x : Key → ℝ) : Integer.Sparse.eval row8957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8957, Integer.Sparse.eval_collectBalanced, rawRowCheck8957]

def rawRow8958 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2276, -2), (key2274, -2), (key2279, -2), (key2274, -2), (key2279, -2), (key2276, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2079, 2), (key2077, 2), (key2079, 2), (key2276, 2), (key2274, 2), (key2287, 2), (key2274, 2), (key2287, 2), (key2276, 2), (key2341, 2), (key2347, 2), (key2341, 2)]

theorem rawRowCheck8958 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8958 := by decide +kernel

def row8958 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8958 : row8958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8958 := by decide +kernel

theorem rowEval8958 (x : Key → ℝ) : Integer.Sparse.eval row8958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8958, Integer.Sparse.eval_collectBalanced, rawRowCheck8958]

def rawRow8959 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2279, -2), (key2279, -2), (key2276, -2), (key2276, -2), (key2274, -2), (key2274, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2079, 2), (key2079, 2), (key2077, 2), (key2287, 2), (key2287, 2), (key2276, 2), (key2276, 2), (key2274, 2), (key2274, 2), (key2347, 2), (key2341, 2), (key2341, 2)]

theorem rawRowCheck8959 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8959 := by decide +kernel

def row8959 : Integer.Sparse Key := [(key2077, 2), (key2079, 4), (key2174, -2), (key2176, -4), (key2279, -4), (key2287, 4), (key2343, -2), (key2347, 2)]

theorem rowCheck8959 : row8959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8959 := by decide +kernel

theorem rowEval8959 (x : Key → ℝ) : Integer.Sparse.eval row8959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8959, Integer.Sparse.eval_collectBalanced, rawRowCheck8959]

end MUB6.Certificate.GramRows

end OAI
