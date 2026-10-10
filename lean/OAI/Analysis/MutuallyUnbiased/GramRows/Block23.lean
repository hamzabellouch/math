import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow832 : Integer.Sparse Key := [(key193, -2), (key202, -2), (key193, -2), (key193, 6), (key90, 2), (key151, 2), (key90, 2), (key90, -2), (key7, -2), (key90, -2), (key84, -6), (key84, 2), (key1, 2), (key84, 2)]

theorem rawRowCheck832 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow832 := by decide +kernel

def row832 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck832 : row832 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow832 := by decide +kernel

theorem rowEval832 (x : Key → ℝ) : Integer.Sparse.eval row832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck832, Integer.Sparse.eval_collectBalanced, rawRowCheck832]

def rawRow833 : Integer.Sparse Key := [(key202, -2), (key193, -2), (key193, -2), (key193, 6), (key151, 2), (key90, 2), (key90, 2), (key90, -2), (key90, -2), (key7, -2), (key84, -6), (key84, 2), (key84, 2), (key1, 2)]

theorem rawRowCheck833 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow833 := by decide +kernel

def row833 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck833 : row833 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow833 := by decide +kernel

theorem rowEval833 (x : Key → ℝ) : Integer.Sparse.eval row833 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck833, Integer.Sparse.eval_collectBalanced, rawRowCheck833]

def rawRow834 : Integer.Sparse Key := [(key2785, -2), (key2785, -2), (key2785, -2), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2808, 2), (key2808, 2), (key2808, 2), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1)]

theorem rawRowCheck834 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow834 := by decide +kernel

def row834 : Integer.Sparse Key := [(key2785, -6), (key2793, 6), (key2808, 6), (key2828, -6), (key2859, -6), (key2869, 6)]

theorem rowCheck834 : row834 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow834 := by decide +kernel

theorem rowEval834 (x : Key → ℝ) : Integer.Sparse.eval row834 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck834, Integer.Sparse.eval_collectBalanced, rawRowCheck834]

def rawRow835 : Integer.Sparse Key := [(key2670, -2), (key2793, -2), (key2793, -2), (key2670, 1), (key2670, 1), (key2785, 1), (key2785, 1), (key2793, 1), (key2793, 1), (key2705, 2), (key2859, 2), (key2859, 2), (key2705, -1), (key2705, -1), (key2808, -1), (key2808, -1), (key2859, -1), (key2859, -1), (key2725, -1), (key2725, -1), (key2869, -1), (key2869, -1), (key2879, -1), (key2879, -1), (key2725, 1), (key2725, 1), (key2828, 1), (key2828, 1), (key2879, 1), (key2879, 1)]

theorem rawRowCheck835 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0 = rawRow835 := by decide +kernel

def row835 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

theorem rowCheck835 : row835 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow835 := by decide +kernel

theorem rowEval835 (x : Key → ℝ) : Integer.Sparse.eval row835 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck835, Integer.Sparse.eval_collectBalanced, rawRowCheck835]

def rawRow836 : Integer.Sparse Key := [(key2793, -2), (key2670, -2), (key2793, -2), (key2785, 1), (key2793, 1), (key2670, 1), (key2793, 1), (key2670, 1), (key2785, 1), (key2859, 2), (key2705, 2), (key2859, 2), (key2808, -1), (key2859, -1), (key2705, -1), (key2859, -1), (key2705, -1), (key2808, -1), (key2869, -1), (key2879, -1), (key2725, -1), (key2879, -1), (key2725, -1), (key2869, -1), (key2828, 1), (key2879, 1), (key2725, 1), (key2879, 1), (key2725, 1), (key2828, 1)]

theorem rawRowCheck836 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0 = rawRow836 := by decide +kernel

def row836 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

theorem rowCheck836 : row836 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow836 := by decide +kernel

theorem rowEval836 (x : Key → ℝ) : Integer.Sparse.eval row836 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck836, Integer.Sparse.eval_collectBalanced, rawRowCheck836]

def rawRow837 : Integer.Sparse Key := [(key2793, -2), (key2793, -2), (key2670, -2), (key2793, 1), (key2785, 1), (key2793, 1), (key2670, 1), (key2785, 1), (key2670, 1), (key2859, 2), (key2859, 2), (key2705, 2), (key2859, -1), (key2808, -1), (key2859, -1), (key2705, -1), (key2808, -1), (key2705, -1), (key2879, -1), (key2869, -1), (key2879, -1), (key2725, -1), (key2869, -1), (key2725, -1), (key2879, 1), (key2828, 1), (key2879, 1), (key2725, 1), (key2828, 1), (key2725, 1)]

theorem rawRowCheck837 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0 = rawRow837 := by decide +kernel

def row837 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

theorem rowCheck837 : row837 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow837 := by decide +kernel

theorem rowEval837 (x : Key → ℝ) : Integer.Sparse.eval row837 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck837, Integer.Sparse.eval_collectBalanced, rawRowCheck837]

def rawRow838 : Integer.Sparse Key := [(key2808, -2), (key2808, -2), (key2808, -2), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2785, 2), (key2785, 2), (key2785, 2), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1)]

theorem rawRowCheck838 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow838 := by decide +kernel

def row838 : Integer.Sparse Key := [(key2785, 6), (key2793, -6), (key2808, -6), (key2828, 6), (key2859, 6), (key2869, -6)]

theorem rowCheck838 : row838 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow838 := by decide +kernel

theorem rowEval838 (x : Key → ℝ) : Integer.Sparse.eval row838 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck838, Integer.Sparse.eval_collectBalanced, rawRowCheck838]

def rawRow839 : Integer.Sparse Key := [(key2615, -2), (key2828, -2), (key2828, -2), (key2615, 1), (key2615, 1), (key2808, 1), (key2808, 1), (key2828, 1), (key2828, 1), (key2631, 2), (key2869, 2), (key2869, 2), (key2631, -1), (key2631, -1), (key2785, -1), (key2785, -1), (key2869, -1), (key2869, -1), (key2639, -1), (key2639, -1), (key2859, -1), (key2859, -1), (key2879, -1), (key2879, -1), (key2639, 1), (key2639, 1), (key2793, 1), (key2793, 1), (key2879, 1), (key2879, 1)]

theorem rawRowCheck839 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow839 := by decide +kernel

def row839 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

theorem rowCheck839 : row839 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow839 := by decide +kernel

theorem rowEval839 (x : Key → ℝ) : Integer.Sparse.eval row839 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck839, Integer.Sparse.eval_collectBalanced, rawRowCheck839]

def rawRow840 : Integer.Sparse Key := [(key2828, -2), (key2615, -2), (key2828, -2), (key2808, 1), (key2828, 1), (key2615, 1), (key2828, 1), (key2615, 1), (key2808, 1), (key2869, 2), (key2631, 2), (key2869, 2), (key2785, -1), (key2869, -1), (key2631, -1), (key2869, -1), (key2631, -1), (key2785, -1), (key2859, -1), (key2879, -1), (key2639, -1), (key2879, -1), (key2639, -1), (key2859, -1), (key2793, 1), (key2879, 1), (key2639, 1), (key2879, 1), (key2639, 1), (key2793, 1)]

theorem rawRowCheck840 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow840 := by decide +kernel

def row840 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

theorem rowCheck840 : row840 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow840 := by decide +kernel

theorem rowEval840 (x : Key → ℝ) : Integer.Sparse.eval row840 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck840, Integer.Sparse.eval_collectBalanced, rawRowCheck840]

def rawRow841 : Integer.Sparse Key := [(key2828, -2), (key2828, -2), (key2615, -2), (key2828, 1), (key2808, 1), (key2828, 1), (key2615, 1), (key2808, 1), (key2615, 1), (key2869, 2), (key2869, 2), (key2631, 2), (key2869, -1), (key2785, -1), (key2869, -1), (key2631, -1), (key2785, -1), (key2631, -1), (key2879, -1), (key2859, -1), (key2879, -1), (key2639, -1), (key2859, -1), (key2639, -1), (key2879, 1), (key2793, 1), (key2879, 1), (key2639, 1), (key2793, 1), (key2639, 1)]

theorem rawRowCheck841 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow841 := by decide +kernel

def row841 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

theorem rowCheck841 : row841 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow841 := by decide +kernel

theorem rowEval841 (x : Key → ℝ) : Integer.Sparse.eval row841 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck841, Integer.Sparse.eval_collectBalanced, rawRowCheck841]

def rawRow842 : Integer.Sparse Key := [(key2705, -2), (key2859, -2), (key2859, -2), (key2725, 1), (key2725, 1), (key2869, 1), (key2869, 1), (key2879, 1), (key2879, 1), (key2670, 2), (key2793, 2), (key2793, 2), (key2725, -1), (key2725, -1), (key2828, -1), (key2828, -1), (key2879, -1), (key2879, -1), (key2670, -1), (key2670, -1), (key2785, -1), (key2785, -1), (key2793, -1), (key2793, -1), (key2705, 1), (key2705, 1), (key2808, 1), (key2808, 1), (key2859, 1), (key2859, 1)]

theorem rawRowCheck842 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0 = rawRow842 := by decide +kernel

def row842 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

theorem rowCheck842 : row842 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow842 := by decide +kernel

theorem rowEval842 (x : Key → ℝ) : Integer.Sparse.eval row842 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck842, Integer.Sparse.eval_collectBalanced, rawRowCheck842]

def rawRow843 : Integer.Sparse Key := [(key2859, -2), (key2705, -2), (key2859, -2), (key2869, 1), (key2879, 1), (key2725, 1), (key2879, 1), (key2725, 1), (key2869, 1), (key2793, 2), (key2670, 2), (key2793, 2), (key2828, -1), (key2879, -1), (key2725, -1), (key2879, -1), (key2725, -1), (key2828, -1), (key2785, -1), (key2793, -1), (key2670, -1), (key2793, -1), (key2670, -1), (key2785, -1), (key2808, 1), (key2859, 1), (key2705, 1), (key2859, 1), (key2705, 1), (key2808, 1)]

theorem rawRowCheck843 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0 = rawRow843 := by decide +kernel

def row843 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

theorem rowCheck843 : row843 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow843 := by decide +kernel

theorem rowEval843 (x : Key → ℝ) : Integer.Sparse.eval row843 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck843, Integer.Sparse.eval_collectBalanced, rawRowCheck843]

def rawRow844 : Integer.Sparse Key := [(key2859, -2), (key2859, -2), (key2705, -2), (key2879, 1), (key2869, 1), (key2879, 1), (key2725, 1), (key2869, 1), (key2725, 1), (key2793, 2), (key2793, 2), (key2670, 2), (key2879, -1), (key2828, -1), (key2879, -1), (key2725, -1), (key2828, -1), (key2725, -1), (key2793, -1), (key2785, -1), (key2793, -1), (key2670, -1), (key2785, -1), (key2670, -1), (key2859, 1), (key2808, 1), (key2859, 1), (key2705, 1), (key2808, 1), (key2705, 1)]

theorem rawRowCheck844 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0 = rawRow844 := by decide +kernel

def row844 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

theorem rowCheck844 : row844 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow844 := by decide +kernel

theorem rowEval844 (x : Key → ℝ) : Integer.Sparse.eval row844 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck844, Integer.Sparse.eval_collectBalanced, rawRowCheck844]

def rawRow845 : Integer.Sparse Key := [(key2631, -2), (key2869, -2), (key2869, -2), (key2639, 1), (key2639, 1), (key2859, 1), (key2859, 1), (key2879, 1), (key2879, 1), (key2615, 2), (key2828, 2), (key2828, 2), (key2639, -1), (key2639, -1), (key2793, -1), (key2793, -1), (key2879, -1), (key2879, -1), (key2615, -1), (key2615, -1), (key2808, -1), (key2808, -1), (key2828, -1), (key2828, -1), (key2631, 1), (key2631, 1), (key2785, 1), (key2785, 1), (key2869, 1), (key2869, 1)]

theorem rawRowCheck845 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow845 := by decide +kernel

def row845 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

theorem rowCheck845 : row845 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow845 := by decide +kernel

theorem rowEval845 (x : Key → ℝ) : Integer.Sparse.eval row845 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck845, Integer.Sparse.eval_collectBalanced, rawRowCheck845]

def rawRow846 : Integer.Sparse Key := [(key2869, -2), (key2631, -2), (key2869, -2), (key2859, 1), (key2879, 1), (key2639, 1), (key2879, 1), (key2639, 1), (key2859, 1), (key2828, 2), (key2615, 2), (key2828, 2), (key2793, -1), (key2879, -1), (key2639, -1), (key2879, -1), (key2639, -1), (key2793, -1), (key2808, -1), (key2828, -1), (key2615, -1), (key2828, -1), (key2615, -1), (key2808, -1), (key2785, 1), (key2869, 1), (key2631, 1), (key2869, 1), (key2631, 1), (key2785, 1)]

theorem rawRowCheck846 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow846 := by decide +kernel

def row846 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

theorem rowCheck846 : row846 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow846 := by decide +kernel

theorem rowEval846 (x : Key → ℝ) : Integer.Sparse.eval row846 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck846, Integer.Sparse.eval_collectBalanced, rawRowCheck846]

def rawRow847 : Integer.Sparse Key := [(key2869, -2), (key2869, -2), (key2631, -2), (key2879, 1), (key2859, 1), (key2879, 1), (key2639, 1), (key2859, 1), (key2639, 1), (key2828, 2), (key2828, 2), (key2615, 2), (key2879, -1), (key2793, -1), (key2879, -1), (key2639, -1), (key2793, -1), (key2639, -1), (key2828, -1), (key2808, -1), (key2828, -1), (key2615, -1), (key2808, -1), (key2615, -1), (key2869, 1), (key2785, 1), (key2869, 1), (key2631, 1), (key2785, 1), (key2631, 1)]

theorem rawRowCheck847 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow847 := by decide +kernel

def row847 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

theorem rowCheck847 : row847 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow847 := by decide +kernel

theorem rowEval847 (x : Key → ℝ) : Integer.Sparse.eval row847 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck847, Integer.Sparse.eval_collectBalanced, rawRowCheck847]

def rawRow848 : Integer.Sparse Key := [(key1287, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1382, 6), (key1537, -2), (key1537, -2), (key1537, -2), (key1415, -2), (key1415, -2), (key1415, -2), (key1564, 2), (key1564, 2), (key1564, 2)]

theorem rawRowCheck848 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow848 := by decide +kernel

def row848 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1382, 6), (key1415, -6), (key1537, -6), (key1564, 6)]

theorem rowCheck848 : row848 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow848 := by decide +kernel

theorem rowEval848 (x : Key → ℝ) : Integer.Sparse.eval row848 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck848, Integer.Sparse.eval_collectBalanced, rawRowCheck848]

def rawRow849 : Integer.Sparse Key := [(key1307, -6), (key1287, 2), (key1307, 2), (key1307, 2), (key1537, 6), (key1382, -2), (key1537, -2), (key1537, -2), (key1564, -2), (key1613, -2), (key1613, -2), (key1415, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck849 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1 = rawRow849 := by decide +kernel

def row849 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

theorem rowCheck849 : row849 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow849 := by decide +kernel

theorem rowEval849 (x : Key → ℝ) : Integer.Sparse.eval row849 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck849, Integer.Sparse.eval_collectBalanced, rawRowCheck849]

def rawRow850 : Integer.Sparse Key := [(key1307, -6), (key1307, 2), (key1287, 2), (key1307, 2), (key1537, 6), (key1537, -2), (key1382, -2), (key1537, -2), (key1613, -2), (key1564, -2), (key1613, -2), (key1613, 2), (key1415, 2), (key1613, 2)]

theorem rawRowCheck850 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1 = rawRow850 := by decide +kernel

def row850 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

theorem rowCheck850 : row850 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow850 := by decide +kernel

theorem rowEval850 (x : Key → ℝ) : Integer.Sparse.eval row850 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck850, Integer.Sparse.eval_collectBalanced, rawRowCheck850]

def rawRow851 : Integer.Sparse Key := [(key1307, -6), (key1307, 2), (key1307, 2), (key1287, 2), (key1537, 6), (key1537, -2), (key1537, -2), (key1382, -2), (key1613, -2), (key1613, -2), (key1564, -2), (key1613, 2), (key1613, 2), (key1415, 2)]

theorem rawRowCheck851 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1 = rawRow851 := by decide +kernel

def row851 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

theorem rowCheck851 : row851 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow851 := by decide +kernel

theorem rowEval851 (x : Key → ℝ) : Integer.Sparse.eval row851 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck851, Integer.Sparse.eval_collectBalanced, rawRowCheck851]

def rawRow852 : Integer.Sparse Key := [(key1382, -6), (key1415, 2), (key1415, 2), (key1415, 2), (key1287, 6), (key1564, -2), (key1564, -2), (key1564, -2), (key1307, -2), (key1307, -2), (key1307, -2), (key1537, 2), (key1537, 2), (key1537, 2)]

theorem rawRowCheck852 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow852 := by decide +kernel

def row852 : Integer.Sparse Key := [(key1287, 6), (key1307, -6), (key1382, -6), (key1415, 6), (key1537, 6), (key1564, -6)]

theorem rowCheck852 : row852 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow852 := by decide +kernel

theorem rowEval852 (x : Key → ℝ) : Integer.Sparse.eval row852 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck852, Integer.Sparse.eval_collectBalanced, rawRowCheck852]

def rawRow853 : Integer.Sparse Key := [(key1415, -6), (key1382, 2), (key1415, 2), (key1415, 2), (key1564, 6), (key1287, -2), (key1564, -2), (key1564, -2), (key1537, -2), (key1613, -2), (key1613, -2), (key1307, 2), (key1613, 2), (key1613, 2)]

theorem rawRowCheck853 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow853 := by decide +kernel

def row853 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

theorem rowCheck853 : row853 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow853 := by decide +kernel

theorem rowEval853 (x : Key → ℝ) : Integer.Sparse.eval row853 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck853, Integer.Sparse.eval_collectBalanced, rawRowCheck853]

def rawRow854 : Integer.Sparse Key := [(key1415, -6), (key1415, 2), (key1382, 2), (key1415, 2), (key1564, 6), (key1564, -2), (key1287, -2), (key1564, -2), (key1613, -2), (key1537, -2), (key1613, -2), (key1613, 2), (key1307, 2), (key1613, 2)]

theorem rawRowCheck854 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow854 := by decide +kernel

def row854 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

theorem rowCheck854 : row854 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow854 := by decide +kernel

theorem rowEval854 (x : Key → ℝ) : Integer.Sparse.eval row854 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck854, Integer.Sparse.eval_collectBalanced, rawRowCheck854]

def rawRow855 : Integer.Sparse Key := [(key1415, -6), (key1415, 2), (key1415, 2), (key1382, 2), (key1564, 6), (key1564, -2), (key1564, -2), (key1287, -2), (key1613, -2), (key1613, -2), (key1537, -2), (key1613, 2), (key1613, 2), (key1307, 2)]

theorem rawRowCheck855 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow855 := by decide +kernel

def row855 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

theorem rowCheck855 : row855 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow855 := by decide +kernel

theorem rowEval855 (x : Key → ℝ) : Integer.Sparse.eval row855 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck855, Integer.Sparse.eval_collectBalanced, rawRowCheck855]

def rawRow856 : Integer.Sparse Key := [(key1537, -6), (key1564, 2), (key1613, 2), (key1613, 2), (key1307, 6), (key1415, -2), (key1613, -2), (key1613, -2), (key1287, -2), (key1307, -2), (key1307, -2), (key1382, 2), (key1537, 2), (key1537, 2)]

theorem rawRowCheck856 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1 = rawRow856 := by decide +kernel

def row856 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

theorem rowCheck856 : row856 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow856 := by decide +kernel

theorem rowEval856 (x : Key → ℝ) : Integer.Sparse.eval row856 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck856, Integer.Sparse.eval_collectBalanced, rawRowCheck856]

def rawRow857 : Integer.Sparse Key := [(key1537, -6), (key1613, 2), (key1564, 2), (key1613, 2), (key1307, 6), (key1613, -2), (key1415, -2), (key1613, -2), (key1307, -2), (key1287, -2), (key1307, -2), (key1537, 2), (key1382, 2), (key1537, 2)]

theorem rawRowCheck857 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1 = rawRow857 := by decide +kernel

def row857 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

theorem rowCheck857 : row857 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow857 := by decide +kernel

theorem rowEval857 (x : Key → ℝ) : Integer.Sparse.eval row857 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck857, Integer.Sparse.eval_collectBalanced, rawRowCheck857]

def rawRow858 : Integer.Sparse Key := [(key1537, -6), (key1613, 2), (key1613, 2), (key1564, 2), (key1307, 6), (key1613, -2), (key1613, -2), (key1415, -2), (key1307, -2), (key1307, -2), (key1287, -2), (key1537, 2), (key1537, 2), (key1382, 2)]

theorem rawRowCheck858 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1 = rawRow858 := by decide +kernel

def row858 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

theorem rowCheck858 : row858 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow858 := by decide +kernel

theorem rowEval858 (x : Key → ℝ) : Integer.Sparse.eval row858 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck858, Integer.Sparse.eval_collectBalanced, rawRowCheck858]

def rawRow859 : Integer.Sparse Key := [(key1564, -6), (key1537, 2), (key1613, 2), (key1613, 2), (key1415, 6), (key1307, -2), (key1613, -2), (key1613, -2), (key1382, -2), (key1415, -2), (key1415, -2), (key1287, 2), (key1564, 2), (key1564, 2)]

theorem rawRowCheck859 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow859 := by decide +kernel

def row859 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

theorem rowCheck859 : row859 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow859 := by decide +kernel

theorem rowEval859 (x : Key → ℝ) : Integer.Sparse.eval row859 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck859, Integer.Sparse.eval_collectBalanced, rawRowCheck859]

def rawRow860 : Integer.Sparse Key := [(key1564, -6), (key1613, 2), (key1537, 2), (key1613, 2), (key1415, 6), (key1613, -2), (key1307, -2), (key1613, -2), (key1415, -2), (key1382, -2), (key1415, -2), (key1564, 2), (key1287, 2), (key1564, 2)]

theorem rawRowCheck860 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow860 := by decide +kernel

def row860 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

theorem rowCheck860 : row860 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow860 := by decide +kernel

theorem rowEval860 (x : Key → ℝ) : Integer.Sparse.eval row860 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck860, Integer.Sparse.eval_collectBalanced, rawRowCheck860]

def rawRow861 : Integer.Sparse Key := [(key1564, -6), (key1613, 2), (key1613, 2), (key1537, 2), (key1415, 6), (key1613, -2), (key1613, -2), (key1307, -2), (key1415, -2), (key1415, -2), (key1382, -2), (key1564, 2), (key1564, 2), (key1287, 2)]

theorem rawRowCheck861 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow861 := by decide +kernel

def row861 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

theorem rowCheck861 : row861 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow861 := by decide +kernel

theorem rowEval861 (x : Key → ℝ) : Integer.Sparse.eval row861 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck861, Integer.Sparse.eval_collectBalanced, rawRowCheck861]

def rawRow862 : Integer.Sparse Key := [(key2610, -2), (key2610, -2), (key2610, -2), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2626, 1), (key2665, 2), (key2665, 2), (key2665, 2), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2780, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2700, -1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1), (key2803, 1)]

theorem rawRowCheck862 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow862 := by decide +kernel

def row862 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2665, 6), (key2700, -6), (key2780, -6), (key2803, 6)]

theorem rowCheck862 : row862 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow862 := by decide +kernel

theorem rowEval862 (x : Key → ℝ) : Integer.Sparse.eval row862 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck862, Integer.Sparse.eval_collectBalanced, rawRowCheck862]

def rawRow863 : Integer.Sparse Key := [(key2626, -2), (key2626, -2), (key2635, -2), (key2610, 1), (key2610, 1), (key2626, 1), (key2626, 1), (key2635, 1), (key2635, 1), (key2780, 2), (key2780, 2), (key2789, 2), (key2665, -1), (key2665, -1), (key2780, -1), (key2780, -1), (key2789, -1), (key2789, -1), (key2803, -1), (key2803, -1), (key2853, -1), (key2853, -1), (key2855, -1), (key2855, -1), (key2700, 1), (key2700, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1)]

theorem rawRowCheck863 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form2 = rawRow863 := by decide +kernel

def row863 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

theorem rowCheck863 : row863 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow863 := by decide +kernel

theorem rowEval863 (x : Key → ℝ) : Integer.Sparse.eval row863 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck863, Integer.Sparse.eval_collectBalanced, rawRowCheck863]

end MUB6.Certificate.GramRows

end OAI
