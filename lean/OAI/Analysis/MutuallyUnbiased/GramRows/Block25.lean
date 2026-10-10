import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow896 : Integer.Sparse Key := [(key2696, -6), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 6), (key2799, -2), (key2606, -2), (key2799, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, 2), (key2622, 2), (key2849, 2)]

theorem rawRowCheck896 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form4 = rawRow896 := by decide +kernel

def row896 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

theorem rowCheck896 : row896 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow896 := by decide +kernel

theorem rowEval896 (x : Key → ℝ) : Integer.Sparse.eval row896 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck896, Integer.Sparse.eval_collectBalanced, rawRowCheck896]

def rawRow897 : Integer.Sparse Key := [(key2696, -6), (key2696, 2), (key2696, 2), (key2661, 2), (key2799, 6), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, -2), (key2849, -2), (key2696, -2), (key2849, 2), (key2849, 2), (key2622, 2)]

theorem rawRowCheck897 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form4 = rawRow897 := by decide +kernel

def row897 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

theorem rowCheck897 : row897 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow897 := by decide +kernel

theorem rowEval897 (x : Key → ℝ) : Integer.Sparse.eval row897 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck897, Integer.Sparse.eval_collectBalanced, rawRowCheck897]

def rawRow898 : Integer.Sparse Key := [(key2776, -6), (key2799, 2), (key2849, 2), (key2849, 2), (key2622, 6), (key2696, -2), (key2849, -2), (key2849, -2), (key2606, -2), (key2622, -2), (key2622, -2), (key2661, 2), (key2696, 2), (key2696, 2)]

theorem rawRowCheck898 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form4 = rawRow898 := by decide +kernel

def row898 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

theorem rowCheck898 : row898 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow898 := by decide +kernel

theorem rowEval898 (x : Key → ℝ) : Integer.Sparse.eval row898 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck898, Integer.Sparse.eval_collectBalanced, rawRowCheck898]

def rawRow899 : Integer.Sparse Key := [(key2776, -6), (key2849, 2), (key2799, 2), (key2849, 2), (key2622, 6), (key2849, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, 2), (key2661, 2), (key2696, 2)]

theorem rawRowCheck899 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form4 = rawRow899 := by decide +kernel

def row899 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

theorem rowCheck899 : row899 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow899 := by decide +kernel

theorem rowEval899 (x : Key → ℝ) : Integer.Sparse.eval row899 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck899, Integer.Sparse.eval_collectBalanced, rawRowCheck899]

def rawRow900 : Integer.Sparse Key := [(key2776, -6), (key2849, 2), (key2849, 2), (key2799, 2), (key2622, 6), (key2849, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, 2), (key2696, 2), (key2661, 2)]

theorem rawRowCheck900 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form4 = rawRow900 := by decide +kernel

def row900 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

theorem rowCheck900 : row900 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow900 := by decide +kernel

theorem rowEval900 (x : Key → ℝ) : Integer.Sparse.eval row900 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck900, Integer.Sparse.eval_collectBalanced, rawRowCheck900]

def rawRow901 : Integer.Sparse Key := [(key2799, -6), (key2776, 2), (key2849, 2), (key2849, 2), (key2696, 6), (key2622, -2), (key2849, -2), (key2849, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2606, 2), (key2799, 2), (key2799, 2)]

theorem rawRowCheck901 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form4 = rawRow901 := by decide +kernel

def row901 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

theorem rowCheck901 : row901 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow901 := by decide +kernel

theorem rowEval901 (x : Key → ℝ) : Integer.Sparse.eval row901 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck901, Integer.Sparse.eval_collectBalanced, rawRowCheck901]

def rawRow902 : Integer.Sparse Key := [(key2799, -6), (key2849, 2), (key2776, 2), (key2849, 2), (key2696, 6), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 2), (key2606, 2), (key2799, 2)]

theorem rawRowCheck902 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form4 = rawRow902 := by decide +kernel

def row902 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

theorem rowCheck902 : row902 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow902 := by decide +kernel

theorem rowEval902 (x : Key → ℝ) : Integer.Sparse.eval row902 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck902, Integer.Sparse.eval_collectBalanced, rawRowCheck902]

def rawRow903 : Integer.Sparse Key := [(key2799, -6), (key2849, 2), (key2849, 2), (key2776, 2), (key2696, 6), (key2849, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, 2), (key2799, 2), (key2606, 2)]

theorem rawRowCheck903 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form4 = rawRow903 := by decide +kernel

def row903 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

theorem rowCheck903 : row903 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow903 := by decide +kernel

theorem rowEval903 (x : Key → ℝ) : Integer.Sparse.eval row903 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block1.form4) x := by
  rw [rowCheck903, Integer.Sparse.eval_collectBalanced, rawRowCheck903]

def rawRow904 : Integer.Sparse Key := [(key1296, -2), (key1788, -2), (key1799, -2), (key1296, 1), (key1303, 1), (key1573, 1), (key1597, 1), (key1791, 1), (key1799, 1), (key1316, 2), (key1813, 2), (key1826, 2), (key1316, -1), (key1330, -1), (key1424, -1), (key1448, -1), (key1818, -1), (key1826, -1), (key1337, -1), (key1340, -1), (key1655, -1), (key1668, -1), (key1840, -1), (key1845, -1), (key1337, 1), (key1346, 1), (key1455, 1), (key1467, 1), (key1842, 1), (key1845, 1)]

theorem rawRowCheck904 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form0 = rawRow904 := by decide +kernel

def row904 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

theorem rowCheck904 : row904 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow904 := by decide +kernel

theorem rowEval904 (x : Key → ℝ) : Integer.Sparse.eval row904 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck904, Integer.Sparse.eval_collectBalanced, rawRowCheck904]

def rawRow905 : Integer.Sparse Key := [(key1296, -2), (key1799, -2), (key1788, -2), (key1303, 1), (key1296, 1), (key1597, 1), (key1573, 1), (key1799, 1), (key1791, 1), (key1316, 2), (key1826, 2), (key1813, 2), (key1330, -1), (key1316, -1), (key1448, -1), (key1424, -1), (key1826, -1), (key1818, -1), (key1340, -1), (key1337, -1), (key1668, -1), (key1655, -1), (key1845, -1), (key1840, -1), (key1346, 1), (key1337, 1), (key1467, 1), (key1455, 1), (key1845, 1), (key1842, 1)]

theorem rawRowCheck905 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form0 = rawRow905 := by decide +kernel

def row905 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

theorem rowCheck905 : row905 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow905 := by decide +kernel

theorem rowEval905 (x : Key → ℝ) : Integer.Sparse.eval row905 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck905, Integer.Sparse.eval_collectBalanced, rawRowCheck905]

def rawRow906 : Integer.Sparse Key := [(key1788, -2), (key1296, -2), (key1799, -2), (key1573, 1), (key1791, 1), (key1296, 1), (key1799, 1), (key1303, 1), (key1597, 1), (key1813, 2), (key1316, 2), (key1826, 2), (key1424, -1), (key1818, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1655, -1), (key1840, -1), (key1337, -1), (key1845, -1), (key1340, -1), (key1668, -1), (key1455, 1), (key1842, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1467, 1)]

theorem rawRowCheck906 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form0 = rawRow906 := by decide +kernel

def row906 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

theorem rowCheck906 : row906 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow906 := by decide +kernel

theorem rowEval906 (x : Key → ℝ) : Integer.Sparse.eval row906 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck906, Integer.Sparse.eval_collectBalanced, rawRowCheck906]

def rawRow907 : Integer.Sparse Key := [(key1788, -2), (key1799, -2), (key1296, -2), (key1791, 1), (key1573, 1), (key1799, 1), (key1296, 1), (key1597, 1), (key1303, 1), (key1813, 2), (key1826, 2), (key1316, 2), (key1818, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1448, -1), (key1330, -1), (key1840, -1), (key1655, -1), (key1845, -1), (key1337, -1), (key1668, -1), (key1340, -1), (key1842, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1467, 1), (key1346, 1)]

theorem rawRowCheck907 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form0 = rawRow907 := by decide +kernel

def row907 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

theorem rowCheck907 : row907 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow907 := by decide +kernel

theorem rowEval907 (x : Key → ℝ) : Integer.Sparse.eval row907 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck907, Integer.Sparse.eval_collectBalanced, rawRowCheck907]

def rawRow908 : Integer.Sparse Key := [(key1799, -2), (key1296, -2), (key1788, -2), (key1597, 1), (key1799, 1), (key1303, 1), (key1791, 1), (key1296, 1), (key1573, 1), (key1826, 2), (key1316, 2), (key1813, 2), (key1448, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1316, -1), (key1424, -1), (key1668, -1), (key1845, -1), (key1340, -1), (key1840, -1), (key1337, -1), (key1655, -1), (key1467, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck908 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form0 = rawRow908 := by decide +kernel

def row908 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

theorem rowCheck908 : row908 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow908 := by decide +kernel

theorem rowEval908 (x : Key → ℝ) : Integer.Sparse.eval row908 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck908, Integer.Sparse.eval_collectBalanced, rawRowCheck908]

def rawRow909 : Integer.Sparse Key := [(key1799, -2), (key1788, -2), (key1296, -2), (key1799, 1), (key1597, 1), (key1791, 1), (key1303, 1), (key1573, 1), (key1296, 1), (key1826, 2), (key1813, 2), (key1316, 2), (key1826, -1), (key1448, -1), (key1818, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1845, -1), (key1668, -1), (key1840, -1), (key1340, -1), (key1655, -1), (key1337, -1), (key1845, 1), (key1467, 1), (key1842, 1), (key1346, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck909 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form0 = rawRow909 := by decide +kernel

def row909 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

theorem rowCheck909 : row909 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow909 := by decide +kernel

theorem rowEval909 (x : Key → ℝ) : Integer.Sparse.eval row909 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck909, Integer.Sparse.eval_collectBalanced, rawRowCheck909]

def rawRow910 : Integer.Sparse Key := [(key1303, -2), (key1791, -2), (key1791, -2), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1330, 2), (key1818, 2), (key1818, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1346, -1), (key1346, -1), (key1660, -1), (key1660, -1), (key1842, -1), (key1842, -1), (key1340, 1), (key1340, 1), (key1458, 1), (key1458, 1), (key1840, 1), (key1840, 1)]

theorem rawRowCheck910 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form0 = rawRow910 := by decide +kernel

def row910 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

theorem rowCheck910 : row910 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow910 := by decide +kernel

theorem rowEval910 (x : Key → ℝ) : Integer.Sparse.eval row910 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck910, Integer.Sparse.eval_collectBalanced, rawRowCheck910]

def rawRow911 : Integer.Sparse Key := [(key1791, -2), (key1303, -2), (key1791, -2), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1818, 2), (key1330, 2), (key1818, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1660, -1), (key1842, -1), (key1346, -1), (key1842, -1), (key1346, -1), (key1660, -1), (key1458, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1458, 1)]

theorem rawRowCheck911 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form0 = rawRow911 := by decide +kernel

def row911 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

theorem rowCheck911 : row911 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow911 := by decide +kernel

theorem rowEval911 (x : Key → ℝ) : Integer.Sparse.eval row911 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck911, Integer.Sparse.eval_collectBalanced, rawRowCheck911]

def rawRow912 : Integer.Sparse Key := [(key1791, -2), (key1791, -2), (key1303, -2), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1296, 1), (key1818, 2), (key1818, 2), (key1330, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1842, -1), (key1660, -1), (key1842, -1), (key1346, -1), (key1660, -1), (key1346, -1), (key1840, 1), (key1458, 1), (key1840, 1), (key1340, 1), (key1458, 1), (key1340, 1)]

theorem rawRowCheck912 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form0 = rawRow912 := by decide +kernel

def row912 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

theorem rowCheck912 : row912 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow912 := by decide +kernel

theorem rowEval912 (x : Key → ℝ) : Integer.Sparse.eval row912 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck912, Integer.Sparse.eval_collectBalanced, rawRowCheck912]

def rawRow913 : Integer.Sparse Key := [(key1316, -2), (key1813, -2), (key1826, -2), (key1337, 1), (key1340, 1), (key1655, 1), (key1668, 1), (key1840, 1), (key1845, 1), (key1296, 2), (key1788, 2), (key1799, 2), (key1337, -1), (key1346, -1), (key1455, -1), (key1467, -1), (key1842, -1), (key1845, -1), (key1296, -1), (key1303, -1), (key1573, -1), (key1597, -1), (key1791, -1), (key1799, -1), (key1316, 1), (key1330, 1), (key1424, 1), (key1448, 1), (key1818, 1), (key1826, 1)]

theorem rawRowCheck913 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form0 = rawRow913 := by decide +kernel

def row913 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

theorem rowCheck913 : row913 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow913 := by decide +kernel

theorem rowEval913 (x : Key → ℝ) : Integer.Sparse.eval row913 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck913, Integer.Sparse.eval_collectBalanced, rawRowCheck913]

def rawRow914 : Integer.Sparse Key := [(key1316, -2), (key1826, -2), (key1813, -2), (key1340, 1), (key1337, 1), (key1668, 1), (key1655, 1), (key1845, 1), (key1840, 1), (key1296, 2), (key1799, 2), (key1788, 2), (key1346, -1), (key1337, -1), (key1467, -1), (key1455, -1), (key1845, -1), (key1842, -1), (key1303, -1), (key1296, -1), (key1597, -1), (key1573, -1), (key1799, -1), (key1791, -1), (key1330, 1), (key1316, 1), (key1448, 1), (key1424, 1), (key1826, 1), (key1818, 1)]

theorem rawRowCheck914 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form0 = rawRow914 := by decide +kernel

def row914 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

theorem rowCheck914 : row914 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow914 := by decide +kernel

theorem rowEval914 (x : Key → ℝ) : Integer.Sparse.eval row914 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck914, Integer.Sparse.eval_collectBalanced, rawRowCheck914]

def rawRow915 : Integer.Sparse Key := [(key1813, -2), (key1316, -2), (key1826, -2), (key1655, 1), (key1840, 1), (key1337, 1), (key1845, 1), (key1340, 1), (key1668, 1), (key1788, 2), (key1296, 2), (key1799, 2), (key1455, -1), (key1842, -1), (key1337, -1), (key1845, -1), (key1346, -1), (key1467, -1), (key1573, -1), (key1791, -1), (key1296, -1), (key1799, -1), (key1303, -1), (key1597, -1), (key1424, 1), (key1818, 1), (key1316, 1), (key1826, 1), (key1330, 1), (key1448, 1)]

theorem rawRowCheck915 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form0 = rawRow915 := by decide +kernel

def row915 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

theorem rowCheck915 : row915 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow915 := by decide +kernel

theorem rowEval915 (x : Key → ℝ) : Integer.Sparse.eval row915 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck915, Integer.Sparse.eval_collectBalanced, rawRowCheck915]

def rawRow916 : Integer.Sparse Key := [(key1813, -2), (key1826, -2), (key1316, -2), (key1840, 1), (key1655, 1), (key1845, 1), (key1337, 1), (key1668, 1), (key1340, 1), (key1788, 2), (key1799, 2), (key1296, 2), (key1842, -1), (key1455, -1), (key1845, -1), (key1337, -1), (key1467, -1), (key1346, -1), (key1791, -1), (key1573, -1), (key1799, -1), (key1296, -1), (key1597, -1), (key1303, -1), (key1818, 1), (key1424, 1), (key1826, 1), (key1316, 1), (key1448, 1), (key1330, 1)]

theorem rawRowCheck916 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form0 = rawRow916 := by decide +kernel

def row916 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

theorem rowCheck916 : row916 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow916 := by decide +kernel

theorem rowEval916 (x : Key → ℝ) : Integer.Sparse.eval row916 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck916, Integer.Sparse.eval_collectBalanced, rawRowCheck916]

def rawRow917 : Integer.Sparse Key := [(key1826, -2), (key1316, -2), (key1813, -2), (key1668, 1), (key1845, 1), (key1340, 1), (key1840, 1), (key1337, 1), (key1655, 1), (key1799, 2), (key1296, 2), (key1788, 2), (key1467, -1), (key1845, -1), (key1346, -1), (key1842, -1), (key1337, -1), (key1455, -1), (key1597, -1), (key1799, -1), (key1303, -1), (key1791, -1), (key1296, -1), (key1573, -1), (key1448, 1), (key1826, 1), (key1330, 1), (key1818, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck917 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form0 = rawRow917 := by decide +kernel

def row917 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

theorem rowCheck917 : row917 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow917 := by decide +kernel

theorem rowEval917 (x : Key → ℝ) : Integer.Sparse.eval row917 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck917, Integer.Sparse.eval_collectBalanced, rawRowCheck917]

def rawRow918 : Integer.Sparse Key := [(key1826, -2), (key1813, -2), (key1316, -2), (key1845, 1), (key1668, 1), (key1840, 1), (key1340, 1), (key1655, 1), (key1337, 1), (key1799, 2), (key1788, 2), (key1296, 2), (key1845, -1), (key1467, -1), (key1842, -1), (key1346, -1), (key1455, -1), (key1337, -1), (key1799, -1), (key1597, -1), (key1791, -1), (key1303, -1), (key1573, -1), (key1296, -1), (key1826, 1), (key1448, 1), (key1818, 1), (key1330, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck918 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form0 = rawRow918 := by decide +kernel

def row918 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

theorem rowCheck918 : row918 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow918 := by decide +kernel

theorem rowEval918 (x : Key → ℝ) : Integer.Sparse.eval row918 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck918, Integer.Sparse.eval_collectBalanced, rawRowCheck918]

def rawRow919 : Integer.Sparse Key := [(key1340, -2), (key1775, -2), (key1840, -2), (key1316, 1), (key1337, 1), (key1546, 1), (key1655, 1), (key1772, 1), (key1813, 1), (key1346, 2), (key1781, 2), (key1842, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1330, -1), (key1346, -1), (key1560, -1), (key1660, -1), (key1781, -1), (key1818, -1), (key1303, 1), (key1340, 1), (key1398, 1), (key1458, 1), (key1775, 1), (key1791, 1)]

theorem rawRowCheck919 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form0 = rawRow919 := by decide +kernel

def row919 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

theorem rowCheck919 : row919 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow919 := by decide +kernel

theorem rowEval919 (x : Key → ℝ) : Integer.Sparse.eval row919 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck919, Integer.Sparse.eval_collectBalanced, rawRowCheck919]

def rawRow920 : Integer.Sparse Key := [(key1340, -2), (key1840, -2), (key1775, -2), (key1337, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1772, 1), (key1346, 2), (key1842, 2), (key1781, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1346, -1), (key1330, -1), (key1660, -1), (key1560, -1), (key1818, -1), (key1781, -1), (key1340, 1), (key1303, 1), (key1458, 1), (key1398, 1), (key1791, 1), (key1775, 1)]

theorem rawRowCheck920 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form0 = rawRow920 := by decide +kernel

def row920 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

theorem rowCheck920 : row920 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow920 := by decide +kernel

theorem rowEval920 (x : Key → ℝ) : Integer.Sparse.eval row920 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck920, Integer.Sparse.eval_collectBalanced, rawRowCheck920]

def rawRow921 : Integer.Sparse Key := [(key1775, -2), (key1340, -2), (key1840, -2), (key1546, 1), (key1772, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1781, 2), (key1346, 2), (key1842, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1560, -1), (key1781, -1), (key1330, -1), (key1818, -1), (key1346, -1), (key1660, -1), (key1398, 1), (key1775, 1), (key1303, 1), (key1791, 1), (key1340, 1), (key1458, 1)]

theorem rawRowCheck921 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form0 = rawRow921 := by decide +kernel

def row921 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

theorem rowCheck921 : row921 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow921 := by decide +kernel

theorem rowEval921 (x : Key → ℝ) : Integer.Sparse.eval row921 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck921, Integer.Sparse.eval_collectBalanced, rawRowCheck921]

def rawRow922 : Integer.Sparse Key := [(key1775, -2), (key1840, -2), (key1340, -2), (key1772, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1655, 1), (key1337, 1), (key1781, 2), (key1842, 2), (key1346, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1781, -1), (key1560, -1), (key1818, -1), (key1330, -1), (key1660, -1), (key1346, -1), (key1775, 1), (key1398, 1), (key1791, 1), (key1303, 1), (key1458, 1), (key1340, 1)]

theorem rawRowCheck922 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form0 = rawRow922 := by decide +kernel

def row922 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

theorem rowCheck922 : row922 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow922 := by decide +kernel

theorem rowEval922 (x : Key → ℝ) : Integer.Sparse.eval row922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck922, Integer.Sparse.eval_collectBalanced, rawRowCheck922]

def rawRow923 : Integer.Sparse Key := [(key1840, -2), (key1340, -2), (key1775, -2), (key1655, 1), (key1813, 1), (key1337, 1), (key1772, 1), (key1316, 1), (key1546, 1), (key1842, 2), (key1346, 2), (key1781, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1660, -1), (key1818, -1), (key1346, -1), (key1781, -1), (key1330, -1), (key1560, -1), (key1458, 1), (key1791, 1), (key1340, 1), (key1775, 1), (key1303, 1), (key1398, 1)]

theorem rawRowCheck923 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form0 = rawRow923 := by decide +kernel

def row923 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

theorem rowCheck923 : row923 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow923 := by decide +kernel

theorem rowEval923 (x : Key → ℝ) : Integer.Sparse.eval row923 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck923, Integer.Sparse.eval_collectBalanced, rawRowCheck923]

def rawRow924 : Integer.Sparse Key := [(key1840, -2), (key1775, -2), (key1340, -2), (key1813, 1), (key1655, 1), (key1772, 1), (key1337, 1), (key1546, 1), (key1316, 1), (key1842, 2), (key1781, 2), (key1346, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1818, -1), (key1660, -1), (key1781, -1), (key1346, -1), (key1560, -1), (key1330, -1), (key1791, 1), (key1458, 1), (key1775, 1), (key1340, 1), (key1398, 1), (key1303, 1)]

theorem rawRowCheck924 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form0 = rawRow924 := by decide +kernel

def row924 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

theorem rowCheck924 : row924 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow924 := by decide +kernel

theorem rowEval924 (x : Key → ℝ) : Integer.Sparse.eval row924 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck924, Integer.Sparse.eval_collectBalanced, rawRowCheck924]

def rawRow925 : Integer.Sparse Key := [(key1330, -2), (key1818, -2), (key1818, -2), (key1346, 1), (key1346, 1), (key1660, 1), (key1660, 1), (key1842, 1), (key1842, 1), (key1303, 2), (key1791, 2), (key1791, 2), (key1340, -1), (key1340, -1), (key1458, -1), (key1458, -1), (key1840, -1), (key1840, -1), (key1296, -1), (key1296, -1), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

theorem rawRowCheck925 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow925 := by decide +kernel

def row925 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

theorem rowCheck925 : row925 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow925 := by decide +kernel

theorem rowEval925 (x : Key → ℝ) : Integer.Sparse.eval row925 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck925, Integer.Sparse.eval_collectBalanced, rawRowCheck925]

def rawRow926 : Integer.Sparse Key := [(key1818, -2), (key1330, -2), (key1818, -2), (key1660, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1660, 1), (key1791, 2), (key1303, 2), (key1791, 2), (key1458, -1), (key1840, -1), (key1340, -1), (key1840, -1), (key1340, -1), (key1458, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

theorem rawRowCheck926 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow926 := by decide +kernel

def row926 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

theorem rowCheck926 : row926 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow926 := by decide +kernel

theorem rowEval926 (x : Key → ℝ) : Integer.Sparse.eval row926 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck926, Integer.Sparse.eval_collectBalanced, rawRowCheck926]

def rawRow927 : Integer.Sparse Key := [(key1818, -2), (key1818, -2), (key1330, -2), (key1842, 1), (key1660, 1), (key1842, 1), (key1346, 1), (key1660, 1), (key1346, 1), (key1791, 2), (key1791, 2), (key1303, 2), (key1840, -1), (key1458, -1), (key1840, -1), (key1340, -1), (key1458, -1), (key1340, -1), (key1788, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1296, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

theorem rawRowCheck927 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow927 := by decide +kernel

def row927 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

theorem rowCheck927 : row927 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow927 := by decide +kernel

theorem rowEval927 (x : Key → ℝ) : Integer.Sparse.eval row927 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck927, Integer.Sparse.eval_collectBalanced, rawRowCheck927]

end MUB6.Certificate.GramRows

end OAI
