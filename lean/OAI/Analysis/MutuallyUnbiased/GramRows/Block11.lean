import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow448 : Integer.Sparse Key := [(key1654, -1), (key1657, -1), (key1665, 2), (key1545, 1), (key1554, 1), (key1591, -1), (key1631, -1), (key1541, -2), (key1568, 1), (key1617, 1), (key1812, 1), (key1815, 1), (key1823, -2), (key1315, -1), (key1324, -1), (key1442, 1), (key1631, 1), (key1311, 2), (key1419, -1), (key1617, -1), (key1771, -1), (key1778, -1), (key1796, 1), (key1823, 1), (key1336, 1), (key1343, 1), (key1464, -1), (key1665, -1), (key1291, -1), (key1311, -1), (key1386, 1), (key1541, 1), (key1771, 2), (key1787, -1), (key1812, -1), (key1336, -2), (key1454, 1), (key1654, 1), (key1295, 1), (key1315, 1), (key1390, -1), (key1545, -1)]

theorem rawRowCheck448 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form0 = rawRow448 := by decide +kernel

def row448 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck448 : row448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow448 := by decide +kernel

theorem rowEval448 (x : Key → ℝ) : Integer.Sparse.eval row448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck448, Integer.Sparse.eval_collectBalanced, rawRowCheck448]

def rawRow449 : Integer.Sparse Key := [(key1657, -1), (key1654, -1), (key1665, 2), (key1554, 1), (key1545, 1), (key1631, -1), (key1591, -1), (key1541, -2), (key1617, 1), (key1568, 1), (key1815, 1), (key1812, 1), (key1823, -2), (key1324, -1), (key1315, -1), (key1631, 1), (key1442, 1), (key1311, 2), (key1617, -1), (key1419, -1), (key1778, -1), (key1771, -1), (key1823, 1), (key1796, 1), (key1343, 1), (key1336, 1), (key1665, -1), (key1464, -1), (key1311, -1), (key1291, -1), (key1541, 1), (key1386, 1), (key1771, 2), (key1812, -1), (key1787, -1), (key1336, -2), (key1654, 1), (key1454, 1), (key1315, 1), (key1295, 1), (key1545, -1), (key1390, -1)]

theorem rawRowCheck449 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form0 = rawRow449 := by decide +kernel

def row449 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck449 : row449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow449 := by decide +kernel

theorem rowEval449 (x : Key → ℝ) : Integer.Sparse.eval row449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck449, Integer.Sparse.eval_collectBalanced, rawRowCheck449]

def rawRow450 : Integer.Sparse Key := [(key1654, -1), (key1665, -1), (key1657, 2), (key1572, 1), (key1591, 1), (key1554, -1), (key1622, -1), (key1568, -2), (key1541, 1), (key1617, 1), (key1812, 1), (key1823, 1), (key1815, -2), (key1423, -1), (key1442, -1), (key1324, 1), (key1622, 1), (key1419, 2), (key1311, -1), (key1617, -1), (key1787, -1), (key1796, -1), (key1778, 1), (key1815, 1), (key1454, 1), (key1464, 1), (key1343, -1), (key1657, -1), (key1386, -1), (key1419, -1), (key1291, 1), (key1568, 1), (key1787, 2), (key1771, -1), (key1812, -1), (key1454, -2), (key1336, 1), (key1654, 1), (key1390, 1), (key1423, 1), (key1295, -1), (key1572, -1)]

theorem rawRowCheck450 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form0 = rawRow450 := by decide +kernel

def row450 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck450 : row450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow450 := by decide +kernel

theorem rowEval450 (x : Key → ℝ) : Integer.Sparse.eval row450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck450, Integer.Sparse.eval_collectBalanced, rawRowCheck450]

def rawRow451 : Integer.Sparse Key := [(key1665, -1), (key1654, -1), (key1657, 2), (key1591, 1), (key1572, 1), (key1622, -1), (key1554, -1), (key1568, -2), (key1617, 1), (key1541, 1), (key1823, 1), (key1812, 1), (key1815, -2), (key1442, -1), (key1423, -1), (key1622, 1), (key1324, 1), (key1419, 2), (key1617, -1), (key1311, -1), (key1796, -1), (key1787, -1), (key1815, 1), (key1778, 1), (key1464, 1), (key1454, 1), (key1657, -1), (key1343, -1), (key1419, -1), (key1386, -1), (key1568, 1), (key1291, 1), (key1787, 2), (key1812, -1), (key1771, -1), (key1454, -2), (key1654, 1), (key1336, 1), (key1423, 1), (key1390, 1), (key1572, -1), (key1295, -1)]

theorem rawRowCheck451 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form0 = rawRow451 := by decide +kernel

def row451 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck451 : row451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow451 := by decide +kernel

theorem rowEval451 (x : Key → ℝ) : Integer.Sparse.eval row451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck451, Integer.Sparse.eval_collectBalanced, rawRowCheck451]

def rawRow452 : Integer.Sparse Key := [(key1771, -1), (key1771, -1), (key1778, 2), (key1787, 1), (key1787, 1), (key1815, -1), (key1815, -1), (key1796, -2), (key1823, 1), (key1823, 1), (key1336, 1), (key1336, 1), (key1343, -2), (key1454, -1), (key1454, -1), (key1657, 1), (key1657, 1), (key1464, 2), (key1665, -1), (key1665, -1), (key1295, -1), (key1295, -1), (key1324, 1), (key1324, 1), (key1390, 1), (key1390, 1), (key1554, -1), (key1554, -1), (key1442, -1), (key1442, -1), (key1591, 1), (key1591, 1), (key1291, 2), (key1311, -1), (key1311, -1), (key1386, -2), (key1541, 1), (key1541, 1), (key1419, 1), (key1419, 1), (key1568, -1), (key1568, -1)]

theorem rawRowCheck452 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow452 := by decide +kernel

def row452 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck452 : row452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow452 := by decide +kernel

theorem rowEval452 (x : Key → ℝ) : Integer.Sparse.eval row452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck452, Integer.Sparse.eval_collectBalanced, rawRowCheck452]

def rawRow453 : Integer.Sparse Key := [(key1771, -1), (key1778, -1), (key1771, 2), (key1812, 1), (key1815, 1), (key1787, -1), (key1812, -1), (key1823, -2), (key1796, 1), (key1823, 1), (key1336, 1), (key1343, 1), (key1336, -2), (key1654, -1), (key1657, -1), (key1454, 1), (key1654, 1), (key1665, 2), (key1464, -1), (key1665, -1), (key1315, -1), (key1324, -1), (key1295, 1), (key1315, 1), (key1545, 1), (key1554, 1), (key1390, -1), (key1545, -1), (key1591, -1), (key1631, -1), (key1442, 1), (key1631, 1), (key1311, 2), (key1291, -1), (key1311, -1), (key1541, -2), (key1386, 1), (key1541, 1), (key1568, 1), (key1617, 1), (key1419, -1), (key1617, -1)]

theorem rawRowCheck453 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow453 := by decide +kernel

def row453 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck453 : row453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow453 := by decide +kernel

theorem rowEval453 (x : Key → ℝ) : Integer.Sparse.eval row453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck453, Integer.Sparse.eval_collectBalanced, rawRowCheck453]

def rawRow454 : Integer.Sparse Key := [(key1778, -1), (key1771, -1), (key1771, 2), (key1815, 1), (key1812, 1), (key1812, -1), (key1787, -1), (key1823, -2), (key1823, 1), (key1796, 1), (key1343, 1), (key1336, 1), (key1336, -2), (key1657, -1), (key1654, -1), (key1654, 1), (key1454, 1), (key1665, 2), (key1665, -1), (key1464, -1), (key1324, -1), (key1315, -1), (key1315, 1), (key1295, 1), (key1554, 1), (key1545, 1), (key1545, -1), (key1390, -1), (key1631, -1), (key1591, -1), (key1631, 1), (key1442, 1), (key1311, 2), (key1311, -1), (key1291, -1), (key1541, -2), (key1541, 1), (key1386, 1), (key1617, 1), (key1568, 1), (key1617, -1), (key1419, -1)]

theorem rawRowCheck454 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow454 := by decide +kernel

def row454 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck454 : row454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow454 := by decide +kernel

theorem rowEval454 (x : Key → ℝ) : Integer.Sparse.eval row454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck454, Integer.Sparse.eval_collectBalanced, rawRowCheck454]

def rawRow455 : Integer.Sparse Key := [(key1787, -1), (key1787, -1), (key1796, 2), (key1771, 1), (key1771, 1), (key1823, -1), (key1823, -1), (key1778, -2), (key1815, 1), (key1815, 1), (key1454, 1), (key1454, 1), (key1464, -2), (key1336, -1), (key1336, -1), (key1665, 1), (key1665, 1), (key1343, 2), (key1657, -1), (key1657, -1), (key1390, -1), (key1390, -1), (key1442, 1), (key1442, 1), (key1295, 1), (key1295, 1), (key1591, -1), (key1591, -1), (key1324, -1), (key1324, -1), (key1554, 1), (key1554, 1), (key1386, 2), (key1419, -1), (key1419, -1), (key1291, -2), (key1568, 1), (key1568, 1), (key1311, 1), (key1311, 1), (key1541, -1), (key1541, -1)]

theorem rawRowCheck455 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow455 := by decide +kernel

def row455 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

theorem rowCheck455 : row455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow455 := by decide +kernel

theorem rowEval455 (x : Key → ℝ) : Integer.Sparse.eval row455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck455, Integer.Sparse.eval_collectBalanced, rawRowCheck455]

def rawRow456 : Integer.Sparse Key := [(key1787, -1), (key1796, -1), (key1787, 2), (key1812, 1), (key1823, 1), (key1771, -1), (key1812, -1), (key1815, -2), (key1778, 1), (key1815, 1), (key1454, 1), (key1464, 1), (key1454, -2), (key1654, -1), (key1665, -1), (key1336, 1), (key1654, 1), (key1657, 2), (key1343, -1), (key1657, -1), (key1423, -1), (key1442, -1), (key1390, 1), (key1423, 1), (key1572, 1), (key1591, 1), (key1295, -1), (key1572, -1), (key1554, -1), (key1622, -1), (key1324, 1), (key1622, 1), (key1419, 2), (key1386, -1), (key1419, -1), (key1568, -2), (key1291, 1), (key1568, 1), (key1541, 1), (key1617, 1), (key1311, -1), (key1617, -1)]

theorem rawRowCheck456 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow456 := by decide +kernel

def row456 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck456 : row456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow456 := by decide +kernel

theorem rowEval456 (x : Key → ℝ) : Integer.Sparse.eval row456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck456, Integer.Sparse.eval_collectBalanced, rawRowCheck456]

def rawRow457 : Integer.Sparse Key := [(key1796, -1), (key1787, -1), (key1787, 2), (key1823, 1), (key1812, 1), (key1812, -1), (key1771, -1), (key1815, -2), (key1815, 1), (key1778, 1), (key1464, 1), (key1454, 1), (key1454, -2), (key1665, -1), (key1654, -1), (key1654, 1), (key1336, 1), (key1657, 2), (key1657, -1), (key1343, -1), (key1442, -1), (key1423, -1), (key1423, 1), (key1390, 1), (key1591, 1), (key1572, 1), (key1572, -1), (key1295, -1), (key1622, -1), (key1554, -1), (key1622, 1), (key1324, 1), (key1419, 2), (key1419, -1), (key1386, -1), (key1568, -2), (key1568, 1), (key1291, 1), (key1617, 1), (key1541, 1), (key1617, -1), (key1311, -1)]

theorem rawRowCheck457 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow457 := by decide +kernel

def row457 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck457 : row457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow457 := by decide +kernel

theorem rowEval457 (x : Key → ℝ) : Integer.Sparse.eval row457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck457, Integer.Sparse.eval_collectBalanced, rawRowCheck457]

def rawRow458 : Integer.Sparse Key := [(key1812, -1), (key1815, -1), (key1823, 2), (key1771, 1), (key1778, 1), (key1796, -1), (key1823, -1), (key1771, -2), (key1787, 1), (key1812, 1), (key1654, 1), (key1657, 1), (key1665, -2), (key1336, -1), (key1343, -1), (key1464, 1), (key1665, 1), (key1336, 2), (key1454, -1), (key1654, -1), (key1545, -1), (key1554, -1), (key1591, 1), (key1631, 1), (key1315, 1), (key1324, 1), (key1442, -1), (key1631, -1), (key1295, -1), (key1315, -1), (key1390, 1), (key1545, 1), (key1541, 2), (key1568, -1), (key1617, -1), (key1311, -2), (key1419, 1), (key1617, 1), (key1291, 1), (key1311, 1), (key1386, -1), (key1541, -1)]

theorem rawRowCheck458 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form0 = rawRow458 := by decide +kernel

def row458 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck458 : row458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow458 := by decide +kernel

theorem rowEval458 (x : Key → ℝ) : Integer.Sparse.eval row458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck458, Integer.Sparse.eval_collectBalanced, rawRowCheck458]

def rawRow459 : Integer.Sparse Key := [(key1815, -1), (key1812, -1), (key1823, 2), (key1778, 1), (key1771, 1), (key1823, -1), (key1796, -1), (key1771, -2), (key1812, 1), (key1787, 1), (key1657, 1), (key1654, 1), (key1665, -2), (key1343, -1), (key1336, -1), (key1665, 1), (key1464, 1), (key1336, 2), (key1654, -1), (key1454, -1), (key1554, -1), (key1545, -1), (key1631, 1), (key1591, 1), (key1324, 1), (key1315, 1), (key1631, -1), (key1442, -1), (key1315, -1), (key1295, -1), (key1545, 1), (key1390, 1), (key1541, 2), (key1617, -1), (key1568, -1), (key1311, -2), (key1617, 1), (key1419, 1), (key1311, 1), (key1291, 1), (key1541, -1), (key1386, -1)]

theorem rawRowCheck459 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form0 = rawRow459 := by decide +kernel

def row459 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck459 : row459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow459 := by decide +kernel

theorem rowEval459 (x : Key → ℝ) : Integer.Sparse.eval row459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck459, Integer.Sparse.eval_collectBalanced, rawRowCheck459]

def rawRow460 : Integer.Sparse Key := [(key1812, -1), (key1823, -1), (key1815, 2), (key1787, 1), (key1796, 1), (key1778, -1), (key1815, -1), (key1787, -2), (key1771, 1), (key1812, 1), (key1654, 1), (key1665, 1), (key1657, -2), (key1454, -1), (key1464, -1), (key1343, 1), (key1657, 1), (key1454, 2), (key1336, -1), (key1654, -1), (key1572, -1), (key1591, -1), (key1554, 1), (key1622, 1), (key1423, 1), (key1442, 1), (key1324, -1), (key1622, -1), (key1390, -1), (key1423, -1), (key1295, 1), (key1572, 1), (key1568, 2), (key1541, -1), (key1617, -1), (key1419, -2), (key1311, 1), (key1617, 1), (key1386, 1), (key1419, 1), (key1291, -1), (key1568, -1)]

theorem rawRowCheck460 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form0 = rawRow460 := by decide +kernel

def row460 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck460 : row460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow460 := by decide +kernel

theorem rowEval460 (x : Key → ℝ) : Integer.Sparse.eval row460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck460, Integer.Sparse.eval_collectBalanced, rawRowCheck460]

def rawRow461 : Integer.Sparse Key := [(key1823, -1), (key1812, -1), (key1815, 2), (key1796, 1), (key1787, 1), (key1815, -1), (key1778, -1), (key1787, -2), (key1812, 1), (key1771, 1), (key1665, 1), (key1654, 1), (key1657, -2), (key1464, -1), (key1454, -1), (key1657, 1), (key1343, 1), (key1454, 2), (key1654, -1), (key1336, -1), (key1591, -1), (key1572, -1), (key1622, 1), (key1554, 1), (key1442, 1), (key1423, 1), (key1622, -1), (key1324, -1), (key1423, -1), (key1390, -1), (key1572, 1), (key1295, 1), (key1568, 2), (key1617, -1), (key1541, -1), (key1419, -2), (key1617, 1), (key1311, 1), (key1419, 1), (key1386, 1), (key1568, -1), (key1291, -1)]

theorem rawRowCheck461 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form0 = rawRow461 := by decide +kernel

def row461 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck461 : row461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow461 := by decide +kernel

theorem rowEval461 (x : Key → ℝ) : Integer.Sparse.eval row461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck461, Integer.Sparse.eval_collectBalanced, rawRowCheck461]

def rawRow462 : Integer.Sparse Key := [(key2616, -2), (key2616, 1), (key2619, 1), (key2632, 2), (key2632, -1), (key2649, -1), (key2640, -1), (key2642, -1), (key2640, 1), (key2654, 1), (key2671, 2), (key2671, -1), (key2674, -1), (key2786, -2), (key2786, 1), (key2939, 1), (key2794, 1), (key2796, 1), (key2794, -1), (key2944, -1), (key2706, -2), (key2706, 1), (key2738, 1), (key2809, 2), (key2809, -1), (key2951, -1), (key2860, -1), (key2898, -1), (key2860, 1), (key2977, 1), (key2726, 1), (key2729, 1), (key2726, -1), (key2748, -1), (key2829, -1), (key2832, -1), (key2829, 1), (key2961, 1), (key2870, 1), (key2905, 1), (key2870, -1), (key2984, -1)]

theorem rawRowCheck462 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form1 = rawRow462 := by decide +kernel

def row462 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck462 : row462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow462 := by decide +kernel

theorem rowEval462 (x : Key → ℝ) : Integer.Sparse.eval row462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck462, Integer.Sparse.eval_collectBalanced, rawRowCheck462]

def rawRow463 : Integer.Sparse Key := [(key2616, -2), (key2619, 1), (key2616, 1), (key2632, 2), (key2649, -1), (key2632, -1), (key2642, -1), (key2640, -1), (key2654, 1), (key2640, 1), (key2671, 2), (key2674, -1), (key2671, -1), (key2786, -2), (key2939, 1), (key2786, 1), (key2796, 1), (key2794, 1), (key2944, -1), (key2794, -1), (key2706, -2), (key2738, 1), (key2706, 1), (key2809, 2), (key2951, -1), (key2809, -1), (key2898, -1), (key2860, -1), (key2977, 1), (key2860, 1), (key2729, 1), (key2726, 1), (key2748, -1), (key2726, -1), (key2832, -1), (key2829, -1), (key2961, 1), (key2829, 1), (key2905, 1), (key2870, 1), (key2984, -1), (key2870, -1)]

theorem rawRowCheck463 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form1 = rawRow463 := by decide +kernel

def row463 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck463 : row463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow463 := by decide +kernel

theorem rowEval463 (x : Key → ℝ) : Integer.Sparse.eval row463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck463, Integer.Sparse.eval_collectBalanced, rawRowCheck463]

def rawRow464 : Integer.Sparse Key := [(key2619, -2), (key2616, 1), (key2616, 1), (key2649, 2), (key2632, -1), (key2632, -1), (key2654, -1), (key2654, -1), (key2642, 1), (key2642, 1), (key2674, 2), (key2671, -1), (key2671, -1), (key2939, -2), (key2786, 1), (key2786, 1), (key2944, 1), (key2944, 1), (key2796, -1), (key2796, -1), (key2738, -2), (key2706, 1), (key2706, 1), (key2951, 2), (key2809, -1), (key2809, -1), (key2977, -1), (key2977, -1), (key2898, 1), (key2898, 1), (key2748, 1), (key2748, 1), (key2729, -1), (key2729, -1), (key2961, -1), (key2961, -1), (key2832, 1), (key2832, 1), (key2984, 1), (key2984, 1), (key2905, -1), (key2905, -1)]

theorem rawRowCheck464 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form1 = rawRow464 := by decide +kernel

def row464 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck464 : row464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow464 := by decide +kernel

theorem rowEval464 (x : Key → ℝ) : Integer.Sparse.eval row464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck464, Integer.Sparse.eval_collectBalanced, rawRowCheck464]

def rawRow465 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2642, 1), (key2616, 2), (key2640, -1), (key2654, -1), (key2616, -1), (key2619, -1), (key2632, 1), (key2649, 1), (key2786, 2), (key2794, -1), (key2796, -1), (key2671, -2), (key2794, 1), (key2944, 1), (key2671, 1), (key2674, 1), (key2786, -1), (key2939, -1), (key2809, -2), (key2860, 1), (key2898, 1), (key2706, 2), (key2860, -1), (key2977, -1), (key2706, -1), (key2738, -1), (key2809, 1), (key2951, 1), (key2829, 1), (key2832, 1), (key2870, -1), (key2905, -1), (key2726, -1), (key2729, -1), (key2870, 1), (key2984, 1), (key2726, 1), (key2748, 1), (key2829, -1), (key2961, -1)]

theorem rawRowCheck465 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form1 = rawRow465 := by decide +kernel

def row465 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck465 : row465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow465 := by decide +kernel

theorem rowEval465 (x : Key → ℝ) : Integer.Sparse.eval row465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck465, Integer.Sparse.eval_collectBalanced, rawRowCheck465]

def rawRow466 : Integer.Sparse Key := [(key2632, -2), (key2642, 1), (key2640, 1), (key2616, 2), (key2654, -1), (key2640, -1), (key2619, -1), (key2616, -1), (key2649, 1), (key2632, 1), (key2786, 2), (key2796, -1), (key2794, -1), (key2671, -2), (key2944, 1), (key2794, 1), (key2674, 1), (key2671, 1), (key2939, -1), (key2786, -1), (key2809, -2), (key2898, 1), (key2860, 1), (key2706, 2), (key2977, -1), (key2860, -1), (key2738, -1), (key2706, -1), (key2951, 1), (key2809, 1), (key2832, 1), (key2829, 1), (key2905, -1), (key2870, -1), (key2729, -1), (key2726, -1), (key2984, 1), (key2870, 1), (key2748, 1), (key2726, 1), (key2961, -1), (key2829, -1)]

theorem rawRowCheck466 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form1 = rawRow466 := by decide +kernel

def row466 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck466 : row466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow466 := by decide +kernel

theorem rowEval466 (x : Key → ℝ) : Integer.Sparse.eval row466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck466, Integer.Sparse.eval_collectBalanced, rawRowCheck466]

def rawRow467 : Integer.Sparse Key := [(key2642, -2), (key2632, 1), (key2640, 1), (key2654, 2), (key2616, -1), (key2640, -1), (key2649, -1), (key2654, -1), (key2619, 1), (key2642, 1), (key2796, 2), (key2786, -1), (key2794, -1), (key2944, -2), (key2671, 1), (key2794, 1), (key2939, 1), (key2944, 1), (key2674, -1), (key2796, -1), (key2898, -2), (key2809, 1), (key2860, 1), (key2977, 2), (key2706, -1), (key2860, -1), (key2951, -1), (key2977, -1), (key2738, 1), (key2898, 1), (key2905, 1), (key2913, 1), (key2832, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2729, 1), (key2883, 1), (key2961, 1), (key2992, 1), (key2748, -1), (key2913, -1)]

theorem rawRowCheck467 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form1 = rawRow467 := by decide +kernel

def row467 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck467 : row467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow467 := by decide +kernel

theorem rowEval467 (x : Key → ℝ) : Integer.Sparse.eval row467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck467, Integer.Sparse.eval_collectBalanced, rawRowCheck467]

def rawRow468 : Integer.Sparse Key := [(key2642, -2), (key2640, 1), (key2632, 1), (key2654, 2), (key2640, -1), (key2616, -1), (key2654, -1), (key2649, -1), (key2642, 1), (key2619, 1), (key2796, 2), (key2794, -1), (key2786, -1), (key2944, -2), (key2794, 1), (key2671, 1), (key2944, 1), (key2939, 1), (key2796, -1), (key2674, -1), (key2898, -2), (key2860, 1), (key2809, 1), (key2977, 2), (key2860, -1), (key2706, -1), (key2977, -1), (key2951, -1), (key2898, 1), (key2738, 1), (key2913, 1), (key2905, 1), (key2883, -1), (key2832, -1), (key2992, -1), (key2984, -1), (key2883, 1), (key2729, 1), (key2992, 1), (key2961, 1), (key2913, -1), (key2748, -1)]

theorem rawRowCheck468 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form1 = rawRow468 := by decide +kernel

def row468 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck468 : row468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow468 := by decide +kernel

theorem rowEval468 (x : Key → ℝ) : Integer.Sparse.eval row468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck468, Integer.Sparse.eval_collectBalanced, rawRowCheck468]

def rawRow469 : Integer.Sparse Key := [(key2649, -2), (key2654, 1), (key2654, 1), (key2619, 2), (key2642, -1), (key2642, -1), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2939, 2), (key2944, -1), (key2944, -1), (key2674, -2), (key2796, 1), (key2796, 1), (key2671, 1), (key2671, 1), (key2786, -1), (key2786, -1), (key2951, -2), (key2977, 1), (key2977, 1), (key2738, 2), (key2898, -1), (key2898, -1), (key2706, -1), (key2706, -1), (key2809, 1), (key2809, 1), (key2961, 1), (key2961, 1), (key2984, -1), (key2984, -1), (key2748, -1), (key2748, -1), (key2905, 1), (key2905, 1), (key2729, 1), (key2729, 1), (key2832, -1), (key2832, -1)]

theorem rawRowCheck469 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form1 = rawRow469 := by decide +kernel

def row469 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck469 : row469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow469 := by decide +kernel

theorem rowEval469 (x : Key → ℝ) : Integer.Sparse.eval row469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck469, Integer.Sparse.eval_collectBalanced, rawRowCheck469]

def rawRow470 : Integer.Sparse Key := [(key2654, -2), (key2649, 1), (key2654, 1), (key2642, 2), (key2619, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2944, 2), (key2939, -1), (key2944, -1), (key2796, -2), (key2674, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2671, -1), (key2794, -1), (key2977, -2), (key2951, 1), (key2977, 1), (key2898, 2), (key2738, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2706, 1), (key2860, 1), (key2984, 1), (key2992, 1), (key2961, -1), (key2992, -1), (key2905, -1), (key2913, -1), (key2748, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2729, -1), (key2883, -1)]

theorem rawRowCheck470 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form1 = rawRow470 := by decide +kernel

def row470 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck470 : row470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow470 := by decide +kernel

theorem rowEval470 (x : Key → ℝ) : Integer.Sparse.eval row470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck470, Integer.Sparse.eval_collectBalanced, rawRowCheck470]

def rawRow471 : Integer.Sparse Key := [(key2654, -2), (key2654, 1), (key2649, 1), (key2642, 2), (key2642, -1), (key2619, -1), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2944, 2), (key2944, -1), (key2939, -1), (key2796, -2), (key2796, 1), (key2674, 1), (key2794, 1), (key2786, 1), (key2794, -1), (key2671, -1), (key2977, -2), (key2977, 1), (key2951, 1), (key2898, 2), (key2898, -1), (key2738, -1), (key2860, -1), (key2809, -1), (key2860, 1), (key2706, 1), (key2992, 1), (key2984, 1), (key2992, -1), (key2961, -1), (key2913, -1), (key2905, -1), (key2913, 1), (key2748, 1), (key2883, 1), (key2832, 1), (key2883, -1), (key2729, -1)]

theorem rawRowCheck471 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form1 = rawRow471 := by decide +kernel

def row471 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck471 : row471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow471 := by decide +kernel

theorem rowEval471 (x : Key → ℝ) : Integer.Sparse.eval row471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck471, Integer.Sparse.eval_collectBalanced, rawRowCheck471]

def rawRow472 : Integer.Sparse Key := [(key2671, -2), (key2671, 1), (key2674, 1), (key2706, 2), (key2706, -1), (key2738, -1), (key2726, -1), (key2729, -1), (key2726, 1), (key2748, 1), (key2616, 2), (key2616, -1), (key2619, -1), (key2809, -2), (key2809, 1), (key2951, 1), (key2829, 1), (key2832, 1), (key2829, -1), (key2961, -1), (key2632, -2), (key2632, 1), (key2649, 1), (key2786, 2), (key2786, -1), (key2939, -1), (key2870, -1), (key2905, -1), (key2870, 1), (key2984, 1), (key2640, 1), (key2642, 1), (key2640, -1), (key2654, -1), (key2794, -1), (key2796, -1), (key2794, 1), (key2944, 1), (key2860, 1), (key2898, 1), (key2860, -1), (key2977, -1)]

theorem rawRowCheck472 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form1 = rawRow472 := by decide +kernel

def row472 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck472 : row472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow472 := by decide +kernel

theorem rowEval472 (x : Key → ℝ) : Integer.Sparse.eval row472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck472, Integer.Sparse.eval_collectBalanced, rawRowCheck472]

def rawRow473 : Integer.Sparse Key := [(key2671, -2), (key2674, 1), (key2671, 1), (key2706, 2), (key2738, -1), (key2706, -1), (key2729, -1), (key2726, -1), (key2748, 1), (key2726, 1), (key2616, 2), (key2619, -1), (key2616, -1), (key2809, -2), (key2951, 1), (key2809, 1), (key2832, 1), (key2829, 1), (key2961, -1), (key2829, -1), (key2632, -2), (key2649, 1), (key2632, 1), (key2786, 2), (key2939, -1), (key2786, -1), (key2905, -1), (key2870, -1), (key2984, 1), (key2870, 1), (key2642, 1), (key2640, 1), (key2654, -1), (key2640, -1), (key2796, -1), (key2794, -1), (key2944, 1), (key2794, 1), (key2898, 1), (key2860, 1), (key2977, -1), (key2860, -1)]

theorem rawRowCheck473 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form1 = rawRow473 := by decide +kernel

def row473 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck473 : row473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow473 := by decide +kernel

theorem rowEval473 (x : Key → ℝ) : Integer.Sparse.eval row473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck473, Integer.Sparse.eval_collectBalanced, rawRowCheck473]

def rawRow474 : Integer.Sparse Key := [(key2674, -2), (key2671, 1), (key2671, 1), (key2738, 2), (key2706, -1), (key2706, -1), (key2748, -1), (key2748, -1), (key2729, 1), (key2729, 1), (key2619, 2), (key2616, -1), (key2616, -1), (key2951, -2), (key2809, 1), (key2809, 1), (key2961, 1), (key2961, 1), (key2832, -1), (key2832, -1), (key2649, -2), (key2632, 1), (key2632, 1), (key2939, 2), (key2786, -1), (key2786, -1), (key2984, -1), (key2984, -1), (key2905, 1), (key2905, 1), (key2654, 1), (key2654, 1), (key2642, -1), (key2642, -1), (key2944, -1), (key2944, -1), (key2796, 1), (key2796, 1), (key2977, 1), (key2977, 1), (key2898, -1), (key2898, -1)]

theorem rawRowCheck474 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form1 = rawRow474 := by decide +kernel

def row474 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2832, -2), (key2898, -2), (key2905, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck474 : row474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow474 := by decide +kernel

theorem rowEval474 (x : Key → ℝ) : Integer.Sparse.eval row474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck474, Integer.Sparse.eval_collectBalanced, rawRowCheck474]

def rawRow475 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2729, 1), (key2671, 2), (key2726, -1), (key2748, -1), (key2671, -1), (key2674, -1), (key2706, 1), (key2738, 1), (key2809, 2), (key2829, -1), (key2832, -1), (key2616, -2), (key2829, 1), (key2961, 1), (key2616, 1), (key2619, 1), (key2809, -1), (key2951, -1), (key2786, -2), (key2870, 1), (key2905, 1), (key2632, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2649, -1), (key2786, 1), (key2939, 1), (key2794, 1), (key2796, 1), (key2860, -1), (key2898, -1), (key2640, -1), (key2642, -1), (key2860, 1), (key2977, 1), (key2640, 1), (key2654, 1), (key2794, -1), (key2944, -1)]

theorem rawRowCheck475 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form1 = rawRow475 := by decide +kernel

def row475 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck475 : row475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow475 := by decide +kernel

theorem rowEval475 (x : Key → ℝ) : Integer.Sparse.eval row475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck475, Integer.Sparse.eval_collectBalanced, rawRowCheck475]

def rawRow476 : Integer.Sparse Key := [(key2706, -2), (key2729, 1), (key2726, 1), (key2671, 2), (key2748, -1), (key2726, -1), (key2674, -1), (key2671, -1), (key2738, 1), (key2706, 1), (key2809, 2), (key2832, -1), (key2829, -1), (key2616, -2), (key2961, 1), (key2829, 1), (key2619, 1), (key2616, 1), (key2951, -1), (key2809, -1), (key2786, -2), (key2905, 1), (key2870, 1), (key2632, 2), (key2984, -1), (key2870, -1), (key2649, -1), (key2632, -1), (key2939, 1), (key2786, 1), (key2796, 1), (key2794, 1), (key2898, -1), (key2860, -1), (key2642, -1), (key2640, -1), (key2977, 1), (key2860, 1), (key2654, 1), (key2640, 1), (key2944, -1), (key2794, -1)]

theorem rawRowCheck476 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form1 = rawRow476 := by decide +kernel

def row476 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2796, 1), (key2809, 1), (key2832, -1), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck476 : row476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow476 := by decide +kernel

theorem rowEval476 (x : Key → ℝ) : Integer.Sparse.eval row476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck476, Integer.Sparse.eval_collectBalanced, rawRowCheck476]

def rawRow477 : Integer.Sparse Key := [(key2729, -2), (key2706, 1), (key2726, 1), (key2748, 2), (key2671, -1), (key2726, -1), (key2738, -1), (key2748, -1), (key2674, 1), (key2729, 1), (key2832, 2), (key2809, -1), (key2829, -1), (key2961, -2), (key2616, 1), (key2829, 1), (key2951, 1), (key2961, 1), (key2619, -1), (key2832, -1), (key2905, -2), (key2786, 1), (key2870, 1), (key2984, 2), (key2632, -1), (key2870, -1), (key2939, -1), (key2984, -1), (key2649, 1), (key2905, 1), (key2898, 1), (key2913, 1), (key2796, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2642, 1), (key2883, 1), (key2944, 1), (key2992, 1), (key2654, -1), (key2913, -1)]

theorem rawRowCheck477 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form1 = rawRow477 := by decide +kernel

def row477 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck477 : row477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow477 := by decide +kernel

theorem rowEval477 (x : Key → ℝ) : Integer.Sparse.eval row477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck477, Integer.Sparse.eval_collectBalanced, rawRowCheck477]

def rawRow478 : Integer.Sparse Key := [(key2729, -2), (key2726, 1), (key2706, 1), (key2748, 2), (key2726, -1), (key2671, -1), (key2748, -1), (key2738, -1), (key2729, 1), (key2674, 1), (key2832, 2), (key2829, -1), (key2809, -1), (key2961, -2), (key2829, 1), (key2616, 1), (key2961, 1), (key2951, 1), (key2832, -1), (key2619, -1), (key2905, -2), (key2870, 1), (key2786, 1), (key2984, 2), (key2870, -1), (key2632, -1), (key2984, -1), (key2939, -1), (key2905, 1), (key2649, 1), (key2913, 1), (key2898, 1), (key2883, -1), (key2796, -1), (key2992, -1), (key2977, -1), (key2883, 1), (key2642, 1), (key2992, 1), (key2944, 1), (key2913, -1), (key2654, -1)]

theorem rawRowCheck478 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form1 = rawRow478 := by decide +kernel

def row478 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2796, -1), (key2809, -1), (key2832, 1), (key2898, 1), (key2905, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck478 : row478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow478 := by decide +kernel

theorem rowEval478 (x : Key → ℝ) : Integer.Sparse.eval row478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck478, Integer.Sparse.eval_collectBalanced, rawRowCheck478]

def rawRow479 : Integer.Sparse Key := [(key2738, -2), (key2748, 1), (key2748, 1), (key2674, 2), (key2729, -1), (key2729, -1), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key2951, 2), (key2961, -1), (key2961, -1), (key2619, -2), (key2832, 1), (key2832, 1), (key2616, 1), (key2616, 1), (key2809, -1), (key2809, -1), (key2939, -2), (key2984, 1), (key2984, 1), (key2649, 2), (key2905, -1), (key2905, -1), (key2632, -1), (key2632, -1), (key2786, 1), (key2786, 1), (key2944, 1), (key2944, 1), (key2977, -1), (key2977, -1), (key2654, -1), (key2654, -1), (key2898, 1), (key2898, 1), (key2642, 1), (key2642, 1), (key2796, -1), (key2796, -1)]

theorem rawRowCheck479 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form1 = rawRow479 := by decide +kernel

def row479 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2832, 2), (key2898, 2), (key2905, -2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck479 : row479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow479 := by decide +kernel

theorem rowEval479 (x : Key → ℝ) : Integer.Sparse.eval row479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck479, Integer.Sparse.eval_collectBalanced, rawRowCheck479]

end MUB6.Certificate.GramRows

end OAI
