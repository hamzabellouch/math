import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow128 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1292, 2), (key1351, 1), (key1351, 1), (key1312, -1), (key1312, -1), (key1354, -2), (key1326, 1), (key1326, 1), (key1393, 1), (key1393, 1), (key1387, -2), (key1896, -1), (key1896, -1), (key1542, 1), (key1542, 1), (key1899, 2), (key1556, -1), (key1556, -1), (key1472, -1), (key1472, -1), (key1420, 1), (key1420, 1), (key1903, 1), (key1903, 1), (key1569, -1), (key1569, -1), (key1920, -1), (key1920, -1), (key1683, 1), (key1683, 1), (key1480, 2), (key1444, -1), (key1444, -1), (key1911, -2), (key1593, 1), (key1593, 1), (key1926, 1), (key1926, 1), (key1689, -1), (key1689, -1)]

theorem rawRowCheck128 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form0 = rawRow128 := by decide +kernel

def row128 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1387, -2), (key1393, 2), (key1420, 2), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, 2), (key1556, -2), (key1569, -2), (key1593, 2), (key1683, 2), (key1689, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck128 : row128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow128 := by decide +kernel

theorem rowEval128 (x : Key → ℝ) : Integer.Sparse.eval row128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck128, Integer.Sparse.eval_collectBalanced, rawRowCheck128]

def rawRow129 : Integer.Sparse Key := [(key1312, -1), (key1318, -1), (key1326, 2), (key1292, 1), (key1298, 1), (key1326, -1), (key1354, -1), (key1298, -2), (key1318, 1), (key1351, 1), (key1542, 1), (key1548, 1), (key1556, -2), (key1387, -1), (key1393, -1), (key1556, 1), (key1899, 1), (key1393, 2), (key1548, -1), (key1896, -1), (key1569, -1), (key1575, -1), (key1624, 1), (key1683, 1), (key1420, 1), (key1426, 1), (key1624, -1), (key1920, -1), (key1426, -1), (key1472, -1), (key1575, 1), (key1903, 1), (key1593, 2), (key1633, -1), (key1689, -1), (key1444, -2), (key1633, 1), (key1926, 1), (key1444, 1), (key1480, 1), (key1593, -1), (key1911, -1)]

theorem rawRowCheck129 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form0 = rawRow129 := by decide +kernel

def row129 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck129 : row129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow129 := by decide +kernel

theorem rowEval129 (x : Key → ℝ) : Integer.Sparse.eval row129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck129, Integer.Sparse.eval_collectBalanced, rawRowCheck129]

def rawRow130 : Integer.Sparse Key := [(key1318, -1), (key1312, -1), (key1326, 2), (key1298, 1), (key1292, 1), (key1354, -1), (key1326, -1), (key1298, -2), (key1351, 1), (key1318, 1), (key1548, 1), (key1542, 1), (key1556, -2), (key1393, -1), (key1387, -1), (key1899, 1), (key1556, 1), (key1393, 2), (key1896, -1), (key1548, -1), (key1575, -1), (key1569, -1), (key1683, 1), (key1624, 1), (key1426, 1), (key1420, 1), (key1920, -1), (key1624, -1), (key1472, -1), (key1426, -1), (key1903, 1), (key1575, 1), (key1593, 2), (key1689, -1), (key1633, -1), (key1444, -2), (key1926, 1), (key1633, 1), (key1480, 1), (key1444, 1), (key1911, -1), (key1593, -1)]

theorem rawRowCheck130 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form0 = rawRow130 := by decide +kernel

def row130 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck130 : row130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow130 := by decide +kernel

theorem rowEval130 (x : Key → ℝ) : Integer.Sparse.eval row130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck130, Integer.Sparse.eval_collectBalanced, rawRowCheck130]

def rawRow131 : Integer.Sparse Key := [(key1318, -1), (key1326, -1), (key1312, 2), (key1351, 1), (key1354, 1), (key1292, -1), (key1312, -1), (key1351, -2), (key1298, 1), (key1318, 1), (key1548, 1), (key1556, 1), (key1542, -2), (key1896, -1), (key1899, -1), (key1387, 1), (key1542, 1), (key1896, 2), (key1393, -1), (key1548, -1), (key1681, -1), (key1683, -1), (key1569, 1), (key1618, 1), (key1918, 1), (key1920, 1), (key1420, -1), (key1618, -1), (key1903, -1), (key1918, -1), (key1472, 1), (key1681, 1), (key1689, 2), (key1593, -1), (key1633, -1), (key1926, -2), (key1444, 1), (key1633, 1), (key1911, 1), (key1926, 1), (key1480, -1), (key1689, -1)]

theorem rawRowCheck131 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form0 = rawRow131 := by decide +kernel

def row131 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck131 : row131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow131 := by decide +kernel

theorem rowEval131 (x : Key → ℝ) : Integer.Sparse.eval row131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck131, Integer.Sparse.eval_collectBalanced, rawRowCheck131]

def rawRow132 : Integer.Sparse Key := [(key1326, -1), (key1318, -1), (key1312, 2), (key1354, 1), (key1351, 1), (key1312, -1), (key1292, -1), (key1351, -2), (key1318, 1), (key1298, 1), (key1556, 1), (key1548, 1), (key1542, -2), (key1899, -1), (key1896, -1), (key1542, 1), (key1387, 1), (key1896, 2), (key1548, -1), (key1393, -1), (key1683, -1), (key1681, -1), (key1618, 1), (key1569, 1), (key1920, 1), (key1918, 1), (key1618, -1), (key1420, -1), (key1918, -1), (key1903, -1), (key1681, 1), (key1472, 1), (key1689, 2), (key1633, -1), (key1593, -1), (key1926, -2), (key1633, 1), (key1444, 1), (key1926, 1), (key1911, 1), (key1689, -1), (key1480, -1)]

theorem rawRowCheck132 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form0 = rawRow132 := by decide +kernel

def row132 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck132 : row132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow132 := by decide +kernel

theorem rowEval132 (x : Key → ℝ) : Integer.Sparse.eval row132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck132, Integer.Sparse.eval_collectBalanced, rawRowCheck132]

def rawRow133 : Integer.Sparse Key := [(key1351, -1), (key1351, -1), (key1354, 2), (key1298, 1), (key1298, 1), (key1326, -1), (key1326, -1), (key1292, -2), (key1312, 1), (key1312, 1), (key1896, 1), (key1896, 1), (key1899, -2), (key1393, -1), (key1393, -1), (key1556, 1), (key1556, 1), (key1387, 2), (key1542, -1), (key1542, -1), (key1903, -1), (key1903, -1), (key1920, 1), (key1920, 1), (key1472, 1), (key1472, 1), (key1683, -1), (key1683, -1), (key1420, -1), (key1420, -1), (key1569, 1), (key1569, 1), (key1911, 2), (key1926, -1), (key1926, -1), (key1480, -2), (key1689, 1), (key1689, 1), (key1444, 1), (key1444, 1), (key1593, -1), (key1593, -1)]

theorem rawRowCheck133 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow133 := by decide +kernel

def row133 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, 2), (key1393, -2), (key1420, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, -2), (key1556, 2), (key1569, 2), (key1593, -2), (key1683, -2), (key1689, 2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

theorem rowCheck133 : row133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow133 := by decide +kernel

theorem rowEval133 (x : Key → ℝ) : Integer.Sparse.eval row133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck133, Integer.Sparse.eval_collectBalanced, rawRowCheck133]

def rawRow134 : Integer.Sparse Key := [(key1351, -1), (key1354, -1), (key1351, 2), (key1318, 1), (key1326, 1), (key1298, -1), (key1318, -1), (key1312, -2), (key1292, 1), (key1312, 1), (key1896, 1), (key1899, 1), (key1896, -2), (key1548, -1), (key1556, -1), (key1393, 1), (key1548, 1), (key1542, 2), (key1387, -1), (key1542, -1), (key1918, -1), (key1920, -1), (key1903, 1), (key1918, 1), (key1681, 1), (key1683, 1), (key1472, -1), (key1681, -1), (key1569, -1), (key1618, -1), (key1420, 1), (key1618, 1), (key1926, 2), (key1911, -1), (key1926, -1), (key1689, -2), (key1480, 1), (key1689, 1), (key1593, 1), (key1633, 1), (key1444, -1), (key1633, -1)]

theorem rawRowCheck134 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow134 := by decide +kernel

def row134 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck134 : row134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow134 := by decide +kernel

theorem rowEval134 (x : Key → ℝ) : Integer.Sparse.eval row134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck134, Integer.Sparse.eval_collectBalanced, rawRowCheck134]

def rawRow135 : Integer.Sparse Key := [(key1354, -1), (key1351, -1), (key1351, 2), (key1326, 1), (key1318, 1), (key1318, -1), (key1298, -1), (key1312, -2), (key1312, 1), (key1292, 1), (key1899, 1), (key1896, 1), (key1896, -2), (key1556, -1), (key1548, -1), (key1548, 1), (key1393, 1), (key1542, 2), (key1542, -1), (key1387, -1), (key1920, -1), (key1918, -1), (key1918, 1), (key1903, 1), (key1683, 1), (key1681, 1), (key1681, -1), (key1472, -1), (key1618, -1), (key1569, -1), (key1618, 1), (key1420, 1), (key1926, 2), (key1926, -1), (key1911, -1), (key1689, -2), (key1689, 1), (key1480, 1), (key1633, 1), (key1593, 1), (key1633, -1), (key1444, -1)]

theorem rawRowCheck135 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow135 := by decide +kernel

def row135 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck135 : row135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow135 := by decide +kernel

theorem rowEval135 (x : Key → ℝ) : Integer.Sparse.eval row135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck135, Integer.Sparse.eval_collectBalanced, rawRowCheck135]

def rawRow136 : Integer.Sparse Key := [(key1387, -1), (key1393, -1), (key1393, 2), (key1420, 1), (key1426, 1), (key1426, -1), (key1472, -1), (key1444, -2), (key1444, 1), (key1480, 1), (key1292, 1), (key1298, 1), (key1298, -2), (key1569, -1), (key1575, -1), (key1575, 1), (key1903, 1), (key1593, 2), (key1593, -1), (key1911, -1), (key1312, -1), (key1318, -1), (key1318, 1), (key1351, 1), (key1542, 1), (key1548, 1), (key1548, -1), (key1896, -1), (key1633, -1), (key1689, -1), (key1633, 1), (key1926, 1), (key1326, 2), (key1326, -1), (key1354, -1), (key1556, -2), (key1556, 1), (key1899, 1), (key1624, 1), (key1683, 1), (key1624, -1), (key1920, -1)]

theorem rawRowCheck136 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form0 = rawRow136 := by decide +kernel

def row136 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck136 : row136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow136 := by decide +kernel

theorem rowEval136 (x : Key → ℝ) : Integer.Sparse.eval row136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck136, Integer.Sparse.eval_collectBalanced, rawRowCheck136]

def rawRow137 : Integer.Sparse Key := [(key1393, -1), (key1387, -1), (key1393, 2), (key1426, 1), (key1420, 1), (key1472, -1), (key1426, -1), (key1444, -2), (key1480, 1), (key1444, 1), (key1298, 1), (key1292, 1), (key1298, -2), (key1575, -1), (key1569, -1), (key1903, 1), (key1575, 1), (key1593, 2), (key1911, -1), (key1593, -1), (key1318, -1), (key1312, -1), (key1351, 1), (key1318, 1), (key1548, 1), (key1542, 1), (key1896, -1), (key1548, -1), (key1689, -1), (key1633, -1), (key1926, 1), (key1633, 1), (key1326, 2), (key1354, -1), (key1326, -1), (key1556, -2), (key1899, 1), (key1556, 1), (key1683, 1), (key1624, 1), (key1920, -1), (key1624, -1)]

theorem rawRowCheck137 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form0 = rawRow137 := by decide +kernel

def row137 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck137 : row137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow137 := by decide +kernel

theorem rowEval137 (x : Key → ℝ) : Integer.Sparse.eval row137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck137, Integer.Sparse.eval_collectBalanced, rawRowCheck137]

def rawRow138 : Integer.Sparse Key := [(key1393, -1), (key1393, -1), (key1387, 2), (key1472, 1), (key1472, 1), (key1420, -1), (key1420, -1), (key1480, -2), (key1444, 1), (key1444, 1), (key1298, 1), (key1298, 1), (key1292, -2), (key1903, -1), (key1903, -1), (key1569, 1), (key1569, 1), (key1911, 2), (key1593, -1), (key1593, -1), (key1351, -1), (key1351, -1), (key1312, 1), (key1312, 1), (key1896, 1), (key1896, 1), (key1542, -1), (key1542, -1), (key1926, -1), (key1926, -1), (key1689, 1), (key1689, 1), (key1354, 2), (key1326, -1), (key1326, -1), (key1899, -2), (key1556, 1), (key1556, 1), (key1920, 1), (key1920, 1), (key1683, -1), (key1683, -1)]

theorem rawRowCheck138 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form0 = rawRow138 := by decide +kernel

def row138 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, 2), (key1393, -2), (key1420, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, -2), (key1556, 2), (key1569, 2), (key1593, -2), (key1683, -2), (key1689, 2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

theorem rowCheck138 : row138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow138 := by decide +kernel

theorem rowEval138 (x : Key → ℝ) : Integer.Sparse.eval row138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck138, Integer.Sparse.eval_collectBalanced, rawRowCheck138]

def rawRow139 : Integer.Sparse Key := [(key1420, -1), (key1426, -1), (key1444, 2), (key1387, 1), (key1393, 1), (key1444, -1), (key1480, -1), (key1393, -2), (key1426, 1), (key1472, 1), (key1569, 1), (key1575, 1), (key1593, -2), (key1292, -1), (key1298, -1), (key1593, 1), (key1911, 1), (key1298, 2), (key1575, -1), (key1903, -1), (key1542, -1), (key1548, -1), (key1633, 1), (key1689, 1), (key1312, 1), (key1318, 1), (key1633, -1), (key1926, -1), (key1318, -1), (key1351, -1), (key1548, 1), (key1896, 1), (key1556, 2), (key1624, -1), (key1683, -1), (key1326, -2), (key1624, 1), (key1920, 1), (key1326, 1), (key1354, 1), (key1556, -1), (key1899, -1)]

theorem rawRowCheck139 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form0 = rawRow139 := by decide +kernel

def row139 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck139 : row139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow139 := by decide +kernel

theorem rowEval139 (x : Key → ℝ) : Integer.Sparse.eval row139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck139, Integer.Sparse.eval_collectBalanced, rawRowCheck139]

def rawRow140 : Integer.Sparse Key := [(key1426, -1), (key1420, -1), (key1444, 2), (key1393, 1), (key1387, 1), (key1480, -1), (key1444, -1), (key1393, -2), (key1472, 1), (key1426, 1), (key1575, 1), (key1569, 1), (key1593, -2), (key1298, -1), (key1292, -1), (key1911, 1), (key1593, 1), (key1298, 2), (key1903, -1), (key1575, -1), (key1548, -1), (key1542, -1), (key1689, 1), (key1633, 1), (key1318, 1), (key1312, 1), (key1926, -1), (key1633, -1), (key1351, -1), (key1318, -1), (key1896, 1), (key1548, 1), (key1556, 2), (key1683, -1), (key1624, -1), (key1326, -2), (key1920, 1), (key1624, 1), (key1354, 1), (key1326, 1), (key1899, -1), (key1556, -1)]

theorem rawRowCheck140 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form0 = rawRow140 := by decide +kernel

def row140 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck140 : row140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow140 := by decide +kernel

theorem rowEval140 (x : Key → ℝ) : Integer.Sparse.eval row140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck140, Integer.Sparse.eval_collectBalanced, rawRowCheck140]

def rawRow141 : Integer.Sparse Key := [(key1426, -1), (key1444, -1), (key1420, 2), (key1472, 1), (key1480, 1), (key1387, -1), (key1420, -1), (key1472, -2), (key1393, 1), (key1426, 1), (key1575, 1), (key1593, 1), (key1569, -2), (key1903, -1), (key1911, -1), (key1292, 1), (key1569, 1), (key1903, 2), (key1298, -1), (key1575, -1), (key1681, -1), (key1689, -1), (key1542, 1), (key1618, 1), (key1918, 1), (key1926, 1), (key1312, -1), (key1618, -1), (key1896, -1), (key1918, -1), (key1351, 1), (key1681, 1), (key1683, 2), (key1556, -1), (key1624, -1), (key1920, -2), (key1326, 1), (key1624, 1), (key1899, 1), (key1920, 1), (key1354, -1), (key1683, -1)]

theorem rawRowCheck141 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form0 = rawRow141 := by decide +kernel

def row141 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck141 : row141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow141 := by decide +kernel

theorem rowEval141 (x : Key → ℝ) : Integer.Sparse.eval row141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck141, Integer.Sparse.eval_collectBalanced, rawRowCheck141]

def rawRow142 : Integer.Sparse Key := [(key1444, -1), (key1426, -1), (key1420, 2), (key1480, 1), (key1472, 1), (key1420, -1), (key1387, -1), (key1472, -2), (key1426, 1), (key1393, 1), (key1593, 1), (key1575, 1), (key1569, -2), (key1911, -1), (key1903, -1), (key1569, 1), (key1292, 1), (key1903, 2), (key1575, -1), (key1298, -1), (key1689, -1), (key1681, -1), (key1618, 1), (key1542, 1), (key1926, 1), (key1918, 1), (key1618, -1), (key1312, -1), (key1918, -1), (key1896, -1), (key1681, 1), (key1351, 1), (key1683, 2), (key1624, -1), (key1556, -1), (key1920, -2), (key1624, 1), (key1326, 1), (key1920, 1), (key1899, 1), (key1683, -1), (key1354, -1)]

theorem rawRowCheck142 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form0 = rawRow142 := by decide +kernel

def row142 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck142 : row142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow142 := by decide +kernel

theorem rowEval142 (x : Key → ℝ) : Integer.Sparse.eval row142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck142, Integer.Sparse.eval_collectBalanced, rawRowCheck142]

def rawRow143 : Integer.Sparse Key := [(key1472, -1), (key1472, -1), (key1480, 2), (key1393, 1), (key1393, 1), (key1444, -1), (key1444, -1), (key1387, -2), (key1420, 1), (key1420, 1), (key1903, 1), (key1903, 1), (key1911, -2), (key1298, -1), (key1298, -1), (key1593, 1), (key1593, 1), (key1292, 2), (key1569, -1), (key1569, -1), (key1896, -1), (key1896, -1), (key1926, 1), (key1926, 1), (key1351, 1), (key1351, 1), (key1689, -1), (key1689, -1), (key1312, -1), (key1312, -1), (key1542, 1), (key1542, 1), (key1899, 2), (key1920, -1), (key1920, -1), (key1354, -2), (key1683, 1), (key1683, 1), (key1326, 1), (key1326, 1), (key1556, -1), (key1556, -1)]

theorem rawRowCheck143 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form0 = rawRow143 := by decide +kernel

def row143 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1387, -2), (key1393, 2), (key1420, 2), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, 2), (key1556, -2), (key1569, -2), (key1593, 2), (key1683, 2), (key1689, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck143 : row143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow143 := by decide +kernel

theorem rowEval143 (x : Key → ℝ) : Integer.Sparse.eval row143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck143, Integer.Sparse.eval_collectBalanced, rawRowCheck143]

def rawRow144 : Integer.Sparse Key := [(key1472, -1), (key1480, -1), (key1472, 2), (key1426, 1), (key1444, 1), (key1393, -1), (key1426, -1), (key1420, -2), (key1387, 1), (key1420, 1), (key1903, 1), (key1911, 1), (key1903, -2), (key1575, -1), (key1593, -1), (key1298, 1), (key1575, 1), (key1569, 2), (key1292, -1), (key1569, -1), (key1918, -1), (key1926, -1), (key1896, 1), (key1918, 1), (key1681, 1), (key1689, 1), (key1351, -1), (key1681, -1), (key1542, -1), (key1618, -1), (key1312, 1), (key1618, 1), (key1920, 2), (key1899, -1), (key1920, -1), (key1683, -2), (key1354, 1), (key1683, 1), (key1556, 1), (key1624, 1), (key1326, -1), (key1624, -1)]

theorem rawRowCheck144 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form0 = rawRow144 := by decide +kernel

def row144 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck144 : row144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow144 := by decide +kernel

theorem rowEval144 (x : Key → ℝ) : Integer.Sparse.eval row144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck144, Integer.Sparse.eval_collectBalanced, rawRowCheck144]

def rawRow145 : Integer.Sparse Key := [(key1480, -1), (key1472, -1), (key1472, 2), (key1444, 1), (key1426, 1), (key1426, -1), (key1393, -1), (key1420, -2), (key1420, 1), (key1387, 1), (key1911, 1), (key1903, 1), (key1903, -2), (key1593, -1), (key1575, -1), (key1575, 1), (key1298, 1), (key1569, 2), (key1569, -1), (key1292, -1), (key1926, -1), (key1918, -1), (key1918, 1), (key1896, 1), (key1689, 1), (key1681, 1), (key1681, -1), (key1351, -1), (key1618, -1), (key1542, -1), (key1618, 1), (key1312, 1), (key1920, 2), (key1920, -1), (key1899, -1), (key1683, -2), (key1683, 1), (key1354, 1), (key1624, 1), (key1556, 1), (key1624, -1), (key1326, -1)]

theorem rawRowCheck145 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form0 = rawRow145 := by decide +kernel

def row145 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck145 : row145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow145 := by decide +kernel

theorem rowEval145 (x : Key → ℝ) : Integer.Sparse.eval row145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck145, Integer.Sparse.eval_collectBalanced, rawRowCheck145]

def rawRow146 : Integer.Sparse Key := [(key1542, -1), (key1548, -1), (key1556, 2), (key1569, 1), (key1575, 1), (key1624, -1), (key1683, -1), (key1593, -2), (key1633, 1), (key1689, 1), (key1312, 1), (key1318, 1), (key1326, -2), (key1420, -1), (key1426, -1), (key1624, 1), (key1920, 1), (key1444, 2), (key1633, -1), (key1926, -1), (key1292, -1), (key1298, -1), (key1326, 1), (key1354, 1), (key1387, 1), (key1393, 1), (key1556, -1), (key1899, -1), (key1444, -1), (key1480, -1), (key1593, 1), (key1911, 1), (key1298, 2), (key1318, -1), (key1351, -1), (key1393, -2), (key1548, 1), (key1896, 1), (key1426, 1), (key1472, 1), (key1575, -1), (key1903, -1)]

theorem rawRowCheck146 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form0 = rawRow146 := by decide +kernel

def row146 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck146 : row146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow146 := by decide +kernel

theorem rowEval146 (x : Key → ℝ) : Integer.Sparse.eval row146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck146, Integer.Sparse.eval_collectBalanced, rawRowCheck146]

def rawRow147 : Integer.Sparse Key := [(key1548, -1), (key1542, -1), (key1556, 2), (key1575, 1), (key1569, 1), (key1683, -1), (key1624, -1), (key1593, -2), (key1689, 1), (key1633, 1), (key1318, 1), (key1312, 1), (key1326, -2), (key1426, -1), (key1420, -1), (key1920, 1), (key1624, 1), (key1444, 2), (key1926, -1), (key1633, -1), (key1298, -1), (key1292, -1), (key1354, 1), (key1326, 1), (key1393, 1), (key1387, 1), (key1899, -1), (key1556, -1), (key1480, -1), (key1444, -1), (key1911, 1), (key1593, 1), (key1298, 2), (key1351, -1), (key1318, -1), (key1393, -2), (key1896, 1), (key1548, 1), (key1472, 1), (key1426, 1), (key1903, -1), (key1575, -1)]

theorem rawRowCheck147 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form0 = rawRow147 := by decide +kernel

def row147 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck147 : row147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow147 := by decide +kernel

theorem rowEval147 (x : Key → ℝ) : Integer.Sparse.eval row147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck147, Integer.Sparse.eval_collectBalanced, rawRowCheck147]

def rawRow148 : Integer.Sparse Key := [(key1548, -1), (key1556, -1), (key1542, 2), (key1681, 1), (key1683, 1), (key1569, -1), (key1618, -1), (key1689, -2), (key1593, 1), (key1633, 1), (key1318, 1), (key1326, 1), (key1312, -2), (key1918, -1), (key1920, -1), (key1420, 1), (key1618, 1), (key1926, 2), (key1444, -1), (key1633, -1), (key1351, -1), (key1354, -1), (key1292, 1), (key1312, 1), (key1896, 1), (key1899, 1), (key1387, -1), (key1542, -1), (key1911, -1), (key1926, -1), (key1480, 1), (key1689, 1), (key1351, 2), (key1298, -1), (key1318, -1), (key1896, -2), (key1393, 1), (key1548, 1), (key1903, 1), (key1918, 1), (key1472, -1), (key1681, -1)]

theorem rawRowCheck148 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form0 = rawRow148 := by decide +kernel

def row148 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck148 : row148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow148 := by decide +kernel

theorem rowEval148 (x : Key → ℝ) : Integer.Sparse.eval row148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck148, Integer.Sparse.eval_collectBalanced, rawRowCheck148]

def rawRow149 : Integer.Sparse Key := [(key1556, -1), (key1548, -1), (key1542, 2), (key1683, 1), (key1681, 1), (key1618, -1), (key1569, -1), (key1689, -2), (key1633, 1), (key1593, 1), (key1326, 1), (key1318, 1), (key1312, -2), (key1920, -1), (key1918, -1), (key1618, 1), (key1420, 1), (key1926, 2), (key1633, -1), (key1444, -1), (key1354, -1), (key1351, -1), (key1312, 1), (key1292, 1), (key1899, 1), (key1896, 1), (key1542, -1), (key1387, -1), (key1926, -1), (key1911, -1), (key1689, 1), (key1480, 1), (key1351, 2), (key1318, -1), (key1298, -1), (key1896, -2), (key1548, 1), (key1393, 1), (key1918, 1), (key1903, 1), (key1681, -1), (key1472, -1)]

theorem rawRowCheck149 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form0 = rawRow149 := by decide +kernel

def row149 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck149 : row149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow149 := by decide +kernel

theorem rowEval149 (x : Key → ℝ) : Integer.Sparse.eval row149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck149, Integer.Sparse.eval_collectBalanced, rawRowCheck149]

def rawRow150 : Integer.Sparse Key := [(key1569, -1), (key1575, -1), (key1593, 2), (key1542, 1), (key1548, 1), (key1633, -1), (key1689, -1), (key1556, -2), (key1624, 1), (key1683, 1), (key1420, 1), (key1426, 1), (key1444, -2), (key1312, -1), (key1318, -1), (key1633, 1), (key1926, 1), (key1326, 2), (key1624, -1), (key1920, -1), (key1387, -1), (key1393, -1), (key1444, 1), (key1480, 1), (key1292, 1), (key1298, 1), (key1593, -1), (key1911, -1), (key1326, -1), (key1354, -1), (key1556, 1), (key1899, 1), (key1393, 2), (key1426, -1), (key1472, -1), (key1298, -2), (key1575, 1), (key1903, 1), (key1318, 1), (key1351, 1), (key1548, -1), (key1896, -1)]

theorem rawRowCheck150 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form0 = rawRow150 := by decide +kernel

def row150 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck150 : row150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow150 := by decide +kernel

theorem rowEval150 (x : Key → ℝ) : Integer.Sparse.eval row150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block0.form0) x := by
  rw [rowCheck150, Integer.Sparse.eval_collectBalanced, rawRowCheck150]

def rawRow151 : Integer.Sparse Key := [(key1575, -1), (key1569, -1), (key1593, 2), (key1548, 1), (key1542, 1), (key1689, -1), (key1633, -1), (key1556, -2), (key1683, 1), (key1624, 1), (key1426, 1), (key1420, 1), (key1444, -2), (key1318, -1), (key1312, -1), (key1926, 1), (key1633, 1), (key1326, 2), (key1920, -1), (key1624, -1), (key1393, -1), (key1387, -1), (key1480, 1), (key1444, 1), (key1298, 1), (key1292, 1), (key1911, -1), (key1593, -1), (key1354, -1), (key1326, -1), (key1899, 1), (key1556, 1), (key1393, 2), (key1472, -1), (key1426, -1), (key1298, -2), (key1903, 1), (key1575, 1), (key1351, 1), (key1318, 1), (key1896, -1), (key1548, -1)]

theorem rawRowCheck151 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form0 = rawRow151 := by decide +kernel

def row151 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck151 : row151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow151 := by decide +kernel

theorem rowEval151 (x : Key → ℝ) : Integer.Sparse.eval row151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck151, Integer.Sparse.eval_collectBalanced, rawRowCheck151]

def rawRow152 : Integer.Sparse Key := [(key1575, -1), (key1593, -1), (key1569, 2), (key1681, 1), (key1689, 1), (key1542, -1), (key1618, -1), (key1683, -2), (key1556, 1), (key1624, 1), (key1426, 1), (key1444, 1), (key1420, -2), (key1918, -1), (key1926, -1), (key1312, 1), (key1618, 1), (key1920, 2), (key1326, -1), (key1624, -1), (key1472, -1), (key1480, -1), (key1387, 1), (key1420, 1), (key1903, 1), (key1911, 1), (key1292, -1), (key1569, -1), (key1899, -1), (key1920, -1), (key1354, 1), (key1683, 1), (key1472, 2), (key1393, -1), (key1426, -1), (key1903, -2), (key1298, 1), (key1575, 1), (key1896, 1), (key1918, 1), (key1351, -1), (key1681, -1)]

theorem rawRowCheck152 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form0 = rawRow152 := by decide +kernel

def row152 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck152 : row152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow152 := by decide +kernel

theorem rowEval152 (x : Key → ℝ) : Integer.Sparse.eval row152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck152, Integer.Sparse.eval_collectBalanced, rawRowCheck152]

def rawRow153 : Integer.Sparse Key := [(key1593, -1), (key1575, -1), (key1569, 2), (key1689, 1), (key1681, 1), (key1618, -1), (key1542, -1), (key1683, -2), (key1624, 1), (key1556, 1), (key1444, 1), (key1426, 1), (key1420, -2), (key1926, -1), (key1918, -1), (key1618, 1), (key1312, 1), (key1920, 2), (key1624, -1), (key1326, -1), (key1480, -1), (key1472, -1), (key1420, 1), (key1387, 1), (key1911, 1), (key1903, 1), (key1569, -1), (key1292, -1), (key1920, -1), (key1899, -1), (key1683, 1), (key1354, 1), (key1472, 2), (key1426, -1), (key1393, -1), (key1903, -2), (key1575, 1), (key1298, 1), (key1918, 1), (key1896, 1), (key1681, -1), (key1351, -1)]

theorem rawRowCheck153 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form0 = rawRow153 := by decide +kernel

def row153 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck153 : row153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow153 := by decide +kernel

theorem rowEval153 (x : Key → ℝ) : Integer.Sparse.eval row153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck153, Integer.Sparse.eval_collectBalanced, rawRowCheck153]

def rawRow154 : Integer.Sparse Key := [(key1681, -1), (key1683, -1), (key1689, 2), (key1548, 1), (key1556, 1), (key1593, -1), (key1633, -1), (key1542, -2), (key1569, 1), (key1618, 1), (key1918, 1), (key1920, 1), (key1926, -2), (key1318, -1), (key1326, -1), (key1444, 1), (key1633, 1), (key1312, 2), (key1420, -1), (key1618, -1), (key1896, -1), (key1899, -1), (key1911, 1), (key1926, 1), (key1351, 1), (key1354, 1), (key1480, -1), (key1689, -1), (key1292, -1), (key1312, -1), (key1387, 1), (key1542, 1), (key1896, 2), (key1903, -1), (key1918, -1), (key1351, -2), (key1472, 1), (key1681, 1), (key1298, 1), (key1318, 1), (key1393, -1), (key1548, -1)]

theorem rawRowCheck154 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form0 = rawRow154 := by decide +kernel

def row154 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck154 : row154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow154 := by decide +kernel

theorem rowEval154 (x : Key → ℝ) : Integer.Sparse.eval row154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck154, Integer.Sparse.eval_collectBalanced, rawRowCheck154]

def rawRow155 : Integer.Sparse Key := [(key1683, -1), (key1681, -1), (key1689, 2), (key1556, 1), (key1548, 1), (key1633, -1), (key1593, -1), (key1542, -2), (key1618, 1), (key1569, 1), (key1920, 1), (key1918, 1), (key1926, -2), (key1326, -1), (key1318, -1), (key1633, 1), (key1444, 1), (key1312, 2), (key1618, -1), (key1420, -1), (key1899, -1), (key1896, -1), (key1926, 1), (key1911, 1), (key1354, 1), (key1351, 1), (key1689, -1), (key1480, -1), (key1312, -1), (key1292, -1), (key1542, 1), (key1387, 1), (key1896, 2), (key1918, -1), (key1903, -1), (key1351, -2), (key1681, 1), (key1472, 1), (key1318, 1), (key1298, 1), (key1548, -1), (key1393, -1)]

theorem rawRowCheck155 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form0 = rawRow155 := by decide +kernel

def row155 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck155 : row155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow155 := by decide +kernel

theorem rowEval155 (x : Key → ℝ) : Integer.Sparse.eval row155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck155, Integer.Sparse.eval_collectBalanced, rawRowCheck155]

def rawRow156 : Integer.Sparse Key := [(key1681, -1), (key1689, -1), (key1683, 2), (key1575, 1), (key1593, 1), (key1556, -1), (key1624, -1), (key1569, -2), (key1542, 1), (key1618, 1), (key1918, 1), (key1926, 1), (key1920, -2), (key1426, -1), (key1444, -1), (key1326, 1), (key1624, 1), (key1420, 2), (key1312, -1), (key1618, -1), (key1903, -1), (key1911, -1), (key1899, 1), (key1920, 1), (key1472, 1), (key1480, 1), (key1354, -1), (key1683, -1), (key1387, -1), (key1420, -1), (key1292, 1), (key1569, 1), (key1903, 2), (key1896, -1), (key1918, -1), (key1472, -2), (key1351, 1), (key1681, 1), (key1393, 1), (key1426, 1), (key1298, -1), (key1575, -1)]

theorem rawRowCheck156 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form0 = rawRow156 := by decide +kernel

def row156 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck156 : row156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow156 := by decide +kernel

theorem rowEval156 (x : Key → ℝ) : Integer.Sparse.eval row156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck156, Integer.Sparse.eval_collectBalanced, rawRowCheck156]

def rawRow157 : Integer.Sparse Key := [(key1689, -1), (key1681, -1), (key1683, 2), (key1593, 1), (key1575, 1), (key1624, -1), (key1556, -1), (key1569, -2), (key1618, 1), (key1542, 1), (key1926, 1), (key1918, 1), (key1920, -2), (key1444, -1), (key1426, -1), (key1624, 1), (key1326, 1), (key1420, 2), (key1618, -1), (key1312, -1), (key1911, -1), (key1903, -1), (key1920, 1), (key1899, 1), (key1480, 1), (key1472, 1), (key1683, -1), (key1354, -1), (key1420, -1), (key1387, -1), (key1569, 1), (key1292, 1), (key1903, 2), (key1918, -1), (key1896, -1), (key1472, -2), (key1681, 1), (key1351, 1), (key1426, 1), (key1393, 1), (key1575, -1), (key1298, -1)]

theorem rawRowCheck157 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form0 = rawRow157 := by decide +kernel

def row157 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck157 : row157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow157 := by decide +kernel

theorem rowEval157 (x : Key → ℝ) : Integer.Sparse.eval row157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck157, Integer.Sparse.eval_collectBalanced, rawRowCheck157]

def rawRow158 : Integer.Sparse Key := [(key1896, -1), (key1896, -1), (key1899, 2), (key1903, 1), (key1903, 1), (key1920, -1), (key1920, -1), (key1911, -2), (key1926, 1), (key1926, 1), (key1351, 1), (key1351, 1), (key1354, -2), (key1472, -1), (key1472, -1), (key1683, 1), (key1683, 1), (key1480, 2), (key1689, -1), (key1689, -1), (key1298, -1), (key1298, -1), (key1326, 1), (key1326, 1), (key1393, 1), (key1393, 1), (key1556, -1), (key1556, -1), (key1444, -1), (key1444, -1), (key1593, 1), (key1593, 1), (key1292, 2), (key1312, -1), (key1312, -1), (key1387, -2), (key1542, 1), (key1542, 1), (key1420, 1), (key1420, 1), (key1569, -1), (key1569, -1)]

theorem rawRowCheck158 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form0 = rawRow158 := by decide +kernel

def row158 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1387, -2), (key1393, 2), (key1420, 2), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, 2), (key1556, -2), (key1569, -2), (key1593, 2), (key1683, 2), (key1689, -2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

theorem rowCheck158 : row158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow158 := by decide +kernel

theorem rowEval158 (x : Key → ℝ) : Integer.Sparse.eval row158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck158, Integer.Sparse.eval_collectBalanced, rawRowCheck158]

def rawRow159 : Integer.Sparse Key := [(key1896, -1), (key1899, -1), (key1896, 2), (key1918, 1), (key1920, 1), (key1903, -1), (key1918, -1), (key1926, -2), (key1911, 1), (key1926, 1), (key1351, 1), (key1354, 1), (key1351, -2), (key1681, -1), (key1683, -1), (key1472, 1), (key1681, 1), (key1689, 2), (key1480, -1), (key1689, -1), (key1318, -1), (key1326, -1), (key1298, 1), (key1318, 1), (key1548, 1), (key1556, 1), (key1393, -1), (key1548, -1), (key1593, -1), (key1633, -1), (key1444, 1), (key1633, 1), (key1312, 2), (key1292, -1), (key1312, -1), (key1542, -2), (key1387, 1), (key1542, 1), (key1569, 1), (key1618, 1), (key1420, -1), (key1618, -1)]

theorem rawRowCheck159 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form0 = rawRow159 := by decide +kernel

def row159 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck159 : row159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow159 := by decide +kernel

theorem rowEval159 (x : Key → ℝ) : Integer.Sparse.eval row159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck159, Integer.Sparse.eval_collectBalanced, rawRowCheck159]

end MUB6.Certificate.GramRows

end OAI
