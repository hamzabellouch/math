import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
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

def rawRow6400 : Integer.Sparse Key := [(key1393, -1), (key1393, -1), (key1387, 2), (key1472, -1), (key1472, -1), (key1426, 2), (key1426, 2), (key1420, -1), (key1420, -1), (key1480, 2), (key1444, -1), (key1444, -1), (key1298, 1), (key1298, 1), (key1292, -2), (key1903, 1), (key1903, 1), (key1575, -2), (key1575, -2), (key1569, 1), (key1569, 1), (key1911, -2), (key1593, 1), (key1593, 1), (key1318, -1), (key1318, -1), (key1312, 1), (key1312, 1), (key1548, 1), (key1548, 1), (key1542, -1), (key1542, -1), (key1918, -1), (key1918, -1), (key1681, 1), (key1681, 1), (key1926, 1), (key1926, 1), (key1689, -1), (key1689, -1)]

theorem rawRowCheck6400 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form6 = rawRow6400 := by decide +kernel

def row6400 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

theorem rowCheck6400 : row6400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6400 := by decide +kernel

theorem rowEval6400 (x : Key → ℝ) : Integer.Sparse.eval row6400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6400, Integer.Sparse.eval_collectBalanced, rawRowCheck6400]

def rawRow6401 : Integer.Sparse Key := [(key1420, -1), (key1426, -1), (key1444, 2), (key1387, -1), (key1393, -1), (key1420, 2), (key1472, 2), (key1444, -1), (key1480, -1), (key1393, 2), (key1426, -1), (key1472, -1), (key1569, 1), (key1575, 1), (key1593, -2), (key1292, 1), (key1298, 1), (key1569, -2), (key1903, -2), (key1593, 1), (key1911, 1), (key1298, -2), (key1575, 1), (key1903, 1), (key1618, -1), (key1681, -1), (key1633, 1), (key1689, 1), (key1618, 1), (key1918, 1), (key1633, -1), (key1926, -1), (key1312, -1), (key1351, -1), (key1542, 1), (key1896, 1), (key1318, 1), (key1351, 1), (key1548, -1), (key1896, -1)]

theorem rawRowCheck6401 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form6 = rawRow6401 := by decide +kernel

def row6401 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6401 : row6401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6401 := by decide +kernel

theorem rowEval6401 (x : Key → ℝ) : Integer.Sparse.eval row6401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6401, Integer.Sparse.eval_collectBalanced, rawRowCheck6401]

def rawRow6402 : Integer.Sparse Key := [(key1426, -1), (key1420, -1), (key1444, 2), (key1393, -1), (key1387, -1), (key1472, 2), (key1420, 2), (key1480, -1), (key1444, -1), (key1393, 2), (key1472, -1), (key1426, -1), (key1575, 1), (key1569, 1), (key1593, -2), (key1298, 1), (key1292, 1), (key1903, -2), (key1569, -2), (key1911, 1), (key1593, 1), (key1298, -2), (key1903, 1), (key1575, 1), (key1681, -1), (key1618, -1), (key1689, 1), (key1633, 1), (key1918, 1), (key1618, 1), (key1926, -1), (key1633, -1), (key1351, -1), (key1312, -1), (key1896, 1), (key1542, 1), (key1351, 1), (key1318, 1), (key1896, -1), (key1548, -1)]

theorem rawRowCheck6402 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form6 = rawRow6402 := by decide +kernel

def row6402 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6402 : row6402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6402 := by decide +kernel

theorem rowEval6402 (x : Key → ℝ) : Integer.Sparse.eval row6402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6402, Integer.Sparse.eval_collectBalanced, rawRowCheck6402]

def rawRow6403 : Integer.Sparse Key := [(key1420, -1), (key1444, -1), (key1426, 2), (key1420, -1), (key1444, -1), (key1387, 2), (key1480, 2), (key1393, -1), (key1472, -1), (key1426, 2), (key1393, -1), (key1472, -1), (key1569, 1), (key1593, 1), (key1575, -2), (key1569, 1), (key1593, 1), (key1292, -2), (key1911, -2), (key1298, 1), (key1903, 1), (key1575, -2), (key1298, 1), (key1903, 1), (key1542, -1), (key1689, -1), (key1548, 1), (key1681, 1), (key1312, 1), (key1926, 1), (key1318, -1), (key1918, -1), (key1542, -1), (key1689, -1), (key1312, 1), (key1926, 1), (key1548, 1), (key1681, 1), (key1318, -1), (key1918, -1)]

theorem rawRowCheck6403 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form6 = rawRow6403 := by decide +kernel

def row6403 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

theorem rowCheck6403 : row6403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6403 := by decide +kernel

theorem rowEval6403 (x : Key → ℝ) : Integer.Sparse.eval row6403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6403, Integer.Sparse.eval_collectBalanced, rawRowCheck6403]

def rawRow6404 : Integer.Sparse Key := [(key1444, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1420, -1), (key1480, 2), (key1387, 2), (key1472, -1), (key1393, -1), (key1426, 2), (key1472, -1), (key1393, -1), (key1593, 1), (key1569, 1), (key1575, -2), (key1593, 1), (key1569, 1), (key1911, -2), (key1292, -2), (key1903, 1), (key1298, 1), (key1575, -2), (key1903, 1), (key1298, 1), (key1689, -1), (key1542, -1), (key1681, 1), (key1548, 1), (key1926, 1), (key1312, 1), (key1918, -1), (key1318, -1), (key1689, -1), (key1542, -1), (key1926, 1), (key1312, 1), (key1681, 1), (key1548, 1), (key1918, -1), (key1318, -1)]

theorem rawRowCheck6404 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form6 = rawRow6404 := by decide +kernel

def row6404 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

theorem rowCheck6404 : row6404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6404 := by decide +kernel

theorem rowEval6404 (x : Key → ℝ) : Integer.Sparse.eval row6404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6404, Integer.Sparse.eval_collectBalanced, rawRowCheck6404]

def rawRow6405 : Integer.Sparse Key := [(key1426, -1), (key1444, -1), (key1420, 2), (key1472, -1), (key1480, -1), (key1393, 2), (key1444, 2), (key1387, -1), (key1420, -1), (key1472, 2), (key1393, -1), (key1426, -1), (key1575, 1), (key1593, 1), (key1569, -2), (key1903, 1), (key1911, 1), (key1298, -2), (key1593, -2), (key1292, 1), (key1569, 1), (key1903, -2), (key1298, 1), (key1575, 1), (key1548, -1), (key1633, -1), (key1542, 1), (key1618, 1), (key1318, 1), (key1633, 1), (key1312, -1), (key1618, -1), (key1896, -1), (key1926, -1), (key1351, 1), (key1689, 1), (key1896, 1), (key1918, 1), (key1351, -1), (key1681, -1)]

theorem rawRowCheck6405 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form6 = rawRow6405 := by decide +kernel

def row6405 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6405 : row6405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6405 := by decide +kernel

theorem rowEval6405 (x : Key → ℝ) : Integer.Sparse.eval row6405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6405, Integer.Sparse.eval_collectBalanced, rawRowCheck6405]

def rawRow6406 : Integer.Sparse Key := [(key1444, -1), (key1426, -1), (key1420, 2), (key1480, -1), (key1472, -1), (key1444, 2), (key1393, 2), (key1420, -1), (key1387, -1), (key1472, 2), (key1426, -1), (key1393, -1), (key1593, 1), (key1575, 1), (key1569, -2), (key1911, 1), (key1903, 1), (key1593, -2), (key1298, -2), (key1569, 1), (key1292, 1), (key1903, -2), (key1575, 1), (key1298, 1), (key1633, -1), (key1548, -1), (key1618, 1), (key1542, 1), (key1633, 1), (key1318, 1), (key1618, -1), (key1312, -1), (key1926, -1), (key1896, -1), (key1689, 1), (key1351, 1), (key1918, 1), (key1896, 1), (key1681, -1), (key1351, -1)]

theorem rawRowCheck6406 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form6 = rawRow6406 := by decide +kernel

def row6406 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6406 : row6406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6406 := by decide +kernel

theorem rowEval6406 (x : Key → ℝ) : Integer.Sparse.eval row6406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6406, Integer.Sparse.eval_collectBalanced, rawRowCheck6406]

def rawRow6407 : Integer.Sparse Key := [(key1472, -1), (key1472, -1), (key1480, 2), (key1393, -1), (key1393, -1), (key1426, 2), (key1426, 2), (key1444, -1), (key1444, -1), (key1387, 2), (key1420, -1), (key1420, -1), (key1903, 1), (key1903, 1), (key1911, -2), (key1298, 1), (key1298, 1), (key1575, -2), (key1575, -2), (key1593, 1), (key1593, 1), (key1292, -2), (key1569, 1), (key1569, 1), (key1918, -1), (key1918, -1), (key1926, 1), (key1926, 1), (key1681, 1), (key1681, 1), (key1689, -1), (key1689, -1), (key1318, -1), (key1318, -1), (key1548, 1), (key1548, 1), (key1312, 1), (key1312, 1), (key1542, -1), (key1542, -1)]

theorem rawRowCheck6407 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form6 = rawRow6407 := by decide +kernel

def row6407 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1318, -2), (key1387, 2), (key1393, -2), (key1420, -2), (key1426, 4), (key1444, -2), (key1472, -2), (key1480, 2), (key1542, -2), (key1548, 2), (key1569, 2), (key1575, -4), (key1593, 2), (key1681, 2), (key1689, -2), (key1903, 2), (key1911, -2), (key1918, -2), (key1926, 2)]

theorem rowCheck6407 : row6407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6407 := by decide +kernel

theorem rowEval6407 (x : Key → ℝ) : Integer.Sparse.eval row6407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6407, Integer.Sparse.eval_collectBalanced, rawRowCheck6407]

def rawRow6408 : Integer.Sparse Key := [(key1472, -1), (key1480, -1), (key1472, 2), (key1426, -1), (key1444, -1), (key1393, 2), (key1444, 2), (key1393, -1), (key1426, -1), (key1420, 2), (key1387, -1), (key1420, -1), (key1903, 1), (key1911, 1), (key1903, -2), (key1575, 1), (key1593, 1), (key1298, -2), (key1593, -2), (key1298, 1), (key1575, 1), (key1569, -2), (key1292, 1), (key1569, 1), (key1896, -1), (key1926, -1), (key1896, 1), (key1918, 1), (key1351, 1), (key1689, 1), (key1351, -1), (key1681, -1), (key1548, -1), (key1633, -1), (key1318, 1), (key1633, 1), (key1542, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

theorem rawRowCheck6408 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form6 = rawRow6408 := by decide +kernel

def row6408 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6408 : row6408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6408 := by decide +kernel

theorem rowEval6408 (x : Key → ℝ) : Integer.Sparse.eval row6408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6408, Integer.Sparse.eval_collectBalanced, rawRowCheck6408]

def rawRow6409 : Integer.Sparse Key := [(key1480, -1), (key1472, -1), (key1472, 2), (key1444, -1), (key1426, -1), (key1444, 2), (key1393, 2), (key1426, -1), (key1393, -1), (key1420, 2), (key1420, -1), (key1387, -1), (key1911, 1), (key1903, 1), (key1903, -2), (key1593, 1), (key1575, 1), (key1593, -2), (key1298, -2), (key1575, 1), (key1298, 1), (key1569, -2), (key1569, 1), (key1292, 1), (key1926, -1), (key1896, -1), (key1918, 1), (key1896, 1), (key1689, 1), (key1351, 1), (key1681, -1), (key1351, -1), (key1633, -1), (key1548, -1), (key1633, 1), (key1318, 1), (key1618, 1), (key1542, 1), (key1618, -1), (key1312, -1)]

theorem rawRowCheck6409 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form6 = rawRow6409 := by decide +kernel

def row6409 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6409 : row6409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6409 := by decide +kernel

theorem rowEval6409 (x : Key → ℝ) : Integer.Sparse.eval row6409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6409, Integer.Sparse.eval_collectBalanced, rawRowCheck6409]

def rawRow6410 : Integer.Sparse Key := [(key1542, -1), (key1548, -1), (key1556, 2), (key1569, -1), (key1575, -1), (key1618, 2), (key1681, 2), (key1624, -1), (key1683, -1), (key1593, 2), (key1633, -1), (key1689, -1), (key1312, 1), (key1318, 1), (key1326, -2), (key1420, 1), (key1426, 1), (key1618, -2), (key1918, -2), (key1624, 1), (key1920, 1), (key1444, -2), (key1633, 1), (key1926, 1), (key1312, -1), (key1351, -1), (key1326, 1), (key1354, 1), (key1542, 1), (key1896, 1), (key1556, -1), (key1899, -1), (key1420, -1), (key1472, -1), (key1569, 1), (key1903, 1), (key1444, 1), (key1480, 1), (key1593, -1), (key1911, -1)]

theorem rawRowCheck6410 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form6 = rawRow6410 := by decide +kernel

def row6410 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6410 : row6410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6410 := by decide +kernel

theorem rowEval6410 (x : Key → ℝ) : Integer.Sparse.eval row6410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6410, Integer.Sparse.eval_collectBalanced, rawRowCheck6410]

def rawRow6411 : Integer.Sparse Key := [(key1548, -1), (key1542, -1), (key1556, 2), (key1575, -1), (key1569, -1), (key1681, 2), (key1618, 2), (key1683, -1), (key1624, -1), (key1593, 2), (key1689, -1), (key1633, -1), (key1318, 1), (key1312, 1), (key1326, -2), (key1426, 1), (key1420, 1), (key1918, -2), (key1618, -2), (key1920, 1), (key1624, 1), (key1444, -2), (key1926, 1), (key1633, 1), (key1351, -1), (key1312, -1), (key1354, 1), (key1326, 1), (key1896, 1), (key1542, 1), (key1899, -1), (key1556, -1), (key1472, -1), (key1420, -1), (key1903, 1), (key1569, 1), (key1480, 1), (key1444, 1), (key1911, -1), (key1593, -1)]

theorem rawRowCheck6411 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form6 = rawRow6411 := by decide +kernel

def row6411 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6411 : row6411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6411 := by decide +kernel

theorem rowEval6411 (x : Key → ℝ) : Integer.Sparse.eval row6411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6411, Integer.Sparse.eval_collectBalanced, rawRowCheck6411]

def rawRow6412 : Integer.Sparse Key := [(key1548, -1), (key1556, -1), (key1542, 2), (key1681, -1), (key1683, -1), (key1575, 2), (key1624, 2), (key1569, -1), (key1618, -1), (key1689, 2), (key1593, -1), (key1633, -1), (key1318, 1), (key1326, 1), (key1312, -2), (key1918, 1), (key1920, 1), (key1426, -2), (key1624, -2), (key1420, 1), (key1618, 1), (key1926, -2), (key1444, 1), (key1633, 1), (key1298, -1), (key1326, -1), (key1292, 1), (key1312, 1), (key1393, 1), (key1556, 1), (key1387, -1), (key1542, -1), (key1903, -1), (key1920, -1), (key1472, 1), (key1683, 1), (key1911, 1), (key1926, 1), (key1480, -1), (key1689, -1)]

theorem rawRowCheck6412 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form6 = rawRow6412 := by decide +kernel

def row6412 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6412 : row6412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6412 := by decide +kernel

theorem rowEval6412 (x : Key → ℝ) : Integer.Sparse.eval row6412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6412, Integer.Sparse.eval_collectBalanced, rawRowCheck6412]

def rawRow6413 : Integer.Sparse Key := [(key1556, -1), (key1548, -1), (key1542, 2), (key1683, -1), (key1681, -1), (key1624, 2), (key1575, 2), (key1618, -1), (key1569, -1), (key1689, 2), (key1633, -1), (key1593, -1), (key1326, 1), (key1318, 1), (key1312, -2), (key1920, 1), (key1918, 1), (key1624, -2), (key1426, -2), (key1618, 1), (key1420, 1), (key1926, -2), (key1633, 1), (key1444, 1), (key1326, -1), (key1298, -1), (key1312, 1), (key1292, 1), (key1556, 1), (key1393, 1), (key1542, -1), (key1387, -1), (key1920, -1), (key1903, -1), (key1683, 1), (key1472, 1), (key1926, 1), (key1911, 1), (key1689, -1), (key1480, -1)]

theorem rawRowCheck6413 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form6 = rawRow6413 := by decide +kernel

def row6413 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6413 : row6413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6413 := by decide +kernel

theorem rowEval6413 (x : Key → ℝ) : Integer.Sparse.eval row6413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6413, Integer.Sparse.eval_collectBalanced, rawRowCheck6413]

def rawRow6414 : Integer.Sparse Key := [(key1569, -1), (key1575, -1), (key1593, 2), (key1542, -1), (key1548, -1), (key1618, 2), (key1681, 2), (key1633, -1), (key1689, -1), (key1556, 2), (key1624, -1), (key1683, -1), (key1420, 1), (key1426, 1), (key1444, -2), (key1312, 1), (key1318, 1), (key1618, -2), (key1918, -2), (key1633, 1), (key1926, 1), (key1326, -2), (key1624, 1), (key1920, 1), (key1420, -1), (key1472, -1), (key1444, 1), (key1480, 1), (key1569, 1), (key1903, 1), (key1593, -1), (key1911, -1), (key1312, -1), (key1351, -1), (key1542, 1), (key1896, 1), (key1326, 1), (key1354, 1), (key1556, -1), (key1899, -1)]

theorem rawRowCheck6414 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form6 = rawRow6414 := by decide +kernel

def row6414 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6414 : row6414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6414 := by decide +kernel

theorem rowEval6414 (x : Key → ℝ) : Integer.Sparse.eval row6414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6414, Integer.Sparse.eval_collectBalanced, rawRowCheck6414]

def rawRow6415 : Integer.Sparse Key := [(key1575, -1), (key1569, -1), (key1593, 2), (key1548, -1), (key1542, -1), (key1681, 2), (key1618, 2), (key1689, -1), (key1633, -1), (key1556, 2), (key1683, -1), (key1624, -1), (key1426, 1), (key1420, 1), (key1444, -2), (key1318, 1), (key1312, 1), (key1918, -2), (key1618, -2), (key1926, 1), (key1633, 1), (key1326, -2), (key1920, 1), (key1624, 1), (key1472, -1), (key1420, -1), (key1480, 1), (key1444, 1), (key1903, 1), (key1569, 1), (key1911, -1), (key1593, -1), (key1351, -1), (key1312, -1), (key1896, 1), (key1542, 1), (key1354, 1), (key1326, 1), (key1899, -1), (key1556, -1)]

theorem rawRowCheck6415 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form6 = rawRow6415 := by decide +kernel

def row6415 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6415 : row6415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6415 := by decide +kernel

theorem rowEval6415 (x : Key → ℝ) : Integer.Sparse.eval row6415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6415, Integer.Sparse.eval_collectBalanced, rawRowCheck6415]

def rawRow6416 : Integer.Sparse Key := [(key1569, -1), (key1593, -1), (key1575, 2), (key1618, -1), (key1633, -1), (key1542, 2), (key1689, 2), (key1548, -1), (key1681, -1), (key1624, 2), (key1556, -1), (key1683, -1), (key1420, 1), (key1444, 1), (key1426, -2), (key1618, 1), (key1633, 1), (key1312, -2), (key1926, -2), (key1318, 1), (key1918, 1), (key1624, -2), (key1326, 1), (key1920, 1), (key1387, -1), (key1480, -1), (key1393, 1), (key1472, 1), (key1292, 1), (key1911, 1), (key1298, -1), (key1903, -1), (key1542, -1), (key1689, -1), (key1312, 1), (key1926, 1), (key1556, 1), (key1683, 1), (key1326, -1), (key1920, -1)]

theorem rawRowCheck6416 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form6 = rawRow6416 := by decide +kernel

def row6416 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6416 : row6416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6416 := by decide +kernel

theorem rowEval6416 (x : Key → ℝ) : Integer.Sparse.eval row6416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6416, Integer.Sparse.eval_collectBalanced, rawRowCheck6416]

def rawRow6417 : Integer.Sparse Key := [(key1593, -1), (key1569, -1), (key1575, 2), (key1633, -1), (key1618, -1), (key1689, 2), (key1542, 2), (key1681, -1), (key1548, -1), (key1624, 2), (key1683, -1), (key1556, -1), (key1444, 1), (key1420, 1), (key1426, -2), (key1633, 1), (key1618, 1), (key1926, -2), (key1312, -2), (key1918, 1), (key1318, 1), (key1624, -2), (key1920, 1), (key1326, 1), (key1480, -1), (key1387, -1), (key1472, 1), (key1393, 1), (key1911, 1), (key1292, 1), (key1903, -1), (key1298, -1), (key1689, -1), (key1542, -1), (key1926, 1), (key1312, 1), (key1683, 1), (key1556, 1), (key1920, -1), (key1326, -1)]

theorem rawRowCheck6417 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form6 = rawRow6417 := by decide +kernel

def row6417 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6417 : row6417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6417 := by decide +kernel

theorem rowEval6417 (x : Key → ℝ) : Integer.Sparse.eval row6417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6417, Integer.Sparse.eval_collectBalanced, rawRowCheck6417]

def rawRow6418 : Integer.Sparse Key := [(key1618, -1), (key1633, -1), (key1624, 2), (key1569, -1), (key1593, -1), (key1542, 2), (key1689, 2), (key1556, -1), (key1683, -1), (key1575, 2), (key1548, -1), (key1681, -1), (key1618, 1), (key1633, 1), (key1624, -2), (key1420, 1), (key1444, 1), (key1312, -2), (key1926, -2), (key1326, 1), (key1920, 1), (key1426, -2), (key1318, 1), (key1918, 1), (key1542, -1), (key1689, -1), (key1556, 1), (key1683, 1), (key1312, 1), (key1926, 1), (key1326, -1), (key1920, -1), (key1387, -1), (key1480, -1), (key1292, 1), (key1911, 1), (key1393, 1), (key1472, 1), (key1298, -1), (key1903, -1)]

theorem rawRowCheck6418 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form6 = rawRow6418 := by decide +kernel

def row6418 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6418 : row6418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6418 := by decide +kernel

theorem rowEval6418 (x : Key → ℝ) : Integer.Sparse.eval row6418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6418, Integer.Sparse.eval_collectBalanced, rawRowCheck6418]

def rawRow6419 : Integer.Sparse Key := [(key1633, -1), (key1618, -1), (key1624, 2), (key1593, -1), (key1569, -1), (key1689, 2), (key1542, 2), (key1683, -1), (key1556, -1), (key1575, 2), (key1681, -1), (key1548, -1), (key1633, 1), (key1618, 1), (key1624, -2), (key1444, 1), (key1420, 1), (key1926, -2), (key1312, -2), (key1920, 1), (key1326, 1), (key1426, -2), (key1918, 1), (key1318, 1), (key1689, -1), (key1542, -1), (key1683, 1), (key1556, 1), (key1926, 1), (key1312, 1), (key1920, -1), (key1326, -1), (key1480, -1), (key1387, -1), (key1911, 1), (key1292, 1), (key1472, 1), (key1393, 1), (key1903, -1), (key1298, -1)]

theorem rawRowCheck6419 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form6 = rawRow6419 := by decide +kernel

def row6419 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6419 : row6419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6419 := by decide +kernel

theorem rowEval6419 (x : Key → ℝ) : Integer.Sparse.eval row6419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6419, Integer.Sparse.eval_collectBalanced, rawRowCheck6419]

def rawRow6420 : Integer.Sparse Key := [(key1624, -1), (key1633, -1), (key1618, 2), (key1683, -1), (key1689, -1), (key1556, 2), (key1593, 2), (key1542, -1), (key1569, -1), (key1681, 2), (key1548, -1), (key1575, -1), (key1624, 1), (key1633, 1), (key1618, -2), (key1920, 1), (key1926, 1), (key1326, -2), (key1444, -2), (key1312, 1), (key1420, 1), (key1918, -2), (key1318, 1), (key1426, 1), (key1556, -1), (key1593, -1), (key1542, 1), (key1569, 1), (key1326, 1), (key1444, 1), (key1312, -1), (key1420, -1), (key1899, -1), (key1911, -1), (key1354, 1), (key1480, 1), (key1896, 1), (key1903, 1), (key1351, -1), (key1472, -1)]

theorem rawRowCheck6420 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form6 = rawRow6420 := by decide +kernel

def row6420 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6420 : row6420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6420 := by decide +kernel

theorem rowEval6420 (x : Key → ℝ) : Integer.Sparse.eval row6420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6420, Integer.Sparse.eval_collectBalanced, rawRowCheck6420]

def rawRow6421 : Integer.Sparse Key := [(key1633, -1), (key1624, -1), (key1618, 2), (key1689, -1), (key1683, -1), (key1593, 2), (key1556, 2), (key1569, -1), (key1542, -1), (key1681, 2), (key1575, -1), (key1548, -1), (key1633, 1), (key1624, 1), (key1618, -2), (key1926, 1), (key1920, 1), (key1444, -2), (key1326, -2), (key1420, 1), (key1312, 1), (key1918, -2), (key1426, 1), (key1318, 1), (key1593, -1), (key1556, -1), (key1569, 1), (key1542, 1), (key1444, 1), (key1326, 1), (key1420, -1), (key1312, -1), (key1911, -1), (key1899, -1), (key1480, 1), (key1354, 1), (key1903, 1), (key1896, 1), (key1472, -1), (key1351, -1)]

theorem rawRowCheck6421 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form6 = rawRow6421 := by decide +kernel

def row6421 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6421 : row6421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6421 := by decide +kernel

theorem rowEval6421 (x : Key → ℝ) : Integer.Sparse.eval row6421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6421, Integer.Sparse.eval_collectBalanced, rawRowCheck6421]

def rawRow6422 : Integer.Sparse Key := [(key1681, -1), (key1683, -1), (key1689, 2), (key1548, -1), (key1556, -1), (key1575, 2), (key1624, 2), (key1593, -1), (key1633, -1), (key1542, 2), (key1569, -1), (key1618, -1), (key1918, 1), (key1920, 1), (key1926, -2), (key1318, 1), (key1326, 1), (key1426, -2), (key1624, -2), (key1444, 1), (key1633, 1), (key1312, -2), (key1420, 1), (key1618, 1), (key1903, -1), (key1920, -1), (key1911, 1), (key1926, 1), (key1472, 1), (key1683, 1), (key1480, -1), (key1689, -1), (key1298, -1), (key1326, -1), (key1393, 1), (key1556, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1542, -1)]

theorem rawRowCheck6422 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form6 = rawRow6422 := by decide +kernel

def row6422 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6422 : row6422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6422 := by decide +kernel

theorem rowEval6422 (x : Key → ℝ) : Integer.Sparse.eval row6422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6422, Integer.Sparse.eval_collectBalanced, rawRowCheck6422]

def rawRow6423 : Integer.Sparse Key := [(key1683, -1), (key1681, -1), (key1689, 2), (key1556, -1), (key1548, -1), (key1624, 2), (key1575, 2), (key1633, -1), (key1593, -1), (key1542, 2), (key1618, -1), (key1569, -1), (key1920, 1), (key1918, 1), (key1926, -2), (key1326, 1), (key1318, 1), (key1624, -2), (key1426, -2), (key1633, 1), (key1444, 1), (key1312, -2), (key1618, 1), (key1420, 1), (key1920, -1), (key1903, -1), (key1926, 1), (key1911, 1), (key1683, 1), (key1472, 1), (key1689, -1), (key1480, -1), (key1326, -1), (key1298, -1), (key1556, 1), (key1393, 1), (key1312, 1), (key1292, 1), (key1542, -1), (key1387, -1)]

theorem rawRowCheck6423 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form6 = rawRow6423 := by decide +kernel

def row6423 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6423 : row6423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6423 := by decide +kernel

theorem rowEval6423 (x : Key → ℝ) : Integer.Sparse.eval row6423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6423, Integer.Sparse.eval_collectBalanced, rawRowCheck6423]

def rawRow6424 : Integer.Sparse Key := [(key1683, -1), (key1689, -1), (key1681, 2), (key1624, -1), (key1633, -1), (key1556, 2), (key1593, 2), (key1548, -1), (key1575, -1), (key1618, 2), (key1542, -1), (key1569, -1), (key1920, 1), (key1926, 1), (key1918, -2), (key1624, 1), (key1633, 1), (key1326, -2), (key1444, -2), (key1318, 1), (key1426, 1), (key1618, -2), (key1312, 1), (key1420, 1), (key1899, -1), (key1911, -1), (key1896, 1), (key1903, 1), (key1354, 1), (key1480, 1), (key1351, -1), (key1472, -1), (key1556, -1), (key1593, -1), (key1326, 1), (key1444, 1), (key1542, 1), (key1569, 1), (key1312, -1), (key1420, -1)]

theorem rawRowCheck6424 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form6 = rawRow6424 := by decide +kernel

def row6424 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6424 : row6424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6424 := by decide +kernel

theorem rowEval6424 (x : Key → ℝ) : Integer.Sparse.eval row6424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6424, Integer.Sparse.eval_collectBalanced, rawRowCheck6424]

def rawRow6425 : Integer.Sparse Key := [(key1689, -1), (key1683, -1), (key1681, 2), (key1633, -1), (key1624, -1), (key1593, 2), (key1556, 2), (key1575, -1), (key1548, -1), (key1618, 2), (key1569, -1), (key1542, -1), (key1926, 1), (key1920, 1), (key1918, -2), (key1633, 1), (key1624, 1), (key1444, -2), (key1326, -2), (key1426, 1), (key1318, 1), (key1618, -2), (key1420, 1), (key1312, 1), (key1911, -1), (key1899, -1), (key1903, 1), (key1896, 1), (key1480, 1), (key1354, 1), (key1472, -1), (key1351, -1), (key1593, -1), (key1556, -1), (key1444, 1), (key1326, 1), (key1569, 1), (key1542, 1), (key1420, -1), (key1312, -1)]

theorem rawRowCheck6425 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form6 = rawRow6425 := by decide +kernel

def row6425 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6425 : row6425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6425 := by decide +kernel

theorem rowEval6425 (x : Key → ℝ) : Integer.Sparse.eval row6425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6425, Integer.Sparse.eval_collectBalanced, rawRowCheck6425]

def rawRow6426 : Integer.Sparse Key := [(key1896, -1), (key1896, -1), (key1899, 2), (key1903, -1), (key1903, -1), (key1918, 2), (key1918, 2), (key1920, -1), (key1920, -1), (key1911, 2), (key1926, -1), (key1926, -1), (key1351, 1), (key1351, 1), (key1354, -2), (key1472, 1), (key1472, 1), (key1681, -2), (key1681, -2), (key1683, 1), (key1683, 1), (key1480, -2), (key1689, 1), (key1689, 1), (key1318, -1), (key1318, -1), (key1326, 1), (key1326, 1), (key1548, 1), (key1548, 1), (key1556, -1), (key1556, -1), (key1426, -1), (key1426, -1), (key1575, 1), (key1575, 1), (key1444, 1), (key1444, 1), (key1593, -1), (key1593, -1)]

theorem rawRowCheck6426 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form6 = rawRow6426 := by decide +kernel

def row6426 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

theorem rowCheck6426 : row6426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6426 := by decide +kernel

theorem rowEval6426 (x : Key → ℝ) : Integer.Sparse.eval row6426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6426, Integer.Sparse.eval_collectBalanced, rawRowCheck6426]

def rawRow6427 : Integer.Sparse Key := [(key1896, -1), (key1899, -1), (key1896, 2), (key1918, -1), (key1920, -1), (key1903, 2), (key1920, 2), (key1903, -1), (key1918, -1), (key1926, 2), (key1911, -1), (key1926, -1), (key1351, 1), (key1354, 1), (key1351, -2), (key1681, 1), (key1683, 1), (key1472, -2), (key1683, -2), (key1472, 1), (key1681, 1), (key1689, -2), (key1480, 1), (key1689, 1), (key1298, -1), (key1326, -1), (key1298, 1), (key1318, 1), (key1393, 1), (key1556, 1), (key1393, -1), (key1548, -1), (key1575, -1), (key1624, -1), (key1426, 1), (key1624, 1), (key1593, 1), (key1633, 1), (key1444, -1), (key1633, -1)]

theorem rawRowCheck6427 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form6 = rawRow6427 := by decide +kernel

def row6427 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6427 : row6427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6427 := by decide +kernel

theorem rowEval6427 (x : Key → ℝ) : Integer.Sparse.eval row6427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6427, Integer.Sparse.eval_collectBalanced, rawRowCheck6427]

def rawRow6428 : Integer.Sparse Key := [(key1899, -1), (key1896, -1), (key1896, 2), (key1920, -1), (key1918, -1), (key1920, 2), (key1903, 2), (key1918, -1), (key1903, -1), (key1926, 2), (key1926, -1), (key1911, -1), (key1354, 1), (key1351, 1), (key1351, -2), (key1683, 1), (key1681, 1), (key1683, -2), (key1472, -2), (key1681, 1), (key1472, 1), (key1689, -2), (key1689, 1), (key1480, 1), (key1326, -1), (key1298, -1), (key1318, 1), (key1298, 1), (key1556, 1), (key1393, 1), (key1548, -1), (key1393, -1), (key1624, -1), (key1575, -1), (key1624, 1), (key1426, 1), (key1633, 1), (key1593, 1), (key1633, -1), (key1444, -1)]

theorem rawRowCheck6428 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form6 = rawRow6428 := by decide +kernel

def row6428 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6428 : row6428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6428 := by decide +kernel

theorem rowEval6428 (x : Key → ℝ) : Integer.Sparse.eval row6428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6428, Integer.Sparse.eval_collectBalanced, rawRowCheck6428]

def rawRow6429 : Integer.Sparse Key := [(key1903, -1), (key1903, -1), (key1911, 2), (key1896, -1), (key1896, -1), (key1918, 2), (key1918, 2), (key1926, -1), (key1926, -1), (key1899, 2), (key1920, -1), (key1920, -1), (key1472, 1), (key1472, 1), (key1480, -2), (key1351, 1), (key1351, 1), (key1681, -2), (key1681, -2), (key1689, 1), (key1689, 1), (key1354, -2), (key1683, 1), (key1683, 1), (key1426, -1), (key1426, -1), (key1444, 1), (key1444, 1), (key1575, 1), (key1575, 1), (key1593, -1), (key1593, -1), (key1318, -1), (key1318, -1), (key1548, 1), (key1548, 1), (key1326, 1), (key1326, 1), (key1556, -1), (key1556, -1)]

theorem rawRowCheck6429 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form6 = rawRow6429 := by decide +kernel

def row6429 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

theorem rowCheck6429 : row6429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6429 := by decide +kernel

theorem rowEval6429 (x : Key → ℝ) : Integer.Sparse.eval row6429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6429, Integer.Sparse.eval_collectBalanced, rawRowCheck6429]

def rawRow6430 : Integer.Sparse Key := [(key1903, -1), (key1911, -1), (key1903, 2), (key1918, -1), (key1926, -1), (key1896, 2), (key1926, 2), (key1896, -1), (key1918, -1), (key1920, 2), (key1899, -1), (key1920, -1), (key1472, 1), (key1480, 1), (key1472, -2), (key1681, 1), (key1689, 1), (key1351, -2), (key1689, -2), (key1351, 1), (key1681, 1), (key1683, -2), (key1354, 1), (key1683, 1), (key1393, -1), (key1444, -1), (key1393, 1), (key1426, 1), (key1298, 1), (key1593, 1), (key1298, -1), (key1575, -1), (key1548, -1), (key1633, -1), (key1318, 1), (key1633, 1), (key1556, 1), (key1624, 1), (key1326, -1), (key1624, -1)]

theorem rawRowCheck6430 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form6 = rawRow6430 := by decide +kernel

def row6430 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6430 : row6430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6430 := by decide +kernel

theorem rowEval6430 (x : Key → ℝ) : Integer.Sparse.eval row6430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6430, Integer.Sparse.eval_collectBalanced, rawRowCheck6430]

def rawRow6431 : Integer.Sparse Key := [(key1911, -1), (key1903, -1), (key1903, 2), (key1926, -1), (key1918, -1), (key1926, 2), (key1896, 2), (key1918, -1), (key1896, -1), (key1920, 2), (key1920, -1), (key1899, -1), (key1480, 1), (key1472, 1), (key1472, -2), (key1689, 1), (key1681, 1), (key1689, -2), (key1351, -2), (key1681, 1), (key1351, 1), (key1683, -2), (key1683, 1), (key1354, 1), (key1444, -1), (key1393, -1), (key1426, 1), (key1393, 1), (key1593, 1), (key1298, 1), (key1575, -1), (key1298, -1), (key1633, -1), (key1548, -1), (key1633, 1), (key1318, 1), (key1624, 1), (key1556, 1), (key1624, -1), (key1326, -1)]

theorem rawRowCheck6431 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form6 = rawRow6431 := by decide +kernel

def row6431 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6431 : row6431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6431 := by decide +kernel

theorem rowEval6431 (x : Key → ℝ) : Integer.Sparse.eval row6431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6431, Integer.Sparse.eval_collectBalanced, rawRowCheck6431]

def rawRow6432 : Integer.Sparse Key := [(key1918, -1), (key1920, -1), (key1926, 2), (key1896, -1), (key1899, -1), (key1903, 2), (key1920, 2), (key1911, -1), (key1926, -1), (key1896, 2), (key1903, -1), (key1918, -1), (key1681, 1), (key1683, 1), (key1689, -2), (key1351, 1), (key1354, 1), (key1472, -2), (key1683, -2), (key1480, 1), (key1689, 1), (key1351, -2), (key1472, 1), (key1681, 1), (key1575, -1), (key1624, -1), (key1593, 1), (key1633, 1), (key1426, 1), (key1624, 1), (key1444, -1), (key1633, -1), (key1298, -1), (key1326, -1), (key1393, 1), (key1556, 1), (key1298, 1), (key1318, 1), (key1393, -1), (key1548, -1)]

theorem rawRowCheck6432 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form6 = rawRow6432 := by decide +kernel

def row6432 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6432 : row6432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6432 := by decide +kernel

theorem rowEval6432 (x : Key → ℝ) : Integer.Sparse.eval row6432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6432, Integer.Sparse.eval_collectBalanced, rawRowCheck6432]

def rawRow6433 : Integer.Sparse Key := [(key1920, -1), (key1918, -1), (key1926, 2), (key1899, -1), (key1896, -1), (key1920, 2), (key1903, 2), (key1926, -1), (key1911, -1), (key1896, 2), (key1918, -1), (key1903, -1), (key1683, 1), (key1681, 1), (key1689, -2), (key1354, 1), (key1351, 1), (key1683, -2), (key1472, -2), (key1689, 1), (key1480, 1), (key1351, -2), (key1681, 1), (key1472, 1), (key1624, -1), (key1575, -1), (key1633, 1), (key1593, 1), (key1624, 1), (key1426, 1), (key1633, -1), (key1444, -1), (key1326, -1), (key1298, -1), (key1556, 1), (key1393, 1), (key1318, 1), (key1298, 1), (key1548, -1), (key1393, -1)]

theorem rawRowCheck6433 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form6 = rawRow6433 := by decide +kernel

def row6433 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6433 : row6433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6433 := by decide +kernel

theorem rowEval6433 (x : Key → ℝ) : Integer.Sparse.eval row6433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6433, Integer.Sparse.eval_collectBalanced, rawRowCheck6433]

def rawRow6434 : Integer.Sparse Key := [(key1918, -1), (key1926, -1), (key1920, 2), (key1903, -1), (key1911, -1), (key1896, 2), (key1926, 2), (key1899, -1), (key1920, -1), (key1903, 2), (key1896, -1), (key1918, -1), (key1681, 1), (key1689, 1), (key1683, -2), (key1472, 1), (key1480, 1), (key1351, -2), (key1689, -2), (key1354, 1), (key1683, 1), (key1472, -2), (key1351, 1), (key1681, 1), (key1548, -1), (key1633, -1), (key1556, 1), (key1624, 1), (key1318, 1), (key1633, 1), (key1326, -1), (key1624, -1), (key1393, -1), (key1444, -1), (key1298, 1), (key1593, 1), (key1393, 1), (key1426, 1), (key1298, -1), (key1575, -1)]

theorem rawRowCheck6434 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form6 = rawRow6434 := by decide +kernel

def row6434 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6434 : row6434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6434 := by decide +kernel

theorem rowEval6434 (x : Key → ℝ) : Integer.Sparse.eval row6434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6434, Integer.Sparse.eval_collectBalanced, rawRowCheck6434]

def rawRow6435 : Integer.Sparse Key := [(key1926, -1), (key1918, -1), (key1920, 2), (key1911, -1), (key1903, -1), (key1926, 2), (key1896, 2), (key1920, -1), (key1899, -1), (key1903, 2), (key1918, -1), (key1896, -1), (key1689, 1), (key1681, 1), (key1683, -2), (key1480, 1), (key1472, 1), (key1689, -2), (key1351, -2), (key1683, 1), (key1354, 1), (key1472, -2), (key1681, 1), (key1351, 1), (key1633, -1), (key1548, -1), (key1624, 1), (key1556, 1), (key1633, 1), (key1318, 1), (key1624, -1), (key1326, -1), (key1444, -1), (key1393, -1), (key1593, 1), (key1298, 1), (key1426, 1), (key1393, 1), (key1575, -1), (key1298, -1)]

theorem rawRowCheck6435 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form6 = rawRow6435 := by decide +kernel

def row6435 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1548, -1), (key1556, 1), (key1575, -1), (key1593, 1), (key1681, 2), (key1683, -1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, 1), (key1911, -1), (key1918, -2), (key1920, 1), (key1926, 1)]

theorem rowCheck6435 : row6435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6435 := by decide +kernel

theorem rowEval6435 (x : Key → ℝ) : Integer.Sparse.eval row6435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6435, Integer.Sparse.eval_collectBalanced, rawRowCheck6435]

def rawRow6436 : Integer.Sparse Key := [(key1920, -1), (key1926, -1), (key1918, 2), (key1920, -1), (key1926, -1), (key1899, 2), (key1911, 2), (key1896, -1), (key1903, -1), (key1918, 2), (key1896, -1), (key1903, -1), (key1683, 1), (key1689, 1), (key1681, -2), (key1683, 1), (key1689, 1), (key1354, -2), (key1480, -2), (key1351, 1), (key1472, 1), (key1681, -2), (key1351, 1), (key1472, 1), (key1556, -1), (key1593, -1), (key1548, 1), (key1575, 1), (key1326, 1), (key1444, 1), (key1318, -1), (key1426, -1), (key1556, -1), (key1593, -1), (key1326, 1), (key1444, 1), (key1548, 1), (key1575, 1), (key1318, -1), (key1426, -1)]

theorem rawRowCheck6436 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form6 = rawRow6436 := by decide +kernel

def row6436 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

theorem rowCheck6436 : row6436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6436 := by decide +kernel

theorem rowEval6436 (x : Key → ℝ) : Integer.Sparse.eval row6436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form6) x := by
  rw [rowCheck6436, Integer.Sparse.eval_collectBalanced, rawRowCheck6436]

def rawRow6437 : Integer.Sparse Key := [(key1926, -1), (key1920, -1), (key1918, 2), (key1926, -1), (key1920, -1), (key1911, 2), (key1899, 2), (key1903, -1), (key1896, -1), (key1918, 2), (key1903, -1), (key1896, -1), (key1689, 1), (key1683, 1), (key1681, -2), (key1689, 1), (key1683, 1), (key1480, -2), (key1354, -2), (key1472, 1), (key1351, 1), (key1681, -2), (key1472, 1), (key1351, 1), (key1593, -1), (key1556, -1), (key1575, 1), (key1548, 1), (key1444, 1), (key1326, 1), (key1426, -1), (key1318, -1), (key1593, -1), (key1556, -1), (key1444, 1), (key1326, 1), (key1575, 1), (key1548, 1), (key1426, -1), (key1318, -1)]

theorem rawRowCheck6437 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form6 = rawRow6437 := by decide +kernel

def row6437 : Integer.Sparse Key := [(key1318, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1426, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1548, 2), (key1556, -2), (key1575, 2), (key1593, -2), (key1681, -4), (key1683, 2), (key1689, 2), (key1896, -2), (key1899, 2), (key1903, -2), (key1911, 2), (key1918, 4), (key1920, -2), (key1926, -2)]

theorem rowCheck6437 : row6437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6437 := by decide +kernel

theorem rowEval6437 (x : Key → ℝ) : Integer.Sparse.eval row6437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6437, Integer.Sparse.eval_collectBalanced, rawRowCheck6437]

def rawRow6438 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2614, -2), (key2801, 1), (key2807, 1), (key2801, -2), (key2827, -2), (key2807, 1), (key2827, 1), (key3011, -2), (key3011, 1), (key3016, 1), (key2624, -1), (key2630, -1), (key2630, 1), (key2638, 1), (key2698, -1), (key2704, -1), (key2698, 1), (key2724, 1), (key2851, 1), (key2868, 1), (key2858, -1), (key2868, -1), (key3021, 1), (key3022, 1), (key3022, -1), (key3025, -1), (key2657, 2), (key2657, -1), (key2659, -1), (key2752, 2), (key2752, -1), (key2757, -1), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, 2), (key2922, 2)]

theorem rawRowCheck6438 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form7 = rawRow6438 := by decide +kernel

def row6438 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6438 : row6438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6438 := by decide +kernel

theorem rowEval6438 (x : Key → ℝ) : Integer.Sparse.eval row6438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6438, Integer.Sparse.eval_collectBalanced, rawRowCheck6438]

def rawRow6439 : Integer.Sparse Key := [(key2614, 1), (key2608, 1), (key2614, -2), (key2807, 1), (key2801, 1), (key2827, -2), (key2801, -2), (key2827, 1), (key2807, 1), (key3011, -2), (key3016, 1), (key3011, 1), (key2630, -1), (key2624, -1), (key2638, 1), (key2630, 1), (key2704, -1), (key2698, -1), (key2724, 1), (key2698, 1), (key2868, 1), (key2851, 1), (key2868, -1), (key2858, -1), (key3022, 1), (key3021, 1), (key3025, -1), (key3022, -1), (key2657, 2), (key2659, -1), (key2657, -1), (key2752, 2), (key2757, -1), (key2752, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, 2), (key2919, 2)]

theorem rawRowCheck6439 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form7 = rawRow6439 := by decide +kernel

def row6439 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6439 : row6439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6439 := by decide +kernel

theorem rowEval6439 (x : Key → ℝ) : Integer.Sparse.eval row6439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6439, Integer.Sparse.eval_collectBalanced, rawRowCheck6439]

def rawRow6440 : Integer.Sparse Key := [(key2614, 1), (key2614, 1), (key2608, -2), (key2827, 1), (key2827, 1), (key2807, -2), (key2807, -2), (key2801, 1), (key2801, 1), (key3016, -2), (key3011, 1), (key3011, 1), (key2638, -1), (key2638, -1), (key2624, 1), (key2624, 1), (key2724, -1), (key2724, -1), (key2704, 1), (key2704, 1), (key2858, 1), (key2858, 1), (key2851, -1), (key2851, -1), (key3025, 1), (key3025, 1), (key3021, -1), (key3021, -1), (key2659, 2), (key2657, -1), (key2657, -1), (key2757, 2), (key2752, -1), (key2752, -1), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, 2), (key2918, 2)]

theorem rawRowCheck6440 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form7 = rawRow6440 := by decide +kernel

def row6440 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3011, 2), (key3016, -2), (key3021, -2), (key3025, 2)]

theorem rowCheck6440 : row6440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6440 := by decide +kernel

theorem rowEval6440 (x : Key → ℝ) : Integer.Sparse.eval row6440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6440, Integer.Sparse.eval_collectBalanced, rawRowCheck6440]

def rawRow6441 : Integer.Sparse Key := [(key2801, 1), (key2807, 1), (key2827, -2), (key2608, 1), (key2614, 1), (key2801, -2), (key2827, -2), (key3011, 1), (key3016, 1), (key2614, -2), (key2807, 1), (key2827, 1), (key2698, -1), (key2704, -1), (key3021, 1), (key3022, 1), (key2624, -1), (key2630, -1), (key2851, 1), (key2868, 1), (key2698, 1), (key2724, 1), (key3022, -1), (key3025, -1), (key2630, 1), (key2638, 1), (key2858, -1), (key2868, -1), (key2752, 2), (key2918, -1), (key2919, -1), (key2657, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, 2), (key2922, 2)]

theorem rawRowCheck6441 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form7 = rawRow6441 := by decide +kernel

def row6441 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6441 : row6441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6441 := by decide +kernel

theorem rowEval6441 (x : Key → ℝ) : Integer.Sparse.eval row6441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6441, Integer.Sparse.eval_collectBalanced, rawRowCheck6441]

def rawRow6442 : Integer.Sparse Key := [(key2807, 1), (key2801, 1), (key2827, -2), (key2614, 1), (key2608, 1), (key2827, -2), (key2801, -2), (key3016, 1), (key3011, 1), (key2614, -2), (key2827, 1), (key2807, 1), (key2704, -1), (key2698, -1), (key3022, 1), (key3021, 1), (key2630, -1), (key2624, -1), (key2868, 1), (key2851, 1), (key2724, 1), (key2698, 1), (key3025, -1), (key3022, -1), (key2638, 1), (key2630, 1), (key2868, -1), (key2858, -1), (key2752, 2), (key2919, -1), (key2918, -1), (key2657, 2), (key2922, -1), (key2918, -1), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, 2), (key2919, 2)]

theorem rawRowCheck6442 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form7 = rawRow6442 := by decide +kernel

def row6442 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6442 : row6442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6442 := by decide +kernel

theorem rowEval6442 (x : Key → ℝ) : Integer.Sparse.eval row6442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6442, Integer.Sparse.eval_collectBalanced, rawRowCheck6442]

def rawRow6443 : Integer.Sparse Key := [(key2801, 1), (key2827, 1), (key2807, -2), (key2801, 1), (key2827, 1), (key2608, -2), (key3016, -2), (key2614, 1), (key2827, 1), (key2807, -2), (key2614, 1), (key2827, 1), (key2851, -1), (key3021, -1), (key2704, 1), (key2858, 1), (key2851, -1), (key3021, -1), (key2624, 1), (key3025, 1), (key2624, 1), (key3025, 1), (key2638, -1), (key2724, -1), (key2704, 1), (key2858, 1), (key2638, -1), (key2724, -1), (key2918, 2), (key2752, -1), (key2919, -1), (key2918, 2), (key2657, -1), (key2922, -1), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, 2), (key2757, 2)]

theorem rawRowCheck6443 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form7 = rawRow6443 := by decide +kernel

def row6443 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3016, -2), (key3021, -2), (key3025, 2)]

theorem rowCheck6443 : row6443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6443 := by decide +kernel

theorem rowEval6443 (x : Key → ℝ) : Integer.Sparse.eval row6443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6443, Integer.Sparse.eval_collectBalanced, rawRowCheck6443]

def rawRow6444 : Integer.Sparse Key := [(key2827, 1), (key2801, 1), (key2807, -2), (key2827, 1), (key2801, 1), (key3016, -2), (key2608, -2), (key2827, 1), (key2614, 1), (key2807, -2), (key2827, 1), (key2614, 1), (key3021, -1), (key2851, -1), (key2858, 1), (key2704, 1), (key3021, -1), (key2851, -1), (key3025, 1), (key2624, 1), (key3025, 1), (key2624, 1), (key2724, -1), (key2638, -1), (key2858, 1), (key2704, 1), (key2724, -1), (key2638, -1), (key2918, 2), (key2919, -1), (key2752, -1), (key2918, 2), (key2922, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, 2), (key2659, 2)]

theorem rawRowCheck6444 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form7 = rawRow6444 := by decide +kernel

def row6444 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3016, -2), (key3021, -2), (key3025, 2)]

theorem rowCheck6444 : row6444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6444 := by decide +kernel

theorem rowEval6444 (x : Key → ℝ) : Integer.Sparse.eval row6444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6444, Integer.Sparse.eval_collectBalanced, rawRowCheck6444]

def rawRow6445 : Integer.Sparse Key := [(key2807, 1), (key2827, 1), (key2801, -2), (key3011, 1), (key3016, 1), (key2614, -2), (key2827, -2), (key2608, 1), (key2801, 1), (key2827, -2), (key2614, 1), (key2807, 1), (key2858, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key2868, -1), (key3025, -1), (key2630, 1), (key3021, 1), (key2638, 1), (key3022, 1), (key2624, -1), (key2698, -1), (key2724, 1), (key2868, 1), (key2630, -1), (key2704, -1), (key2919, 2), (key2752, -1), (key2918, -1), (key2922, 2), (key2657, -1), (key2918, -1), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, 2), (key2752, 2)]

theorem rawRowCheck6445 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form7 = rawRow6445 := by decide +kernel

def row6445 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6445 : row6445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6445 := by decide +kernel

theorem rowEval6445 (x : Key → ℝ) : Integer.Sparse.eval row6445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6445, Integer.Sparse.eval_collectBalanced, rawRowCheck6445]

def rawRow6446 : Integer.Sparse Key := [(key2827, 1), (key2807, 1), (key2801, -2), (key3016, 1), (key3011, 1), (key2827, -2), (key2614, -2), (key2801, 1), (key2608, 1), (key2827, -2), (key2807, 1), (key2614, 1), (key3022, -1), (key2858, -1), (key2851, 1), (key2698, 1), (key3025, -1), (key2868, -1), (key3021, 1), (key2630, 1), (key3022, 1), (key2638, 1), (key2698, -1), (key2624, -1), (key2868, 1), (key2724, 1), (key2704, -1), (key2630, -1), (key2919, 2), (key2918, -1), (key2752, -1), (key2922, 2), (key2918, -1), (key2657, -1), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2657, 2)]

theorem rawRowCheck6446 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form7 = rawRow6446 := by decide +kernel

def row6446 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6446 : row6446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6446 := by decide +kernel

theorem rowEval6446 (x : Key → ℝ) : Integer.Sparse.eval row6446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6446, Integer.Sparse.eval_collectBalanced, rawRowCheck6446]

def rawRow6447 : Integer.Sparse Key := [(key3011, 1), (key3011, 1), (key3016, -2), (key2614, 1), (key2614, 1), (key2807, -2), (key2807, -2), (key2827, 1), (key2827, 1), (key2608, -2), (key2801, 1), (key2801, 1), (key2724, -1), (key2724, -1), (key3025, 1), (key3025, 1), (key2638, -1), (key2638, -1), (key2858, 1), (key2858, 1), (key2704, 1), (key2704, 1), (key3021, -1), (key3021, -1), (key2624, 1), (key2624, 1), (key2851, -1), (key2851, -1), (key2757, 2), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, -1), (key2919, -1), (key2657, -1), (key2657, -1), (key2752, -1), (key2752, -1), (key2918, 2), (key2918, 2)]

theorem rawRowCheck6447 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form7 = rawRow6447 := by decide +kernel

def row6447 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3011, 2), (key3016, -2), (key3021, -2), (key3025, 2)]

theorem rowCheck6447 : row6447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6447 := by decide +kernel

theorem rowEval6447 (x : Key → ℝ) : Integer.Sparse.eval row6447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6447, Integer.Sparse.eval_collectBalanced, rawRowCheck6447]

def rawRow6448 : Integer.Sparse Key := [(key3011, 1), (key3016, 1), (key3011, -2), (key2807, 1), (key2827, 1), (key2614, -2), (key2827, -2), (key2614, 1), (key2807, 1), (key2801, -2), (key2608, 1), (key2801, 1), (key2868, -1), (key3025, -1), (key2724, 1), (key2868, 1), (key2858, -1), (key3022, -1), (key2638, 1), (key3022, 1), (key2630, 1), (key3021, 1), (key2630, -1), (key2704, -1), (key2698, 1), (key2851, 1), (key2624, -1), (key2698, -1), (key2922, 2), (key2757, -1), (key2922, -1), (key2919, 2), (key2659, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2918, -1), (key2657, 2), (key2752, 2)]

theorem rawRowCheck6448 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form7 = rawRow6448 := by decide +kernel

def row6448 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6448 : row6448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6448 := by decide +kernel

theorem rowEval6448 (x : Key → ℝ) : Integer.Sparse.eval row6448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6448, Integer.Sparse.eval_collectBalanced, rawRowCheck6448]

def rawRow6449 : Integer.Sparse Key := [(key3016, 1), (key3011, 1), (key3011, -2), (key2827, 1), (key2807, 1), (key2827, -2), (key2614, -2), (key2807, 1), (key2614, 1), (key2801, -2), (key2801, 1), (key2608, 1), (key3025, -1), (key2868, -1), (key2868, 1), (key2724, 1), (key3022, -1), (key2858, -1), (key3022, 1), (key2638, 1), (key3021, 1), (key2630, 1), (key2704, -1), (key2630, -1), (key2851, 1), (key2698, 1), (key2698, -1), (key2624, -1), (key2922, 2), (key2922, -1), (key2757, -1), (key2919, 2), (key2919, -1), (key2659, -1), (key2918, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2752, 2), (key2657, 2)]

theorem rawRowCheck6449 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form7 = rawRow6449 := by decide +kernel

def row6449 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

theorem rowCheck6449 : row6449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6449 := by decide +kernel

theorem rowEval6449 (x : Key → ℝ) : Integer.Sparse.eval row6449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6449, Integer.Sparse.eval_collectBalanced, rawRowCheck6449]

def rawRow6450 : Integer.Sparse Key := [(key2624, 1), (key2630, 1), (key2638, -2), (key2698, 1), (key2704, 1), (key2851, -2), (key3021, -2), (key2858, 1), (key3022, 1), (key2724, -2), (key2868, 1), (key3025, 1), (key2608, -1), (key2614, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2724, 1), (key2801, 1), (key2827, 1), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3022, -1), (key3025, -1), (key2614, 2), (key2630, -1), (key2638, -1), (key2669, 2), (key2704, -1), (key2724, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, 2), (key2868, 2)]

theorem rawRowCheck6450 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form7 = rawRow6450 := by decide +kernel

def row6450 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3021, -2)]

theorem rowCheck6450 : row6450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6450 := by decide +kernel

theorem rowEval6450 (x : Key → ℝ) : Integer.Sparse.eval row6450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6450, Integer.Sparse.eval_collectBalanced, rawRowCheck6450]

def rawRow6451 : Integer.Sparse Key := [(key2630, 1), (key2624, 1), (key2638, -2), (key2704, 1), (key2698, 1), (key3021, -2), (key2851, -2), (key3022, 1), (key2858, 1), (key2724, -2), (key3025, 1), (key2868, 1), (key2614, -1), (key2608, -1), (key2659, 1), (key2657, 1), (key2669, -1), (key2663, -1), (key2724, 1), (key2698, 1), (key2827, 1), (key2801, 1), (key2922, -1), (key2919, -1), (key3009, 1), (key3007, 1), (key3025, -1), (key3022, -1), (key2614, 2), (key2638, -1), (key2630, -1), (key2669, 2), (key2724, -1), (key2704, -1), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, 2), (key2858, 2)]

theorem rawRowCheck6451 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form7 = rawRow6451 := by decide +kernel

def row6451 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3021, -2)]

theorem rowCheck6451 : row6451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6451 := by decide +kernel

theorem rowEval6451 (x : Key → ℝ) : Integer.Sparse.eval row6451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6451, Integer.Sparse.eval_collectBalanced, rawRowCheck6451]

def rawRow6452 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2624, -2), (key3021, 1), (key3022, 1), (key2704, -2), (key2858, -2), (key2698, 1), (key2851, 1), (key3025, -2), (key2724, 1), (key2868, 1), (key2657, -1), (key2659, -1), (key2608, 1), (key2624, 1), (key2724, -1), (key2757, -1), (key2669, 1), (key2752, 1), (key2792, 1), (key2919, 1), (key2778, -1), (key2801, -1), (key3016, 1), (key3025, 1), (key3007, -1), (key3011, -1), (key2638, 2), (key2614, -1), (key2630, -1), (key2724, 2), (key2669, -1), (key2704, -1), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, 2), (key2807, 2)]

theorem rawRowCheck6452 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form7 = rawRow6452 := by decide +kernel

def row6452 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3011, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6452 : row6452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6452 := by decide +kernel

theorem rowEval6452 (x : Key → ℝ) : Integer.Sparse.eval row6452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6452, Integer.Sparse.eval_collectBalanced, rawRowCheck6452]

def rawRow6453 : Integer.Sparse Key := [(key2638, 1), (key2630, 1), (key2624, -2), (key3022, 1), (key3021, 1), (key2858, -2), (key2704, -2), (key2851, 1), (key2698, 1), (key3025, -2), (key2868, 1), (key2724, 1), (key2659, -1), (key2657, -1), (key2624, 1), (key2608, 1), (key2757, -1), (key2724, -1), (key2752, 1), (key2669, 1), (key2919, 1), (key2792, 1), (key2801, -1), (key2778, -1), (key3025, 1), (key3016, 1), (key3011, -1), (key3007, -1), (key2638, 2), (key2630, -1), (key2614, -1), (key2724, 2), (key2704, -1), (key2669, -1), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, 2), (key2784, 2)]

theorem rawRowCheck6453 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form7 = rawRow6453 := by decide +kernel

def row6453 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3011, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6453 : row6453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6453 := by decide +kernel

theorem rowEval6453 (x : Key → ℝ) : Integer.Sparse.eval row6453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6453, Integer.Sparse.eval_collectBalanced, rawRowCheck6453]

def rawRow6454 : Integer.Sparse Key := [(key2698, 1), (key2704, 1), (key2724, -2), (key2624, 1), (key2630, 1), (key2851, -2), (key3021, -2), (key2868, 1), (key3025, 1), (key2638, -2), (key2858, 1), (key3022, 1), (key2663, -1), (key2669, -1), (key2724, 1), (key2757, 1), (key2608, -1), (key2614, -1), (key2801, 1), (key2827, 1), (key2698, 1), (key2724, 1), (key3022, -1), (key3025, -1), (key2657, 1), (key2659, 1), (key2919, -1), (key2922, -1), (key2669, 2), (key2784, -1), (key2792, -1), (key2614, 2), (key2807, -1), (key2827, -1), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, 2), (key2868, 2)]

theorem rawRowCheck6454 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form7 = rawRow6454 := by decide +kernel

def row6454 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2757, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

theorem rowCheck6454 : row6454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6454 := by decide +kernel

theorem rowEval6454 (x : Key → ℝ) : Integer.Sparse.eval row6454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6454, Integer.Sparse.eval_collectBalanced, rawRowCheck6454]

def rawRow6455 : Integer.Sparse Key := [(key2704, 1), (key2698, 1), (key2724, -2), (key2630, 1), (key2624, 1), (key3021, -2), (key2851, -2), (key3025, 1), (key2868, 1), (key2638, -2), (key3022, 1), (key2858, 1), (key2669, -1), (key2663, -1), (key2757, 1), (key2724, 1), (key2614, -1), (key2608, -1), (key2827, 1), (key2801, 1), (key2724, 1), (key2698, 1), (key3025, -1), (key3022, -1), (key2659, 1), (key2657, 1), (key2922, -1), (key2919, -1), (key2669, 2), (key2792, -1), (key2784, -1), (key2614, 2), (key2827, -1), (key2807, -1), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, 2), (key2858, 2)]

theorem rawRowCheck6455 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form7 = rawRow6455 := by decide +kernel

def row6455 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2757, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

theorem rowCheck6455 : row6455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6455 := by decide +kernel

theorem rowEval6455 (x : Key → ℝ) : Integer.Sparse.eval row6455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6455, Integer.Sparse.eval_collectBalanced, rawRowCheck6455]

def rawRow6456 : Integer.Sparse Key := [(key2698, 1), (key2724, 1), (key2704, -2), (key2851, 1), (key2868, 1), (key2624, -2), (key3025, -2), (key2630, 1), (key3021, 1), (key2858, -2), (key2638, 1), (key3022, 1), (key2698, -1), (key2724, -1), (key2669, 1), (key2752, 1), (key2801, -1), (key2827, -1), (key2608, 1), (key3016, 1), (key2624, 1), (key3025, 1), (key2638, -1), (key2724, -1), (key2752, 1), (key2919, 1), (key2659, -1), (key2757, -1), (key2784, 2), (key2669, -1), (key2792, -1), (key2807, 2), (key2614, -1), (key2827, -1), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, 2), (key2724, 2)]

theorem rawRowCheck6456 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form7 = rawRow6456 := by decide +kernel

def row6456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2752, 2), (key2757, -1), (key2784, 2), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6456 : row6456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6456 := by decide +kernel

theorem rowEval6456 (x : Key → ℝ) : Integer.Sparse.eval row6456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6456, Integer.Sparse.eval_collectBalanced, rawRowCheck6456]

def rawRow6457 : Integer.Sparse Key := [(key2724, 1), (key2698, 1), (key2704, -2), (key2868, 1), (key2851, 1), (key3025, -2), (key2624, -2), (key3021, 1), (key2630, 1), (key2858, -2), (key3022, 1), (key2638, 1), (key2724, -1), (key2698, -1), (key2752, 1), (key2669, 1), (key2827, -1), (key2801, -1), (key3016, 1), (key2608, 1), (key3025, 1), (key2624, 1), (key2724, -1), (key2638, -1), (key2919, 1), (key2752, 1), (key2757, -1), (key2659, -1), (key2784, 2), (key2792, -1), (key2669, -1), (key2807, 2), (key2827, -1), (key2614, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, 2), (key2638, 2)]

theorem rawRowCheck6457 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form7 = rawRow6457 := by decide +kernel

def row6457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2752, 2), (key2757, -1), (key2784, 2), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6457 : row6457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6457 := by decide +kernel

theorem rowEval6457 (x : Key → ℝ) : Integer.Sparse.eval row6457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6457, Integer.Sparse.eval_collectBalanced, rawRowCheck6457]

def rawRow6458 : Integer.Sparse Key := [(key2851, 1), (key2868, 1), (key2858, -2), (key2698, 1), (key2724, 1), (key2624, -2), (key3025, -2), (key2638, 1), (key3022, 1), (key2704, -2), (key2630, 1), (key3021, 1), (key2801, -1), (key2827, -1), (key2792, 1), (key2919, 1), (key2698, -1), (key2724, -1), (key2624, 1), (key3025, 1), (key2608, 1), (key3016, 1), (key2659, -1), (key2757, -1), (key2669, 1), (key2792, 1), (key2638, -1), (key2724, -1), (key2807, 2), (key2704, -1), (key2858, -1), (key2784, 2), (key2630, -1), (key2868, -1), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, 2), (key2724, 2)]

theorem rawRowCheck6458 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form7 = rawRow6458 := by decide +kernel

def row6458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2757, -1), (key2784, 2), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6458 : row6458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6458 := by decide +kernel

theorem rowEval6458 (x : Key → ℝ) : Integer.Sparse.eval row6458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6458, Integer.Sparse.eval_collectBalanced, rawRowCheck6458]

def rawRow6459 : Integer.Sparse Key := [(key2868, 1), (key2851, 1), (key2858, -2), (key2724, 1), (key2698, 1), (key3025, -2), (key2624, -2), (key3022, 1), (key2638, 1), (key2704, -2), (key3021, 1), (key2630, 1), (key2827, -1), (key2801, -1), (key2919, 1), (key2792, 1), (key2724, -1), (key2698, -1), (key3025, 1), (key2624, 1), (key3016, 1), (key2608, 1), (key2757, -1), (key2659, -1), (key2792, 1), (key2669, 1), (key2724, -1), (key2638, -1), (key2807, 2), (key2858, -1), (key2704, -1), (key2784, 2), (key2868, -1), (key2630, -1), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, 2), (key2638, 2)]

theorem rawRowCheck6459 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form7 = rawRow6459 := by decide +kernel

def row6459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2757, -1), (key2784, 2), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6459 : row6459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6459 := by decide +kernel

theorem rowEval6459 (x : Key → ℝ) : Integer.Sparse.eval row6459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6459, Integer.Sparse.eval_collectBalanced, rawRowCheck6459]

def rawRow6460 : Integer.Sparse Key := [(key2858, 1), (key2868, 1), (key2851, -2), (key3022, 1), (key3025, 1), (key2638, -2), (key2724, -2), (key2624, 1), (key2698, 1), (key3021, -2), (key2630, 1), (key2704, 1), (key2919, -1), (key2922, -1), (key2778, 1), (key2801, 1), (key3022, -1), (key3025, -1), (key2638, 1), (key2724, 1), (key2659, 1), (key2757, 1), (key2608, -1), (key2663, -1), (key2724, 1), (key2827, 1), (key2614, -1), (key2669, -1), (key2858, 2), (key2704, -1), (key2807, -1), (key2868, 2), (key2630, -1), (key2784, -1), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, 2), (key2669, 2)]

theorem rawRowCheck6460 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form7 = rawRow6460 := by decide +kernel

def row6460 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

theorem rowCheck6460 : row6460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6460 := by decide +kernel

theorem rowEval6460 (x : Key → ℝ) : Integer.Sparse.eval row6460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6460, Integer.Sparse.eval_collectBalanced, rawRowCheck6460]

def rawRow6461 : Integer.Sparse Key := [(key2868, 1), (key2858, 1), (key2851, -2), (key3025, 1), (key3022, 1), (key2724, -2), (key2638, -2), (key2698, 1), (key2624, 1), (key3021, -2), (key2704, 1), (key2630, 1), (key2922, -1), (key2919, -1), (key2801, 1), (key2778, 1), (key3025, -1), (key3022, -1), (key2724, 1), (key2638, 1), (key2757, 1), (key2659, 1), (key2663, -1), (key2608, -1), (key2827, 1), (key2724, 1), (key2669, -1), (key2614, -1), (key2858, 2), (key2807, -1), (key2704, -1), (key2868, 2), (key2784, -1), (key2630, -1), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, 2), (key2614, 2)]

theorem rawRowCheck6461 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form7 = rawRow6461 := by decide +kernel

def row6461 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

theorem rowCheck6461 : row6461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6461 := by decide +kernel

theorem rowEval6461 (x : Key → ℝ) : Integer.Sparse.eval row6461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6461, Integer.Sparse.eval_collectBalanced, rawRowCheck6461]

def rawRow6462 : Integer.Sparse Key := [(key3021, 1), (key3022, 1), (key3025, -2), (key2630, 1), (key2638, 1), (key2704, -2), (key2858, -2), (key2724, 1), (key2868, 1), (key2624, -2), (key2698, 1), (key2851, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3025, 1), (key2657, -1), (key2659, -1), (key2752, 1), (key2919, 1), (key2669, 1), (key2792, 1), (key2724, -1), (key2827, -1), (key2608, 1), (key2624, 1), (key2778, -1), (key2801, -1), (key2724, 2), (key2827, -1), (key2868, -1), (key2638, 2), (key2792, -1), (key2858, -1), (key2614, -1), (key2630, -1), (key2669, -1), (key2704, -1), (key2784, 2), (key2807, 2)]

theorem rawRowCheck6462 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form7 = rawRow6462 := by decide +kernel

def row6462 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6462 : row6462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6462 := by decide +kernel

theorem rowEval6462 (x : Key → ℝ) : Integer.Sparse.eval row6462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6462, Integer.Sparse.eval_collectBalanced, rawRowCheck6462]

def rawRow6463 : Integer.Sparse Key := [(key3022, 1), (key3021, 1), (key3025, -2), (key2638, 1), (key2630, 1), (key2858, -2), (key2704, -2), (key2868, 1), (key2724, 1), (key2624, -2), (key2851, 1), (key2698, 1), (key3009, -1), (key3007, -1), (key3025, 1), (key3016, 1), (key2659, -1), (key2657, -1), (key2919, 1), (key2752, 1), (key2792, 1), (key2669, 1), (key2827, -1), (key2724, -1), (key2624, 1), (key2608, 1), (key2801, -1), (key2778, -1), (key2724, 2), (key2868, -1), (key2827, -1), (key2638, 2), (key2858, -1), (key2792, -1), (key2630, -1), (key2614, -1), (key2704, -1), (key2669, -1), (key2807, 2), (key2784, 2)]

theorem rawRowCheck6463 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form7 = rawRow6463 := by decide +kernel

def row6463 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

theorem rowCheck6463 : row6463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6463 := by decide +kernel

theorem rowEval6463 (x : Key → ℝ) : Integer.Sparse.eval row6463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6463, Integer.Sparse.eval_collectBalanced, rawRowCheck6463]

def rawRow6464 : Integer.Sparse Key := [(key3022, 1), (key3025, 1), (key3021, -2), (key2858, 1), (key2868, 1), (key2638, -2), (key2724, -2), (key2630, 1), (key2704, 1), (key2851, -2), (key2624, 1), (key2698, 1), (key3022, -1), (key3025, -1), (key3007, 1), (key3011, 1), (key2919, -1), (key2922, -1), (key2659, 1), (key2757, 1), (key2638, 1), (key2724, 1), (key2614, -1), (key2669, -1), (key2778, 1), (key2801, 1), (key2608, -1), (key2663, -1), (key2868, 2), (key2724, -1), (key2827, -1), (key2858, 2), (key2638, -1), (key2792, -1), (key2704, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2614, 2), (key2669, 2)]

theorem rawRowCheck6464 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form7 = rawRow6464 := by decide +kernel

def row6464 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3011, 1), (key3021, -2)]

theorem rowCheck6464 : row6464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6464 := by decide +kernel

theorem rowEval6464 (x : Key → ℝ) : Integer.Sparse.eval row6464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6464, Integer.Sparse.eval_collectBalanced, rawRowCheck6464]

def rawRow6465 : Integer.Sparse Key := [(key3025, 1), (key3022, 1), (key3021, -2), (key2868, 1), (key2858, 1), (key2724, -2), (key2638, -2), (key2704, 1), (key2630, 1), (key2851, -2), (key2698, 1), (key2624, 1), (key3025, -1), (key3022, -1), (key3011, 1), (key3007, 1), (key2922, -1), (key2919, -1), (key2757, 1), (key2659, 1), (key2724, 1), (key2638, 1), (key2669, -1), (key2614, -1), (key2801, 1), (key2778, 1), (key2663, -1), (key2608, -1), (key2868, 2), (key2827, -1), (key2724, -1), (key2858, 2), (key2792, -1), (key2638, -1), (key2807, -1), (key2704, -1), (key2784, -1), (key2630, -1), (key2669, 2), (key2614, 2)]

theorem rawRowCheck6465 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form7 = rawRow6465 := by decide +kernel

def row6465 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3011, 1), (key3021, -2)]

theorem rowCheck6465 : row6465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6465 := by decide +kernel

theorem rowEval6465 (x : Key → ℝ) : Integer.Sparse.eval row6465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6465, Integer.Sparse.eval_collectBalanced, rawRowCheck6465]

def rawRow6466 : Integer.Sparse Key := [(key2657, 1), (key2657, 1), (key2659, -2), (key2752, 1), (key2752, 1), (key2918, -2), (key2918, -2), (key2919, 1), (key2919, 1), (key2757, -2), (key2922, 1), (key2922, 1), (key2614, -1), (key2614, -1), (key2638, 1), (key2638, 1), (key2669, -1), (key2669, -1), (key2784, 1), (key2784, 1), (key2807, 1), (key2807, 1), (key2858, -1), (key2858, -1), (key2724, 1), (key2724, 1), (key2868, -1), (key2868, -1), (key2608, 2), (key2624, -1), (key2624, -1), (key2663, 2), (key2698, -1), (key2698, -1), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, 2), (key2851, 2)]

theorem rawRowCheck6466 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form7 = rawRow6466 := by decide +kernel

def row6466 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

theorem rowCheck6466 : row6466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6466 := by decide +kernel

theorem rowEval6466 (x : Key → ℝ) : Integer.Sparse.eval row6466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6466, Integer.Sparse.eval_collectBalanced, rawRowCheck6466]

def rawRow6467 : Integer.Sparse Key := [(key2657, 1), (key2659, 1), (key2657, -2), (key2918, 1), (key2919, 1), (key2752, -2), (key2919, -2), (key2752, 1), (key2918, 1), (key2922, -2), (key2757, 1), (key2922, 1), (key2630, -1), (key2638, -1), (key2614, 1), (key2630, 1), (key2784, -1), (key2792, -1), (key2669, 1), (key2792, 1), (key2704, 1), (key2858, 1), (key2704, -1), (key2807, -1), (key2827, 1), (key2868, 1), (key2724, -1), (key2827, -1), (key2624, 2), (key2608, -1), (key2624, -1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, 2), (key2801, 2)]

theorem rawRowCheck6467 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form7 = rawRow6467 := by decide +kernel

def row6467 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6467 : row6467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6467 := by decide +kernel

theorem rowEval6467 (x : Key → ℝ) : Integer.Sparse.eval row6467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6467, Integer.Sparse.eval_collectBalanced, rawRowCheck6467]

def rawRow6468 : Integer.Sparse Key := [(key2659, 1), (key2657, 1), (key2657, -2), (key2919, 1), (key2918, 1), (key2919, -2), (key2752, -2), (key2918, 1), (key2752, 1), (key2922, -2), (key2922, 1), (key2757, 1), (key2638, -1), (key2630, -1), (key2630, 1), (key2614, 1), (key2792, -1), (key2784, -1), (key2792, 1), (key2669, 1), (key2858, 1), (key2704, 1), (key2807, -1), (key2704, -1), (key2868, 1), (key2827, 1), (key2827, -1), (key2724, -1), (key2624, 2), (key2624, -1), (key2608, -1), (key2698, 2), (key2698, -1), (key2663, -1), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, 2), (key2778, 2)]

theorem rawRowCheck6468 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form7 = rawRow6468 := by decide +kernel

def row6468 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6468 : row6468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6468 := by decide +kernel

theorem rowEval6468 (x : Key → ℝ) : Integer.Sparse.eval row6468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6468, Integer.Sparse.eval_collectBalanced, rawRowCheck6468]

def rawRow6469 : Integer.Sparse Key := [(key2752, 1), (key2752, 1), (key2757, -2), (key2657, 1), (key2657, 1), (key2918, -2), (key2918, -2), (key2922, 1), (key2922, 1), (key2659, -2), (key2919, 1), (key2919, 1), (key2669, -1), (key2669, -1), (key2724, 1), (key2724, 1), (key2614, -1), (key2614, -1), (key2807, 1), (key2807, 1), (key2784, 1), (key2784, 1), (key2868, -1), (key2868, -1), (key2638, 1), (key2638, 1), (key2858, -1), (key2858, -1), (key2663, 2), (key2698, -1), (key2698, -1), (key2608, 2), (key2801, -1), (key2801, -1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, 2), (key2851, 2)]

theorem rawRowCheck6469 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form7 = rawRow6469 := by decide +kernel

def row6469 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

theorem rowCheck6469 : row6469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6469 := by decide +kernel

theorem rowEval6469 (x : Key → ℝ) : Integer.Sparse.eval row6469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6469, Integer.Sparse.eval_collectBalanced, rawRowCheck6469]

def rawRow6470 : Integer.Sparse Key := [(key2752, 1), (key2757, 1), (key2752, -2), (key2918, 1), (key2922, 1), (key2657, -2), (key2922, -2), (key2657, 1), (key2918, 1), (key2919, -2), (key2659, 1), (key2919, 1), (key2704, -1), (key2724, -1), (key2669, 1), (key2704, 1), (key2807, -1), (key2827, -1), (key2614, 1), (key2827, 1), (key2630, 1), (key2868, 1), (key2630, -1), (key2784, -1), (key2792, 1), (key2858, 1), (key2638, -1), (key2792, -1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, 2), (key2608, -1), (key2801, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, 2), (key2698, 2)]

theorem rawRowCheck6470 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form7 = rawRow6470 := by decide +kernel

def row6470 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6470 : row6470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6470 := by decide +kernel

theorem rowEval6470 (x : Key → ℝ) : Integer.Sparse.eval row6470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6470, Integer.Sparse.eval_collectBalanced, rawRowCheck6470]

def rawRow6471 : Integer.Sparse Key := [(key2757, 1), (key2752, 1), (key2752, -2), (key2922, 1), (key2918, 1), (key2922, -2), (key2657, -2), (key2918, 1), (key2657, 1), (key2919, -2), (key2919, 1), (key2659, 1), (key2724, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2827, -1), (key2807, -1), (key2827, 1), (key2614, 1), (key2868, 1), (key2630, 1), (key2784, -1), (key2630, -1), (key2858, 1), (key2792, 1), (key2792, -1), (key2638, -1), (key2698, 2), (key2698, -1), (key2663, -1), (key2801, 2), (key2801, -1), (key2608, -1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, 2), (key2624, 2)]

theorem rawRowCheck6471 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form7 = rawRow6471 := by decide +kernel

def row6471 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6471 : row6471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6471 := by decide +kernel

theorem rowEval6471 (x : Key → ℝ) : Integer.Sparse.eval row6471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6471, Integer.Sparse.eval_collectBalanced, rawRowCheck6471]

def rawRow6472 : Integer.Sparse Key := [(key2918, 1), (key2919, 1), (key2922, -2), (key2657, 1), (key2659, 1), (key2752, -2), (key2919, -2), (key2757, 1), (key2922, 1), (key2657, -2), (key2752, 1), (key2918, 1), (key2784, -1), (key2792, -1), (key2827, 1), (key2868, 1), (key2630, -1), (key2638, -1), (key2704, 1), (key2858, 1), (key2669, 1), (key2792, 1), (key2724, -1), (key2827, -1), (key2614, 1), (key2630, 1), (key2704, -1), (key2807, -1), (key2778, 2), (key2801, -1), (key2851, -1), (key2624, 2), (key2698, -1), (key2851, -1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, 2), (key2801, 2)]

theorem rawRowCheck6472 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form7 = rawRow6472 := by decide +kernel

def row6472 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, -2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 4), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6472 : row6472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6472 := by decide +kernel

theorem rowEval6472 (x : Key → ℝ) : Integer.Sparse.eval row6472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6472, Integer.Sparse.eval_collectBalanced, rawRowCheck6472]

def rawRow6473 : Integer.Sparse Key := [(key2919, 1), (key2918, 1), (key2922, -2), (key2659, 1), (key2657, 1), (key2919, -2), (key2752, -2), (key2922, 1), (key2757, 1), (key2657, -2), (key2918, 1), (key2752, 1), (key2792, -1), (key2784, -1), (key2868, 1), (key2827, 1), (key2638, -1), (key2630, -1), (key2858, 1), (key2704, 1), (key2792, 1), (key2669, 1), (key2827, -1), (key2724, -1), (key2630, 1), (key2614, 1), (key2807, -1), (key2704, -1), (key2778, 2), (key2851, -1), (key2801, -1), (key2624, 2), (key2851, -1), (key2698, -1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, 2), (key2778, 2)]

theorem rawRowCheck6473 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form7 = rawRow6473 := by decide +kernel

def row6473 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, -2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 4), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6473 : row6473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6473 := by decide +kernel

theorem rowEval6473 (x : Key → ℝ) : Integer.Sparse.eval row6473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6473, Integer.Sparse.eval_collectBalanced, rawRowCheck6473]

def rawRow6474 : Integer.Sparse Key := [(key2918, 1), (key2922, 1), (key2919, -2), (key2752, 1), (key2757, 1), (key2657, -2), (key2922, -2), (key2659, 1), (key2919, 1), (key2752, -2), (key2657, 1), (key2918, 1), (key2807, -1), (key2827, -1), (key2792, 1), (key2858, 1), (key2704, -1), (key2724, -1), (key2630, 1), (key2868, 1), (key2614, 1), (key2827, 1), (key2638, -1), (key2792, -1), (key2669, 1), (key2704, 1), (key2630, -1), (key2784, -1), (key2801, 2), (key2778, -1), (key2851, -1), (key2698, 2), (key2624, -1), (key2851, -1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, 2), (key2698, 2)]

theorem rawRowCheck6474 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form7 = rawRow6474 := by decide +kernel

def row6474 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 3), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6474 : row6474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6474 := by decide +kernel

theorem rowEval6474 (x : Key → ℝ) : Integer.Sparse.eval row6474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form7) x := by
  rw [rowCheck6474, Integer.Sparse.eval_collectBalanced, rawRowCheck6474]

def rawRow6475 : Integer.Sparse Key := [(key2922, 1), (key2918, 1), (key2919, -2), (key2757, 1), (key2752, 1), (key2922, -2), (key2657, -2), (key2919, 1), (key2659, 1), (key2752, -2), (key2918, 1), (key2657, 1), (key2827, -1), (key2807, -1), (key2858, 1), (key2792, 1), (key2724, -1), (key2704, -1), (key2868, 1), (key2630, 1), (key2827, 1), (key2614, 1), (key2792, -1), (key2638, -1), (key2704, 1), (key2669, 1), (key2784, -1), (key2630, -1), (key2801, 2), (key2851, -1), (key2778, -1), (key2698, 2), (key2851, -1), (key2624, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, 2), (key2624, 2)]

theorem rawRowCheck6475 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form7 = rawRow6475 := by decide +kernel

def row6475 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 3), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

theorem rowCheck6475 : row6475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6475 := by decide +kernel

theorem rowEval6475 (x : Key → ℝ) : Integer.Sparse.eval row6475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6475, Integer.Sparse.eval_collectBalanced, rawRowCheck6475]

def rawRow6476 : Integer.Sparse Key := [(key2919, 1), (key2922, 1), (key2918, -2), (key2919, 1), (key2922, 1), (key2659, -2), (key2757, -2), (key2657, 1), (key2752, 1), (key2918, -2), (key2657, 1), (key2752, 1), (key2858, -1), (key2868, -1), (key2784, 1), (key2807, 1), (key2858, -1), (key2868, -1), (key2638, 1), (key2724, 1), (key2638, 1), (key2724, 1), (key2614, -1), (key2669, -1), (key2784, 1), (key2807, 1), (key2614, -1), (key2669, -1), (key2851, 2), (key2778, -1), (key2801, -1), (key2851, 2), (key2624, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, 2), (key2663, 2)]

theorem rawRowCheck6476 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form7 = rawRow6476 := by decide +kernel

def row6476 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

theorem rowCheck6476 : row6476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6476 := by decide +kernel

theorem rowEval6476 (x : Key → ℝ) : Integer.Sparse.eval row6476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6476, Integer.Sparse.eval_collectBalanced, rawRowCheck6476]

def rawRow6477 : Integer.Sparse Key := [(key2922, 1), (key2919, 1), (key2918, -2), (key2922, 1), (key2919, 1), (key2757, -2), (key2659, -2), (key2752, 1), (key2657, 1), (key2918, -2), (key2752, 1), (key2657, 1), (key2868, -1), (key2858, -1), (key2807, 1), (key2784, 1), (key2868, -1), (key2858, -1), (key2724, 1), (key2638, 1), (key2724, 1), (key2638, 1), (key2669, -1), (key2614, -1), (key2807, 1), (key2784, 1), (key2669, -1), (key2614, -1), (key2851, 2), (key2801, -1), (key2778, -1), (key2851, 2), (key2698, -1), (key2624, -1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, 2), (key2608, 2)]

theorem rawRowCheck6477 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form7 = rawRow6477 := by decide +kernel

def row6477 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

theorem rowCheck6477 : row6477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6477 := by decide +kernel

theorem rowEval6477 (x : Key → ℝ) : Integer.Sparse.eval row6477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form7) x := by
  rw [rowCheck6477, Integer.Sparse.eval_collectBalanced, rawRowCheck6477]

def rawRow6478 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -1), (key2632, -1), (key2640, 2), (key2640, 2), (key2644, -1), (key2644, -1), (key2658, 2), (key2660, -1), (key2660, -1), (key2671, 1), (key2671, 1), (key2676, -2), (key2706, 1), (key2706, 1), (key2726, -2), (key2726, -2), (key2732, 1), (key2732, 1), (key2753, -2), (key2758, 1), (key2758, 1), (key2794, -1), (key2794, -1), (key2798, 1), (key2798, 1), (key2829, 1), (key2829, 1), (key2835, -1), (key2835, -1), (key2860, -1), (key2860, -1), (key2870, 1), (key2870, 1), (key2920, 1), (key2920, 1), (key2923, -1), (key2923, -1)]

theorem rawRowCheck6478 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form0 = rawRow6478 := by decide +kernel

def row6478 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

theorem rowCheck6478 : row6478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6478 := by decide +kernel

theorem rowEval6478 (x : Key → ℝ) : Integer.Sparse.eval row6478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6478, Integer.Sparse.eval_collectBalanced, rawRowCheck6478]

def rawRow6479 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2616, 2), (key2640, -1), (key2644, -1), (key2632, 2), (key2644, 2), (key2632, -1), (key2640, -1), (key2660, 2), (key2658, -1), (key2660, -1), (key2671, 1), (key2676, 1), (key2671, -2), (key2726, 1), (key2732, 1), (key2706, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2758, -2), (key2753, 1), (key2758, 1), (key2786, -1), (key2798, -1), (key2786, 1), (key2794, 1), (key2809, 1), (key2835, 1), (key2809, -1), (key2829, -1), (key2870, -1), (key2885, -1), (key2860, 1), (key2885, 1), (key2923, 1), (key2927, 1), (key2920, -1), (key2927, -1)]

theorem rawRowCheck6479 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form0 = rawRow6479 := by decide +kernel

def row6479 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6479 : row6479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6479 := by decide +kernel

theorem rowEval6479 (x : Key → ℝ) : Integer.Sparse.eval row6479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6479, Integer.Sparse.eval_collectBalanced, rawRowCheck6479]

def rawRow6480 : Integer.Sparse Key := [(key2618, -1), (key2612, -1), (key2616, 2), (key2644, -1), (key2640, -1), (key2644, 2), (key2632, 2), (key2640, -1), (key2632, -1), (key2660, 2), (key2660, -1), (key2658, -1), (key2676, 1), (key2671, 1), (key2671, -2), (key2732, 1), (key2726, 1), (key2732, -2), (key2706, -2), (key2726, 1), (key2706, 1), (key2758, -2), (key2758, 1), (key2753, 1), (key2798, -1), (key2786, -1), (key2794, 1), (key2786, 1), (key2835, 1), (key2809, 1), (key2829, -1), (key2809, -1), (key2885, -1), (key2870, -1), (key2885, 1), (key2860, 1), (key2927, 1), (key2923, 1), (key2927, -1), (key2920, -1)]

theorem rawRowCheck6480 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form0 = rawRow6480 := by decide +kernel

def row6480 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6480 : row6480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6480 := by decide +kernel

theorem rowEval6480 (x : Key → ℝ) : Integer.Sparse.eval row6480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6480, Integer.Sparse.eval_collectBalanced, rawRowCheck6480]

def rawRow6481 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2641, 2), (key2612, -1), (key2616, -1), (key2640, 2), (key2640, 2), (key2660, -1), (key2660, -1), (key2621, 2), (key2644, -1), (key2644, -1), (key2706, 1), (key2706, 1), (key2753, -2), (key2671, 1), (key2671, 1), (key2726, -2), (key2726, -2), (key2758, 1), (key2758, 1), (key2676, -2), (key2732, 1), (key2732, 1), (key2860, -1), (key2860, -1), (key2920, 1), (key2920, 1), (key2870, 1), (key2870, 1), (key2923, -1), (key2923, -1), (key2794, -1), (key2794, -1), (key2829, 1), (key2829, 1), (key2798, 1), (key2798, 1), (key2835, -1), (key2835, -1)]

theorem rawRowCheck6481 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form0 = rawRow6481 := by decide +kernel

def row6481 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

theorem rowCheck6481 : row6481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6481 := by decide +kernel

theorem rowEval6481 (x : Key → ℝ) : Integer.Sparse.eval row6481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6481, Integer.Sparse.eval_collectBalanced, rawRowCheck6481]

def rawRow6482 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2628, 2), (key2646, -1), (key2653, -1), (key2612, 2), (key2653, 2), (key2616, -1), (key2640, -1), (key2644, 2), (key2621, -1), (key2644, -1), (key2706, 1), (key2753, 1), (key2706, -2), (key2726, 1), (key2758, 1), (key2671, -2), (key2758, -2), (key2671, 1), (key2726, 1), (key2732, -2), (key2676, 1), (key2732, 1), (key2809, -1), (key2920, -1), (key2809, 1), (key2860, 1), (key2786, 1), (key2923, 1), (key2786, -1), (key2870, -1), (key2829, -1), (key2927, -1), (key2794, 1), (key2927, 1), (key2835, 1), (key2885, 1), (key2798, -1), (key2885, -1)]

theorem rawRowCheck6482 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form0 = rawRow6482 := by decide +kernel

def row6482 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6482 : row6482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6482 := by decide +kernel

theorem rowEval6482 (x : Key → ℝ) : Integer.Sparse.eval row6482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6482, Integer.Sparse.eval_collectBalanced, rawRowCheck6482]

def rawRow6483 : Integer.Sparse Key := [(key2641, -1), (key2628, -1), (key2628, 2), (key2653, -1), (key2646, -1), (key2653, 2), (key2612, 2), (key2640, -1), (key2616, -1), (key2644, 2), (key2644, -1), (key2621, -1), (key2753, 1), (key2706, 1), (key2706, -2), (key2758, 1), (key2726, 1), (key2758, -2), (key2671, -2), (key2726, 1), (key2671, 1), (key2732, -2), (key2732, 1), (key2676, 1), (key2920, -1), (key2809, -1), (key2860, 1), (key2809, 1), (key2923, 1), (key2786, 1), (key2870, -1), (key2786, -1), (key2927, -1), (key2829, -1), (key2927, 1), (key2794, 1), (key2885, 1), (key2835, 1), (key2885, -1), (key2798, -1)]

theorem rawRowCheck6483 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form0 = rawRow6483 := by decide +kernel

def row6483 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6483 : row6483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6483 := by decide +kernel

theorem rowEval6483 (x : Key → ℝ) : Integer.Sparse.eval row6483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6483, Integer.Sparse.eval_collectBalanced, rawRowCheck6483]

def rawRow6484 : Integer.Sparse Key := [(key2646, -1), (key2648, -1), (key2653, 2), (key2612, -1), (key2618, -1), (key2628, 2), (key2648, 2), (key2641, -1), (key2653, -1), (key2616, 2), (key2632, -1), (key2640, -1), (key2726, 1), (key2732, 1), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, -2), (key2732, -2), (key2753, 1), (key2758, 1), (key2671, -2), (key2706, 1), (key2726, 1), (key2870, -1), (key2885, -1), (key2923, 1), (key2927, 1), (key2860, 1), (key2885, 1), (key2920, -1), (key2927, -1), (key2786, -1), (key2798, -1), (key2809, 1), (key2835, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2829, -1)]

theorem rawRowCheck6484 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form0 = rawRow6484 := by decide +kernel

def row6484 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6484 : row6484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6484 := by decide +kernel

theorem rowEval6484 (x : Key → ℝ) : Integer.Sparse.eval row6484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6484, Integer.Sparse.eval_collectBalanced, rawRowCheck6484]

def rawRow6485 : Integer.Sparse Key := [(key2648, -1), (key2646, -1), (key2653, 2), (key2618, -1), (key2612, -1), (key2648, 2), (key2628, 2), (key2653, -1), (key2641, -1), (key2616, 2), (key2640, -1), (key2632, -1), (key2732, 1), (key2726, 1), (key2758, -2), (key2676, 1), (key2671, 1), (key2732, -2), (key2706, -2), (key2758, 1), (key2753, 1), (key2671, -2), (key2726, 1), (key2706, 1), (key2885, -1), (key2870, -1), (key2927, 1), (key2923, 1), (key2885, 1), (key2860, 1), (key2927, -1), (key2920, -1), (key2798, -1), (key2786, -1), (key2835, 1), (key2809, 1), (key2794, 1), (key2786, 1), (key2829, -1), (key2809, -1)]

theorem rawRowCheck6485 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form0 = rawRow6485 := by decide +kernel

def row6485 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6485 : row6485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6485 := by decide +kernel

theorem rowEval6485 (x : Key → ℝ) : Integer.Sparse.eval row6485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6485, Integer.Sparse.eval_collectBalanced, rawRowCheck6485]

def rawRow6486 : Integer.Sparse Key := [(key2646, -1), (key2653, -1), (key2648, 2), (key2628, -1), (key2641, -1), (key2612, 2), (key2653, 2), (key2618, -1), (key2648, -1), (key2632, 2), (key2616, -1), (key2640, -1), (key2726, 1), (key2758, 1), (key2732, -2), (key2706, 1), (key2753, 1), (key2671, -2), (key2758, -2), (key2676, 1), (key2732, 1), (key2706, -2), (key2671, 1), (key2726, 1), (key2829, -1), (key2927, -1), (key2835, 1), (key2885, 1), (key2794, 1), (key2927, 1), (key2798, -1), (key2885, -1), (key2809, -1), (key2920, -1), (key2786, 1), (key2923, 1), (key2809, 1), (key2860, 1), (key2786, -1), (key2870, -1)]

theorem rawRowCheck6486 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form0 = rawRow6486 := by decide +kernel

def row6486 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6486 : row6486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6486 := by decide +kernel

theorem rowEval6486 (x : Key → ℝ) : Integer.Sparse.eval row6486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6486, Integer.Sparse.eval_collectBalanced, rawRowCheck6486]

def rawRow6487 : Integer.Sparse Key := [(key2653, -1), (key2646, -1), (key2648, 2), (key2641, -1), (key2628, -1), (key2653, 2), (key2612, 2), (key2648, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2616, -1), (key2758, 1), (key2726, 1), (key2732, -2), (key2753, 1), (key2706, 1), (key2758, -2), (key2671, -2), (key2732, 1), (key2676, 1), (key2706, -2), (key2726, 1), (key2671, 1), (key2927, -1), (key2829, -1), (key2885, 1), (key2835, 1), (key2927, 1), (key2794, 1), (key2885, -1), (key2798, -1), (key2920, -1), (key2809, -1), (key2923, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, -1), (key2786, -1)]

theorem rawRowCheck6487 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form0 = rawRow6487 := by decide +kernel

def row6487 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

theorem rowCheck6487 : row6487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6487 := by decide +kernel

theorem rowEval6487 (x : Key → ℝ) : Integer.Sparse.eval row6487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6487, Integer.Sparse.eval_collectBalanced, rawRowCheck6487]

def rawRow6488 : Integer.Sparse Key := [(key2648, -1), (key2653, -1), (key2646, 2), (key2648, -1), (key2653, -1), (key2618, 2), (key2641, 2), (key2612, -1), (key2628, -1), (key2640, 2), (key2616, -1), (key2632, -1), (key2732, 1), (key2758, 1), (key2726, -2), (key2732, 1), (key2758, 1), (key2676, -2), (key2753, -2), (key2671, 1), (key2706, 1), (key2726, -2), (key2671, 1), (key2706, 1), (key2835, -1), (key2923, -1), (key2829, 1), (key2870, 1), (key2798, 1), (key2920, 1), (key2794, -1), (key2860, -1), (key2835, -1), (key2923, -1), (key2798, 1), (key2920, 1), (key2829, 1), (key2870, 1), (key2794, -1), (key2860, -1)]

theorem rawRowCheck6488 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form0 = rawRow6488 := by decide +kernel

def row6488 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

theorem rowCheck6488 : row6488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6488 := by decide +kernel

theorem rowEval6488 (x : Key → ℝ) : Integer.Sparse.eval row6488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6488, Integer.Sparse.eval_collectBalanced, rawRowCheck6488]

def rawRow6489 : Integer.Sparse Key := [(key2653, -1), (key2648, -1), (key2646, 2), (key2653, -1), (key2648, -1), (key2641, 2), (key2618, 2), (key2628, -1), (key2612, -1), (key2640, 2), (key2632, -1), (key2616, -1), (key2758, 1), (key2732, 1), (key2726, -2), (key2758, 1), (key2732, 1), (key2753, -2), (key2676, -2), (key2706, 1), (key2671, 1), (key2726, -2), (key2706, 1), (key2671, 1), (key2923, -1), (key2835, -1), (key2870, 1), (key2829, 1), (key2920, 1), (key2798, 1), (key2860, -1), (key2794, -1), (key2923, -1), (key2835, -1), (key2920, 1), (key2798, 1), (key2870, 1), (key2829, 1), (key2860, -1), (key2794, -1)]

theorem rawRowCheck6489 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form0 = rawRow6489 := by decide +kernel

def row6489 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

theorem rowCheck6489 : row6489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6489 := by decide +kernel

theorem rowEval6489 (x : Key → ℝ) : Integer.Sparse.eval row6489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6489, Integer.Sparse.eval_collectBalanced, rawRowCheck6489]

def rawRow6490 : Integer.Sparse Key := [(key2938, -1), (key2943, -1), (key2936, 2), (key2997, -1), (key2998, -1), (key2950, 2), (key2976, 2), (key2948, -1), (key2972, -1), (key3000, 2), (key2960, -1), (key2983, -1), (key2648, 1), (key2653, 1), (key2646, -2), (key2997, 1), (key2998, 1), (key2737, -2), (key2897, -2), (key2735, 1), (key2893, 1), (key3000, -2), (key2747, 1), (key2904, 1), (key2618, -1), (key2641, -1), (key2612, 1), (key2628, 1), (key2673, 1), (key2795, 1), (key2667, -1), (key2782, -1), (key2950, -1), (key2976, -1), (key2737, 1), (key2897, 1), (key2960, 1), (key2983, 1), (key2747, -1), (key2904, -1)]

theorem rawRowCheck6490 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form0 = rawRow6490 := by decide +kernel

def row6490 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6490 : row6490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6490 := by decide +kernel

theorem rowEval6490 (x : Key → ℝ) : Integer.Sparse.eval row6490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6490, Integer.Sparse.eval_collectBalanced, rawRowCheck6490]

def rawRow6491 : Integer.Sparse Key := [(key2943, -1), (key2938, -1), (key2936, 2), (key2998, -1), (key2997, -1), (key2976, 2), (key2950, 2), (key2972, -1), (key2948, -1), (key3000, 2), (key2983, -1), (key2960, -1), (key2653, 1), (key2648, 1), (key2646, -2), (key2998, 1), (key2997, 1), (key2897, -2), (key2737, -2), (key2893, 1), (key2735, 1), (key3000, -2), (key2904, 1), (key2747, 1), (key2641, -1), (key2618, -1), (key2628, 1), (key2612, 1), (key2795, 1), (key2673, 1), (key2782, -1), (key2667, -1), (key2976, -1), (key2950, -1), (key2897, 1), (key2737, 1), (key2983, 1), (key2960, 1), (key2904, -1), (key2747, -1)]

theorem rawRowCheck6491 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form0 = rawRow6491 := by decide +kernel

def row6491 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6491 : row6491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6491 := by decide +kernel

theorem rowEval6491 (x : Key → ℝ) : Integer.Sparse.eval row6491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6491, Integer.Sparse.eval_collectBalanced, rawRowCheck6491]

def rawRow6492 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2950, 2), (key2972, -1), (key2983, -1), (key2936, 2), (key3000, 2), (key2938, -1), (key2997, -1), (key2976, 2), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2737, -2), (key2893, 1), (key2904, 1), (key2646, -2), (key3000, -2), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, 1), (key2998, 1), (key2667, -1), (key2747, -1), (key2673, 1), (key2737, 1), (key2612, 1), (key2960, 1), (key2618, -1), (key2950, -1), (key2782, -1), (key2904, -1), (key2628, 1), (key2983, 1), (key2795, 1), (key2897, 1), (key2641, -1), (key2976, -1)]

theorem rawRowCheck6492 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form0 = rawRow6492 := by decide +kernel

def row6492 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6492 : row6492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6492 := by decide +kernel

theorem rowEval6492 (x : Key → ℝ) : Integer.Sparse.eval row6492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6492, Integer.Sparse.eval_collectBalanced, rawRowCheck6492]

def rawRow6493 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2950, 2), (key2983, -1), (key2972, -1), (key3000, 2), (key2936, 2), (key2997, -1), (key2938, -1), (key2976, 2), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key2737, -2), (key2904, 1), (key2893, 1), (key3000, -2), (key2646, -2), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, 1), (key2653, 1), (key2747, -1), (key2667, -1), (key2737, 1), (key2673, 1), (key2960, 1), (key2612, 1), (key2950, -1), (key2618, -1), (key2904, -1), (key2782, -1), (key2983, 1), (key2628, 1), (key2897, 1), (key2795, 1), (key2976, -1), (key2641, -1)]

theorem rawRowCheck6493 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form0 = rawRow6493 := by decide +kernel

def row6493 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6493 : row6493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6493 := by decide +kernel

theorem rowEval6493 (x : Key → ℝ) : Integer.Sparse.eval row6493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6493, Integer.Sparse.eval_collectBalanced, rawRowCheck6493]

def rawRow6494 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2976, 2), (key2948, -1), (key2960, -1), (key2936, 2), (key3000, 2), (key2943, -1), (key2998, -1), (key2950, 2), (key2938, -1), (key2997, -1), (key2893, 1), (key2904, 1), (key2897, -2), (key2735, 1), (key2747, 1), (key2646, -2), (key3000, -2), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, 1), (key2997, 1), (key2782, -1), (key2904, -1), (key2795, 1), (key2897, 1), (key2628, 1), (key2983, 1), (key2641, -1), (key2976, -1), (key2667, -1), (key2747, -1), (key2612, 1), (key2960, 1), (key2673, 1), (key2737, 1), (key2618, -1), (key2950, -1)]

theorem rawRowCheck6494 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form0 = rawRow6494 := by decide +kernel

def row6494 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6494 : row6494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6494 := by decide +kernel

theorem rowEval6494 (x : Key → ℝ) : Integer.Sparse.eval row6494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6494, Integer.Sparse.eval_collectBalanced, rawRowCheck6494]

def rawRow6495 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2976, 2), (key2960, -1), (key2948, -1), (key3000, 2), (key2936, 2), (key2998, -1), (key2943, -1), (key2950, 2), (key2997, -1), (key2938, -1), (key2904, 1), (key2893, 1), (key2897, -2), (key2747, 1), (key2735, 1), (key3000, -2), (key2646, -2), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, 1), (key2648, 1), (key2904, -1), (key2782, -1), (key2897, 1), (key2795, 1), (key2983, 1), (key2628, 1), (key2976, -1), (key2641, -1), (key2747, -1), (key2667, -1), (key2960, 1), (key2612, 1), (key2737, 1), (key2673, 1), (key2950, -1), (key2618, -1)]

theorem rawRowCheck6495 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form0 = rawRow6495 := by decide +kernel

def row6495 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6495 : row6495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6495 := by decide +kernel

theorem rowEval6495 (x : Key → ℝ) : Integer.Sparse.eval row6495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck6495, Integer.Sparse.eval_collectBalanced, rawRowCheck6495]

def rawRow6496 : Integer.Sparse Key := [(key2997, -1), (key2998, -1), (key3000, 2), (key2938, -1), (key2943, -1), (key2950, 2), (key2976, 2), (key2960, -1), (key2983, -1), (key2936, 2), (key2948, -1), (key2972, -1), (key2997, 1), (key2998, 1), (key3000, -2), (key2648, 1), (key2653, 1), (key2737, -2), (key2897, -2), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, 1), (key2893, 1), (key2950, -1), (key2976, -1), (key2960, 1), (key2983, 1), (key2737, 1), (key2897, 1), (key2747, -1), (key2904, -1), (key2618, -1), (key2641, -1), (key2673, 1), (key2795, 1), (key2612, 1), (key2628, 1), (key2667, -1), (key2782, -1)]

theorem rawRowCheck6496 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form0 = rawRow6496 := by decide +kernel

def row6496 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6496 : row6496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6496 := by decide +kernel

theorem rowEval6496 (x : Key → ℝ) : Integer.Sparse.eval row6496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck6496, Integer.Sparse.eval_collectBalanced, rawRowCheck6496]

def rawRow6497 : Integer.Sparse Key := [(key2998, -1), (key2997, -1), (key3000, 2), (key2943, -1), (key2938, -1), (key2976, 2), (key2950, 2), (key2983, -1), (key2960, -1), (key2936, 2), (key2972, -1), (key2948, -1), (key2998, 1), (key2997, 1), (key3000, -2), (key2653, 1), (key2648, 1), (key2897, -2), (key2737, -2), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, 1), (key2735, 1), (key2976, -1), (key2950, -1), (key2983, 1), (key2960, 1), (key2897, 1), (key2737, 1), (key2904, -1), (key2747, -1), (key2641, -1), (key2618, -1), (key2795, 1), (key2673, 1), (key2628, 1), (key2612, 1), (key2782, -1), (key2667, -1)]

theorem rawRowCheck6497 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form0 = rawRow6497 := by decide +kernel

def row6497 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

theorem rowCheck6497 : row6497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6497 := by decide +kernel

theorem rowEval6497 (x : Key → ℝ) : Integer.Sparse.eval row6497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck6497, Integer.Sparse.eval_collectBalanced, rawRowCheck6497]

def rawRow6498 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1303, 2), (key1316, -1), (key1316, -1), (key1337, 2), (key1337, 2), (key1340, -1), (key1340, -1), (key1330, 2), (key1346, -1), (key1346, -1), (key1391, 1), (key1391, 1), (key1398, -2), (key1546, 1), (key1546, 1), (key1772, -2), (key1772, -2), (key1775, 1), (key1775, 1), (key1560, -2), (key1781, 1), (key1781, 1), (key1455, -1), (key1455, -1), (key1458, 1), (key1458, 1), (key1788, 1), (key1788, 1), (key1791, -1), (key1791, -1), (key1655, -1), (key1655, -1), (key1813, 1), (key1813, 1), (key1660, 1), (key1660, 1), (key1818, -1), (key1818, -1)]

theorem rawRowCheck6498 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form1 = rawRow6498 := by decide +kernel

def row6498 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

theorem rowCheck6498 : row6498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6498 := by decide +kernel

theorem rowEval6498 (x : Key → ℝ) : Integer.Sparse.eval row6498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6498, Integer.Sparse.eval_collectBalanced, rawRowCheck6498]

def rawRow6499 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1296, 2), (key1337, -1), (key1340, -1), (key1316, 2), (key1340, 2), (key1316, -1), (key1337, -1), (key1346, 2), (key1330, -1), (key1346, -1), (key1391, 1), (key1398, 1), (key1391, -2), (key1772, 1), (key1775, 1), (key1546, -2), (key1775, -2), (key1546, 1), (key1772, 1), (key1781, -2), (key1560, 1), (key1781, 1), (key1424, -1), (key1458, -1), (key1424, 1), (key1455, 1), (key1573, 1), (key1791, 1), (key1573, -1), (key1788, -1), (key1813, -1), (key1840, -1), (key1655, 1), (key1840, 1), (key1818, 1), (key1842, 1), (key1660, -1), (key1842, -1)]

theorem rawRowCheck6499 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form1 = rawRow6499 := by decide +kernel

def row6499 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6499 : row6499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6499 := by decide +kernel

theorem rowEval6499 (x : Key → ℝ) : Integer.Sparse.eval row6499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6499, Integer.Sparse.eval_collectBalanced, rawRowCheck6499]

def rawRow6500 : Integer.Sparse Key := [(key1303, -1), (key1296, -1), (key1296, 2), (key1340, -1), (key1337, -1), (key1340, 2), (key1316, 2), (key1337, -1), (key1316, -1), (key1346, 2), (key1346, -1), (key1330, -1), (key1398, 1), (key1391, 1), (key1391, -2), (key1775, 1), (key1772, 1), (key1775, -2), (key1546, -2), (key1772, 1), (key1546, 1), (key1781, -2), (key1781, 1), (key1560, 1), (key1458, -1), (key1424, -1), (key1455, 1), (key1424, 1), (key1791, 1), (key1573, 1), (key1788, -1), (key1573, -1), (key1840, -1), (key1813, -1), (key1840, 1), (key1655, 1), (key1842, 1), (key1818, 1), (key1842, -1), (key1660, -1)]

theorem rawRowCheck6500 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form1 = rawRow6500 := by decide +kernel

def row6500 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6500 : row6500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6500 := by decide +kernel

theorem rowEval6500 (x : Key → ℝ) : Integer.Sparse.eval row6500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6500, Integer.Sparse.eval_collectBalanced, rawRowCheck6500]

def rawRow6501 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1330, 2), (key1296, -1), (key1296, -1), (key1337, 2), (key1337, 2), (key1346, -1), (key1346, -1), (key1303, 2), (key1340, -1), (key1340, -1), (key1546, 1), (key1546, 1), (key1560, -2), (key1391, 1), (key1391, 1), (key1772, -2), (key1772, -2), (key1781, 1), (key1781, 1), (key1398, -2), (key1775, 1), (key1775, 1), (key1655, -1), (key1655, -1), (key1660, 1), (key1660, 1), (key1813, 1), (key1813, 1), (key1818, -1), (key1818, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1458, 1), (key1458, 1), (key1791, -1), (key1791, -1)]

theorem rawRowCheck6501 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form1 = rawRow6501 := by decide +kernel

def row6501 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

theorem rowCheck6501 : row6501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6501 := by decide +kernel

theorem rowEval6501 (x : Key → ℝ) : Integer.Sparse.eval row6501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6501, Integer.Sparse.eval_collectBalanced, rawRowCheck6501]

def rawRow6502 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1316, 2), (key1337, -1), (key1346, -1), (key1296, 2), (key1346, 2), (key1296, -1), (key1337, -1), (key1340, 2), (key1303, -1), (key1340, -1), (key1546, 1), (key1560, 1), (key1546, -2), (key1772, 1), (key1781, 1), (key1391, -2), (key1781, -2), (key1391, 1), (key1772, 1), (key1775, -2), (key1398, 1), (key1775, 1), (key1573, -1), (key1660, -1), (key1573, 1), (key1655, 1), (key1424, 1), (key1818, 1), (key1424, -1), (key1813, -1), (key1788, -1), (key1842, -1), (key1455, 1), (key1842, 1), (key1791, 1), (key1840, 1), (key1458, -1), (key1840, -1)]

theorem rawRowCheck6502 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form1 = rawRow6502 := by decide +kernel

def row6502 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6502 : row6502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6502 := by decide +kernel

theorem rowEval6502 (x : Key → ℝ) : Integer.Sparse.eval row6502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6502, Integer.Sparse.eval_collectBalanced, rawRowCheck6502]

def rawRow6503 : Integer.Sparse Key := [(key1330, -1), (key1316, -1), (key1316, 2), (key1346, -1), (key1337, -1), (key1346, 2), (key1296, 2), (key1337, -1), (key1296, -1), (key1340, 2), (key1340, -1), (key1303, -1), (key1560, 1), (key1546, 1), (key1546, -2), (key1781, 1), (key1772, 1), (key1781, -2), (key1391, -2), (key1772, 1), (key1391, 1), (key1775, -2), (key1775, 1), (key1398, 1), (key1660, -1), (key1573, -1), (key1655, 1), (key1573, 1), (key1818, 1), (key1424, 1), (key1813, -1), (key1424, -1), (key1842, -1), (key1788, -1), (key1842, 1), (key1455, 1), (key1840, 1), (key1791, 1), (key1840, -1), (key1458, -1)]

theorem rawRowCheck6503 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form1 = rawRow6503 := by decide +kernel

def row6503 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6503 : row6503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6503 := by decide +kernel

theorem rowEval6503 (x : Key → ℝ) : Integer.Sparse.eval row6503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6503, Integer.Sparse.eval_collectBalanced, rawRowCheck6503]

def rawRow6504 : Integer.Sparse Key := [(key1337, -1), (key1340, -1), (key1346, 2), (key1296, -1), (key1303, -1), (key1316, 2), (key1340, 2), (key1330, -1), (key1346, -1), (key1296, 2), (key1316, -1), (key1337, -1), (key1772, 1), (key1775, 1), (key1781, -2), (key1391, 1), (key1398, 1), (key1546, -2), (key1775, -2), (key1560, 1), (key1781, 1), (key1391, -2), (key1546, 1), (key1772, 1), (key1813, -1), (key1840, -1), (key1818, 1), (key1842, 1), (key1655, 1), (key1840, 1), (key1660, -1), (key1842, -1), (key1424, -1), (key1458, -1), (key1573, 1), (key1791, 1), (key1424, 1), (key1455, 1), (key1573, -1), (key1788, -1)]

theorem rawRowCheck6504 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form1 = rawRow6504 := by decide +kernel

def row6504 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6504 : row6504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6504 := by decide +kernel

theorem rowEval6504 (x : Key → ℝ) : Integer.Sparse.eval row6504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6504, Integer.Sparse.eval_collectBalanced, rawRowCheck6504]

def rawRow6505 : Integer.Sparse Key := [(key1340, -1), (key1337, -1), (key1346, 2), (key1303, -1), (key1296, -1), (key1340, 2), (key1316, 2), (key1346, -1), (key1330, -1), (key1296, 2), (key1337, -1), (key1316, -1), (key1775, 1), (key1772, 1), (key1781, -2), (key1398, 1), (key1391, 1), (key1775, -2), (key1546, -2), (key1781, 1), (key1560, 1), (key1391, -2), (key1772, 1), (key1546, 1), (key1840, -1), (key1813, -1), (key1842, 1), (key1818, 1), (key1840, 1), (key1655, 1), (key1842, -1), (key1660, -1), (key1458, -1), (key1424, -1), (key1791, 1), (key1573, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

theorem rawRowCheck6505 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form1 = rawRow6505 := by decide +kernel

def row6505 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6505 : row6505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6505 := by decide +kernel

theorem rowEval6505 (x : Key → ℝ) : Integer.Sparse.eval row6505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6505, Integer.Sparse.eval_collectBalanced, rawRowCheck6505]

def rawRow6506 : Integer.Sparse Key := [(key1337, -1), (key1346, -1), (key1340, 2), (key1316, -1), (key1330, -1), (key1296, 2), (key1346, 2), (key1303, -1), (key1340, -1), (key1316, 2), (key1296, -1), (key1337, -1), (key1772, 1), (key1781, 1), (key1775, -2), (key1546, 1), (key1560, 1), (key1391, -2), (key1781, -2), (key1398, 1), (key1775, 1), (key1546, -2), (key1391, 1), (key1772, 1), (key1788, -1), (key1842, -1), (key1791, 1), (key1840, 1), (key1455, 1), (key1842, 1), (key1458, -1), (key1840, -1), (key1573, -1), (key1660, -1), (key1424, 1), (key1818, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

theorem rawRowCheck6506 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form1 = rawRow6506 := by decide +kernel

def row6506 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6506 : row6506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6506 := by decide +kernel

theorem rowEval6506 (x : Key → ℝ) : Integer.Sparse.eval row6506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6506, Integer.Sparse.eval_collectBalanced, rawRowCheck6506]

def rawRow6507 : Integer.Sparse Key := [(key1346, -1), (key1337, -1), (key1340, 2), (key1330, -1), (key1316, -1), (key1346, 2), (key1296, 2), (key1340, -1), (key1303, -1), (key1316, 2), (key1337, -1), (key1296, -1), (key1781, 1), (key1772, 1), (key1775, -2), (key1560, 1), (key1546, 1), (key1781, -2), (key1391, -2), (key1775, 1), (key1398, 1), (key1546, -2), (key1772, 1), (key1391, 1), (key1842, -1), (key1788, -1), (key1840, 1), (key1791, 1), (key1842, 1), (key1455, 1), (key1840, -1), (key1458, -1), (key1660, -1), (key1573, -1), (key1818, 1), (key1424, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

theorem rawRowCheck6507 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form1 = rawRow6507 := by decide +kernel

def row6507 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6507 : row6507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6507 := by decide +kernel

theorem rowEval6507 (x : Key → ℝ) : Integer.Sparse.eval row6507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6507, Integer.Sparse.eval_collectBalanced, rawRowCheck6507]

def rawRow6508 : Integer.Sparse Key := [(key1340, -1), (key1346, -1), (key1337, 2), (key1340, -1), (key1346, -1), (key1303, 2), (key1330, 2), (key1296, -1), (key1316, -1), (key1337, 2), (key1296, -1), (key1316, -1), (key1775, 1), (key1781, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1398, -2), (key1560, -2), (key1391, 1), (key1546, 1), (key1772, -2), (key1391, 1), (key1546, 1), (key1791, -1), (key1818, -1), (key1788, 1), (key1813, 1), (key1458, 1), (key1660, 1), (key1455, -1), (key1655, -1), (key1791, -1), (key1818, -1), (key1458, 1), (key1660, 1), (key1788, 1), (key1813, 1), (key1455, -1), (key1655, -1)]

theorem rawRowCheck6508 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form1 = rawRow6508 := by decide +kernel

def row6508 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

theorem rowCheck6508 : row6508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6508 := by decide +kernel

theorem rowEval6508 (x : Key → ℝ) : Integer.Sparse.eval row6508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6508, Integer.Sparse.eval_collectBalanced, rawRowCheck6508]

def rawRow6509 : Integer.Sparse Key := [(key1346, -1), (key1340, -1), (key1337, 2), (key1346, -1), (key1340, -1), (key1330, 2), (key1303, 2), (key1316, -1), (key1296, -1), (key1337, 2), (key1316, -1), (key1296, -1), (key1781, 1), (key1775, 1), (key1772, -2), (key1781, 1), (key1775, 1), (key1560, -2), (key1398, -2), (key1546, 1), (key1391, 1), (key1772, -2), (key1546, 1), (key1391, 1), (key1818, -1), (key1791, -1), (key1813, 1), (key1788, 1), (key1660, 1), (key1458, 1), (key1655, -1), (key1455, -1), (key1818, -1), (key1791, -1), (key1660, 1), (key1458, 1), (key1813, 1), (key1788, 1), (key1655, -1), (key1455, -1)]

theorem rawRowCheck6509 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form1 = rawRow6509 := by decide +kernel

def row6509 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, -2), (key1330, 2), (key1337, 4), (key1340, -2), (key1346, -2), (key1391, 2), (key1398, -2), (key1455, -2), (key1458, 2), (key1546, 2), (key1560, -2), (key1655, -2), (key1660, 2), (key1772, -4), (key1775, 2), (key1781, 2), (key1788, 2), (key1791, -2), (key1813, 2), (key1818, -2)]

theorem rowCheck6509 : row6509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6509 := by decide +kernel

theorem rowEval6509 (x : Key → ℝ) : Integer.Sparse.eval row6509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6509, Integer.Sparse.eval_collectBalanced, rawRowCheck6509]

def rawRow6510 : Integer.Sparse Key := [(key1775, -1), (key1781, -1), (key1772, 2), (key1840, -1), (key1842, -1), (key1791, 2), (key1818, 2), (key1788, -1), (key1813, -1), (key1845, 2), (key1799, -1), (key1826, -1), (key1340, 1), (key1346, 1), (key1337, -2), (key1840, 1), (key1842, 1), (key1458, -2), (key1660, -2), (key1455, 1), (key1655, 1), (key1845, -2), (key1467, 1), (key1668, 1), (key1303, -1), (key1330, -1), (key1296, 1), (key1316, 1), (key1398, 1), (key1560, 1), (key1391, -1), (key1546, -1), (key1791, -1), (key1818, -1), (key1458, 1), (key1660, 1), (key1799, 1), (key1826, 1), (key1467, -1), (key1668, -1)]

theorem rawRowCheck6510 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form1 = rawRow6510 := by decide +kernel

def row6510 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6510 : row6510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6510 := by decide +kernel

theorem rowEval6510 (x : Key → ℝ) : Integer.Sparse.eval row6510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6510, Integer.Sparse.eval_collectBalanced, rawRowCheck6510]

def rawRow6511 : Integer.Sparse Key := [(key1781, -1), (key1775, -1), (key1772, 2), (key1842, -1), (key1840, -1), (key1818, 2), (key1791, 2), (key1813, -1), (key1788, -1), (key1845, 2), (key1826, -1), (key1799, -1), (key1346, 1), (key1340, 1), (key1337, -2), (key1842, 1), (key1840, 1), (key1660, -2), (key1458, -2), (key1655, 1), (key1455, 1), (key1845, -2), (key1668, 1), (key1467, 1), (key1330, -1), (key1303, -1), (key1316, 1), (key1296, 1), (key1560, 1), (key1398, 1), (key1546, -1), (key1391, -1), (key1818, -1), (key1791, -1), (key1660, 1), (key1458, 1), (key1826, 1), (key1799, 1), (key1668, -1), (key1467, -1)]

theorem rawRowCheck6511 : GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form1 = rawRow6511 := by decide +kernel

def row6511 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6511 : row6511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6511 := by decide +kernel

theorem rowEval6511 (x : Key → ℝ) : Integer.Sparse.eval row6511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -2, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6511, Integer.Sparse.eval_collectBalanced, rawRowCheck6511]

def rawRow6512 : Integer.Sparse Key := [(key1788, -1), (key1799, -1), (key1791, 2), (key1813, -1), (key1826, -1), (key1772, 2), (key1845, 2), (key1775, -1), (key1840, -1), (key1818, 2), (key1781, -1), (key1842, -1), (key1455, 1), (key1467, 1), (key1458, -2), (key1655, 1), (key1668, 1), (key1337, -2), (key1845, -2), (key1340, 1), (key1840, 1), (key1660, -2), (key1346, 1), (key1842, 1), (key1391, -1), (key1467, -1), (key1398, 1), (key1458, 1), (key1296, 1), (key1799, 1), (key1303, -1), (key1791, -1), (key1546, -1), (key1668, -1), (key1316, 1), (key1826, 1), (key1560, 1), (key1660, 1), (key1330, -1), (key1818, -1)]

theorem rawRowCheck6512 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form1 = rawRow6512 := by decide +kernel

def row6512 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6512 : row6512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6512 := by decide +kernel

theorem rowEval6512 (x : Key → ℝ) : Integer.Sparse.eval row6512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6512, Integer.Sparse.eval_collectBalanced, rawRowCheck6512]

def rawRow6513 : Integer.Sparse Key := [(key1799, -1), (key1788, -1), (key1791, 2), (key1826, -1), (key1813, -1), (key1845, 2), (key1772, 2), (key1840, -1), (key1775, -1), (key1818, 2), (key1842, -1), (key1781, -1), (key1467, 1), (key1455, 1), (key1458, -2), (key1668, 1), (key1655, 1), (key1845, -2), (key1337, -2), (key1840, 1), (key1340, 1), (key1660, -2), (key1842, 1), (key1346, 1), (key1467, -1), (key1391, -1), (key1458, 1), (key1398, 1), (key1799, 1), (key1296, 1), (key1791, -1), (key1303, -1), (key1668, -1), (key1546, -1), (key1826, 1), (key1316, 1), (key1660, 1), (key1560, 1), (key1818, -1), (key1330, -1)]

theorem rawRowCheck6513 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form1 = rawRow6513 := by decide +kernel

def row6513 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6513 : row6513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6513 := by decide +kernel

theorem rowEval6513 (x : Key → ℝ) : Integer.Sparse.eval row6513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6513, Integer.Sparse.eval_collectBalanced, rawRowCheck6513]

def rawRow6514 : Integer.Sparse Key := [(key1813, -1), (key1826, -1), (key1818, 2), (key1788, -1), (key1799, -1), (key1772, 2), (key1845, 2), (key1781, -1), (key1842, -1), (key1791, 2), (key1775, -1), (key1840, -1), (key1655, 1), (key1668, 1), (key1660, -2), (key1455, 1), (key1467, 1), (key1337, -2), (key1845, -2), (key1346, 1), (key1842, 1), (key1458, -2), (key1340, 1), (key1840, 1), (key1546, -1), (key1668, -1), (key1560, 1), (key1660, 1), (key1316, 1), (key1826, 1), (key1330, -1), (key1818, -1), (key1391, -1), (key1467, -1), (key1296, 1), (key1799, 1), (key1398, 1), (key1458, 1), (key1303, -1), (key1791, -1)]

theorem rawRowCheck6514 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form1 = rawRow6514 := by decide +kernel

def row6514 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6514 : row6514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6514 := by decide +kernel

theorem rowEval6514 (x : Key → ℝ) : Integer.Sparse.eval row6514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6514, Integer.Sparse.eval_collectBalanced, rawRowCheck6514]

def rawRow6515 : Integer.Sparse Key := [(key1826, -1), (key1813, -1), (key1818, 2), (key1799, -1), (key1788, -1), (key1845, 2), (key1772, 2), (key1842, -1), (key1781, -1), (key1791, 2), (key1840, -1), (key1775, -1), (key1668, 1), (key1655, 1), (key1660, -2), (key1467, 1), (key1455, 1), (key1845, -2), (key1337, -2), (key1842, 1), (key1346, 1), (key1458, -2), (key1840, 1), (key1340, 1), (key1668, -1), (key1546, -1), (key1660, 1), (key1560, 1), (key1826, 1), (key1316, 1), (key1818, -1), (key1330, -1), (key1467, -1), (key1391, -1), (key1799, 1), (key1296, 1), (key1458, 1), (key1398, 1), (key1791, -1), (key1303, -1)]

theorem rawRowCheck6515 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form1 = rawRow6515 := by decide +kernel

def row6515 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6515 : row6515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6515 := by decide +kernel

theorem rowEval6515 (x : Key → ℝ) : Integer.Sparse.eval row6515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck6515, Integer.Sparse.eval_collectBalanced, rawRowCheck6515]

def rawRow6516 : Integer.Sparse Key := [(key1840, -1), (key1842, -1), (key1845, 2), (key1775, -1), (key1781, -1), (key1791, 2), (key1818, 2), (key1799, -1), (key1826, -1), (key1772, 2), (key1788, -1), (key1813, -1), (key1840, 1), (key1842, 1), (key1845, -2), (key1340, 1), (key1346, 1), (key1458, -2), (key1660, -2), (key1467, 1), (key1668, 1), (key1337, -2), (key1455, 1), (key1655, 1), (key1791, -1), (key1818, -1), (key1799, 1), (key1826, 1), (key1458, 1), (key1660, 1), (key1467, -1), (key1668, -1), (key1303, -1), (key1330, -1), (key1398, 1), (key1560, 1), (key1296, 1), (key1316, 1), (key1391, -1), (key1546, -1)]

theorem rawRowCheck6516 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form1 = rawRow6516 := by decide +kernel

def row6516 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6516 : row6516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6516 := by decide +kernel

theorem rowEval6516 (x : Key → ℝ) : Integer.Sparse.eval row6516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck6516, Integer.Sparse.eval_collectBalanced, rawRowCheck6516]

def rawRow6517 : Integer.Sparse Key := [(key1842, -1), (key1840, -1), (key1845, 2), (key1781, -1), (key1775, -1), (key1818, 2), (key1791, 2), (key1826, -1), (key1799, -1), (key1772, 2), (key1813, -1), (key1788, -1), (key1842, 1), (key1840, 1), (key1845, -2), (key1346, 1), (key1340, 1), (key1660, -2), (key1458, -2), (key1668, 1), (key1467, 1), (key1337, -2), (key1655, 1), (key1455, 1), (key1818, -1), (key1791, -1), (key1826, 1), (key1799, 1), (key1660, 1), (key1458, 1), (key1668, -1), (key1467, -1), (key1330, -1), (key1303, -1), (key1560, 1), (key1398, 1), (key1316, 1), (key1296, 1), (key1546, -1), (key1391, -1)]

theorem rawRowCheck6517 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form1 = rawRow6517 := by decide +kernel

def row6517 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, 1), (key1330, -1), (key1337, -2), (key1340, 1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, 1), (key1660, -1), (key1772, 2), (key1775, -1), (key1781, -1), (key1788, -1), (key1791, 1), (key1813, -1), (key1818, 1)]

theorem rowCheck6517 : row6517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6517 := by decide +kernel

theorem rowEval6517 (x : Key → ℝ) : Integer.Sparse.eval row6517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck6517, Integer.Sparse.eval_collectBalanced, rawRowCheck6517]

def rawRow6518 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2619, 2), (key2632, -1), (key2632, -1), (key2640, 2), (key2640, 2), (key2642, -1), (key2642, -1), (key2649, 2), (key2654, -1), (key2654, -1), (key2671, 1), (key2671, 1), (key2674, -2), (key2706, 1), (key2706, 1), (key2726, -2), (key2726, -2), (key2729, 1), (key2729, 1), (key2738, -2), (key2748, 1), (key2748, 1), (key2794, -1), (key2794, -1), (key2796, 1), (key2796, 1), (key2829, 1), (key2829, 1), (key2832, -1), (key2832, -1), (key2860, -1), (key2860, -1), (key2870, 1), (key2870, 1), (key2898, 1), (key2898, 1), (key2905, -1), (key2905, -1)]

theorem rawRowCheck6518 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form2 = rawRow6518 := by decide +kernel

def row6518 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

theorem rowCheck6518 : row6518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6518 := by decide +kernel

theorem rowEval6518 (x : Key → ℝ) : Integer.Sparse.eval row6518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6518, Integer.Sparse.eval_collectBalanced, rawRowCheck6518]

def rawRow6519 : Integer.Sparse Key := [(key2616, -1), (key2619, -1), (key2616, 2), (key2640, -1), (key2642, -1), (key2632, 2), (key2642, 2), (key2632, -1), (key2640, -1), (key2654, 2), (key2649, -1), (key2654, -1), (key2671, 1), (key2674, 1), (key2671, -2), (key2726, 1), (key2729, 1), (key2706, -2), (key2729, -2), (key2706, 1), (key2726, 1), (key2748, -2), (key2738, 1), (key2748, 1), (key2786, -1), (key2796, -1), (key2786, 1), (key2794, 1), (key2809, 1), (key2832, 1), (key2809, -1), (key2829, -1), (key2870, -1), (key2883, -1), (key2860, 1), (key2883, 1), (key2905, 1), (key2913, 1), (key2898, -1), (key2913, -1)]

theorem rawRowCheck6519 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form2 = rawRow6519 := by decide +kernel

def row6519 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6519 : row6519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6519 := by decide +kernel

theorem rowEval6519 (x : Key → ℝ) : Integer.Sparse.eval row6519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6519, Integer.Sparse.eval_collectBalanced, rawRowCheck6519]

def rawRow6520 : Integer.Sparse Key := [(key2619, -1), (key2616, -1), (key2616, 2), (key2642, -1), (key2640, -1), (key2642, 2), (key2632, 2), (key2640, -1), (key2632, -1), (key2654, 2), (key2654, -1), (key2649, -1), (key2674, 1), (key2671, 1), (key2671, -2), (key2729, 1), (key2726, 1), (key2729, -2), (key2706, -2), (key2726, 1), (key2706, 1), (key2748, -2), (key2748, 1), (key2738, 1), (key2796, -1), (key2786, -1), (key2794, 1), (key2786, 1), (key2832, 1), (key2809, 1), (key2829, -1), (key2809, -1), (key2883, -1), (key2870, -1), (key2883, 1), (key2860, 1), (key2913, 1), (key2905, 1), (key2913, -1), (key2898, -1)]

theorem rawRowCheck6520 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form2 = rawRow6520 := by decide +kernel

def row6520 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6520 : row6520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6520 := by decide +kernel

theorem rowEval6520 (x : Key → ℝ) : Integer.Sparse.eval row6520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6520, Integer.Sparse.eval_collectBalanced, rawRowCheck6520]

def rawRow6521 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2649, 2), (key2616, -1), (key2616, -1), (key2640, 2), (key2640, 2), (key2654, -1), (key2654, -1), (key2619, 2), (key2642, -1), (key2642, -1), (key2706, 1), (key2706, 1), (key2738, -2), (key2671, 1), (key2671, 1), (key2726, -2), (key2726, -2), (key2748, 1), (key2748, 1), (key2674, -2), (key2729, 1), (key2729, 1), (key2860, -1), (key2860, -1), (key2898, 1), (key2898, 1), (key2870, 1), (key2870, 1), (key2905, -1), (key2905, -1), (key2794, -1), (key2794, -1), (key2829, 1), (key2829, 1), (key2796, 1), (key2796, 1), (key2832, -1), (key2832, -1)]

theorem rawRowCheck6521 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form2 = rawRow6521 := by decide +kernel

def row6521 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

theorem rowCheck6521 : row6521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6521 := by decide +kernel

theorem rowEval6521 (x : Key → ℝ) : Integer.Sparse.eval row6521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6521, Integer.Sparse.eval_collectBalanced, rawRowCheck6521]

def rawRow6522 : Integer.Sparse Key := [(key2632, -1), (key2649, -1), (key2632, 2), (key2640, -1), (key2654, -1), (key2616, 2), (key2654, 2), (key2616, -1), (key2640, -1), (key2642, 2), (key2619, -1), (key2642, -1), (key2706, 1), (key2738, 1), (key2706, -2), (key2726, 1), (key2748, 1), (key2671, -2), (key2748, -2), (key2671, 1), (key2726, 1), (key2729, -2), (key2674, 1), (key2729, 1), (key2809, -1), (key2898, -1), (key2809, 1), (key2860, 1), (key2786, 1), (key2905, 1), (key2786, -1), (key2870, -1), (key2829, -1), (key2913, -1), (key2794, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2796, -1), (key2883, -1)]

theorem rawRowCheck6522 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form2 = rawRow6522 := by decide +kernel

def row6522 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6522 : row6522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6522 := by decide +kernel

theorem rowEval6522 (x : Key → ℝ) : Integer.Sparse.eval row6522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6522, Integer.Sparse.eval_collectBalanced, rawRowCheck6522]

def rawRow6523 : Integer.Sparse Key := [(key2649, -1), (key2632, -1), (key2632, 2), (key2654, -1), (key2640, -1), (key2654, 2), (key2616, 2), (key2640, -1), (key2616, -1), (key2642, 2), (key2642, -1), (key2619, -1), (key2738, 1), (key2706, 1), (key2706, -2), (key2748, 1), (key2726, 1), (key2748, -2), (key2671, -2), (key2726, 1), (key2671, 1), (key2729, -2), (key2729, 1), (key2674, 1), (key2898, -1), (key2809, -1), (key2860, 1), (key2809, 1), (key2905, 1), (key2786, 1), (key2870, -1), (key2786, -1), (key2913, -1), (key2829, -1), (key2913, 1), (key2794, 1), (key2883, 1), (key2832, 1), (key2883, -1), (key2796, -1)]

theorem rawRowCheck6523 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form2 = rawRow6523 := by decide +kernel

def row6523 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6523 : row6523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6523 := by decide +kernel

theorem rowEval6523 (x : Key → ℝ) : Integer.Sparse.eval row6523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 1, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6523, Integer.Sparse.eval_collectBalanced, rawRowCheck6523]

def rawRow6524 : Integer.Sparse Key := [(key2640, -1), (key2642, -1), (key2654, 2), (key2616, -1), (key2619, -1), (key2632, 2), (key2642, 2), (key2649, -1), (key2654, -1), (key2616, 2), (key2632, -1), (key2640, -1), (key2726, 1), (key2729, 1), (key2748, -2), (key2671, 1), (key2674, 1), (key2706, -2), (key2729, -2), (key2738, 1), (key2748, 1), (key2671, -2), (key2706, 1), (key2726, 1), (key2870, -1), (key2883, -1), (key2905, 1), (key2913, 1), (key2860, 1), (key2883, 1), (key2898, -1), (key2913, -1), (key2786, -1), (key2796, -1), (key2809, 1), (key2832, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2829, -1)]

theorem rawRowCheck6524 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form2 = rawRow6524 := by decide +kernel

def row6524 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6524 : row6524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6524 := by decide +kernel

theorem rowEval6524 (x : Key → ℝ) : Integer.Sparse.eval row6524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6524, Integer.Sparse.eval_collectBalanced, rawRowCheck6524]

def rawRow6525 : Integer.Sparse Key := [(key2642, -1), (key2640, -1), (key2654, 2), (key2619, -1), (key2616, -1), (key2642, 2), (key2632, 2), (key2654, -1), (key2649, -1), (key2616, 2), (key2640, -1), (key2632, -1), (key2729, 1), (key2726, 1), (key2748, -2), (key2674, 1), (key2671, 1), (key2729, -2), (key2706, -2), (key2748, 1), (key2738, 1), (key2671, -2), (key2726, 1), (key2706, 1), (key2883, -1), (key2870, -1), (key2913, 1), (key2905, 1), (key2883, 1), (key2860, 1), (key2913, -1), (key2898, -1), (key2796, -1), (key2786, -1), (key2832, 1), (key2809, 1), (key2794, 1), (key2786, 1), (key2829, -1), (key2809, -1)]

theorem rawRowCheck6525 : GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form2 = rawRow6525 := by decide +kernel

def row6525 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6525 : row6525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6525 := by decide +kernel

theorem rowEval6525 (x : Key → ℝ) : Integer.Sparse.eval row6525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6525, Integer.Sparse.eval_collectBalanced, rawRowCheck6525]

def rawRow6526 : Integer.Sparse Key := [(key2640, -1), (key2654, -1), (key2642, 2), (key2632, -1), (key2649, -1), (key2616, 2), (key2654, 2), (key2619, -1), (key2642, -1), (key2632, 2), (key2616, -1), (key2640, -1), (key2726, 1), (key2748, 1), (key2729, -2), (key2706, 1), (key2738, 1), (key2671, -2), (key2748, -2), (key2674, 1), (key2729, 1), (key2706, -2), (key2671, 1), (key2726, 1), (key2829, -1), (key2913, -1), (key2832, 1), (key2883, 1), (key2794, 1), (key2913, 1), (key2796, -1), (key2883, -1), (key2809, -1), (key2898, -1), (key2786, 1), (key2905, 1), (key2809, 1), (key2860, 1), (key2786, -1), (key2870, -1)]

theorem rawRowCheck6526 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form2 = rawRow6526 := by decide +kernel

def row6526 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6526 : row6526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6526 := by decide +kernel

theorem rowEval6526 (x : Key → ℝ) : Integer.Sparse.eval row6526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6526, Integer.Sparse.eval_collectBalanced, rawRowCheck6526]

def rawRow6527 : Integer.Sparse Key := [(key2654, -1), (key2640, -1), (key2642, 2), (key2649, -1), (key2632, -1), (key2654, 2), (key2616, 2), (key2642, -1), (key2619, -1), (key2632, 2), (key2640, -1), (key2616, -1), (key2748, 1), (key2726, 1), (key2729, -2), (key2738, 1), (key2706, 1), (key2748, -2), (key2671, -2), (key2729, 1), (key2674, 1), (key2706, -2), (key2726, 1), (key2671, 1), (key2913, -1), (key2829, -1), (key2883, 1), (key2832, 1), (key2913, 1), (key2794, 1), (key2883, -1), (key2796, -1), (key2898, -1), (key2809, -1), (key2905, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, -1), (key2786, -1)]

theorem rawRowCheck6527 : GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form2 = rawRow6527 := by decide +kernel

def row6527 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

theorem rowCheck6527 : row6527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6527 := by decide +kernel

theorem rowEval6527 (x : Key → ℝ) : Integer.Sparse.eval row6527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 1, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6527, Integer.Sparse.eval_collectBalanced, rawRowCheck6527]

end MUB6.Certificate.GramRows

end OAI
