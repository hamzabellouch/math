import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
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

def rawRow160 : Integer.Sparse Key := [(key1899, -1), (key1896, -1), (key1896, 2), (key1920, 1), (key1918, 1), (key1918, -1), (key1903, -1), (key1926, -2), (key1926, 1), (key1911, 1), (key1354, 1), (key1351, 1), (key1351, -2), (key1683, -1), (key1681, -1), (key1681, 1), (key1472, 1), (key1689, 2), (key1689, -1), (key1480, -1), (key1326, -1), (key1318, -1), (key1318, 1), (key1298, 1), (key1556, 1), (key1548, 1), (key1548, -1), (key1393, -1), (key1633, -1), (key1593, -1), (key1633, 1), (key1444, 1), (key1312, 2), (key1312, -1), (key1292, -1), (key1542, -2), (key1542, 1), (key1387, 1), (key1618, 1), (key1569, 1), (key1618, -1), (key1420, -1)]

theorem rawRowCheck160 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form0 = rawRow160 := by decide +kernel

def row160 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck160 : row160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow160 := by decide +kernel

theorem rowEval160 (x : Key → ℝ) : Integer.Sparse.eval row160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck160, Integer.Sparse.eval_collectBalanced, rawRowCheck160]

def rawRow161 : Integer.Sparse Key := [(key1903, -1), (key1903, -1), (key1911, 2), (key1896, 1), (key1896, 1), (key1926, -1), (key1926, -1), (key1899, -2), (key1920, 1), (key1920, 1), (key1472, 1), (key1472, 1), (key1480, -2), (key1351, -1), (key1351, -1), (key1689, 1), (key1689, 1), (key1354, 2), (key1683, -1), (key1683, -1), (key1393, -1), (key1393, -1), (key1444, 1), (key1444, 1), (key1298, 1), (key1298, 1), (key1593, -1), (key1593, -1), (key1326, -1), (key1326, -1), (key1556, 1), (key1556, 1), (key1387, 2), (key1420, -1), (key1420, -1), (key1292, -2), (key1569, 1), (key1569, 1), (key1312, 1), (key1312, 1), (key1542, -1), (key1542, -1)]

theorem rawRowCheck161 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow161 := by decide +kernel

def row161 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1387, 2), (key1393, -2), (key1420, -2), (key1444, 2), (key1472, 2), (key1480, -2), (key1542, -2), (key1556, 2), (key1569, 2), (key1593, -2), (key1683, -2), (key1689, 2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

theorem rowCheck161 : row161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow161 := by decide +kernel

theorem rowEval161 (x : Key → ℝ) : Integer.Sparse.eval row161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck161, Integer.Sparse.eval_collectBalanced, rawRowCheck161]

def rawRow162 : Integer.Sparse Key := [(key1903, -1), (key1911, -1), (key1903, 2), (key1918, 1), (key1926, 1), (key1896, -1), (key1918, -1), (key1920, -2), (key1899, 1), (key1920, 1), (key1472, 1), (key1480, 1), (key1472, -2), (key1681, -1), (key1689, -1), (key1351, 1), (key1681, 1), (key1683, 2), (key1354, -1), (key1683, -1), (key1426, -1), (key1444, -1), (key1393, 1), (key1426, 1), (key1575, 1), (key1593, 1), (key1298, -1), (key1575, -1), (key1556, -1), (key1624, -1), (key1326, 1), (key1624, 1), (key1420, 2), (key1387, -1), (key1420, -1), (key1569, -2), (key1292, 1), (key1569, 1), (key1542, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

theorem rawRowCheck162 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow162 := by decide +kernel

def row162 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck162 : row162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow162 := by decide +kernel

theorem rowEval162 (x : Key → ℝ) : Integer.Sparse.eval row162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck162, Integer.Sparse.eval_collectBalanced, rawRowCheck162]

def rawRow163 : Integer.Sparse Key := [(key1911, -1), (key1903, -1), (key1903, 2), (key1926, 1), (key1918, 1), (key1918, -1), (key1896, -1), (key1920, -2), (key1920, 1), (key1899, 1), (key1480, 1), (key1472, 1), (key1472, -2), (key1689, -1), (key1681, -1), (key1681, 1), (key1351, 1), (key1683, 2), (key1683, -1), (key1354, -1), (key1444, -1), (key1426, -1), (key1426, 1), (key1393, 1), (key1593, 1), (key1575, 1), (key1575, -1), (key1298, -1), (key1624, -1), (key1556, -1), (key1624, 1), (key1326, 1), (key1420, 2), (key1420, -1), (key1387, -1), (key1569, -2), (key1569, 1), (key1292, 1), (key1618, 1), (key1542, 1), (key1618, -1), (key1312, -1)]

theorem rawRowCheck163 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow163 := by decide +kernel

def row163 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck163 : row163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow163 := by decide +kernel

theorem rowEval163 (x : Key → ℝ) : Integer.Sparse.eval row163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck163, Integer.Sparse.eval_collectBalanced, rawRowCheck163]

def rawRow164 : Integer.Sparse Key := [(key1918, -1), (key1920, -1), (key1926, 2), (key1896, 1), (key1899, 1), (key1911, -1), (key1926, -1), (key1896, -2), (key1903, 1), (key1918, 1), (key1681, 1), (key1683, 1), (key1689, -2), (key1351, -1), (key1354, -1), (key1480, 1), (key1689, 1), (key1351, 2), (key1472, -1), (key1681, -1), (key1548, -1), (key1556, -1), (key1593, 1), (key1633, 1), (key1318, 1), (key1326, 1), (key1444, -1), (key1633, -1), (key1298, -1), (key1318, -1), (key1393, 1), (key1548, 1), (key1542, 2), (key1569, -1), (key1618, -1), (key1312, -2), (key1420, 1), (key1618, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1542, -1)]

theorem rawRowCheck164 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form0 = rawRow164 := by decide +kernel

def row164 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck164 : row164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow164 := by decide +kernel

theorem rowEval164 (x : Key → ℝ) : Integer.Sparse.eval row164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck164, Integer.Sparse.eval_collectBalanced, rawRowCheck164]

def rawRow165 : Integer.Sparse Key := [(key1920, -1), (key1918, -1), (key1926, 2), (key1899, 1), (key1896, 1), (key1926, -1), (key1911, -1), (key1896, -2), (key1918, 1), (key1903, 1), (key1683, 1), (key1681, 1), (key1689, -2), (key1354, -1), (key1351, -1), (key1689, 1), (key1480, 1), (key1351, 2), (key1681, -1), (key1472, -1), (key1556, -1), (key1548, -1), (key1633, 1), (key1593, 1), (key1326, 1), (key1318, 1), (key1633, -1), (key1444, -1), (key1318, -1), (key1298, -1), (key1548, 1), (key1393, 1), (key1542, 2), (key1618, -1), (key1569, -1), (key1312, -2), (key1618, 1), (key1420, 1), (key1312, 1), (key1292, 1), (key1542, -1), (key1387, -1)]

theorem rawRowCheck165 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form0 = rawRow165 := by decide +kernel

def row165 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, -1), (key1393, 1), (key1420, 1), (key1444, -1), (key1472, -1), (key1480, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1593, 1), (key1683, 1), (key1689, -1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

theorem rowCheck165 : row165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow165 := by decide +kernel

theorem rowEval165 (x : Key → ℝ) : Integer.Sparse.eval row165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck165, Integer.Sparse.eval_collectBalanced, rawRowCheck165]

def rawRow166 : Integer.Sparse Key := [(key1918, -1), (key1926, -1), (key1920, 2), (key1903, 1), (key1911, 1), (key1899, -1), (key1920, -1), (key1903, -2), (key1896, 1), (key1918, 1), (key1681, 1), (key1689, 1), (key1683, -2), (key1472, -1), (key1480, -1), (key1354, 1), (key1683, 1), (key1472, 2), (key1351, -1), (key1681, -1), (key1575, -1), (key1593, -1), (key1556, 1), (key1624, 1), (key1426, 1), (key1444, 1), (key1326, -1), (key1624, -1), (key1393, -1), (key1426, -1), (key1298, 1), (key1575, 1), (key1569, 2), (key1542, -1), (key1618, -1), (key1420, -2), (key1312, 1), (key1618, 1), (key1387, 1), (key1420, 1), (key1292, -1), (key1569, -1)]

theorem rawRowCheck166 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form0 = rawRow166 := by decide +kernel

def row166 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck166 : row166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow166 := by decide +kernel

theorem rowEval166 (x : Key → ℝ) : Integer.Sparse.eval row166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck166, Integer.Sparse.eval_collectBalanced, rawRowCheck166]

def rawRow167 : Integer.Sparse Key := [(key1926, -1), (key1918, -1), (key1920, 2), (key1911, 1), (key1903, 1), (key1920, -1), (key1899, -1), (key1903, -2), (key1918, 1), (key1896, 1), (key1689, 1), (key1681, 1), (key1683, -2), (key1480, -1), (key1472, -1), (key1683, 1), (key1354, 1), (key1472, 2), (key1681, -1), (key1351, -1), (key1593, -1), (key1575, -1), (key1624, 1), (key1556, 1), (key1444, 1), (key1426, 1), (key1624, -1), (key1326, -1), (key1426, -1), (key1393, -1), (key1575, 1), (key1298, 1), (key1569, 2), (key1618, -1), (key1542, -1), (key1420, -2), (key1618, 1), (key1312, 1), (key1420, 1), (key1387, 1), (key1569, -1), (key1292, -1)]

theorem rawRowCheck167 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form0 = rawRow167 := by decide +kernel

def row167 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, 1), (key1393, -1), (key1420, -1), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1593, -1), (key1683, -1), (key1689, 1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

theorem rowCheck167 : row167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow167 := by decide +kernel

theorem rowEval167 (x : Key → ℝ) : Integer.Sparse.eval row167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck167, Integer.Sparse.eval_collectBalanced, rawRowCheck167]

def rawRow168 : Integer.Sparse Key := [(key2612, -2), (key2612, 1), (key2618, 1), (key2628, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2648, -1), (key2646, 1), (key2653, 1), (key2667, 2), (key2667, -1), (key2673, -1), (key2702, -2), (key2702, 1), (key2728, 1), (key2735, 1), (key2737, 1), (key2735, -1), (key2747, -1), (key2782, -2), (key2782, 1), (key2795, 1), (key2805, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2897, -1), (key2893, 1), (key2904, 1), (key2936, 1), (key2938, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, -1), (key2948, 1), (key2960, 1), (key2972, 1), (key2976, 1), (key2972, -1), (key2983, -1)]

theorem rawRowCheck168 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form1 = rawRow168 := by decide +kernel

def row168 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

theorem rowCheck168 : row168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow168 := by decide +kernel

theorem rowEval168 (x : Key → ℝ) : Integer.Sparse.eval row168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block0.form1) x := by
  rw [rowCheck168, Integer.Sparse.eval_collectBalanced, rawRowCheck168]

def rawRow169 : Integer.Sparse Key := [(key2616, -2), (key2618, 1), (key2612, 1), (key2628, 2), (key2641, -1), (key2628, -1), (key2648, -1), (key2646, -1), (key2653, 1), (key2646, 1), (key2667, 2), (key2673, -1), (key2667, -1), (key2702, -2), (key2728, 1), (key2702, 1), (key2737, 1), (key2735, 1), (key2747, -1), (key2735, -1), (key2782, -2), (key2795, 1), (key2782, 1), (key2805, 2), (key2831, -1), (key2805, -1), (key2897, -1), (key2893, -1), (key2904, 1), (key2893, 1), (key2938, 1), (key2936, 1), (key2943, -1), (key2936, -1), (key2950, -1), (key2948, -1), (key2960, 1), (key2948, 1), (key2976, 1), (key2972, 1), (key2983, -1), (key2972, -1)]

theorem rawRowCheck169 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form1 = rawRow169 := by decide +kernel

def row169 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

theorem rowCheck169 : row169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow169 := by decide +kernel

theorem rowEval169 (x : Key → ℝ) : Integer.Sparse.eval row169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck169, Integer.Sparse.eval_collectBalanced, rawRowCheck169]

def rawRow170 : Integer.Sparse Key := [(key2621, -2), (key2616, 1), (key2616, 1), (key2641, 2), (key2628, -1), (key2628, -1), (key2653, -1), (key2653, -1), (key2648, 1), (key2648, 1), (key2673, 2), (key2667, -1), (key2667, -1), (key2728, -2), (key2702, 1), (key2702, 1), (key2747, 1), (key2747, 1), (key2737, -1), (key2737, -1), (key2795, -2), (key2782, 1), (key2782, 1), (key2831, 2), (key2805, -1), (key2805, -1), (key2904, -1), (key2904, -1), (key2897, 1), (key2897, 1), (key2943, 1), (key2943, 1), (key2938, -1), (key2938, -1), (key2960, -1), (key2960, -1), (key2950, 1), (key2950, 1), (key2983, 1), (key2983, 1), (key2976, -1), (key2976, -1)]

theorem rawRowCheck170 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form1 = rawRow170 := by decide +kernel

def row170 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2667, -2), (key2673, 2), (key2702, 2), (key2728, -2), (key2737, -2), (key2747, 2), (key2782, 2), (key2795, -2), (key2805, -2), (key2831, 2), (key2897, 2), (key2904, -2), (key2938, -2), (key2943, 2), (key2950, 2), (key2960, -2), (key2976, -2), (key2983, 2)]

theorem rowCheck170 : row170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow170 := by decide +kernel

theorem rowEval170 (x : Key → ℝ) : Integer.Sparse.eval row170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck170, Integer.Sparse.eval_collectBalanced, rawRowCheck170]

def rawRow171 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2644, 1), (key2612, 2), (key2646, -1), (key2653, -1), (key2612, -1), (key2618, -1), (key2628, 1), (key2641, 1), (key2702, 2), (key2735, -1), (key2737, -1), (key2667, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2673, 1), (key2702, -1), (key2728, -1), (key2805, -2), (key2893, 1), (key2897, 1), (key2782, 2), (key2893, -1), (key2904, -1), (key2782, -1), (key2795, -1), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2972, -1), (key2976, -1), (key2936, -1), (key2938, -1), (key2972, 1), (key2983, 1), (key2936, 1), (key2943, 1), (key2948, -1), (key2960, -1)]

theorem rawRowCheck171 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form1 = rawRow171 := by decide +kernel

def row171 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

theorem rowCheck171 : row171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow171 := by decide +kernel

theorem rowEval171 (x : Key → ℝ) : Integer.Sparse.eval row171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block0.form1) x := by
  rw [rowCheck171, Integer.Sparse.eval_collectBalanced, rawRowCheck171]

def rawRow172 : Integer.Sparse Key := [(key2632, -2), (key2644, 1), (key2640, 1), (key2616, 2), (key2653, -1), (key2646, -1), (key2618, -1), (key2612, -1), (key2641, 1), (key2628, 1), (key2702, 2), (key2737, -1), (key2735, -1), (key2667, -2), (key2747, 1), (key2735, 1), (key2673, 1), (key2667, 1), (key2728, -1), (key2702, -1), (key2805, -2), (key2897, 1), (key2893, 1), (key2782, 2), (key2904, -1), (key2893, -1), (key2795, -1), (key2782, -1), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2976, -1), (key2972, -1), (key2938, -1), (key2936, -1), (key2983, 1), (key2972, 1), (key2943, 1), (key2936, 1), (key2960, -1), (key2948, -1)]

theorem rawRowCheck172 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form1 = rawRow172 := by decide +kernel

def row172 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

theorem rowCheck172 : row172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow172 := by decide +kernel

theorem rowEval172 (x : Key → ℝ) : Integer.Sparse.eval row172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck172, Integer.Sparse.eval_collectBalanced, rawRowCheck172]

def rawRow173 : Integer.Sparse Key := [(key2644, -2), (key2632, 1), (key2640, 1), (key2660, 2), (key2616, -1), (key2640, -1), (key2641, -1), (key2653, -1), (key2618, 1), (key2648, 1), (key2737, 2), (key2702, -1), (key2735, -1), (key2747, -2), (key2667, 1), (key2735, 1), (key2728, 1), (key2747, 1), (key2673, -1), (key2737, -1), (key2897, -2), (key2805, 1), (key2893, 1), (key2904, 2), (key2782, -1), (key2893, -1), (key2831, -1), (key2904, -1), (key2795, 1), (key2897, 1), (key2976, 1), (key2998, 1), (key2950, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2938, 1), (key2997, 1), (key2960, 1), (key3000, 1), (key2943, -1), (key2998, -1)]

theorem rawRowCheck173 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form1 = rawRow173 := by decide +kernel

def row173 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

theorem rowCheck173 : row173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow173 := by decide +kernel

theorem rowEval173 (x : Key → ℝ) : Integer.Sparse.eval row173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck173, Integer.Sparse.eval_collectBalanced, rawRowCheck173]

def rawRow174 : Integer.Sparse Key := [(key2644, -2), (key2640, 1), (key2632, 1), (key2660, 2), (key2640, -1), (key2616, -1), (key2653, -1), (key2641, -1), (key2648, 1), (key2618, 1), (key2737, 2), (key2735, -1), (key2702, -1), (key2747, -2), (key2735, 1), (key2667, 1), (key2747, 1), (key2728, 1), (key2737, -1), (key2673, -1), (key2897, -2), (key2893, 1), (key2805, 1), (key2904, 2), (key2893, -1), (key2782, -1), (key2904, -1), (key2831, -1), (key2897, 1), (key2795, 1), (key2998, 1), (key2976, 1), (key2997, -1), (key2950, -1), (key3000, -1), (key2983, -1), (key2997, 1), (key2938, 1), (key3000, 1), (key2960, 1), (key2998, -1), (key2943, -1)]

theorem rawRowCheck174 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form1 = rawRow174 := by decide +kernel

def row174 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2673, -1), (key2702, -1), (key2728, 1), (key2737, 1), (key2747, -1), (key2782, -1), (key2795, 1), (key2805, 1), (key2831, -1), (key2897, -1), (key2904, 1), (key2938, 1), (key2943, -1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, -1)]

theorem rowCheck174 : row174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow174 := by decide +kernel

theorem rowEval174 (x : Key → ℝ) : Integer.Sparse.eval row174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck174, Integer.Sparse.eval_collectBalanced, rawRowCheck174]

def rawRow175 : Integer.Sparse Key := [(key2658, -2), (key2660, 1), (key2660, 1), (key2621, 2), (key2644, -1), (key2644, -1), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2728, 2), (key2747, -1), (key2747, -1), (key2673, -2), (key2737, 1), (key2737, 1), (key2667, 1), (key2667, 1), (key2702, -1), (key2702, -1), (key2831, -2), (key2904, 1), (key2904, 1), (key2795, 2), (key2897, -1), (key2897, -1), (key2782, -1), (key2782, -1), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2983, -1), (key2983, -1), (key2943, -1), (key2943, -1), (key2976, 1), (key2976, 1), (key2938, 1), (key2938, 1), (key2950, -1), (key2950, -1)]

theorem rawRowCheck175 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form1 = rawRow175 := by decide +kernel

def row175 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2667, 2), (key2673, -2), (key2702, -2), (key2728, 2), (key2737, 2), (key2747, -2), (key2782, -2), (key2795, 2), (key2805, 2), (key2831, -2), (key2897, -2), (key2904, 2), (key2938, 2), (key2943, -2), (key2950, -2), (key2960, 2), (key2976, 2), (key2983, -2)]

theorem rowCheck175 : row175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow175 := by decide +kernel

theorem rowEval175 (x : Key → ℝ) : Integer.Sparse.eval row175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck175, Integer.Sparse.eval_collectBalanced, rawRowCheck175]

def rawRow176 : Integer.Sparse Key := [(key2660, -2), (key2658, 1), (key2660, 1), (key2644, 2), (key2621, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2747, 2), (key2728, -1), (key2747, -1), (key2737, -2), (key2673, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2667, -1), (key2735, -1), (key2904, -2), (key2831, 1), (key2904, 1), (key2897, 2), (key2795, -1), (key2897, -1), (key2805, -1), (key2893, -1), (key2782, 1), (key2893, 1), (key2983, 1), (key3000, 1), (key2960, -1), (key3000, -1), (key2976, -1), (key2998, -1), (key2943, 1), (key2998, 1), (key2950, 1), (key2997, 1), (key2938, -1), (key2997, -1)]

theorem rawRowCheck176 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form1 = rawRow176 := by decide +kernel

def row176 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

theorem rowCheck176 : row176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow176 := by decide +kernel

theorem rowEval176 (x : Key → ℝ) : Integer.Sparse.eval row176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck176, Integer.Sparse.eval_collectBalanced, rawRowCheck176]

def rawRow177 : Integer.Sparse Key := [(key2660, -2), (key2660, 1), (key2658, 1), (key2644, 2), (key2644, -1), (key2621, -1), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2747, 2), (key2747, -1), (key2728, -1), (key2737, -2), (key2737, 1), (key2673, 1), (key2735, 1), (key2702, 1), (key2735, -1), (key2667, -1), (key2904, -2), (key2904, 1), (key2831, 1), (key2897, 2), (key2897, -1), (key2795, -1), (key2893, -1), (key2805, -1), (key2893, 1), (key2782, 1), (key3000, 1), (key2983, 1), (key3000, -1), (key2960, -1), (key2998, -1), (key2976, -1), (key2998, 1), (key2943, 1), (key2997, 1), (key2950, 1), (key2997, -1), (key2938, -1)]

theorem rawRowCheck177 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form1 = rawRow177 := by decide +kernel

def row177 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2667, -1), (key2673, 1), (key2702, 1), (key2728, -1), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2938, -1), (key2943, 1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

theorem rowCheck177 : row177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow177 := by decide +kernel

theorem rowEval177 (x : Key → ℝ) : Integer.Sparse.eval row177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck177, Integer.Sparse.eval_collectBalanced, rawRowCheck177]

def rawRow178 : Integer.Sparse Key := [(key2671, -2), (key2671, 1), (key2676, 1), (key2706, 2), (key2706, -1), (key2753, -1), (key2726, -1), (key2732, -1), (key2726, 1), (key2758, 1), (key2612, 2), (key2612, -1), (key2618, -1), (key2805, -2), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2948, -1), (key2960, -1), (key2628, -2), (key2628, 1), (key2641, 1), (key2702, 2), (key2702, -1), (key2728, -1), (key2972, -1), (key2976, -1), (key2972, 1), (key2983, 1), (key2646, 1), (key2648, 1), (key2646, -1), (key2653, -1), (key2735, -1), (key2737, -1), (key2735, 1), (key2747, 1), (key2893, 1), (key2897, 1), (key2893, -1), (key2904, -1)]

theorem rawRowCheck178 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form1 = rawRow178 := by decide +kernel

def row178 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

theorem rowCheck178 : row178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow178 := by decide +kernel

theorem rowEval178 (x : Key → ℝ) : Integer.Sparse.eval row178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block0.form1) x := by
  rw [rowCheck178, Integer.Sparse.eval_collectBalanced, rawRowCheck178]

def rawRow179 : Integer.Sparse Key := [(key2671, -2), (key2676, 1), (key2671, 1), (key2706, 2), (key2753, -1), (key2706, -1), (key2732, -1), (key2726, -1), (key2758, 1), (key2726, 1), (key2616, 2), (key2618, -1), (key2612, -1), (key2805, -2), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2960, -1), (key2948, -1), (key2628, -2), (key2641, 1), (key2628, 1), (key2702, 2), (key2728, -1), (key2702, -1), (key2976, -1), (key2972, -1), (key2983, 1), (key2972, 1), (key2648, 1), (key2646, 1), (key2653, -1), (key2646, -1), (key2737, -1), (key2735, -1), (key2747, 1), (key2735, 1), (key2897, 1), (key2893, 1), (key2904, -1), (key2893, -1)]

theorem rawRowCheck179 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form1 = rawRow179 := by decide +kernel

def row179 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2805, -1), (key2831, 1), (key2897, 1), (key2904, -1), (key2950, 1), (key2960, -1), (key2976, -1), (key2983, 1)]

theorem rowCheck179 : row179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow179 := by decide +kernel

theorem rowEval179 (x : Key → ℝ) : Integer.Sparse.eval row179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck179, Integer.Sparse.eval_collectBalanced, rawRowCheck179]

def rawRow180 : Integer.Sparse Key := [(key2676, -2), (key2671, 1), (key2671, 1), (key2753, 2), (key2706, -1), (key2706, -1), (key2758, -1), (key2758, -1), (key2732, 1), (key2732, 1), (key2621, 2), (key2616, -1), (key2616, -1), (key2831, -2), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2950, -1), (key2950, -1), (key2641, -2), (key2628, 1), (key2628, 1), (key2728, 2), (key2702, -1), (key2702, -1), (key2983, -1), (key2983, -1), (key2976, 1), (key2976, 1), (key2653, 1), (key2653, 1), (key2648, -1), (key2648, -1), (key2747, -1), (key2747, -1), (key2737, 1), (key2737, 1), (key2904, 1), (key2904, 1), (key2897, -1), (key2897, -1)]

theorem rawRowCheck180 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form1 = rawRow180 := by decide +kernel

def row180 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2628, 2), (key2641, -2), (key2648, -2), (key2653, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, -2), (key2728, 2), (key2732, 2), (key2737, 2), (key2747, -2), (key2753, 2), (key2758, -2), (key2805, 2), (key2831, -2), (key2897, -2), (key2904, 2), (key2950, -2), (key2960, 2), (key2976, 2), (key2983, -2)]

theorem rowCheck180 : row180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow180 := by decide +kernel

theorem rowEval180 (x : Key → ℝ) : Integer.Sparse.eval row180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck180, Integer.Sparse.eval_collectBalanced, rawRowCheck180]

def rawRow181 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2732, 1), (key2671, 2), (key2726, -1), (key2758, -1), (key2671, -1), (key2676, -1), (key2706, 1), (key2753, 1), (key2809, 2), (key2829, -1), (key2835, -1), (key2612, -2), (key2948, 1), (key2960, 1), (key2612, 1), (key2618, 1), (key2805, -1), (key2831, -1), (key2702, -2), (key2972, 1), (key2976, 1), (key2628, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2641, -1), (key2702, 1), (key2728, 1), (key2735, 1), (key2737, 1), (key2893, -1), (key2897, -1), (key2646, -1), (key2648, -1), (key2893, 1), (key2904, 1), (key2646, 1), (key2653, 1), (key2735, -1), (key2747, -1)]

theorem rawRowCheck181 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form1 = rawRow181 := by decide +kernel

def row181 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2897, -1), (key2904, 1), (key2948, 1), (key2960, 1), (key2976, 1), (key2983, -1)]

theorem rowCheck181 : row181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow181 := by decide +kernel

theorem rowEval181 (x : Key → ℝ) : Integer.Sparse.eval row181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block0.form1) x := by
  rw [rowCheck181, Integer.Sparse.eval_collectBalanced, rawRowCheck181]

def rawRow182 : Integer.Sparse Key := [(key2706, -2), (key2732, 1), (key2726, 1), (key2671, 2), (key2758, -1), (key2726, -1), (key2676, -1), (key2671, -1), (key2753, 1), (key2706, 1), (key2809, 2), (key2835, -1), (key2829, -1), (key2616, -2), (key2960, 1), (key2948, 1), (key2618, 1), (key2612, 1), (key2831, -1), (key2805, -1), (key2702, -2), (key2976, 1), (key2972, 1), (key2628, 2), (key2983, -1), (key2972, -1), (key2641, -1), (key2628, -1), (key2728, 1), (key2702, 1), (key2737, 1), (key2735, 1), (key2897, -1), (key2893, -1), (key2648, -1), (key2646, -1), (key2904, 1), (key2893, 1), (key2653, 1), (key2646, 1), (key2747, -1), (key2735, -1)]

theorem rawRowCheck182 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form1 = rawRow182 := by decide +kernel

def row182 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2897, -1), (key2904, 1), (key2948, 1), (key2960, 1), (key2976, 1), (key2983, -1)]

theorem rowCheck182 : row182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow182 := by decide +kernel

theorem rowEval182 (x : Key → ℝ) : Integer.Sparse.eval row182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck182, Integer.Sparse.eval_collectBalanced, rawRowCheck182]

def rawRow183 : Integer.Sparse Key := [(key2732, -2), (key2706, 1), (key2726, 1), (key2758, 2), (key2671, -1), (key2726, -1), (key2753, -1), (key2758, -1), (key2676, 1), (key2732, 1), (key2835, 2), (key2809, -1), (key2829, -1), (key3017, -2), (key2616, 1), (key2829, 1), (key2831, 1), (key2960, 1), (key2618, -1), (key2950, -1), (key2976, -2), (key2702, 1), (key2972, 1), (key2983, 2), (key2628, -1), (key2972, -1), (key2728, -1), (key2983, -1), (key2641, 1), (key2976, 1), (key2897, 1), (key2998, 1), (key2737, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2648, 1), (key2997, 1), (key2747, 1), (key3000, 1), (key2653, -1), (key2998, -1)]

theorem rawRowCheck183 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form1 = rawRow183 := by decide +kernel

def row183 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2809, -1), (key2831, 1), (key2835, 2), (key2897, 1), (key2904, -1), (key2950, -1), (key2960, 1), (key2976, -1), (key2983, 1), (key3017, -2)]

theorem rowCheck183 : row183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow183 := by decide +kernel

theorem rowEval183 (x : Key → ℝ) : Integer.Sparse.eval row183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck183, Integer.Sparse.eval_collectBalanced, rawRowCheck183]

def rawRow184 : Integer.Sparse Key := [(key2732, -2), (key2726, 1), (key2706, 1), (key2758, 2), (key2726, -1), (key2671, -1), (key2758, -1), (key2753, -1), (key2732, 1), (key2676, 1), (key2835, 2), (key2829, -1), (key2809, -1), (key3017, -2), (key2829, 1), (key2616, 1), (key2960, 1), (key2831, 1), (key2950, -1), (key2618, -1), (key2976, -2), (key2972, 1), (key2702, 1), (key2983, 2), (key2972, -1), (key2628, -1), (key2983, -1), (key2728, -1), (key2976, 1), (key2641, 1), (key2998, 1), (key2897, 1), (key2997, -1), (key2737, -1), (key3000, -1), (key2904, -1), (key2997, 1), (key2648, 1), (key3000, 1), (key2747, 1), (key2998, -1), (key2653, -1)]

theorem rawRowCheck184 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form1 = rawRow184 := by decide +kernel

def row184 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2628, -1), (key2641, 1), (key2648, 1), (key2653, -1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2737, -1), (key2747, 1), (key2753, -1), (key2758, 1), (key2809, -1), (key2831, 1), (key2835, 2), (key2897, 1), (key2904, -1), (key2950, -1), (key2960, 1), (key2976, -1), (key2983, 1), (key3017, -2)]

theorem rowCheck184 : row184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow184 := by decide +kernel

theorem rowEval184 (x : Key → ℝ) : Integer.Sparse.eval row184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck184, Integer.Sparse.eval_collectBalanced, rawRowCheck184]

def rawRow185 : Integer.Sparse Key := [(key2753, -2), (key2758, 1), (key2758, 1), (key2676, 2), (key2732, -1), (key2732, -1), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key3012, 2), (key3017, -1), (key3017, -1), (key2621, -2), (key2835, 1), (key2835, 1), (key2616, 1), (key2616, 1), (key2809, -1), (key2809, -1), (key2728, -2), (key2983, 1), (key2983, 1), (key2641, 2), (key2976, -1), (key2976, -1), (key2628, -1), (key2628, -1), (key2702, 1), (key2702, 1), (key2747, 1), (key2747, 1), (key2904, -1), (key2904, -1), (key2653, -1), (key2653, -1), (key2897, 1), (key2897, 1), (key2648, 1), (key2648, 1), (key2737, -1), (key2737, -1)]

theorem rawRowCheck185 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form1 = rawRow185 := by decide +kernel

def row185 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2671, -2), (key2676, 2), (key2702, 2), (key2706, 2), (key2728, -2), (key2732, -2), (key2737, -2), (key2747, 2), (key2753, -2), (key2758, 2), (key2809, -2), (key2835, 2), (key2897, 2), (key2904, -2), (key2976, -2), (key2983, 2), (key3012, 2), (key3017, -2)]

theorem rowCheck185 : row185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow185 := by decide +kernel

theorem rowEval185 (x : Key → ℝ) : Integer.Sparse.eval row185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck185, Integer.Sparse.eval_collectBalanced, rawRowCheck185]

def rawRow186 : Integer.Sparse Key := [(key2758, -2), (key2753, 1), (key2758, 1), (key2732, 2), (key2676, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key3017, 2), (key3012, -1), (key3017, -1), (key2835, -2), (key2621, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2616, -1), (key2829, -1), (key2983, -2), (key2728, 1), (key2983, 1), (key2976, 2), (key2641, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2628, 1), (key2972, 1), (key2904, 1), (key3000, 1), (key2747, -1), (key3000, -1), (key2897, -1), (key2998, -1), (key2653, 1), (key2998, 1), (key2737, 1), (key2997, 1), (key2648, -1), (key2997, -1)]

theorem rawRowCheck186 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form1 = rawRow186 := by decide +kernel

def row186 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2809, 1), (key2835, -1), (key2897, -1), (key2904, 1), (key2976, 1), (key2983, -1), (key3012, -1), (key3017, 1)]

theorem rowCheck186 : row186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow186 := by decide +kernel

theorem rowEval186 (x : Key → ℝ) : Integer.Sparse.eval row186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck186, Integer.Sparse.eval_collectBalanced, rawRowCheck186]

def rawRow187 : Integer.Sparse Key := [(key2758, -2), (key2758, 1), (key2753, 1), (key2732, 2), (key2732, -1), (key2676, -1), (key2726, -1), (key2706, -1), (key2726, 1), (key2671, 1), (key3017, 2), (key3017, -1), (key3012, -1), (key2835, -2), (key2835, 1), (key2621, 1), (key2829, 1), (key2809, 1), (key2829, -1), (key2616, -1), (key2983, -2), (key2983, 1), (key2728, 1), (key2976, 2), (key2976, -1), (key2641, -1), (key2972, -1), (key2702, -1), (key2972, 1), (key2628, 1), (key3000, 1), (key2904, 1), (key3000, -1), (key2747, -1), (key2998, -1), (key2897, -1), (key2998, 1), (key2653, 1), (key2997, 1), (key2737, 1), (key2997, -1), (key2648, -1)]

theorem rawRowCheck187 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form1 = rawRow187 := by decide +kernel

def row187 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2671, 1), (key2676, -1), (key2702, -1), (key2706, -1), (key2728, 1), (key2732, 1), (key2737, 1), (key2747, -1), (key2753, 1), (key2758, -1), (key2809, 1), (key2835, -1), (key2897, -1), (key2904, 1), (key2976, 1), (key2983, -1), (key3012, -1), (key3017, 1)]

theorem rowCheck187 : row187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow187 := by decide +kernel

theorem rowEval187 (x : Key → ℝ) : Integer.Sparse.eval row187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck187, Integer.Sparse.eval_collectBalanced, rawRowCheck187]

def rawRow188 : Integer.Sparse Key := [(key2786, -2), (key2794, 1), (key2798, 1), (key2809, 2), (key2860, -1), (key2920, -1), (key2829, -1), (key2835, -1), (key2870, 1), (key2923, 1), (key2632, 2), (key2640, -1), (key2644, -1), (key2706, -2), (key2860, 1), (key3023, 1), (key2726, 1), (key2732, 1), (key2870, -1), (key3026, -1), (key2612, -2), (key2646, 1), (key2653, 1), (key2667, 2), (key2735, -1), (key2747, -1), (key2936, -1), (key2943, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2618, 1), (key2628, -1), (key2641, -1), (key2667, -1), (key2673, -1), (key2702, 1), (key2728, 1), (key2782, 1), (key2795, 1), (key2805, -1), (key2831, -1)]

theorem rawRowCheck188 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form1 = rawRow188 := by decide +kernel

def row188 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2644, -1), (key2646, 1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, 1), (key2706, -2), (key2726, 1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2782, 1), (key2786, -2), (key2794, 1), (key2795, 1), (key2798, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2920, -1), (key2923, 1), (key2936, -1), (key2943, -1), (key2948, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck188 : row188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow188 := by decide +kernel

theorem rowEval188 (x : Key → ℝ) : Integer.Sparse.eval row188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block0.form1) x := by
  rw [rowCheck188, Integer.Sparse.eval_collectBalanced, rawRowCheck188]

def rawRow189 : Integer.Sparse Key := [(key2786, -2), (key2798, 1), (key2794, 1), (key2809, 2), (key2920, -1), (key2860, -1), (key2835, -1), (key2829, -1), (key2923, 1), (key2870, 1), (key2632, 2), (key2644, -1), (key2640, -1), (key2706, -2), (key3023, 1), (key2860, 1), (key2732, 1), (key2726, 1), (key3026, -1), (key2870, -1), (key2616, -2), (key2653, 1), (key2646, 1), (key2667, 2), (key2747, -1), (key2735, -1), (key2943, -1), (key2936, -1), (key2960, 1), (key2948, 1), (key2618, 1), (key2612, 1), (key2641, -1), (key2628, -1), (key2673, -1), (key2667, -1), (key2728, 1), (key2702, 1), (key2795, 1), (key2782, 1), (key2831, -1), (key2805, -1)]

theorem rawRowCheck189 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form1 = rawRow189 := by decide +kernel

def row189 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2644, -1), (key2646, 1), (key2653, 1), (key2667, 1), (key2673, -1), (key2702, 1), (key2706, -2), (key2726, 1), (key2728, 1), (key2732, 1), (key2735, -1), (key2747, -1), (key2782, 1), (key2786, -2), (key2794, 1), (key2795, 1), (key2798, 1), (key2805, -1), (key2809, 2), (key2829, -1), (key2831, -1), (key2835, -1), (key2920, -1), (key2923, 1), (key2936, -1), (key2943, -1), (key2948, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

theorem rowCheck189 : row189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow189 := by decide +kernel

theorem rowEval189 (x : Key → ℝ) : Integer.Sparse.eval row189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck189, Integer.Sparse.eval_collectBalanced, rawRowCheck189]

def rawRow190 : Integer.Sparse Key := [(key2798, -2), (key2786, 1), (key2794, 1), (key2920, 2), (key2809, -1), (key2860, -1), (key2923, -1), (key2927, -1), (key2835, 1), (key2885, 1), (key2644, 2), (key2632, -1), (key2640, -1), (key3023, -2), (key2706, 1), (key2860, 1), (key3026, 1), (key3030, 1), (key2732, -1), (key2885, -1), (key2660, -2), (key2616, 1), (key2640, 1), (key2747, 2), (key2667, -1), (key2735, -1), (key2960, -1), (key3000, -1), (key2943, 1), (key2998, 1), (key2641, 1), (key2653, 1), (key2618, -1), (key2648, -1), (key2728, -1), (key2747, -1), (key2673, 1), (key2737, 1), (key2831, 1), (key2904, 1), (key2795, -1), (key2897, -1)]

theorem rawRowCheck190 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form1 = rawRow190 := by decide +kernel

def row190 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 2), (key2648, -1), (key2653, 1), (key2660, -2), (key2667, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 1), (key2794, 1), (key2795, -1), (key2798, -2), (key2809, -1), (key2831, 1), (key2835, 1), (key2897, -1), (key2904, 1), (key2920, 2), (key2923, -1), (key2927, -1), (key2943, 1), (key2960, -1), (key2998, 1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck190 : row190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow190 := by decide +kernel

theorem rowEval190 (x : Key → ℝ) : Integer.Sparse.eval row190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck190, Integer.Sparse.eval_collectBalanced, rawRowCheck190]

def rawRow191 : Integer.Sparse Key := [(key2798, -2), (key2794, 1), (key2786, 1), (key2920, 2), (key2860, -1), (key2809, -1), (key2927, -1), (key2923, -1), (key2885, 1), (key2835, 1), (key2644, 2), (key2640, -1), (key2632, -1), (key3023, -2), (key2860, 1), (key2706, 1), (key3030, 1), (key3026, 1), (key2885, -1), (key2732, -1), (key2660, -2), (key2640, 1), (key2616, 1), (key2747, 2), (key2735, -1), (key2667, -1), (key3000, -1), (key2960, -1), (key2998, 1), (key2943, 1), (key2653, 1), (key2641, 1), (key2648, -1), (key2618, -1), (key2747, -1), (key2728, -1), (key2737, 1), (key2673, 1), (key2904, 1), (key2831, 1), (key2897, -1), (key2795, -1)]

theorem rawRowCheck191 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form1 = rawRow191 := by decide +kernel

def row191 : Integer.Sparse Key := [(key2616, 1), (key2618, -1), (key2632, -1), (key2641, 1), (key2644, 2), (key2648, -1), (key2653, 1), (key2660, -2), (key2667, -1), (key2673, 1), (key2706, 1), (key2728, -1), (key2732, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 1), (key2794, 1), (key2795, -1), (key2798, -2), (key2809, -1), (key2831, 1), (key2835, 1), (key2897, -1), (key2904, 1), (key2920, 2), (key2923, -1), (key2927, -1), (key2943, 1), (key2960, -1), (key2998, 1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck191 : row191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow191 := by decide +kernel

theorem rowEval191 (x : Key → ℝ) : Integer.Sparse.eval row191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck191, Integer.Sparse.eval_collectBalanced, rawRowCheck191]

end MUB6.Certificate.GramRows

end OAI
