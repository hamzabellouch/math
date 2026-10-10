import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow352 : Integer.Sparse Key := [(key1558, -1), (key1563, -1), (key1901, 2), (key1395, 1), (key1401, 1), (key1898, -1), (key1901, -1), (key1395, -2), (key1550, 1), (key1558, 1), (key1595, 1), (key1600, 1), (key1913, -2), (key1300, -1), (key1306, -1), (key1905, 1), (key1913, 1), (key1300, 2), (key1577, -1), (key1595, -1), (key1446, -1), (key1451, -1), (key1928, 1), (key1931, 1), (key1328, 1), (key1333, 1), (key1922, -1), (key1931, -1), (key1320, -1), (key1328, -1), (key1428, 1), (key1446, 1), (key1482, 2), (key1691, -1), (key1694, -1), (key1356, -2), (key1685, 1), (key1694, 1), (key1353, 1), (key1356, 1), (key1474, -1), (key1482, -1)]

theorem rawRowCheck352 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form2 = rawRow352 := by decide +kernel

def row352 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck352 : row352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow352 := by decide +kernel

theorem rowEval352 (x : Key → ℝ) : Integer.Sparse.eval row352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck352, Integer.Sparse.eval_collectBalanced, rawRowCheck352]

def rawRow353 : Integer.Sparse Key := [(key1563, -1), (key1558, -1), (key1901, 2), (key1401, 1), (key1395, 1), (key1901, -1), (key1898, -1), (key1395, -2), (key1558, 1), (key1550, 1), (key1600, 1), (key1595, 1), (key1913, -2), (key1306, -1), (key1300, -1), (key1913, 1), (key1905, 1), (key1300, 2), (key1595, -1), (key1577, -1), (key1451, -1), (key1446, -1), (key1931, 1), (key1928, 1), (key1333, 1), (key1328, 1), (key1931, -1), (key1922, -1), (key1328, -1), (key1320, -1), (key1446, 1), (key1428, 1), (key1482, 2), (key1694, -1), (key1691, -1), (key1356, -2), (key1694, 1), (key1685, 1), (key1356, 1), (key1353, 1), (key1482, -1), (key1474, -1)]

theorem rawRowCheck353 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form2 = rawRow353 := by decide +kernel

def row353 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck353 : row353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow353 := by decide +kernel

theorem rowEval353 (x : Key → ℝ) : Integer.Sparse.eval row353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck353, Integer.Sparse.eval_collectBalanced, rawRowCheck353]

def rawRow354 : Integer.Sparse Key := [(key1558, -1), (key1901, -1), (key1563, 2), (key1550, 1), (key1898, 1), (key1401, -1), (key1563, -1), (key1550, -2), (key1395, 1), (key1558, 1), (key1595, 1), (key1913, 1), (key1600, -2), (key1577, -1), (key1905, -1), (key1306, 1), (key1600, 1), (key1577, 2), (key1300, -1), (key1595, -1), (key1635, -1), (key1928, -1), (key1451, 1), (key1644, 1), (key1626, 1), (key1922, 1), (key1333, -1), (key1644, -1), (key1428, -1), (key1626, -1), (key1320, 1), (key1635, 1), (key1691, 2), (key1482, -1), (key1694, -1), (key1685, -2), (key1356, 1), (key1694, 1), (key1474, 1), (key1685, 1), (key1353, -1), (key1691, -1)]

theorem rawRowCheck354 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form2 = rawRow354 := by decide +kernel

def row354 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck354 : row354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow354 := by decide +kernel

theorem rowEval354 (x : Key → ℝ) : Integer.Sparse.eval row354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck354, Integer.Sparse.eval_collectBalanced, rawRowCheck354]

def rawRow355 : Integer.Sparse Key := [(key1901, -1), (key1558, -1), (key1563, 2), (key1898, 1), (key1550, 1), (key1563, -1), (key1401, -1), (key1550, -2), (key1558, 1), (key1395, 1), (key1913, 1), (key1595, 1), (key1600, -2), (key1905, -1), (key1577, -1), (key1600, 1), (key1306, 1), (key1577, 2), (key1595, -1), (key1300, -1), (key1928, -1), (key1635, -1), (key1644, 1), (key1451, 1), (key1922, 1), (key1626, 1), (key1644, -1), (key1333, -1), (key1626, -1), (key1428, -1), (key1635, 1), (key1320, 1), (key1691, 2), (key1694, -1), (key1482, -1), (key1685, -2), (key1694, 1), (key1356, 1), (key1685, 1), (key1474, 1), (key1691, -1), (key1353, -1)]

theorem rawRowCheck355 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form2 = rawRow355 := by decide +kernel

def row355 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck355 : row355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow355 := by decide +kernel

theorem rowEval355 (x : Key → ℝ) : Integer.Sparse.eval row355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck355, Integer.Sparse.eval_collectBalanced, rawRowCheck355]

def rawRow356 : Integer.Sparse Key := [(key1428, -1), (key1428, -1), (key1474, 2), (key1577, 1), (key1577, 1), (key1685, -1), (key1685, -1), (key1905, -2), (key1922, 1), (key1922, 1), (key1320, 1), (key1320, 1), (key1353, -2), (key1550, -1), (key1550, -1), (key1691, 1), (key1691, 1), (key1898, 2), (key1928, -1), (key1928, -1), (key1300, -1), (key1300, -1), (key1356, 1), (key1356, 1), (key1395, 1), (key1395, 1), (key1482, -1), (key1482, -1), (key1901, -1), (key1901, -1), (key1913, 1), (key1913, 1), (key1306, 2), (key1333, -1), (key1333, -1), (key1401, -2), (key1451, 1), (key1451, 1), (key1563, 1), (key1563, 1), (key1600, -1), (key1600, -1)]

theorem rawRowCheck356 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form2 = rawRow356 := by decide +kernel

def row356 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

theorem rowCheck356 : row356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow356 := by decide +kernel

theorem rowEval356 (x : Key → ℝ) : Integer.Sparse.eval row356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck356, Integer.Sparse.eval_collectBalanced, rawRowCheck356]

def rawRow357 : Integer.Sparse Key := [(key1428, -1), (key1474, -1), (key1428, 2), (key1626, 1), (key1685, 1), (key1577, -1), (key1626, -1), (key1922, -2), (key1905, 1), (key1922, 1), (key1320, 1), (key1353, 1), (key1320, -2), (key1635, -1), (key1691, -1), (key1550, 1), (key1635, 1), (key1928, 2), (key1898, -1), (key1928, -1), (key1328, -1), (key1356, -1), (key1300, 1), (key1328, 1), (key1446, 1), (key1482, 1), (key1395, -1), (key1446, -1), (key1913, -1), (key1931, -1), (key1901, 1), (key1931, 1), (key1333, 2), (key1306, -1), (key1333, -1), (key1451, -2), (key1401, 1), (key1451, 1), (key1600, 1), (key1644, 1), (key1563, -1), (key1644, -1)]

theorem rawRowCheck357 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form2 = rawRow357 := by decide +kernel

def row357 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck357 : row357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow357 := by decide +kernel

theorem rowEval357 (x : Key → ℝ) : Integer.Sparse.eval row357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck357, Integer.Sparse.eval_collectBalanced, rawRowCheck357]

def rawRow358 : Integer.Sparse Key := [(key1474, -1), (key1428, -1), (key1428, 2), (key1685, 1), (key1626, 1), (key1626, -1), (key1577, -1), (key1922, -2), (key1922, 1), (key1905, 1), (key1353, 1), (key1320, 1), (key1320, -2), (key1691, -1), (key1635, -1), (key1635, 1), (key1550, 1), (key1928, 2), (key1928, -1), (key1898, -1), (key1356, -1), (key1328, -1), (key1328, 1), (key1300, 1), (key1482, 1), (key1446, 1), (key1446, -1), (key1395, -1), (key1931, -1), (key1913, -1), (key1931, 1), (key1901, 1), (key1333, 2), (key1333, -1), (key1306, -1), (key1451, -2), (key1451, 1), (key1401, 1), (key1644, 1), (key1600, 1), (key1644, -1), (key1563, -1)]

theorem rawRowCheck358 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form2 = rawRow358 := by decide +kernel

def row358 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck358 : row358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow358 := by decide +kernel

theorem rowEval358 (x : Key → ℝ) : Integer.Sparse.eval row358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck358, Integer.Sparse.eval_collectBalanced, rawRowCheck358]

def rawRow359 : Integer.Sparse Key := [(key1577, -1), (key1577, -1), (key1905, 2), (key1428, 1), (key1428, 1), (key1922, -1), (key1922, -1), (key1474, -2), (key1685, 1), (key1685, 1), (key1550, 1), (key1550, 1), (key1898, -2), (key1320, -1), (key1320, -1), (key1928, 1), (key1928, 1), (key1353, 2), (key1691, -1), (key1691, -1), (key1395, -1), (key1395, -1), (key1901, 1), (key1901, 1), (key1300, 1), (key1300, 1), (key1913, -1), (key1913, -1), (key1356, -1), (key1356, -1), (key1482, 1), (key1482, 1), (key1401, 2), (key1563, -1), (key1563, -1), (key1306, -2), (key1600, 1), (key1600, 1), (key1333, 1), (key1333, 1), (key1451, -1), (key1451, -1)]

theorem rawRowCheck359 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form2 = rawRow359 := by decide +kernel

def row359 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

theorem rowCheck359 : row359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow359 := by decide +kernel

theorem rowEval359 (x : Key → ℝ) : Integer.Sparse.eval row359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck359, Integer.Sparse.eval_collectBalanced, rawRowCheck359]

def rawRow360 : Integer.Sparse Key := [(key1577, -1), (key1905, -1), (key1577, 2), (key1626, 1), (key1922, 1), (key1428, -1), (key1626, -1), (key1685, -2), (key1474, 1), (key1685, 1), (key1550, 1), (key1898, 1), (key1550, -2), (key1635, -1), (key1928, -1), (key1320, 1), (key1635, 1), (key1691, 2), (key1353, -1), (key1691, -1), (key1558, -1), (key1901, -1), (key1395, 1), (key1558, 1), (key1595, 1), (key1913, 1), (key1300, -1), (key1595, -1), (key1482, -1), (key1694, -1), (key1356, 1), (key1694, 1), (key1563, 2), (key1401, -1), (key1563, -1), (key1600, -2), (key1306, 1), (key1600, 1), (key1451, 1), (key1644, 1), (key1333, -1), (key1644, -1)]

theorem rawRowCheck360 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form2 = rawRow360 := by decide +kernel

def row360 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck360 : row360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow360 := by decide +kernel

theorem rowEval360 (x : Key → ℝ) : Integer.Sparse.eval row360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck360, Integer.Sparse.eval_collectBalanced, rawRowCheck360]

def rawRow361 : Integer.Sparse Key := [(key1905, -1), (key1577, -1), (key1577, 2), (key1922, 1), (key1626, 1), (key1626, -1), (key1428, -1), (key1685, -2), (key1685, 1), (key1474, 1), (key1898, 1), (key1550, 1), (key1550, -2), (key1928, -1), (key1635, -1), (key1635, 1), (key1320, 1), (key1691, 2), (key1691, -1), (key1353, -1), (key1901, -1), (key1558, -1), (key1558, 1), (key1395, 1), (key1913, 1), (key1595, 1), (key1595, -1), (key1300, -1), (key1694, -1), (key1482, -1), (key1694, 1), (key1356, 1), (key1563, 2), (key1563, -1), (key1401, -1), (key1600, -2), (key1600, 1), (key1306, 1), (key1644, 1), (key1451, 1), (key1644, -1), (key1333, -1)]

theorem rawRowCheck361 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form2 = rawRow361 := by decide +kernel

def row361 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck361 : row361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow361 := by decide +kernel

theorem rowEval361 (x : Key → ℝ) : Integer.Sparse.eval row361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck361, Integer.Sparse.eval_collectBalanced, rawRowCheck361]

def rawRow362 : Integer.Sparse Key := [(key1626, -1), (key1685, -1), (key1922, 2), (key1428, 1), (key1474, 1), (key1905, -1), (key1922, -1), (key1428, -2), (key1577, 1), (key1626, 1), (key1635, 1), (key1691, 1), (key1928, -2), (key1320, -1), (key1353, -1), (key1898, 1), (key1928, 1), (key1320, 2), (key1550, -1), (key1635, -1), (key1446, -1), (key1482, -1), (key1913, 1), (key1931, 1), (key1328, 1), (key1356, 1), (key1901, -1), (key1931, -1), (key1300, -1), (key1328, -1), (key1395, 1), (key1446, 1), (key1451, 2), (key1600, -1), (key1644, -1), (key1333, -2), (key1563, 1), (key1644, 1), (key1306, 1), (key1333, 1), (key1401, -1), (key1451, -1)]

theorem rawRowCheck362 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form2 = rawRow362 := by decide +kernel

def row362 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck362 : row362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow362 := by decide +kernel

theorem rowEval362 (x : Key → ℝ) : Integer.Sparse.eval row362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck362, Integer.Sparse.eval_collectBalanced, rawRowCheck362]

def rawRow363 : Integer.Sparse Key := [(key1685, -1), (key1626, -1), (key1922, 2), (key1474, 1), (key1428, 1), (key1922, -1), (key1905, -1), (key1428, -2), (key1626, 1), (key1577, 1), (key1691, 1), (key1635, 1), (key1928, -2), (key1353, -1), (key1320, -1), (key1928, 1), (key1898, 1), (key1320, 2), (key1635, -1), (key1550, -1), (key1482, -1), (key1446, -1), (key1931, 1), (key1913, 1), (key1356, 1), (key1328, 1), (key1931, -1), (key1901, -1), (key1328, -1), (key1300, -1), (key1446, 1), (key1395, 1), (key1451, 2), (key1644, -1), (key1600, -1), (key1333, -2), (key1644, 1), (key1563, 1), (key1333, 1), (key1306, 1), (key1451, -1), (key1401, -1)]

theorem rawRowCheck363 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form2 = rawRow363 := by decide +kernel

def row363 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck363 : row363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow363 := by decide +kernel

theorem rowEval363 (x : Key → ℝ) : Integer.Sparse.eval row363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck363, Integer.Sparse.eval_collectBalanced, rawRowCheck363]

def rawRow364 : Integer.Sparse Key := [(key1626, -1), (key1922, -1), (key1685, 2), (key1577, 1), (key1905, 1), (key1474, -1), (key1685, -1), (key1577, -2), (key1428, 1), (key1626, 1), (key1635, 1), (key1928, 1), (key1691, -2), (key1550, -1), (key1898, -1), (key1353, 1), (key1691, 1), (key1550, 2), (key1320, -1), (key1635, -1), (key1595, -1), (key1913, -1), (key1482, 1), (key1694, 1), (key1558, 1), (key1901, 1), (key1356, -1), (key1694, -1), (key1395, -1), (key1558, -1), (key1300, 1), (key1595, 1), (key1600, 2), (key1451, -1), (key1644, -1), (key1563, -2), (key1333, 1), (key1644, 1), (key1401, 1), (key1563, 1), (key1306, -1), (key1600, -1)]

theorem rawRowCheck364 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form2 = rawRow364 := by decide +kernel

def row364 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck364 : row364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow364 := by decide +kernel

theorem rowEval364 (x : Key → ℝ) : Integer.Sparse.eval row364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck364, Integer.Sparse.eval_collectBalanced, rawRowCheck364]

def rawRow365 : Integer.Sparse Key := [(key1922, -1), (key1626, -1), (key1685, 2), (key1905, 1), (key1577, 1), (key1685, -1), (key1474, -1), (key1577, -2), (key1626, 1), (key1428, 1), (key1928, 1), (key1635, 1), (key1691, -2), (key1898, -1), (key1550, -1), (key1691, 1), (key1353, 1), (key1550, 2), (key1635, -1), (key1320, -1), (key1913, -1), (key1595, -1), (key1694, 1), (key1482, 1), (key1901, 1), (key1558, 1), (key1694, -1), (key1356, -1), (key1558, -1), (key1395, -1), (key1595, 1), (key1300, 1), (key1600, 2), (key1644, -1), (key1451, -1), (key1563, -2), (key1644, 1), (key1333, 1), (key1563, 1), (key1401, 1), (key1600, -1), (key1306, -1)]

theorem rawRowCheck365 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form2 = rawRow365 := by decide +kernel

def row365 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck365 : row365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow365 := by decide +kernel

theorem rowEval365 (x : Key → ℝ) : Integer.Sparse.eval row365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck365, Integer.Sparse.eval_collectBalanced, rawRowCheck365]

def rawRow366 : Integer.Sparse Key := [(key1446, -1), (key1451, -1), (key1482, 2), (key1595, 1), (key1600, 1), (key1691, -1), (key1694, -1), (key1913, -2), (key1928, 1), (key1931, 1), (key1328, 1), (key1333, 1), (key1356, -2), (key1558, -1), (key1563, -1), (key1685, 1), (key1694, 1), (key1901, 2), (key1922, -1), (key1931, -1), (key1300, -1), (key1306, -1), (key1353, 1), (key1356, 1), (key1395, 1), (key1401, 1), (key1474, -1), (key1482, -1), (key1898, -1), (key1901, -1), (key1905, 1), (key1913, 1), (key1300, 2), (key1320, -1), (key1328, -1), (key1395, -2), (key1428, 1), (key1446, 1), (key1550, 1), (key1558, 1), (key1577, -1), (key1595, -1)]

theorem rawRowCheck366 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form2 = rawRow366 := by decide +kernel

def row366 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck366 : row366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow366 := by decide +kernel

theorem rowEval366 (x : Key → ℝ) : Integer.Sparse.eval row366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck366, Integer.Sparse.eval_collectBalanced, rawRowCheck366]

def rawRow367 : Integer.Sparse Key := [(key1451, -1), (key1446, -1), (key1482, 2), (key1600, 1), (key1595, 1), (key1694, -1), (key1691, -1), (key1913, -2), (key1931, 1), (key1928, 1), (key1333, 1), (key1328, 1), (key1356, -2), (key1563, -1), (key1558, -1), (key1694, 1), (key1685, 1), (key1901, 2), (key1931, -1), (key1922, -1), (key1306, -1), (key1300, -1), (key1356, 1), (key1353, 1), (key1401, 1), (key1395, 1), (key1482, -1), (key1474, -1), (key1901, -1), (key1898, -1), (key1913, 1), (key1905, 1), (key1300, 2), (key1328, -1), (key1320, -1), (key1395, -2), (key1446, 1), (key1428, 1), (key1558, 1), (key1550, 1), (key1595, -1), (key1577, -1)]

theorem rawRowCheck367 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form2 = rawRow367 := by decide +kernel

def row367 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck367 : row367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow367 := by decide +kernel

theorem rowEval367 (x : Key → ℝ) : Integer.Sparse.eval row367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck367, Integer.Sparse.eval_collectBalanced, rawRowCheck367]

def rawRow368 : Integer.Sparse Key := [(key1446, -1), (key1482, -1), (key1451, 2), (key1635, 1), (key1691, 1), (key1600, -1), (key1644, -1), (key1928, -2), (key1913, 1), (key1931, 1), (key1328, 1), (key1356, 1), (key1333, -2), (key1626, -1), (key1685, -1), (key1563, 1), (key1644, 1), (key1922, 2), (key1901, -1), (key1931, -1), (key1320, -1), (key1353, -1), (key1306, 1), (key1333, 1), (key1428, 1), (key1474, 1), (key1401, -1), (key1451, -1), (key1905, -1), (key1922, -1), (key1898, 1), (key1928, 1), (key1320, 2), (key1300, -1), (key1328, -1), (key1428, -2), (key1395, 1), (key1446, 1), (key1577, 1), (key1626, 1), (key1550, -1), (key1635, -1)]

theorem rawRowCheck368 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form2 = rawRow368 := by decide +kernel

def row368 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck368 : row368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow368 := by decide +kernel

theorem rowEval368 (x : Key → ℝ) : Integer.Sparse.eval row368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck368, Integer.Sparse.eval_collectBalanced, rawRowCheck368]

def rawRow369 : Integer.Sparse Key := [(key1482, -1), (key1446, -1), (key1451, 2), (key1691, 1), (key1635, 1), (key1644, -1), (key1600, -1), (key1928, -2), (key1931, 1), (key1913, 1), (key1356, 1), (key1328, 1), (key1333, -2), (key1685, -1), (key1626, -1), (key1644, 1), (key1563, 1), (key1922, 2), (key1931, -1), (key1901, -1), (key1353, -1), (key1320, -1), (key1333, 1), (key1306, 1), (key1474, 1), (key1428, 1), (key1451, -1), (key1401, -1), (key1922, -1), (key1905, -1), (key1928, 1), (key1898, 1), (key1320, 2), (key1328, -1), (key1300, -1), (key1428, -2), (key1446, 1), (key1395, 1), (key1626, 1), (key1577, 1), (key1635, -1), (key1550, -1)]

theorem rawRowCheck369 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form2 = rawRow369 := by decide +kernel

def row369 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck369 : row369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow369 := by decide +kernel

theorem rowEval369 (x : Key → ℝ) : Integer.Sparse.eval row369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck369, Integer.Sparse.eval_collectBalanced, rawRowCheck369]

def rawRow370 : Integer.Sparse Key := [(key1595, -1), (key1600, -1), (key1913, 2), (key1446, 1), (key1451, 1), (key1928, -1), (key1931, -1), (key1482, -2), (key1691, 1), (key1694, 1), (key1558, 1), (key1563, 1), (key1901, -2), (key1328, -1), (key1333, -1), (key1922, 1), (key1931, 1), (key1356, 2), (key1685, -1), (key1694, -1), (key1395, -1), (key1401, -1), (key1898, 1), (key1901, 1), (key1300, 1), (key1306, 1), (key1905, -1), (key1913, -1), (key1353, -1), (key1356, -1), (key1474, 1), (key1482, 1), (key1395, 2), (key1550, -1), (key1558, -1), (key1300, -2), (key1577, 1), (key1595, 1), (key1320, 1), (key1328, 1), (key1428, -1), (key1446, -1)]

theorem rawRowCheck370 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form2 = rawRow370 := by decide +kernel

def row370 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck370 : row370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow370 := by decide +kernel

theorem rowEval370 (x : Key → ℝ) : Integer.Sparse.eval row370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck370, Integer.Sparse.eval_collectBalanced, rawRowCheck370]

def rawRow371 : Integer.Sparse Key := [(key1600, -1), (key1595, -1), (key1913, 2), (key1451, 1), (key1446, 1), (key1931, -1), (key1928, -1), (key1482, -2), (key1694, 1), (key1691, 1), (key1563, 1), (key1558, 1), (key1901, -2), (key1333, -1), (key1328, -1), (key1931, 1), (key1922, 1), (key1356, 2), (key1694, -1), (key1685, -1), (key1401, -1), (key1395, -1), (key1901, 1), (key1898, 1), (key1306, 1), (key1300, 1), (key1913, -1), (key1905, -1), (key1356, -1), (key1353, -1), (key1482, 1), (key1474, 1), (key1395, 2), (key1558, -1), (key1550, -1), (key1300, -2), (key1595, 1), (key1577, 1), (key1328, 1), (key1320, 1), (key1446, -1), (key1428, -1)]

theorem rawRowCheck371 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form2 = rawRow371 := by decide +kernel

def row371 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck371 : row371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow371 := by decide +kernel

theorem rowEval371 (x : Key → ℝ) : Integer.Sparse.eval row371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck371, Integer.Sparse.eval_collectBalanced, rawRowCheck371]

def rawRow372 : Integer.Sparse Key := [(key1595, -1), (key1913, -1), (key1600, 2), (key1635, 1), (key1928, 1), (key1451, -1), (key1644, -1), (key1691, -2), (key1482, 1), (key1694, 1), (key1558, 1), (key1901, 1), (key1563, -2), (key1626, -1), (key1922, -1), (key1333, 1), (key1644, 1), (key1685, 2), (key1356, -1), (key1694, -1), (key1550, -1), (key1898, -1), (key1401, 1), (key1563, 1), (key1577, 1), (key1905, 1), (key1306, -1), (key1600, -1), (key1474, -1), (key1685, -1), (key1353, 1), (key1691, 1), (key1550, 2), (key1395, -1), (key1558, -1), (key1577, -2), (key1300, 1), (key1595, 1), (key1428, 1), (key1626, 1), (key1320, -1), (key1635, -1)]

theorem rawRowCheck372 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form2 = rawRow372 := by decide +kernel

def row372 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck372 : row372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow372 := by decide +kernel

theorem rowEval372 (x : Key → ℝ) : Integer.Sparse.eval row372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck372, Integer.Sparse.eval_collectBalanced, rawRowCheck372]

def rawRow373 : Integer.Sparse Key := [(key1913, -1), (key1595, -1), (key1600, 2), (key1928, 1), (key1635, 1), (key1644, -1), (key1451, -1), (key1691, -2), (key1694, 1), (key1482, 1), (key1901, 1), (key1558, 1), (key1563, -2), (key1922, -1), (key1626, -1), (key1644, 1), (key1333, 1), (key1685, 2), (key1694, -1), (key1356, -1), (key1898, -1), (key1550, -1), (key1563, 1), (key1401, 1), (key1905, 1), (key1577, 1), (key1600, -1), (key1306, -1), (key1685, -1), (key1474, -1), (key1691, 1), (key1353, 1), (key1550, 2), (key1558, -1), (key1395, -1), (key1577, -2), (key1595, 1), (key1300, 1), (key1626, 1), (key1428, 1), (key1635, -1), (key1320, -1)]

theorem rawRowCheck373 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form2 = rawRow373 := by decide +kernel

def row373 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck373 : row373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow373 := by decide +kernel

theorem rowEval373 (x : Key → ℝ) : Integer.Sparse.eval row373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck373, Integer.Sparse.eval_collectBalanced, rawRowCheck373]

def rawRow374 : Integer.Sparse Key := [(key1635, -1), (key1691, -1), (key1928, 2), (key1446, 1), (key1482, 1), (key1913, -1), (key1931, -1), (key1451, -2), (key1600, 1), (key1644, 1), (key1626, 1), (key1685, 1), (key1922, -2), (key1328, -1), (key1356, -1), (key1901, 1), (key1931, 1), (key1333, 2), (key1563, -1), (key1644, -1), (key1428, -1), (key1474, -1), (key1905, 1), (key1922, 1), (key1320, 1), (key1353, 1), (key1898, -1), (key1928, -1), (key1306, -1), (key1333, -1), (key1401, 1), (key1451, 1), (key1428, 2), (key1577, -1), (key1626, -1), (key1320, -2), (key1550, 1), (key1635, 1), (key1300, 1), (key1328, 1), (key1395, -1), (key1446, -1)]

theorem rawRowCheck374 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form2 = rawRow374 := by decide +kernel

def row374 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck374 : row374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow374 := by decide +kernel

theorem rowEval374 (x : Key → ℝ) : Integer.Sparse.eval row374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck374, Integer.Sparse.eval_collectBalanced, rawRowCheck374]

def rawRow375 : Integer.Sparse Key := [(key1691, -1), (key1635, -1), (key1928, 2), (key1482, 1), (key1446, 1), (key1931, -1), (key1913, -1), (key1451, -2), (key1644, 1), (key1600, 1), (key1685, 1), (key1626, 1), (key1922, -2), (key1356, -1), (key1328, -1), (key1931, 1), (key1901, 1), (key1333, 2), (key1644, -1), (key1563, -1), (key1474, -1), (key1428, -1), (key1922, 1), (key1905, 1), (key1353, 1), (key1320, 1), (key1928, -1), (key1898, -1), (key1333, -1), (key1306, -1), (key1451, 1), (key1401, 1), (key1428, 2), (key1626, -1), (key1577, -1), (key1320, -2), (key1635, 1), (key1550, 1), (key1328, 1), (key1300, 1), (key1446, -1), (key1395, -1)]

theorem rawRowCheck375 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form2 = rawRow375 := by decide +kernel

def row375 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck375 : row375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow375 := by decide +kernel

theorem rowEval375 (x : Key → ℝ) : Integer.Sparse.eval row375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck375, Integer.Sparse.eval_collectBalanced, rawRowCheck375]

def rawRow376 : Integer.Sparse Key := [(key1635, -1), (key1928, -1), (key1691, 2), (key1595, 1), (key1913, 1), (key1482, -1), (key1694, -1), (key1600, -2), (key1451, 1), (key1644, 1), (key1626, 1), (key1922, 1), (key1685, -2), (key1558, -1), (key1901, -1), (key1356, 1), (key1694, 1), (key1563, 2), (key1333, -1), (key1644, -1), (key1577, -1), (key1905, -1), (key1474, 1), (key1685, 1), (key1550, 1), (key1898, 1), (key1353, -1), (key1691, -1), (key1401, -1), (key1563, -1), (key1306, 1), (key1600, 1), (key1577, 2), (key1428, -1), (key1626, -1), (key1550, -2), (key1320, 1), (key1635, 1), (key1395, 1), (key1558, 1), (key1300, -1), (key1595, -1)]

theorem rawRowCheck376 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form2 = rawRow376 := by decide +kernel

def row376 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck376 : row376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow376 := by decide +kernel

theorem rowEval376 (x : Key → ℝ) : Integer.Sparse.eval row376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck376, Integer.Sparse.eval_collectBalanced, rawRowCheck376]

def rawRow377 : Integer.Sparse Key := [(key1928, -1), (key1635, -1), (key1691, 2), (key1913, 1), (key1595, 1), (key1694, -1), (key1482, -1), (key1600, -2), (key1644, 1), (key1451, 1), (key1922, 1), (key1626, 1), (key1685, -2), (key1901, -1), (key1558, -1), (key1694, 1), (key1356, 1), (key1563, 2), (key1644, -1), (key1333, -1), (key1905, -1), (key1577, -1), (key1685, 1), (key1474, 1), (key1898, 1), (key1550, 1), (key1691, -1), (key1353, -1), (key1563, -1), (key1401, -1), (key1600, 1), (key1306, 1), (key1577, 2), (key1626, -1), (key1428, -1), (key1550, -2), (key1635, 1), (key1320, 1), (key1558, 1), (key1395, 1), (key1595, -1), (key1300, -1)]

theorem rawRowCheck377 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form2 = rawRow377 := by decide +kernel

def row377 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck377 : row377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow377 := by decide +kernel

theorem rowEval377 (x : Key → ℝ) : Integer.Sparse.eval row377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck377, Integer.Sparse.eval_collectBalanced, rawRowCheck377]

def rawRow378 : Integer.Sparse Key := [(key243, -2), (key245, 1), (key245, 1), (key255, 2), (key266, -1), (key266, -1), (key270, -1), (key270, -1), (key275, 1), (key275, 1), (key309, 2), (key311, -1), (key311, -1), (key323, -2), (key334, 1), (key334, 1), (key338, 1), (key338, 1), (key344, -1), (key344, -1), (key392, -2), (key403, 1), (key403, 1), (key413, 2), (key424, -1), (key424, -1), (key473, -1), (key473, -1), (key479, 1), (key479, 1), (key571, 1), (key571, 1), (key576, -1), (key576, -1), (key581, -1), (key581, -1), (key587, 1), (key587, 1), (key599, 1), (key599, 1), (key605, -1), (key605, -1)]

theorem rawRowCheck378 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form3 = rawRow378 := by decide +kernel

def row378 : Integer.Sparse Key := [(key243, -2), (key245, 2), (key255, 2), (key266, -2), (key270, -2), (key275, 2), (key309, 2), (key311, -2), (key323, -2), (key334, 2), (key338, 2), (key344, -2), (key392, -2), (key403, 2), (key413, 2), (key424, -2), (key473, -2), (key479, 2), (key571, 2), (key576, -2), (key581, -2), (key587, 2), (key599, 2), (key605, -2)]

theorem rowCheck378 : row378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow378 := by decide +kernel

theorem rowEval378 (x : Key → ℝ) : Integer.Sparse.eval row378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck378, Integer.Sparse.eval_collectBalanced, rawRowCheck378]

def rawRow379 : Integer.Sparse Key := [(key245, -2), (key243, 1), (key245, 1), (key266, 2), (key255, -1), (key266, -1), (key275, -1), (key276, -1), (key270, 1), (key276, 1), (key311, 2), (key309, -1), (key311, -1), (key334, -2), (key323, 1), (key334, 1), (key344, 1), (key345, 1), (key338, -1), (key345, -1), (key403, -2), (key392, 1), (key403, 1), (key424, 2), (key413, -1), (key424, -1), (key479, -1), (key485, -1), (key473, 1), (key485, 1), (key576, 1), (key577, 1), (key571, -1), (key577, -1), (key587, -1), (key588, -1), (key581, 1), (key588, 1), (key605, 1), (key611, 1), (key599, -1), (key611, -1)]

theorem rawRowCheck379 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form3 = rawRow379 := by decide +kernel

def row379 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck379 : row379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow379 := by decide +kernel

theorem rowEval379 (x : Key → ℝ) : Integer.Sparse.eval row379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck379, Integer.Sparse.eval_collectBalanced, rawRowCheck379]

def rawRow380 : Integer.Sparse Key := [(key245, -2), (key245, 1), (key243, 1), (key266, 2), (key266, -1), (key255, -1), (key276, -1), (key275, -1), (key276, 1), (key270, 1), (key311, 2), (key311, -1), (key309, -1), (key334, -2), (key334, 1), (key323, 1), (key345, 1), (key344, 1), (key345, -1), (key338, -1), (key403, -2), (key403, 1), (key392, 1), (key424, 2), (key424, -1), (key413, -1), (key485, -1), (key479, -1), (key485, 1), (key473, 1), (key577, 1), (key576, 1), (key577, -1), (key571, -1), (key588, -1), (key587, -1), (key588, 1), (key581, 1), (key611, 1), (key605, 1), (key611, -1), (key599, -1)]

theorem rawRowCheck380 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form3 = rawRow380 := by decide +kernel

def row380 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key344, 1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 1), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck380 : row380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow380 := by decide +kernel

theorem rowEval380 (x : Key → ℝ) : Integer.Sparse.eval row380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form3) x := by
  rw [rowCheck380, Integer.Sparse.eval_collectBalanced, rawRowCheck380]

def rawRow381 : Integer.Sparse Key := [(key255, -2), (key266, 1), (key266, 1), (key243, 2), (key275, -1), (key275, -1), (key245, -1), (key245, -1), (key266, 1), (key266, 1), (key323, 2), (key338, -1), (key338, -1), (key309, -2), (key344, 1), (key344, 1), (key311, 1), (key311, 1), (key334, -1), (key334, -1), (key413, -2), (key473, 1), (key473, 1), (key392, 2), (key479, -1), (key479, -1), (key403, -1), (key403, -1), (key424, 1), (key424, 1), (key581, 1), (key581, 1), (key599, -1), (key599, -1), (key571, -1), (key571, -1), (key605, 1), (key605, 1), (key576, 1), (key576, 1), (key587, -1), (key587, -1)]

theorem rawRowCheck381 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form3 = rawRow381 := by decide +kernel

def row381 : Integer.Sparse Key := [(key243, 2), (key245, -2), (key255, -2), (key266, 4), (key275, -2), (key309, -2), (key311, 2), (key323, 2), (key334, -2), (key338, -2), (key344, 2), (key392, 2), (key403, -2), (key413, -2), (key424, 2), (key473, 2), (key479, -2), (key571, -2), (key576, 2), (key581, 2), (key587, -2), (key599, -2), (key605, 2)]

theorem rowCheck381 : row381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow381 := by decide +kernel

theorem rowEval381 (x : Key → ℝ) : Integer.Sparse.eval row381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck381, Integer.Sparse.eval_collectBalanced, rawRowCheck381]

def rawRow382 : Integer.Sparse Key := [(key266, -2), (key255, 1), (key266, 1), (key275, 2), (key243, -1), (key275, -1), (key266, -1), (key276, -1), (key245, 1), (key276, 1), (key338, 2), (key323, -1), (key338, -1), (key344, -2), (key309, 1), (key344, 1), (key334, 1), (key345, 1), (key311, -1), (key345, -1), (key473, -2), (key413, 1), (key473, 1), (key479, 2), (key392, -1), (key479, -1), (key424, -1), (key485, -1), (key403, 1), (key485, 1), (key599, 1), (key613, 1), (key581, -1), (key613, -1), (key605, -1), (key614, -1), (key571, 1), (key614, 1), (key587, 1), (key616, 1), (key576, -1), (key616, -1)]

theorem rawRowCheck382 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form3 = rawRow382 := by decide +kernel

def row382 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck382 : row382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow382 := by decide +kernel

theorem rowEval382 (x : Key → ℝ) : Integer.Sparse.eval row382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck382, Integer.Sparse.eval_collectBalanced, rawRowCheck382]

def rawRow383 : Integer.Sparse Key := [(key266, -2), (key266, 1), (key255, 1), (key275, 2), (key275, -1), (key243, -1), (key276, -1), (key266, -1), (key276, 1), (key245, 1), (key338, 2), (key338, -1), (key323, -1), (key344, -2), (key344, 1), (key309, 1), (key345, 1), (key334, 1), (key345, -1), (key311, -1), (key473, -2), (key473, 1), (key413, 1), (key479, 2), (key479, -1), (key392, -1), (key485, -1), (key424, -1), (key485, 1), (key403, 1), (key613, 1), (key599, 1), (key613, -1), (key581, -1), (key614, -1), (key605, -1), (key614, 1), (key571, 1), (key616, 1), (key587, 1), (key616, -1), (key576, -1)]

theorem rawRowCheck383 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form3 = rawRow383 := by decide +kernel

def row383 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -2), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck383 : row383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow383 := by decide +kernel

theorem rowEval383 (x : Key → ℝ) : Integer.Sparse.eval row383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck383, Integer.Sparse.eval_collectBalanced, rawRowCheck383]

end MUB6.Certificate.GramRows

end OAI
