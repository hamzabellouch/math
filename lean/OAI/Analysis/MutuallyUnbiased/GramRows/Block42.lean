import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
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

def rawRow2304 : Integer.Sparse Key := [(key1325, -2), (key1317, -2), (key1312, -2), (key1344, 1), (key1338, 1), (key1325, 1), (key1297, 1), (key1312, 1), (key1292, 1), (key1555, 2), (key1547, 2), (key1542, 2), (key1779, -1), (key1773, -1), (key1555, -1), (key1392, -1), (key1542, -1), (key1387, -1), (key1658, -1), (key1656, -1), (key1623, -1), (key1574, -1), (key1618, -1), (key1569, -1), (key1816, 1), (key1814, 1), (key1623, 1), (key1425, 1), (key1618, 1), (key1420, 1)]

theorem rawRowCheck2304 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form7 = rawRow2304 := by decide +kernel

def row2304 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -2), (key1325, -1), (key1338, 1), (key1344, 1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 1), (key1542, 1), (key1547, 2), (key1555, 1), (key1569, -1), (key1574, -1), (key1656, -1), (key1658, -1), (key1773, -1), (key1779, -1), (key1814, 1), (key1816, 1)]

theorem rowCheck2304 : row2304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2304 := by decide +kernel

theorem rowEval2304 (x : Key → ℝ) : Integer.Sparse.eval row2304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2304, Integer.Sparse.eval_collectBalanced, rawRowCheck2304]

def rawRow2305 : Integer.Sparse Key := [(key1387, -2), (key1392, -2), (key1392, -2), (key1420, 1), (key1425, 1), (key1420, 1), (key1456, 1), (key1425, 1), (key1456, 1), (key1292, 2), (key1297, 2), (key1297, 2), (key1569, -1), (key1574, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1789, -1), (key1312, -1), (key1317, -1), (key1312, -1), (key1338, -1), (key1317, -1), (key1338, -1), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1)]

theorem rawRowCheck2305 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form7 = rawRow2305 := by decide +kernel

def row2305 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

theorem rowCheck2305 : row2305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2305 := by decide +kernel

theorem rowEval2305 (x : Key → ℝ) : Integer.Sparse.eval row2305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2305, Integer.Sparse.eval_collectBalanced, rawRowCheck2305]

def rawRow2306 : Integer.Sparse Key := [(key1392, -2), (key1387, -2), (key1392, -2), (key1425, 1), (key1420, 1), (key1456, 1), (key1420, 1), (key1456, 1), (key1425, 1), (key1297, 2), (key1292, 2), (key1297, 2), (key1574, -1), (key1569, -1), (key1789, -1), (key1569, -1), (key1789, -1), (key1574, -1), (key1317, -1), (key1312, -1), (key1338, -1), (key1312, -1), (key1338, -1), (key1317, -1), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1)]

theorem rawRowCheck2306 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form7 = rawRow2306 := by decide +kernel

def row2306 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

theorem rowCheck2306 : row2306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2306 := by decide +kernel

theorem rowEval2306 (x : Key → ℝ) : Integer.Sparse.eval row2306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2306, Integer.Sparse.eval_collectBalanced, rawRowCheck2306]

def rawRow2307 : Integer.Sparse Key := [(key1392, -2), (key1392, -2), (key1387, -2), (key1456, 1), (key1456, 1), (key1425, 1), (key1425, 1), (key1420, 1), (key1420, 1), (key1297, 2), (key1297, 2), (key1292, 2), (key1789, -1), (key1789, -1), (key1574, -1), (key1574, -1), (key1569, -1), (key1569, -1), (key1338, -1), (key1338, -1), (key1317, -1), (key1317, -1), (key1312, -1), (key1312, -1), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1)]

theorem rawRowCheck2307 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form7 = rawRow2307 := by decide +kernel

def row2307 : Integer.Sparse Key := [(key1292, 2), (key1297, 4), (key1312, -2), (key1317, -2), (key1338, -2), (key1387, -2), (key1392, -4), (key1420, 2), (key1425, 2), (key1456, 2), (key1542, 2), (key1547, 2), (key1569, -2), (key1574, -2), (key1773, 2), (key1789, -2)]

theorem rowCheck2307 : row2307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2307 := by decide +kernel

theorem rowEval2307 (x : Key → ℝ) : Integer.Sparse.eval row2307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2307, Integer.Sparse.eval_collectBalanced, rawRowCheck2307]

def rawRow2308 : Integer.Sparse Key := [(key1420, -2), (key1425, -2), (key1443, -2), (key1387, 1), (key1392, 1), (key1420, 1), (key1456, 1), (key1443, 1), (key1465, 1), (key1569, 2), (key1574, 2), (key1592, 2), (key1292, -1), (key1297, -1), (key1569, -1), (key1789, -1), (key1592, -1), (key1797, -1), (key1542, -1), (key1547, -1), (key1618, -1), (key1656, -1), (key1632, -1), (key1666, -1), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1)]

theorem rawRowCheck2308 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form7 = rawRow2308 := by decide +kernel

def row2308 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

theorem rowCheck2308 : row2308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2308 := by decide +kernel

theorem rowEval2308 (x : Key → ℝ) : Integer.Sparse.eval row2308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2308, Integer.Sparse.eval_collectBalanced, rawRowCheck2308]

def rawRow2309 : Integer.Sparse Key := [(key1425, -2), (key1420, -2), (key1443, -2), (key1392, 1), (key1387, 1), (key1456, 1), (key1420, 1), (key1465, 1), (key1443, 1), (key1574, 2), (key1569, 2), (key1592, 2), (key1297, -1), (key1292, -1), (key1789, -1), (key1569, -1), (key1797, -1), (key1592, -1), (key1547, -1), (key1542, -1), (key1656, -1), (key1618, -1), (key1666, -1), (key1632, -1), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1)]

theorem rawRowCheck2309 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form7 = rawRow2309 := by decide +kernel

def row2309 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

theorem rowCheck2309 : row2309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2309 := by decide +kernel

theorem rowEval2309 (x : Key → ℝ) : Integer.Sparse.eval row2309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2309, Integer.Sparse.eval_collectBalanced, rawRowCheck2309]

def rawRow2310 : Integer.Sparse Key := [(key1420, -2), (key1443, -2), (key1425, -2), (key1420, 1), (key1443, 1), (key1387, 1), (key1465, 1), (key1392, 1), (key1456, 1), (key1569, 2), (key1592, 2), (key1574, 2), (key1569, -1), (key1592, -1), (key1292, -1), (key1797, -1), (key1297, -1), (key1789, -1), (key1618, -1), (key1632, -1), (key1542, -1), (key1666, -1), (key1547, -1), (key1656, -1), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1)]

theorem rawRowCheck2310 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form7 = rawRow2310 := by decide +kernel

def row2310 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

theorem rowCheck2310 : row2310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2310 := by decide +kernel

theorem rowEval2310 (x : Key → ℝ) : Integer.Sparse.eval row2310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2310, Integer.Sparse.eval_collectBalanced, rawRowCheck2310]

def rawRow2311 : Integer.Sparse Key := [(key1443, -2), (key1420, -2), (key1425, -2), (key1443, 1), (key1420, 1), (key1465, 1), (key1387, 1), (key1456, 1), (key1392, 1), (key1592, 2), (key1569, 2), (key1574, 2), (key1592, -1), (key1569, -1), (key1797, -1), (key1292, -1), (key1789, -1), (key1297, -1), (key1632, -1), (key1618, -1), (key1666, -1), (key1542, -1), (key1656, -1), (key1547, -1), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1)]

theorem rawRowCheck2311 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form7 = rawRow2311 := by decide +kernel

def row2311 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

theorem rowCheck2311 : row2311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2311 := by decide +kernel

theorem rowEval2311 (x : Key → ℝ) : Integer.Sparse.eval row2311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2311, Integer.Sparse.eval_collectBalanced, rawRowCheck2311]

def rawRow2312 : Integer.Sparse Key := [(key1425, -2), (key1443, -2), (key1420, -2), (key1456, 1), (key1465, 1), (key1392, 1), (key1443, 1), (key1387, 1), (key1420, 1), (key1574, 2), (key1592, 2), (key1569, 2), (key1789, -1), (key1797, -1), (key1297, -1), (key1592, -1), (key1292, -1), (key1569, -1), (key1656, -1), (key1666, -1), (key1547, -1), (key1632, -1), (key1542, -1), (key1618, -1), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1)]

theorem rawRowCheck2312 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form7 = rawRow2312 := by decide +kernel

def row2312 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

theorem rowCheck2312 : row2312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2312 := by decide +kernel

theorem rowEval2312 (x : Key → ℝ) : Integer.Sparse.eval row2312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2312, Integer.Sparse.eval_collectBalanced, rawRowCheck2312]

def rawRow2313 : Integer.Sparse Key := [(key1443, -2), (key1425, -2), (key1420, -2), (key1465, 1), (key1456, 1), (key1443, 1), (key1392, 1), (key1420, 1), (key1387, 1), (key1592, 2), (key1574, 2), (key1569, 2), (key1797, -1), (key1789, -1), (key1592, -1), (key1297, -1), (key1569, -1), (key1292, -1), (key1666, -1), (key1656, -1), (key1632, -1), (key1547, -1), (key1618, -1), (key1542, -1), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1)]

theorem rawRowCheck2313 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form7 = rawRow2313 := by decide +kernel

def row2313 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -2), (key1443, -1), (key1456, 1), (key1465, 1), (key1542, -1), (key1547, -1), (key1569, 1), (key1574, 2), (key1592, 1), (key1656, -1), (key1666, -1), (key1789, -1), (key1797, -1), (key1814, 1), (key1824, 1)]

theorem rowCheck2313 : row2313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2313 := by decide +kernel

theorem rowEval2313 (x : Key → ℝ) : Integer.Sparse.eval row2313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2313, Integer.Sparse.eval_collectBalanced, rawRowCheck2313]

def rawRow2314 : Integer.Sparse Key := [(key1542, -2), (key1547, -2), (key1555, -2), (key1569, 1), (key1574, 1), (key1618, 1), (key1656, 1), (key1623, 1), (key1658, 1), (key1312, 2), (key1317, 2), (key1325, 2), (key1420, -1), (key1425, -1), (key1618, -1), (key1814, -1), (key1623, -1), (key1816, -1), (key1292, -1), (key1297, -1), (key1312, -1), (key1338, -1), (key1325, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1)]

theorem rawRowCheck2314 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form7 = rawRow2314 := by decide +kernel

def row2314 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

theorem rowCheck2314 : row2314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2314 := by decide +kernel

theorem rowEval2314 (x : Key → ℝ) : Integer.Sparse.eval row2314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2314, Integer.Sparse.eval_collectBalanced, rawRowCheck2314]

def rawRow2315 : Integer.Sparse Key := [(key1547, -2), (key1542, -2), (key1555, -2), (key1574, 1), (key1569, 1), (key1656, 1), (key1618, 1), (key1658, 1), (key1623, 1), (key1317, 2), (key1312, 2), (key1325, 2), (key1425, -1), (key1420, -1), (key1814, -1), (key1618, -1), (key1816, -1), (key1623, -1), (key1297, -1), (key1292, -1), (key1338, -1), (key1312, -1), (key1344, -1), (key1325, -1), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1)]

theorem rawRowCheck2315 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form7 = rawRow2315 := by decide +kernel

def row2315 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

theorem rowCheck2315 : row2315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2315 := by decide +kernel

theorem rowEval2315 (x : Key → ℝ) : Integer.Sparse.eval row2315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2315, Integer.Sparse.eval_collectBalanced, rawRowCheck2315]

def rawRow2316 : Integer.Sparse Key := [(key1542, -2), (key1555, -2), (key1547, -2), (key1618, 1), (key1623, 1), (key1569, 1), (key1658, 1), (key1574, 1), (key1656, 1), (key1312, 2), (key1325, 2), (key1317, 2), (key1618, -1), (key1623, -1), (key1420, -1), (key1816, -1), (key1425, -1), (key1814, -1), (key1312, -1), (key1325, -1), (key1292, -1), (key1344, -1), (key1297, -1), (key1338, -1), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1)]

theorem rawRowCheck2316 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form7 = rawRow2316 := by decide +kernel

def row2316 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

theorem rowCheck2316 : row2316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2316 := by decide +kernel

theorem rowEval2316 (x : Key → ℝ) : Integer.Sparse.eval row2316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2316, Integer.Sparse.eval_collectBalanced, rawRowCheck2316]

def rawRow2317 : Integer.Sparse Key := [(key1555, -2), (key1542, -2), (key1547, -2), (key1623, 1), (key1618, 1), (key1658, 1), (key1569, 1), (key1656, 1), (key1574, 1), (key1325, 2), (key1312, 2), (key1317, 2), (key1623, -1), (key1618, -1), (key1816, -1), (key1420, -1), (key1814, -1), (key1425, -1), (key1325, -1), (key1312, -1), (key1344, -1), (key1292, -1), (key1338, -1), (key1297, -1), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1)]

theorem rawRowCheck2317 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form7 = rawRow2317 := by decide +kernel

def row2317 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

theorem rowCheck2317 : row2317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2317 := by decide +kernel

theorem rowEval2317 (x : Key → ℝ) : Integer.Sparse.eval row2317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2317, Integer.Sparse.eval_collectBalanced, rawRowCheck2317]

def rawRow2318 : Integer.Sparse Key := [(key1547, -2), (key1555, -2), (key1542, -2), (key1656, 1), (key1658, 1), (key1574, 1), (key1623, 1), (key1569, 1), (key1618, 1), (key1317, 2), (key1325, 2), (key1312, 2), (key1814, -1), (key1816, -1), (key1425, -1), (key1623, -1), (key1420, -1), (key1618, -1), (key1338, -1), (key1344, -1), (key1297, -1), (key1325, -1), (key1292, -1), (key1312, -1), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1)]

theorem rawRowCheck2318 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form7 = rawRow2318 := by decide +kernel

def row2318 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

theorem rowCheck2318 : row2318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2318 := by decide +kernel

theorem rowEval2318 (x : Key → ℝ) : Integer.Sparse.eval row2318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2318, Integer.Sparse.eval_collectBalanced, rawRowCheck2318]

def rawRow2319 : Integer.Sparse Key := [(key1555, -2), (key1547, -2), (key1542, -2), (key1658, 1), (key1656, 1), (key1623, 1), (key1574, 1), (key1618, 1), (key1569, 1), (key1325, 2), (key1317, 2), (key1312, 2), (key1816, -1), (key1814, -1), (key1623, -1), (key1425, -1), (key1618, -1), (key1420, -1), (key1344, -1), (key1338, -1), (key1325, -1), (key1297, -1), (key1312, -1), (key1292, -1), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1)]

theorem rawRowCheck2319 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form7 = rawRow2319 := by decide +kernel

def row2319 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1312, 1), (key1317, 2), (key1325, 1), (key1338, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1420, -1), (key1425, -1), (key1542, -1), (key1547, -2), (key1555, -1), (key1569, 1), (key1574, 1), (key1656, 1), (key1658, 1), (key1773, 1), (key1779, 1), (key1814, -1), (key1816, -1)]

theorem rowCheck2319 : row2319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2319 := by decide +kernel

theorem rowEval2319 (x : Key → ℝ) : Integer.Sparse.eval row2319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2319, Integer.Sparse.eval_collectBalanced, rawRowCheck2319]

def rawRow2320 : Integer.Sparse Key := [(key1569, -2), (key1574, -2), (key1592, -2), (key1542, 1), (key1547, 1), (key1618, 1), (key1656, 1), (key1632, 1), (key1666, 1), (key1420, 2), (key1425, 2), (key1443, 2), (key1312, -1), (key1317, -1), (key1618, -1), (key1814, -1), (key1632, -1), (key1824, -1), (key1387, -1), (key1392, -1), (key1420, -1), (key1456, -1), (key1443, -1), (key1465, -1), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1)]

theorem rawRowCheck2320 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form7 = rawRow2320 := by decide +kernel

def row2320 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

theorem rowCheck2320 : row2320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2320 := by decide +kernel

theorem rowEval2320 (x : Key → ℝ) : Integer.Sparse.eval row2320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2320, Integer.Sparse.eval_collectBalanced, rawRowCheck2320]

def rawRow2321 : Integer.Sparse Key := [(key1574, -2), (key1569, -2), (key1592, -2), (key1547, 1), (key1542, 1), (key1656, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1425, 2), (key1420, 2), (key1443, 2), (key1317, -1), (key1312, -1), (key1814, -1), (key1618, -1), (key1824, -1), (key1632, -1), (key1392, -1), (key1387, -1), (key1456, -1), (key1420, -1), (key1465, -1), (key1443, -1), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1)]

theorem rawRowCheck2321 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form7 = rawRow2321 := by decide +kernel

def row2321 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

theorem rowCheck2321 : row2321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2321 := by decide +kernel

theorem rowEval2321 (x : Key → ℝ) : Integer.Sparse.eval row2321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2321, Integer.Sparse.eval_collectBalanced, rawRowCheck2321]

def rawRow2322 : Integer.Sparse Key := [(key1569, -2), (key1592, -2), (key1574, -2), (key1618, 1), (key1632, 1), (key1542, 1), (key1666, 1), (key1547, 1), (key1656, 1), (key1420, 2), (key1443, 2), (key1425, 2), (key1618, -1), (key1632, -1), (key1312, -1), (key1824, -1), (key1317, -1), (key1814, -1), (key1420, -1), (key1443, -1), (key1387, -1), (key1465, -1), (key1392, -1), (key1456, -1), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1)]

theorem rawRowCheck2322 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form7 = rawRow2322 := by decide +kernel

def row2322 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

theorem rowCheck2322 : row2322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2322 := by decide +kernel

theorem rowEval2322 (x : Key → ℝ) : Integer.Sparse.eval row2322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form7) x := by
  rw [rowCheck2322, Integer.Sparse.eval_collectBalanced, rawRowCheck2322]

def rawRow2323 : Integer.Sparse Key := [(key1592, -2), (key1569, -2), (key1574, -2), (key1632, 1), (key1618, 1), (key1666, 1), (key1542, 1), (key1656, 1), (key1547, 1), (key1443, 2), (key1420, 2), (key1425, 2), (key1632, -1), (key1618, -1), (key1824, -1), (key1312, -1), (key1814, -1), (key1317, -1), (key1443, -1), (key1420, -1), (key1465, -1), (key1387, -1), (key1456, -1), (key1392, -1), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1)]

theorem rawRowCheck2323 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form7 = rawRow2323 := by decide +kernel

def row2323 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

theorem rowCheck2323 : row2323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2323 := by decide +kernel

theorem rowEval2323 (x : Key → ℝ) : Integer.Sparse.eval row2323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2323, Integer.Sparse.eval_collectBalanced, rawRowCheck2323]

def rawRow2324 : Integer.Sparse Key := [(key1574, -2), (key1592, -2), (key1569, -2), (key1656, 1), (key1666, 1), (key1547, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1425, 2), (key1443, 2), (key1420, 2), (key1814, -1), (key1824, -1), (key1317, -1), (key1632, -1), (key1312, -1), (key1618, -1), (key1456, -1), (key1465, -1), (key1392, -1), (key1443, -1), (key1387, -1), (key1420, -1), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1)]

theorem rawRowCheck2324 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form7 = rawRow2324 := by decide +kernel

def row2324 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

theorem rowCheck2324 : row2324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2324 := by decide +kernel

theorem rowEval2324 (x : Key → ℝ) : Integer.Sparse.eval row2324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2324, Integer.Sparse.eval_collectBalanced, rawRowCheck2324]

def rawRow2325 : Integer.Sparse Key := [(key1592, -2), (key1574, -2), (key1569, -2), (key1666, 1), (key1656, 1), (key1632, 1), (key1547, 1), (key1618, 1), (key1542, 1), (key1443, 2), (key1425, 2), (key1420, 2), (key1824, -1), (key1814, -1), (key1632, -1), (key1317, -1), (key1618, -1), (key1312, -1), (key1465, -1), (key1456, -1), (key1443, -1), (key1392, -1), (key1420, -1), (key1387, -1), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1)]

theorem rawRowCheck2325 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form7 = rawRow2325 := by decide +kernel

def row2325 : Integer.Sparse Key := [(key1292, 1), (key1297, 1), (key1312, -1), (key1317, -1), (key1387, -1), (key1392, -1), (key1420, 1), (key1425, 2), (key1443, 1), (key1456, -1), (key1465, -1), (key1542, 1), (key1547, 1), (key1569, -1), (key1574, -2), (key1592, -1), (key1656, 1), (key1666, 1), (key1789, 1), (key1797, 1), (key1814, -1), (key1824, -1)]

theorem rowCheck2325 : row2325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2325 := by decide +kernel

theorem rowEval2325 (x : Key → ℝ) : Integer.Sparse.eval row2325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck2325, Integer.Sparse.eval_collectBalanced, rawRowCheck2325]

def rawRow2326 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key997, -2), (key1012, 6), (key1028, 2), (key1032, 2), (key1032, 2), (key1120, -2), (key1120, -2), (key1196, -2), (key1068, -6), (key1147, 2), (key1147, 2), (key1209, 2)]

theorem rawRowCheck2326 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2326 := by decide +kernel

def row2326 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck2326 : row2326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2326 := by decide +kernel

theorem rowEval2326 (x : Key → ℝ) : Integer.Sparse.eval row2326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2326, Integer.Sparse.eval_collectBalanced, rawRowCheck2326]

def rawRow2327 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key997, -2), (key1012, 6), (key1032, 2), (key1028, 2), (key1032, 2), (key1120, -2), (key1196, -2), (key1120, -2), (key1068, -6), (key1147, 2), (key1209, 2), (key1147, 2)]

theorem rawRowCheck2327 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2327 := by decide +kernel

def row2327 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck2327 : row2327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2327 := by decide +kernel

theorem rowEval2327 (x : Key → ℝ) : Integer.Sparse.eval row2327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2327, Integer.Sparse.eval_collectBalanced, rawRowCheck2327]

def rawRow2328 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key993, -2), (key1012, 6), (key1032, 2), (key1032, 2), (key1028, 2), (key1196, -2), (key1120, -2), (key1120, -2), (key1068, -6), (key1209, 2), (key1147, 2), (key1147, 2)]

theorem rawRowCheck2328 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2328 := by decide +kernel

def row2328 : Integer.Sparse Key := [(key993, -2), (key997, -4), (key1012, 6), (key1028, 2), (key1032, 4), (key1068, -6), (key1120, -4), (key1147, 4), (key1196, -2), (key1209, 2)]

theorem rowCheck2328 : row2328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2328 := by decide +kernel

theorem rowEval2328 (x : Key → ℝ) : Integer.Sparse.eval row2328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2328, Integer.Sparse.eval_collectBalanced, rawRowCheck2328]

def rawRow2329 : Integer.Sparse Key := [(key993, -2), (key997, -2), (key1012, -2), (key997, 6), (key1106, 2), (key1110, 2), (key1120, 2), (key1032, -2), (key1110, -2), (key1189, -2), (key1147, -6), (key1068, 2), (key1147, 2), (key1209, 2)]

theorem rawRowCheck2329 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form8 = rawRow2329 := by decide +kernel

def row2329 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

theorem rowCheck2329 : row2329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2329 := by decide +kernel

theorem rowEval2329 (x : Key → ℝ) : Integer.Sparse.eval row2329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2329, Integer.Sparse.eval_collectBalanced, rawRowCheck2329]

def rawRow2330 : Integer.Sparse Key := [(key997, -2), (key993, -2), (key1012, -2), (key997, 6), (key1110, 2), (key1106, 2), (key1120, 2), (key1032, -2), (key1189, -2), (key1110, -2), (key1147, -6), (key1068, 2), (key1209, 2), (key1147, 2)]

theorem rawRowCheck2330 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form8 = rawRow2330 := by decide +kernel

def row2330 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

theorem rowCheck2330 : row2330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2330 := by decide +kernel

theorem rowEval2330 (x : Key → ℝ) : Integer.Sparse.eval row2330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2330, Integer.Sparse.eval_collectBalanced, rawRowCheck2330]

def rawRow2331 : Integer.Sparse Key := [(key993, -2), (key1012, -2), (key997, -2), (key997, 6), (key1106, 2), (key1120, 2), (key1110, 2), (key1110, -2), (key1032, -2), (key1189, -2), (key1147, -6), (key1147, 2), (key1068, 2), (key1209, 2)]

theorem rawRowCheck2331 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form8 = rawRow2331 := by decide +kernel

def row2331 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

theorem rowCheck2331 : row2331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2331 := by decide +kernel

theorem rowEval2331 (x : Key → ℝ) : Integer.Sparse.eval row2331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2331, Integer.Sparse.eval_collectBalanced, rawRowCheck2331]

def rawRow2332 : Integer.Sparse Key := [(key1012, -2), (key993, -2), (key997, -2), (key997, 6), (key1120, 2), (key1106, 2), (key1110, 2), (key1110, -2), (key1189, -2), (key1032, -2), (key1147, -6), (key1147, 2), (key1209, 2), (key1068, 2)]

theorem rawRowCheck2332 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form8 = rawRow2332 := by decide +kernel

def row2332 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

theorem rowCheck2332 : row2332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2332 := by decide +kernel

theorem rowEval2332 (x : Key → ℝ) : Integer.Sparse.eval row2332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2332, Integer.Sparse.eval_collectBalanced, rawRowCheck2332]

def rawRow2333 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key993, -2), (key997, 6), (key1110, 2), (key1120, 2), (key1106, 2), (key1189, -2), (key1032, -2), (key1110, -2), (key1147, -6), (key1209, 2), (key1068, 2), (key1147, 2)]

theorem rawRowCheck2333 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form8 = rawRow2333 := by decide +kernel

def row2333 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

theorem rowCheck2333 : row2333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2333 := by decide +kernel

theorem rowEval2333 (x : Key → ℝ) : Integer.Sparse.eval row2333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2333, Integer.Sparse.eval_collectBalanced, rawRowCheck2333]

def rawRow2334 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key993, -2), (key997, 6), (key1120, 2), (key1110, 2), (key1106, 2), (key1189, -2), (key1110, -2), (key1032, -2), (key1147, -6), (key1209, 2), (key1147, 2), (key1068, 2)]

theorem rawRowCheck2334 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form8 = rawRow2334 := by decide +kernel

def row2334 : Integer.Sparse Key := [(key993, -2), (key997, 4), (key1012, -2), (key1032, -2), (key1068, 2), (key1106, 2), (key1120, 2), (key1147, -4), (key1189, -2), (key1209, 2)]

theorem rowCheck2334 : row2334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2334 := by decide +kernel

theorem rowEval2334 (x : Key → ℝ) : Integer.Sparse.eval row2334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2334, Integer.Sparse.eval_collectBalanced, rawRowCheck2334]

def rawRow2335 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1032, -2), (key1068, 6), (key993, 2), (key997, 2), (key997, 2), (key1147, -2), (key1147, -2), (key1209, -2), (key1012, -6), (key1120, 2), (key1120, 2), (key1196, 2)]

theorem rawRowCheck2335 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form8 = rawRow2335 := by decide +kernel

def row2335 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

theorem rowCheck2335 : row2335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2335 := by decide +kernel

theorem rowEval2335 (x : Key → ℝ) : Integer.Sparse.eval row2335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2335, Integer.Sparse.eval_collectBalanced, rawRowCheck2335]

def rawRow2336 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1032, -2), (key1068, 6), (key997, 2), (key993, 2), (key997, 2), (key1147, -2), (key1209, -2), (key1147, -2), (key1012, -6), (key1120, 2), (key1196, 2), (key1120, 2)]

theorem rawRowCheck2336 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form8 = rawRow2336 := by decide +kernel

def row2336 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

theorem rowCheck2336 : row2336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2336 := by decide +kernel

theorem rowEval2336 (x : Key → ℝ) : Integer.Sparse.eval row2336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2336, Integer.Sparse.eval_collectBalanced, rawRowCheck2336]

def rawRow2337 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1028, -2), (key1068, 6), (key997, 2), (key997, 2), (key993, 2), (key1209, -2), (key1147, -2), (key1147, -2), (key1012, -6), (key1196, 2), (key1120, 2), (key1120, 2)]

theorem rawRowCheck2337 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form8 = rawRow2337 := by decide +kernel

def row2337 : Integer.Sparse Key := [(key993, 2), (key997, 4), (key1012, -6), (key1028, -2), (key1032, -4), (key1068, 6), (key1120, 4), (key1147, -4), (key1196, 2), (key1209, -2)]

theorem rowCheck2337 : row2337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2337 := by decide +kernel

theorem rowEval2337 (x : Key → ℝ) : Integer.Sparse.eval row2337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2337, Integer.Sparse.eval_collectBalanced, rawRowCheck2337]

def rawRow2338 : Integer.Sparse Key := [(key1028, -2), (key1032, -2), (key1068, -2), (key1032, 6), (key1106, 2), (key1110, 2), (key1147, 2), (key997, -2), (key1110, -2), (key1189, -2), (key1120, -6), (key1012, 2), (key1120, 2), (key1196, 2)]

theorem rawRowCheck2338 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form8 = rawRow2338 := by decide +kernel

def row2338 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

theorem rowCheck2338 : row2338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2338 := by decide +kernel

theorem rowEval2338 (x : Key → ℝ) : Integer.Sparse.eval row2338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2338, Integer.Sparse.eval_collectBalanced, rawRowCheck2338]

def rawRow2339 : Integer.Sparse Key := [(key1032, -2), (key1028, -2), (key1068, -2), (key1032, 6), (key1110, 2), (key1106, 2), (key1147, 2), (key997, -2), (key1189, -2), (key1110, -2), (key1120, -6), (key1012, 2), (key1196, 2), (key1120, 2)]

theorem rawRowCheck2339 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form8 = rawRow2339 := by decide +kernel

def row2339 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

theorem rowCheck2339 : row2339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2339 := by decide +kernel

theorem rowEval2339 (x : Key → ℝ) : Integer.Sparse.eval row2339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2339, Integer.Sparse.eval_collectBalanced, rawRowCheck2339]

def rawRow2340 : Integer.Sparse Key := [(key1028, -2), (key1068, -2), (key1032, -2), (key1032, 6), (key1106, 2), (key1147, 2), (key1110, 2), (key1110, -2), (key997, -2), (key1189, -2), (key1120, -6), (key1120, 2), (key1012, 2), (key1196, 2)]

theorem rawRowCheck2340 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form8 = rawRow2340 := by decide +kernel

def row2340 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

theorem rowCheck2340 : row2340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2340 := by decide +kernel

theorem rowEval2340 (x : Key → ℝ) : Integer.Sparse.eval row2340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2340, Integer.Sparse.eval_collectBalanced, rawRowCheck2340]

def rawRow2341 : Integer.Sparse Key := [(key1068, -2), (key1028, -2), (key1032, -2), (key1032, 6), (key1147, 2), (key1106, 2), (key1110, 2), (key1110, -2), (key1189, -2), (key997, -2), (key1120, -6), (key1120, 2), (key1196, 2), (key1012, 2)]

theorem rawRowCheck2341 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form8 = rawRow2341 := by decide +kernel

def row2341 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

theorem rowCheck2341 : row2341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2341 := by decide +kernel

theorem rowEval2341 (x : Key → ℝ) : Integer.Sparse.eval row2341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2341, Integer.Sparse.eval_collectBalanced, rawRowCheck2341]

def rawRow2342 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1028, -2), (key1032, 6), (key1110, 2), (key1147, 2), (key1106, 2), (key1189, -2), (key997, -2), (key1110, -2), (key1120, -6), (key1196, 2), (key1012, 2), (key1120, 2)]

theorem rawRowCheck2342 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form8 = rawRow2342 := by decide +kernel

def row2342 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

theorem rowCheck2342 : row2342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2342 := by decide +kernel

theorem rowEval2342 (x : Key → ℝ) : Integer.Sparse.eval row2342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2342, Integer.Sparse.eval_collectBalanced, rawRowCheck2342]

def rawRow2343 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1028, -2), (key1032, 6), (key1147, 2), (key1110, 2), (key1106, 2), (key1189, -2), (key1110, -2), (key997, -2), (key1120, -6), (key1196, 2), (key1120, 2), (key1012, 2)]

theorem rawRowCheck2343 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form8 = rawRow2343 := by decide +kernel

def row2343 : Integer.Sparse Key := [(key997, -2), (key1012, 2), (key1028, -2), (key1032, 4), (key1068, -2), (key1106, 2), (key1120, -4), (key1147, 2), (key1189, -2), (key1196, 2)]

theorem rowCheck2343 : row2343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2343 := by decide +kernel

theorem rowEval2343 (x : Key → ℝ) : Integer.Sparse.eval row2343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2343, Integer.Sparse.eval_collectBalanced, rawRowCheck2343]

def rawRow2344 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1120, -2), (key1147, 6), (key993, 2), (key997, 2), (key1012, 2), (key1068, -2), (key1147, -2), (key1209, -2), (key997, -6), (key1032, 2), (key1110, 2), (key1189, 2)]

theorem rawRowCheck2344 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form8 = rawRow2344 := by decide +kernel

def row2344 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

theorem rowCheck2344 : row2344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2344 := by decide +kernel

theorem rowEval2344 (x : Key → ℝ) : Integer.Sparse.eval row2344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2344, Integer.Sparse.eval_collectBalanced, rawRowCheck2344]

def rawRow2345 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1120, -2), (key1147, 6), (key997, 2), (key993, 2), (key1012, 2), (key1068, -2), (key1209, -2), (key1147, -2), (key997, -6), (key1032, 2), (key1189, 2), (key1110, 2)]

theorem rawRowCheck2345 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form8 = rawRow2345 := by decide +kernel

def row2345 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

theorem rowCheck2345 : row2345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2345 := by decide +kernel

theorem rowEval2345 (x : Key → ℝ) : Integer.Sparse.eval row2345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2345, Integer.Sparse.eval_collectBalanced, rawRowCheck2345]

def rawRow2346 : Integer.Sparse Key := [(key1106, -2), (key1120, -2), (key1110, -2), (key1147, 6), (key993, 2), (key1012, 2), (key997, 2), (key1147, -2), (key1068, -2), (key1209, -2), (key997, -6), (key1110, 2), (key1032, 2), (key1189, 2)]

theorem rawRowCheck2346 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form8 = rawRow2346 := by decide +kernel

def row2346 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

theorem rowCheck2346 : row2346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2346 := by decide +kernel

theorem rowEval2346 (x : Key → ℝ) : Integer.Sparse.eval row2346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2346, Integer.Sparse.eval_collectBalanced, rawRowCheck2346]

def rawRow2347 : Integer.Sparse Key := [(key1120, -2), (key1106, -2), (key1110, -2), (key1147, 6), (key1012, 2), (key993, 2), (key997, 2), (key1147, -2), (key1209, -2), (key1068, -2), (key997, -6), (key1110, 2), (key1189, 2), (key1032, 2)]

theorem rawRowCheck2347 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form8 = rawRow2347 := by decide +kernel

def row2347 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

theorem rowCheck2347 : row2347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2347 := by decide +kernel

theorem rowEval2347 (x : Key → ℝ) : Integer.Sparse.eval row2347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2347, Integer.Sparse.eval_collectBalanced, rawRowCheck2347]

def rawRow2348 : Integer.Sparse Key := [(key1110, -2), (key1120, -2), (key1106, -2), (key1147, 6), (key997, 2), (key1012, 2), (key993, 2), (key1209, -2), (key1068, -2), (key1147, -2), (key997, -6), (key1189, 2), (key1032, 2), (key1110, 2)]

theorem rawRowCheck2348 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form8 = rawRow2348 := by decide +kernel

def row2348 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

theorem rowCheck2348 : row2348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2348 := by decide +kernel

theorem rowEval2348 (x : Key → ℝ) : Integer.Sparse.eval row2348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2348, Integer.Sparse.eval_collectBalanced, rawRowCheck2348]

def rawRow2349 : Integer.Sparse Key := [(key1120, -2), (key1110, -2), (key1106, -2), (key1147, 6), (key1012, 2), (key997, 2), (key993, 2), (key1209, -2), (key1147, -2), (key1068, -2), (key997, -6), (key1189, 2), (key1110, 2), (key1032, 2)]

theorem rawRowCheck2349 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form8 = rawRow2349 := by decide +kernel

def row2349 : Integer.Sparse Key := [(key993, 2), (key997, -4), (key1012, 2), (key1032, 2), (key1068, -2), (key1106, -2), (key1120, -2), (key1147, 4), (key1189, 2), (key1209, -2)]

theorem rowCheck2349 : row2349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2349 := by decide +kernel

theorem rowEval2349 (x : Key → ℝ) : Integer.Sparse.eval row2349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2349, Integer.Sparse.eval_collectBalanced, rawRowCheck2349]

def rawRow2350 : Integer.Sparse Key := [(key1106, -2), (key1110, -2), (key1147, -2), (key1120, 6), (key1028, 2), (key1032, 2), (key1068, 2), (key1012, -2), (key1120, -2), (key1196, -2), (key1032, -6), (key997, 2), (key1110, 2), (key1189, 2)]

theorem rawRowCheck2350 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form8 = rawRow2350 := by decide +kernel

def row2350 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

theorem rowCheck2350 : row2350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2350 := by decide +kernel

theorem rowEval2350 (x : Key → ℝ) : Integer.Sparse.eval row2350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2350, Integer.Sparse.eval_collectBalanced, rawRowCheck2350]

def rawRow2351 : Integer.Sparse Key := [(key1110, -2), (key1106, -2), (key1147, -2), (key1120, 6), (key1032, 2), (key1028, 2), (key1068, 2), (key1012, -2), (key1196, -2), (key1120, -2), (key1032, -6), (key997, 2), (key1189, 2), (key1110, 2)]

theorem rawRowCheck2351 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form8 = rawRow2351 := by decide +kernel

def row2351 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

theorem rowCheck2351 : row2351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2351 := by decide +kernel

theorem rowEval2351 (x : Key → ℝ) : Integer.Sparse.eval row2351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2351, Integer.Sparse.eval_collectBalanced, rawRowCheck2351]

def rawRow2352 : Integer.Sparse Key := [(key1106, -2), (key1147, -2), (key1110, -2), (key1120, 6), (key1028, 2), (key1068, 2), (key1032, 2), (key1120, -2), (key1012, -2), (key1196, -2), (key1032, -6), (key1110, 2), (key997, 2), (key1189, 2)]

theorem rawRowCheck2352 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form8 = rawRow2352 := by decide +kernel

def row2352 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

theorem rowCheck2352 : row2352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2352 := by decide +kernel

theorem rowEval2352 (x : Key → ℝ) : Integer.Sparse.eval row2352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form8) x := by
  rw [rowCheck2352, Integer.Sparse.eval_collectBalanced, rawRowCheck2352]

def rawRow2353 : Integer.Sparse Key := [(key1147, -2), (key1106, -2), (key1110, -2), (key1120, 6), (key1068, 2), (key1028, 2), (key1032, 2), (key1120, -2), (key1196, -2), (key1012, -2), (key1032, -6), (key1110, 2), (key1189, 2), (key997, 2)]

theorem rawRowCheck2353 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form8 = rawRow2353 := by decide +kernel

def row2353 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

theorem rowCheck2353 : row2353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2353 := by decide +kernel

theorem rowEval2353 (x : Key → ℝ) : Integer.Sparse.eval row2353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2353, Integer.Sparse.eval_collectBalanced, rawRowCheck2353]

def rawRow2354 : Integer.Sparse Key := [(key1110, -2), (key1147, -2), (key1106, -2), (key1120, 6), (key1032, 2), (key1068, 2), (key1028, 2), (key1196, -2), (key1012, -2), (key1120, -2), (key1032, -6), (key1189, 2), (key997, 2), (key1110, 2)]

theorem rawRowCheck2354 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form8 = rawRow2354 := by decide +kernel

def row2354 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

theorem rowCheck2354 : row2354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2354 := by decide +kernel

theorem rowEval2354 (x : Key → ℝ) : Integer.Sparse.eval row2354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck2354, Integer.Sparse.eval_collectBalanced, rawRowCheck2354]

def rawRow2355 : Integer.Sparse Key := [(key1147, -2), (key1110, -2), (key1106, -2), (key1120, 6), (key1068, 2), (key1032, 2), (key1028, 2), (key1196, -2), (key1120, -2), (key1012, -2), (key1032, -6), (key1189, 2), (key1110, 2), (key997, 2)]

theorem rawRowCheck2355 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form8 = rawRow2355 := by decide +kernel

def row2355 : Integer.Sparse Key := [(key997, 2), (key1012, -2), (key1028, 2), (key1032, -4), (key1068, 2), (key1106, -2), (key1120, 4), (key1147, -2), (key1189, 2), (key1196, -2)]

theorem rowCheck2355 : row2355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2355 := by decide +kernel

theorem rowEval2355 (x : Key → ℝ) : Integer.Sparse.eval row2355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck2355, Integer.Sparse.eval_collectBalanced, rawRowCheck2355]

def rawRow2356 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2640, 1), (key2642, 1), (key2640, 1), (key2654, 1), (key2642, 1), (key2654, 1), (key2706, 2), (key2706, 2), (key2738, 2), (key2860, -1), (key2898, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2977, -1), (key2726, -1), (key2729, -1), (key2726, -1), (key2748, -1), (key2729, -1), (key2748, -1), (key2870, 1), (key2905, 1), (key2870, 1), (key2984, 1), (key2905, 1), (key2984, 1)]

theorem rawRowCheck2356 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2356 := by decide +kernel

def row2356 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck2356 : row2356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2356 := by decide +kernel

theorem rowEval2356 (x : Key → ℝ) : Integer.Sparse.eval row2356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2356, Integer.Sparse.eval_collectBalanced, rawRowCheck2356]

def rawRow2357 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2642, 1), (key2640, 1), (key2654, 1), (key2640, 1), (key2654, 1), (key2642, 1), (key2706, 2), (key2738, 2), (key2706, 2), (key2898, -1), (key2860, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2729, -1), (key2726, -1), (key2748, -1), (key2726, -1), (key2748, -1), (key2729, -1), (key2905, 1), (key2870, 1), (key2984, 1), (key2870, 1), (key2984, 1), (key2905, 1)]

theorem rawRowCheck2357 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2357 := by decide +kernel

def row2357 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck2357 : row2357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2357 := by decide +kernel

theorem rowEval2357 (x : Key → ℝ) : Integer.Sparse.eval row2357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2357, Integer.Sparse.eval_collectBalanced, rawRowCheck2357]

def rawRow2358 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2654, 1), (key2654, 1), (key2642, 1), (key2642, 1), (key2640, 1), (key2640, 1), (key2738, 2), (key2706, 2), (key2706, 2), (key2977, -1), (key2977, -1), (key2898, -1), (key2898, -1), (key2860, -1), (key2860, -1), (key2748, -1), (key2748, -1), (key2729, -1), (key2729, -1), (key2726, -1), (key2726, -1), (key2984, 1), (key2984, 1), (key2905, 1), (key2905, 1), (key2870, 1), (key2870, 1)]

theorem rawRowCheck2358 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2358 := by decide +kernel

def row2358 : Integer.Sparse Key := [(key2632, -4), (key2640, 2), (key2642, 2), (key2649, -2), (key2654, 2), (key2706, 4), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2977, -2), (key2984, 2)]

theorem rowCheck2358 : row2358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2358 := by decide +kernel

theorem rowEval2358 (x : Key → ℝ) : Integer.Sparse.eval row2358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2358, Integer.Sparse.eval_collectBalanced, rawRowCheck2358]

def rawRow2359 : Integer.Sparse Key := [(key2616, -2), (key2640, -2), (key2654, -2), (key2616, 1), (key2619, 1), (key2632, 1), (key2649, 1), (key2642, 1), (key2654, 1), (key2809, 2), (key2860, 2), (key2898, 2), (key2706, -1), (key2738, -1), (key2809, -1), (key2951, -1), (key2898, -1), (key2977, -1), (key2829, -1), (key2832, -1), (key2870, -1), (key2905, -1), (key2883, -1), (key2913, -1), (key2726, 1), (key2748, 1), (key2829, 1), (key2961, 1), (key2913, 1), (key2992, 1)]

theorem rawRowCheck2359 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form9 = rawRow2359 := by decide +kernel

def row2359 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

theorem rowCheck2359 : row2359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2359 := by decide +kernel

theorem rowEval2359 (x : Key → ℝ) : Integer.Sparse.eval row2359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2359, Integer.Sparse.eval_collectBalanced, rawRowCheck2359]

def rawRow2360 : Integer.Sparse Key := [(key2616, -2), (key2654, -2), (key2640, -2), (key2619, 1), (key2616, 1), (key2649, 1), (key2632, 1), (key2654, 1), (key2642, 1), (key2809, 2), (key2898, 2), (key2860, 2), (key2738, -1), (key2706, -1), (key2951, -1), (key2809, -1), (key2977, -1), (key2898, -1), (key2832, -1), (key2829, -1), (key2905, -1), (key2870, -1), (key2913, -1), (key2883, -1), (key2748, 1), (key2726, 1), (key2961, 1), (key2829, 1), (key2992, 1), (key2913, 1)]

theorem rawRowCheck2360 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form9 = rawRow2360 := by decide +kernel

def row2360 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

theorem rowCheck2360 : row2360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2360 := by decide +kernel

theorem rowEval2360 (x : Key → ℝ) : Integer.Sparse.eval row2360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2360, Integer.Sparse.eval_collectBalanced, rawRowCheck2360]

def rawRow2361 : Integer.Sparse Key := [(key2640, -2), (key2616, -2), (key2654, -2), (key2632, 1), (key2642, 1), (key2616, 1), (key2654, 1), (key2619, 1), (key2649, 1), (key2860, 2), (key2809, 2), (key2898, 2), (key2809, -1), (key2898, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2870, -1), (key2883, -1), (key2829, -1), (key2913, -1), (key2832, -1), (key2905, -1), (key2829, 1), (key2913, 1), (key2726, 1), (key2992, 1), (key2748, 1), (key2961, 1)]

theorem rawRowCheck2361 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form9 = rawRow2361 := by decide +kernel

def row2361 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

theorem rowCheck2361 : row2361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2361 := by decide +kernel

theorem rowEval2361 (x : Key → ℝ) : Integer.Sparse.eval row2361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2361, Integer.Sparse.eval_collectBalanced, rawRowCheck2361]

def rawRow2362 : Integer.Sparse Key := [(key2640, -2), (key2654, -2), (key2616, -2), (key2642, 1), (key2632, 1), (key2654, 1), (key2616, 1), (key2649, 1), (key2619, 1), (key2860, 2), (key2898, 2), (key2809, 2), (key2898, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2951, -1), (key2738, -1), (key2883, -1), (key2870, -1), (key2913, -1), (key2829, -1), (key2905, -1), (key2832, -1), (key2913, 1), (key2829, 1), (key2992, 1), (key2726, 1), (key2961, 1), (key2748, 1)]

theorem rawRowCheck2362 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form9 = rawRow2362 := by decide +kernel

def row2362 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

theorem rowCheck2362 : row2362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2362 := by decide +kernel

theorem rowEval2362 (x : Key → ℝ) : Integer.Sparse.eval row2362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2362, Integer.Sparse.eval_collectBalanced, rawRowCheck2362]

def rawRow2363 : Integer.Sparse Key := [(key2654, -2), (key2616, -2), (key2640, -2), (key2649, 1), (key2654, 1), (key2619, 1), (key2642, 1), (key2616, 1), (key2632, 1), (key2898, 2), (key2809, 2), (key2860, 2), (key2951, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2706, -1), (key2809, -1), (key2905, -1), (key2913, -1), (key2832, -1), (key2883, -1), (key2829, -1), (key2870, -1), (key2961, 1), (key2992, 1), (key2748, 1), (key2913, 1), (key2726, 1), (key2829, 1)]

theorem rawRowCheck2363 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form9 = rawRow2363 := by decide +kernel

def row2363 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

theorem rowCheck2363 : row2363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2363 := by decide +kernel

theorem rowEval2363 (x : Key → ℝ) : Integer.Sparse.eval row2363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2363, Integer.Sparse.eval_collectBalanced, rawRowCheck2363]

def rawRow2364 : Integer.Sparse Key := [(key2654, -2), (key2640, -2), (key2616, -2), (key2654, 1), (key2649, 1), (key2642, 1), (key2619, 1), (key2632, 1), (key2616, 1), (key2898, 2), (key2860, 2), (key2809, 2), (key2977, -1), (key2951, -1), (key2898, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2913, -1), (key2905, -1), (key2883, -1), (key2832, -1), (key2870, -1), (key2829, -1), (key2992, 1), (key2961, 1), (key2913, 1), (key2748, 1), (key2829, 1), (key2726, 1)]

theorem rawRowCheck2364 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form9 = rawRow2364 := by decide +kernel

def row2364 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, 1), (key2654, -1), (key2706, -1), (key2726, 1), (key2738, -1), (key2748, 1), (key2809, 1), (key2832, -1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2951, -1), (key2961, 1), (key2977, -1), (key2992, 1)]

theorem rowCheck2364 : row2364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2364 := by decide +kernel

theorem rowEval2364 (x : Key → ℝ) : Integer.Sparse.eval row2364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2364, Integer.Sparse.eval_collectBalanced, rawRowCheck2364]

def rawRow2365 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2726, 1), (key2729, 1), (key2726, 1), (key2748, 1), (key2729, 1), (key2748, 1), (key2632, 2), (key2632, 2), (key2649, 2), (key2870, -1), (key2905, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2984, -1), (key2640, -1), (key2642, -1), (key2640, -1), (key2654, -1), (key2642, -1), (key2654, -1), (key2860, 1), (key2898, 1), (key2860, 1), (key2977, 1), (key2898, 1), (key2977, 1)]

theorem rawRowCheck2365 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2365 := by decide +kernel

def row2365 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck2365 : row2365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2365 := by decide +kernel

theorem rowEval2365 (x : Key → ℝ) : Integer.Sparse.eval row2365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2365, Integer.Sparse.eval_collectBalanced, rawRowCheck2365]

def rawRow2366 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2729, 1), (key2726, 1), (key2748, 1), (key2726, 1), (key2748, 1), (key2729, 1), (key2632, 2), (key2649, 2), (key2632, 2), (key2905, -1), (key2870, -1), (key2984, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2642, -1), (key2640, -1), (key2654, -1), (key2640, -1), (key2654, -1), (key2642, -1), (key2898, 1), (key2860, 1), (key2977, 1), (key2860, 1), (key2977, 1), (key2898, 1)]

theorem rawRowCheck2366 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2366 := by decide +kernel

def row2366 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck2366 : row2366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2366 := by decide +kernel

theorem rowEval2366 (x : Key → ℝ) : Integer.Sparse.eval row2366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2366, Integer.Sparse.eval_collectBalanced, rawRowCheck2366]

def rawRow2367 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2748, 1), (key2748, 1), (key2729, 1), (key2729, 1), (key2726, 1), (key2726, 1), (key2649, 2), (key2632, 2), (key2632, 2), (key2984, -1), (key2984, -1), (key2905, -1), (key2905, -1), (key2870, -1), (key2870, -1), (key2654, -1), (key2654, -1), (key2642, -1), (key2642, -1), (key2640, -1), (key2640, -1), (key2977, 1), (key2977, 1), (key2898, 1), (key2898, 1), (key2860, 1), (key2860, 1)]

theorem rawRowCheck2367 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2367 := by decide +kernel

def row2367 : Integer.Sparse Key := [(key2632, 4), (key2640, -2), (key2642, -2), (key2649, 2), (key2654, -2), (key2706, -4), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2977, 2), (key2984, -2)]

theorem rowCheck2367 : row2367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2367 := by decide +kernel

theorem rowEval2367 (x : Key → ℝ) : Integer.Sparse.eval row2367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2367, Integer.Sparse.eval_collectBalanced, rawRowCheck2367]

def rawRow2368 : Integer.Sparse Key := [(key2671, -2), (key2726, -2), (key2748, -2), (key2671, 1), (key2674, 1), (key2706, 1), (key2738, 1), (key2729, 1), (key2748, 1), (key2786, 2), (key2870, 2), (key2905, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2939, -1), (key2905, -1), (key2984, -1), (key2794, -1), (key2796, -1), (key2860, -1), (key2898, -1), (key2883, -1), (key2913, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2944, 1), (key2913, 1), (key2992, 1)]

theorem rawRowCheck2368 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form9 = rawRow2368 := by decide +kernel

def row2368 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

theorem rowCheck2368 : row2368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2368 := by decide +kernel

theorem rowEval2368 (x : Key → ℝ) : Integer.Sparse.eval row2368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2368, Integer.Sparse.eval_collectBalanced, rawRowCheck2368]

def rawRow2369 : Integer.Sparse Key := [(key2671, -2), (key2748, -2), (key2726, -2), (key2674, 1), (key2671, 1), (key2738, 1), (key2706, 1), (key2748, 1), (key2729, 1), (key2786, 2), (key2905, 2), (key2870, 2), (key2649, -1), (key2632, -1), (key2939, -1), (key2786, -1), (key2984, -1), (key2905, -1), (key2796, -1), (key2794, -1), (key2898, -1), (key2860, -1), (key2913, -1), (key2883, -1), (key2654, 1), (key2640, 1), (key2944, 1), (key2794, 1), (key2992, 1), (key2913, 1)]

theorem rawRowCheck2369 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form9 = rawRow2369 := by decide +kernel

def row2369 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

theorem rowCheck2369 : row2369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2369 := by decide +kernel

theorem rowEval2369 (x : Key → ℝ) : Integer.Sparse.eval row2369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2369, Integer.Sparse.eval_collectBalanced, rawRowCheck2369]

def rawRow2370 : Integer.Sparse Key := [(key2726, -2), (key2671, -2), (key2748, -2), (key2706, 1), (key2729, 1), (key2671, 1), (key2748, 1), (key2674, 1), (key2738, 1), (key2870, 2), (key2786, 2), (key2905, 2), (key2786, -1), (key2905, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2860, -1), (key2883, -1), (key2794, -1), (key2913, -1), (key2796, -1), (key2898, -1), (key2794, 1), (key2913, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2944, 1)]

theorem rawRowCheck2370 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form9 = rawRow2370 := by decide +kernel

def row2370 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

theorem rowCheck2370 : row2370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2370 := by decide +kernel

theorem rowEval2370 (x : Key → ℝ) : Integer.Sparse.eval row2370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2370, Integer.Sparse.eval_collectBalanced, rawRowCheck2370]

def rawRow2371 : Integer.Sparse Key := [(key2726, -2), (key2748, -2), (key2671, -2), (key2729, 1), (key2706, 1), (key2748, 1), (key2671, 1), (key2738, 1), (key2674, 1), (key2870, 2), (key2905, 2), (key2786, 2), (key2905, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2939, -1), (key2649, -1), (key2883, -1), (key2860, -1), (key2913, -1), (key2794, -1), (key2898, -1), (key2796, -1), (key2913, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2944, 1), (key2654, 1)]

theorem rawRowCheck2371 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form9 = rawRow2371 := by decide +kernel

def row2371 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

theorem rowCheck2371 : row2371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2371 := by decide +kernel

theorem rowEval2371 (x : Key → ℝ) : Integer.Sparse.eval row2371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2371, Integer.Sparse.eval_collectBalanced, rawRowCheck2371]

def rawRow2372 : Integer.Sparse Key := [(key2748, -2), (key2671, -2), (key2726, -2), (key2738, 1), (key2748, 1), (key2674, 1), (key2729, 1), (key2671, 1), (key2706, 1), (key2905, 2), (key2786, 2), (key2870, 2), (key2939, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2632, -1), (key2786, -1), (key2898, -1), (key2913, -1), (key2796, -1), (key2883, -1), (key2794, -1), (key2860, -1), (key2944, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2640, 1), (key2794, 1)]

theorem rawRowCheck2372 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form9 = rawRow2372 := by decide +kernel

def row2372 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

theorem rowCheck2372 : row2372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2372 := by decide +kernel

theorem rowEval2372 (x : Key → ℝ) : Integer.Sparse.eval row2372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2372, Integer.Sparse.eval_collectBalanced, rawRowCheck2372]

def rawRow2373 : Integer.Sparse Key := [(key2748, -2), (key2726, -2), (key2671, -2), (key2748, 1), (key2738, 1), (key2729, 1), (key2674, 1), (key2706, 1), (key2671, 1), (key2905, 2), (key2870, 2), (key2786, 2), (key2984, -1), (key2939, -1), (key2905, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2913, -1), (key2898, -1), (key2883, -1), (key2796, -1), (key2860, -1), (key2794, -1), (key2992, 1), (key2944, 1), (key2913, 1), (key2654, 1), (key2794, 1), (key2640, 1)]

theorem rawRowCheck2373 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form9 = rawRow2373 := by decide +kernel

def row2373 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2726, -2), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, 1), (key2796, -1), (key2860, -1), (key2870, 2), (key2883, -1), (key2898, -1), (key2905, 1), (key2939, -1), (key2944, 1), (key2984, -1), (key2992, 1)]

theorem rowCheck2373 : row2373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2373 := by decide +kernel

theorem rowEval2373 (x : Key → ℝ) : Integer.Sparse.eval row2373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2373, Integer.Sparse.eval_collectBalanced, rawRowCheck2373]

def rawRow2374 : Integer.Sparse Key := [(key2809, -2), (key2860, -2), (key2898, -2), (key2829, 1), (key2832, 1), (key2870, 1), (key2905, 1), (key2883, 1), (key2913, 1), (key2616, 2), (key2640, 2), (key2654, 2), (key2726, -1), (key2748, -1), (key2829, -1), (key2961, -1), (key2913, -1), (key2992, -1), (key2616, -1), (key2619, -1), (key2632, -1), (key2649, -1), (key2642, -1), (key2654, -1), (key2706, 1), (key2738, 1), (key2809, 1), (key2951, 1), (key2898, 1), (key2977, 1)]

theorem rawRowCheck2374 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form9 = rawRow2374 := by decide +kernel

def row2374 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

theorem rowCheck2374 : row2374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2374 := by decide +kernel

theorem rowEval2374 (x : Key → ℝ) : Integer.Sparse.eval row2374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2374, Integer.Sparse.eval_collectBalanced, rawRowCheck2374]

def rawRow2375 : Integer.Sparse Key := [(key2809, -2), (key2898, -2), (key2860, -2), (key2832, 1), (key2829, 1), (key2905, 1), (key2870, 1), (key2913, 1), (key2883, 1), (key2616, 2), (key2654, 2), (key2640, 2), (key2748, -1), (key2726, -1), (key2961, -1), (key2829, -1), (key2992, -1), (key2913, -1), (key2619, -1), (key2616, -1), (key2649, -1), (key2632, -1), (key2654, -1), (key2642, -1), (key2738, 1), (key2706, 1), (key2951, 1), (key2809, 1), (key2977, 1), (key2898, 1)]

theorem rawRowCheck2375 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form9 = rawRow2375 := by decide +kernel

def row2375 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

theorem rowCheck2375 : row2375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2375 := by decide +kernel

theorem rowEval2375 (x : Key → ℝ) : Integer.Sparse.eval row2375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2375, Integer.Sparse.eval_collectBalanced, rawRowCheck2375]

def rawRow2376 : Integer.Sparse Key := [(key2860, -2), (key2809, -2), (key2898, -2), (key2870, 1), (key2883, 1), (key2829, 1), (key2913, 1), (key2832, 1), (key2905, 1), (key2640, 2), (key2616, 2), (key2654, 2), (key2829, -1), (key2913, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2632, -1), (key2642, -1), (key2616, -1), (key2654, -1), (key2619, -1), (key2649, -1), (key2809, 1), (key2898, 1), (key2706, 1), (key2977, 1), (key2738, 1), (key2951, 1)]

theorem rawRowCheck2376 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form9 = rawRow2376 := by decide +kernel

def row2376 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

theorem rowCheck2376 : row2376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2376 := by decide +kernel

theorem rowEval2376 (x : Key → ℝ) : Integer.Sparse.eval row2376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2376, Integer.Sparse.eval_collectBalanced, rawRowCheck2376]

def rawRow2377 : Integer.Sparse Key := [(key2860, -2), (key2898, -2), (key2809, -2), (key2883, 1), (key2870, 1), (key2913, 1), (key2829, 1), (key2905, 1), (key2832, 1), (key2640, 2), (key2654, 2), (key2616, 2), (key2913, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2961, -1), (key2748, -1), (key2642, -1), (key2632, -1), (key2654, -1), (key2616, -1), (key2649, -1), (key2619, -1), (key2898, 1), (key2809, 1), (key2977, 1), (key2706, 1), (key2951, 1), (key2738, 1)]

theorem rawRowCheck2377 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form9 = rawRow2377 := by decide +kernel

def row2377 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

theorem rowCheck2377 : row2377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2377 := by decide +kernel

theorem rowEval2377 (x : Key → ℝ) : Integer.Sparse.eval row2377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2377, Integer.Sparse.eval_collectBalanced, rawRowCheck2377]

def rawRow2378 : Integer.Sparse Key := [(key2898, -2), (key2809, -2), (key2860, -2), (key2905, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2829, 1), (key2870, 1), (key2654, 2), (key2616, 2), (key2640, 2), (key2961, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2726, -1), (key2829, -1), (key2649, -1), (key2654, -1), (key2619, -1), (key2642, -1), (key2616, -1), (key2632, -1), (key2951, 1), (key2977, 1), (key2738, 1), (key2898, 1), (key2706, 1), (key2809, 1)]

theorem rawRowCheck2378 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form9 = rawRow2378 := by decide +kernel

def row2378 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

theorem rowCheck2378 : row2378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2378 := by decide +kernel

theorem rowEval2378 (x : Key → ℝ) : Integer.Sparse.eval row2378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2378, Integer.Sparse.eval_collectBalanced, rawRowCheck2378]

def rawRow2379 : Integer.Sparse Key := [(key2898, -2), (key2860, -2), (key2809, -2), (key2913, 1), (key2905, 1), (key2883, 1), (key2832, 1), (key2870, 1), (key2829, 1), (key2654, 2), (key2640, 2), (key2616, 2), (key2992, -1), (key2961, -1), (key2913, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2654, -1), (key2649, -1), (key2642, -1), (key2619, -1), (key2632, -1), (key2616, -1), (key2977, 1), (key2951, 1), (key2898, 1), (key2738, 1), (key2809, 1), (key2706, 1)]

theorem rawRowCheck2379 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form9 = rawRow2379 := by decide +kernel

def row2379 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2640, 2), (key2642, -1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2738, 1), (key2748, -1), (key2809, -1), (key2832, 1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, -1), (key2905, 1), (key2951, 1), (key2961, -1), (key2977, 1), (key2992, -1)]

theorem rowCheck2379 : row2379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2379 := by decide +kernel

theorem rowEval2379 (x : Key → ℝ) : Integer.Sparse.eval row2379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2379, Integer.Sparse.eval_collectBalanced, rawRowCheck2379]

def rawRow2380 : Integer.Sparse Key := [(key2786, -2), (key2870, -2), (key2905, -2), (key2794, 1), (key2796, 1), (key2860, 1), (key2898, 1), (key2883, 1), (key2913, 1), (key2671, 2), (key2726, 2), (key2748, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2944, -1), (key2913, -1), (key2992, -1), (key2671, -1), (key2674, -1), (key2706, -1), (key2738, -1), (key2729, -1), (key2748, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2939, 1), (key2905, 1), (key2984, 1)]

theorem rawRowCheck2380 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form9 = rawRow2380 := by decide +kernel

def row2380 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

theorem rowCheck2380 : row2380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2380 := by decide +kernel

theorem rowEval2380 (x : Key → ℝ) : Integer.Sparse.eval row2380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2380, Integer.Sparse.eval_collectBalanced, rawRowCheck2380]

def rawRow2381 : Integer.Sparse Key := [(key2786, -2), (key2905, -2), (key2870, -2), (key2796, 1), (key2794, 1), (key2898, 1), (key2860, 1), (key2913, 1), (key2883, 1), (key2671, 2), (key2748, 2), (key2726, 2), (key2654, -1), (key2640, -1), (key2944, -1), (key2794, -1), (key2992, -1), (key2913, -1), (key2674, -1), (key2671, -1), (key2738, -1), (key2706, -1), (key2748, -1), (key2729, -1), (key2649, 1), (key2632, 1), (key2939, 1), (key2786, 1), (key2984, 1), (key2905, 1)]

theorem rawRowCheck2381 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form9 = rawRow2381 := by decide +kernel

def row2381 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

theorem rowCheck2381 : row2381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2381 := by decide +kernel

theorem rowEval2381 (x : Key → ℝ) : Integer.Sparse.eval row2381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2381, Integer.Sparse.eval_collectBalanced, rawRowCheck2381]

def rawRow2382 : Integer.Sparse Key := [(key2870, -2), (key2786, -2), (key2905, -2), (key2860, 1), (key2883, 1), (key2794, 1), (key2913, 1), (key2796, 1), (key2898, 1), (key2726, 2), (key2671, 2), (key2748, 2), (key2794, -1), (key2913, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2706, -1), (key2729, -1), (key2671, -1), (key2748, -1), (key2674, -1), (key2738, -1), (key2786, 1), (key2905, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2939, 1)]

theorem rawRowCheck2382 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form9 = rawRow2382 := by decide +kernel

def row2382 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

theorem rowCheck2382 : row2382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2382 := by decide +kernel

theorem rowEval2382 (x : Key → ℝ) : Integer.Sparse.eval row2382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2382, Integer.Sparse.eval_collectBalanced, rawRowCheck2382]

def rawRow2383 : Integer.Sparse Key := [(key2870, -2), (key2905, -2), (key2786, -2), (key2883, 1), (key2860, 1), (key2913, 1), (key2794, 1), (key2898, 1), (key2796, 1), (key2726, 2), (key2748, 2), (key2671, 2), (key2913, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2944, -1), (key2654, -1), (key2729, -1), (key2706, -1), (key2748, -1), (key2671, -1), (key2738, -1), (key2674, -1), (key2905, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2939, 1), (key2649, 1)]

theorem rawRowCheck2383 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form9 = rawRow2383 := by decide +kernel

def row2383 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

theorem rowCheck2383 : row2383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2383 := by decide +kernel

theorem rowEval2383 (x : Key → ℝ) : Integer.Sparse.eval row2383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2383, Integer.Sparse.eval_collectBalanced, rawRowCheck2383]

def rawRow2384 : Integer.Sparse Key := [(key2905, -2), (key2786, -2), (key2870, -2), (key2898, 1), (key2913, 1), (key2796, 1), (key2883, 1), (key2794, 1), (key2860, 1), (key2748, 2), (key2671, 2), (key2726, 2), (key2944, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2640, -1), (key2794, -1), (key2738, -1), (key2748, -1), (key2674, -1), (key2729, -1), (key2671, -1), (key2706, -1), (key2939, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2632, 1), (key2786, 1)]

theorem rawRowCheck2384 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form9 = rawRow2384 := by decide +kernel

def row2384 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

theorem rowCheck2384 : row2384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2384 := by decide +kernel

theorem rowEval2384 (x : Key → ℝ) : Integer.Sparse.eval row2384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2384, Integer.Sparse.eval_collectBalanced, rawRowCheck2384]

def rawRow2385 : Integer.Sparse Key := [(key2905, -2), (key2870, -2), (key2786, -2), (key2913, 1), (key2898, 1), (key2883, 1), (key2796, 1), (key2860, 1), (key2794, 1), (key2748, 2), (key2726, 2), (key2671, 2), (key2992, -1), (key2944, -1), (key2913, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2748, -1), (key2738, -1), (key2729, -1), (key2674, -1), (key2706, -1), (key2671, -1), (key2984, 1), (key2939, 1), (key2905, 1), (key2649, 1), (key2786, 1), (key2632, 1)]

theorem rawRowCheck2385 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form9 = rawRow2385 := by decide +kernel

def row2385 : Integer.Sparse Key := [(key2632, 1), (key2640, -1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2796, 1), (key2860, 1), (key2870, -2), (key2883, 1), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2984, 1), (key2992, -1)]

theorem rowCheck2385 : row2385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2385 := by decide +kernel

theorem rowEval2385 (x : Key → ℝ) : Integer.Sparse.eval row2385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck2385, Integer.Sparse.eval_collectBalanced, rawRowCheck2385]

def rawRow2386 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2375, -2), (key2387, 6), (key2399, 2), (key2403, 2), (key2403, 2), (key2477, -2), (key2477, -2), (key2541, -2), (key2434, -6), (key2500, 2), (key2500, 2), (key2552, 2)]

theorem rawRowCheck2386 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2386 := by decide +kernel

def row2386 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck2386 : row2386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2386 := by decide +kernel

theorem rowEval2386 (x : Key → ℝ) : Integer.Sparse.eval row2386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2386, Integer.Sparse.eval_collectBalanced, rawRowCheck2386]

def rawRow2387 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2375, -2), (key2387, 6), (key2403, 2), (key2399, 2), (key2403, 2), (key2477, -2), (key2541, -2), (key2477, -2), (key2434, -6), (key2500, 2), (key2552, 2), (key2500, 2)]

theorem rawRowCheck2387 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2387 := by decide +kernel

def row2387 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck2387 : row2387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2387 := by decide +kernel

theorem rowEval2387 (x : Key → ℝ) : Integer.Sparse.eval row2387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2387, Integer.Sparse.eval_collectBalanced, rawRowCheck2387]

def rawRow2388 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2371, -2), (key2387, 6), (key2403, 2), (key2403, 2), (key2399, 2), (key2541, -2), (key2477, -2), (key2477, -2), (key2434, -6), (key2552, 2), (key2500, 2), (key2500, 2)]

theorem rawRowCheck2388 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2388 := by decide +kernel

def row2388 : Integer.Sparse Key := [(key2371, -2), (key2375, -4), (key2387, 6), (key2399, 2), (key2403, 4), (key2434, -6), (key2477, -4), (key2500, 4), (key2541, -2), (key2552, 2)]

theorem rowCheck2388 : row2388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2388 := by decide +kernel

theorem rowEval2388 (x : Key → ℝ) : Integer.Sparse.eval row2388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2388, Integer.Sparse.eval_collectBalanced, rawRowCheck2388]

def rawRow2389 : Integer.Sparse Key := [(key2371, -2), (key2375, -2), (key2387, -2), (key2375, 6), (key2465, 2), (key2469, 2), (key2477, 2), (key2403, -2), (key2469, -2), (key2536, -2), (key2500, -6), (key2434, 2), (key2500, 2), (key2552, 2)]

theorem rawRowCheck2389 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form10 = rawRow2389 := by decide +kernel

def row2389 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

theorem rowCheck2389 : row2389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2389 := by decide +kernel

theorem rowEval2389 (x : Key → ℝ) : Integer.Sparse.eval row2389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2389, Integer.Sparse.eval_collectBalanced, rawRowCheck2389]

def rawRow2390 : Integer.Sparse Key := [(key2375, -2), (key2371, -2), (key2387, -2), (key2375, 6), (key2469, 2), (key2465, 2), (key2477, 2), (key2403, -2), (key2536, -2), (key2469, -2), (key2500, -6), (key2434, 2), (key2552, 2), (key2500, 2)]

theorem rawRowCheck2390 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form10 = rawRow2390 := by decide +kernel

def row2390 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

theorem rowCheck2390 : row2390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2390 := by decide +kernel

theorem rowEval2390 (x : Key → ℝ) : Integer.Sparse.eval row2390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2390, Integer.Sparse.eval_collectBalanced, rawRowCheck2390]

def rawRow2391 : Integer.Sparse Key := [(key2371, -2), (key2387, -2), (key2375, -2), (key2375, 6), (key2465, 2), (key2477, 2), (key2469, 2), (key2469, -2), (key2403, -2), (key2536, -2), (key2500, -6), (key2500, 2), (key2434, 2), (key2552, 2)]

theorem rawRowCheck2391 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form10 = rawRow2391 := by decide +kernel

def row2391 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

theorem rowCheck2391 : row2391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2391 := by decide +kernel

theorem rowEval2391 (x : Key → ℝ) : Integer.Sparse.eval row2391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2391, Integer.Sparse.eval_collectBalanced, rawRowCheck2391]

def rawRow2392 : Integer.Sparse Key := [(key2387, -2), (key2371, -2), (key2375, -2), (key2375, 6), (key2477, 2), (key2465, 2), (key2469, 2), (key2469, -2), (key2536, -2), (key2403, -2), (key2500, -6), (key2500, 2), (key2552, 2), (key2434, 2)]

theorem rawRowCheck2392 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form10 = rawRow2392 := by decide +kernel

def row2392 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

theorem rowCheck2392 : row2392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2392 := by decide +kernel

theorem rowEval2392 (x : Key → ℝ) : Integer.Sparse.eval row2392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2392, Integer.Sparse.eval_collectBalanced, rawRowCheck2392]

def rawRow2393 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2371, -2), (key2375, 6), (key2469, 2), (key2477, 2), (key2465, 2), (key2536, -2), (key2403, -2), (key2469, -2), (key2500, -6), (key2552, 2), (key2434, 2), (key2500, 2)]

theorem rawRowCheck2393 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form10 = rawRow2393 := by decide +kernel

def row2393 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

theorem rowCheck2393 : row2393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2393 := by decide +kernel

theorem rowEval2393 (x : Key → ℝ) : Integer.Sparse.eval row2393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2393, Integer.Sparse.eval_collectBalanced, rawRowCheck2393]

def rawRow2394 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2371, -2), (key2375, 6), (key2477, 2), (key2469, 2), (key2465, 2), (key2536, -2), (key2469, -2), (key2403, -2), (key2500, -6), (key2552, 2), (key2500, 2), (key2434, 2)]

theorem rawRowCheck2394 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form10 = rawRow2394 := by decide +kernel

def row2394 : Integer.Sparse Key := [(key2371, -2), (key2375, 4), (key2387, -2), (key2403, -2), (key2434, 2), (key2465, 2), (key2477, 2), (key2500, -4), (key2536, -2), (key2552, 2)]

theorem rowCheck2394 : row2394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2394 := by decide +kernel

theorem rowEval2394 (x : Key → ℝ) : Integer.Sparse.eval row2394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2394, Integer.Sparse.eval_collectBalanced, rawRowCheck2394]

def rawRow2395 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2403, -2), (key2434, 6), (key2371, 2), (key2375, 2), (key2375, 2), (key2500, -2), (key2500, -2), (key2552, -2), (key2387, -6), (key2477, 2), (key2477, 2), (key2541, 2)]

theorem rawRowCheck2395 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2395 := by decide +kernel

def row2395 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

theorem rowCheck2395 : row2395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2395 := by decide +kernel

theorem rowEval2395 (x : Key → ℝ) : Integer.Sparse.eval row2395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2395, Integer.Sparse.eval_collectBalanced, rawRowCheck2395]

def rawRow2396 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2403, -2), (key2434, 6), (key2375, 2), (key2371, 2), (key2375, 2), (key2500, -2), (key2552, -2), (key2500, -2), (key2387, -6), (key2477, 2), (key2541, 2), (key2477, 2)]

theorem rawRowCheck2396 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2396 := by decide +kernel

def row2396 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

theorem rowCheck2396 : row2396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2396 := by decide +kernel

theorem rowEval2396 (x : Key → ℝ) : Integer.Sparse.eval row2396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2396, Integer.Sparse.eval_collectBalanced, rawRowCheck2396]

def rawRow2397 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2399, -2), (key2434, 6), (key2375, 2), (key2375, 2), (key2371, 2), (key2552, -2), (key2500, -2), (key2500, -2), (key2387, -6), (key2541, 2), (key2477, 2), (key2477, 2)]

theorem rawRowCheck2397 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2397 := by decide +kernel

def row2397 : Integer.Sparse Key := [(key2371, 2), (key2375, 4), (key2387, -6), (key2399, -2), (key2403, -4), (key2434, 6), (key2477, 4), (key2500, -4), (key2541, 2), (key2552, -2)]

theorem rowCheck2397 : row2397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2397 := by decide +kernel

theorem rowEval2397 (x : Key → ℝ) : Integer.Sparse.eval row2397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2397, Integer.Sparse.eval_collectBalanced, rawRowCheck2397]

def rawRow2398 : Integer.Sparse Key := [(key2399, -2), (key2403, -2), (key2434, -2), (key2403, 6), (key2465, 2), (key2469, 2), (key2500, 2), (key2375, -2), (key2469, -2), (key2536, -2), (key2477, -6), (key2387, 2), (key2477, 2), (key2541, 2)]

theorem rawRowCheck2398 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form10 = rawRow2398 := by decide +kernel

def row2398 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

theorem rowCheck2398 : row2398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2398 := by decide +kernel

theorem rowEval2398 (x : Key → ℝ) : Integer.Sparse.eval row2398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2398, Integer.Sparse.eval_collectBalanced, rawRowCheck2398]

def rawRow2399 : Integer.Sparse Key := [(key2403, -2), (key2399, -2), (key2434, -2), (key2403, 6), (key2469, 2), (key2465, 2), (key2500, 2), (key2375, -2), (key2536, -2), (key2469, -2), (key2477, -6), (key2387, 2), (key2541, 2), (key2477, 2)]

theorem rawRowCheck2399 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form10 = rawRow2399 := by decide +kernel

def row2399 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

theorem rowCheck2399 : row2399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2399 := by decide +kernel

theorem rowEval2399 (x : Key → ℝ) : Integer.Sparse.eval row2399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2399, Integer.Sparse.eval_collectBalanced, rawRowCheck2399]

def rawRow2400 : Integer.Sparse Key := [(key2399, -2), (key2434, -2), (key2403, -2), (key2403, 6), (key2465, 2), (key2500, 2), (key2469, 2), (key2469, -2), (key2375, -2), (key2536, -2), (key2477, -6), (key2477, 2), (key2387, 2), (key2541, 2)]

theorem rawRowCheck2400 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form10 = rawRow2400 := by decide +kernel

def row2400 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

theorem rowCheck2400 : row2400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2400 := by decide +kernel

theorem rowEval2400 (x : Key → ℝ) : Integer.Sparse.eval row2400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2400, Integer.Sparse.eval_collectBalanced, rawRowCheck2400]

def rawRow2401 : Integer.Sparse Key := [(key2434, -2), (key2399, -2), (key2403, -2), (key2403, 6), (key2500, 2), (key2465, 2), (key2469, 2), (key2469, -2), (key2536, -2), (key2375, -2), (key2477, -6), (key2477, 2), (key2541, 2), (key2387, 2)]

theorem rawRowCheck2401 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form10 = rawRow2401 := by decide +kernel

def row2401 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

theorem rowCheck2401 : row2401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2401 := by decide +kernel

theorem rowEval2401 (x : Key → ℝ) : Integer.Sparse.eval row2401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2401, Integer.Sparse.eval_collectBalanced, rawRowCheck2401]

def rawRow2402 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2399, -2), (key2403, 6), (key2469, 2), (key2500, 2), (key2465, 2), (key2536, -2), (key2375, -2), (key2469, -2), (key2477, -6), (key2541, 2), (key2387, 2), (key2477, 2)]

theorem rawRowCheck2402 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form10 = rawRow2402 := by decide +kernel

def row2402 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

theorem rowCheck2402 : row2402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2402 := by decide +kernel

theorem rowEval2402 (x : Key → ℝ) : Integer.Sparse.eval row2402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2402, Integer.Sparse.eval_collectBalanced, rawRowCheck2402]

def rawRow2403 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2399, -2), (key2403, 6), (key2500, 2), (key2469, 2), (key2465, 2), (key2536, -2), (key2469, -2), (key2375, -2), (key2477, -6), (key2541, 2), (key2477, 2), (key2387, 2)]

theorem rawRowCheck2403 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form10 = rawRow2403 := by decide +kernel

def row2403 : Integer.Sparse Key := [(key2375, -2), (key2387, 2), (key2399, -2), (key2403, 4), (key2434, -2), (key2465, 2), (key2477, -4), (key2500, 2), (key2536, -2), (key2541, 2)]

theorem rowCheck2403 : row2403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2403 := by decide +kernel

theorem rowEval2403 (x : Key → ℝ) : Integer.Sparse.eval row2403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2403, Integer.Sparse.eval_collectBalanced, rawRowCheck2403]

def rawRow2404 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2477, -2), (key2500, 6), (key2371, 2), (key2375, 2), (key2387, 2), (key2434, -2), (key2500, -2), (key2552, -2), (key2375, -6), (key2403, 2), (key2469, 2), (key2536, 2)]

theorem rawRowCheck2404 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form10 = rawRow2404 := by decide +kernel

def row2404 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

theorem rowCheck2404 : row2404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2404 := by decide +kernel

theorem rowEval2404 (x : Key → ℝ) : Integer.Sparse.eval row2404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2404, Integer.Sparse.eval_collectBalanced, rawRowCheck2404]

def rawRow2405 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2477, -2), (key2500, 6), (key2375, 2), (key2371, 2), (key2387, 2), (key2434, -2), (key2552, -2), (key2500, -2), (key2375, -6), (key2403, 2), (key2536, 2), (key2469, 2)]

theorem rawRowCheck2405 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form10 = rawRow2405 := by decide +kernel

def row2405 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

theorem rowCheck2405 : row2405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2405 := by decide +kernel

theorem rowEval2405 (x : Key → ℝ) : Integer.Sparse.eval row2405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2405, Integer.Sparse.eval_collectBalanced, rawRowCheck2405]

def rawRow2406 : Integer.Sparse Key := [(key2465, -2), (key2477, -2), (key2469, -2), (key2500, 6), (key2371, 2), (key2387, 2), (key2375, 2), (key2500, -2), (key2434, -2), (key2552, -2), (key2375, -6), (key2469, 2), (key2403, 2), (key2536, 2)]

theorem rawRowCheck2406 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form10 = rawRow2406 := by decide +kernel

def row2406 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

theorem rowCheck2406 : row2406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2406 := by decide +kernel

theorem rowEval2406 (x : Key → ℝ) : Integer.Sparse.eval row2406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2406, Integer.Sparse.eval_collectBalanced, rawRowCheck2406]

def rawRow2407 : Integer.Sparse Key := [(key2477, -2), (key2465, -2), (key2469, -2), (key2500, 6), (key2387, 2), (key2371, 2), (key2375, 2), (key2500, -2), (key2552, -2), (key2434, -2), (key2375, -6), (key2469, 2), (key2536, 2), (key2403, 2)]

theorem rawRowCheck2407 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form10 = rawRow2407 := by decide +kernel

def row2407 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

theorem rowCheck2407 : row2407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2407 := by decide +kernel

theorem rowEval2407 (x : Key → ℝ) : Integer.Sparse.eval row2407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2407, Integer.Sparse.eval_collectBalanced, rawRowCheck2407]

def rawRow2408 : Integer.Sparse Key := [(key2469, -2), (key2477, -2), (key2465, -2), (key2500, 6), (key2375, 2), (key2387, 2), (key2371, 2), (key2552, -2), (key2434, -2), (key2500, -2), (key2375, -6), (key2536, 2), (key2403, 2), (key2469, 2)]

theorem rawRowCheck2408 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form10 = rawRow2408 := by decide +kernel

def row2408 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

theorem rowCheck2408 : row2408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2408 := by decide +kernel

theorem rowEval2408 (x : Key → ℝ) : Integer.Sparse.eval row2408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2408, Integer.Sparse.eval_collectBalanced, rawRowCheck2408]

def rawRow2409 : Integer.Sparse Key := [(key2477, -2), (key2469, -2), (key2465, -2), (key2500, 6), (key2387, 2), (key2375, 2), (key2371, 2), (key2552, -2), (key2500, -2), (key2434, -2), (key2375, -6), (key2536, 2), (key2469, 2), (key2403, 2)]

theorem rawRowCheck2409 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form10 = rawRow2409 := by decide +kernel

def row2409 : Integer.Sparse Key := [(key2371, 2), (key2375, -4), (key2387, 2), (key2403, 2), (key2434, -2), (key2465, -2), (key2477, -2), (key2500, 4), (key2536, 2), (key2552, -2)]

theorem rowCheck2409 : row2409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2409 := by decide +kernel

theorem rowEval2409 (x : Key → ℝ) : Integer.Sparse.eval row2409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2409, Integer.Sparse.eval_collectBalanced, rawRowCheck2409]

def rawRow2410 : Integer.Sparse Key := [(key2465, -2), (key2469, -2), (key2500, -2), (key2477, 6), (key2399, 2), (key2403, 2), (key2434, 2), (key2387, -2), (key2477, -2), (key2541, -2), (key2403, -6), (key2375, 2), (key2469, 2), (key2536, 2)]

theorem rawRowCheck2410 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form10 = rawRow2410 := by decide +kernel

def row2410 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

theorem rowCheck2410 : row2410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2410 := by decide +kernel

theorem rowEval2410 (x : Key → ℝ) : Integer.Sparse.eval row2410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2410, Integer.Sparse.eval_collectBalanced, rawRowCheck2410]

def rawRow2411 : Integer.Sparse Key := [(key2469, -2), (key2465, -2), (key2500, -2), (key2477, 6), (key2403, 2), (key2399, 2), (key2434, 2), (key2387, -2), (key2541, -2), (key2477, -2), (key2403, -6), (key2375, 2), (key2536, 2), (key2469, 2)]

theorem rawRowCheck2411 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form10 = rawRow2411 := by decide +kernel

def row2411 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

theorem rowCheck2411 : row2411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2411 := by decide +kernel

theorem rowEval2411 (x : Key → ℝ) : Integer.Sparse.eval row2411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2411, Integer.Sparse.eval_collectBalanced, rawRowCheck2411]

def rawRow2412 : Integer.Sparse Key := [(key2465, -2), (key2500, -2), (key2469, -2), (key2477, 6), (key2399, 2), (key2434, 2), (key2403, 2), (key2477, -2), (key2387, -2), (key2541, -2), (key2403, -6), (key2469, 2), (key2375, 2), (key2536, 2)]

theorem rawRowCheck2412 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form10 = rawRow2412 := by decide +kernel

def row2412 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

theorem rowCheck2412 : row2412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2412 := by decide +kernel

theorem rowEval2412 (x : Key → ℝ) : Integer.Sparse.eval row2412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2412, Integer.Sparse.eval_collectBalanced, rawRowCheck2412]

def rawRow2413 : Integer.Sparse Key := [(key2500, -2), (key2465, -2), (key2469, -2), (key2477, 6), (key2434, 2), (key2399, 2), (key2403, 2), (key2477, -2), (key2541, -2), (key2387, -2), (key2403, -6), (key2469, 2), (key2536, 2), (key2375, 2)]

theorem rawRowCheck2413 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form10 = rawRow2413 := by decide +kernel

def row2413 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

theorem rowCheck2413 : row2413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2413 := by decide +kernel

theorem rowEval2413 (x : Key → ℝ) : Integer.Sparse.eval row2413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2413, Integer.Sparse.eval_collectBalanced, rawRowCheck2413]

def rawRow2414 : Integer.Sparse Key := [(key2469, -2), (key2500, -2), (key2465, -2), (key2477, 6), (key2403, 2), (key2434, 2), (key2399, 2), (key2541, -2), (key2387, -2), (key2477, -2), (key2403, -6), (key2536, 2), (key2375, 2), (key2469, 2)]

theorem rawRowCheck2414 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form10 = rawRow2414 := by decide +kernel

def row2414 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

theorem rowCheck2414 : row2414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2414 := by decide +kernel

theorem rowEval2414 (x : Key → ℝ) : Integer.Sparse.eval row2414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2414, Integer.Sparse.eval_collectBalanced, rawRowCheck2414]

def rawRow2415 : Integer.Sparse Key := [(key2500, -2), (key2469, -2), (key2465, -2), (key2477, 6), (key2434, 2), (key2403, 2), (key2399, 2), (key2541, -2), (key2477, -2), (key2387, -2), (key2403, -6), (key2536, 2), (key2469, 2), (key2375, 2)]

theorem rawRowCheck2415 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form10 = rawRow2415 := by decide +kernel

def row2415 : Integer.Sparse Key := [(key2375, 2), (key2387, -2), (key2399, 2), (key2403, -4), (key2434, 2), (key2465, -2), (key2477, 4), (key2500, -2), (key2536, 2), (key2541, -2)]

theorem rowCheck2415 : row2415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2415 := by decide +kernel

theorem rowEval2415 (x : Key → ℝ) : Integer.Sparse.eval row2415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck2415, Integer.Sparse.eval_collectBalanced, rawRowCheck2415]

def rawRow2416 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2373, -2), (key2386, 6), (key2762, 2), (key2765, 2), (key2765, 2), (key2886, -2), (key2886, -2), (key2908, -2), (key2928, -6), (key2965, 2), (key2965, 2), (key2987, 2)]

theorem rawRowCheck2416 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2416 := by decide +kernel

def row2416 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

theorem rowCheck2416 : row2416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2416 := by decide +kernel

theorem rowEval2416 (x : Key → ℝ) : Integer.Sparse.eval row2416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2416, Integer.Sparse.eval_collectBalanced, rawRowCheck2416]

def rawRow2417 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2373, -2), (key2386, 6), (key2765, 2), (key2762, 2), (key2765, 2), (key2886, -2), (key2908, -2), (key2886, -2), (key2928, -6), (key2965, 2), (key2987, 2), (key2965, 2)]

theorem rawRowCheck2417 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2417 := by decide +kernel

def row2417 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

theorem rowCheck2417 : row2417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2417 := by decide +kernel

theorem rowEval2417 (x : Key → ℝ) : Integer.Sparse.eval row2417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2417, Integer.Sparse.eval_collectBalanced, rawRowCheck2417]

def rawRow2418 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2370, -2), (key2386, 6), (key2765, 2), (key2765, 2), (key2762, 2), (key2908, -2), (key2886, -2), (key2886, -2), (key2928, -6), (key2987, 2), (key2965, 2), (key2965, 2)]

theorem rawRowCheck2418 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2418 := by decide +kernel

def row2418 : Integer.Sparse Key := [(key2370, -2), (key2373, -4), (key2386, 6), (key2762, 2), (key2765, 4), (key2886, -4), (key2908, -2), (key2928, -6), (key2965, 4), (key2987, 2)]

theorem rowCheck2418 : row2418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2418 := by decide +kernel

theorem rowEval2418 (x : Key → ℝ) : Integer.Sparse.eval row2418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2418, Integer.Sparse.eval_collectBalanced, rawRowCheck2418]

def rawRow2419 : Integer.Sparse Key := [(key2370, -2), (key2373, -2), (key2386, -2), (key2373, 6), (key2839, 2), (key2842, 2), (key2886, 2), (key2765, -2), (key2842, -2), (key2874, -2), (key2965, -6), (key2928, 2), (key2965, 2), (key2987, 2)]

theorem rawRowCheck2419 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form11 = rawRow2419 := by decide +kernel

def row2419 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

theorem rowCheck2419 : row2419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2419 := by decide +kernel

theorem rowEval2419 (x : Key → ℝ) : Integer.Sparse.eval row2419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2419, Integer.Sparse.eval_collectBalanced, rawRowCheck2419]

def rawRow2420 : Integer.Sparse Key := [(key2373, -2), (key2370, -2), (key2386, -2), (key2373, 6), (key2842, 2), (key2839, 2), (key2886, 2), (key2765, -2), (key2874, -2), (key2842, -2), (key2965, -6), (key2928, 2), (key2987, 2), (key2965, 2)]

theorem rawRowCheck2420 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form11 = rawRow2420 := by decide +kernel

def row2420 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

theorem rowCheck2420 : row2420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2420 := by decide +kernel

theorem rowEval2420 (x : Key → ℝ) : Integer.Sparse.eval row2420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2420, Integer.Sparse.eval_collectBalanced, rawRowCheck2420]

def rawRow2421 : Integer.Sparse Key := [(key2370, -2), (key2386, -2), (key2373, -2), (key2373, 6), (key2839, 2), (key2886, 2), (key2842, 2), (key2842, -2), (key2765, -2), (key2874, -2), (key2965, -6), (key2965, 2), (key2928, 2), (key2987, 2)]

theorem rawRowCheck2421 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form11 = rawRow2421 := by decide +kernel

def row2421 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

theorem rowCheck2421 : row2421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2421 := by decide +kernel

theorem rowEval2421 (x : Key → ℝ) : Integer.Sparse.eval row2421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2421, Integer.Sparse.eval_collectBalanced, rawRowCheck2421]

def rawRow2422 : Integer.Sparse Key := [(key2386, -2), (key2370, -2), (key2373, -2), (key2373, 6), (key2886, 2), (key2839, 2), (key2842, 2), (key2842, -2), (key2874, -2), (key2765, -2), (key2965, -6), (key2965, 2), (key2987, 2), (key2928, 2)]

theorem rawRowCheck2422 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form11 = rawRow2422 := by decide +kernel

def row2422 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

theorem rowCheck2422 : row2422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2422 := by decide +kernel

theorem rowEval2422 (x : Key → ℝ) : Integer.Sparse.eval row2422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2422, Integer.Sparse.eval_collectBalanced, rawRowCheck2422]

def rawRow2423 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2370, -2), (key2373, 6), (key2842, 2), (key2886, 2), (key2839, 2), (key2874, -2), (key2765, -2), (key2842, -2), (key2965, -6), (key2987, 2), (key2928, 2), (key2965, 2)]

theorem rawRowCheck2423 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form11 = rawRow2423 := by decide +kernel

def row2423 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

theorem rowCheck2423 : row2423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2423 := by decide +kernel

theorem rowEval2423 (x : Key → ℝ) : Integer.Sparse.eval row2423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2423, Integer.Sparse.eval_collectBalanced, rawRowCheck2423]

def rawRow2424 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2370, -2), (key2373, 6), (key2886, 2), (key2842, 2), (key2839, 2), (key2874, -2), (key2842, -2), (key2765, -2), (key2965, -6), (key2987, 2), (key2965, 2), (key2928, 2)]

theorem rawRowCheck2424 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form11 = rawRow2424 := by decide +kernel

def row2424 : Integer.Sparse Key := [(key2370, -2), (key2373, 4), (key2386, -2), (key2765, -2), (key2839, 2), (key2874, -2), (key2886, 2), (key2928, 2), (key2965, -4), (key2987, 2)]

theorem rowCheck2424 : row2424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2424 := by decide +kernel

theorem rowEval2424 (x : Key → ℝ) : Integer.Sparse.eval row2424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2424, Integer.Sparse.eval_collectBalanced, rawRowCheck2424]

def rawRow2425 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2401, -2), (key2433, 6), (key2583, 2), (key2586, 2), (key2586, 2), (key2965, -2), (key2965, -2), (key2987, -2), (key2597, -6), (key2886, 2), (key2886, 2), (key2908, 2)]

theorem rawRowCheck2425 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2425 := by decide +kernel

def row2425 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

theorem rowCheck2425 : row2425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2425 := by decide +kernel

theorem rowEval2425 (x : Key → ℝ) : Integer.Sparse.eval row2425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2425, Integer.Sparse.eval_collectBalanced, rawRowCheck2425]

def rawRow2426 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2401, -2), (key2433, 6), (key2586, 2), (key2583, 2), (key2586, 2), (key2965, -2), (key2987, -2), (key2965, -2), (key2597, -6), (key2886, 2), (key2908, 2), (key2886, 2)]

theorem rawRowCheck2426 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2426 := by decide +kernel

def row2426 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

theorem rowCheck2426 : row2426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2426 := by decide +kernel

theorem rowEval2426 (x : Key → ℝ) : Integer.Sparse.eval row2426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2426, Integer.Sparse.eval_collectBalanced, rawRowCheck2426]

def rawRow2427 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2398, -2), (key2433, 6), (key2586, 2), (key2586, 2), (key2583, 2), (key2987, -2), (key2965, -2), (key2965, -2), (key2597, -6), (key2908, 2), (key2886, 2), (key2886, 2)]

theorem rawRowCheck2427 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2427 := by decide +kernel

def row2427 : Integer.Sparse Key := [(key2398, -2), (key2401, -4), (key2433, 6), (key2583, 2), (key2586, 4), (key2597, -6), (key2886, 4), (key2908, 2), (key2965, -4), (key2987, -2)]

theorem rowCheck2427 : row2427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2427 := by decide +kernel

theorem rowEval2427 (x : Key → ℝ) : Integer.Sparse.eval row2427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2427, Integer.Sparse.eval_collectBalanced, rawRowCheck2427]

def rawRow2428 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2401, 6), (key2839, 2), (key2842, 2), (key2965, 2), (key2586, -2), (key2842, -2), (key2874, -2), (key2886, -6), (key2597, 2), (key2886, 2), (key2908, 2)]

theorem rawRowCheck2428 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form11 = rawRow2428 := by decide +kernel

def row2428 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

theorem rowCheck2428 : row2428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2428 := by decide +kernel

theorem rowEval2428 (x : Key → ℝ) : Integer.Sparse.eval row2428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2428, Integer.Sparse.eval_collectBalanced, rawRowCheck2428]

def rawRow2429 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2433, -2), (key2401, 6), (key2842, 2), (key2839, 2), (key2965, 2), (key2586, -2), (key2874, -2), (key2842, -2), (key2886, -6), (key2597, 2), (key2908, 2), (key2886, 2)]

theorem rawRowCheck2429 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form11 = rawRow2429 := by decide +kernel

def row2429 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

theorem rowCheck2429 : row2429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2429 := by decide +kernel

theorem rowEval2429 (x : Key → ℝ) : Integer.Sparse.eval row2429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2429, Integer.Sparse.eval_collectBalanced, rawRowCheck2429]

def rawRow2430 : Integer.Sparse Key := [(key2398, -2), (key2433, -2), (key2401, -2), (key2401, 6), (key2839, 2), (key2965, 2), (key2842, 2), (key2842, -2), (key2586, -2), (key2874, -2), (key2886, -6), (key2886, 2), (key2597, 2), (key2908, 2)]

theorem rawRowCheck2430 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form11 = rawRow2430 := by decide +kernel

def row2430 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

theorem rowCheck2430 : row2430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2430 := by decide +kernel

theorem rowEval2430 (x : Key → ℝ) : Integer.Sparse.eval row2430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2430, Integer.Sparse.eval_collectBalanced, rawRowCheck2430]

def rawRow2431 : Integer.Sparse Key := [(key2433, -2), (key2398, -2), (key2401, -2), (key2401, 6), (key2965, 2), (key2839, 2), (key2842, 2), (key2842, -2), (key2874, -2), (key2586, -2), (key2886, -6), (key2886, 2), (key2908, 2), (key2597, 2)]

theorem rawRowCheck2431 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form11 = rawRow2431 := by decide +kernel

def row2431 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2586, -2), (key2597, 2), (key2839, 2), (key2874, -2), (key2886, -4), (key2908, 2), (key2965, 2)]

theorem rowCheck2431 : row2431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2431 := by decide +kernel

theorem rowEval2431 (x : Key → ℝ) : Integer.Sparse.eval row2431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form11) x := by
  rw [rowCheck2431, Integer.Sparse.eval_collectBalanced, rawRowCheck2431]

end MUB6.Certificate.GramRows

end OAI
