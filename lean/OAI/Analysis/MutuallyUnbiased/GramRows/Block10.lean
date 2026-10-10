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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow416 : Integer.Sparse Key := [(key599, -2), (key605, 1), (key611, 1), (key576, 2), (key587, -1), (key616, -1), (key571, -1), (key577, -1), (key581, 1), (key613, 1), (key473, 2), (key479, -1), (key485, -1), (key275, -2), (key344, 1), (key616, 1), (key270, 1), (key276, 1), (key338, -1), (key613, -1), (key403, -2), (key424, 1), (key485, 1), (key266, 2), (key334, -1), (key611, -1), (key245, -1), (key276, -1), (key311, 1), (key577, 1), (key392, 1), (key403, 1), (key413, -1), (key473, -1), (key255, -1), (key266, -1), (key323, 1), (key599, 1), (key243, 1), (key275, 1), (key309, -1), (key344, -1)]

theorem rawRowCheck416 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form3 = rawRow416 := by decide +kernel

def row416 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 2), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck416 : row416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow416 := by decide +kernel

theorem rowEval416 (x : Key → ℝ) : Integer.Sparse.eval row416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck416, Integer.Sparse.eval_collectBalanced, rawRowCheck416]

def rawRow417 : Integer.Sparse Key := [(key599, -2), (key611, 1), (key605, 1), (key576, 2), (key616, -1), (key587, -1), (key577, -1), (key571, -1), (key613, 1), (key581, 1), (key473, 2), (key485, -1), (key479, -1), (key275, -2), (key616, 1), (key344, 1), (key276, 1), (key270, 1), (key613, -1), (key338, -1), (key403, -2), (key485, 1), (key424, 1), (key266, 2), (key611, -1), (key334, -1), (key276, -1), (key245, -1), (key577, 1), (key311, 1), (key403, 1), (key392, 1), (key473, -1), (key413, -1), (key266, -1), (key255, -1), (key599, 1), (key323, 1), (key275, 1), (key243, 1), (key344, -1), (key309, -1)]

theorem rawRowCheck417 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form3 = rawRow417 := by decide +kernel

def row417 : Integer.Sparse Key := [(key243, 1), (key245, -1), (key255, -1), (key266, 1), (key270, 1), (key275, -1), (key309, -1), (key311, 1), (key323, 1), (key334, -1), (key338, -1), (key392, 1), (key403, -1), (key413, -1), (key424, 1), (key473, 1), (key479, -1), (key571, -1), (key576, 2), (key581, 1), (key587, -1), (key599, -1), (key605, 1)]

theorem rowCheck417 : row417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow417 := by decide +kernel

theorem rowEval417 (x : Key → ℝ) : Integer.Sparse.eval row417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form3) x := by
  rw [rowCheck417, Integer.Sparse.eval_collectBalanced, rawRowCheck417]

def rawRow418 : Integer.Sparse Key := [(key605, -2), (key599, 1), (key611, 1), (key587, 2), (key576, -1), (key616, -1), (key581, -1), (key588, -1), (key571, 1), (key614, 1), (key479, 2), (key473, -1), (key485, -1), (key344, -2), (key275, 1), (key616, 1), (key338, 1), (key345, 1), (key270, -1), (key614, -1), (key424, -2), (key403, 1), (key485, 1), (key334, 2), (key266, -1), (key611, -1), (key311, -1), (key345, -1), (key245, 1), (key588, 1), (key413, 1), (key424, 1), (key392, -1), (key479, -1), (key323, -1), (key334, -1), (key255, 1), (key605, 1), (key309, 1), (key344, 1), (key243, -1), (key587, -1)]

theorem rawRowCheck418 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form3 = rawRow418 := by decide +kernel

def row418 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck418 : row418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow418 := by decide +kernel

theorem rowEval418 (x : Key → ℝ) : Integer.Sparse.eval row418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form3) x := by
  rw [rowCheck418, Integer.Sparse.eval_collectBalanced, rawRowCheck418]

def rawRow419 : Integer.Sparse Key := [(key605, -2), (key611, 1), (key599, 1), (key587, 2), (key616, -1), (key576, -1), (key588, -1), (key581, -1), (key614, 1), (key571, 1), (key479, 2), (key485, -1), (key473, -1), (key344, -2), (key616, 1), (key275, 1), (key345, 1), (key338, 1), (key614, -1), (key270, -1), (key424, -2), (key485, 1), (key403, 1), (key334, 2), (key611, -1), (key266, -1), (key345, -1), (key311, -1), (key588, 1), (key245, 1), (key424, 1), (key413, 1), (key479, -1), (key392, -1), (key334, -1), (key323, -1), (key605, 1), (key255, 1), (key344, 1), (key309, 1), (key587, -1), (key243, -1)]

theorem rawRowCheck419 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form3 = rawRow419 := by decide +kernel

def row419 : Integer.Sparse Key := [(key243, -1), (key245, 1), (key255, 1), (key266, -1), (key270, -1), (key275, 1), (key309, 1), (key311, -1), (key323, -1), (key334, 1), (key338, 1), (key344, -1), (key392, -1), (key403, 1), (key413, 1), (key424, -1), (key473, -1), (key479, 1), (key571, 1), (key576, -1), (key581, -1), (key587, 1), (key599, 1), (key605, -1)]

theorem rowCheck419 : row419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow419 := by decide +kernel

theorem rowEval419 (x : Key → ℝ) : Integer.Sparse.eval row419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form3) x := by
  rw [rowCheck419, Integer.Sparse.eval_collectBalanced, rawRowCheck419]

def rawRow420 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1295, 2), (key1311, 1), (key1315, 1), (key1315, -1), (key1336, -1), (key1324, -2), (key1324, 1), (key1343, 1), (key1386, 1), (key1390, 1), (key1390, -2), (key1541, -1), (key1545, -1), (key1545, 1), (key1771, 1), (key1554, 2), (key1554, -1), (key1778, -1), (key1419, -1), (key1423, -1), (key1423, 1), (key1454, 1), (key1568, 1), (key1572, 1), (key1572, -1), (key1787, -1), (key1622, -1), (key1657, -1), (key1622, 1), (key1815, 1), (key1442, 2), (key1442, -1), (key1464, -1), (key1591, -2), (key1591, 1), (key1796, 1), (key1631, 1), (key1665, 1), (key1631, -1), (key1823, -1)]

theorem rawRowCheck420 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form0 = rawRow420 := by decide +kernel

def row420 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck420 : row420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow420 := by decide +kernel

theorem rowEval420 (x : Key → ℝ) : Integer.Sparse.eval row420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck420, Integer.Sparse.eval_collectBalanced, rawRowCheck420]

def rawRow421 : Integer.Sparse Key := [(key1295, -1), (key1291, -1), (key1295, 2), (key1315, 1), (key1311, 1), (key1336, -1), (key1315, -1), (key1324, -2), (key1343, 1), (key1324, 1), (key1390, 1), (key1386, 1), (key1390, -2), (key1545, -1), (key1541, -1), (key1771, 1), (key1545, 1), (key1554, 2), (key1778, -1), (key1554, -1), (key1423, -1), (key1419, -1), (key1454, 1), (key1423, 1), (key1572, 1), (key1568, 1), (key1787, -1), (key1572, -1), (key1657, -1), (key1622, -1), (key1815, 1), (key1622, 1), (key1442, 2), (key1464, -1), (key1442, -1), (key1591, -2), (key1796, 1), (key1591, 1), (key1665, 1), (key1631, 1), (key1823, -1), (key1631, -1)]

theorem rawRowCheck421 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form0 = rawRow421 := by decide +kernel

def row421 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck421 : row421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow421 := by decide +kernel

theorem rowEval421 (x : Key → ℝ) : Integer.Sparse.eval row421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck421, Integer.Sparse.eval_collectBalanced, rawRowCheck421]

def rawRow422 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1291, 2), (key1336, 1), (key1336, 1), (key1311, -1), (key1311, -1), (key1343, -2), (key1324, 1), (key1324, 1), (key1390, 1), (key1390, 1), (key1386, -2), (key1771, -1), (key1771, -1), (key1541, 1), (key1541, 1), (key1778, 2), (key1554, -1), (key1554, -1), (key1454, -1), (key1454, -1), (key1419, 1), (key1419, 1), (key1787, 1), (key1787, 1), (key1568, -1), (key1568, -1), (key1815, -1), (key1815, -1), (key1657, 1), (key1657, 1), (key1464, 2), (key1442, -1), (key1442, -1), (key1796, -2), (key1591, 1), (key1591, 1), (key1823, 1), (key1823, 1), (key1665, -1), (key1665, -1)]

theorem rawRowCheck422 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form0 = rawRow422 := by decide +kernel

def row422 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck422 : row422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow422 := by decide +kernel

theorem rowEval422 (x : Key → ℝ) : Integer.Sparse.eval row422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck422, Integer.Sparse.eval_collectBalanced, rawRowCheck422]

def rawRow423 : Integer.Sparse Key := [(key1311, -1), (key1315, -1), (key1324, 2), (key1291, 1), (key1295, 1), (key1324, -1), (key1343, -1), (key1295, -2), (key1315, 1), (key1336, 1), (key1541, 1), (key1545, 1), (key1554, -2), (key1386, -1), (key1390, -1), (key1554, 1), (key1778, 1), (key1390, 2), (key1545, -1), (key1771, -1), (key1568, -1), (key1572, -1), (key1622, 1), (key1657, 1), (key1419, 1), (key1423, 1), (key1622, -1), (key1815, -1), (key1423, -1), (key1454, -1), (key1572, 1), (key1787, 1), (key1591, 2), (key1631, -1), (key1665, -1), (key1442, -2), (key1631, 1), (key1823, 1), (key1442, 1), (key1464, 1), (key1591, -1), (key1796, -1)]

theorem rawRowCheck423 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form0 = rawRow423 := by decide +kernel

def row423 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck423 : row423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow423 := by decide +kernel

theorem rowEval423 (x : Key → ℝ) : Integer.Sparse.eval row423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck423, Integer.Sparse.eval_collectBalanced, rawRowCheck423]

def rawRow424 : Integer.Sparse Key := [(key1315, -1), (key1311, -1), (key1324, 2), (key1295, 1), (key1291, 1), (key1343, -1), (key1324, -1), (key1295, -2), (key1336, 1), (key1315, 1), (key1545, 1), (key1541, 1), (key1554, -2), (key1390, -1), (key1386, -1), (key1778, 1), (key1554, 1), (key1390, 2), (key1771, -1), (key1545, -1), (key1572, -1), (key1568, -1), (key1657, 1), (key1622, 1), (key1423, 1), (key1419, 1), (key1815, -1), (key1622, -1), (key1454, -1), (key1423, -1), (key1787, 1), (key1572, 1), (key1591, 2), (key1665, -1), (key1631, -1), (key1442, -2), (key1823, 1), (key1631, 1), (key1464, 1), (key1442, 1), (key1796, -1), (key1591, -1)]

theorem rawRowCheck424 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form0 = rawRow424 := by decide +kernel

def row424 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck424 : row424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow424 := by decide +kernel

theorem rowEval424 (x : Key → ℝ) : Integer.Sparse.eval row424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck424, Integer.Sparse.eval_collectBalanced, rawRowCheck424]

def rawRow425 : Integer.Sparse Key := [(key1315, -1), (key1324, -1), (key1311, 2), (key1336, 1), (key1343, 1), (key1291, -1), (key1311, -1), (key1336, -2), (key1295, 1), (key1315, 1), (key1545, 1), (key1554, 1), (key1541, -2), (key1771, -1), (key1778, -1), (key1386, 1), (key1541, 1), (key1771, 2), (key1390, -1), (key1545, -1), (key1654, -1), (key1657, -1), (key1568, 1), (key1617, 1), (key1812, 1), (key1815, 1), (key1419, -1), (key1617, -1), (key1787, -1), (key1812, -1), (key1454, 1), (key1654, 1), (key1665, 2), (key1591, -1), (key1631, -1), (key1823, -2), (key1442, 1), (key1631, 1), (key1796, 1), (key1823, 1), (key1464, -1), (key1665, -1)]

theorem rawRowCheck425 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form0 = rawRow425 := by decide +kernel

def row425 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck425 : row425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow425 := by decide +kernel

theorem rowEval425 (x : Key → ℝ) : Integer.Sparse.eval row425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck425, Integer.Sparse.eval_collectBalanced, rawRowCheck425]

def rawRow426 : Integer.Sparse Key := [(key1324, -1), (key1315, -1), (key1311, 2), (key1343, 1), (key1336, 1), (key1311, -1), (key1291, -1), (key1336, -2), (key1315, 1), (key1295, 1), (key1554, 1), (key1545, 1), (key1541, -2), (key1778, -1), (key1771, -1), (key1541, 1), (key1386, 1), (key1771, 2), (key1545, -1), (key1390, -1), (key1657, -1), (key1654, -1), (key1617, 1), (key1568, 1), (key1815, 1), (key1812, 1), (key1617, -1), (key1419, -1), (key1812, -1), (key1787, -1), (key1654, 1), (key1454, 1), (key1665, 2), (key1631, -1), (key1591, -1), (key1823, -2), (key1631, 1), (key1442, 1), (key1823, 1), (key1796, 1), (key1665, -1), (key1464, -1)]

theorem rawRowCheck426 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form0 = rawRow426 := by decide +kernel

def row426 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck426 : row426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow426 := by decide +kernel

theorem rowEval426 (x : Key → ℝ) : Integer.Sparse.eval row426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck426, Integer.Sparse.eval_collectBalanced, rawRowCheck426]

def rawRow427 : Integer.Sparse Key := [(key1336, -1), (key1336, -1), (key1343, 2), (key1295, 1), (key1295, 1), (key1324, -1), (key1324, -1), (key1291, -2), (key1311, 1), (key1311, 1), (key1771, 1), (key1771, 1), (key1778, -2), (key1390, -1), (key1390, -1), (key1554, 1), (key1554, 1), (key1386, 2), (key1541, -1), (key1541, -1), (key1787, -1), (key1787, -1), (key1815, 1), (key1815, 1), (key1454, 1), (key1454, 1), (key1657, -1), (key1657, -1), (key1419, -1), (key1419, -1), (key1568, 1), (key1568, 1), (key1796, 2), (key1823, -1), (key1823, -1), (key1464, -2), (key1665, 1), (key1665, 1), (key1442, 1), (key1442, 1), (key1591, -1), (key1591, -1)]

theorem rawRowCheck427 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form0 = rawRow427 := by decide +kernel

def row427 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

theorem rowCheck427 : row427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow427 := by decide +kernel

theorem rowEval427 (x : Key → ℝ) : Integer.Sparse.eval row427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck427, Integer.Sparse.eval_collectBalanced, rawRowCheck427]

def rawRow428 : Integer.Sparse Key := [(key1336, -1), (key1343, -1), (key1336, 2), (key1315, 1), (key1324, 1), (key1295, -1), (key1315, -1), (key1311, -2), (key1291, 1), (key1311, 1), (key1771, 1), (key1778, 1), (key1771, -2), (key1545, -1), (key1554, -1), (key1390, 1), (key1545, 1), (key1541, 2), (key1386, -1), (key1541, -1), (key1812, -1), (key1815, -1), (key1787, 1), (key1812, 1), (key1654, 1), (key1657, 1), (key1454, -1), (key1654, -1), (key1568, -1), (key1617, -1), (key1419, 1), (key1617, 1), (key1823, 2), (key1796, -1), (key1823, -1), (key1665, -2), (key1464, 1), (key1665, 1), (key1591, 1), (key1631, 1), (key1442, -1), (key1631, -1)]

theorem rawRowCheck428 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form0 = rawRow428 := by decide +kernel

def row428 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck428 : row428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow428 := by decide +kernel

theorem rowEval428 (x : Key → ℝ) : Integer.Sparse.eval row428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck428, Integer.Sparse.eval_collectBalanced, rawRowCheck428]

def rawRow429 : Integer.Sparse Key := [(key1343, -1), (key1336, -1), (key1336, 2), (key1324, 1), (key1315, 1), (key1315, -1), (key1295, -1), (key1311, -2), (key1311, 1), (key1291, 1), (key1778, 1), (key1771, 1), (key1771, -2), (key1554, -1), (key1545, -1), (key1545, 1), (key1390, 1), (key1541, 2), (key1541, -1), (key1386, -1), (key1815, -1), (key1812, -1), (key1812, 1), (key1787, 1), (key1657, 1), (key1654, 1), (key1654, -1), (key1454, -1), (key1617, -1), (key1568, -1), (key1617, 1), (key1419, 1), (key1823, 2), (key1823, -1), (key1796, -1), (key1665, -2), (key1665, 1), (key1464, 1), (key1631, 1), (key1591, 1), (key1631, -1), (key1442, -1)]

theorem rawRowCheck429 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form0 = rawRow429 := by decide +kernel

def row429 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck429 : row429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow429 := by decide +kernel

theorem rowEval429 (x : Key → ℝ) : Integer.Sparse.eval row429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck429, Integer.Sparse.eval_collectBalanced, rawRowCheck429]

def rawRow430 : Integer.Sparse Key := [(key1386, -1), (key1390, -1), (key1390, 2), (key1419, 1), (key1423, 1), (key1423, -1), (key1454, -1), (key1442, -2), (key1442, 1), (key1464, 1), (key1291, 1), (key1295, 1), (key1295, -2), (key1568, -1), (key1572, -1), (key1572, 1), (key1787, 1), (key1591, 2), (key1591, -1), (key1796, -1), (key1311, -1), (key1315, -1), (key1315, 1), (key1336, 1), (key1541, 1), (key1545, 1), (key1545, -1), (key1771, -1), (key1631, -1), (key1665, -1), (key1631, 1), (key1823, 1), (key1324, 2), (key1324, -1), (key1343, -1), (key1554, -2), (key1554, 1), (key1778, 1), (key1622, 1), (key1657, 1), (key1622, -1), (key1815, -1)]

theorem rawRowCheck430 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form0 = rawRow430 := by decide +kernel

def row430 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck430 : row430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow430 := by decide +kernel

theorem rowEval430 (x : Key → ℝ) : Integer.Sparse.eval row430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck430, Integer.Sparse.eval_collectBalanced, rawRowCheck430]

def rawRow431 : Integer.Sparse Key := [(key1390, -1), (key1386, -1), (key1390, 2), (key1423, 1), (key1419, 1), (key1454, -1), (key1423, -1), (key1442, -2), (key1464, 1), (key1442, 1), (key1295, 1), (key1291, 1), (key1295, -2), (key1572, -1), (key1568, -1), (key1787, 1), (key1572, 1), (key1591, 2), (key1796, -1), (key1591, -1), (key1315, -1), (key1311, -1), (key1336, 1), (key1315, 1), (key1545, 1), (key1541, 1), (key1771, -1), (key1545, -1), (key1665, -1), (key1631, -1), (key1823, 1), (key1631, 1), (key1324, 2), (key1343, -1), (key1324, -1), (key1554, -2), (key1778, 1), (key1554, 1), (key1657, 1), (key1622, 1), (key1815, -1), (key1622, -1)]

theorem rawRowCheck431 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form0 = rawRow431 := by decide +kernel

def row431 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck431 : row431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow431 := by decide +kernel

theorem rowEval431 (x : Key → ℝ) : Integer.Sparse.eval row431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck431, Integer.Sparse.eval_collectBalanced, rawRowCheck431]

def rawRow432 : Integer.Sparse Key := [(key1390, -1), (key1390, -1), (key1386, 2), (key1454, 1), (key1454, 1), (key1419, -1), (key1419, -1), (key1464, -2), (key1442, 1), (key1442, 1), (key1295, 1), (key1295, 1), (key1291, -2), (key1787, -1), (key1787, -1), (key1568, 1), (key1568, 1), (key1796, 2), (key1591, -1), (key1591, -1), (key1336, -1), (key1336, -1), (key1311, 1), (key1311, 1), (key1771, 1), (key1771, 1), (key1541, -1), (key1541, -1), (key1823, -1), (key1823, -1), (key1665, 1), (key1665, 1), (key1343, 2), (key1324, -1), (key1324, -1), (key1778, -2), (key1554, 1), (key1554, 1), (key1815, 1), (key1815, 1), (key1657, -1), (key1657, -1)]

theorem rawRowCheck432 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form0 = rawRow432 := by decide +kernel

def row432 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1386, 2), (key1390, -2), (key1419, -2), (key1442, 2), (key1454, 2), (key1464, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

theorem rowCheck432 : row432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow432 := by decide +kernel

theorem rowEval432 (x : Key → ℝ) : Integer.Sparse.eval row432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck432, Integer.Sparse.eval_collectBalanced, rawRowCheck432]

def rawRow433 : Integer.Sparse Key := [(key1419, -1), (key1423, -1), (key1442, 2), (key1386, 1), (key1390, 1), (key1442, -1), (key1464, -1), (key1390, -2), (key1423, 1), (key1454, 1), (key1568, 1), (key1572, 1), (key1591, -2), (key1291, -1), (key1295, -1), (key1591, 1), (key1796, 1), (key1295, 2), (key1572, -1), (key1787, -1), (key1541, -1), (key1545, -1), (key1631, 1), (key1665, 1), (key1311, 1), (key1315, 1), (key1631, -1), (key1823, -1), (key1315, -1), (key1336, -1), (key1545, 1), (key1771, 1), (key1554, 2), (key1622, -1), (key1657, -1), (key1324, -2), (key1622, 1), (key1815, 1), (key1324, 1), (key1343, 1), (key1554, -1), (key1778, -1)]

theorem rawRowCheck433 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form0 = rawRow433 := by decide +kernel

def row433 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck433 : row433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow433 := by decide +kernel

theorem rowEval433 (x : Key → ℝ) : Integer.Sparse.eval row433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck433, Integer.Sparse.eval_collectBalanced, rawRowCheck433]

def rawRow434 : Integer.Sparse Key := [(key1423, -1), (key1419, -1), (key1442, 2), (key1390, 1), (key1386, 1), (key1464, -1), (key1442, -1), (key1390, -2), (key1454, 1), (key1423, 1), (key1572, 1), (key1568, 1), (key1591, -2), (key1295, -1), (key1291, -1), (key1796, 1), (key1591, 1), (key1295, 2), (key1787, -1), (key1572, -1), (key1545, -1), (key1541, -1), (key1665, 1), (key1631, 1), (key1315, 1), (key1311, 1), (key1823, -1), (key1631, -1), (key1336, -1), (key1315, -1), (key1771, 1), (key1545, 1), (key1554, 2), (key1657, -1), (key1622, -1), (key1324, -2), (key1815, 1), (key1622, 1), (key1343, 1), (key1324, 1), (key1778, -1), (key1554, -1)]

theorem rawRowCheck434 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form0 = rawRow434 := by decide +kernel

def row434 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck434 : row434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow434 := by decide +kernel

theorem rowEval434 (x : Key → ℝ) : Integer.Sparse.eval row434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck434, Integer.Sparse.eval_collectBalanced, rawRowCheck434]

def rawRow435 : Integer.Sparse Key := [(key1423, -1), (key1442, -1), (key1419, 2), (key1454, 1), (key1464, 1), (key1386, -1), (key1419, -1), (key1454, -2), (key1390, 1), (key1423, 1), (key1572, 1), (key1591, 1), (key1568, -2), (key1787, -1), (key1796, -1), (key1291, 1), (key1568, 1), (key1787, 2), (key1295, -1), (key1572, -1), (key1654, -1), (key1665, -1), (key1541, 1), (key1617, 1), (key1812, 1), (key1823, 1), (key1311, -1), (key1617, -1), (key1771, -1), (key1812, -1), (key1336, 1), (key1654, 1), (key1657, 2), (key1554, -1), (key1622, -1), (key1815, -2), (key1324, 1), (key1622, 1), (key1778, 1), (key1815, 1), (key1343, -1), (key1657, -1)]

theorem rawRowCheck435 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form0 = rawRow435 := by decide +kernel

def row435 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck435 : row435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow435 := by decide +kernel

theorem rowEval435 (x : Key → ℝ) : Integer.Sparse.eval row435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck435, Integer.Sparse.eval_collectBalanced, rawRowCheck435]

def rawRow436 : Integer.Sparse Key := [(key1442, -1), (key1423, -1), (key1419, 2), (key1464, 1), (key1454, 1), (key1419, -1), (key1386, -1), (key1454, -2), (key1423, 1), (key1390, 1), (key1591, 1), (key1572, 1), (key1568, -2), (key1796, -1), (key1787, -1), (key1568, 1), (key1291, 1), (key1787, 2), (key1572, -1), (key1295, -1), (key1665, -1), (key1654, -1), (key1617, 1), (key1541, 1), (key1823, 1), (key1812, 1), (key1617, -1), (key1311, -1), (key1812, -1), (key1771, -1), (key1654, 1), (key1336, 1), (key1657, 2), (key1622, -1), (key1554, -1), (key1815, -2), (key1622, 1), (key1324, 1), (key1815, 1), (key1778, 1), (key1657, -1), (key1343, -1)]

theorem rawRowCheck436 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form0 = rawRow436 := by decide +kernel

def row436 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck436 : row436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow436 := by decide +kernel

theorem rowEval436 (x : Key → ℝ) : Integer.Sparse.eval row436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck436, Integer.Sparse.eval_collectBalanced, rawRowCheck436]

def rawRow437 : Integer.Sparse Key := [(key1454, -1), (key1454, -1), (key1464, 2), (key1390, 1), (key1390, 1), (key1442, -1), (key1442, -1), (key1386, -2), (key1419, 1), (key1419, 1), (key1787, 1), (key1787, 1), (key1796, -2), (key1295, -1), (key1295, -1), (key1591, 1), (key1591, 1), (key1291, 2), (key1568, -1), (key1568, -1), (key1771, -1), (key1771, -1), (key1823, 1), (key1823, 1), (key1336, 1), (key1336, 1), (key1665, -1), (key1665, -1), (key1311, -1), (key1311, -1), (key1541, 1), (key1541, 1), (key1778, 2), (key1815, -1), (key1815, -1), (key1343, -2), (key1657, 1), (key1657, 1), (key1324, 1), (key1324, 1), (key1554, -1), (key1554, -1)]

theorem rawRowCheck437 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form0 = rawRow437 := by decide +kernel

def row437 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1386, -2), (key1390, 2), (key1419, 2), (key1442, -2), (key1454, -2), (key1464, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

theorem rowCheck437 : row437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow437 := by decide +kernel

theorem rowEval437 (x : Key → ℝ) : Integer.Sparse.eval row437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck437, Integer.Sparse.eval_collectBalanced, rawRowCheck437]

def rawRow438 : Integer.Sparse Key := [(key1454, -1), (key1464, -1), (key1454, 2), (key1423, 1), (key1442, 1), (key1390, -1), (key1423, -1), (key1419, -2), (key1386, 1), (key1419, 1), (key1787, 1), (key1796, 1), (key1787, -2), (key1572, -1), (key1591, -1), (key1295, 1), (key1572, 1), (key1568, 2), (key1291, -1), (key1568, -1), (key1812, -1), (key1823, -1), (key1771, 1), (key1812, 1), (key1654, 1), (key1665, 1), (key1336, -1), (key1654, -1), (key1541, -1), (key1617, -1), (key1311, 1), (key1617, 1), (key1815, 2), (key1778, -1), (key1815, -1), (key1657, -2), (key1343, 1), (key1657, 1), (key1554, 1), (key1622, 1), (key1324, -1), (key1622, -1)]

theorem rawRowCheck438 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form0 = rawRow438 := by decide +kernel

def row438 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck438 : row438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow438 := by decide +kernel

theorem rowEval438 (x : Key → ℝ) : Integer.Sparse.eval row438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck438, Integer.Sparse.eval_collectBalanced, rawRowCheck438]

def rawRow439 : Integer.Sparse Key := [(key1464, -1), (key1454, -1), (key1454, 2), (key1442, 1), (key1423, 1), (key1423, -1), (key1390, -1), (key1419, -2), (key1419, 1), (key1386, 1), (key1796, 1), (key1787, 1), (key1787, -2), (key1591, -1), (key1572, -1), (key1572, 1), (key1295, 1), (key1568, 2), (key1568, -1), (key1291, -1), (key1823, -1), (key1812, -1), (key1812, 1), (key1771, 1), (key1665, 1), (key1654, 1), (key1654, -1), (key1336, -1), (key1617, -1), (key1541, -1), (key1617, 1), (key1311, 1), (key1815, 2), (key1815, -1), (key1778, -1), (key1657, -2), (key1657, 1), (key1343, 1), (key1622, 1), (key1554, 1), (key1622, -1), (key1324, -1)]

theorem rawRowCheck439 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form0 = rawRow439 := by decide +kernel

def row439 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck439 : row439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow439 := by decide +kernel

theorem rowEval439 (x : Key → ℝ) : Integer.Sparse.eval row439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck439, Integer.Sparse.eval_collectBalanced, rawRowCheck439]

def rawRow440 : Integer.Sparse Key := [(key1541, -1), (key1545, -1), (key1554, 2), (key1568, 1), (key1572, 1), (key1622, -1), (key1657, -1), (key1591, -2), (key1631, 1), (key1665, 1), (key1311, 1), (key1315, 1), (key1324, -2), (key1419, -1), (key1423, -1), (key1622, 1), (key1815, 1), (key1442, 2), (key1631, -1), (key1823, -1), (key1291, -1), (key1295, -1), (key1324, 1), (key1343, 1), (key1386, 1), (key1390, 1), (key1554, -1), (key1778, -1), (key1442, -1), (key1464, -1), (key1591, 1), (key1796, 1), (key1295, 2), (key1315, -1), (key1336, -1), (key1390, -2), (key1545, 1), (key1771, 1), (key1423, 1), (key1454, 1), (key1572, -1), (key1787, -1)]

theorem rawRowCheck440 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form0 = rawRow440 := by decide +kernel

def row440 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck440 : row440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow440 := by decide +kernel

theorem rowEval440 (x : Key → ℝ) : Integer.Sparse.eval row440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck440, Integer.Sparse.eval_collectBalanced, rawRowCheck440]

def rawRow441 : Integer.Sparse Key := [(key1545, -1), (key1541, -1), (key1554, 2), (key1572, 1), (key1568, 1), (key1657, -1), (key1622, -1), (key1591, -2), (key1665, 1), (key1631, 1), (key1315, 1), (key1311, 1), (key1324, -2), (key1423, -1), (key1419, -1), (key1815, 1), (key1622, 1), (key1442, 2), (key1823, -1), (key1631, -1), (key1295, -1), (key1291, -1), (key1343, 1), (key1324, 1), (key1390, 1), (key1386, 1), (key1778, -1), (key1554, -1), (key1464, -1), (key1442, -1), (key1796, 1), (key1591, 1), (key1295, 2), (key1336, -1), (key1315, -1), (key1390, -2), (key1771, 1), (key1545, 1), (key1454, 1), (key1423, 1), (key1787, -1), (key1572, -1)]

theorem rawRowCheck441 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form0 = rawRow441 := by decide +kernel

def row441 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck441 : row441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow441 := by decide +kernel

theorem rowEval441 (x : Key → ℝ) : Integer.Sparse.eval row441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck441, Integer.Sparse.eval_collectBalanced, rawRowCheck441]

def rawRow442 : Integer.Sparse Key := [(key1545, -1), (key1554, -1), (key1541, 2), (key1654, 1), (key1657, 1), (key1568, -1), (key1617, -1), (key1665, -2), (key1591, 1), (key1631, 1), (key1315, 1), (key1324, 1), (key1311, -2), (key1812, -1), (key1815, -1), (key1419, 1), (key1617, 1), (key1823, 2), (key1442, -1), (key1631, -1), (key1336, -1), (key1343, -1), (key1291, 1), (key1311, 1), (key1771, 1), (key1778, 1), (key1386, -1), (key1541, -1), (key1796, -1), (key1823, -1), (key1464, 1), (key1665, 1), (key1336, 2), (key1295, -1), (key1315, -1), (key1771, -2), (key1390, 1), (key1545, 1), (key1787, 1), (key1812, 1), (key1454, -1), (key1654, -1)]

theorem rawRowCheck442 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form0 = rawRow442 := by decide +kernel

def row442 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck442 : row442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow442 := by decide +kernel

theorem rowEval442 (x : Key → ℝ) : Integer.Sparse.eval row442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck442, Integer.Sparse.eval_collectBalanced, rawRowCheck442]

def rawRow443 : Integer.Sparse Key := [(key1554, -1), (key1545, -1), (key1541, 2), (key1657, 1), (key1654, 1), (key1617, -1), (key1568, -1), (key1665, -2), (key1631, 1), (key1591, 1), (key1324, 1), (key1315, 1), (key1311, -2), (key1815, -1), (key1812, -1), (key1617, 1), (key1419, 1), (key1823, 2), (key1631, -1), (key1442, -1), (key1343, -1), (key1336, -1), (key1311, 1), (key1291, 1), (key1778, 1), (key1771, 1), (key1541, -1), (key1386, -1), (key1823, -1), (key1796, -1), (key1665, 1), (key1464, 1), (key1336, 2), (key1315, -1), (key1295, -1), (key1771, -2), (key1545, 1), (key1390, 1), (key1812, 1), (key1787, 1), (key1654, -1), (key1454, -1)]

theorem rawRowCheck443 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form0 = rawRow443 := by decide +kernel

def row443 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck443 : row443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow443 := by decide +kernel

theorem rowEval443 (x : Key → ℝ) : Integer.Sparse.eval row443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck443, Integer.Sparse.eval_collectBalanced, rawRowCheck443]

def rawRow444 : Integer.Sparse Key := [(key1568, -1), (key1572, -1), (key1591, 2), (key1541, 1), (key1545, 1), (key1631, -1), (key1665, -1), (key1554, -2), (key1622, 1), (key1657, 1), (key1419, 1), (key1423, 1), (key1442, -2), (key1311, -1), (key1315, -1), (key1631, 1), (key1823, 1), (key1324, 2), (key1622, -1), (key1815, -1), (key1386, -1), (key1390, -1), (key1442, 1), (key1464, 1), (key1291, 1), (key1295, 1), (key1591, -1), (key1796, -1), (key1324, -1), (key1343, -1), (key1554, 1), (key1778, 1), (key1390, 2), (key1423, -1), (key1454, -1), (key1295, -2), (key1572, 1), (key1787, 1), (key1315, 1), (key1336, 1), (key1545, -1), (key1771, -1)]

theorem rawRowCheck444 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form0 = rawRow444 := by decide +kernel

def row444 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck444 : row444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow444 := by decide +kernel

theorem rowEval444 (x : Key → ℝ) : Integer.Sparse.eval row444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck444, Integer.Sparse.eval_collectBalanced, rawRowCheck444]

def rawRow445 : Integer.Sparse Key := [(key1572, -1), (key1568, -1), (key1591, 2), (key1545, 1), (key1541, 1), (key1665, -1), (key1631, -1), (key1554, -2), (key1657, 1), (key1622, 1), (key1423, 1), (key1419, 1), (key1442, -2), (key1315, -1), (key1311, -1), (key1823, 1), (key1631, 1), (key1324, 2), (key1815, -1), (key1622, -1), (key1390, -1), (key1386, -1), (key1464, 1), (key1442, 1), (key1295, 1), (key1291, 1), (key1796, -1), (key1591, -1), (key1343, -1), (key1324, -1), (key1778, 1), (key1554, 1), (key1390, 2), (key1454, -1), (key1423, -1), (key1295, -2), (key1787, 1), (key1572, 1), (key1336, 1), (key1315, 1), (key1771, -1), (key1545, -1)]

theorem rawRowCheck445 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form0 = rawRow445 := by decide +kernel

def row445 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, 1), (key1554, -1), (key1568, -1), (key1591, 1), (key1657, 1), (key1665, -1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck445 : row445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow445 := by decide +kernel

theorem rowEval445 (x : Key → ℝ) : Integer.Sparse.eval row445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck445, Integer.Sparse.eval_collectBalanced, rawRowCheck445]

def rawRow446 : Integer.Sparse Key := [(key1572, -1), (key1591, -1), (key1568, 2), (key1654, 1), (key1665, 1), (key1541, -1), (key1617, -1), (key1657, -2), (key1554, 1), (key1622, 1), (key1423, 1), (key1442, 1), (key1419, -2), (key1812, -1), (key1823, -1), (key1311, 1), (key1617, 1), (key1815, 2), (key1324, -1), (key1622, -1), (key1454, -1), (key1464, -1), (key1386, 1), (key1419, 1), (key1787, 1), (key1796, 1), (key1291, -1), (key1568, -1), (key1778, -1), (key1815, -1), (key1343, 1), (key1657, 1), (key1454, 2), (key1390, -1), (key1423, -1), (key1787, -2), (key1295, 1), (key1572, 1), (key1771, 1), (key1812, 1), (key1336, -1), (key1654, -1)]

theorem rawRowCheck446 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form0 = rawRow446 := by decide +kernel

def row446 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck446 : row446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow446 := by decide +kernel

theorem rowEval446 (x : Key → ℝ) : Integer.Sparse.eval row446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form0) x := by
  rw [rowCheck446, Integer.Sparse.eval_collectBalanced, rawRowCheck446]

def rawRow447 : Integer.Sparse Key := [(key1591, -1), (key1572, -1), (key1568, 2), (key1665, 1), (key1654, 1), (key1617, -1), (key1541, -1), (key1657, -2), (key1622, 1), (key1554, 1), (key1442, 1), (key1423, 1), (key1419, -2), (key1823, -1), (key1812, -1), (key1617, 1), (key1311, 1), (key1815, 2), (key1622, -1), (key1324, -1), (key1464, -1), (key1454, -1), (key1419, 1), (key1386, 1), (key1796, 1), (key1787, 1), (key1568, -1), (key1291, -1), (key1815, -1), (key1778, -1), (key1657, 1), (key1343, 1), (key1454, 2), (key1423, -1), (key1390, -1), (key1787, -2), (key1572, 1), (key1295, 1), (key1812, 1), (key1771, 1), (key1654, -1), (key1336, -1)]

theorem rawRowCheck447 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form0 = rawRow447 := by decide +kernel

def row447 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, -1), (key1554, 1), (key1568, 1), (key1591, -1), (key1657, -1), (key1665, 1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck447 : row447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow447 := by decide +kernel

theorem rowEval447 (x : Key → ℝ) : Integer.Sparse.eval row447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck447, Integer.Sparse.eval_collectBalanced, rawRowCheck447]

end MUB6.Certificate.GramRows

end OAI
