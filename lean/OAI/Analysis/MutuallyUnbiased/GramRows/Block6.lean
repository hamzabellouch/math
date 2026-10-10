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

def rawRow288 : Integer.Sparse Key := [(key422, -1), (key586, -1), (key423, 2), (key454, 1), (key604, 1), (key333, -1), (key462, -1), (key478, -2), (key343, 1), (key484, 1), (key401, 1), (key575, 1), (key402, -2), (key446, -1), (key598, -1), (key265, 1), (key462, 1), (key472, 2), (key274, -1), (key484, -1), (key391, -1), (key570, -1), (key310, 1), (key402, 1), (key412, 1), (key580, 1), (key244, -1), (key423, -1), (key337, -1), (key472, -1), (key269, 1), (key478, 1), (key391, 2), (key308, -1), (key401, -1), (key412, -2), (key242, 1), (key422, 1), (key322, 1), (key446, 1), (key254, -1), (key454, -1)]

theorem rawRowCheck288 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form0 = rawRow288 := by decide +kernel

def row288 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck288 : row288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow288 := by decide +kernel

theorem rowEval288 (x : Key → ℝ) : Integer.Sparse.eval row288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck288, Integer.Sparse.eval_collectBalanced, rawRowCheck288]

def rawRow289 : Integer.Sparse Key := [(key586, -1), (key422, -1), (key423, 2), (key604, 1), (key454, 1), (key462, -1), (key333, -1), (key478, -2), (key484, 1), (key343, 1), (key575, 1), (key401, 1), (key402, -2), (key598, -1), (key446, -1), (key462, 1), (key265, 1), (key472, 2), (key484, -1), (key274, -1), (key570, -1), (key391, -1), (key402, 1), (key310, 1), (key580, 1), (key412, 1), (key423, -1), (key244, -1), (key472, -1), (key337, -1), (key478, 1), (key269, 1), (key391, 2), (key401, -1), (key308, -1), (key412, -2), (key422, 1), (key242, 1), (key446, 1), (key322, 1), (key454, -1), (key254, -1)]

theorem rawRowCheck289 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form0 = rawRow289 := by decide +kernel

def row289 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck289 : row289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow289 := by decide +kernel

theorem rowEval289 (x : Key → ℝ) : Integer.Sparse.eval row289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck289, Integer.Sparse.eval_collectBalanced, rawRowCheck289]

def rawRow290 : Integer.Sparse Key := [(key454, -1), (key478, -1), (key604, 2), (key332, 1), (key343, 1), (key586, -1), (key610, -1), (key333, -2), (key423, 1), (key462, 1), (key446, 1), (key472, 1), (key598, -2), (key264, -1), (key274, -1), (key575, 1), (key610, 1), (key265, 2), (key402, -1), (key462, -1), (key322, -1), (key337, -1), (key580, 1), (key598, 1), (key254, 1), (key269, 1), (key570, -1), (key604, -1), (key244, -1), (key265, -1), (key310, 1), (key333, 1), (key322, 2), (key412, -1), (key446, -1), (key254, -2), (key391, 1), (key454, 1), (key242, 1), (key264, 1), (key308, -1), (key332, -1)]

theorem rawRowCheck290 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form0 = rawRow290 := by decide +kernel

def row290 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck290 : row290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow290 := by decide +kernel

theorem rowEval290 (x : Key → ℝ) : Integer.Sparse.eval row290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck290, Integer.Sparse.eval_collectBalanced, rawRowCheck290]

def rawRow291 : Integer.Sparse Key := [(key478, -1), (key454, -1), (key604, 2), (key343, 1), (key332, 1), (key610, -1), (key586, -1), (key333, -2), (key462, 1), (key423, 1), (key472, 1), (key446, 1), (key598, -2), (key274, -1), (key264, -1), (key610, 1), (key575, 1), (key265, 2), (key462, -1), (key402, -1), (key337, -1), (key322, -1), (key598, 1), (key580, 1), (key269, 1), (key254, 1), (key604, -1), (key570, -1), (key265, -1), (key244, -1), (key333, 1), (key310, 1), (key322, 2), (key446, -1), (key412, -1), (key254, -2), (key454, 1), (key391, 1), (key264, 1), (key242, 1), (key332, -1), (key308, -1)]

theorem rawRowCheck291 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form0 = rawRow291 := by decide +kernel

def row291 : Integer.Sparse Key := [(key242, 1), (key244, -1), (key254, -1), (key265, 1), (key269, 1), (key274, -1), (key308, -1), (key310, 1), (key322, 1), (key333, -1), (key337, -1), (key343, 1), (key391, 1), (key402, -1), (key412, -1), (key423, 1), (key472, 1), (key478, -1), (key570, -1), (key575, 1), (key580, 1), (key586, -1), (key598, -1), (key604, 1)]

theorem rowCheck291 : row291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow291 := by decide +kernel

theorem rowEval291 (x : Key → ℝ) : Integer.Sparse.eval row291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form0) x := by
  rw [rowCheck291, Integer.Sparse.eval_collectBalanced, rawRowCheck291]

def rawRow292 : Integer.Sparse Key := [(key454, -1), (key604, -1), (key478, 2), (key422, 1), (key586, 1), (key343, -1), (key484, -1), (key423, -2), (key333, 1), (key462, 1), (key446, 1), (key598, 1), (key472, -2), (key401, -1), (key575, -1), (key274, 1), (key484, 1), (key402, 2), (key265, -1), (key462, -1), (key412, -1), (key580, -1), (key337, 1), (key472, 1), (key391, 1), (key570, 1), (key269, -1), (key478, -1), (key310, -1), (key402, -1), (key244, 1), (key423, 1), (key412, 2), (key322, -1), (key446, -1), (key391, -2), (key254, 1), (key454, 1), (key308, 1), (key401, 1), (key242, -1), (key422, -1)]

theorem rawRowCheck292 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form0 = rawRow292 := by decide +kernel

def row292 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck292 : row292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow292 := by decide +kernel

theorem rowEval292 (x : Key → ℝ) : Integer.Sparse.eval row292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form0) x := by
  rw [rowCheck292, Integer.Sparse.eval_collectBalanced, rawRowCheck292]

def rawRow293 : Integer.Sparse Key := [(key604, -1), (key454, -1), (key478, 2), (key586, 1), (key422, 1), (key484, -1), (key343, -1), (key423, -2), (key462, 1), (key333, 1), (key598, 1), (key446, 1), (key472, -2), (key575, -1), (key401, -1), (key484, 1), (key274, 1), (key402, 2), (key462, -1), (key265, -1), (key580, -1), (key412, -1), (key472, 1), (key337, 1), (key570, 1), (key391, 1), (key478, -1), (key269, -1), (key402, -1), (key310, -1), (key423, 1), (key244, 1), (key412, 2), (key446, -1), (key322, -1), (key391, -2), (key454, 1), (key254, 1), (key401, 1), (key308, 1), (key422, -1), (key242, -1)]

theorem rawRowCheck293 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form0 = rawRow293 := by decide +kernel

def row293 : Integer.Sparse Key := [(key242, -1), (key244, 1), (key254, 1), (key265, -1), (key269, -1), (key274, 1), (key308, 1), (key310, -1), (key322, -1), (key333, 1), (key337, 1), (key343, -1), (key391, -1), (key402, 1), (key412, 1), (key423, -1), (key472, -1), (key478, 1), (key570, 1), (key575, -1), (key580, -1), (key586, 1), (key598, 1), (key604, -1)]

theorem rowCheck293 : row293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow293 := by decide +kernel

theorem rowEval293 (x : Key → ℝ) : Integer.Sparse.eval row293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form0) x := by
  rw [rowCheck293, Integer.Sparse.eval_collectBalanced, rawRowCheck293]

def rawRow294 : Integer.Sparse Key := [(key1301, -2), (key1305, 1), (key1305, 1), (key1321, 2), (key1332, -1), (key1332, -1), (key1342, -1), (key1342, -1), (key1348, 1), (key1348, 1), (key1396, 2), (key1400, -1), (key1400, -1), (key1429, -2), (key1450, 1), (key1450, 1), (key1460, 1), (key1460, 1), (key1469, -1), (key1469, -1), (key1551, -2), (key1562, 1), (key1562, 1), (key1578, 2), (key1599, -1), (key1599, -1), (key1662, -1), (key1662, -1), (key1670, 1), (key1670, 1), (key1777, 1), (key1777, 1), (key1783, -1), (key1783, -1), (key1793, -1), (key1793, -1), (key1801, 1), (key1801, 1), (key1820, 1), (key1820, 1), (key1828, -1), (key1828, -1)]

theorem rawRowCheck294 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1 = rawRow294 := by decide +kernel

def row294 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

theorem rowCheck294 : row294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow294 := by decide +kernel

theorem rowEval294 (x : Key → ℝ) : Integer.Sparse.eval row294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck294, Integer.Sparse.eval_collectBalanced, rawRowCheck294]

def rawRow295 : Integer.Sparse Key := [(key1305, -2), (key1301, 1), (key1305, 1), (key1332, 2), (key1321, -1), (key1332, -1), (key1348, -1), (key1349, -1), (key1342, 1), (key1349, 1), (key1400, 2), (key1396, -1), (key1400, -1), (key1450, -2), (key1429, 1), (key1450, 1), (key1469, 1), (key1470, 1), (key1460, -1), (key1470, -1), (key1562, -2), (key1551, 1), (key1562, 1), (key1599, 2), (key1578, -1), (key1599, -1), (key1670, -1), (key1676, -1), (key1662, 1), (key1676, 1), (key1783, 1), (key1784, 1), (key1777, -1), (key1784, -1), (key1801, -1), (key1802, -1), (key1793, 1), (key1802, 1), (key1828, 1), (key1834, 1), (key1820, -1), (key1834, -1)]

theorem rawRowCheck295 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1 = rawRow295 := by decide +kernel

def row295 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck295 : row295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow295 := by decide +kernel

theorem rowEval295 (x : Key → ℝ) : Integer.Sparse.eval row295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck295, Integer.Sparse.eval_collectBalanced, rawRowCheck295]

def rawRow296 : Integer.Sparse Key := [(key1305, -2), (key1305, 1), (key1301, 1), (key1332, 2), (key1332, -1), (key1321, -1), (key1349, -1), (key1348, -1), (key1349, 1), (key1342, 1), (key1400, 2), (key1400, -1), (key1396, -1), (key1450, -2), (key1450, 1), (key1429, 1), (key1470, 1), (key1469, 1), (key1470, -1), (key1460, -1), (key1562, -2), (key1562, 1), (key1551, 1), (key1599, 2), (key1599, -1), (key1578, -1), (key1676, -1), (key1670, -1), (key1676, 1), (key1662, 1), (key1784, 1), (key1783, 1), (key1784, -1), (key1777, -1), (key1802, -1), (key1801, -1), (key1802, 1), (key1793, 1), (key1834, 1), (key1828, 1), (key1834, -1), (key1820, -1)]

theorem rawRowCheck296 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1 = rawRow296 := by decide +kernel

def row296 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck296 : row296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow296 := by decide +kernel

theorem rowEval296 (x : Key → ℝ) : Integer.Sparse.eval row296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck296, Integer.Sparse.eval_collectBalanced, rawRowCheck296]

def rawRow297 : Integer.Sparse Key := [(key1321, -2), (key1342, 1), (key1342, 1), (key1301, 2), (key1348, -1), (key1348, -1), (key1305, -1), (key1305, -1), (key1332, 1), (key1332, 1), (key1429, 2), (key1460, -1), (key1460, -1), (key1396, -2), (key1469, 1), (key1469, 1), (key1400, 1), (key1400, 1), (key1450, -1), (key1450, -1), (key1578, -2), (key1662, 1), (key1662, 1), (key1551, 2), (key1670, -1), (key1670, -1), (key1562, -1), (key1562, -1), (key1599, 1), (key1599, 1), (key1793, 1), (key1793, 1), (key1820, -1), (key1820, -1), (key1777, -1), (key1777, -1), (key1828, 1), (key1828, 1), (key1783, 1), (key1783, 1), (key1801, -1), (key1801, -1)]

theorem rawRowCheck297 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1 = rawRow297 := by decide +kernel

def row297 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

theorem rowCheck297 : row297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow297 := by decide +kernel

theorem rowEval297 (x : Key → ℝ) : Integer.Sparse.eval row297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck297, Integer.Sparse.eval_collectBalanced, rawRowCheck297]

def rawRow298 : Integer.Sparse Key := [(key1342, -2), (key1321, 1), (key1342, 1), (key1348, 2), (key1301, -1), (key1348, -1), (key1332, -1), (key1349, -1), (key1305, 1), (key1349, 1), (key1460, 2), (key1429, -1), (key1460, -1), (key1469, -2), (key1396, 1), (key1469, 1), (key1450, 1), (key1470, 1), (key1400, -1), (key1470, -1), (key1662, -2), (key1578, 1), (key1662, 1), (key1670, 2), (key1551, -1), (key1670, -1), (key1599, -1), (key1676, -1), (key1562, 1), (key1676, 1), (key1820, 1), (key1843, 1), (key1793, -1), (key1843, -1), (key1828, -1), (key1846, -1), (key1777, 1), (key1846, 1), (key1801, 1), (key1849, 1), (key1783, -1), (key1849, -1)]

theorem rawRowCheck298 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1 = rawRow298 := by decide +kernel

def row298 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck298 : row298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow298 := by decide +kernel

theorem rowEval298 (x : Key → ℝ) : Integer.Sparse.eval row298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck298, Integer.Sparse.eval_collectBalanced, rawRowCheck298]

def rawRow299 : Integer.Sparse Key := [(key1342, -2), (key1342, 1), (key1321, 1), (key1348, 2), (key1348, -1), (key1301, -1), (key1349, -1), (key1332, -1), (key1349, 1), (key1305, 1), (key1460, 2), (key1460, -1), (key1429, -1), (key1469, -2), (key1469, 1), (key1396, 1), (key1470, 1), (key1450, 1), (key1470, -1), (key1400, -1), (key1662, -2), (key1662, 1), (key1578, 1), (key1670, 2), (key1670, -1), (key1551, -1), (key1676, -1), (key1599, -1), (key1676, 1), (key1562, 1), (key1843, 1), (key1820, 1), (key1843, -1), (key1793, -1), (key1846, -1), (key1828, -1), (key1846, 1), (key1777, 1), (key1849, 1), (key1801, 1), (key1849, -1), (key1783, -1)]

theorem rawRowCheck299 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1 = rawRow299 := by decide +kernel

def row299 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck299 : row299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow299 := by decide +kernel

theorem rowEval299 (x : Key → ℝ) : Integer.Sparse.eval row299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck299, Integer.Sparse.eval_collectBalanced, rawRowCheck299]

def rawRow300 : Integer.Sparse Key := [(key1332, -2), (key1348, 1), (key1349, 1), (key1305, 2), (key1342, -1), (key1349, -1), (key1301, -1), (key1305, -1), (key1321, 1), (key1332, 1), (key1450, 2), (key1469, -1), (key1470, -1), (key1400, -2), (key1460, 1), (key1470, 1), (key1396, 1), (key1400, 1), (key1429, -1), (key1450, -1), (key1599, -2), (key1670, 1), (key1676, 1), (key1562, 2), (key1662, -1), (key1676, -1), (key1551, -1), (key1562, -1), (key1578, 1), (key1599, 1), (key1801, 1), (key1802, 1), (key1828, -1), (key1834, -1), (key1783, -1), (key1784, -1), (key1820, 1), (key1834, 1), (key1777, 1), (key1784, 1), (key1793, -1), (key1802, -1)]

theorem rawRowCheck300 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1 = rawRow300 := by decide +kernel

def row300 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck300 : row300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow300 := by decide +kernel

theorem rowEval300 (x : Key → ℝ) : Integer.Sparse.eval row300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck300, Integer.Sparse.eval_collectBalanced, rawRowCheck300]

def rawRow301 : Integer.Sparse Key := [(key1332, -2), (key1349, 1), (key1348, 1), (key1305, 2), (key1349, -1), (key1342, -1), (key1305, -1), (key1301, -1), (key1332, 1), (key1321, 1), (key1450, 2), (key1470, -1), (key1469, -1), (key1400, -2), (key1470, 1), (key1460, 1), (key1400, 1), (key1396, 1), (key1450, -1), (key1429, -1), (key1599, -2), (key1676, 1), (key1670, 1), (key1562, 2), (key1676, -1), (key1662, -1), (key1562, -1), (key1551, -1), (key1599, 1), (key1578, 1), (key1802, 1), (key1801, 1), (key1834, -1), (key1828, -1), (key1784, -1), (key1783, -1), (key1834, 1), (key1820, 1), (key1784, 1), (key1777, 1), (key1802, -1), (key1793, -1)]

theorem rawRowCheck301 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1 = rawRow301 := by decide +kernel

def row301 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck301 : row301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow301 := by decide +kernel

theorem rowEval301 (x : Key → ℝ) : Integer.Sparse.eval row301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck301, Integer.Sparse.eval_collectBalanced, rawRowCheck301]

def rawRow302 : Integer.Sparse Key := [(key1348, -2), (key1332, 1), (key1349, 1), (key1342, 2), (key1305, -1), (key1349, -1), (key1321, -1), (key1342, -1), (key1301, 1), (key1348, 1), (key1469, 2), (key1450, -1), (key1470, -1), (key1460, -2), (key1400, 1), (key1470, 1), (key1429, 1), (key1460, 1), (key1396, -1), (key1469, -1), (key1670, -2), (key1599, 1), (key1676, 1), (key1662, 2), (key1562, -1), (key1676, -1), (key1578, -1), (key1662, -1), (key1551, 1), (key1670, 1), (key1828, 1), (key1846, 1), (key1801, -1), (key1849, -1), (key1820, -1), (key1843, -1), (key1783, 1), (key1849, 1), (key1793, 1), (key1843, 1), (key1777, -1), (key1846, -1)]

theorem rawRowCheck302 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1 = rawRow302 := by decide +kernel

def row302 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck302 : row302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow302 := by decide +kernel

theorem rowEval302 (x : Key → ℝ) : Integer.Sparse.eval row302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck302, Integer.Sparse.eval_collectBalanced, rawRowCheck302]

def rawRow303 : Integer.Sparse Key := [(key1348, -2), (key1349, 1), (key1332, 1), (key1342, 2), (key1349, -1), (key1305, -1), (key1342, -1), (key1321, -1), (key1348, 1), (key1301, 1), (key1469, 2), (key1470, -1), (key1450, -1), (key1460, -2), (key1470, 1), (key1400, 1), (key1460, 1), (key1429, 1), (key1469, -1), (key1396, -1), (key1670, -2), (key1676, 1), (key1599, 1), (key1662, 2), (key1676, -1), (key1562, -1), (key1662, -1), (key1578, -1), (key1670, 1), (key1551, 1), (key1846, 1), (key1828, 1), (key1849, -1), (key1801, -1), (key1843, -1), (key1820, -1), (key1849, 1), (key1783, 1), (key1843, 1), (key1793, 1), (key1846, -1), (key1777, -1)]

theorem rawRowCheck303 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1 = rawRow303 := by decide +kernel

def row303 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck303 : row303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow303 := by decide +kernel

theorem rowEval303 (x : Key → ℝ) : Integer.Sparse.eval row303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck303, Integer.Sparse.eval_collectBalanced, rawRowCheck303]

def rawRow304 : Integer.Sparse Key := [(key1396, -2), (key1400, 1), (key1400, 1), (key1551, 2), (key1562, -1), (key1562, -1), (key1777, -1), (key1777, -1), (key1783, 1), (key1783, 1), (key1301, 2), (key1305, -1), (key1305, -1), (key1578, -2), (key1599, 1), (key1599, 1), (key1793, 1), (key1793, 1), (key1801, -1), (key1801, -1), (key1321, -2), (key1332, 1), (key1332, 1), (key1429, 2), (key1450, -1), (key1450, -1), (key1820, -1), (key1820, -1), (key1828, 1), (key1828, 1), (key1342, 1), (key1342, 1), (key1348, -1), (key1348, -1), (key1460, -1), (key1460, -1), (key1469, 1), (key1469, 1), (key1662, 1), (key1662, 1), (key1670, -1), (key1670, -1)]

theorem rawRowCheck304 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1 = rawRow304 := by decide +kernel

def row304 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

theorem rowCheck304 : row304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow304 := by decide +kernel

theorem rowEval304 (x : Key → ℝ) : Integer.Sparse.eval row304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck304, Integer.Sparse.eval_collectBalanced, rawRowCheck304]

def rawRow305 : Integer.Sparse Key := [(key1400, -2), (key1396, 1), (key1400, 1), (key1562, 2), (key1551, -1), (key1562, -1), (key1783, -1), (key1784, -1), (key1777, 1), (key1784, 1), (key1305, 2), (key1301, -1), (key1305, -1), (key1599, -2), (key1578, 1), (key1599, 1), (key1801, 1), (key1802, 1), (key1793, -1), (key1802, -1), (key1332, -2), (key1321, 1), (key1332, 1), (key1450, 2), (key1429, -1), (key1450, -1), (key1828, -1), (key1834, -1), (key1820, 1), (key1834, 1), (key1348, 1), (key1349, 1), (key1342, -1), (key1349, -1), (key1469, -1), (key1470, -1), (key1460, 1), (key1470, 1), (key1670, 1), (key1676, 1), (key1662, -1), (key1676, -1)]

theorem rawRowCheck305 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1 = rawRow305 := by decide +kernel

def row305 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck305 : row305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow305 := by decide +kernel

theorem rowEval305 (x : Key → ℝ) : Integer.Sparse.eval row305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck305, Integer.Sparse.eval_collectBalanced, rawRowCheck305]

def rawRow306 : Integer.Sparse Key := [(key1400, -2), (key1400, 1), (key1396, 1), (key1562, 2), (key1562, -1), (key1551, -1), (key1784, -1), (key1783, -1), (key1784, 1), (key1777, 1), (key1305, 2), (key1305, -1), (key1301, -1), (key1599, -2), (key1599, 1), (key1578, 1), (key1802, 1), (key1801, 1), (key1802, -1), (key1793, -1), (key1332, -2), (key1332, 1), (key1321, 1), (key1450, 2), (key1450, -1), (key1429, -1), (key1834, -1), (key1828, -1), (key1834, 1), (key1820, 1), (key1349, 1), (key1348, 1), (key1349, -1), (key1342, -1), (key1470, -1), (key1469, -1), (key1470, 1), (key1460, 1), (key1676, 1), (key1670, 1), (key1676, -1), (key1662, -1)]

theorem rawRowCheck306 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1 = rawRow306 := by decide +kernel

def row306 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck306 : row306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow306 := by decide +kernel

theorem rowEval306 (x : Key → ℝ) : Integer.Sparse.eval row306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck306, Integer.Sparse.eval_collectBalanced, rawRowCheck306]

def rawRow307 : Integer.Sparse Key := [(key1551, -2), (key1777, 1), (key1777, 1), (key1396, 2), (key1783, -1), (key1783, -1), (key1400, -1), (key1400, -1), (key1562, 1), (key1562, 1), (key1578, 2), (key1793, -1), (key1793, -1), (key1301, -2), (key1801, 1), (key1801, 1), (key1305, 1), (key1305, 1), (key1599, -1), (key1599, -1), (key1429, -2), (key1820, 1), (key1820, 1), (key1321, 2), (key1828, -1), (key1828, -1), (key1332, -1), (key1332, -1), (key1450, 1), (key1450, 1), (key1460, 1), (key1460, 1), (key1662, -1), (key1662, -1), (key1342, -1), (key1342, -1), (key1670, 1), (key1670, 1), (key1348, 1), (key1348, 1), (key1469, -1), (key1469, -1)]

theorem rawRowCheck307 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1 = rawRow307 := by decide +kernel

def row307 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

theorem rowCheck307 : row307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow307 := by decide +kernel

theorem rowEval307 (x : Key → ℝ) : Integer.Sparse.eval row307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck307, Integer.Sparse.eval_collectBalanced, rawRowCheck307]

def rawRow308 : Integer.Sparse Key := [(key1777, -2), (key1551, 1), (key1777, 1), (key1783, 2), (key1396, -1), (key1783, -1), (key1562, -1), (key1784, -1), (key1400, 1), (key1784, 1), (key1793, 2), (key1578, -1), (key1793, -1), (key1801, -2), (key1301, 1), (key1801, 1), (key1599, 1), (key1802, 1), (key1305, -1), (key1802, -1), (key1820, -2), (key1429, 1), (key1820, 1), (key1828, 2), (key1321, -1), (key1828, -1), (key1450, -1), (key1834, -1), (key1332, 1), (key1834, 1), (key1662, 1), (key1843, 1), (key1460, -1), (key1843, -1), (key1670, -1), (key1846, -1), (key1342, 1), (key1846, 1), (key1469, 1), (key1849, 1), (key1348, -1), (key1849, -1)]

theorem rawRowCheck308 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1 = rawRow308 := by decide +kernel

def row308 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck308 : row308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow308 := by decide +kernel

theorem rowEval308 (x : Key → ℝ) : Integer.Sparse.eval row308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck308, Integer.Sparse.eval_collectBalanced, rawRowCheck308]

def rawRow309 : Integer.Sparse Key := [(key1777, -2), (key1777, 1), (key1551, 1), (key1783, 2), (key1783, -1), (key1396, -1), (key1784, -1), (key1562, -1), (key1784, 1), (key1400, 1), (key1793, 2), (key1793, -1), (key1578, -1), (key1801, -2), (key1801, 1), (key1301, 1), (key1802, 1), (key1599, 1), (key1802, -1), (key1305, -1), (key1820, -2), (key1820, 1), (key1429, 1), (key1828, 2), (key1828, -1), (key1321, -1), (key1834, -1), (key1450, -1), (key1834, 1), (key1332, 1), (key1843, 1), (key1662, 1), (key1843, -1), (key1460, -1), (key1846, -1), (key1670, -1), (key1846, 1), (key1342, 1), (key1849, 1), (key1469, 1), (key1849, -1), (key1348, -1)]

theorem rawRowCheck309 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1 = rawRow309 := by decide +kernel

def row309 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck309 : row309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow309 := by decide +kernel

theorem rowEval309 (x : Key → ℝ) : Integer.Sparse.eval row309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck309, Integer.Sparse.eval_collectBalanced, rawRowCheck309]

def rawRow310 : Integer.Sparse Key := [(key1562, -2), (key1783, 1), (key1784, 1), (key1400, 2), (key1777, -1), (key1784, -1), (key1396, -1), (key1400, -1), (key1551, 1), (key1562, 1), (key1599, 2), (key1801, -1), (key1802, -1), (key1305, -2), (key1793, 1), (key1802, 1), (key1301, 1), (key1305, 1), (key1578, -1), (key1599, -1), (key1450, -2), (key1828, 1), (key1834, 1), (key1332, 2), (key1820, -1), (key1834, -1), (key1321, -1), (key1332, -1), (key1429, 1), (key1450, 1), (key1469, 1), (key1470, 1), (key1670, -1), (key1676, -1), (key1348, -1), (key1349, -1), (key1662, 1), (key1676, 1), (key1342, 1), (key1349, 1), (key1460, -1), (key1470, -1)]

theorem rawRowCheck310 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow310 := by decide +kernel

def row310 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck310 : row310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow310 := by decide +kernel

theorem rowEval310 (x : Key → ℝ) : Integer.Sparse.eval row310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck310, Integer.Sparse.eval_collectBalanced, rawRowCheck310]

def rawRow311 : Integer.Sparse Key := [(key1562, -2), (key1784, 1), (key1783, 1), (key1400, 2), (key1784, -1), (key1777, -1), (key1400, -1), (key1396, -1), (key1562, 1), (key1551, 1), (key1599, 2), (key1802, -1), (key1801, -1), (key1305, -2), (key1802, 1), (key1793, 1), (key1305, 1), (key1301, 1), (key1599, -1), (key1578, -1), (key1450, -2), (key1834, 1), (key1828, 1), (key1332, 2), (key1834, -1), (key1820, -1), (key1332, -1), (key1321, -1), (key1450, 1), (key1429, 1), (key1470, 1), (key1469, 1), (key1676, -1), (key1670, -1), (key1349, -1), (key1348, -1), (key1676, 1), (key1662, 1), (key1349, 1), (key1342, 1), (key1470, -1), (key1460, -1)]

theorem rawRowCheck311 : GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow311 := by decide +kernel

def row311 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck311 : row311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow311 := by decide +kernel

theorem rowEval311 (x : Key → ℝ) : Integer.Sparse.eval row311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck311, Integer.Sparse.eval_collectBalanced, rawRowCheck311]

def rawRow312 : Integer.Sparse Key := [(key1783, -2), (key1562, 1), (key1784, 1), (key1777, 2), (key1400, -1), (key1784, -1), (key1551, -1), (key1777, -1), (key1396, 1), (key1783, 1), (key1801, 2), (key1599, -1), (key1802, -1), (key1793, -2), (key1305, 1), (key1802, 1), (key1578, 1), (key1793, 1), (key1301, -1), (key1801, -1), (key1828, -2), (key1450, 1), (key1834, 1), (key1820, 2), (key1332, -1), (key1834, -1), (key1429, -1), (key1820, -1), (key1321, 1), (key1828, 1), (key1670, 1), (key1846, 1), (key1469, -1), (key1849, -1), (key1662, -1), (key1843, -1), (key1348, 1), (key1849, 1), (key1460, 1), (key1843, 1), (key1342, -1), (key1846, -1)]

theorem rawRowCheck312 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow312 := by decide +kernel

def row312 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck312 : row312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow312 := by decide +kernel

theorem rowEval312 (x : Key → ℝ) : Integer.Sparse.eval row312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck312, Integer.Sparse.eval_collectBalanced, rawRowCheck312]

def rawRow313 : Integer.Sparse Key := [(key1783, -2), (key1784, 1), (key1562, 1), (key1777, 2), (key1784, -1), (key1400, -1), (key1777, -1), (key1551, -1), (key1783, 1), (key1396, 1), (key1801, 2), (key1802, -1), (key1599, -1), (key1793, -2), (key1802, 1), (key1305, 1), (key1793, 1), (key1578, 1), (key1801, -1), (key1301, -1), (key1828, -2), (key1834, 1), (key1450, 1), (key1820, 2), (key1834, -1), (key1332, -1), (key1820, -1), (key1429, -1), (key1828, 1), (key1321, 1), (key1846, 1), (key1670, 1), (key1849, -1), (key1469, -1), (key1843, -1), (key1662, -1), (key1849, 1), (key1348, 1), (key1843, 1), (key1460, 1), (key1846, -1), (key1342, -1)]

theorem rawRowCheck313 : GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow313 := by decide +kernel

def row313 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck313 : row313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow313 := by decide +kernel

theorem rowEval313 (x : Key → ℝ) : Integer.Sparse.eval row313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck313, Integer.Sparse.eval_collectBalanced, rawRowCheck313]

def rawRow314 : Integer.Sparse Key := [(key1429, -2), (key1460, 1), (key1460, 1), (key1578, 2), (key1662, -1), (key1662, -1), (key1793, -1), (key1793, -1), (key1820, 1), (key1820, 1), (key1321, 2), (key1342, -1), (key1342, -1), (key1551, -2), (key1670, 1), (key1670, 1), (key1777, 1), (key1777, 1), (key1828, -1), (key1828, -1), (key1301, -2), (key1348, 1), (key1348, 1), (key1396, 2), (key1469, -1), (key1469, -1), (key1783, -1), (key1783, -1), (key1801, 1), (key1801, 1), (key1305, 1), (key1305, 1), (key1332, -1), (key1332, -1), (key1400, -1), (key1400, -1), (key1450, 1), (key1450, 1), (key1562, 1), (key1562, 1), (key1599, -1), (key1599, -1)]

theorem rawRowCheck314 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1 = rawRow314 := by decide +kernel

def row314 : Integer.Sparse Key := [(key1301, -2), (key1305, 2), (key1321, 2), (key1332, -2), (key1342, -2), (key1348, 2), (key1396, 2), (key1400, -2), (key1429, -2), (key1450, 2), (key1460, 2), (key1469, -2), (key1551, -2), (key1562, 2), (key1578, 2), (key1599, -2), (key1662, -2), (key1670, 2), (key1777, 2), (key1783, -2), (key1793, -2), (key1801, 2), (key1820, 2), (key1828, -2)]

theorem rowCheck314 : row314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow314 := by decide +kernel

theorem rowEval314 (x : Key → ℝ) : Integer.Sparse.eval row314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck314, Integer.Sparse.eval_collectBalanced, rawRowCheck314]

def rawRow315 : Integer.Sparse Key := [(key1460, -2), (key1429, 1), (key1460, 1), (key1662, 2), (key1578, -1), (key1662, -1), (key1820, -1), (key1843, -1), (key1793, 1), (key1843, 1), (key1342, 2), (key1321, -1), (key1342, -1), (key1670, -2), (key1551, 1), (key1670, 1), (key1828, 1), (key1846, 1), (key1777, -1), (key1846, -1), (key1348, -2), (key1301, 1), (key1348, 1), (key1469, 2), (key1396, -1), (key1469, -1), (key1801, -1), (key1849, -1), (key1783, 1), (key1849, 1), (key1332, 1), (key1349, 1), (key1305, -1), (key1349, -1), (key1450, -1), (key1470, -1), (key1400, 1), (key1470, 1), (key1599, 1), (key1676, 1), (key1562, -1), (key1676, -1)]

theorem rawRowCheck315 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1 = rawRow315 := by decide +kernel

def row315 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck315 : row315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow315 := by decide +kernel

theorem rowEval315 (x : Key → ℝ) : Integer.Sparse.eval row315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck315, Integer.Sparse.eval_collectBalanced, rawRowCheck315]

def rawRow316 : Integer.Sparse Key := [(key1460, -2), (key1460, 1), (key1429, 1), (key1662, 2), (key1662, -1), (key1578, -1), (key1843, -1), (key1820, -1), (key1843, 1), (key1793, 1), (key1342, 2), (key1342, -1), (key1321, -1), (key1670, -2), (key1670, 1), (key1551, 1), (key1846, 1), (key1828, 1), (key1846, -1), (key1777, -1), (key1348, -2), (key1348, 1), (key1301, 1), (key1469, 2), (key1469, -1), (key1396, -1), (key1849, -1), (key1801, -1), (key1849, 1), (key1783, 1), (key1349, 1), (key1332, 1), (key1349, -1), (key1305, -1), (key1470, -1), (key1450, -1), (key1470, 1), (key1400, 1), (key1676, 1), (key1599, 1), (key1676, -1), (key1562, -1)]

theorem rawRowCheck316 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1 = rawRow316 := by decide +kernel

def row316 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck316 : row316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow316 := by decide +kernel

theorem rowEval316 (x : Key → ℝ) : Integer.Sparse.eval row316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck316, Integer.Sparse.eval_collectBalanced, rawRowCheck316]

def rawRow317 : Integer.Sparse Key := [(key1578, -2), (key1793, 1), (key1793, 1), (key1429, 2), (key1820, -1), (key1820, -1), (key1460, -1), (key1460, -1), (key1662, 1), (key1662, 1), (key1551, 2), (key1777, -1), (key1777, -1), (key1321, -2), (key1828, 1), (key1828, 1), (key1342, 1), (key1342, 1), (key1670, -1), (key1670, -1), (key1396, -2), (key1783, 1), (key1783, 1), (key1301, 2), (key1801, -1), (key1801, -1), (key1348, -1), (key1348, -1), (key1469, 1), (key1469, 1), (key1400, 1), (key1400, 1), (key1562, -1), (key1562, -1), (key1305, -1), (key1305, -1), (key1599, 1), (key1599, 1), (key1332, 1), (key1332, 1), (key1450, -1), (key1450, -1)]

theorem rawRowCheck317 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1 = rawRow317 := by decide +kernel

def row317 : Integer.Sparse Key := [(key1301, 2), (key1305, -2), (key1321, -2), (key1332, 2), (key1342, 2), (key1348, -2), (key1396, -2), (key1400, 2), (key1429, 2), (key1450, -2), (key1460, -2), (key1469, 2), (key1551, 2), (key1562, -2), (key1578, -2), (key1599, 2), (key1662, 2), (key1670, -2), (key1777, -2), (key1783, 2), (key1793, 2), (key1801, -2), (key1820, -2), (key1828, 2)]

theorem rowCheck317 : row317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow317 := by decide +kernel

theorem rowEval317 (x : Key → ℝ) : Integer.Sparse.eval row317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck317, Integer.Sparse.eval_collectBalanced, rawRowCheck317]

def rawRow318 : Integer.Sparse Key := [(key1793, -2), (key1578, 1), (key1793, 1), (key1820, 2), (key1429, -1), (key1820, -1), (key1662, -1), (key1843, -1), (key1460, 1), (key1843, 1), (key1777, 2), (key1551, -1), (key1777, -1), (key1828, -2), (key1321, 1), (key1828, 1), (key1670, 1), (key1846, 1), (key1342, -1), (key1846, -1), (key1783, -2), (key1396, 1), (key1783, 1), (key1801, 2), (key1301, -1), (key1801, -1), (key1469, -1), (key1849, -1), (key1348, 1), (key1849, 1), (key1562, 1), (key1784, 1), (key1400, -1), (key1784, -1), (key1599, -1), (key1802, -1), (key1305, 1), (key1802, 1), (key1450, 1), (key1834, 1), (key1332, -1), (key1834, -1)]

theorem rawRowCheck318 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1 = rawRow318 := by decide +kernel

def row318 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck318 : row318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow318 := by decide +kernel

theorem rowEval318 (x : Key → ℝ) : Integer.Sparse.eval row318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck318, Integer.Sparse.eval_collectBalanced, rawRowCheck318]

def rawRow319 : Integer.Sparse Key := [(key1793, -2), (key1793, 1), (key1578, 1), (key1820, 2), (key1820, -1), (key1429, -1), (key1843, -1), (key1662, -1), (key1843, 1), (key1460, 1), (key1777, 2), (key1777, -1), (key1551, -1), (key1828, -2), (key1828, 1), (key1321, 1), (key1846, 1), (key1670, 1), (key1846, -1), (key1342, -1), (key1783, -2), (key1783, 1), (key1396, 1), (key1801, 2), (key1801, -1), (key1301, -1), (key1849, -1), (key1469, -1), (key1849, 1), (key1348, 1), (key1784, 1), (key1562, 1), (key1784, -1), (key1400, -1), (key1802, -1), (key1599, -1), (key1802, 1), (key1305, 1), (key1834, 1), (key1450, 1), (key1834, -1), (key1332, -1)]

theorem rawRowCheck319 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1 = rawRow319 := by decide +kernel

def row319 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck319 : row319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow319 := by decide +kernel

theorem rowEval319 (x : Key → ℝ) : Integer.Sparse.eval row319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck319, Integer.Sparse.eval_collectBalanced, rawRowCheck319]

end MUB6.Certificate.GramRows

end OAI
