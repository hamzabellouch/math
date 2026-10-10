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

def rawRow320 : Integer.Sparse Key := [(key1662, -2), (key1820, 1), (key1843, 1), (key1460, 2), (key1793, -1), (key1843, -1), (key1429, -1), (key1460, -1), (key1578, 1), (key1662, 1), (key1670, 2), (key1828, -1), (key1846, -1), (key1342, -2), (key1777, 1), (key1846, 1), (key1321, 1), (key1342, 1), (key1551, -1), (key1670, -1), (key1469, -2), (key1801, 1), (key1849, 1), (key1348, 2), (key1783, -1), (key1849, -1), (key1301, -1), (key1348, -1), (key1396, 1), (key1469, 1), (key1450, 1), (key1470, 1), (key1599, -1), (key1676, -1), (key1332, -1), (key1349, -1), (key1562, 1), (key1676, 1), (key1305, 1), (key1349, 1), (key1400, -1), (key1470, -1)]

theorem rawRowCheck320 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1 = rawRow320 := by decide +kernel

def row320 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck320 : row320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow320 := by decide +kernel

theorem rowEval320 (x : Key → ℝ) : Integer.Sparse.eval row320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck320, Integer.Sparse.eval_collectBalanced, rawRowCheck320]

def rawRow321 : Integer.Sparse Key := [(key1662, -2), (key1843, 1), (key1820, 1), (key1460, 2), (key1843, -1), (key1793, -1), (key1460, -1), (key1429, -1), (key1662, 1), (key1578, 1), (key1670, 2), (key1846, -1), (key1828, -1), (key1342, -2), (key1846, 1), (key1777, 1), (key1342, 1), (key1321, 1), (key1670, -1), (key1551, -1), (key1469, -2), (key1849, 1), (key1801, 1), (key1348, 2), (key1849, -1), (key1783, -1), (key1348, -1), (key1301, -1), (key1469, 1), (key1396, 1), (key1470, 1), (key1450, 1), (key1676, -1), (key1599, -1), (key1349, -1), (key1332, -1), (key1676, 1), (key1562, 1), (key1349, 1), (key1305, 1), (key1470, -1), (key1400, -1)]

theorem rawRowCheck321 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1 = rawRow321 := by decide +kernel

def row321 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck321 : row321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow321 := by decide +kernel

theorem rowEval321 (x : Key → ℝ) : Integer.Sparse.eval row321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck321, Integer.Sparse.eval_collectBalanced, rawRowCheck321]

def rawRow322 : Integer.Sparse Key := [(key1820, -2), (key1662, 1), (key1843, 1), (key1793, 2), (key1460, -1), (key1843, -1), (key1578, -1), (key1793, -1), (key1429, 1), (key1820, 1), (key1828, 2), (key1670, -1), (key1846, -1), (key1777, -2), (key1342, 1), (key1846, 1), (key1551, 1), (key1777, 1), (key1321, -1), (key1828, -1), (key1801, -2), (key1469, 1), (key1849, 1), (key1783, 2), (key1348, -1), (key1849, -1), (key1396, -1), (key1783, -1), (key1301, 1), (key1801, 1), (key1599, 1), (key1802, 1), (key1450, -1), (key1834, -1), (key1562, -1), (key1784, -1), (key1332, 1), (key1834, 1), (key1400, 1), (key1784, 1), (key1305, -1), (key1802, -1)]

theorem rawRowCheck322 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1 = rawRow322 := by decide +kernel

def row322 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck322 : row322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow322 := by decide +kernel

theorem rowEval322 (x : Key → ℝ) : Integer.Sparse.eval row322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck322, Integer.Sparse.eval_collectBalanced, rawRowCheck322]

def rawRow323 : Integer.Sparse Key := [(key1820, -2), (key1843, 1), (key1662, 1), (key1793, 2), (key1843, -1), (key1460, -1), (key1793, -1), (key1578, -1), (key1820, 1), (key1429, 1), (key1828, 2), (key1846, -1), (key1670, -1), (key1777, -2), (key1846, 1), (key1342, 1), (key1777, 1), (key1551, 1), (key1828, -1), (key1321, -1), (key1801, -2), (key1849, 1), (key1469, 1), (key1783, 2), (key1849, -1), (key1348, -1), (key1783, -1), (key1396, -1), (key1801, 1), (key1301, 1), (key1802, 1), (key1599, 1), (key1834, -1), (key1450, -1), (key1784, -1), (key1562, -1), (key1834, 1), (key1332, 1), (key1784, 1), (key1400, 1), (key1802, -1), (key1305, -1)]

theorem rawRowCheck323 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1 = rawRow323 := by decide +kernel

def row323 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck323 : row323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow323 := by decide +kernel

theorem rowEval323 (x : Key → ℝ) : Integer.Sparse.eval row323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck323, Integer.Sparse.eval_collectBalanced, rawRowCheck323]

def rawRow324 : Integer.Sparse Key := [(key1450, -2), (key1469, 1), (key1470, 1), (key1599, 2), (key1670, -1), (key1676, -1), (key1801, -1), (key1802, -1), (key1828, 1), (key1834, 1), (key1332, 2), (key1348, -1), (key1349, -1), (key1562, -2), (key1662, 1), (key1676, 1), (key1783, 1), (key1784, 1), (key1820, -1), (key1834, -1), (key1305, -2), (key1342, 1), (key1349, 1), (key1400, 2), (key1460, -1), (key1470, -1), (key1777, -1), (key1784, -1), (key1793, 1), (key1802, 1), (key1301, 1), (key1305, 1), (key1321, -1), (key1332, -1), (key1396, -1), (key1400, -1), (key1429, 1), (key1450, 1), (key1551, 1), (key1562, 1), (key1578, -1), (key1599, -1)]

theorem rawRowCheck324 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1 = rawRow324 := by decide +kernel

def row324 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck324 : row324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow324 := by decide +kernel

theorem rowEval324 (x : Key → ℝ) : Integer.Sparse.eval row324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck324, Integer.Sparse.eval_collectBalanced, rawRowCheck324]

def rawRow325 : Integer.Sparse Key := [(key1450, -2), (key1470, 1), (key1469, 1), (key1599, 2), (key1676, -1), (key1670, -1), (key1802, -1), (key1801, -1), (key1834, 1), (key1828, 1), (key1332, 2), (key1349, -1), (key1348, -1), (key1562, -2), (key1676, 1), (key1662, 1), (key1784, 1), (key1783, 1), (key1834, -1), (key1820, -1), (key1305, -2), (key1349, 1), (key1342, 1), (key1400, 2), (key1470, -1), (key1460, -1), (key1784, -1), (key1777, -1), (key1802, 1), (key1793, 1), (key1305, 1), (key1301, 1), (key1332, -1), (key1321, -1), (key1400, -1), (key1396, -1), (key1450, 1), (key1429, 1), (key1562, 1), (key1551, 1), (key1599, -1), (key1578, -1)]

theorem rawRowCheck325 : GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1 = rawRow325 := by decide +kernel

def row325 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck325 : row325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow325 := by decide +kernel

theorem rowEval325 (x : Key → ℝ) : Integer.Sparse.eval row325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, -1, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck325, Integer.Sparse.eval_collectBalanced, rawRowCheck325]

def rawRow326 : Integer.Sparse Key := [(key1469, -2), (key1450, 1), (key1470, 1), (key1670, 2), (key1599, -1), (key1676, -1), (key1828, -1), (key1846, -1), (key1801, 1), (key1849, 1), (key1348, 2), (key1332, -1), (key1349, -1), (key1662, -2), (key1562, 1), (key1676, 1), (key1820, 1), (key1843, 1), (key1783, -1), (key1849, -1), (key1342, -2), (key1305, 1), (key1349, 1), (key1460, 2), (key1400, -1), (key1470, -1), (key1793, -1), (key1843, -1), (key1777, 1), (key1846, 1), (key1321, 1), (key1342, 1), (key1301, -1), (key1348, -1), (key1429, -1), (key1460, -1), (key1396, 1), (key1469, 1), (key1578, 1), (key1662, 1), (key1551, -1), (key1670, -1)]

theorem rawRowCheck326 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1 = rawRow326 := by decide +kernel

def row326 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck326 : row326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow326 := by decide +kernel

theorem rowEval326 (x : Key → ℝ) : Integer.Sparse.eval row326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck326, Integer.Sparse.eval_collectBalanced, rawRowCheck326]

def rawRow327 : Integer.Sparse Key := [(key1469, -2), (key1470, 1), (key1450, 1), (key1670, 2), (key1676, -1), (key1599, -1), (key1846, -1), (key1828, -1), (key1849, 1), (key1801, 1), (key1348, 2), (key1349, -1), (key1332, -1), (key1662, -2), (key1676, 1), (key1562, 1), (key1843, 1), (key1820, 1), (key1849, -1), (key1783, -1), (key1342, -2), (key1349, 1), (key1305, 1), (key1460, 2), (key1470, -1), (key1400, -1), (key1843, -1), (key1793, -1), (key1846, 1), (key1777, 1), (key1342, 1), (key1321, 1), (key1348, -1), (key1301, -1), (key1460, -1), (key1429, -1), (key1469, 1), (key1396, 1), (key1662, 1), (key1578, 1), (key1670, -1), (key1551, -1)]

theorem rawRowCheck327 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1 = rawRow327 := by decide +kernel

def row327 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck327 : row327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow327 := by decide +kernel

theorem rowEval327 (x : Key → ℝ) : Integer.Sparse.eval row327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck327, Integer.Sparse.eval_collectBalanced, rawRowCheck327]

def rawRow328 : Integer.Sparse Key := [(key1599, -2), (key1801, 1), (key1802, 1), (key1450, 2), (key1828, -1), (key1834, -1), (key1469, -1), (key1470, -1), (key1670, 1), (key1676, 1), (key1562, 2), (key1783, -1), (key1784, -1), (key1332, -2), (key1820, 1), (key1834, 1), (key1348, 1), (key1349, 1), (key1662, -1), (key1676, -1), (key1400, -2), (key1777, 1), (key1784, 1), (key1305, 2), (key1793, -1), (key1802, -1), (key1342, -1), (key1349, -1), (key1460, 1), (key1470, 1), (key1396, 1), (key1400, 1), (key1551, -1), (key1562, -1), (key1301, -1), (key1305, -1), (key1578, 1), (key1599, 1), (key1321, 1), (key1332, 1), (key1429, -1), (key1450, -1)]

theorem rawRowCheck328 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1 = rawRow328 := by decide +kernel

def row328 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck328 : row328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow328 := by decide +kernel

theorem rowEval328 (x : Key → ℝ) : Integer.Sparse.eval row328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 0, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck328, Integer.Sparse.eval_collectBalanced, rawRowCheck328]

def rawRow329 : Integer.Sparse Key := [(key1599, -2), (key1802, 1), (key1801, 1), (key1450, 2), (key1834, -1), (key1828, -1), (key1470, -1), (key1469, -1), (key1676, 1), (key1670, 1), (key1562, 2), (key1784, -1), (key1783, -1), (key1332, -2), (key1834, 1), (key1820, 1), (key1349, 1), (key1348, 1), (key1676, -1), (key1662, -1), (key1400, -2), (key1784, 1), (key1777, 1), (key1305, 2), (key1802, -1), (key1793, -1), (key1349, -1), (key1342, -1), (key1470, 1), (key1460, 1), (key1400, 1), (key1396, 1), (key1562, -1), (key1551, -1), (key1305, -1), (key1301, -1), (key1599, 1), (key1578, 1), (key1332, 1), (key1321, 1), (key1450, -1), (key1429, -1)]

theorem rawRowCheck329 : GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1 = rawRow329 := by decide +kernel

def row329 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck329 : row329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow329 := by decide +kernel

theorem rowEval329 (x : Key → ℝ) : Integer.Sparse.eval row329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, -2, 1, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck329, Integer.Sparse.eval_collectBalanced, rawRowCheck329]

def rawRow330 : Integer.Sparse Key := [(key1801, -2), (key1599, 1), (key1802, 1), (key1828, 2), (key1450, -1), (key1834, -1), (key1670, -1), (key1846, -1), (key1469, 1), (key1849, 1), (key1783, 2), (key1562, -1), (key1784, -1), (key1820, -2), (key1332, 1), (key1834, 1), (key1662, 1), (key1843, 1), (key1348, -1), (key1849, -1), (key1777, -2), (key1400, 1), (key1784, 1), (key1793, 2), (key1305, -1), (key1802, -1), (key1460, -1), (key1843, -1), (key1342, 1), (key1846, 1), (key1551, 1), (key1777, 1), (key1396, -1), (key1783, -1), (key1578, -1), (key1793, -1), (key1301, 1), (key1801, 1), (key1429, 1), (key1820, 1), (key1321, -1), (key1828, -1)]

theorem rawRowCheck330 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1 = rawRow330 := by decide +kernel

def row330 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck330 : row330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow330 := by decide +kernel

theorem rowEval330 (x : Key → ℝ) : Integer.Sparse.eval row330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck330, Integer.Sparse.eval_collectBalanced, rawRowCheck330]

def rawRow331 : Integer.Sparse Key := [(key1801, -2), (key1802, 1), (key1599, 1), (key1828, 2), (key1834, -1), (key1450, -1), (key1846, -1), (key1670, -1), (key1849, 1), (key1469, 1), (key1783, 2), (key1784, -1), (key1562, -1), (key1820, -2), (key1834, 1), (key1332, 1), (key1843, 1), (key1662, 1), (key1849, -1), (key1348, -1), (key1777, -2), (key1784, 1), (key1400, 1), (key1793, 2), (key1802, -1), (key1305, -1), (key1843, -1), (key1460, -1), (key1846, 1), (key1342, 1), (key1777, 1), (key1551, 1), (key1783, -1), (key1396, -1), (key1793, -1), (key1578, -1), (key1801, 1), (key1301, 1), (key1820, 1), (key1429, 1), (key1828, -1), (key1321, -1)]

theorem rawRowCheck331 : GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1 = rawRow331 := by decide +kernel

def row331 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck331 : row331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow331 := by decide +kernel

theorem rowEval331 (x : Key → ℝ) : Integer.Sparse.eval row331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck331, Integer.Sparse.eval_collectBalanced, rawRowCheck331]

def rawRow332 : Integer.Sparse Key := [(key1670, -2), (key1828, 1), (key1846, 1), (key1469, 2), (key1801, -1), (key1849, -1), (key1450, -1), (key1470, -1), (key1599, 1), (key1676, 1), (key1662, 2), (key1820, -1), (key1843, -1), (key1348, -2), (key1783, 1), (key1849, 1), (key1332, 1), (key1349, 1), (key1562, -1), (key1676, -1), (key1460, -2), (key1793, 1), (key1843, 1), (key1342, 2), (key1777, -1), (key1846, -1), (key1305, -1), (key1349, -1), (key1400, 1), (key1470, 1), (key1429, 1), (key1460, 1), (key1578, -1), (key1662, -1), (key1321, -1), (key1342, -1), (key1551, 1), (key1670, 1), (key1301, 1), (key1348, 1), (key1396, -1), (key1469, -1)]

theorem rawRowCheck332 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1 = rawRow332 := by decide +kernel

def row332 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck332 : row332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow332 := by decide +kernel

theorem rowEval332 (x : Key → ℝ) : Integer.Sparse.eval row332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, -1, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck332, Integer.Sparse.eval_collectBalanced, rawRowCheck332]

def rawRow333 : Integer.Sparse Key := [(key1670, -2), (key1846, 1), (key1828, 1), (key1469, 2), (key1849, -1), (key1801, -1), (key1470, -1), (key1450, -1), (key1676, 1), (key1599, 1), (key1662, 2), (key1843, -1), (key1820, -1), (key1348, -2), (key1849, 1), (key1783, 1), (key1349, 1), (key1332, 1), (key1676, -1), (key1562, -1), (key1460, -2), (key1843, 1), (key1793, 1), (key1342, 2), (key1846, -1), (key1777, -1), (key1349, -1), (key1305, -1), (key1470, 1), (key1400, 1), (key1460, 1), (key1429, 1), (key1662, -1), (key1578, -1), (key1342, -1), (key1321, -1), (key1670, 1), (key1551, 1), (key1348, 1), (key1301, 1), (key1469, -1), (key1396, -1)]

theorem rawRowCheck333 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1 = rawRow333 := by decide +kernel

def row333 : Integer.Sparse Key := [(key1301, 1), (key1305, -1), (key1321, -1), (key1332, 1), (key1342, 1), (key1348, -1), (key1396, -1), (key1400, 1), (key1429, 1), (key1450, -1), (key1460, -1), (key1469, 1), (key1551, 1), (key1562, -1), (key1578, -1), (key1599, 1), (key1662, 1), (key1670, -1), (key1777, -1), (key1783, 1), (key1793, 1), (key1801, -1), (key1820, -1), (key1828, 1)]

theorem rowCheck333 : row333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow333 := by decide +kernel

theorem rowEval333 (x : Key → ℝ) : Integer.Sparse.eval row333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 1, -1] GramFunctions.Block0.form1) x := by
  rw [rowCheck333, Integer.Sparse.eval_collectBalanced, rawRowCheck333]

def rawRow334 : Integer.Sparse Key := [(key1828, -2), (key1670, 1), (key1846, 1), (key1801, 2), (key1469, -1), (key1849, -1), (key1599, -1), (key1802, -1), (key1450, 1), (key1834, 1), (key1820, 2), (key1662, -1), (key1843, -1), (key1783, -2), (key1348, 1), (key1849, 1), (key1562, 1), (key1784, 1), (key1332, -1), (key1834, -1), (key1793, -2), (key1460, 1), (key1843, 1), (key1777, 2), (key1342, -1), (key1846, -1), (key1400, -1), (key1784, -1), (key1305, 1), (key1802, 1), (key1578, 1), (key1793, 1), (key1429, -1), (key1820, -1), (key1551, -1), (key1777, -1), (key1321, 1), (key1828, 1), (key1396, 1), (key1783, 1), (key1301, -1), (key1801, -1)]

theorem rawRowCheck334 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1 = rawRow334 := by decide +kernel

def row334 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck334 : row334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow334 := by decide +kernel

theorem rowEval334 (x : Key → ℝ) : Integer.Sparse.eval row334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, -2, 1] GramFunctions.Block0.form1) x := by
  rw [rowCheck334, Integer.Sparse.eval_collectBalanced, rawRowCheck334]

def rawRow335 : Integer.Sparse Key := [(key1828, -2), (key1846, 1), (key1670, 1), (key1801, 2), (key1849, -1), (key1469, -1), (key1802, -1), (key1599, -1), (key1834, 1), (key1450, 1), (key1820, 2), (key1843, -1), (key1662, -1), (key1783, -2), (key1849, 1), (key1348, 1), (key1784, 1), (key1562, 1), (key1834, -1), (key1332, -1), (key1793, -2), (key1843, 1), (key1460, 1), (key1777, 2), (key1846, -1), (key1342, -1), (key1784, -1), (key1400, -1), (key1802, 1), (key1305, 1), (key1793, 1), (key1578, 1), (key1820, -1), (key1429, -1), (key1777, -1), (key1551, -1), (key1828, 1), (key1321, 1), (key1783, 1), (key1396, 1), (key1801, -1), (key1301, -1)]

theorem rawRowCheck335 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1 = rawRow335 := by decide +kernel

def row335 : Integer.Sparse Key := [(key1301, -1), (key1305, 1), (key1321, 1), (key1332, -1), (key1342, -1), (key1348, 1), (key1396, 1), (key1400, -1), (key1429, -1), (key1450, 1), (key1460, 1), (key1469, -1), (key1551, -1), (key1562, 1), (key1578, 1), (key1599, -1), (key1662, -1), (key1670, 1), (key1777, 1), (key1783, -1), (key1793, -1), (key1801, 1), (key1820, 1), (key1828, -1)]

theorem rowCheck335 : row335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow335 := by decide +kernel

theorem rowEval335 (x : Key → ℝ) : Integer.Sparse.eval row335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -1, 1, -2] GramFunctions.Block0.form1) x := by
  rw [rowCheck335, Integer.Sparse.eval_collectBalanced, rawRowCheck335]

def rawRow336 : Integer.Sparse Key := [(key1300, -1), (key1300, -1), (key1306, 2), (key1320, 1), (key1320, 1), (key1333, -1), (key1333, -1), (key1353, -2), (key1356, 1), (key1356, 1), (key1395, 1), (key1395, 1), (key1401, -2), (key1428, -1), (key1428, -1), (key1451, 1), (key1451, 1), (key1474, 2), (key1482, -1), (key1482, -1), (key1550, -1), (key1550, -1), (key1563, 1), (key1563, 1), (key1577, 1), (key1577, 1), (key1600, -1), (key1600, -1), (key1685, -1), (key1685, -1), (key1691, 1), (key1691, 1), (key1898, 2), (key1901, -1), (key1901, -1), (key1905, -2), (key1913, 1), (key1913, 1), (key1922, 1), (key1922, 1), (key1928, -1), (key1928, -1)]

theorem rawRowCheck336 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form2 = rawRow336 := by decide +kernel

def row336 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

theorem rowCheck336 : row336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow336 := by decide +kernel

theorem rowEval336 (x : Key → ℝ) : Integer.Sparse.eval row336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck336, Integer.Sparse.eval_collectBalanced, rawRowCheck336]

def rawRow337 : Integer.Sparse Key := [(key1300, -1), (key1306, -1), (key1300, 2), (key1328, 1), (key1333, 1), (key1320, -1), (key1328, -1), (key1356, -2), (key1353, 1), (key1356, 1), (key1395, 1), (key1401, 1), (key1395, -2), (key1446, -1), (key1451, -1), (key1428, 1), (key1446, 1), (key1482, 2), (key1474, -1), (key1482, -1), (key1558, -1), (key1563, -1), (key1550, 1), (key1558, 1), (key1595, 1), (key1600, 1), (key1577, -1), (key1595, -1), (key1691, -1), (key1694, -1), (key1685, 1), (key1694, 1), (key1901, 2), (key1898, -1), (key1901, -1), (key1913, -2), (key1905, 1), (key1913, 1), (key1928, 1), (key1931, 1), (key1922, -1), (key1931, -1)]

theorem rawRowCheck337 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form2 = rawRow337 := by decide +kernel

def row337 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck337 : row337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow337 := by decide +kernel

theorem rowEval337 (x : Key → ℝ) : Integer.Sparse.eval row337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck337, Integer.Sparse.eval_collectBalanced, rawRowCheck337]

def rawRow338 : Integer.Sparse Key := [(key1306, -1), (key1300, -1), (key1300, 2), (key1333, 1), (key1328, 1), (key1328, -1), (key1320, -1), (key1356, -2), (key1356, 1), (key1353, 1), (key1401, 1), (key1395, 1), (key1395, -2), (key1451, -1), (key1446, -1), (key1446, 1), (key1428, 1), (key1482, 2), (key1482, -1), (key1474, -1), (key1563, -1), (key1558, -1), (key1558, 1), (key1550, 1), (key1600, 1), (key1595, 1), (key1595, -1), (key1577, -1), (key1694, -1), (key1691, -1), (key1694, 1), (key1685, 1), (key1901, 2), (key1901, -1), (key1898, -1), (key1913, -2), (key1913, 1), (key1905, 1), (key1931, 1), (key1928, 1), (key1931, -1), (key1922, -1)]

theorem rawRowCheck338 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form2 = rawRow338 := by decide +kernel

def row338 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck338 : row338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow338 := by decide +kernel

theorem rowEval338 (x : Key → ℝ) : Integer.Sparse.eval row338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck338, Integer.Sparse.eval_collectBalanced, rawRowCheck338]

def rawRow339 : Integer.Sparse Key := [(key1320, -1), (key1320, -1), (key1353, 2), (key1300, 1), (key1300, 1), (key1356, -1), (key1356, -1), (key1306, -2), (key1333, 1), (key1333, 1), (key1428, 1), (key1428, 1), (key1474, -2), (key1395, -1), (key1395, -1), (key1482, 1), (key1482, 1), (key1401, 2), (key1451, -1), (key1451, -1), (key1577, -1), (key1577, -1), (key1685, 1), (key1685, 1), (key1550, 1), (key1550, 1), (key1691, -1), (key1691, -1), (key1563, -1), (key1563, -1), (key1600, 1), (key1600, 1), (key1905, 2), (key1922, -1), (key1922, -1), (key1898, -2), (key1928, 1), (key1928, 1), (key1901, 1), (key1901, 1), (key1913, -1), (key1913, -1)]

theorem rawRowCheck339 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form2 = rawRow339 := by decide +kernel

def row339 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

theorem rowCheck339 : row339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow339 := by decide +kernel

theorem rowEval339 (x : Key → ℝ) : Integer.Sparse.eval row339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck339, Integer.Sparse.eval_collectBalanced, rawRowCheck339]

def rawRow340 : Integer.Sparse Key := [(key1320, -1), (key1353, -1), (key1320, 2), (key1328, 1), (key1356, 1), (key1300, -1), (key1328, -1), (key1333, -2), (key1306, 1), (key1333, 1), (key1428, 1), (key1474, 1), (key1428, -2), (key1446, -1), (key1482, -1), (key1395, 1), (key1446, 1), (key1451, 2), (key1401, -1), (key1451, -1), (key1626, -1), (key1685, -1), (key1577, 1), (key1626, 1), (key1635, 1), (key1691, 1), (key1550, -1), (key1635, -1), (key1600, -1), (key1644, -1), (key1563, 1), (key1644, 1), (key1922, 2), (key1905, -1), (key1922, -1), (key1928, -2), (key1898, 1), (key1928, 1), (key1913, 1), (key1931, 1), (key1901, -1), (key1931, -1)]

theorem rawRowCheck340 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form2 = rawRow340 := by decide +kernel

def row340 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck340 : row340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow340 := by decide +kernel

theorem rowEval340 (x : Key → ℝ) : Integer.Sparse.eval row340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck340, Integer.Sparse.eval_collectBalanced, rawRowCheck340]

def rawRow341 : Integer.Sparse Key := [(key1353, -1), (key1320, -1), (key1320, 2), (key1356, 1), (key1328, 1), (key1328, -1), (key1300, -1), (key1333, -2), (key1333, 1), (key1306, 1), (key1474, 1), (key1428, 1), (key1428, -2), (key1482, -1), (key1446, -1), (key1446, 1), (key1395, 1), (key1451, 2), (key1451, -1), (key1401, -1), (key1685, -1), (key1626, -1), (key1626, 1), (key1577, 1), (key1691, 1), (key1635, 1), (key1635, -1), (key1550, -1), (key1644, -1), (key1600, -1), (key1644, 1), (key1563, 1), (key1922, 2), (key1922, -1), (key1905, -1), (key1928, -2), (key1928, 1), (key1898, 1), (key1931, 1), (key1913, 1), (key1931, -1), (key1901, -1)]

theorem rawRowCheck341 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form2 = rawRow341 := by decide +kernel

def row341 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck341 : row341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow341 := by decide +kernel

theorem rowEval341 (x : Key → ℝ) : Integer.Sparse.eval row341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck341, Integer.Sparse.eval_collectBalanced, rawRowCheck341]

def rawRow342 : Integer.Sparse Key := [(key1328, -1), (key1333, -1), (key1356, 2), (key1300, 1), (key1306, 1), (key1353, -1), (key1356, -1), (key1300, -2), (key1320, 1), (key1328, 1), (key1446, 1), (key1451, 1), (key1482, -2), (key1395, -1), (key1401, -1), (key1474, 1), (key1482, 1), (key1395, 2), (key1428, -1), (key1446, -1), (key1595, -1), (key1600, -1), (key1691, 1), (key1694, 1), (key1558, 1), (key1563, 1), (key1685, -1), (key1694, -1), (key1550, -1), (key1558, -1), (key1577, 1), (key1595, 1), (key1913, 2), (key1928, -1), (key1931, -1), (key1901, -2), (key1922, 1), (key1931, 1), (key1898, 1), (key1901, 1), (key1905, -1), (key1913, -1)]

theorem rawRowCheck342 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form2 = rawRow342 := by decide +kernel

def row342 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck342 : row342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow342 := by decide +kernel

theorem rowEval342 (x : Key → ℝ) : Integer.Sparse.eval row342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck342, Integer.Sparse.eval_collectBalanced, rawRowCheck342]

def rawRow343 : Integer.Sparse Key := [(key1333, -1), (key1328, -1), (key1356, 2), (key1306, 1), (key1300, 1), (key1356, -1), (key1353, -1), (key1300, -2), (key1328, 1), (key1320, 1), (key1451, 1), (key1446, 1), (key1482, -2), (key1401, -1), (key1395, -1), (key1482, 1), (key1474, 1), (key1395, 2), (key1446, -1), (key1428, -1), (key1600, -1), (key1595, -1), (key1694, 1), (key1691, 1), (key1563, 1), (key1558, 1), (key1694, -1), (key1685, -1), (key1558, -1), (key1550, -1), (key1595, 1), (key1577, 1), (key1913, 2), (key1931, -1), (key1928, -1), (key1901, -2), (key1931, 1), (key1922, 1), (key1901, 1), (key1898, 1), (key1913, -1), (key1905, -1)]

theorem rawRowCheck343 : GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form2 = rawRow343 := by decide +kernel

def row343 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck343 : row343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow343 := by decide +kernel

theorem rowEval343 (x : Key → ℝ) : Integer.Sparse.eval row343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, -1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck343, Integer.Sparse.eval_collectBalanced, rawRowCheck343]

def rawRow344 : Integer.Sparse Key := [(key1328, -1), (key1356, -1), (key1333, 2), (key1320, 1), (key1353, 1), (key1306, -1), (key1333, -1), (key1320, -2), (key1300, 1), (key1328, 1), (key1446, 1), (key1482, 1), (key1451, -2), (key1428, -1), (key1474, -1), (key1401, 1), (key1451, 1), (key1428, 2), (key1395, -1), (key1446, -1), (key1635, -1), (key1691, -1), (key1600, 1), (key1644, 1), (key1626, 1), (key1685, 1), (key1563, -1), (key1644, -1), (key1577, -1), (key1626, -1), (key1550, 1), (key1635, 1), (key1928, 2), (key1913, -1), (key1931, -1), (key1922, -2), (key1901, 1), (key1931, 1), (key1905, 1), (key1922, 1), (key1898, -1), (key1928, -1)]

theorem rawRowCheck344 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form2 = rawRow344 := by decide +kernel

def row344 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck344 : row344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow344 := by decide +kernel

theorem rowEval344 (x : Key → ℝ) : Integer.Sparse.eval row344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, -1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck344, Integer.Sparse.eval_collectBalanced, rawRowCheck344]

def rawRow345 : Integer.Sparse Key := [(key1356, -1), (key1328, -1), (key1333, 2), (key1353, 1), (key1320, 1), (key1333, -1), (key1306, -1), (key1320, -2), (key1328, 1), (key1300, 1), (key1482, 1), (key1446, 1), (key1451, -2), (key1474, -1), (key1428, -1), (key1451, 1), (key1401, 1), (key1428, 2), (key1446, -1), (key1395, -1), (key1691, -1), (key1635, -1), (key1644, 1), (key1600, 1), (key1685, 1), (key1626, 1), (key1644, -1), (key1563, -1), (key1626, -1), (key1577, -1), (key1635, 1), (key1550, 1), (key1928, 2), (key1931, -1), (key1913, -1), (key1922, -2), (key1931, 1), (key1901, 1), (key1922, 1), (key1905, 1), (key1928, -1), (key1898, -1)]

theorem rawRowCheck345 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form2 = rawRow345 := by decide +kernel

def row345 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck345 : row345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow345 := by decide +kernel

theorem rowEval345 (x : Key → ℝ) : Integer.Sparse.eval row345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 1, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck345, Integer.Sparse.eval_collectBalanced, rawRowCheck345]

def rawRow346 : Integer.Sparse Key := [(key1395, -1), (key1395, -1), (key1401, 2), (key1550, 1), (key1550, 1), (key1563, -1), (key1563, -1), (key1898, -2), (key1901, 1), (key1901, 1), (key1300, 1), (key1300, 1), (key1306, -2), (key1577, -1), (key1577, -1), (key1600, 1), (key1600, 1), (key1905, 2), (key1913, -1), (key1913, -1), (key1320, -1), (key1320, -1), (key1333, 1), (key1333, 1), (key1428, 1), (key1428, 1), (key1451, -1), (key1451, -1), (key1922, -1), (key1922, -1), (key1928, 1), (key1928, 1), (key1353, 2), (key1356, -1), (key1356, -1), (key1474, -2), (key1482, 1), (key1482, 1), (key1685, 1), (key1685, 1), (key1691, -1), (key1691, -1)]

theorem rawRowCheck346 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form2 = rawRow346 := by decide +kernel

def row346 : Integer.Sparse Key := [(key1300, 2), (key1306, -2), (key1320, -2), (key1333, 2), (key1353, 2), (key1356, -2), (key1395, -2), (key1401, 2), (key1428, 2), (key1451, -2), (key1474, -2), (key1482, 2), (key1550, 2), (key1563, -2), (key1577, -2), (key1600, 2), (key1685, 2), (key1691, -2), (key1898, -2), (key1901, 2), (key1905, 2), (key1913, -2), (key1922, -2), (key1928, 2)]

theorem rowCheck346 : row346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow346 := by decide +kernel

theorem rowEval346 (x : Key → ℝ) : Integer.Sparse.eval row346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck346, Integer.Sparse.eval_collectBalanced, rawRowCheck346]

def rawRow347 : Integer.Sparse Key := [(key1395, -1), (key1401, -1), (key1395, 2), (key1558, 1), (key1563, 1), (key1550, -1), (key1558, -1), (key1901, -2), (key1898, 1), (key1901, 1), (key1300, 1), (key1306, 1), (key1300, -2), (key1595, -1), (key1600, -1), (key1577, 1), (key1595, 1), (key1913, 2), (key1905, -1), (key1913, -1), (key1328, -1), (key1333, -1), (key1320, 1), (key1328, 1), (key1446, 1), (key1451, 1), (key1428, -1), (key1446, -1), (key1928, -1), (key1931, -1), (key1922, 1), (key1931, 1), (key1356, 2), (key1353, -1), (key1356, -1), (key1482, -2), (key1474, 1), (key1482, 1), (key1691, 1), (key1694, 1), (key1685, -1), (key1694, -1)]

theorem rawRowCheck347 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form2 = rawRow347 := by decide +kernel

def row347 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck347 : row347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow347 := by decide +kernel

theorem rowEval347 (x : Key → ℝ) : Integer.Sparse.eval row347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck347, Integer.Sparse.eval_collectBalanced, rawRowCheck347]

def rawRow348 : Integer.Sparse Key := [(key1401, -1), (key1395, -1), (key1395, 2), (key1563, 1), (key1558, 1), (key1558, -1), (key1550, -1), (key1901, -2), (key1901, 1), (key1898, 1), (key1306, 1), (key1300, 1), (key1300, -2), (key1600, -1), (key1595, -1), (key1595, 1), (key1577, 1), (key1913, 2), (key1913, -1), (key1905, -1), (key1333, -1), (key1328, -1), (key1328, 1), (key1320, 1), (key1451, 1), (key1446, 1), (key1446, -1), (key1428, -1), (key1931, -1), (key1928, -1), (key1931, 1), (key1922, 1), (key1356, 2), (key1356, -1), (key1353, -1), (key1482, -2), (key1482, 1), (key1474, 1), (key1694, 1), (key1691, 1), (key1694, -1), (key1685, -1)]

theorem rawRowCheck348 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form2 = rawRow348 := by decide +kernel

def row348 : Integer.Sparse Key := [(key1300, -1), (key1306, 1), (key1320, 1), (key1333, -1), (key1353, -1), (key1356, 1), (key1395, 1), (key1401, -1), (key1428, -1), (key1451, 1), (key1474, 1), (key1482, -1), (key1550, -1), (key1563, 1), (key1577, 1), (key1600, -1), (key1685, -1), (key1691, 1), (key1898, 1), (key1901, -1), (key1905, -1), (key1913, 1), (key1922, 1), (key1928, -1)]

theorem rowCheck348 : row348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow348 := by decide +kernel

theorem rowEval348 (x : Key → ℝ) : Integer.Sparse.eval row348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck348, Integer.Sparse.eval_collectBalanced, rawRowCheck348]

def rawRow349 : Integer.Sparse Key := [(key1550, -1), (key1550, -1), (key1898, 2), (key1395, 1), (key1395, 1), (key1901, -1), (key1901, -1), (key1401, -2), (key1563, 1), (key1563, 1), (key1577, 1), (key1577, 1), (key1905, -2), (key1300, -1), (key1300, -1), (key1913, 1), (key1913, 1), (key1306, 2), (key1600, -1), (key1600, -1), (key1428, -1), (key1428, -1), (key1922, 1), (key1922, 1), (key1320, 1), (key1320, 1), (key1928, -1), (key1928, -1), (key1333, -1), (key1333, -1), (key1451, 1), (key1451, 1), (key1474, 2), (key1685, -1), (key1685, -1), (key1353, -2), (key1691, 1), (key1691, 1), (key1356, 1), (key1356, 1), (key1482, -1), (key1482, -1)]

theorem rawRowCheck349 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form2 = rawRow349 := by decide +kernel

def row349 : Integer.Sparse Key := [(key1300, -2), (key1306, 2), (key1320, 2), (key1333, -2), (key1353, -2), (key1356, 2), (key1395, 2), (key1401, -2), (key1428, -2), (key1451, 2), (key1474, 2), (key1482, -2), (key1550, -2), (key1563, 2), (key1577, 2), (key1600, -2), (key1685, -2), (key1691, 2), (key1898, 2), (key1901, -2), (key1905, -2), (key1913, 2), (key1922, 2), (key1928, -2)]

theorem rowCheck349 : row349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow349 := by decide +kernel

theorem rowEval349 (x : Key → ℝ) : Integer.Sparse.eval row349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 1, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck349, Integer.Sparse.eval_collectBalanced, rawRowCheck349]

def rawRow350 : Integer.Sparse Key := [(key1550, -1), (key1898, -1), (key1550, 2), (key1558, 1), (key1901, 1), (key1395, -1), (key1558, -1), (key1563, -2), (key1401, 1), (key1563, 1), (key1577, 1), (key1905, 1), (key1577, -2), (key1595, -1), (key1913, -1), (key1300, 1), (key1595, 1), (key1600, 2), (key1306, -1), (key1600, -1), (key1626, -1), (key1922, -1), (key1428, 1), (key1626, 1), (key1635, 1), (key1928, 1), (key1320, -1), (key1635, -1), (key1451, -1), (key1644, -1), (key1333, 1), (key1644, 1), (key1685, 2), (key1474, -1), (key1685, -1), (key1691, -2), (key1353, 1), (key1691, 1), (key1482, 1), (key1694, 1), (key1356, -1), (key1694, -1)]

theorem rawRowCheck350 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form2 = rawRow350 := by decide +kernel

def row350 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck350 : row350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow350 := by decide +kernel

theorem rowEval350 (x : Key → ℝ) : Integer.Sparse.eval row350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, -2, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck350, Integer.Sparse.eval_collectBalanced, rawRowCheck350]

def rawRow351 : Integer.Sparse Key := [(key1898, -1), (key1550, -1), (key1550, 2), (key1901, 1), (key1558, 1), (key1558, -1), (key1395, -1), (key1563, -2), (key1563, 1), (key1401, 1), (key1905, 1), (key1577, 1), (key1577, -2), (key1913, -1), (key1595, -1), (key1595, 1), (key1300, 1), (key1600, 2), (key1600, -1), (key1306, -1), (key1922, -1), (key1626, -1), (key1626, 1), (key1428, 1), (key1928, 1), (key1635, 1), (key1635, -1), (key1320, -1), (key1644, -1), (key1451, -1), (key1644, 1), (key1333, 1), (key1685, 2), (key1685, -1), (key1474, -1), (key1691, -2), (key1691, 1), (key1353, 1), (key1694, 1), (key1482, 1), (key1694, -1), (key1356, -1)]

theorem rawRowCheck351 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form2 = rawRow351 := by decide +kernel

def row351 : Integer.Sparse Key := [(key1300, 1), (key1306, -1), (key1320, -1), (key1333, 1), (key1353, 1), (key1356, -1), (key1395, -1), (key1401, 1), (key1428, 1), (key1451, -1), (key1474, -1), (key1482, 1), (key1550, 1), (key1563, -1), (key1577, -1), (key1600, 1), (key1685, 1), (key1691, -1), (key1898, -1), (key1901, 1), (key1905, 1), (key1913, -1), (key1922, -1), (key1928, 1)]

theorem rowCheck351 : row351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow351 := by decide +kernel

theorem rowEval351 (x : Key → ℝ) : Integer.Sparse.eval row351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 1, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck351, Integer.Sparse.eval_collectBalanced, rawRowCheck351]

end MUB6.Certificate.GramRows

end OAI
