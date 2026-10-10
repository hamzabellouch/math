import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow960 : Integer.Sparse Key := [(key449, -6), (key417, 2), (key327, 2), (key449, 2), (key441, 6), (key396, -2), (key259, -2), (key441, -2), (key408, -2), (key318, -2), (key437, -2), (key387, 2), (key250, 2), (key437, 2)]

theorem rawRowCheck960 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form1 = rawRow960 := by decide +kernel

def row960 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

theorem rowCheck960 : row960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow960 := by decide +kernel

theorem rowEval960 (x : Key → ℝ) : Integer.Sparse.eval row960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck960, Integer.Sparse.eval_collectBalanced, rawRowCheck960]

def rawRow961 : Integer.Sparse Key := [(key449, -6), (key417, 2), (key449, 2), (key327, 2), (key441, 6), (key396, -2), (key441, -2), (key259, -2), (key408, -2), (key437, -2), (key318, -2), (key387, 2), (key437, 2), (key250, 2)]

theorem rawRowCheck961 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form1 = rawRow961 := by decide +kernel

def row961 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

theorem rowCheck961 : row961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow961 := by decide +kernel

theorem rowEval961 (x : Key → ℝ) : Integer.Sparse.eval row961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck961, Integer.Sparse.eval_collectBalanced, rawRowCheck961]

def rawRow962 : Integer.Sparse Key := [(key449, -6), (key449, 2), (key327, 2), (key417, 2), (key441, 6), (key441, -2), (key259, -2), (key396, -2), (key437, -2), (key318, -2), (key408, -2), (key437, 2), (key250, 2), (key387, 2)]

theorem rawRowCheck962 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form1 = rawRow962 := by decide +kernel

def row962 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

theorem rowCheck962 : row962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow962 := by decide +kernel

theorem rowEval962 (x : Key → ℝ) : Integer.Sparse.eval row962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck962, Integer.Sparse.eval_collectBalanced, rawRowCheck962]

def rawRow963 : Integer.Sparse Key := [(key449, -6), (key449, 2), (key417, 2), (key327, 2), (key441, 6), (key441, -2), (key396, -2), (key259, -2), (key437, -2), (key408, -2), (key318, -2), (key437, 2), (key387, 2), (key250, 2)]

theorem rawRowCheck963 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form1 = rawRow963 := by decide +kernel

def row963 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

theorem rowCheck963 : row963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow963 := by decide +kernel

theorem rowEval963 (x : Key → ℝ) : Integer.Sparse.eval row963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck963, Integer.Sparse.eval_collectBalanced, rawRowCheck963]

def rawRow964 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1386, 1), (key1394, 1), (key1541, 1), (key1557, 1), (key1897, 1), (key1900, 1), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, -1), (key1299, -1), (key1568, -1), (key1594, -1), (key1904, -1), (key1912, -1), (key1419, -1), (key1427, -1), (key1617, -1), (key1625, -1), (key1919, -1), (key1921, -1), (key1311, 1), (key1319, 1), (key1617, 1), (key1634, 1), (key1919, 1), (key1927, 1)]

theorem rawRowCheck964 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form2 = rawRow964 := by decide +kernel

def row964 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck964 : row964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow964 := by decide +kernel

theorem rowEval964 (x : Key → ℝ) : Integer.Sparse.eval row964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck964, Integer.Sparse.eval_collectBalanced, rawRowCheck964]

def rawRow965 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1394, 1), (key1386, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1897, 1), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, -1), (key1291, -1), (key1594, -1), (key1568, -1), (key1912, -1), (key1904, -1), (key1427, -1), (key1419, -1), (key1625, -1), (key1617, -1), (key1921, -1), (key1919, -1), (key1319, 1), (key1311, 1), (key1634, 1), (key1617, 1), (key1927, 1), (key1919, 1)]

theorem rawRowCheck965 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form2 = rawRow965 := by decide +kernel

def row965 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck965 : row965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow965 := by decide +kernel

theorem rowEval965 (x : Key → ℝ) : Integer.Sparse.eval row965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck965, Integer.Sparse.eval_collectBalanced, rawRowCheck965]

def rawRow966 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1541, 1), (key1897, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, -1), (key1904, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1617, -1), (key1919, -1), (key1419, -1), (key1921, -1), (key1427, -1), (key1625, -1), (key1617, 1), (key1919, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1634, 1)]

theorem rawRowCheck966 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form2 = rawRow966 := by decide +kernel

def row966 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck966 : row966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow966 := by decide +kernel

theorem rowEval966 (x : Key → ℝ) : Integer.Sparse.eval row966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck966, Integer.Sparse.eval_collectBalanced, rawRowCheck966]

def rawRow967 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1897, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1557, 1), (key1394, 1), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1594, -1), (key1299, -1), (key1919, -1), (key1617, -1), (key1921, -1), (key1419, -1), (key1625, -1), (key1427, -1), (key1919, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1634, 1), (key1319, 1)]

theorem rawRowCheck967 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form2 = rawRow967 := by decide +kernel

def row967 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck967 : row967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow967 := by decide +kernel

theorem rowEval967 (x : Key → ℝ) : Integer.Sparse.eval row967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck967, Integer.Sparse.eval_collectBalanced, rawRowCheck967]

def rawRow968 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1557, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1386, 1), (key1541, 1), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1291, -1), (key1568, -1), (key1625, -1), (key1921, -1), (key1427, -1), (key1919, -1), (key1419, -1), (key1617, -1), (key1634, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1311, 1), (key1617, 1)]

theorem rawRowCheck968 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form2 = rawRow968 := by decide +kernel

def row968 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck968 : row968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow968 := by decide +kernel

theorem rowEval968 (x : Key → ℝ) : Integer.Sparse.eval row968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck968, Integer.Sparse.eval_collectBalanced, rawRowCheck968]

def rawRow969 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1900, 1), (key1557, 1), (key1897, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, -1), (key1594, -1), (key1904, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1921, -1), (key1625, -1), (key1919, -1), (key1427, -1), (key1617, -1), (key1419, -1), (key1927, 1), (key1634, 1), (key1919, 1), (key1319, 1), (key1617, 1), (key1311, 1)]

theorem rawRowCheck969 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form2 = rawRow969 := by decide +kernel

def row969 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck969 : row969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow969 := by decide +kernel

theorem rowEval969 (x : Key → ℝ) : Integer.Sparse.eval row969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck969, Integer.Sparse.eval_collectBalanced, rawRowCheck969]

def rawRow970 : Integer.Sparse Key := [(key1557, -2), (key1557, -2), (key1900, -2), (key1394, 1), (key1394, 1), (key1549, 1), (key1549, 1), (key1897, 1), (key1897, 1), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1904, -1), (key1904, -1), (key1445, -1), (key1445, -1), (key1634, -1), (key1634, -1), (key1927, -1), (key1927, -1), (key1327, 1), (key1327, 1), (key1625, 1), (key1625, 1), (key1921, 1), (key1921, 1)]

theorem rawRowCheck970 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form2 = rawRow970 := by decide +kernel

def row970 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

theorem rowCheck970 : row970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow970 := by decide +kernel

theorem rowEval970 (x : Key → ℝ) : Integer.Sparse.eval row970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck970, Integer.Sparse.eval_collectBalanced, rawRowCheck970]

def rawRow971 : Integer.Sparse Key := [(key1557, -2), (key1900, -2), (key1557, -2), (key1549, 1), (key1897, 1), (key1394, 1), (key1897, 1), (key1394, 1), (key1549, 1), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, -1), (key1904, -1), (key1299, -1), (key1904, -1), (key1299, -1), (key1576, -1), (key1634, -1), (key1927, -1), (key1445, -1), (key1927, -1), (key1445, -1), (key1634, -1), (key1625, 1), (key1921, 1), (key1327, 1), (key1921, 1), (key1327, 1), (key1625, 1)]

theorem rawRowCheck971 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form2 = rawRow971 := by decide +kernel

def row971 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

theorem rowCheck971 : row971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow971 := by decide +kernel

theorem rowEval971 (x : Key → ℝ) : Integer.Sparse.eval row971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck971, Integer.Sparse.eval_collectBalanced, rawRowCheck971]

def rawRow972 : Integer.Sparse Key := [(key1900, -2), (key1557, -2), (key1557, -2), (key1897, 1), (key1549, 1), (key1897, 1), (key1394, 1), (key1549, 1), (key1394, 1), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, -1), (key1576, -1), (key1904, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1927, -1), (key1634, -1), (key1927, -1), (key1445, -1), (key1634, -1), (key1445, -1), (key1921, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1327, 1)]

theorem rawRowCheck972 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form2 = rawRow972 := by decide +kernel

def row972 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

theorem rowCheck972 : row972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow972 := by decide +kernel

theorem rowEval972 (x : Key → ℝ) : Integer.Sparse.eval row972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck972, Integer.Sparse.eval_collectBalanced, rawRowCheck972]

def rawRow973 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1419, 1), (key1427, 1), (key1617, 1), (key1625, 1), (key1919, 1), (key1921, 1), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, -1), (key1319, -1), (key1617, -1), (key1634, -1), (key1919, -1), (key1927, -1), (key1386, -1), (key1394, -1), (key1541, -1), (key1557, -1), (key1897, -1), (key1900, -1), (key1291, 1), (key1299, 1), (key1568, 1), (key1594, 1), (key1904, 1), (key1912, 1)]

theorem rawRowCheck973 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form2 = rawRow973 := by decide +kernel

def row973 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck973 : row973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow973 := by decide +kernel

theorem rowEval973 (x : Key → ℝ) : Integer.Sparse.eval row973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck973, Integer.Sparse.eval_collectBalanced, rawRowCheck973]

def rawRow974 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1427, 1), (key1419, 1), (key1625, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, -1), (key1311, -1), (key1634, -1), (key1617, -1), (key1927, -1), (key1919, -1), (key1394, -1), (key1386, -1), (key1557, -1), (key1541, -1), (key1900, -1), (key1897, -1), (key1299, 1), (key1291, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1904, 1)]

theorem rawRowCheck974 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form2 = rawRow974 := by decide +kernel

def row974 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck974 : row974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow974 := by decide +kernel

theorem rowEval974 (x : Key → ℝ) : Integer.Sparse.eval row974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck974, Integer.Sparse.eval_collectBalanced, rawRowCheck974]

def rawRow975 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1617, 1), (key1919, 1), (key1419, 1), (key1921, 1), (key1427, 1), (key1625, 1), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, -1), (key1919, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1541, -1), (key1897, -1), (key1386, -1), (key1900, -1), (key1394, -1), (key1557, -1), (key1568, 1), (key1904, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1594, 1)]

theorem rawRowCheck975 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form2 = rawRow975 := by decide +kernel

def row975 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck975 : row975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow975 := by decide +kernel

theorem rowEval975 (x : Key → ℝ) : Integer.Sparse.eval row975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form2) x := by
  rw [rowCheck975, Integer.Sparse.eval_collectBalanced, rawRowCheck975]

def rawRow976 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1919, 1), (key1617, 1), (key1921, 1), (key1419, 1), (key1625, 1), (key1427, 1), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1634, -1), (key1319, -1), (key1897, -1), (key1541, -1), (key1900, -1), (key1386, -1), (key1557, -1), (key1394, -1), (key1904, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1594, 1), (key1299, 1)]

theorem rawRowCheck976 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form2 = rawRow976 := by decide +kernel

def row976 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck976 : row976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow976 := by decide +kernel

theorem rowEval976 (x : Key → ℝ) : Integer.Sparse.eval row976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck976, Integer.Sparse.eval_collectBalanced, rawRowCheck976]

def rawRow977 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1625, 1), (key1921, 1), (key1427, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1311, -1), (key1617, -1), (key1557, -1), (key1900, -1), (key1394, -1), (key1897, -1), (key1386, -1), (key1541, -1), (key1594, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1291, 1), (key1568, 1)]

theorem rawRowCheck977 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form2 = rawRow977 := by decide +kernel

def row977 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck977 : row977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow977 := by decide +kernel

theorem rowEval977 (x : Key → ℝ) : Integer.Sparse.eval row977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck977, Integer.Sparse.eval_collectBalanced, rawRowCheck977]

def rawRow978 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1921, 1), (key1625, 1), (key1919, 1), (key1427, 1), (key1617, 1), (key1419, 1), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, -1), (key1634, -1), (key1919, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1900, -1), (key1557, -1), (key1897, -1), (key1394, -1), (key1541, -1), (key1386, -1), (key1912, 1), (key1594, 1), (key1904, 1), (key1299, 1), (key1568, 1), (key1291, 1)]

theorem rawRowCheck978 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form2 = rawRow978 := by decide +kernel

def row978 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck978 : row978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow978 := by decide +kernel

theorem rowEval978 (x : Key → ℝ) : Integer.Sparse.eval row978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck978, Integer.Sparse.eval_collectBalanced, rawRowCheck978]

def rawRow979 : Integer.Sparse Key := [(key1625, -2), (key1684, -2), (key1921, -2), (key1427, 1), (key1473, 1), (key1576, 1), (key1682, 1), (key1904, 1), (key1919, 1), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, -1), (key1352, -1), (key1549, -1), (key1682, -1), (key1897, -1), (key1919, -1), (key1445, -1), (key1481, -1), (key1594, -1), (key1690, -1), (key1912, -1), (key1927, -1), (key1327, 1), (key1355, 1), (key1557, 1), (key1684, 1), (key1900, 1), (key1921, 1)]

theorem rawRowCheck979 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form2 = rawRow979 := by decide +kernel

def row979 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck979 : row979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow979 := by decide +kernel

theorem rowEval979 (x : Key → ℝ) : Integer.Sparse.eval row979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck979, Integer.Sparse.eval_collectBalanced, rawRowCheck979]

def rawRow980 : Integer.Sparse Key := [(key1684, -2), (key1625, -2), (key1921, -2), (key1473, 1), (key1427, 1), (key1682, 1), (key1576, 1), (key1919, 1), (key1904, 1), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, -1), (key1319, -1), (key1682, -1), (key1549, -1), (key1919, -1), (key1897, -1), (key1481, -1), (key1445, -1), (key1690, -1), (key1594, -1), (key1927, -1), (key1912, -1), (key1355, 1), (key1327, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1900, 1)]

theorem rawRowCheck980 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form2 = rawRow980 := by decide +kernel

def row980 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck980 : row980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow980 := by decide +kernel

theorem rowEval980 (x : Key → ℝ) : Integer.Sparse.eval row980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck980, Integer.Sparse.eval_collectBalanced, rawRowCheck980]

def rawRow981 : Integer.Sparse Key := [(key1625, -2), (key1921, -2), (key1684, -2), (key1576, 1), (key1904, 1), (key1427, 1), (key1919, 1), (key1473, 1), (key1682, 1), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, -1), (key1897, -1), (key1319, -1), (key1919, -1), (key1352, -1), (key1682, -1), (key1594, -1), (key1912, -1), (key1445, -1), (key1927, -1), (key1481, -1), (key1690, -1), (key1557, 1), (key1900, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1684, 1)]

theorem rawRowCheck981 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form2 = rawRow981 := by decide +kernel

def row981 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck981 : row981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow981 := by decide +kernel

theorem rowEval981 (x : Key → ℝ) : Integer.Sparse.eval row981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck981, Integer.Sparse.eval_collectBalanced, rawRowCheck981]

def rawRow982 : Integer.Sparse Key := [(key1921, -2), (key1625, -2), (key1684, -2), (key1904, 1), (key1576, 1), (key1919, 1), (key1427, 1), (key1682, 1), (key1473, 1), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, -1), (key1549, -1), (key1919, -1), (key1319, -1), (key1682, -1), (key1352, -1), (key1912, -1), (key1594, -1), (key1927, -1), (key1445, -1), (key1690, -1), (key1481, -1), (key1900, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1684, 1), (key1355, 1)]

theorem rawRowCheck982 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form2 = rawRow982 := by decide +kernel

def row982 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck982 : row982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow982 := by decide +kernel

theorem rowEval982 (x : Key → ℝ) : Integer.Sparse.eval row982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck982, Integer.Sparse.eval_collectBalanced, rawRowCheck982]

def rawRow983 : Integer.Sparse Key := [(key1684, -2), (key1921, -2), (key1625, -2), (key1682, 1), (key1919, 1), (key1473, 1), (key1904, 1), (key1427, 1), (key1576, 1), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, -1), (key1919, -1), (key1352, -1), (key1897, -1), (key1319, -1), (key1549, -1), (key1690, -1), (key1927, -1), (key1481, -1), (key1912, -1), (key1445, -1), (key1594, -1), (key1684, 1), (key1921, 1), (key1355, 1), (key1900, 1), (key1327, 1), (key1557, 1)]

theorem rawRowCheck983 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form2 = rawRow983 := by decide +kernel

def row983 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck983 : row983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow983 := by decide +kernel

theorem rowEval983 (x : Key → ℝ) : Integer.Sparse.eval row983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck983, Integer.Sparse.eval_collectBalanced, rawRowCheck983]

def rawRow984 : Integer.Sparse Key := [(key1921, -2), (key1684, -2), (key1625, -2), (key1919, 1), (key1682, 1), (key1904, 1), (key1473, 1), (key1576, 1), (key1427, 1), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, -1), (key1682, -1), (key1897, -1), (key1352, -1), (key1549, -1), (key1319, -1), (key1927, -1), (key1690, -1), (key1912, -1), (key1481, -1), (key1594, -1), (key1445, -1), (key1921, 1), (key1684, 1), (key1900, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

theorem rawRowCheck984 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form2 = rawRow984 := by decide +kernel

def row984 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

theorem rowCheck984 : row984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow984 := by decide +kernel

theorem rowEval984 (x : Key → ℝ) : Integer.Sparse.eval row984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck984, Integer.Sparse.eval_collectBalanced, rawRowCheck984]

def rawRow985 : Integer.Sparse Key := [(key1594, -2), (key1594, -2), (key1912, -2), (key1445, 1), (key1445, 1), (key1634, 1), (key1634, 1), (key1927, 1), (key1927, 1), (key1557, 2), (key1557, 2), (key1900, 2), (key1327, -1), (key1327, -1), (key1625, -1), (key1625, -1), (key1921, -1), (key1921, -1), (key1394, -1), (key1394, -1), (key1549, -1), (key1549, -1), (key1897, -1), (key1897, -1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1904, 1), (key1904, 1)]

theorem rawRowCheck985 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow985 := by decide +kernel

def row985 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck985 : row985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow985 := by decide +kernel

theorem rowEval985 (x : Key → ℝ) : Integer.Sparse.eval row985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck985, Integer.Sparse.eval_collectBalanced, rawRowCheck985]

def rawRow986 : Integer.Sparse Key := [(key1594, -2), (key1912, -2), (key1594, -2), (key1634, 1), (key1927, 1), (key1445, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1557, 2), (key1900, 2), (key1557, 2), (key1625, -1), (key1921, -1), (key1327, -1), (key1921, -1), (key1327, -1), (key1625, -1), (key1549, -1), (key1897, -1), (key1394, -1), (key1897, -1), (key1394, -1), (key1549, -1), (key1576, 1), (key1904, 1), (key1299, 1), (key1904, 1), (key1299, 1), (key1576, 1)]

theorem rawRowCheck986 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow986 := by decide +kernel

def row986 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck986 : row986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow986 := by decide +kernel

theorem rowEval986 (x : Key → ℝ) : Integer.Sparse.eval row986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck986, Integer.Sparse.eval_collectBalanced, rawRowCheck986]

def rawRow987 : Integer.Sparse Key := [(key1912, -2), (key1594, -2), (key1594, -2), (key1927, 1), (key1634, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1900, 2), (key1557, 2), (key1557, 2), (key1921, -1), (key1625, -1), (key1921, -1), (key1327, -1), (key1625, -1), (key1327, -1), (key1897, -1), (key1549, -1), (key1897, -1), (key1394, -1), (key1549, -1), (key1394, -1), (key1904, 1), (key1576, 1), (key1904, 1), (key1299, 1), (key1576, 1), (key1299, 1)]

theorem rawRowCheck987 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow987 := by decide +kernel

def row987 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck987 : row987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow987 := by decide +kernel

theorem rowEval987 (x : Key → ℝ) : Integer.Sparse.eval row987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck987, Integer.Sparse.eval_collectBalanced, rawRowCheck987]

def rawRow988 : Integer.Sparse Key := [(key1634, -2), (key1690, -2), (key1927, -2), (key1445, 1), (key1481, 1), (key1594, 1), (key1690, 1), (key1912, 1), (key1927, 1), (key1625, 2), (key1684, 2), (key1921, 2), (key1327, -1), (key1355, -1), (key1557, -1), (key1684, -1), (key1900, -1), (key1921, -1), (key1427, -1), (key1473, -1), (key1576, -1), (key1682, -1), (key1904, -1), (key1919, -1), (key1319, 1), (key1352, 1), (key1549, 1), (key1682, 1), (key1897, 1), (key1919, 1)]

theorem rawRowCheck988 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form2 = rawRow988 := by decide +kernel

def row988 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck988 : row988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow988 := by decide +kernel

theorem rowEval988 (x : Key → ℝ) : Integer.Sparse.eval row988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck988, Integer.Sparse.eval_collectBalanced, rawRowCheck988]

def rawRow989 : Integer.Sparse Key := [(key1690, -2), (key1634, -2), (key1927, -2), (key1481, 1), (key1445, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1912, 1), (key1684, 2), (key1625, 2), (key1921, 2), (key1355, -1), (key1327, -1), (key1684, -1), (key1557, -1), (key1921, -1), (key1900, -1), (key1473, -1), (key1427, -1), (key1682, -1), (key1576, -1), (key1919, -1), (key1904, -1), (key1352, 1), (key1319, 1), (key1682, 1), (key1549, 1), (key1919, 1), (key1897, 1)]

theorem rawRowCheck989 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form2 = rawRow989 := by decide +kernel

def row989 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck989 : row989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow989 := by decide +kernel

theorem rowEval989 (x : Key → ℝ) : Integer.Sparse.eval row989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck989, Integer.Sparse.eval_collectBalanced, rawRowCheck989]

def rawRow990 : Integer.Sparse Key := [(key1634, -2), (key1927, -2), (key1690, -2), (key1594, 1), (key1912, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1625, 2), (key1921, 2), (key1684, 2), (key1557, -1), (key1900, -1), (key1327, -1), (key1921, -1), (key1355, -1), (key1684, -1), (key1576, -1), (key1904, -1), (key1427, -1), (key1919, -1), (key1473, -1), (key1682, -1), (key1549, 1), (key1897, 1), (key1319, 1), (key1919, 1), (key1352, 1), (key1682, 1)]

theorem rawRowCheck990 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form2 = rawRow990 := by decide +kernel

def row990 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck990 : row990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow990 := by decide +kernel

theorem rowEval990 (x : Key → ℝ) : Integer.Sparse.eval row990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck990, Integer.Sparse.eval_collectBalanced, rawRowCheck990]

def rawRow991 : Integer.Sparse Key := [(key1927, -2), (key1634, -2), (key1690, -2), (key1912, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1690, 1), (key1481, 1), (key1921, 2), (key1625, 2), (key1684, 2), (key1900, -1), (key1557, -1), (key1921, -1), (key1327, -1), (key1684, -1), (key1355, -1), (key1904, -1), (key1576, -1), (key1919, -1), (key1427, -1), (key1682, -1), (key1473, -1), (key1897, 1), (key1549, 1), (key1919, 1), (key1319, 1), (key1682, 1), (key1352, 1)]

theorem rawRowCheck991 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form2 = rawRow991 := by decide +kernel

def row991 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

theorem rowCheck991 : row991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow991 := by decide +kernel

theorem rowEval991 (x : Key → ℝ) : Integer.Sparse.eval row991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck991, Integer.Sparse.eval_collectBalanced, rawRowCheck991]

end MUB6.Certificate.GramRows

end OAI
