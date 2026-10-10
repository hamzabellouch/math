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
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3200 : Integer.Sparse Key := [(key3058, -2), (key3076, -2), (key3115, -2), (key3058, 2), (key3075, 2), (key3113, 2), (key3053, 2), (key3068, 2), (key3105, 2), (key3053, -6), (key3047, -2), (key3061, -2), (key3096, -2), (key2679, 6)]

theorem rawRowCheck3200 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form6 = rawRow3200 := by decide +kernel

def row3200 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

theorem rowCheck3200 : row3200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3200 := by decide +kernel

theorem rowEval3200 (x : Key → ℝ) : Integer.Sparse.eval row3200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3200, Integer.Sparse.eval_collectBalanced, rawRowCheck3200]

def rawRow3201 : Integer.Sparse Key := [(key3076, -2), (key3058, -2), (key3115, -2), (key3075, 2), (key3058, 2), (key3113, 2), (key3068, 2), (key3053, 2), (key3105, 2), (key3053, -6), (key3061, -2), (key3047, -2), (key3096, -2), (key2679, 6)]

theorem rawRowCheck3201 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form6 = rawRow3201 := by decide +kernel

def row3201 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

theorem rowCheck3201 : row3201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3201 := by decide +kernel

theorem rowEval3201 (x : Key → ℝ) : Integer.Sparse.eval row3201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3201, Integer.Sparse.eval_collectBalanced, rawRowCheck3201]

def rawRow3202 : Integer.Sparse Key := [(key3058, -2), (key3115, -2), (key3076, -2), (key3058, 2), (key3113, 2), (key3075, 2), (key3053, 2), (key3105, 2), (key3068, 2), (key3053, -6), (key3047, -2), (key3096, -2), (key3061, -2), (key2679, 6)]

theorem rawRowCheck3202 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form6 = rawRow3202 := by decide +kernel

def row3202 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

theorem rowCheck3202 : row3202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3202 := by decide +kernel

theorem rowEval3202 (x : Key → ℝ) : Integer.Sparse.eval row3202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck3202, Integer.Sparse.eval_collectBalanced, rawRowCheck3202]

def rawRow3203 : Integer.Sparse Key := [(key3115, -2), (key3058, -2), (key3076, -2), (key3113, 2), (key3058, 2), (key3075, 2), (key3105, 2), (key3053, 2), (key3068, 2), (key3053, -6), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, 6)]

theorem rawRowCheck3203 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form6 = rawRow3203 := by decide +kernel

def row3203 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

theorem rowCheck3203 : row3203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3203 := by decide +kernel

theorem rowEval3203 (x : Key → ℝ) : Integer.Sparse.eval row3203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3203, Integer.Sparse.eval_collectBalanced, rawRowCheck3203]

def rawRow3204 : Integer.Sparse Key := [(key3076, -2), (key3115, -2), (key3058, -2), (key3075, 2), (key3113, 2), (key3058, 2), (key3068, 2), (key3105, 2), (key3053, 2), (key3053, -6), (key3061, -2), (key3096, -2), (key3047, -2), (key3047, 6)]

theorem rawRowCheck3204 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form6 = rawRow3204 := by decide +kernel

def row3204 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

theorem rowCheck3204 : row3204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3204 := by decide +kernel

theorem rowEval3204 (x : Key → ℝ) : Integer.Sparse.eval row3204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck3204, Integer.Sparse.eval_collectBalanced, rawRowCheck3204]

def rawRow3205 : Integer.Sparse Key := [(key3115, -2), (key3076, -2), (key3058, -2), (key3113, 2), (key3075, 2), (key3058, 2), (key3105, 2), (key3068, 2), (key3053, 2), (key3053, -6), (key3096, -2), (key3061, -2), (key3047, -2), (key3047, 6)]

theorem rawRowCheck3205 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form6 = rawRow3205 := by decide +kernel

def row3205 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

theorem rowCheck3205 : row3205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3205 := by decide +kernel

theorem rowEval3205 (x : Key → ℝ) : Integer.Sparse.eval row3205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck3205, Integer.Sparse.eval_collectBalanced, rawRowCheck3205]

def rawRow3206 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1445, -2), (key1386, 1), (key1394, 1), (key1419, 1), (key1473, 1), (key1445, 1), (key1481, 1), (key1568, 2), (key1576, 2), (key1594, 2), (key1291, -1), (key1299, -1), (key1568, -1), (key1904, -1), (key1594, -1), (key1912, -1), (key1541, -1), (key1549, -1), (key1617, -1), (key1682, -1), (key1634, -1), (key1690, -1), (key1311, 1), (key1319, 1), (key1617, 1), (key1919, 1), (key1634, 1), (key1927, 1)]

theorem rawRowCheck3206 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form7 = rawRow3206 := by decide +kernel

def row3206 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

theorem rowCheck3206 : row3206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3206 := by decide +kernel

theorem rowEval3206 (x : Key → ℝ) : Integer.Sparse.eval row3206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3206, Integer.Sparse.eval_collectBalanced, rawRowCheck3206]

def rawRow3207 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1445, -2), (key1394, 1), (key1386, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1445, 1), (key1576, 2), (key1568, 2), (key1594, 2), (key1299, -1), (key1291, -1), (key1904, -1), (key1568, -1), (key1912, -1), (key1594, -1), (key1549, -1), (key1541, -1), (key1682, -1), (key1617, -1), (key1690, -1), (key1634, -1), (key1319, 1), (key1311, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1634, 1)]

theorem rawRowCheck3207 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form7 = rawRow3207 := by decide +kernel

def row3207 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

theorem rowCheck3207 : row3207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3207 := by decide +kernel

theorem rowEval3207 (x : Key → ℝ) : Integer.Sparse.eval row3207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3207, Integer.Sparse.eval_collectBalanced, rawRowCheck3207]

def rawRow3208 : Integer.Sparse Key := [(key1419, -2), (key1445, -2), (key1427, -2), (key1419, 1), (key1445, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1568, 2), (key1594, 2), (key1576, 2), (key1568, -1), (key1594, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1617, -1), (key1634, -1), (key1541, -1), (key1690, -1), (key1549, -1), (key1682, -1), (key1617, 1), (key1634, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1919, 1)]

theorem rawRowCheck3208 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form7 = rawRow3208 := by decide +kernel

def row3208 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

theorem rowCheck3208 : row3208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3208 := by decide +kernel

theorem rowEval3208 (x : Key → ℝ) : Integer.Sparse.eval row3208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3208, Integer.Sparse.eval_collectBalanced, rawRowCheck3208]

def rawRow3209 : Integer.Sparse Key := [(key1445, -2), (key1419, -2), (key1427, -2), (key1445, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1473, 1), (key1394, 1), (key1594, 2), (key1568, 2), (key1576, 2), (key1594, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1904, -1), (key1299, -1), (key1634, -1), (key1617, -1), (key1690, -1), (key1541, -1), (key1682, -1), (key1549, -1), (key1634, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1919, 1), (key1319, 1)]

theorem rawRowCheck3209 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form7 = rawRow3209 := by decide +kernel

def row3209 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

theorem rowCheck3209 : row3209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3209 := by decide +kernel

theorem rowEval3209 (x : Key → ℝ) : Integer.Sparse.eval row3209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3209, Integer.Sparse.eval_collectBalanced, rawRowCheck3209]

def rawRow3210 : Integer.Sparse Key := [(key1427, -2), (key1445, -2), (key1419, -2), (key1473, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1386, 1), (key1419, 1), (key1576, 2), (key1594, 2), (key1568, 2), (key1904, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1291, -1), (key1568, -1), (key1682, -1), (key1690, -1), (key1549, -1), (key1634, -1), (key1541, -1), (key1617, -1), (key1919, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1311, 1), (key1617, 1)]

theorem rawRowCheck3210 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form7 = rawRow3210 := by decide +kernel

def row3210 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

theorem rowCheck3210 : row3210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3210 := by decide +kernel

theorem rowEval3210 (x : Key → ℝ) : Integer.Sparse.eval row3210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3210, Integer.Sparse.eval_collectBalanced, rawRowCheck3210]

def rawRow3211 : Integer.Sparse Key := [(key1445, -2), (key1427, -2), (key1419, -2), (key1481, 1), (key1473, 1), (key1445, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1594, 2), (key1576, 2), (key1568, 2), (key1912, -1), (key1904, -1), (key1594, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1690, -1), (key1682, -1), (key1634, -1), (key1549, -1), (key1617, -1), (key1541, -1), (key1927, 1), (key1919, 1), (key1634, 1), (key1319, 1), (key1617, 1), (key1311, 1)]

theorem rawRowCheck3211 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form7 = rawRow3211 := by decide +kernel

def row3211 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

theorem rowCheck3211 : row3211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3211 := by decide +kernel

theorem rowEval3211 (x : Key → ℝ) : Integer.Sparse.eval row3211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3211, Integer.Sparse.eval_collectBalanced, rawRowCheck3211]

def rawRow3212 : Integer.Sparse Key := [(key1473, -2), (key1473, -2), (key1481, -2), (key1394, 1), (key1394, 1), (key1427, 1), (key1427, 1), (key1445, 1), (key1445, 1), (key1904, 2), (key1904, 2), (key1912, 2), (key1299, -1), (key1299, -1), (key1576, -1), (key1576, -1), (key1594, -1), (key1594, -1), (key1897, -1), (key1897, -1), (key1919, -1), (key1919, -1), (key1927, -1), (key1927, -1), (key1352, 1), (key1352, 1), (key1682, 1), (key1682, 1), (key1690, 1), (key1690, 1)]

theorem rawRowCheck3212 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form7 = rawRow3212 := by decide +kernel

def row3212 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

theorem rowCheck3212 : row3212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3212 := by decide +kernel

theorem rowEval3212 (x : Key → ℝ) : Integer.Sparse.eval row3212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3212, Integer.Sparse.eval_collectBalanced, rawRowCheck3212]

def rawRow3213 : Integer.Sparse Key := [(key1473, -2), (key1481, -2), (key1473, -2), (key1427, 1), (key1445, 1), (key1394, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1904, 2), (key1912, 2), (key1904, 2), (key1576, -1), (key1594, -1), (key1299, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1919, -1), (key1927, -1), (key1897, -1), (key1927, -1), (key1897, -1), (key1919, -1), (key1682, 1), (key1690, 1), (key1352, 1), (key1690, 1), (key1352, 1), (key1682, 1)]

theorem rawRowCheck3213 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form7 = rawRow3213 := by decide +kernel

def row3213 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

theorem rowCheck3213 : row3213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3213 := by decide +kernel

theorem rowEval3213 (x : Key → ℝ) : Integer.Sparse.eval row3213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3213, Integer.Sparse.eval_collectBalanced, rawRowCheck3213]

def rawRow3214 : Integer.Sparse Key := [(key1481, -2), (key1473, -2), (key1473, -2), (key1445, 1), (key1427, 1), (key1445, 1), (key1394, 1), (key1427, 1), (key1394, 1), (key1912, 2), (key1904, 2), (key1904, 2), (key1594, -1), (key1576, -1), (key1594, -1), (key1299, -1), (key1576, -1), (key1299, -1), (key1927, -1), (key1919, -1), (key1927, -1), (key1897, -1), (key1919, -1), (key1897, -1), (key1690, 1), (key1682, 1), (key1690, 1), (key1352, 1), (key1682, 1), (key1352, 1)]

theorem rawRowCheck3214 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form7 = rawRow3214 := by decide +kernel

def row3214 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

theorem rowCheck3214 : row3214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3214 := by decide +kernel

theorem rowEval3214 (x : Key → ℝ) : Integer.Sparse.eval row3214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3214, Integer.Sparse.eval_collectBalanced, rawRowCheck3214]

def rawRow3215 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1594, -2), (key1541, 1), (key1549, 1), (key1617, 1), (key1682, 1), (key1634, 1), (key1690, 1), (key1419, 2), (key1427, 2), (key1445, 2), (key1311, -1), (key1319, -1), (key1617, -1), (key1919, -1), (key1634, -1), (key1927, -1), (key1386, -1), (key1394, -1), (key1419, -1), (key1473, -1), (key1445, -1), (key1481, -1), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1)]

theorem rawRowCheck3215 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form7 = rawRow3215 := by decide +kernel

def row3215 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

theorem rowCheck3215 : row3215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3215 := by decide +kernel

theorem rowEval3215 (x : Key → ℝ) : Integer.Sparse.eval row3215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3215, Integer.Sparse.eval_collectBalanced, rawRowCheck3215]

def rawRow3216 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1594, -2), (key1549, 1), (key1541, 1), (key1682, 1), (key1617, 1), (key1690, 1), (key1634, 1), (key1427, 2), (key1419, 2), (key1445, 2), (key1319, -1), (key1311, -1), (key1919, -1), (key1617, -1), (key1927, -1), (key1634, -1), (key1394, -1), (key1386, -1), (key1473, -1), (key1419, -1), (key1481, -1), (key1445, -1), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1)]

theorem rawRowCheck3216 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form7 = rawRow3216 := by decide +kernel

def row3216 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

theorem rowCheck3216 : row3216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3216 := by decide +kernel

theorem rowEval3216 (x : Key → ℝ) : Integer.Sparse.eval row3216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3216, Integer.Sparse.eval_collectBalanced, rawRowCheck3216]

def rawRow3217 : Integer.Sparse Key := [(key1568, -2), (key1594, -2), (key1576, -2), (key1617, 1), (key1634, 1), (key1541, 1), (key1690, 1), (key1549, 1), (key1682, 1), (key1419, 2), (key1445, 2), (key1427, 2), (key1617, -1), (key1634, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1419, -1), (key1445, -1), (key1386, -1), (key1481, -1), (key1394, -1), (key1473, -1), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1)]

theorem rawRowCheck3217 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form7 = rawRow3217 := by decide +kernel

def row3217 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

theorem rowCheck3217 : row3217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3217 := by decide +kernel

theorem rowEval3217 (x : Key → ℝ) : Integer.Sparse.eval row3217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3217, Integer.Sparse.eval_collectBalanced, rawRowCheck3217]

def rawRow3218 : Integer.Sparse Key := [(key1594, -2), (key1568, -2), (key1576, -2), (key1634, 1), (key1617, 1), (key1690, 1), (key1541, 1), (key1682, 1), (key1549, 1), (key1445, 2), (key1419, 2), (key1427, 2), (key1634, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1919, -1), (key1319, -1), (key1445, -1), (key1419, -1), (key1481, -1), (key1386, -1), (key1473, -1), (key1394, -1), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1)]

theorem rawRowCheck3218 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form7 = rawRow3218 := by decide +kernel

def row3218 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

theorem rowCheck3218 : row3218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3218 := by decide +kernel

theorem rowEval3218 (x : Key → ℝ) : Integer.Sparse.eval row3218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3218, Integer.Sparse.eval_collectBalanced, rawRowCheck3218]

def rawRow3219 : Integer.Sparse Key := [(key1576, -2), (key1594, -2), (key1568, -2), (key1682, 1), (key1690, 1), (key1549, 1), (key1634, 1), (key1541, 1), (key1617, 1), (key1427, 2), (key1445, 2), (key1419, 2), (key1919, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1311, -1), (key1617, -1), (key1473, -1), (key1481, -1), (key1394, -1), (key1445, -1), (key1386, -1), (key1419, -1), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1)]

theorem rawRowCheck3219 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form7 = rawRow3219 := by decide +kernel

def row3219 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

theorem rowCheck3219 : row3219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3219 := by decide +kernel

theorem rowEval3219 (x : Key → ℝ) : Integer.Sparse.eval row3219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3219, Integer.Sparse.eval_collectBalanced, rawRowCheck3219]

def rawRow3220 : Integer.Sparse Key := [(key1594, -2), (key1576, -2), (key1568, -2), (key1690, 1), (key1682, 1), (key1634, 1), (key1549, 1), (key1617, 1), (key1541, 1), (key1445, 2), (key1427, 2), (key1419, 2), (key1927, -1), (key1919, -1), (key1634, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1481, -1), (key1473, -1), (key1445, -1), (key1394, -1), (key1419, -1), (key1386, -1), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1)]

theorem rawRowCheck3220 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form7 = rawRow3220 := by decide +kernel

def row3220 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

theorem rowCheck3220 : row3220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3220 := by decide +kernel

theorem rowEval3220 (x : Key → ℝ) : Integer.Sparse.eval row3220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3220, Integer.Sparse.eval_collectBalanced, rawRowCheck3220]

def rawRow3221 : Integer.Sparse Key := [(key1682, -2), (key1684, -2), (key1690, -2), (key1549, 1), (key1557, 1), (key1576, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1919, 2), (key1921, 2), (key1927, 2), (key1319, -1), (key1327, -1), (key1427, -1), (key1625, -1), (key1445, -1), (key1634, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1921, -1), (key1912, -1), (key1927, -1), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1)]

theorem rawRowCheck3221 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form7 = rawRow3221 := by decide +kernel

def row3221 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

theorem rowCheck3221 : row3221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3221 := by decide +kernel

theorem rowEval3221 (x : Key → ℝ) : Integer.Sparse.eval row3221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3221, Integer.Sparse.eval_collectBalanced, rawRowCheck3221]

def rawRow3222 : Integer.Sparse Key := [(key1684, -2), (key1682, -2), (key1690, -2), (key1557, 1), (key1549, 1), (key1625, 1), (key1576, 1), (key1634, 1), (key1594, 1), (key1921, 2), (key1919, 2), (key1927, 2), (key1327, -1), (key1319, -1), (key1625, -1), (key1427, -1), (key1634, -1), (key1445, -1), (key1900, -1), (key1897, -1), (key1921, -1), (key1904, -1), (key1927, -1), (key1912, -1), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1)]

theorem rawRowCheck3222 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form7 = rawRow3222 := by decide +kernel

def row3222 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

theorem rowCheck3222 : row3222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3222 := by decide +kernel

theorem rowEval3222 (x : Key → ℝ) : Integer.Sparse.eval row3222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3222, Integer.Sparse.eval_collectBalanced, rawRowCheck3222]

def rawRow3223 : Integer.Sparse Key := [(key1682, -2), (key1690, -2), (key1684, -2), (key1576, 1), (key1594, 1), (key1549, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1919, 2), (key1927, 2), (key1921, 2), (key1427, -1), (key1445, -1), (key1319, -1), (key1634, -1), (key1327, -1), (key1625, -1), (key1904, -1), (key1912, -1), (key1897, -1), (key1927, -1), (key1900, -1), (key1921, -1), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1)]

theorem rawRowCheck3223 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form7 = rawRow3223 := by decide +kernel

def row3223 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

theorem rowCheck3223 : row3223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3223 := by decide +kernel

theorem rowEval3223 (x : Key → ℝ) : Integer.Sparse.eval row3223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3223, Integer.Sparse.eval_collectBalanced, rawRowCheck3223]

def rawRow3224 : Integer.Sparse Key := [(key1690, -2), (key1682, -2), (key1684, -2), (key1594, 1), (key1576, 1), (key1634, 1), (key1549, 1), (key1625, 1), (key1557, 1), (key1927, 2), (key1919, 2), (key1921, 2), (key1445, -1), (key1427, -1), (key1634, -1), (key1319, -1), (key1625, -1), (key1327, -1), (key1912, -1), (key1904, -1), (key1927, -1), (key1897, -1), (key1921, -1), (key1900, -1), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1)]

theorem rawRowCheck3224 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form7 = rawRow3224 := by decide +kernel

def row3224 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

theorem rowCheck3224 : row3224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3224 := by decide +kernel

theorem rowEval3224 (x : Key → ℝ) : Integer.Sparse.eval row3224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3224, Integer.Sparse.eval_collectBalanced, rawRowCheck3224]

def rawRow3225 : Integer.Sparse Key := [(key1684, -2), (key1690, -2), (key1682, -2), (key1625, 1), (key1634, 1), (key1557, 1), (key1594, 1), (key1549, 1), (key1576, 1), (key1921, 2), (key1927, 2), (key1919, 2), (key1625, -1), (key1634, -1), (key1327, -1), (key1445, -1), (key1319, -1), (key1427, -1), (key1921, -1), (key1927, -1), (key1900, -1), (key1912, -1), (key1897, -1), (key1904, -1), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1)]

theorem rawRowCheck3225 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form7 = rawRow3225 := by decide +kernel

def row3225 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

theorem rowCheck3225 : row3225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3225 := by decide +kernel

theorem rowEval3225 (x : Key → ℝ) : Integer.Sparse.eval row3225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3225, Integer.Sparse.eval_collectBalanced, rawRowCheck3225]

def rawRow3226 : Integer.Sparse Key := [(key1690, -2), (key1684, -2), (key1682, -2), (key1634, 1), (key1625, 1), (key1594, 1), (key1557, 1), (key1576, 1), (key1549, 1), (key1927, 2), (key1921, 2), (key1919, 2), (key1634, -1), (key1625, -1), (key1445, -1), (key1327, -1), (key1427, -1), (key1319, -1), (key1927, -1), (key1921, -1), (key1912, -1), (key1900, -1), (key1904, -1), (key1897, -1), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1)]

theorem rawRowCheck3226 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form7 = rawRow3226 := by decide +kernel

def row3226 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

theorem rowCheck3226 : row3226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3226 := by decide +kernel

theorem rowEval3226 (x : Key → ℝ) : Integer.Sparse.eval row3226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3226, Integer.Sparse.eval_collectBalanced, rawRowCheck3226]

def rawRow3227 : Integer.Sparse Key := [(key1904, -2), (key1904, -2), (key1912, -2), (key1897, 1), (key1897, 1), (key1919, 1), (key1919, 1), (key1927, 1), (key1927, 1), (key1473, 2), (key1473, 2), (key1481, 2), (key1352, -1), (key1352, -1), (key1682, -1), (key1682, -1), (key1690, -1), (key1690, -1), (key1394, -1), (key1394, -1), (key1427, -1), (key1427, -1), (key1445, -1), (key1445, -1), (key1299, 1), (key1299, 1), (key1576, 1), (key1576, 1), (key1594, 1), (key1594, 1)]

theorem rawRowCheck3227 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form7 = rawRow3227 := by decide +kernel

def row3227 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

theorem rowCheck3227 : row3227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3227 := by decide +kernel

theorem rowEval3227 (x : Key → ℝ) : Integer.Sparse.eval row3227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3227, Integer.Sparse.eval_collectBalanced, rawRowCheck3227]

def rawRow3228 : Integer.Sparse Key := [(key1904, -2), (key1912, -2), (key1904, -2), (key1919, 1), (key1927, 1), (key1897, 1), (key1927, 1), (key1897, 1), (key1919, 1), (key1473, 2), (key1481, 2), (key1473, 2), (key1682, -1), (key1690, -1), (key1352, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1427, -1), (key1445, -1), (key1394, -1), (key1445, -1), (key1394, -1), (key1427, -1), (key1576, 1), (key1594, 1), (key1299, 1), (key1594, 1), (key1299, 1), (key1576, 1)]

theorem rawRowCheck3228 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form7 = rawRow3228 := by decide +kernel

def row3228 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

theorem rowCheck3228 : row3228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3228 := by decide +kernel

theorem rowEval3228 (x : Key → ℝ) : Integer.Sparse.eval row3228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3228, Integer.Sparse.eval_collectBalanced, rawRowCheck3228]

def rawRow3229 : Integer.Sparse Key := [(key1912, -2), (key1904, -2), (key1904, -2), (key1927, 1), (key1919, 1), (key1927, 1), (key1897, 1), (key1919, 1), (key1897, 1), (key1481, 2), (key1473, 2), (key1473, 2), (key1690, -1), (key1682, -1), (key1690, -1), (key1352, -1), (key1682, -1), (key1352, -1), (key1445, -1), (key1427, -1), (key1445, -1), (key1394, -1), (key1427, -1), (key1394, -1), (key1594, 1), (key1576, 1), (key1594, 1), (key1299, 1), (key1576, 1), (key1299, 1)]

theorem rawRowCheck3229 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form7 = rawRow3229 := by decide +kernel

def row3229 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

theorem rowCheck3229 : row3229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3229 := by decide +kernel

theorem rowEval3229 (x : Key → ℝ) : Integer.Sparse.eval row3229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3229, Integer.Sparse.eval_collectBalanced, rawRowCheck3229]

def rawRow3230 : Integer.Sparse Key := [(key1919, -2), (key1921, -2), (key1927, -2), (key1897, 1), (key1900, 1), (key1904, 1), (key1921, 1), (key1912, 1), (key1927, 1), (key1682, 2), (key1684, 2), (key1690, 2), (key1352, -1), (key1355, -1), (key1473, -1), (key1684, -1), (key1481, -1), (key1690, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1625, -1), (key1594, -1), (key1634, -1), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1)]

theorem rawRowCheck3230 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form7 = rawRow3230 := by decide +kernel

def row3230 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck3230 : row3230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3230 := by decide +kernel

theorem rowEval3230 (x : Key → ℝ) : Integer.Sparse.eval row3230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3230, Integer.Sparse.eval_collectBalanced, rawRowCheck3230]

def rawRow3231 : Integer.Sparse Key := [(key1921, -2), (key1919, -2), (key1927, -2), (key1900, 1), (key1897, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1912, 1), (key1684, 2), (key1682, 2), (key1690, 2), (key1355, -1), (key1352, -1), (key1684, -1), (key1473, -1), (key1690, -1), (key1481, -1), (key1557, -1), (key1549, -1), (key1625, -1), (key1576, -1), (key1634, -1), (key1594, -1), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1)]

theorem rawRowCheck3231 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form7 = rawRow3231 := by decide +kernel

def row3231 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck3231 : row3231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3231 := by decide +kernel

theorem rowEval3231 (x : Key → ℝ) : Integer.Sparse.eval row3231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3231, Integer.Sparse.eval_collectBalanced, rawRowCheck3231]

def rawRow3232 : Integer.Sparse Key := [(key1919, -2), (key1927, -2), (key1921, -2), (key1904, 1), (key1912, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1682, 2), (key1690, 2), (key1684, 2), (key1473, -1), (key1481, -1), (key1352, -1), (key1690, -1), (key1355, -1), (key1684, -1), (key1576, -1), (key1594, -1), (key1549, -1), (key1634, -1), (key1557, -1), (key1625, -1), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1)]

theorem rawRowCheck3232 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form7 = rawRow3232 := by decide +kernel

def row3232 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck3232 : row3232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3232 := by decide +kernel

theorem rowEval3232 (x : Key → ℝ) : Integer.Sparse.eval row3232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck3232, Integer.Sparse.eval_collectBalanced, rawRowCheck3232]

def rawRow3233 : Integer.Sparse Key := [(key1927, -2), (key1919, -2), (key1921, -2), (key1912, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1921, 1), (key1900, 1), (key1690, 2), (key1682, 2), (key1684, 2), (key1481, -1), (key1473, -1), (key1690, -1), (key1352, -1), (key1684, -1), (key1355, -1), (key1594, -1), (key1576, -1), (key1634, -1), (key1549, -1), (key1625, -1), (key1557, -1), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1)]

theorem rawRowCheck3233 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form7 = rawRow3233 := by decide +kernel

def row3233 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck3233 : row3233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3233 := by decide +kernel

theorem rowEval3233 (x : Key → ℝ) : Integer.Sparse.eval row3233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3233, Integer.Sparse.eval_collectBalanced, rawRowCheck3233]

def rawRow3234 : Integer.Sparse Key := [(key1921, -2), (key1927, -2), (key1919, -2), (key1921, 1), (key1927, 1), (key1900, 1), (key1912, 1), (key1897, 1), (key1904, 1), (key1684, 2), (key1690, 2), (key1682, 2), (key1684, -1), (key1690, -1), (key1355, -1), (key1481, -1), (key1352, -1), (key1473, -1), (key1625, -1), (key1634, -1), (key1557, -1), (key1594, -1), (key1549, -1), (key1576, -1), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1)]

theorem rawRowCheck3234 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form7 = rawRow3234 := by decide +kernel

def row3234 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck3234 : row3234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3234 := by decide +kernel

theorem rowEval3234 (x : Key → ℝ) : Integer.Sparse.eval row3234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck3234, Integer.Sparse.eval_collectBalanced, rawRowCheck3234]

def rawRow3235 : Integer.Sparse Key := [(key1927, -2), (key1921, -2), (key1919, -2), (key1927, 1), (key1921, 1), (key1912, 1), (key1900, 1), (key1904, 1), (key1897, 1), (key1690, 2), (key1684, 2), (key1682, 2), (key1690, -1), (key1684, -1), (key1481, -1), (key1355, -1), (key1473, -1), (key1352, -1), (key1634, -1), (key1625, -1), (key1594, -1), (key1557, -1), (key1576, -1), (key1549, -1), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1)]

theorem rawRowCheck3235 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form7 = rawRow3235 := by decide +kernel

def row3235 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

theorem rowCheck3235 : row3235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3235 := by decide +kernel

theorem rowEval3235 (x : Key → ℝ) : Integer.Sparse.eval row3235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck3235, Integer.Sparse.eval_collectBalanced, rawRowCheck3235]

def rawRow3236 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1070, -2), (key1035, 6), (key1107, 2), (key1113, 2), (key1149, 2), (key1000, -2), (key1113, -2), (key1231, -2), (key1122, -6), (key1014, 2), (key1122, 2), (key1234, 2)]

theorem rawRowCheck3236 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form8 = rawRow3236 := by decide +kernel

def row3236 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

theorem rowCheck3236 : row3236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3236 := by decide +kernel

theorem rowEval3236 (x : Key → ℝ) : Integer.Sparse.eval row3236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3236, Integer.Sparse.eval_collectBalanced, rawRowCheck3236]

def rawRow3237 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1070, -2), (key1035, 6), (key1113, 2), (key1107, 2), (key1149, 2), (key1000, -2), (key1231, -2), (key1113, -2), (key1122, -6), (key1014, 2), (key1234, 2), (key1122, 2)]

theorem rawRowCheck3237 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form8 = rawRow3237 := by decide +kernel

def row3237 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

theorem rowCheck3237 : row3237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3237 := by decide +kernel

theorem rowEval3237 (x : Key → ℝ) : Integer.Sparse.eval row3237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3237, Integer.Sparse.eval_collectBalanced, rawRowCheck3237]

def rawRow3238 : Integer.Sparse Key := [(key1029, -2), (key1070, -2), (key1035, -2), (key1035, 6), (key1107, 2), (key1149, 2), (key1113, 2), (key1113, -2), (key1000, -2), (key1231, -2), (key1122, -6), (key1122, 2), (key1014, 2), (key1234, 2)]

theorem rawRowCheck3238 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form8 = rawRow3238 := by decide +kernel

def row3238 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

theorem rowCheck3238 : row3238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3238 := by decide +kernel

theorem rowEval3238 (x : Key → ℝ) : Integer.Sparse.eval row3238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3238, Integer.Sparse.eval_collectBalanced, rawRowCheck3238]

def rawRow3239 : Integer.Sparse Key := [(key1070, -2), (key1029, -2), (key1035, -2), (key1035, 6), (key1149, 2), (key1107, 2), (key1113, 2), (key1113, -2), (key1231, -2), (key1000, -2), (key1122, -6), (key1122, 2), (key1234, 2), (key1014, 2)]

theorem rawRowCheck3239 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form8 = rawRow3239 := by decide +kernel

def row3239 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

theorem rowCheck3239 : row3239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3239 := by decide +kernel

theorem rowEval3239 (x : Key → ℝ) : Integer.Sparse.eval row3239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3239, Integer.Sparse.eval_collectBalanced, rawRowCheck3239]

def rawRow3240 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1029, -2), (key1035, 6), (key1113, 2), (key1149, 2), (key1107, 2), (key1231, -2), (key1000, -2), (key1113, -2), (key1122, -6), (key1234, 2), (key1014, 2), (key1122, 2)]

theorem rawRowCheck3240 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form8 = rawRow3240 := by decide +kernel

def row3240 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

theorem rowCheck3240 : row3240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3240 := by decide +kernel

theorem rowEval3240 (x : Key → ℝ) : Integer.Sparse.eval row3240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3240, Integer.Sparse.eval_collectBalanced, rawRowCheck3240]

def rawRow3241 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1029, -2), (key1035, 6), (key1149, 2), (key1113, 2), (key1107, 2), (key1231, -2), (key1113, -2), (key1000, -2), (key1122, -6), (key1234, 2), (key1122, 2), (key1014, 2)]

theorem rawRowCheck3241 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form8 = rawRow3241 := by decide +kernel

def row3241 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

theorem rowCheck3241 : row3241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3241 := by decide +kernel

theorem rowEval3241 (x : Key → ℝ) : Integer.Sparse.eval row3241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3241, Integer.Sparse.eval_collectBalanced, rawRowCheck3241]

def rawRow3242 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1070, -2), (key1029, 6), (key1231, 2), (key1231, 2), (key1241, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1234, -6), (key1014, 2), (key1122, 2), (key1122, 2)]

theorem rawRowCheck3242 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3242 := by decide +kernel

def row3242 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

theorem rowCheck3242 : row3242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3242 := by decide +kernel

theorem rowEval3242 (x : Key → ℝ) : Integer.Sparse.eval row3242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3242, Integer.Sparse.eval_collectBalanced, rawRowCheck3242]

def rawRow3243 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1035, -2), (key1029, 6), (key1231, 2), (key1241, 2), (key1231, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1234, -6), (key1122, 2), (key1014, 2), (key1122, 2)]

theorem rawRowCheck3243 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3243 := by decide +kernel

def row3243 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

theorem rowCheck3243 : row3243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3243 := by decide +kernel

theorem rowEval3243 (x : Key → ℝ) : Integer.Sparse.eval row3243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3243, Integer.Sparse.eval_collectBalanced, rawRowCheck3243]

def rawRow3244 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1035, -2), (key1029, 6), (key1241, 2), (key1231, 2), (key1231, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1234, -6), (key1122, 2), (key1122, 2), (key1014, 2)]

theorem rawRowCheck3244 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3244 := by decide +kernel

def row3244 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

theorem rowCheck3244 : row3244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3244 := by decide +kernel

theorem rowEval3244 (x : Key → ℝ) : Integer.Sparse.eval row3244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3244, Integer.Sparse.eval_collectBalanced, rawRowCheck3244]

def rawRow3245 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1149, -2), (key1122, 6), (key1029, 2), (key1035, 2), (key1070, 2), (key1014, -2), (key1122, -2), (key1234, -2), (key1035, -6), (key1000, 2), (key1113, 2), (key1231, 2)]

theorem rawRowCheck3245 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form8 = rawRow3245 := by decide +kernel

def row3245 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

theorem rowCheck3245 : row3245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3245 := by decide +kernel

theorem rowEval3245 (x : Key → ℝ) : Integer.Sparse.eval row3245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3245, Integer.Sparse.eval_collectBalanced, rawRowCheck3245]

def rawRow3246 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1149, -2), (key1122, 6), (key1035, 2), (key1029, 2), (key1070, 2), (key1014, -2), (key1234, -2), (key1122, -2), (key1035, -6), (key1000, 2), (key1231, 2), (key1113, 2)]

theorem rawRowCheck3246 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form8 = rawRow3246 := by decide +kernel

def row3246 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

theorem rowCheck3246 : row3246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3246 := by decide +kernel

theorem rowEval3246 (x : Key → ℝ) : Integer.Sparse.eval row3246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3246, Integer.Sparse.eval_collectBalanced, rawRowCheck3246]

def rawRow3247 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1113, -2), (key1122, 6), (key1029, 2), (key1070, 2), (key1035, 2), (key1122, -2), (key1014, -2), (key1234, -2), (key1035, -6), (key1113, 2), (key1000, 2), (key1231, 2)]

theorem rawRowCheck3247 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form8 = rawRow3247 := by decide +kernel

def row3247 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

theorem rowCheck3247 : row3247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3247 := by decide +kernel

theorem rowEval3247 (x : Key → ℝ) : Integer.Sparse.eval row3247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3247, Integer.Sparse.eval_collectBalanced, rawRowCheck3247]

def rawRow3248 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1113, -2), (key1122, 6), (key1070, 2), (key1029, 2), (key1035, 2), (key1122, -2), (key1234, -2), (key1014, -2), (key1035, -6), (key1113, 2), (key1231, 2), (key1000, 2)]

theorem rawRowCheck3248 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form8 = rawRow3248 := by decide +kernel

def row3248 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

theorem rowCheck3248 : row3248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3248 := by decide +kernel

theorem rowEval3248 (x : Key → ℝ) : Integer.Sparse.eval row3248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3248, Integer.Sparse.eval_collectBalanced, rawRowCheck3248]

def rawRow3249 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1107, -2), (key1122, 6), (key1035, 2), (key1070, 2), (key1029, 2), (key1234, -2), (key1014, -2), (key1122, -2), (key1035, -6), (key1231, 2), (key1000, 2), (key1113, 2)]

theorem rawRowCheck3249 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form8 = rawRow3249 := by decide +kernel

def row3249 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

theorem rowCheck3249 : row3249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3249 := by decide +kernel

theorem rowEval3249 (x : Key → ℝ) : Integer.Sparse.eval row3249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3249, Integer.Sparse.eval_collectBalanced, rawRowCheck3249]

def rawRow3250 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1107, -2), (key1122, 6), (key1070, 2), (key1035, 2), (key1029, 2), (key1234, -2), (key1122, -2), (key1014, -2), (key1035, -6), (key1231, 2), (key1113, 2), (key1000, 2)]

theorem rawRowCheck3250 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form8 = rawRow3250 := by decide +kernel

def row3250 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

theorem rowCheck3250 : row3250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3250 := by decide +kernel

theorem rowEval3250 (x : Key → ℝ) : Integer.Sparse.eval row3250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3250, Integer.Sparse.eval_collectBalanced, rawRowCheck3250]

def rawRow3251 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1149, -2), (key1107, 6), (key1231, 2), (key1234, 2), (key1241, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1231, -6), (key1000, 2), (key1035, 2), (key1113, 2)]

theorem rawRowCheck3251 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form8 = rawRow3251 := by decide +kernel

def row3251 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck3251 : row3251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3251 := by decide +kernel

theorem rowEval3251 (x : Key → ℝ) : Integer.Sparse.eval row3251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3251, Integer.Sparse.eval_collectBalanced, rawRowCheck3251]

def rawRow3252 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1149, -2), (key1107, 6), (key1234, 2), (key1231, 2), (key1241, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1231, -6), (key1000, 2), (key1113, 2), (key1035, 2)]

theorem rawRowCheck3252 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form8 = rawRow3252 := by decide +kernel

def row3252 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck3252 : row3252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3252 := by decide +kernel

theorem rowEval3252 (x : Key → ℝ) : Integer.Sparse.eval row3252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3252, Integer.Sparse.eval_collectBalanced, rawRowCheck3252]

def rawRow3253 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1122, -2), (key1107, 6), (key1231, 2), (key1241, 2), (key1234, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1231, -6), (key1035, 2), (key1000, 2), (key1113, 2)]

theorem rawRowCheck3253 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form8 = rawRow3253 := by decide +kernel

def row3253 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck3253 : row3253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3253 := by decide +kernel

theorem rowEval3253 (x : Key → ℝ) : Integer.Sparse.eval row3253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3253, Integer.Sparse.eval_collectBalanced, rawRowCheck3253]

def rawRow3254 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1122, -2), (key1107, 6), (key1241, 2), (key1231, 2), (key1234, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1231, -6), (key1035, 2), (key1113, 2), (key1000, 2)]

theorem rawRowCheck3254 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form8 = rawRow3254 := by decide +kernel

def row3254 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck3254 : row3254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3254 := by decide +kernel

theorem rowEval3254 (x : Key → ℝ) : Integer.Sparse.eval row3254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3254, Integer.Sparse.eval_collectBalanced, rawRowCheck3254]

def rawRow3255 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1113, -2), (key1107, 6), (key1234, 2), (key1241, 2), (key1231, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1231, -6), (key1113, 2), (key1000, 2), (key1035, 2)]

theorem rawRowCheck3255 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form8 = rawRow3255 := by decide +kernel

def row3255 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck3255 : row3255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3255 := by decide +kernel

theorem rowEval3255 (x : Key → ℝ) : Integer.Sparse.eval row3255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3255, Integer.Sparse.eval_collectBalanced, rawRowCheck3255]

def rawRow3256 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1113, -2), (key1107, 6), (key1241, 2), (key1234, 2), (key1231, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1231, -6), (key1113, 2), (key1035, 2), (key1000, 2)]

theorem rawRowCheck3256 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form8 = rawRow3256 := by decide +kernel

def row3256 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

theorem rowCheck3256 : row3256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3256 := by decide +kernel

theorem rowEval3256 (x : Key → ℝ) : Integer.Sparse.eval row3256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3256, Integer.Sparse.eval_collectBalanced, rawRowCheck3256]

def rawRow3257 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1241, -2), (key1234, 6), (key1035, 2), (key1035, 2), (key1070, 2), (key1014, -2), (key1122, -2), (key1122, -2), (key1029, -6), (key994, 2), (key1107, 2), (key1107, 2)]

theorem rawRowCheck3257 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form8 = rawRow3257 := by decide +kernel

def row3257 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck3257 : row3257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3257 := by decide +kernel

theorem rowEval3257 (x : Key → ℝ) : Integer.Sparse.eval row3257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3257, Integer.Sparse.eval_collectBalanced, rawRowCheck3257]

def rawRow3258 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1231, -2), (key1234, 6), (key1035, 2), (key1070, 2), (key1035, 2), (key1122, -2), (key1014, -2), (key1122, -2), (key1029, -6), (key1107, 2), (key994, 2), (key1107, 2)]

theorem rawRowCheck3258 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form8 = rawRow3258 := by decide +kernel

def row3258 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck3258 : row3258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3258 := by decide +kernel

theorem rowEval3258 (x : Key → ℝ) : Integer.Sparse.eval row3258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3258, Integer.Sparse.eval_collectBalanced, rawRowCheck3258]

def rawRow3259 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1231, -2), (key1234, 6), (key1070, 2), (key1035, 2), (key1035, 2), (key1122, -2), (key1122, -2), (key1014, -2), (key1029, -6), (key1107, 2), (key1107, 2), (key994, 2)]

theorem rawRowCheck3259 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form8 = rawRow3259 := by decide +kernel

def row3259 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

theorem rowCheck3259 : row3259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3259 := by decide +kernel

theorem rowEval3259 (x : Key → ℝ) : Integer.Sparse.eval row3259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3259, Integer.Sparse.eval_collectBalanced, rawRowCheck3259]

def rawRow3260 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1241, -2), (key1231, 6), (key1113, 2), (key1122, 2), (key1149, 2), (key1000, -2), (key1035, -2), (key1113, -2), (key1107, -6), (key994, 2), (key1029, 2), (key1107, 2)]

theorem rawRowCheck3260 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form8 = rawRow3260 := by decide +kernel

def row3260 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck3260 : row3260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3260 := by decide +kernel

theorem rowEval3260 (x : Key → ℝ) : Integer.Sparse.eval row3260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3260, Integer.Sparse.eval_collectBalanced, rawRowCheck3260]

def rawRow3261 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1241, -2), (key1231, 6), (key1122, 2), (key1113, 2), (key1149, 2), (key1000, -2), (key1113, -2), (key1035, -2), (key1107, -6), (key994, 2), (key1107, 2), (key1029, 2)]

theorem rawRowCheck3261 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form8 = rawRow3261 := by decide +kernel

def row3261 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck3261 : row3261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3261 := by decide +kernel

theorem rowEval3261 (x : Key → ℝ) : Integer.Sparse.eval row3261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3261, Integer.Sparse.eval_collectBalanced, rawRowCheck3261]

def rawRow3262 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1234, -2), (key1231, 6), (key1113, 2), (key1149, 2), (key1122, 2), (key1035, -2), (key1000, -2), (key1113, -2), (key1107, -6), (key1029, 2), (key994, 2), (key1107, 2)]

theorem rawRowCheck3262 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form8 = rawRow3262 := by decide +kernel

def row3262 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck3262 : row3262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3262 := by decide +kernel

theorem rowEval3262 (x : Key → ℝ) : Integer.Sparse.eval row3262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3262, Integer.Sparse.eval_collectBalanced, rawRowCheck3262]

def rawRow3263 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1234, -2), (key1231, 6), (key1149, 2), (key1113, 2), (key1122, 2), (key1035, -2), (key1113, -2), (key1000, -2), (key1107, -6), (key1029, 2), (key1107, 2), (key994, 2)]

theorem rawRowCheck3263 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form8 = rawRow3263 := by decide +kernel

def row3263 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck3263 : row3263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3263 := by decide +kernel

theorem rowEval3263 (x : Key → ℝ) : Integer.Sparse.eval row3263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3263, Integer.Sparse.eval_collectBalanced, rawRowCheck3263]

def rawRow3264 : Integer.Sparse Key := [(key1234, -2), (key1241, -2), (key1231, -2), (key1231, 6), (key1122, 2), (key1149, 2), (key1113, 2), (key1113, -2), (key1000, -2), (key1035, -2), (key1107, -6), (key1107, 2), (key994, 2), (key1029, 2)]

theorem rawRowCheck3264 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form8 = rawRow3264 := by decide +kernel

def row3264 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck3264 : row3264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3264 := by decide +kernel

theorem rowEval3264 (x : Key → ℝ) : Integer.Sparse.eval row3264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form8) x := by
  rw [rowCheck3264, Integer.Sparse.eval_collectBalanced, rawRowCheck3264]

def rawRow3265 : Integer.Sparse Key := [(key1241, -2), (key1234, -2), (key1231, -2), (key1231, 6), (key1149, 2), (key1122, 2), (key1113, 2), (key1113, -2), (key1035, -2), (key1000, -2), (key1107, -6), (key1107, 2), (key1029, 2), (key994, 2)]

theorem rawRowCheck3265 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form8 = rawRow3265 := by decide +kernel

def row3265 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck3265 : row3265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3265 := by decide +kernel

theorem rowEval3265 (x : Key → ℝ) : Integer.Sparse.eval row3265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form8) x := by
  rw [rowCheck3265, Integer.Sparse.eval_collectBalanced, rawRowCheck3265]

def rawRow3266 : Integer.Sparse Key := [(key2671, -2), (key2726, -2), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, 1), (key2753, 1), (key2732, 1), (key2758, 1), (key2702, 2), (key2972, 2), (key2976, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2728, -1), (key2976, -1), (key2983, -1), (key2735, -1), (key2737, -1), (key2893, -1), (key2897, -1), (key2997, -1), (key2998, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2747, 1), (key2998, 1), (key3000, 1)]

theorem rawRowCheck3266 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form9 = rawRow3266 := by decide +kernel

def row3266 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

theorem rowCheck3266 : row3266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3266 := by decide +kernel

theorem rowEval3266 (x : Key → ℝ) : Integer.Sparse.eval row3266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3266, Integer.Sparse.eval_collectBalanced, rawRowCheck3266]

def rawRow3267 : Integer.Sparse Key := [(key2671, -2), (key2758, -2), (key2726, -2), (key2676, 1), (key2671, 1), (key2753, 1), (key2706, 1), (key2758, 1), (key2732, 1), (key2702, 2), (key2976, 2), (key2972, 2), (key2641, -1), (key2628, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2976, -1), (key2737, -1), (key2735, -1), (key2897, -1), (key2893, -1), (key2998, -1), (key2997, -1), (key2653, 1), (key2646, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2998, 1)]

theorem rawRowCheck3267 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form9 = rawRow3267 := by decide +kernel

def row3267 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

theorem rowCheck3267 : row3267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3267 := by decide +kernel

theorem rowEval3267 (x : Key → ℝ) : Integer.Sparse.eval row3267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3267, Integer.Sparse.eval_collectBalanced, rawRowCheck3267]

def rawRow3268 : Integer.Sparse Key := [(key2726, -2), (key2671, -2), (key2758, -2), (key2706, 1), (key2732, 1), (key2671, 1), (key2758, 1), (key2676, 1), (key2753, 1), (key2972, 2), (key2702, 2), (key2976, 2), (key2702, -1), (key2976, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2893, -1), (key2997, -1), (key2735, -1), (key2998, -1), (key2737, -1), (key2897, -1), (key2735, 1), (key2998, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2747, 1)]

theorem rawRowCheck3268 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form9 = rawRow3268 := by decide +kernel

def row3268 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

theorem rowCheck3268 : row3268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3268 := by decide +kernel

theorem rowEval3268 (x : Key → ℝ) : Integer.Sparse.eval row3268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3268, Integer.Sparse.eval_collectBalanced, rawRowCheck3268]

def rawRow3269 : Integer.Sparse Key := [(key2726, -2), (key2758, -2), (key2671, -2), (key2732, 1), (key2706, 1), (key2758, 1), (key2671, 1), (key2753, 1), (key2676, 1), (key2972, 2), (key2976, 2), (key2702, 2), (key2976, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2728, -1), (key2641, -1), (key2997, -1), (key2893, -1), (key2998, -1), (key2735, -1), (key2897, -1), (key2737, -1), (key2998, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2747, 1), (key2653, 1)]

theorem rawRowCheck3269 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form9 = rawRow3269 := by decide +kernel

def row3269 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

theorem rowCheck3269 : row3269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3269 := by decide +kernel

theorem rowEval3269 (x : Key → ℝ) : Integer.Sparse.eval row3269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3269, Integer.Sparse.eval_collectBalanced, rawRowCheck3269]

def rawRow3270 : Integer.Sparse Key := [(key2758, -2), (key2671, -2), (key2726, -2), (key2753, 1), (key2758, 1), (key2676, 1), (key2732, 1), (key2671, 1), (key2706, 1), (key2976, 2), (key2702, 2), (key2972, 2), (key2728, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2628, -1), (key2702, -1), (key2897, -1), (key2998, -1), (key2737, -1), (key2997, -1), (key2735, -1), (key2893, -1), (key2747, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2646, 1), (key2735, 1)]

theorem rawRowCheck3270 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form9 = rawRow3270 := by decide +kernel

def row3270 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

theorem rowCheck3270 : row3270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3270 := by decide +kernel

theorem rowEval3270 (x : Key → ℝ) : Integer.Sparse.eval row3270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3270, Integer.Sparse.eval_collectBalanced, rawRowCheck3270]

def rawRow3271 : Integer.Sparse Key := [(key2758, -2), (key2726, -2), (key2671, -2), (key2758, 1), (key2753, 1), (key2732, 1), (key2676, 1), (key2706, 1), (key2671, 1), (key2976, 2), (key2972, 2), (key2702, 2), (key2983, -1), (key2728, -1), (key2976, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2998, -1), (key2897, -1), (key2997, -1), (key2737, -1), (key2893, -1), (key2735, -1), (key3000, 1), (key2747, 1), (key2998, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

theorem rawRowCheck3271 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form9 = rawRow3271 := by decide +kernel

def row3271 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

theorem rowCheck3271 : row3271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3271 := by decide +kernel

theorem rowEval3271 (x : Key → ℝ) : Integer.Sparse.eval row3271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3271, Integer.Sparse.eval_collectBalanced, rawRowCheck3271]

def rawRow3272 : Integer.Sparse Key := [(key2676, -2), (key2732, -2), (key2732, -2), (key2671, 1), (key2671, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2728, 2), (key2983, 2), (key2983, 2), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2747, -1), (key2747, -1), (key2904, -1), (key2904, -1), (key3000, -1), (key3000, -1), (key2648, 1), (key2648, 1), (key2737, 1), (key2737, 1), (key2997, 1), (key2997, 1)]

theorem rawRowCheck3272 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3272 := by decide +kernel

def row3272 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

theorem rowCheck3272 : row3272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3272 := by decide +kernel

theorem rowEval3272 (x : Key → ℝ) : Integer.Sparse.eval row3272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3272, Integer.Sparse.eval_collectBalanced, rawRowCheck3272]

def rawRow3273 : Integer.Sparse Key := [(key2732, -2), (key2676, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2983, 2), (key2728, 2), (key2983, 2), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2904, -1), (key3000, -1), (key2747, -1), (key3000, -1), (key2747, -1), (key2904, -1), (key2737, 1), (key2997, 1), (key2648, 1), (key2997, 1), (key2648, 1), (key2737, 1)]

theorem rawRowCheck3273 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3273 := by decide +kernel

def row3273 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

theorem rowCheck3273 : row3273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3273 := by decide +kernel

theorem rowEval3273 (x : Key → ℝ) : Integer.Sparse.eval row3273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3273, Integer.Sparse.eval_collectBalanced, rawRowCheck3273]

def rawRow3274 : Integer.Sparse Key := [(key2732, -2), (key2732, -2), (key2676, -2), (key2726, 1), (key2706, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2671, 1), (key2983, 2), (key2983, 2), (key2728, 2), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2904, -1), (key3000, -1), (key2747, -1), (key2904, -1), (key2747, -1), (key2997, 1), (key2737, 1), (key2997, 1), (key2648, 1), (key2737, 1), (key2648, 1)]

theorem rawRowCheck3274 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3274 := by decide +kernel

def row3274 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

theorem rowCheck3274 : row3274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3274 := by decide +kernel

theorem rowEval3274 (x : Key → ℝ) : Integer.Sparse.eval row3274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3274, Integer.Sparse.eval_collectBalanced, rawRowCheck3274]

def rawRow3275 : Integer.Sparse Key := [(key2786, -2), (key2870, -2), (key2923, -2), (key2794, 1), (key2798, 1), (key2860, 1), (key2920, 1), (key2885, 1), (key2927, 1), (key2671, 2), (key2726, 2), (key2758, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2747, -1), (key2998, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2782, -1), (key2795, -1), (key2938, -1), (key2943, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2728, 1), (key2976, 1), (key2983, 1)]

theorem rawRowCheck3275 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form9 = rawRow3275 := by decide +kernel

def row3275 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

theorem rowCheck3275 : row3275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3275 := by decide +kernel

theorem rowEval3275 (x : Key → ℝ) : Integer.Sparse.eval row3275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3275, Integer.Sparse.eval_collectBalanced, rawRowCheck3275]

def rawRow3276 : Integer.Sparse Key := [(key2786, -2), (key2923, -2), (key2870, -2), (key2798, 1), (key2794, 1), (key2920, 1), (key2860, 1), (key2927, 1), (key2885, 1), (key2671, 2), (key2758, 2), (key2726, 2), (key2653, -1), (key2646, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2998, -1), (key2673, -1), (key2667, -1), (key2795, -1), (key2782, -1), (key2943, -1), (key2938, -1), (key2641, 1), (key2628, 1), (key2728, 1), (key2702, 1), (key2983, 1), (key2976, 1)]

theorem rawRowCheck3276 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form9 = rawRow3276 := by decide +kernel

def row3276 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

theorem rowCheck3276 : row3276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3276 := by decide +kernel

theorem rowEval3276 (x : Key → ℝ) : Integer.Sparse.eval row3276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3276, Integer.Sparse.eval_collectBalanced, rawRowCheck3276]

def rawRow3277 : Integer.Sparse Key := [(key2870, -2), (key2786, -2), (key2923, -2), (key2860, 1), (key2885, 1), (key2794, 1), (key2927, 1), (key2798, 1), (key2920, 1), (key2726, 2), (key2671, 2), (key2758, 2), (key2735, -1), (key2998, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2782, -1), (key2938, -1), (key2667, -1), (key2943, -1), (key2673, -1), (key2795, -1), (key2702, 1), (key2976, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2728, 1)]

theorem rawRowCheck3277 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form9 = rawRow3277 := by decide +kernel

def row3277 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

theorem rowCheck3277 : row3277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3277 := by decide +kernel

theorem rowEval3277 (x : Key → ℝ) : Integer.Sparse.eval row3277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3277, Integer.Sparse.eval_collectBalanced, rawRowCheck3277]

def rawRow3278 : Integer.Sparse Key := [(key2870, -2), (key2923, -2), (key2786, -2), (key2885, 1), (key2860, 1), (key2927, 1), (key2794, 1), (key2920, 1), (key2798, 1), (key2726, 2), (key2758, 2), (key2671, 2), (key2998, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2747, -1), (key2653, -1), (key2938, -1), (key2782, -1), (key2943, -1), (key2667, -1), (key2795, -1), (key2673, -1), (key2976, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2728, 1), (key2641, 1)]

theorem rawRowCheck3278 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form9 = rawRow3278 := by decide +kernel

def row3278 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

theorem rowCheck3278 : row3278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3278 := by decide +kernel

theorem rowEval3278 (x : Key → ℝ) : Integer.Sparse.eval row3278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3278, Integer.Sparse.eval_collectBalanced, rawRowCheck3278]

def rawRow3279 : Integer.Sparse Key := [(key2923, -2), (key2786, -2), (key2870, -2), (key2920, 1), (key2927, 1), (key2798, 1), (key2885, 1), (key2794, 1), (key2860, 1), (key2758, 2), (key2671, 2), (key2726, 2), (key2747, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2646, -1), (key2735, -1), (key2795, -1), (key2943, -1), (key2673, -1), (key2938, -1), (key2667, -1), (key2782, -1), (key2728, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2628, 1), (key2702, 1)]

theorem rawRowCheck3279 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form9 = rawRow3279 := by decide +kernel

def row3279 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

theorem rowCheck3279 : row3279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3279 := by decide +kernel

theorem rowEval3279 (x : Key → ℝ) : Integer.Sparse.eval row3279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3279, Integer.Sparse.eval_collectBalanced, rawRowCheck3279]

def rawRow3280 : Integer.Sparse Key := [(key2923, -2), (key2870, -2), (key2786, -2), (key2927, 1), (key2920, 1), (key2885, 1), (key2798, 1), (key2860, 1), (key2794, 1), (key2758, 2), (key2726, 2), (key2671, 2), (key3000, -1), (key2747, -1), (key2998, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2943, -1), (key2795, -1), (key2938, -1), (key2673, -1), (key2782, -1), (key2667, -1), (key2983, 1), (key2728, 1), (key2976, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

theorem rawRowCheck3280 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form9 = rawRow3280 := by decide +kernel

def row3280 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

theorem rowCheck3280 : row3280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3280 := by decide +kernel

theorem rowEval3280 (x : Key → ℝ) : Integer.Sparse.eval row3280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3280, Integer.Sparse.eval_collectBalanced, rawRowCheck3280]

def rawRow3281 : Integer.Sparse Key := [(key2798, -2), (key2835, -2), (key2885, -2), (key2786, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2829, 1), (key2870, 1), (key3010, 2), (key3017, 2), (key3030, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2728, -1), (key2747, -1), (key2831, -1), (key2904, -1), (key2960, -1), (key2983, -1), (key2618, 1), (key2648, 1), (key2673, 1), (key2737, 1), (key2938, 1), (key2950, 1)]

theorem rawRowCheck3281 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form9 = rawRow3281 := by decide +kernel

def row3281 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck3281 : row3281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3281 := by decide +kernel

theorem rowEval3281 (x : Key → ℝ) : Integer.Sparse.eval row3281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3281, Integer.Sparse.eval_collectBalanced, rawRowCheck3281]

def rawRow3282 : Integer.Sparse Key := [(key2798, -2), (key2885, -2), (key2835, -2), (key2794, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, 1), (key2829, 1), (key3010, 2), (key3030, 2), (key3017, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2747, -1), (key2728, -1), (key2904, -1), (key2831, -1), (key2983, -1), (key2960, -1), (key2648, 1), (key2618, 1), (key2737, 1), (key2673, 1), (key2950, 1), (key2938, 1)]

theorem rawRowCheck3282 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form9 = rawRow3282 := by decide +kernel

def row3282 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck3282 : row3282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3282 := by decide +kernel

theorem rowEval3282 (x : Key → ℝ) : Integer.Sparse.eval row3282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3282, Integer.Sparse.eval_collectBalanced, rawRowCheck3282]

def rawRow3283 : Integer.Sparse Key := [(key2835, -2), (key2798, -2), (key2885, -2), (key2809, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2794, 1), (key2860, 1), (key3017, 2), (key3010, 2), (key3030, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2831, -1), (key2960, -1), (key2728, -1), (key2983, -1), (key2747, -1), (key2904, -1), (key2673, 1), (key2938, 1), (key2618, 1), (key2950, 1), (key2648, 1), (key2737, 1)]

theorem rawRowCheck3283 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form9 = rawRow3283 := by decide +kernel

def row3283 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck3283 : row3283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3283 := by decide +kernel

theorem rowEval3283 (x : Key → ℝ) : Integer.Sparse.eval row3283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3283, Integer.Sparse.eval_collectBalanced, rawRowCheck3283]

def rawRow3284 : Integer.Sparse Key := [(key2835, -2), (key2885, -2), (key2798, -2), (key2829, 1), (key2809, 1), (key2870, 1), (key2786, 1), (key2860, 1), (key2794, 1), (key3017, 2), (key3030, 2), (key3010, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2960, -1), (key2831, -1), (key2983, -1), (key2728, -1), (key2904, -1), (key2747, -1), (key2938, 1), (key2673, 1), (key2950, 1), (key2618, 1), (key2737, 1), (key2648, 1)]

theorem rawRowCheck3284 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form9 = rawRow3284 := by decide +kernel

def row3284 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck3284 : row3284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3284 := by decide +kernel

theorem rowEval3284 (x : Key → ℝ) : Integer.Sparse.eval row3284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3284, Integer.Sparse.eval_collectBalanced, rawRowCheck3284]

def rawRow3285 : Integer.Sparse Key := [(key2885, -2), (key2798, -2), (key2835, -2), (key2860, 1), (key2870, 1), (key2794, 1), (key2829, 1), (key2786, 1), (key2809, 1), (key3030, 2), (key3010, 2), (key3017, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2904, -1), (key2983, -1), (key2747, -1), (key2960, -1), (key2728, -1), (key2831, -1), (key2737, 1), (key2950, 1), (key2648, 1), (key2938, 1), (key2618, 1), (key2673, 1)]

theorem rawRowCheck3285 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form9 = rawRow3285 := by decide +kernel

def row3285 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck3285 : row3285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3285 := by decide +kernel

theorem rowEval3285 (x : Key → ℝ) : Integer.Sparse.eval row3285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3285, Integer.Sparse.eval_collectBalanced, rawRowCheck3285]

def rawRow3286 : Integer.Sparse Key := [(key2885, -2), (key2835, -2), (key2798, -2), (key2870, 1), (key2860, 1), (key2829, 1), (key2794, 1), (key2809, 1), (key2786, 1), (key3030, 2), (key3017, 2), (key3010, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2983, -1), (key2904, -1), (key2960, -1), (key2747, -1), (key2831, -1), (key2728, -1), (key2950, 1), (key2737, 1), (key2938, 1), (key2648, 1), (key2673, 1), (key2618, 1)]

theorem rawRowCheck3286 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form9 = rawRow3286 := by decide +kernel

def row3286 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

theorem rowCheck3286 : row3286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3286 := by decide +kernel

theorem rowEval3286 (x : Key → ℝ) : Integer.Sparse.eval row3286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3286, Integer.Sparse.eval_collectBalanced, rawRowCheck3286]

def rawRow3287 : Integer.Sparse Key := [(key3008, -2), (key3026, -2), (key3026, -2), (key3010, 1), (key3010, 1), (key3023, 1), (key3023, 1), (key3030, 1), (key3030, 1), (key2676, 2), (key2732, 2), (key2732, 2), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, -1), (key2885, -1), (key2671, -1), (key2671, -1), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

theorem rawRowCheck3287 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form9 = rawRow3287 := by decide +kernel

def row3287 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

theorem rowCheck3287 : row3287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3287 := by decide +kernel

theorem rowEval3287 (x : Key → ℝ) : Integer.Sparse.eval row3287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3287, Integer.Sparse.eval_collectBalanced, rawRowCheck3287]

def rawRow3288 : Integer.Sparse Key := [(key3026, -2), (key3008, -2), (key3026, -2), (key3023, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3023, 1), (key2732, 2), (key2676, 2), (key2732, 2), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

theorem rawRowCheck3288 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form9 = rawRow3288 := by decide +kernel

def row3288 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

theorem rowCheck3288 : row3288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3288 := by decide +kernel

theorem rowEval3288 (x : Key → ℝ) : Integer.Sparse.eval row3288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3288, Integer.Sparse.eval_collectBalanced, rawRowCheck3288]

def rawRow3289 : Integer.Sparse Key := [(key3026, -2), (key3026, -2), (key3008, -2), (key3030, 1), (key3023, 1), (key3030, 1), (key3010, 1), (key3023, 1), (key3010, 1), (key2732, 2), (key2732, 2), (key2676, 2), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, -1), (key2644, -1), (key2726, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2671, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

theorem rawRowCheck3289 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form9 = rawRow3289 := by decide +kernel

def row3289 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

theorem rowCheck3289 : row3289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3289 := by decide +kernel

theorem rowEval3289 (x : Key → ℝ) : Integer.Sparse.eval row3289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3289, Integer.Sparse.eval_collectBalanced, rawRowCheck3289]

def rawRow3290 : Integer.Sparse Key := [(key3010, -2), (key3017, -2), (key3030, -2), (key3008, 1), (key3010, 1), (key3012, 1), (key3023, 1), (key3017, 1), (key3026, 1), (key2798, 2), (key2835, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2860, -1), (key2829, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

theorem rawRowCheck3290 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form9 = rawRow3290 := by decide +kernel

def row3290 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck3290 : row3290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3290 := by decide +kernel

theorem rowEval3290 (x : Key → ℝ) : Integer.Sparse.eval row3290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3290, Integer.Sparse.eval_collectBalanced, rawRowCheck3290]

def rawRow3291 : Integer.Sparse Key := [(key3010, -2), (key3030, -2), (key3017, -2), (key3010, 1), (key3008, 1), (key3023, 1), (key3012, 1), (key3026, 1), (key3017, 1), (key2798, 2), (key2885, 2), (key2835, 2), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2732, -1), (key2794, -1), (key2786, -1), (key2860, -1), (key2809, -1), (key2870, -1), (key2829, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

theorem rawRowCheck3291 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form9 = rawRow3291 := by decide +kernel

def row3291 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck3291 : row3291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3291 := by decide +kernel

theorem rowEval3291 (x : Key → ℝ) : Integer.Sparse.eval row3291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3291, Integer.Sparse.eval_collectBalanced, rawRowCheck3291]

def rawRow3292 : Integer.Sparse Key := [(key3017, -2), (key3010, -2), (key3030, -2), (key3012, 1), (key3017, 1), (key3008, 1), (key3026, 1), (key3010, 1), (key3023, 1), (key2835, 2), (key2798, 2), (key2885, 2), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2809, -1), (key2829, -1), (key2786, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

theorem rawRowCheck3292 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form9 = rawRow3292 := by decide +kernel

def row3292 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck3292 : row3292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3292 := by decide +kernel

theorem rowEval3292 (x : Key → ℝ) : Integer.Sparse.eval row3292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck3292, Integer.Sparse.eval_collectBalanced, rawRowCheck3292]

def rawRow3293 : Integer.Sparse Key := [(key3017, -2), (key3030, -2), (key3010, -2), (key3017, 1), (key3012, 1), (key3026, 1), (key3008, 1), (key3023, 1), (key3010, 1), (key2835, 2), (key2885, 2), (key2798, 2), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, -1), (key2644, -1), (key2829, -1), (key2809, -1), (key2870, -1), (key2786, -1), (key2860, -1), (key2794, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

theorem rawRowCheck3293 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form9 = rawRow3293 := by decide +kernel

def row3293 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck3293 : row3293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3293 := by decide +kernel

theorem rowEval3293 (x : Key → ℝ) : Integer.Sparse.eval row3293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3293, Integer.Sparse.eval_collectBalanced, rawRowCheck3293]

def rawRow3294 : Integer.Sparse Key := [(key3030, -2), (key3010, -2), (key3017, -2), (key3023, 1), (key3026, 1), (key3010, 1), (key3017, 1), (key3008, 1), (key3012, 1), (key2885, 2), (key2798, 2), (key2835, 2), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, -1), (key2676, -1), (key2860, -1), (key2870, -1), (key2794, -1), (key2829, -1), (key2786, -1), (key2809, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

theorem rawRowCheck3294 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form9 = rawRow3294 := by decide +kernel

def row3294 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck3294 : row3294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3294 := by decide +kernel

theorem rowEval3294 (x : Key → ℝ) : Integer.Sparse.eval row3294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck3294, Integer.Sparse.eval_collectBalanced, rawRowCheck3294]

def rawRow3295 : Integer.Sparse Key := [(key3030, -2), (key3017, -2), (key3010, -2), (key3026, 1), (key3023, 1), (key3017, 1), (key3010, 1), (key3012, 1), (key3008, 1), (key2885, 2), (key2835, 2), (key2798, 2), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, -1), (key2621, -1), (key2870, -1), (key2860, -1), (key2829, -1), (key2794, -1), (key2809, -1), (key2786, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

theorem rawRowCheck3295 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form9 = rawRow3295 := by decide +kernel

def row3295 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck3295 : row3295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3295 := by decide +kernel

theorem rowEval3295 (x : Key → ℝ) : Integer.Sparse.eval row3295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form9) x := by
  rw [rowCheck3295, Integer.Sparse.eval_collectBalanced, rawRowCheck3295]

def rawRow3296 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2404, 6), (key2839, 2), (key2845, 2), (key3019, 2), (key2589, -2), (key2845, -2), (key2876, -2), (key2916, -6), (key2604, 2), (key2916, 2), (key2925, 2)]

theorem rawRowCheck3296 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form10 = rawRow3296 := by decide +kernel

def row3296 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

theorem rowCheck3296 : row3296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3296 := by decide +kernel

theorem rowEval3296 (x : Key → ℝ) : Integer.Sparse.eval row3296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3296, Integer.Sparse.eval_collectBalanced, rawRowCheck3296]

def rawRow3297 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2435, -2), (key2404, 6), (key2845, 2), (key2839, 2), (key3019, 2), (key2589, -2), (key2876, -2), (key2845, -2), (key2916, -6), (key2604, 2), (key2925, 2), (key2916, 2)]

theorem rawRowCheck3297 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form10 = rawRow3297 := by decide +kernel

def row3297 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

theorem rowCheck3297 : row3297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3297 := by decide +kernel

theorem rowEval3297 (x : Key → ℝ) : Integer.Sparse.eval row3297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3297, Integer.Sparse.eval_collectBalanced, rawRowCheck3297]

def rawRow3298 : Integer.Sparse Key := [(key2398, -2), (key2435, -2), (key2404, -2), (key2404, 6), (key2839, 2), (key3019, 2), (key2845, 2), (key2845, -2), (key2589, -2), (key2876, -2), (key2916, -6), (key2916, 2), (key2604, 2), (key2925, 2)]

theorem rawRowCheck3298 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form10 = rawRow3298 := by decide +kernel

def row3298 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

theorem rowCheck3298 : row3298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3298 := by decide +kernel

theorem rowEval3298 (x : Key → ℝ) : Integer.Sparse.eval row3298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3298, Integer.Sparse.eval_collectBalanced, rawRowCheck3298]

def rawRow3299 : Integer.Sparse Key := [(key2435, -2), (key2398, -2), (key2404, -2), (key2404, 6), (key3019, 2), (key2839, 2), (key2845, 2), (key2845, -2), (key2876, -2), (key2589, -2), (key2916, -6), (key2916, 2), (key2925, 2), (key2604, 2)]

theorem rawRowCheck3299 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form10 = rawRow3299 := by decide +kernel

def row3299 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

theorem rowCheck3299 : row3299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3299 := by decide +kernel

theorem rowEval3299 (x : Key → ℝ) : Integer.Sparse.eval row3299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3299, Integer.Sparse.eval_collectBalanced, rawRowCheck3299]

def rawRow3300 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2398, -2), (key2404, 6), (key2845, 2), (key3019, 2), (key2839, 2), (key2876, -2), (key2589, -2), (key2845, -2), (key2916, -6), (key2925, 2), (key2604, 2), (key2916, 2)]

theorem rawRowCheck3300 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form10 = rawRow3300 := by decide +kernel

def row3300 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

theorem rowCheck3300 : row3300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3300 := by decide +kernel

theorem rowEval3300 (x : Key → ℝ) : Integer.Sparse.eval row3300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3300, Integer.Sparse.eval_collectBalanced, rawRowCheck3300]

def rawRow3301 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2398, -2), (key2404, 6), (key3019, 2), (key2845, 2), (key2839, 2), (key2876, -2), (key2845, -2), (key2589, -2), (key2916, -6), (key2925, 2), (key2916, 2), (key2604, 2)]

theorem rawRowCheck3301 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form10 = rawRow3301 := by decide +kernel

def row3301 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

theorem rowCheck3301 : row3301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3301 := by decide +kernel

theorem rowEval3301 (x : Key → ℝ) : Integer.Sparse.eval row3301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3301, Integer.Sparse.eval_collectBalanced, rawRowCheck3301]

def rawRow3302 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2435, -2), (key2398, 6), (key2876, 2), (key2876, 2), (key3028, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2925, -6), (key2604, 2), (key2916, 2), (key2916, 2)]

theorem rawRowCheck3302 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form10 = rawRow3302 := by decide +kernel

def row3302 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

theorem rowCheck3302 : row3302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3302 := by decide +kernel

theorem rowEval3302 (x : Key → ℝ) : Integer.Sparse.eval row3302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3302, Integer.Sparse.eval_collectBalanced, rawRowCheck3302]

def rawRow3303 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2404, -2), (key2398, 6), (key2876, 2), (key3028, 2), (key2876, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2925, -6), (key2916, 2), (key2604, 2), (key2916, 2)]

theorem rawRowCheck3303 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form10 = rawRow3303 := by decide +kernel

def row3303 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

theorem rowCheck3303 : row3303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3303 := by decide +kernel

theorem rowEval3303 (x : Key → ℝ) : Integer.Sparse.eval row3303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3303, Integer.Sparse.eval_collectBalanced, rawRowCheck3303]

def rawRow3304 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2404, -2), (key2398, 6), (key3028, 2), (key2876, 2), (key2876, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2925, -6), (key2916, 2), (key2916, 2), (key2604, 2)]

theorem rawRowCheck3304 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form10 = rawRow3304 := by decide +kernel

def row3304 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

theorem rowCheck3304 : row3304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3304 := by decide +kernel

theorem rowEval3304 (x : Key → ℝ) : Integer.Sparse.eval row3304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3304, Integer.Sparse.eval_collectBalanced, rawRowCheck3304]

def rawRow3305 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2501, -2), (key2478, 6), (key2398, 2), (key2404, 2), (key2435, 2), (key2604, -2), (key2916, -2), (key2925, -2), (key2768, -6), (key2589, 2), (key2845, 2), (key2876, 2)]

theorem rawRowCheck3305 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form10 = rawRow3305 := by decide +kernel

def row3305 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

theorem rowCheck3305 : row3305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3305 := by decide +kernel

theorem rowEval3305 (x : Key → ℝ) : Integer.Sparse.eval row3305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3305, Integer.Sparse.eval_collectBalanced, rawRowCheck3305]

def rawRow3306 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2501, -2), (key2478, 6), (key2404, 2), (key2398, 2), (key2435, 2), (key2604, -2), (key2925, -2), (key2916, -2), (key2768, -6), (key2589, 2), (key2876, 2), (key2845, 2)]

theorem rawRowCheck3306 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form10 = rawRow3306 := by decide +kernel

def row3306 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

theorem rowCheck3306 : row3306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3306 := by decide +kernel

theorem rowEval3306 (x : Key → ℝ) : Integer.Sparse.eval row3306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3306, Integer.Sparse.eval_collectBalanced, rawRowCheck3306]

def rawRow3307 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2470, -2), (key2478, 6), (key2398, 2), (key2435, 2), (key2404, 2), (key2916, -2), (key2604, -2), (key2925, -2), (key2768, -6), (key2845, 2), (key2589, 2), (key2876, 2)]

theorem rawRowCheck3307 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form10 = rawRow3307 := by decide +kernel

def row3307 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

theorem rowCheck3307 : row3307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3307 := by decide +kernel

theorem rowEval3307 (x : Key → ℝ) : Integer.Sparse.eval row3307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3307, Integer.Sparse.eval_collectBalanced, rawRowCheck3307]

def rawRow3308 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2435, 2), (key2398, 2), (key2404, 2), (key2916, -2), (key2925, -2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2589, 2)]

theorem rawRowCheck3308 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form10 = rawRow3308 := by decide +kernel

def row3308 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

theorem rowCheck3308 : row3308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3308 := by decide +kernel

theorem rowEval3308 (x : Key → ℝ) : Integer.Sparse.eval row3308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3308, Integer.Sparse.eval_collectBalanced, rawRowCheck3308]

def rawRow3309 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2464, -2), (key2478, 6), (key2404, 2), (key2435, 2), (key2398, 2), (key2925, -2), (key2604, -2), (key2916, -2), (key2768, -6), (key2876, 2), (key2589, 2), (key2845, 2)]

theorem rawRowCheck3309 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form10 = rawRow3309 := by decide +kernel

def row3309 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

theorem rowCheck3309 : row3309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3309 := by decide +kernel

theorem rowEval3309 (x : Key → ℝ) : Integer.Sparse.eval row3309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3309, Integer.Sparse.eval_collectBalanced, rawRowCheck3309]

def rawRow3310 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2464, -2), (key2478, 6), (key2435, 2), (key2404, 2), (key2398, 2), (key2925, -2), (key2916, -2), (key2604, -2), (key2768, -6), (key2876, 2), (key2845, 2), (key2589, 2)]

theorem rawRowCheck3310 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form10 = rawRow3310 := by decide +kernel

def row3310 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

theorem rowCheck3310 : row3310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3310 := by decide +kernel

theorem rowEval3310 (x : Key → ℝ) : Integer.Sparse.eval row3310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3310, Integer.Sparse.eval_collectBalanced, rawRowCheck3310]

def rawRow3311 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2501, -2), (key2464, 6), (key2568, 2), (key2570, 2), (key2575, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2876, -6), (key2589, 2), (key2768, 2), (key2845, 2)]

theorem rawRowCheck3311 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form10 = rawRow3311 := by decide +kernel

def row3311 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

theorem rowCheck3311 : row3311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3311 := by decide +kernel

theorem rowEval3311 (x : Key → ℝ) : Integer.Sparse.eval row3311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3311, Integer.Sparse.eval_collectBalanced, rawRowCheck3311]

def rawRow3312 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2501, -2), (key2464, 6), (key2570, 2), (key2568, 2), (key2575, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2876, -6), (key2589, 2), (key2845, 2), (key2768, 2)]

theorem rawRowCheck3312 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form10 = rawRow3312 := by decide +kernel

def row3312 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

theorem rowCheck3312 : row3312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3312 := by decide +kernel

theorem rowEval3312 (x : Key → ℝ) : Integer.Sparse.eval row3312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3312, Integer.Sparse.eval_collectBalanced, rawRowCheck3312]

def rawRow3313 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2478, -2), (key2464, 6), (key2568, 2), (key2575, 2), (key2570, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2876, -6), (key2768, 2), (key2589, 2), (key2845, 2)]

theorem rawRowCheck3313 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form10 = rawRow3313 := by decide +kernel

def row3313 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

theorem rowCheck3313 : row3313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3313 := by decide +kernel

theorem rowEval3313 (x : Key → ℝ) : Integer.Sparse.eval row3313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3313, Integer.Sparse.eval_collectBalanced, rawRowCheck3313]

def rawRow3314 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2478, -2), (key2464, 6), (key2575, 2), (key2568, 2), (key2570, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2876, -6), (key2768, 2), (key2845, 2), (key2589, 2)]

theorem rawRowCheck3314 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form10 = rawRow3314 := by decide +kernel

def row3314 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

theorem rowCheck3314 : row3314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3314 := by decide +kernel

theorem rowEval3314 (x : Key → ℝ) : Integer.Sparse.eval row3314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3314, Integer.Sparse.eval_collectBalanced, rawRowCheck3314]

def rawRow3315 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2470, -2), (key2464, 6), (key2570, 2), (key2575, 2), (key2568, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2876, -6), (key2845, 2), (key2589, 2), (key2768, 2)]

theorem rawRowCheck3315 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form10 = rawRow3315 := by decide +kernel

def row3315 : Integer.Sparse Key := [(key2370, -2), (key2464, 4), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2845, 2), (key2876, -6)]

theorem rowCheck3315 : row3315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3315 := by decide +kernel

theorem rowEval3315 (x : Key → ℝ) : Integer.Sparse.eval row3315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3315, Integer.Sparse.eval_collectBalanced, rawRowCheck3315]

def rawRow3316 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2470, -2), (key2464, 6), (key2575, 2), (key2570, 2), (key2568, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2876, -6), (key2845, 2), (key2768, 2), (key2589, 2)]

theorem rawRowCheck3316 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form10 = rawRow3316 := by decide +kernel

def row3316 : Integer.Sparse Key := [(key2398, -2), (key2464, 4), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2845, 2), (key2876, -6)]

theorem rowCheck3316 : row3316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3316 := by decide +kernel

theorem rowEval3316 (x : Key → ℝ) : Integer.Sparse.eval row3316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3316, Integer.Sparse.eval_collectBalanced, rawRowCheck3316]

def rawRow3317 : Integer.Sparse Key := [(key2568, -2), (key2568, -2), (key2575, -2), (key2570, 6), (key2404, 2), (key2404, 2), (key2435, 2), (key2388, -2), (key2478, -2), (key2478, -2), (key2398, -6), (key2583, 2), (key2839, 2), (key2839, 2)]

theorem rawRowCheck3317 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form10 = rawRow3317 := by decide +kernel

def row3317 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

theorem rowCheck3317 : row3317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3317 := by decide +kernel

theorem rowEval3317 (x : Key → ℝ) : Integer.Sparse.eval row3317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3317, Integer.Sparse.eval_collectBalanced, rawRowCheck3317]

def rawRow3318 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2568, -2), (key2570, 6), (key2404, 2), (key2435, 2), (key2404, 2), (key2478, -2), (key2388, -2), (key2478, -2), (key2398, -6), (key2839, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck3318 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form10 = rawRow3318 := by decide +kernel

def row3318 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

theorem rowCheck3318 : row3318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3318 := by decide +kernel

theorem rowEval3318 (x : Key → ℝ) : Integer.Sparse.eval row3318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3318, Integer.Sparse.eval_collectBalanced, rawRowCheck3318]

def rawRow3319 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2568, -2), (key2570, 6), (key2435, 2), (key2404, 2), (key2404, 2), (key2478, -2), (key2478, -2), (key2388, -2), (key2398, -6), (key2839, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck3319 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form10 = rawRow3319 := by decide +kernel

def row3319 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

theorem rowCheck3319 : row3319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3319 := by decide +kernel

theorem rowEval3319 (x : Key → ℝ) : Integer.Sparse.eval row3319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3319, Integer.Sparse.eval_collectBalanced, rawRowCheck3319]

def rawRow3320 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2575, -2), (key2568, 6), (key2470, 2), (key2478, 2), (key2501, 2), (key2376, -2), (key2404, -2), (key2470, -2), (key2464, -6), (key2370, 2), (key2762, 2), (key2839, 2)]

theorem rawRowCheck3320 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form10 = rawRow3320 := by decide +kernel

def row3320 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2), (key2839, 2)]

theorem rowCheck3320 : row3320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3320 := by decide +kernel

theorem rowEval3320 (x : Key → ℝ) : Integer.Sparse.eval row3320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3320, Integer.Sparse.eval_collectBalanced, rawRowCheck3320]

def rawRow3321 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2575, -2), (key2568, 6), (key2478, 2), (key2470, 2), (key2501, 2), (key2376, -2), (key2470, -2), (key2404, -2), (key2464, -6), (key2370, 2), (key2839, 2), (key2762, 2)]

theorem rawRowCheck3321 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form10 = rawRow3321 := by decide +kernel

def row3321 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2), (key2839, 2)]

theorem rowCheck3321 : row3321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3321 := by decide +kernel

theorem rowEval3321 (x : Key → ℝ) : Integer.Sparse.eval row3321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3321, Integer.Sparse.eval_collectBalanced, rawRowCheck3321]

def rawRow3322 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2570, -2), (key2568, 6), (key2470, 2), (key2501, 2), (key2478, 2), (key2404, -2), (key2376, -2), (key2470, -2), (key2464, -6), (key2398, 2), (key2583, 2), (key2839, 2)]

theorem rawRowCheck3322 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form10 = rawRow3322 := by decide +kernel

def row3322 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2), (key2839, 2)]

theorem rowCheck3322 : row3322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3322 := by decide +kernel

theorem rowEval3322 (x : Key → ℝ) : Integer.Sparse.eval row3322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck3322, Integer.Sparse.eval_collectBalanced, rawRowCheck3322]

def rawRow3323 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2570, -2), (key2568, 6), (key2501, 2), (key2470, 2), (key2478, 2), (key2404, -2), (key2470, -2), (key2376, -2), (key2464, -6), (key2398, 2), (key2839, 2), (key2583, 2)]

theorem rawRowCheck3323 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form10 = rawRow3323 := by decide +kernel

def row3323 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2), (key2839, 2)]

theorem rowCheck3323 : row3323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3323 := by decide +kernel

theorem rowEval3323 (x : Key → ℝ) : Integer.Sparse.eval row3323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3323, Integer.Sparse.eval_collectBalanced, rawRowCheck3323]

def rawRow3324 : Integer.Sparse Key := [(key2570, -2), (key2575, -2), (key2568, -2), (key2568, 6), (key2478, 2), (key2501, 2), (key2470, 2), (key2470, -2), (key2376, -2), (key2404, -2), (key2464, -6), (key2464, 2), (key2370, 2), (key2762, 2)]

theorem rawRowCheck3324 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form10 = rawRow3324 := by decide +kernel

def row3324 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -4), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2)]

theorem rowCheck3324 : row3324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3324 := by decide +kernel

theorem rowEval3324 (x : Key → ℝ) : Integer.Sparse.eval row3324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form10) x := by
  rw [rowCheck3324, Integer.Sparse.eval_collectBalanced, rawRowCheck3324]

def rawRow3325 : Integer.Sparse Key := [(key2575, -2), (key2570, -2), (key2568, -2), (key2568, 6), (key2501, 2), (key2478, 2), (key2470, 2), (key2470, -2), (key2404, -2), (key2376, -2), (key2464, -6), (key2464, 2), (key2398, 2), (key2583, 2)]

theorem rawRowCheck3325 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form10 = rawRow3325 := by decide +kernel

def row3325 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -4), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2)]

theorem rowCheck3325 : row3325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3325 := by decide +kernel

theorem rowEval3325 (x : Key → ℝ) : Integer.Sparse.eval row3325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form10) x := by
  rw [rowCheck3325, Integer.Sparse.eval_collectBalanced, rawRowCheck3325]

def rawRow3326 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2930, -2), (key2767, 6), (key2840, 2), (key2844, 2), (key2967, 2), (key2588, -2), (key2844, -2), (key2875, -2), (key2888, -6), (key2599, 2), (key2888, 2), (key2909, 2)]

theorem rawRowCheck3326 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form11 = rawRow3326 := by decide +kernel

def row3326 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

theorem rowCheck3326 : row3326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3326 := by decide +kernel

theorem rowEval3326 (x : Key → ℝ) : Integer.Sparse.eval row3326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form11) x := by
  rw [rowCheck3326, Integer.Sparse.eval_collectBalanced, rawRowCheck3326]

def rawRow3327 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2930, -2), (key2767, 6), (key2844, 2), (key2840, 2), (key2967, 2), (key2588, -2), (key2875, -2), (key2844, -2), (key2888, -6), (key2599, 2), (key2909, 2), (key2888, 2)]

theorem rawRowCheck3327 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form11 = rawRow3327 := by decide +kernel

def row3327 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

theorem rowCheck3327 : row3327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow3327 := by decide +kernel

theorem rowEval3327 (x : Key → ℝ) : Integer.Sparse.eval row3327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck3327, Integer.Sparse.eval_collectBalanced, rawRowCheck3327]

end MUB6.Certificate.GramRows

end OAI
