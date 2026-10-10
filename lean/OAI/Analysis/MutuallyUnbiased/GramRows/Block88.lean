import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8192 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1253, 6), (key1606, 6), (key1528, 6)]

theorem rawRowCheck8192 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form6 = rawRow8192 := by decide +kernel

def row8192 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8192 : row8192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8192 := by decide +kernel

theorem rowEval8192 (x : Key → ℝ) : Integer.Sparse.eval row8192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8192, Integer.Sparse.eval_collectBalanced, rawRowCheck8192]

def rawRow8193 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1528, 6), (key1253, 6), (key1606, 6)]

theorem rawRowCheck8193 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form6 = rawRow8193 := by decide +kernel

def row8193 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8193 : row8193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8193 := by decide +kernel

theorem rowEval8193 (x : Key → ℝ) : Integer.Sparse.eval row8193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8193, Integer.Sparse.eval_collectBalanced, rawRowCheck8193]

def rawRow8194 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1528, 6), (key1606, 6), (key1253, 6)]

theorem rawRowCheck8194 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form6 = rawRow8194 := by decide +kernel

def row8194 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8194 : row8194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8194 := by decide +kernel

theorem rowEval8194 (x : Key → ℝ) : Integer.Sparse.eval row8194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8194, Integer.Sparse.eval_collectBalanced, rawRowCheck8194]

def rawRow8195 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1606, 6), (key1253, 6), (key1528, 6)]

theorem rawRowCheck8195 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form6 = rawRow8195 := by decide +kernel

def row8195 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8195 : row8195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8195 := by decide +kernel

theorem rowEval8195 (x : Key → ℝ) : Integer.Sparse.eval row8195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8195, Integer.Sparse.eval_collectBalanced, rawRowCheck8195]

def rawRow8196 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1606, 6), (key1528, 6), (key1253, 6)]

theorem rawRowCheck8196 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form6 = rawRow8196 := by decide +kernel

def row8196 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8196 : row8196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8196 := by decide +kernel

theorem rowEval8196 (x : Key → ℝ) : Integer.Sparse.eval row8196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8196, Integer.Sparse.eval_collectBalanced, rawRowCheck8196]

def rawRow8197 : Integer.Sparse Key := [(key1386, -2), (key1394, -2), (key1394, -2), (key1541, -2), (key1549, -2), (key1541, -2), (key1557, -2), (key1549, -2), (key1557, -2), (key1897, -2), (key1897, -2), (key1900, -2), (key1291, 2), (key1299, 2), (key1299, 2), (key1568, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1594, 2), (key1904, 2), (key1904, 2), (key1912, 2)]

theorem rawRowCheck8197 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form7 = rawRow8197 := by decide +kernel

def row8197 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8197 : row8197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8197 := by decide +kernel

theorem rowEval8197 (x : Key → ℝ) : Integer.Sparse.eval row8197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8197, Integer.Sparse.eval_collectBalanced, rawRowCheck8197]

def rawRow8198 : Integer.Sparse Key := [(key1394, -2), (key1386, -2), (key1394, -2), (key1549, -2), (key1541, -2), (key1557, -2), (key1541, -2), (key1557, -2), (key1549, -2), (key1897, -2), (key1900, -2), (key1897, -2), (key1299, 2), (key1291, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1594, 2), (key1568, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1912, 2), (key1904, 2)]

theorem rawRowCheck8198 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form7 = rawRow8198 := by decide +kernel

def row8198 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8198 : row8198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8198 := by decide +kernel

theorem rowEval8198 (x : Key → ℝ) : Integer.Sparse.eval row8198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8198, Integer.Sparse.eval_collectBalanced, rawRowCheck8198]

def rawRow8199 : Integer.Sparse Key := [(key1394, -2), (key1394, -2), (key1386, -2), (key1557, -2), (key1557, -2), (key1549, -2), (key1549, -2), (key1541, -2), (key1541, -2), (key1900, -2), (key1897, -2), (key1897, -2), (key1299, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1594, 2), (key1576, 2), (key1576, 2), (key1568, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1904, 2)]

theorem rawRowCheck8199 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form7 = rawRow8199 := by decide +kernel

def row8199 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8199 : row8199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8199 := by decide +kernel

theorem rowEval8199 (x : Key → ℝ) : Integer.Sparse.eval row8199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8199, Integer.Sparse.eval_collectBalanced, rawRowCheck8199]

def rawRow8200 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1386, -2), (key1394, -2), (key1541, -2), (key1557, -2), (key1897, -2), (key1900, -2), (key1394, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1904, 2), (key1291, 2), (key1299, 2), (key1568, 2), (key1594, 2), (key1904, 2), (key1912, 2), (key1299, 2), (key1576, 2), (key1594, 2)]

theorem rawRowCheck8200 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form7 = rawRow8200 := by decide +kernel

def row8200 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8200 : row8200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8200 := by decide +kernel

theorem rowEval8200 (x : Key → ℝ) : Integer.Sparse.eval row8200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8200, Integer.Sparse.eval_collectBalanced, rawRowCheck8200]

def rawRow8201 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1394, -2), (key1386, -2), (key1557, -2), (key1541, -2), (key1900, -2), (key1897, -2), (key1394, -2), (key1557, -2), (key1549, -2), (key1576, 2), (key1568, 2), (key1904, 2), (key1299, 2), (key1291, 2), (key1594, 2), (key1568, 2), (key1912, 2), (key1904, 2), (key1299, 2), (key1594, 2), (key1576, 2)]

theorem rawRowCheck8201 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form7 = rawRow8201 := by decide +kernel

def row8201 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8201 : row8201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8201 := by decide +kernel

theorem rowEval8201 (x : Key → ℝ) : Integer.Sparse.eval row8201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8201, Integer.Sparse.eval_collectBalanced, rawRowCheck8201]

def rawRow8202 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1541, -2), (key1897, -2), (key1386, -2), (key1900, -2), (key1394, -2), (key1557, -2), (key1549, -2), (key1394, -2), (key1557, -2), (key1568, 2), (key1904, 2), (key1576, 2), (key1568, 2), (key1904, 2), (key1291, 2), (key1912, 2), (key1299, 2), (key1594, 2), (key1576, 2), (key1299, 2), (key1594, 2)]

theorem rawRowCheck8202 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form7 = rawRow8202 := by decide +kernel

def row8202 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8202 : row8202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8202 := by decide +kernel

theorem rowEval8202 (x : Key → ℝ) : Integer.Sparse.eval row8202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8202, Integer.Sparse.eval_collectBalanced, rawRowCheck8202]

def rawRow8203 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1897, -2), (key1541, -2), (key1900, -2), (key1386, -2), (key1557, -2), (key1394, -2), (key1549, -2), (key1557, -2), (key1394, -2), (key1904, 2), (key1568, 2), (key1576, 2), (key1904, 2), (key1568, 2), (key1912, 2), (key1291, 2), (key1594, 2), (key1299, 2), (key1576, 2), (key1594, 2), (key1299, 2)]

theorem rawRowCheck8203 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form7 = rawRow8203 := by decide +kernel

def row8203 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8203 : row8203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8203 := by decide +kernel

theorem rowEval8203 (x : Key → ℝ) : Integer.Sparse.eval row8203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8203, Integer.Sparse.eval_collectBalanced, rawRowCheck8203]

def rawRow8204 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1557, -2), (key1900, -2), (key1394, -2), (key1897, -2), (key1386, -2), (key1541, -2), (key1557, -2), (key1394, -2), (key1549, -2), (key1576, 2), (key1904, 2), (key1568, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1594, 2), (key1299, 2), (key1576, 2)]

theorem rawRowCheck8204 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form7 = rawRow8204 := by decide +kernel

def row8204 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8204 : row8204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8204 := by decide +kernel

theorem rowEval8204 (x : Key → ℝ) : Integer.Sparse.eval row8204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8204, Integer.Sparse.eval_collectBalanced, rawRowCheck8204]

def rawRow8205 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1900, -2), (key1557, -2), (key1897, -2), (key1394, -2), (key1541, -2), (key1386, -2), (key1557, -2), (key1549, -2), (key1394, -2), (key1904, 2), (key1576, 2), (key1568, 2), (key1912, 2), (key1594, 2), (key1904, 2), (key1299, 2), (key1568, 2), (key1291, 2), (key1594, 2), (key1576, 2), (key1299, 2)]

theorem rawRowCheck8205 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form7 = rawRow8205 := by decide +kernel

def row8205 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8205 : row8205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8205 := by decide +kernel

theorem rowEval8205 (x : Key → ℝ) : Integer.Sparse.eval row8205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8205, Integer.Sparse.eval_collectBalanced, rawRowCheck8205]

def rawRow8206 : Integer.Sparse Key := [(key1557, -2), (key1557, -2), (key1900, -2), (key1394, -2), (key1394, -2), (key1549, -2), (key1549, -2), (key1897, -2), (key1897, -2), (key1386, -2), (key1541, -2), (key1541, -2), (key1594, 2), (key1594, 2), (key1912, 2), (key1299, 2), (key1299, 2), (key1576, 2), (key1576, 2), (key1904, 2), (key1904, 2), (key1291, 2), (key1568, 2), (key1568, 2)]

theorem rawRowCheck8206 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form7 = rawRow8206 := by decide +kernel

def row8206 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8206 : row8206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8206 := by decide +kernel

theorem rowEval8206 (x : Key → ℝ) : Integer.Sparse.eval row8206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8206, Integer.Sparse.eval_collectBalanced, rawRowCheck8206]

def rawRow8207 : Integer.Sparse Key := [(key1557, -2), (key1900, -2), (key1557, -2), (key1549, -2), (key1897, -2), (key1394, -2), (key1897, -2), (key1394, -2), (key1549, -2), (key1541, -2), (key1386, -2), (key1541, -2), (key1594, 2), (key1912, 2), (key1594, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1568, 2), (key1291, 2), (key1568, 2)]

theorem rawRowCheck8207 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form7 = rawRow8207 := by decide +kernel

def row8207 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8207 : row8207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8207 := by decide +kernel

theorem rowEval8207 (x : Key → ℝ) : Integer.Sparse.eval row8207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8207, Integer.Sparse.eval_collectBalanced, rawRowCheck8207]

def rawRow8208 : Integer.Sparse Key := [(key1900, -2), (key1557, -2), (key1557, -2), (key1897, -2), (key1549, -2), (key1897, -2), (key1394, -2), (key1549, -2), (key1394, -2), (key1541, -2), (key1541, -2), (key1386, -2), (key1912, 2), (key1594, 2), (key1594, 2), (key1904, 2), (key1576, 2), (key1904, 2), (key1299, 2), (key1576, 2), (key1299, 2), (key1568, 2), (key1568, 2), (key1291, 2)]

theorem rawRowCheck8208 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form7 = rawRow8208 := by decide +kernel

def row8208 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1386, -2), (key1394, -4), (key1541, -4), (key1549, -4), (key1557, -4), (key1568, 4), (key1576, 4), (key1594, 4), (key1897, -4), (key1900, -2), (key1904, 4), (key1912, 2)]

theorem rowCheck8208 : row8208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8208 := by decide +kernel

theorem rowEval8208 (x : Key → ℝ) : Integer.Sparse.eval row8208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8208, Integer.Sparse.eval_collectBalanced, rawRowCheck8208]

def rawRow8209 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1473, -2), (key1568, -2), (key1576, -2), (key1617, -2), (key1625, -2), (key1682, -2), (key1684, -2), (key1904, -2), (key1919, -2), (key1921, -2), (key1311, 2), (key1319, 2), (key1352, 2), (key1541, 2), (key1549, 2), (key1617, 2), (key1634, 2), (key1682, 2), (key1690, 2), (key1897, 2), (key1919, 2), (key1927, 2)]

theorem rawRowCheck8209 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form7 = rawRow8209 := by decide +kernel

def row8209 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8209 : row8209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8209 := by decide +kernel

theorem rowEval8209 (x : Key → ℝ) : Integer.Sparse.eval row8209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8209, Integer.Sparse.eval_collectBalanced, rawRowCheck8209]

def rawRow8210 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1473, -2), (key1576, -2), (key1568, -2), (key1625, -2), (key1617, -2), (key1684, -2), (key1682, -2), (key1904, -2), (key1921, -2), (key1919, -2), (key1319, 2), (key1311, 2), (key1352, 2), (key1549, 2), (key1541, 2), (key1634, 2), (key1617, 2), (key1690, 2), (key1682, 2), (key1897, 2), (key1927, 2), (key1919, 2)]

theorem rawRowCheck8210 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form7 = rawRow8210 := by decide +kernel

def row8210 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8210 : row8210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8210 := by decide +kernel

theorem rowEval8210 (x : Key → ℝ) : Integer.Sparse.eval row8210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8210, Integer.Sparse.eval_collectBalanced, rawRowCheck8210]

def rawRow8211 : Integer.Sparse Key := [(key1419, -2), (key1473, -2), (key1427, -2), (key1617, -2), (key1682, -2), (key1568, -2), (key1684, -2), (key1576, -2), (key1625, -2), (key1919, -2), (key1904, -2), (key1921, -2), (key1311, 2), (key1352, 2), (key1319, 2), (key1617, 2), (key1682, 2), (key1541, 2), (key1690, 2), (key1549, 2), (key1634, 2), (key1919, 2), (key1897, 2), (key1927, 2)]

theorem rawRowCheck8211 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form7 = rawRow8211 := by decide +kernel

def row8211 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8211 : row8211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8211 := by decide +kernel

theorem rowEval8211 (x : Key → ℝ) : Integer.Sparse.eval row8211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8211, Integer.Sparse.eval_collectBalanced, rawRowCheck8211]

def rawRow8212 : Integer.Sparse Key := [(key1473, -2), (key1419, -2), (key1427, -2), (key1682, -2), (key1617, -2), (key1684, -2), (key1568, -2), (key1625, -2), (key1576, -2), (key1919, -2), (key1921, -2), (key1904, -2), (key1352, 2), (key1311, 2), (key1319, 2), (key1682, 2), (key1617, 2), (key1690, 2), (key1541, 2), (key1634, 2), (key1549, 2), (key1919, 2), (key1927, 2), (key1897, 2)]

theorem rawRowCheck8212 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form7 = rawRow8212 := by decide +kernel

def row8212 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8212 : row8212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8212 := by decide +kernel

theorem rowEval8212 (x : Key → ℝ) : Integer.Sparse.eval row8212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8212, Integer.Sparse.eval_collectBalanced, rawRowCheck8212]

def rawRow8213 : Integer.Sparse Key := [(key1427, -2), (key1473, -2), (key1419, -2), (key1625, -2), (key1684, -2), (key1576, -2), (key1682, -2), (key1568, -2), (key1617, -2), (key1921, -2), (key1904, -2), (key1919, -2), (key1319, 2), (key1352, 2), (key1311, 2), (key1634, 2), (key1690, 2), (key1549, 2), (key1682, 2), (key1541, 2), (key1617, 2), (key1927, 2), (key1897, 2), (key1919, 2)]

theorem rawRowCheck8213 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form7 = rawRow8213 := by decide +kernel

def row8213 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8213 : row8213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8213 := by decide +kernel

theorem rowEval8213 (x : Key → ℝ) : Integer.Sparse.eval row8213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8213, Integer.Sparse.eval_collectBalanced, rawRowCheck8213]

def rawRow8214 : Integer.Sparse Key := [(key1473, -2), (key1427, -2), (key1419, -2), (key1684, -2), (key1625, -2), (key1682, -2), (key1576, -2), (key1617, -2), (key1568, -2), (key1921, -2), (key1919, -2), (key1904, -2), (key1352, 2), (key1319, 2), (key1311, 2), (key1690, 2), (key1634, 2), (key1682, 2), (key1549, 2), (key1617, 2), (key1541, 2), (key1927, 2), (key1919, 2), (key1897, 2)]

theorem rawRowCheck8214 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form7 = rawRow8214 := by decide +kernel

def row8214 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8214 : row8214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8214 := by decide +kernel

theorem rowEval8214 (x : Key → ℝ) : Integer.Sparse.eval row8214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8214, Integer.Sparse.eval_collectBalanced, rawRowCheck8214]

def rawRow8215 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1419, -2), (key1427, -2), (key1617, -2), (key1625, -2), (key1919, -2), (key1921, -2), (key1473, -2), (key1682, -2), (key1684, -2), (key1541, 2), (key1549, 2), (key1897, 2), (key1311, 2), (key1319, 2), (key1617, 2), (key1634, 2), (key1919, 2), (key1927, 2), (key1352, 2), (key1682, 2), (key1690, 2)]

theorem rawRowCheck8215 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form7 = rawRow8215 := by decide +kernel

def row8215 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8215 : row8215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8215 := by decide +kernel

theorem rowEval8215 (x : Key → ℝ) : Integer.Sparse.eval row8215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8215, Integer.Sparse.eval_collectBalanced, rawRowCheck8215]

def rawRow8216 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1427, -2), (key1419, -2), (key1625, -2), (key1617, -2), (key1921, -2), (key1919, -2), (key1473, -2), (key1684, -2), (key1682, -2), (key1549, 2), (key1541, 2), (key1897, 2), (key1319, 2), (key1311, 2), (key1634, 2), (key1617, 2), (key1927, 2), (key1919, 2), (key1352, 2), (key1690, 2), (key1682, 2)]

theorem rawRowCheck8216 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form7 = rawRow8216 := by decide +kernel

def row8216 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8216 : row8216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8216 := by decide +kernel

theorem rowEval8216 (x : Key → ℝ) : Integer.Sparse.eval row8216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8216, Integer.Sparse.eval_collectBalanced, rawRowCheck8216]

def rawRow8217 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1617, -2), (key1919, -2), (key1419, -2), (key1921, -2), (key1427, -2), (key1625, -2), (key1682, -2), (key1473, -2), (key1684, -2), (key1541, 2), (key1897, 2), (key1549, 2), (key1617, 2), (key1919, 2), (key1311, 2), (key1927, 2), (key1319, 2), (key1634, 2), (key1682, 2), (key1352, 2), (key1690, 2)]

theorem rawRowCheck8217 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form7 = rawRow8217 := by decide +kernel

def row8217 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8217 : row8217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8217 := by decide +kernel

theorem rowEval8217 (x : Key → ℝ) : Integer.Sparse.eval row8217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8217, Integer.Sparse.eval_collectBalanced, rawRowCheck8217]

def rawRow8218 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1919, -2), (key1617, -2), (key1921, -2), (key1419, -2), (key1625, -2), (key1427, -2), (key1682, -2), (key1684, -2), (key1473, -2), (key1897, 2), (key1541, 2), (key1549, 2), (key1919, 2), (key1617, 2), (key1927, 2), (key1311, 2), (key1634, 2), (key1319, 2), (key1682, 2), (key1690, 2), (key1352, 2)]

theorem rawRowCheck8218 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form7 = rawRow8218 := by decide +kernel

def row8218 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8218 : row8218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8218 := by decide +kernel

theorem rowEval8218 (x : Key → ℝ) : Integer.Sparse.eval row8218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8218, Integer.Sparse.eval_collectBalanced, rawRowCheck8218]

def rawRow8219 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1625, -2), (key1921, -2), (key1427, -2), (key1919, -2), (key1419, -2), (key1617, -2), (key1684, -2), (key1473, -2), (key1682, -2), (key1549, 2), (key1897, 2), (key1541, 2), (key1634, 2), (key1927, 2), (key1319, 2), (key1919, 2), (key1311, 2), (key1617, 2), (key1690, 2), (key1352, 2), (key1682, 2)]

theorem rawRowCheck8219 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form7 = rawRow8219 := by decide +kernel

def row8219 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8219 : row8219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8219 := by decide +kernel

theorem rowEval8219 (x : Key → ℝ) : Integer.Sparse.eval row8219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8219, Integer.Sparse.eval_collectBalanced, rawRowCheck8219]

def rawRow8220 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1921, -2), (key1625, -2), (key1919, -2), (key1427, -2), (key1617, -2), (key1419, -2), (key1684, -2), (key1682, -2), (key1473, -2), (key1897, 2), (key1549, 2), (key1541, 2), (key1927, 2), (key1634, 2), (key1919, 2), (key1319, 2), (key1617, 2), (key1311, 2), (key1690, 2), (key1682, 2), (key1352, 2)]

theorem rawRowCheck8220 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form7 = rawRow8220 := by decide +kernel

def row8220 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8220 : row8220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8220 := by decide +kernel

theorem rowEval8220 (x : Key → ℝ) : Integer.Sparse.eval row8220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8220, Integer.Sparse.eval_collectBalanced, rawRowCheck8220]

def rawRow8221 : Integer.Sparse Key := [(key1617, -2), (key1682, -2), (key1919, -2), (key1419, -2), (key1473, -2), (key1568, -2), (key1684, -2), (key1904, -2), (key1921, -2), (key1427, -2), (key1576, -2), (key1625, -2), (key1617, 2), (key1682, 2), (key1919, 2), (key1311, 2), (key1352, 2), (key1541, 2), (key1690, 2), (key1897, 2), (key1927, 2), (key1319, 2), (key1549, 2), (key1634, 2)]

theorem rawRowCheck8221 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form7 = rawRow8221 := by decide +kernel

def row8221 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8221 : row8221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8221 := by decide +kernel

theorem rowEval8221 (x : Key → ℝ) : Integer.Sparse.eval row8221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8221, Integer.Sparse.eval_collectBalanced, rawRowCheck8221]

def rawRow8222 : Integer.Sparse Key := [(key1682, -2), (key1617, -2), (key1919, -2), (key1473, -2), (key1419, -2), (key1684, -2), (key1568, -2), (key1921, -2), (key1904, -2), (key1427, -2), (key1625, -2), (key1576, -2), (key1682, 2), (key1617, 2), (key1919, 2), (key1352, 2), (key1311, 2), (key1690, 2), (key1541, 2), (key1927, 2), (key1897, 2), (key1319, 2), (key1634, 2), (key1549, 2)]

theorem rawRowCheck8222 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form7 = rawRow8222 := by decide +kernel

def row8222 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8222 : row8222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8222 := by decide +kernel

theorem rowEval8222 (x : Key → ℝ) : Integer.Sparse.eval row8222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8222, Integer.Sparse.eval_collectBalanced, rawRowCheck8222]

def rawRow8223 : Integer.Sparse Key := [(key1617, -2), (key1919, -2), (key1682, -2), (key1568, -2), (key1904, -2), (key1419, -2), (key1921, -2), (key1473, -2), (key1684, -2), (key1576, -2), (key1427, -2), (key1625, -2), (key1617, 2), (key1919, 2), (key1682, 2), (key1541, 2), (key1897, 2), (key1311, 2), (key1927, 2), (key1352, 2), (key1690, 2), (key1549, 2), (key1319, 2), (key1634, 2)]

theorem rawRowCheck8223 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form7 = rawRow8223 := by decide +kernel

def row8223 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8223 : row8223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8223 := by decide +kernel

theorem rowEval8223 (x : Key → ℝ) : Integer.Sparse.eval row8223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8223, Integer.Sparse.eval_collectBalanced, rawRowCheck8223]

def rawRow8224 : Integer.Sparse Key := [(key1919, -2), (key1617, -2), (key1682, -2), (key1904, -2), (key1568, -2), (key1921, -2), (key1419, -2), (key1684, -2), (key1473, -2), (key1576, -2), (key1625, -2), (key1427, -2), (key1919, 2), (key1617, 2), (key1682, 2), (key1897, 2), (key1541, 2), (key1927, 2), (key1311, 2), (key1690, 2), (key1352, 2), (key1549, 2), (key1634, 2), (key1319, 2)]

theorem rawRowCheck8224 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form7 = rawRow8224 := by decide +kernel

def row8224 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8224 : row8224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8224 := by decide +kernel

theorem rowEval8224 (x : Key → ℝ) : Integer.Sparse.eval row8224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8224, Integer.Sparse.eval_collectBalanced, rawRowCheck8224]

def rawRow8225 : Integer.Sparse Key := [(key1682, -2), (key1919, -2), (key1617, -2), (key1684, -2), (key1921, -2), (key1473, -2), (key1904, -2), (key1419, -2), (key1568, -2), (key1625, -2), (key1427, -2), (key1576, -2), (key1682, 2), (key1919, 2), (key1617, 2), (key1690, 2), (key1927, 2), (key1352, 2), (key1897, 2), (key1311, 2), (key1541, 2), (key1634, 2), (key1319, 2), (key1549, 2)]

theorem rawRowCheck8225 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form7 = rawRow8225 := by decide +kernel

def row8225 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8225 : row8225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8225 := by decide +kernel

theorem rowEval8225 (x : Key → ℝ) : Integer.Sparse.eval row8225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8225, Integer.Sparse.eval_collectBalanced, rawRowCheck8225]

def rawRow8226 : Integer.Sparse Key := [(key1919, -2), (key1682, -2), (key1617, -2), (key1921, -2), (key1684, -2), (key1904, -2), (key1473, -2), (key1568, -2), (key1419, -2), (key1625, -2), (key1576, -2), (key1427, -2), (key1919, 2), (key1682, 2), (key1617, 2), (key1927, 2), (key1690, 2), (key1897, 2), (key1352, 2), (key1541, 2), (key1311, 2), (key1634, 2), (key1549, 2), (key1319, 2)]

theorem rawRowCheck8226 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form7 = rawRow8226 := by decide +kernel

def row8226 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8226 : row8226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8226 := by decide +kernel

theorem rowEval8226 (x : Key → ℝ) : Integer.Sparse.eval row8226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8226, Integer.Sparse.eval_collectBalanced, rawRowCheck8226]

def rawRow8227 : Integer.Sparse Key := [(key1625, -2), (key1684, -2), (key1921, -2), (key1427, -2), (key1473, -2), (key1576, -2), (key1682, -2), (key1904, -2), (key1919, -2), (key1419, -2), (key1568, -2), (key1617, -2), (key1634, 2), (key1690, 2), (key1927, 2), (key1319, 2), (key1352, 2), (key1549, 2), (key1682, 2), (key1897, 2), (key1919, 2), (key1311, 2), (key1541, 2), (key1617, 2)]

theorem rawRowCheck8227 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form7 = rawRow8227 := by decide +kernel

def row8227 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8227 : row8227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8227 := by decide +kernel

theorem rowEval8227 (x : Key → ℝ) : Integer.Sparse.eval row8227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8227, Integer.Sparse.eval_collectBalanced, rawRowCheck8227]

def rawRow8228 : Integer.Sparse Key := [(key1684, -2), (key1625, -2), (key1921, -2), (key1473, -2), (key1427, -2), (key1682, -2), (key1576, -2), (key1919, -2), (key1904, -2), (key1419, -2), (key1617, -2), (key1568, -2), (key1690, 2), (key1634, 2), (key1927, 2), (key1352, 2), (key1319, 2), (key1682, 2), (key1549, 2), (key1919, 2), (key1897, 2), (key1311, 2), (key1617, 2), (key1541, 2)]

theorem rawRowCheck8228 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form7 = rawRow8228 := by decide +kernel

def row8228 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8228 : row8228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8228 := by decide +kernel

theorem rowEval8228 (x : Key → ℝ) : Integer.Sparse.eval row8228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8228, Integer.Sparse.eval_collectBalanced, rawRowCheck8228]

def rawRow8229 : Integer.Sparse Key := [(key1625, -2), (key1921, -2), (key1684, -2), (key1576, -2), (key1904, -2), (key1427, -2), (key1919, -2), (key1473, -2), (key1682, -2), (key1568, -2), (key1419, -2), (key1617, -2), (key1634, 2), (key1927, 2), (key1690, 2), (key1549, 2), (key1897, 2), (key1319, 2), (key1919, 2), (key1352, 2), (key1682, 2), (key1541, 2), (key1311, 2), (key1617, 2)]

theorem rawRowCheck8229 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form7 = rawRow8229 := by decide +kernel

def row8229 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8229 : row8229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8229 := by decide +kernel

theorem rowEval8229 (x : Key → ℝ) : Integer.Sparse.eval row8229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck8229, Integer.Sparse.eval_collectBalanced, rawRowCheck8229]

def rawRow8230 : Integer.Sparse Key := [(key1921, -2), (key1625, -2), (key1684, -2), (key1904, -2), (key1576, -2), (key1919, -2), (key1427, -2), (key1682, -2), (key1473, -2), (key1568, -2), (key1617, -2), (key1419, -2), (key1927, 2), (key1634, 2), (key1690, 2), (key1897, 2), (key1549, 2), (key1919, 2), (key1319, 2), (key1682, 2), (key1352, 2), (key1541, 2), (key1617, 2), (key1311, 2)]

theorem rawRowCheck8230 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form7 = rawRow8230 := by decide +kernel

def row8230 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8230 : row8230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8230 := by decide +kernel

theorem rowEval8230 (x : Key → ℝ) : Integer.Sparse.eval row8230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8230, Integer.Sparse.eval_collectBalanced, rawRowCheck8230]

def rawRow8231 : Integer.Sparse Key := [(key1684, -2), (key1921, -2), (key1625, -2), (key1682, -2), (key1919, -2), (key1473, -2), (key1904, -2), (key1427, -2), (key1576, -2), (key1617, -2), (key1419, -2), (key1568, -2), (key1690, 2), (key1927, 2), (key1634, 2), (key1682, 2), (key1919, 2), (key1352, 2), (key1897, 2), (key1319, 2), (key1549, 2), (key1617, 2), (key1311, 2), (key1541, 2)]

theorem rawRowCheck8231 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form7 = rawRow8231 := by decide +kernel

def row8231 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8231 : row8231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8231 := by decide +kernel

theorem rowEval8231 (x : Key → ℝ) : Integer.Sparse.eval row8231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck8231, Integer.Sparse.eval_collectBalanced, rawRowCheck8231]

def rawRow8232 : Integer.Sparse Key := [(key1921, -2), (key1684, -2), (key1625, -2), (key1919, -2), (key1682, -2), (key1904, -2), (key1473, -2), (key1576, -2), (key1427, -2), (key1617, -2), (key1568, -2), (key1419, -2), (key1927, 2), (key1690, 2), (key1634, 2), (key1919, 2), (key1682, 2), (key1897, 2), (key1352, 2), (key1549, 2), (key1319, 2), (key1617, 2), (key1541, 2), (key1311, 2)]

theorem rawRowCheck8232 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form7 = rawRow8232 := by decide +kernel

def row8232 : Integer.Sparse Key := [(key1311, 2), (key1319, 2), (key1352, 2), (key1419, -2), (key1427, -2), (key1473, -2), (key1541, 2), (key1549, 2), (key1568, -2), (key1576, -2), (key1625, -2), (key1634, 2), (key1684, -2), (key1690, 2), (key1897, 2), (key1904, -2), (key1921, -2), (key1927, 2)]

theorem rowCheck8232 : row8232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8232 := by decide +kernel

theorem rowEval8232 (x : Key → ℝ) : Integer.Sparse.eval row8232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck8232, Integer.Sparse.eval_collectBalanced, rawRowCheck8232]

def rawRow8233 : Integer.Sparse Key := [(key236, -2), (key241, -2), (key241, -2), (key406, -2), (key411, -2), (key406, -2), (key421, -2), (key411, -2), (key421, -2), (key657, -2), (key657, -2), (key658, -2), (key248, 1), (key253, 1), (key248, 1), (key263, 1), (key253, 1), (key263, 1), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1), (key435, 1), (key445, 1), (key435, 1), (key453, 1), (key445, 1), (key453, 1), (key660, 1), (key661, 1), (key660, 1), (key662, 1), (key661, 1), (key662, 1)]

theorem rawRowCheck8233 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form8 = rawRow8233 := by decide +kernel

def row8233 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8233 : row8233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8233 := by decide +kernel

theorem rowEval8233 (x : Key → ℝ) : Integer.Sparse.eval row8233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8233, Integer.Sparse.eval_collectBalanced, rawRowCheck8233]

def rawRow8234 : Integer.Sparse Key := [(key241, -2), (key236, -2), (key241, -2), (key411, -2), (key406, -2), (key421, -2), (key406, -2), (key421, -2), (key411, -2), (key657, -2), (key658, -2), (key657, -2), (key253, 1), (key248, 1), (key263, 1), (key248, 1), (key263, 1), (key253, 1), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1), (key445, 1), (key435, 1), (key453, 1), (key435, 1), (key453, 1), (key445, 1), (key661, 1), (key660, 1), (key662, 1), (key660, 1), (key662, 1), (key661, 1)]

theorem rawRowCheck8234 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form8 = rawRow8234 := by decide +kernel

def row8234 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8234 : row8234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8234 := by decide +kernel

theorem rowEval8234 (x : Key → ℝ) : Integer.Sparse.eval row8234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8234, Integer.Sparse.eval_collectBalanced, rawRowCheck8234]

def rawRow8235 : Integer.Sparse Key := [(key241, -2), (key241, -2), (key236, -2), (key421, -2), (key421, -2), (key411, -2), (key411, -2), (key406, -2), (key406, -2), (key658, -2), (key657, -2), (key657, -2), (key263, 1), (key263, 1), (key253, 1), (key253, 1), (key248, 1), (key248, 1), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key453, 1), (key453, 1), (key445, 1), (key445, 1), (key435, 1), (key435, 1), (key662, 1), (key662, 1), (key661, 1), (key661, 1), (key660, 1), (key660, 1)]

theorem rawRowCheck8235 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form8 = rawRow8235 := by decide +kernel

def row8235 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8235 : row8235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8235 := by decide +kernel

theorem rowEval8235 (x : Key → ℝ) : Integer.Sparse.eval row8235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8235, Integer.Sparse.eval_collectBalanced, rawRowCheck8235]

def rawRow8236 : Integer.Sparse Key := [(key406, -2), (key411, -2), (key421, -2), (key236, -2), (key241, -2), (key406, -2), (key421, -2), (key657, -2), (key658, -2), (key241, -2), (key411, -2), (key421, -2), (key316, 1), (key321, 1), (key435, 1), (key445, 1), (key660, 1), (key661, 1), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1), (key248, 1), (key263, 1), (key316, 1), (key331, 1), (key661, 1), (key662, 1), (key253, 1), (key263, 1), (key321, 1), (key331, 1), (key445, 1), (key453, 1)]

theorem rawRowCheck8236 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form8 = rawRow8236 := by decide +kernel

def row8236 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8236 : row8236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8236 := by decide +kernel

theorem rowEval8236 (x : Key → ℝ) : Integer.Sparse.eval row8236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8236, Integer.Sparse.eval_collectBalanced, rawRowCheck8236]

def rawRow8237 : Integer.Sparse Key := [(key411, -2), (key406, -2), (key421, -2), (key241, -2), (key236, -2), (key421, -2), (key406, -2), (key658, -2), (key657, -2), (key241, -2), (key421, -2), (key411, -2), (key321, 1), (key316, 1), (key445, 1), (key435, 1), (key661, 1), (key660, 1), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1), (key263, 1), (key248, 1), (key331, 1), (key316, 1), (key662, 1), (key661, 1), (key263, 1), (key253, 1), (key331, 1), (key321, 1), (key453, 1), (key445, 1)]

theorem rawRowCheck8237 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form8 = rawRow8237 := by decide +kernel

def row8237 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8237 : row8237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8237 := by decide +kernel

theorem rowEval8237 (x : Key → ℝ) : Integer.Sparse.eval row8237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8237, Integer.Sparse.eval_collectBalanced, rawRowCheck8237]

def rawRow8238 : Integer.Sparse Key := [(key406, -2), (key421, -2), (key411, -2), (key406, -2), (key421, -2), (key236, -2), (key658, -2), (key241, -2), (key421, -2), (key411, -2), (key241, -2), (key421, -2), (key435, 1), (key660, 1), (key316, 1), (key661, 1), (key321, 1), (key445, 1), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1), (key316, 1), (key661, 1), (key248, 1), (key662, 1), (key263, 1), (key331, 1), (key321, 1), (key445, 1), (key253, 1), (key453, 1), (key263, 1), (key331, 1)]

theorem rawRowCheck8238 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form8 = rawRow8238 := by decide +kernel

def row8238 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -8), (key435, 2), (key445, 2), (key453, 2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8238 : row8238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8238 := by decide +kernel

theorem rowEval8238 (x : Key → ℝ) : Integer.Sparse.eval row8238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8238, Integer.Sparse.eval_collectBalanced, rawRowCheck8238]

def rawRow8239 : Integer.Sparse Key := [(key421, -2), (key406, -2), (key411, -2), (key421, -2), (key406, -2), (key658, -2), (key236, -2), (key421, -2), (key241, -2), (key411, -2), (key421, -2), (key241, -2), (key660, 1), (key435, 1), (key661, 1), (key316, 1), (key445, 1), (key321, 1), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1), (key661, 1), (key316, 1), (key662, 1), (key248, 1), (key331, 1), (key263, 1), (key445, 1), (key321, 1), (key453, 1), (key253, 1), (key331, 1), (key263, 1)]

theorem rawRowCheck8239 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form8 = rawRow8239 := by decide +kernel

def row8239 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -8), (key435, 2), (key445, 2), (key453, 2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8239 : row8239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8239 := by decide +kernel

theorem rowEval8239 (x : Key → ℝ) : Integer.Sparse.eval row8239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8239, Integer.Sparse.eval_collectBalanced, rawRowCheck8239]

def rawRow8240 : Integer.Sparse Key := [(key411, -2), (key421, -2), (key406, -2), (key657, -2), (key658, -2), (key241, -2), (key421, -2), (key236, -2), (key406, -2), (key421, -2), (key241, -2), (key411, -2), (key445, 1), (key661, 1), (key321, 1), (key660, 1), (key316, 1), (key435, 1), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1), (key331, 1), (key662, 1), (key263, 1), (key661, 1), (key248, 1), (key316, 1), (key331, 1), (key453, 1), (key263, 1), (key445, 1), (key253, 1), (key321, 1)]

theorem rawRowCheck8240 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form8 = rawRow8240 := by decide +kernel

def row8240 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8240 : row8240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8240 := by decide +kernel

theorem rowEval8240 (x : Key → ℝ) : Integer.Sparse.eval row8240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8240, Integer.Sparse.eval_collectBalanced, rawRowCheck8240]

def rawRow8241 : Integer.Sparse Key := [(key421, -2), (key411, -2), (key406, -2), (key658, -2), (key657, -2), (key421, -2), (key241, -2), (key406, -2), (key236, -2), (key421, -2), (key411, -2), (key241, -2), (key661, 1), (key445, 1), (key660, 1), (key321, 1), (key435, 1), (key316, 1), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1), (key662, 1), (key331, 1), (key661, 1), (key263, 1), (key316, 1), (key248, 1), (key453, 1), (key331, 1), (key445, 1), (key263, 1), (key321, 1), (key253, 1)]

theorem rawRowCheck8241 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form8 = rawRow8241 := by decide +kernel

def row8241 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -6), (key435, 2), (key445, 2), (key453, 2), (key657, -2), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8241 : row8241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8241 := by decide +kernel

theorem rowEval8241 (x : Key → ℝ) : Integer.Sparse.eval row8241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8241, Integer.Sparse.eval_collectBalanced, rawRowCheck8241]

def rawRow8242 : Integer.Sparse Key := [(key657, -2), (key657, -2), (key658, -2), (key241, -2), (key241, -2), (key411, -2), (key411, -2), (key421, -2), (key421, -2), (key236, -2), (key406, -2), (key406, -2), (key331, 1), (key331, 1), (key453, 1), (key453, 1), (key662, 1), (key662, 1), (key263, 1), (key263, 1), (key445, 1), (key445, 1), (key661, 1), (key661, 1), (key253, 1), (key253, 1), (key321, 1), (key321, 1), (key660, 1), (key660, 1), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

theorem rawRowCheck8242 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form8 = rawRow8242 := by decide +kernel

def row8242 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8242 : row8242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8242 := by decide +kernel

theorem rowEval8242 (x : Key → ℝ) : Integer.Sparse.eval row8242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8242, Integer.Sparse.eval_collectBalanced, rawRowCheck8242]

def rawRow8243 : Integer.Sparse Key := [(key657, -2), (key658, -2), (key657, -2), (key411, -2), (key421, -2), (key241, -2), (key421, -2), (key241, -2), (key411, -2), (key406, -2), (key236, -2), (key406, -2), (key453, 1), (key662, 1), (key331, 1), (key662, 1), (key331, 1), (key453, 1), (key445, 1), (key661, 1), (key263, 1), (key661, 1), (key263, 1), (key445, 1), (key321, 1), (key660, 1), (key253, 1), (key660, 1), (key253, 1), (key321, 1), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

theorem rawRowCheck8243 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form8 = rawRow8243 := by decide +kernel

def row8243 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8243 : row8243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8243 := by decide +kernel

theorem rowEval8243 (x : Key → ℝ) : Integer.Sparse.eval row8243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8243, Integer.Sparse.eval_collectBalanced, rawRowCheck8243]

def rawRow8244 : Integer.Sparse Key := [(key658, -2), (key657, -2), (key657, -2), (key421, -2), (key411, -2), (key421, -2), (key241, -2), (key411, -2), (key241, -2), (key406, -2), (key406, -2), (key236, -2), (key662, 1), (key453, 1), (key662, 1), (key331, 1), (key453, 1), (key331, 1), (key661, 1), (key445, 1), (key661, 1), (key263, 1), (key445, 1), (key263, 1), (key660, 1), (key321, 1), (key660, 1), (key253, 1), (key321, 1), (key253, 1), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

theorem rawRowCheck8244 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form8 = rawRow8244 := by decide +kernel

def row8244 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key331, 2), (key406, -4), (key411, -4), (key421, -4), (key435, 2), (key445, 2), (key453, 2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

theorem rowCheck8244 : row8244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8244 := by decide +kernel

theorem rowEval8244 (x : Key → ℝ) : Integer.Sparse.eval row8244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8244, Integer.Sparse.eval_collectBalanced, rawRowCheck8244]

def rawRow8245 : Integer.Sparse Key := [(key248, -2), (key253, -2), (key263, -2), (key316, -2), (key321, -2), (key435, -2), (key660, -2), (key445, -2), (key661, -2), (key331, -2), (key453, -2), (key662, -2), (key236, 1), (key241, 1), (key248, 1), (key263, 1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key661, 1), (key662, 1)]

theorem rawRowCheck8245 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form8 = rawRow8245 := by decide +kernel

def row8245 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8245 : row8245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8245 := by decide +kernel

theorem rowEval8245 (x : Key → ℝ) : Integer.Sparse.eval row8245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8245, Integer.Sparse.eval_collectBalanced, rawRowCheck8245]

def rawRow8246 : Integer.Sparse Key := [(key253, -2), (key248, -2), (key263, -2), (key321, -2), (key316, -2), (key660, -2), (key435, -2), (key661, -2), (key445, -2), (key331, -2), (key662, -2), (key453, -2), (key241, 1), (key236, 1), (key263, 1), (key248, 1), (key278, 1), (key277, 1), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1), (key400, 1), (key385, 1), (key421, 1), (key406, 1), (key489, 1), (key488, 1), (key656, 1), (key655, 1), (key658, 1), (key657, 1), (key662, 1), (key661, 1)]

theorem rawRowCheck8246 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form8 = rawRow8246 := by decide +kernel

def row8246 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8246 : row8246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8246 := by decide +kernel

theorem rowEval8246 (x : Key → ℝ) : Integer.Sparse.eval row8246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8246, Integer.Sparse.eval_collectBalanced, rawRowCheck8246]

def rawRow8247 : Integer.Sparse Key := [(key248, -2), (key263, -2), (key253, -2), (key435, -2), (key445, -2), (key316, -2), (key661, -2), (key321, -2), (key660, -2), (key453, -2), (key331, -2), (key662, -2), (key248, 1), (key263, 1), (key236, 1), (key278, 1), (key241, 1), (key263, 1), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1), (key406, 1), (key488, 1), (key385, 1), (key489, 1), (key400, 1), (key421, 1), (key657, 1), (key661, 1), (key655, 1), (key662, 1), (key656, 1), (key658, 1)]

theorem rawRowCheck8247 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form8 = rawRow8247 := by decide +kernel

def row8247 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8247 : row8247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8247 := by decide +kernel

theorem rowEval8247 (x : Key → ℝ) : Integer.Sparse.eval row8247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8247, Integer.Sparse.eval_collectBalanced, rawRowCheck8247]

def rawRow8248 : Integer.Sparse Key := [(key263, -2), (key248, -2), (key253, -2), (key445, -2), (key435, -2), (key661, -2), (key316, -2), (key660, -2), (key321, -2), (key453, -2), (key662, -2), (key331, -2), (key263, 1), (key248, 1), (key278, 1), (key236, 1), (key263, 1), (key241, 1), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1), (key488, 1), (key406, 1), (key489, 1), (key385, 1), (key421, 1), (key400, 1), (key661, 1), (key657, 1), (key662, 1), (key655, 1), (key658, 1), (key656, 1)]

theorem rawRowCheck8248 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form8 = rawRow8248 := by decide +kernel

def row8248 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8248 : row8248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8248 := by decide +kernel

theorem rowEval8248 (x : Key → ℝ) : Integer.Sparse.eval row8248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8248, Integer.Sparse.eval_collectBalanced, rawRowCheck8248]

def rawRow8249 : Integer.Sparse Key := [(key253, -2), (key263, -2), (key248, -2), (key660, -2), (key661, -2), (key321, -2), (key445, -2), (key316, -2), (key435, -2), (key662, -2), (key331, -2), (key453, -2), (key277, 1), (key278, 1), (key241, 1), (key263, 1), (key236, 1), (key248, 1), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1), (key421, 1), (key489, 1), (key400, 1), (key488, 1), (key385, 1), (key406, 1), (key658, 1), (key662, 1), (key656, 1), (key661, 1), (key655, 1), (key657, 1)]

theorem rawRowCheck8249 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form8 = rawRow8249 := by decide +kernel

def row8249 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8249 : row8249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8249 := by decide +kernel

theorem rowEval8249 (x : Key → ℝ) : Integer.Sparse.eval row8249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8249, Integer.Sparse.eval_collectBalanced, rawRowCheck8249]

def rawRow8250 : Integer.Sparse Key := [(key263, -2), (key253, -2), (key248, -2), (key661, -2), (key660, -2), (key445, -2), (key321, -2), (key435, -2), (key316, -2), (key662, -2), (key453, -2), (key331, -2), (key278, 1), (key277, 1), (key263, 1), (key241, 1), (key248, 1), (key236, 1), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1), (key489, 1), (key421, 1), (key488, 1), (key400, 1), (key406, 1), (key385, 1), (key662, 1), (key658, 1), (key661, 1), (key656, 1), (key657, 1), (key655, 1)]

theorem rawRowCheck8250 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form8 = rawRow8250 := by decide +kernel

def row8250 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8250 : row8250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8250 := by decide +kernel

theorem rowEval8250 (x : Key → ℝ) : Integer.Sparse.eval row8250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8250, Integer.Sparse.eval_collectBalanced, rawRowCheck8250]

def rawRow8251 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key248, -2), (key253, -2), (key435, -2), (key660, -2), (key453, -2), (key662, -2), (key263, -2), (key445, -2), (key661, -2), (key302, 1), (key307, 1), (key316, 1), (key346, 1), (key331, 1), (key347, 1), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1), (key248, 1), (key263, 1), (key316, 1), (key331, 1), (key661, 1), (key662, 1), (key277, 1), (key278, 1), (key346, 1), (key347, 1), (key488, 1), (key489, 1)]

theorem rawRowCheck8251 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form8 = rawRow8251 := by decide +kernel

def row8251 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8251 : row8251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8251 := by decide +kernel

theorem rowEval8251 (x : Key → ℝ) : Integer.Sparse.eval row8251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8251, Integer.Sparse.eval_collectBalanced, rawRowCheck8251]

def rawRow8252 : Integer.Sparse Key := [(key321, -2), (key316, -2), (key331, -2), (key253, -2), (key248, -2), (key660, -2), (key435, -2), (key662, -2), (key453, -2), (key263, -2), (key661, -2), (key445, -2), (key307, 1), (key302, 1), (key346, 1), (key316, 1), (key347, 1), (key331, 1), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1), (key263, 1), (key248, 1), (key331, 1), (key316, 1), (key662, 1), (key661, 1), (key278, 1), (key277, 1), (key347, 1), (key346, 1), (key489, 1), (key488, 1)]

theorem rawRowCheck8252 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form8 = rawRow8252 := by decide +kernel

def row8252 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8252 : row8252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8252 := by decide +kernel

theorem rowEval8252 (x : Key → ℝ) : Integer.Sparse.eval row8252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8252, Integer.Sparse.eval_collectBalanced, rawRowCheck8252]

def rawRow8253 : Integer.Sparse Key := [(key316, -2), (key331, -2), (key321, -2), (key435, -2), (key453, -2), (key248, -2), (key662, -2), (key253, -2), (key660, -2), (key445, -2), (key263, -2), (key661, -2), (key316, 1), (key331, 1), (key302, 1), (key347, 1), (key307, 1), (key346, 1), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1), (key316, 1), (key661, 1), (key248, 1), (key662, 1), (key263, 1), (key331, 1), (key346, 1), (key488, 1), (key277, 1), (key489, 1), (key278, 1), (key347, 1)]

theorem rawRowCheck8253 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form8 = rawRow8253 := by decide +kernel

def row8253 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8253 : row8253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8253 := by decide +kernel

theorem rowEval8253 (x : Key → ℝ) : Integer.Sparse.eval row8253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8253, Integer.Sparse.eval_collectBalanced, rawRowCheck8253]

def rawRow8254 : Integer.Sparse Key := [(key331, -2), (key316, -2), (key321, -2), (key453, -2), (key435, -2), (key662, -2), (key248, -2), (key660, -2), (key253, -2), (key445, -2), (key661, -2), (key263, -2), (key331, 1), (key316, 1), (key347, 1), (key302, 1), (key346, 1), (key307, 1), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1), (key661, 1), (key316, 1), (key662, 1), (key248, 1), (key331, 1), (key263, 1), (key488, 1), (key346, 1), (key489, 1), (key277, 1), (key347, 1), (key278, 1)]

theorem rawRowCheck8254 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form8 = rawRow8254 := by decide +kernel

def row8254 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8254 : row8254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8254 := by decide +kernel

theorem rowEval8254 (x : Key → ℝ) : Integer.Sparse.eval row8254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8254, Integer.Sparse.eval_collectBalanced, rawRowCheck8254]

def rawRow8255 : Integer.Sparse Key := [(key321, -2), (key331, -2), (key316, -2), (key660, -2), (key662, -2), (key253, -2), (key453, -2), (key248, -2), (key435, -2), (key661, -2), (key263, -2), (key445, -2), (key346, 1), (key347, 1), (key307, 1), (key331, 1), (key302, 1), (key316, 1), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1), (key331, 1), (key662, 1), (key263, 1), (key661, 1), (key248, 1), (key316, 1), (key347, 1), (key489, 1), (key278, 1), (key488, 1), (key277, 1), (key346, 1)]

theorem rawRowCheck8255 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form8 = rawRow8255 := by decide +kernel

def row8255 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8255 : row8255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8255 := by decide +kernel

theorem rowEval8255 (x : Key → ℝ) : Integer.Sparse.eval row8255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8255, Integer.Sparse.eval_collectBalanced, rawRowCheck8255]

def rawRow8256 : Integer.Sparse Key := [(key331, -2), (key321, -2), (key316, -2), (key662, -2), (key660, -2), (key453, -2), (key253, -2), (key435, -2), (key248, -2), (key661, -2), (key445, -2), (key263, -2), (key347, 1), (key346, 1), (key331, 1), (key307, 1), (key316, 1), (key302, 1), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1), (key662, 1), (key331, 1), (key661, 1), (key263, 1), (key316, 1), (key248, 1), (key489, 1), (key347, 1), (key488, 1), (key278, 1), (key346, 1), (key277, 1)]

theorem rawRowCheck8256 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form8 = rawRow8256 := by decide +kernel

def row8256 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key346, 2), (key347, 2), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8256 : row8256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8256 := by decide +kernel

theorem rowEval8256 (x : Key → ℝ) : Integer.Sparse.eval row8256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8256, Integer.Sparse.eval_collectBalanced, rawRowCheck8256]

def rawRow8257 : Integer.Sparse Key := [(key435, -2), (key445, -2), (key453, -2), (key248, -2), (key263, -2), (key316, -2), (key661, -2), (key331, -2), (key662, -2), (key253, -2), (key321, -2), (key660, -2), (key385, 1), (key400, 1), (key406, 1), (key488, 1), (key421, 1), (key489, 1), (key248, 1), (key263, 1), (key316, 1), (key661, 1), (key331, 1), (key662, 1), (key236, 1), (key278, 1), (key302, 1), (key347, 1), (key656, 1), (key658, 1), (key241, 1), (key263, 1), (key307, 1), (key331, 1), (key400, 1), (key421, 1)]

theorem rawRowCheck8257 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form8 = rawRow8257 := by decide +kernel

def row8257 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8257 : row8257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8257 := by decide +kernel

theorem rowEval8257 (x : Key → ℝ) : Integer.Sparse.eval row8257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8257, Integer.Sparse.eval_collectBalanced, rawRowCheck8257]

def rawRow8258 : Integer.Sparse Key := [(key445, -2), (key435, -2), (key453, -2), (key263, -2), (key248, -2), (key661, -2), (key316, -2), (key662, -2), (key331, -2), (key253, -2), (key660, -2), (key321, -2), (key400, 1), (key385, 1), (key488, 1), (key406, 1), (key489, 1), (key421, 1), (key263, 1), (key248, 1), (key661, 1), (key316, 1), (key662, 1), (key331, 1), (key278, 1), (key236, 1), (key347, 1), (key302, 1), (key658, 1), (key656, 1), (key263, 1), (key241, 1), (key331, 1), (key307, 1), (key421, 1), (key400, 1)]

theorem rawRowCheck8258 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form8 = rawRow8258 := by decide +kernel

def row8258 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8258 : row8258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8258 := by decide +kernel

theorem rowEval8258 (x : Key → ℝ) : Integer.Sparse.eval row8258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8258, Integer.Sparse.eval_collectBalanced, rawRowCheck8258]

def rawRow8259 : Integer.Sparse Key := [(key435, -2), (key453, -2), (key445, -2), (key316, -2), (key331, -2), (key248, -2), (key662, -2), (key263, -2), (key661, -2), (key321, -2), (key253, -2), (key660, -2), (key406, 1), (key421, 1), (key385, 1), (key489, 1), (key400, 1), (key488, 1), (key316, 1), (key331, 1), (key248, 1), (key662, 1), (key263, 1), (key661, 1), (key302, 1), (key347, 1), (key236, 1), (key658, 1), (key278, 1), (key347, 1), (key307, 1), (key400, 1), (key241, 1), (key421, 1), (key263, 1), (key331, 1)]

theorem rawRowCheck8259 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form8 = rawRow8259 := by decide +kernel

def row8259 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 2), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8259 : row8259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8259 := by decide +kernel

theorem rowEval8259 (x : Key → ℝ) : Integer.Sparse.eval row8259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8259, Integer.Sparse.eval_collectBalanced, rawRowCheck8259]

def rawRow8260 : Integer.Sparse Key := [(key453, -2), (key435, -2), (key445, -2), (key331, -2), (key316, -2), (key662, -2), (key248, -2), (key661, -2), (key263, -2), (key321, -2), (key660, -2), (key253, -2), (key421, 1), (key406, 1), (key489, 1), (key385, 1), (key488, 1), (key400, 1), (key331, 1), (key316, 1), (key662, 1), (key248, 1), (key661, 1), (key263, 1), (key347, 1), (key302, 1), (key658, 1), (key236, 1), (key347, 1), (key278, 1), (key400, 1), (key307, 1), (key421, 1), (key241, 1), (key331, 1), (key263, 1)]

theorem rawRowCheck8260 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form8 = rawRow8260 := by decide +kernel

def row8260 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 2), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8260 : row8260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8260 := by decide +kernel

theorem rowEval8260 (x : Key → ℝ) : Integer.Sparse.eval row8260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8260, Integer.Sparse.eval_collectBalanced, rawRowCheck8260]

def rawRow8261 : Integer.Sparse Key := [(key445, -2), (key453, -2), (key435, -2), (key661, -2), (key662, -2), (key263, -2), (key331, -2), (key248, -2), (key316, -2), (key660, -2), (key253, -2), (key321, -2), (key488, 1), (key489, 1), (key400, 1), (key421, 1), (key385, 1), (key406, 1), (key661, 1), (key662, 1), (key263, 1), (key331, 1), (key248, 1), (key316, 1), (key656, 1), (key658, 1), (key278, 1), (key347, 1), (key236, 1), (key302, 1), (key331, 1), (key421, 1), (key263, 1), (key400, 1), (key241, 1), (key307, 1)]

theorem rawRowCheck8261 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form8 = rawRow8261 := by decide +kernel

def row8261 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8261 : row8261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8261 := by decide +kernel

theorem rowEval8261 (x : Key → ℝ) : Integer.Sparse.eval row8261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8261, Integer.Sparse.eval_collectBalanced, rawRowCheck8261]

def rawRow8262 : Integer.Sparse Key := [(key453, -2), (key445, -2), (key435, -2), (key662, -2), (key661, -2), (key331, -2), (key263, -2), (key316, -2), (key248, -2), (key660, -2), (key321, -2), (key253, -2), (key489, 1), (key488, 1), (key421, 1), (key400, 1), (key406, 1), (key385, 1), (key662, 1), (key661, 1), (key331, 1), (key263, 1), (key316, 1), (key248, 1), (key658, 1), (key656, 1), (key347, 1), (key278, 1), (key302, 1), (key236, 1), (key421, 1), (key331, 1), (key400, 1), (key263, 1), (key307, 1), (key241, 1)]

theorem rawRowCheck8262 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form8 = rawRow8262 := by decide +kernel

def row8262 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key347, 1), (key385, 1), (key400, 2), (key406, 1), (key421, 2), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key656, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8262 : row8262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8262 := by decide +kernel

theorem rowEval8262 (x : Key → ℝ) : Integer.Sparse.eval row8262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8262, Integer.Sparse.eval_collectBalanced, rawRowCheck8262]

def rawRow8263 : Integer.Sparse Key := [(key660, -2), (key661, -2), (key662, -2), (key253, -2), (key263, -2), (key321, -2), (key445, -2), (key331, -2), (key453, -2), (key248, -2), (key316, -2), (key435, -2), (key655, 1), (key656, 1), (key657, 1), (key661, 1), (key658, 1), (key662, 1), (key277, 1), (key278, 1), (key346, 1), (key488, 1), (key347, 1), (key489, 1), (key241, 1), (key263, 1), (key307, 1), (key400, 1), (key331, 1), (key421, 1), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

theorem rawRowCheck8263 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form8 = rawRow8263 := by decide +kernel

def row8263 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8263 : row8263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8263 := by decide +kernel

theorem rowEval8263 (x : Key → ℝ) : Integer.Sparse.eval row8263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8263, Integer.Sparse.eval_collectBalanced, rawRowCheck8263]

def rawRow8264 : Integer.Sparse Key := [(key661, -2), (key660, -2), (key662, -2), (key263, -2), (key253, -2), (key445, -2), (key321, -2), (key453, -2), (key331, -2), (key248, -2), (key435, -2), (key316, -2), (key656, 1), (key655, 1), (key661, 1), (key657, 1), (key662, 1), (key658, 1), (key278, 1), (key277, 1), (key488, 1), (key346, 1), (key489, 1), (key347, 1), (key263, 1), (key241, 1), (key400, 1), (key307, 1), (key421, 1), (key331, 1), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

theorem rawRowCheck8264 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form8 = rawRow8264 := by decide +kernel

def row8264 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8264 : row8264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8264 := by decide +kernel

theorem rowEval8264 (x : Key → ℝ) : Integer.Sparse.eval row8264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8264, Integer.Sparse.eval_collectBalanced, rawRowCheck8264]

def rawRow8265 : Integer.Sparse Key := [(key660, -2), (key662, -2), (key661, -2), (key321, -2), (key331, -2), (key253, -2), (key453, -2), (key263, -2), (key445, -2), (key316, -2), (key248, -2), (key435, -2), (key657, 1), (key658, 1), (key655, 1), (key662, 1), (key656, 1), (key661, 1), (key346, 1), (key347, 1), (key277, 1), (key489, 1), (key278, 1), (key488, 1), (key307, 1), (key331, 1), (key241, 1), (key421, 1), (key263, 1), (key400, 1), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

theorem rawRowCheck8265 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form8 = rawRow8265 := by decide +kernel

def row8265 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8265 : row8265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8265 := by decide +kernel

theorem rowEval8265 (x : Key → ℝ) : Integer.Sparse.eval row8265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck8265, Integer.Sparse.eval_collectBalanced, rawRowCheck8265]

def rawRow8266 : Integer.Sparse Key := [(key662, -2), (key660, -2), (key661, -2), (key331, -2), (key321, -2), (key453, -2), (key253, -2), (key445, -2), (key263, -2), (key316, -2), (key435, -2), (key248, -2), (key658, 1), (key657, 1), (key662, 1), (key655, 1), (key661, 1), (key656, 1), (key347, 1), (key346, 1), (key489, 1), (key277, 1), (key488, 1), (key278, 1), (key331, 1), (key307, 1), (key421, 1), (key241, 1), (key400, 1), (key263, 1), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

theorem rawRowCheck8266 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form8 = rawRow8266 := by decide +kernel

def row8266 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8266 : row8266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8266 := by decide +kernel

theorem rowEval8266 (x : Key → ℝ) : Integer.Sparse.eval row8266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8266, Integer.Sparse.eval_collectBalanced, rawRowCheck8266]

def rawRow8267 : Integer.Sparse Key := [(key661, -2), (key662, -2), (key660, -2), (key445, -2), (key453, -2), (key263, -2), (key331, -2), (key253, -2), (key321, -2), (key435, -2), (key248, -2), (key316, -2), (key661, 1), (key662, 1), (key656, 1), (key658, 1), (key655, 1), (key657, 1), (key488, 1), (key489, 1), (key278, 1), (key347, 1), (key277, 1), (key346, 1), (key400, 1), (key421, 1), (key263, 1), (key331, 1), (key241, 1), (key307, 1), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

theorem rawRowCheck8267 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form8 = rawRow8267 := by decide +kernel

def row8267 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8267 : row8267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8267 := by decide +kernel

theorem rowEval8267 (x : Key → ℝ) : Integer.Sparse.eval row8267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck8267, Integer.Sparse.eval_collectBalanced, rawRowCheck8267]

def rawRow8268 : Integer.Sparse Key := [(key662, -2), (key661, -2), (key660, -2), (key453, -2), (key445, -2), (key331, -2), (key263, -2), (key321, -2), (key253, -2), (key435, -2), (key316, -2), (key248, -2), (key662, 1), (key661, 1), (key658, 1), (key656, 1), (key657, 1), (key655, 1), (key489, 1), (key488, 1), (key347, 1), (key278, 1), (key346, 1), (key277, 1), (key421, 1), (key400, 1), (key331, 1), (key263, 1), (key307, 1), (key241, 1), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

theorem rawRowCheck8268 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form8 = rawRow8268 := by decide +kernel

def row8268 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, 1), (key307, 1), (key316, -1), (key321, -2), (key331, -1), (key346, 1), (key347, 1), (key385, 1), (key400, 1), (key406, 1), (key421, 1), (key435, -2), (key445, -2), (key453, -2), (key488, 1), (key489, 1), (key655, 1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, -1), (key662, -1)]

theorem rowCheck8268 : row8268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8268 := by decide +kernel

theorem rowEval8268 (x : Key → ℝ) : Integer.Sparse.eval row8268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck8268, Integer.Sparse.eval_collectBalanced, rawRowCheck8268]

def rawRow8269 : Integer.Sparse Key := [(key2383, 2), (key2394, 2), (key2394, 2), (key2411, 2), (key2484, 2), (key2484, 2), (key2443, 2), (key2443, 2), (key2509, 2), (key2509, 2), (key2524, 2), (key2524, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2503, -2)]

theorem rawRowCheck8269 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form0 = rawRow8269 := by decide +kernel

def row8269 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8269 : row8269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8269 := by decide +kernel

theorem rowEval8269 (x : Key → ℝ) : Integer.Sparse.eval row8269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8269, Integer.Sparse.eval_collectBalanced, rawRowCheck8269]

def rawRow8270 : Integer.Sparse Key := [(key2394, 2), (key2383, 2), (key2394, 2), (key2484, 2), (key2411, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2443, 2), (key2524, 2), (key2443, 2), (key2509, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2437, -2), (key2503, -2)]

theorem rawRowCheck8270 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form0 = rawRow8270 := by decide +kernel

def row8270 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8270 : row8270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8270 := by decide +kernel

theorem rowEval8270 (x : Key → ℝ) : Integer.Sparse.eval row8270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8270, Integer.Sparse.eval_collectBalanced, rawRowCheck8270]

def rawRow8271 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2383, 2), (key2484, 2), (key2484, 2), (key2411, 2), (key2524, 2), (key2509, 2), (key2524, 2), (key2443, 2), (key2509, 2), (key2443, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, -2), (key2503, -2), (key2437, -2)]

theorem rawRowCheck8271 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form0 = rawRow8271 := by decide +kernel

def row8271 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8271 : row8271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8271 := by decide +kernel

theorem rowEval8271 (x : Key → ℝ) : Integer.Sparse.eval row8271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8271, Integer.Sparse.eval_collectBalanced, rawRowCheck8271]

def rawRow8272 : Integer.Sparse Key := [(key2411, 2), (key2443, 2), (key2443, 2), (key2383, 2), (key2509, 2), (key2509, 2), (key2394, 2), (key2394, 2), (key2484, 2), (key2484, 2), (key2524, 2), (key2524, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

theorem rawRowCheck8272 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form0 = rawRow8272 := by decide +kernel

def row8272 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8272 : row8272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8272 := by decide +kernel

theorem rowEval8272 (x : Key → ℝ) : Integer.Sparse.eval row8272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8272, Integer.Sparse.eval_collectBalanced, rawRowCheck8272]

def rawRow8273 : Integer.Sparse Key := [(key2443, 2), (key2411, 2), (key2443, 2), (key2509, 2), (key2383, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2394, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

theorem rawRowCheck8273 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form0 = rawRow8273 := by decide +kernel

def row8273 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8273 : row8273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8273 := by decide +kernel

theorem rowEval8273 (x : Key → ℝ) : Integer.Sparse.eval row8273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8273, Integer.Sparse.eval_collectBalanced, rawRowCheck8273]

def rawRow8274 : Integer.Sparse Key := [(key2443, 2), (key2443, 2), (key2411, 2), (key2509, 2), (key2509, 2), (key2383, 2), (key2524, 2), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, 2), (key2394, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

theorem rawRowCheck8274 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form0 = rawRow8274 := by decide +kernel

def row8274 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8274 : row8274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8274 := by decide +kernel

theorem rowEval8274 (x : Key → ℝ) : Integer.Sparse.eval row8274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8274, Integer.Sparse.eval_collectBalanced, rawRowCheck8274]

def rawRow8275 : Integer.Sparse Key := [(key2484, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2524, 2), (key2383, 2), (key2394, 2), (key2411, 2), (key2484, 2), (key2443, 2), (key2509, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

theorem rawRowCheck8275 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form0 = rawRow8275 := by decide +kernel

def row8275 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8275 : row8275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8275 := by decide +kernel

theorem rowEval8275 (x : Key → ℝ) : Integer.Sparse.eval row8275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8275, Integer.Sparse.eval_collectBalanced, rawRowCheck8275]

def rawRow8276 : Integer.Sparse Key := [(key2484, 2), (key2524, 2), (key2509, 2), (key2394, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2383, 2), (key2484, 2), (key2411, 2), (key2509, 2), (key2443, 2), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

theorem rawRowCheck8276 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form0 = rawRow8276 := by decide +kernel

def row8276 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8276 : row8276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8276 := by decide +kernel

theorem rowEval8276 (x : Key → ℝ) : Integer.Sparse.eval row8276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8276, Integer.Sparse.eval_collectBalanced, rawRowCheck8276]

def rawRow8277 : Integer.Sparse Key := [(key2509, 2), (key2484, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2524, 2), (key2411, 2), (key2443, 2), (key2383, 2), (key2509, 2), (key2394, 2), (key2484, 2), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

theorem rawRowCheck8277 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form0 = rawRow8277 := by decide +kernel

def row8277 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8277 : row8277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8277 := by decide +kernel

theorem rowEval8277 (x : Key → ℝ) : Integer.Sparse.eval row8277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck8277, Integer.Sparse.eval_collectBalanced, rawRowCheck8277]

def rawRow8278 : Integer.Sparse Key := [(key2509, 2), (key2524, 2), (key2484, 2), (key2443, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2411, 2), (key2509, 2), (key2383, 2), (key2484, 2), (key2394, 2), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

theorem rawRowCheck8278 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form0 = rawRow8278 := by decide +kernel

def row8278 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8278 : row8278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8278 := by decide +kernel

theorem rowEval8278 (x : Key → ℝ) : Integer.Sparse.eval row8278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8278, Integer.Sparse.eval_collectBalanced, rawRowCheck8278]

def rawRow8279 : Integer.Sparse Key := [(key2524, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2394, 2), (key2443, 2), (key2484, 2), (key2509, 2), (key2394, 2), (key2443, 2), (key2383, 2), (key2411, 2), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

theorem rawRowCheck8279 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form0 = rawRow8279 := by decide +kernel

def row8279 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8279 : row8279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8279 := by decide +kernel

theorem rowEval8279 (x : Key → ℝ) : Integer.Sparse.eval row8279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck8279, Integer.Sparse.eval_collectBalanced, rawRowCheck8279]

def rawRow8280 : Integer.Sparse Key := [(key2524, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2443, 2), (key2394, 2), (key2509, 2), (key2484, 2), (key2443, 2), (key2394, 2), (key2411, 2), (key2383, 2), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

theorem rawRowCheck8280 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form0 = rawRow8280 := by decide +kernel

def row8280 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -4), (key2480, -4), (key2484, 4), (key2503, -4), (key2509, 4), (key2524, 4)]

theorem rowCheck8280 : row8280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8280 := by decide +kernel

theorem rowEval8280 (x : Key → ℝ) : Integer.Sparse.eval row8280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck8280, Integer.Sparse.eval_collectBalanced, rawRowCheck8280]

def rawRow8281 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1026, 6), (key1104, 6), (key1104, 6)]

theorem rawRowCheck8281 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form1 = rawRow8281 := by decide +kernel

def row8281 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8281 : row8281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8281 := by decide +kernel

theorem rowEval8281 (x : Key → ℝ) : Integer.Sparse.eval row8281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8281, Integer.Sparse.eval_collectBalanced, rawRowCheck8281]

def rawRow8282 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1104, 6), (key1026, 6), (key1104, 6)]

theorem rawRowCheck8282 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form1 = rawRow8282 := by decide +kernel

def row8282 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8282 : row8282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8282 := by decide +kernel

theorem rowEval8282 (x : Key → ℝ) : Integer.Sparse.eval row8282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8282, Integer.Sparse.eval_collectBalanced, rawRowCheck8282]

def rawRow8283 : Integer.Sparse Key := [(key1230, -24), (key991, 6), (key1104, 6), (key1104, 6), (key1026, 6)]

theorem rawRowCheck8283 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form1 = rawRow8283 := by decide +kernel

def row8283 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8283 : row8283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8283 := by decide +kernel

theorem rowEval8283 (x : Key → ℝ) : Integer.Sparse.eval row8283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8283, Integer.Sparse.eval_collectBalanced, rawRowCheck8283]

def rawRow8284 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key991, 6), (key1104, 6), (key1104, 6)]

theorem rawRowCheck8284 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form1 = rawRow8284 := by decide +kernel

def row8284 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8284 : row8284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8284 := by decide +kernel

theorem rowEval8284 (x : Key → ℝ) : Integer.Sparse.eval row8284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8284, Integer.Sparse.eval_collectBalanced, rawRowCheck8284]

def rawRow8285 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key1104, 6), (key991, 6), (key1104, 6)]

theorem rawRowCheck8285 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form1 = rawRow8285 := by decide +kernel

def row8285 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8285 : row8285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8285 := by decide +kernel

theorem rowEval8285 (x : Key → ℝ) : Integer.Sparse.eval row8285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8285, Integer.Sparse.eval_collectBalanced, rawRowCheck8285]

def rawRow8286 : Integer.Sparse Key := [(key1230, -24), (key1026, 6), (key1104, 6), (key1104, 6), (key991, 6)]

theorem rawRowCheck8286 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form1 = rawRow8286 := by decide +kernel

def row8286 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8286 : row8286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8286 := by decide +kernel

theorem rowEval8286 (x : Key → ℝ) : Integer.Sparse.eval row8286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8286, Integer.Sparse.eval_collectBalanced, rawRowCheck8286]

def rawRow8287 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key991, 6), (key1026, 6), (key1104, 6)]

theorem rawRowCheck8287 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form1 = rawRow8287 := by decide +kernel

def row8287 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8287 : row8287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8287 := by decide +kernel

theorem rowEval8287 (x : Key → ℝ) : Integer.Sparse.eval row8287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8287, Integer.Sparse.eval_collectBalanced, rawRowCheck8287]

def rawRow8288 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key991, 6), (key1104, 6), (key1026, 6)]

theorem rawRowCheck8288 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form1 = rawRow8288 := by decide +kernel

def row8288 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8288 : row8288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8288 := by decide +kernel

theorem rowEval8288 (x : Key → ℝ) : Integer.Sparse.eval row8288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8288, Integer.Sparse.eval_collectBalanced, rawRowCheck8288]

def rawRow8289 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1026, 6), (key991, 6), (key1104, 6)]

theorem rawRowCheck8289 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form1 = rawRow8289 := by decide +kernel

def row8289 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8289 : row8289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8289 := by decide +kernel

theorem rowEval8289 (x : Key → ℝ) : Integer.Sparse.eval row8289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8289, Integer.Sparse.eval_collectBalanced, rawRowCheck8289]

def rawRow8290 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1026, 6), (key1104, 6), (key991, 6)]

theorem rawRowCheck8290 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form1 = rawRow8290 := by decide +kernel

def row8290 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8290 : row8290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8290 := by decide +kernel

theorem rowEval8290 (x : Key → ℝ) : Integer.Sparse.eval row8290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8290, Integer.Sparse.eval_collectBalanced, rawRowCheck8290]

def rawRow8291 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1104, 6), (key991, 6), (key1026, 6)]

theorem rawRowCheck8291 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form1 = rawRow8291 := by decide +kernel

def row8291 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8291 : row8291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8291 := by decide +kernel

theorem rowEval8291 (x : Key → ℝ) : Integer.Sparse.eval row8291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8291, Integer.Sparse.eval_collectBalanced, rawRowCheck8291]

def rawRow8292 : Integer.Sparse Key := [(key1230, -24), (key1104, 6), (key1104, 6), (key1026, 6), (key991, 6)]

theorem rawRowCheck8292 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form1 = rawRow8292 := by decide +kernel

def row8292 : Integer.Sparse Key := [(key991, 6), (key1026, 6), (key1104, 12), (key1230, -24)]

theorem rowCheck8292 : row8292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8292 := by decide +kernel

theorem rowEval8292 (x : Key → ℝ) : Integer.Sparse.eval row8292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8292, Integer.Sparse.eval_collectBalanced, rawRowCheck8292]

def rawRow8293 : Integer.Sparse Key := [(key1232, -6), (key1232, -6), (key1235, -6), (key1242, -6), (key1001, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1123, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1150, 2)]

theorem rawRowCheck8293 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form2 = rawRow8293 := by decide +kernel

def row8293 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8293 : row8293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8293 := by decide +kernel

theorem rowEval8293 (x : Key → ℝ) : Integer.Sparse.eval row8293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8293, Integer.Sparse.eval_collectBalanced, rawRowCheck8293]

def rawRow8294 : Integer.Sparse Key := [(key1232, -6), (key1235, -6), (key1232, -6), (key1242, -6), (key1001, 2), (key1015, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1071, 2), (key1150, 2)]

theorem rawRowCheck8294 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form2 = rawRow8294 := by decide +kernel

def row8294 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8294 : row8294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8294 := by decide +kernel

theorem rowEval8294 (x : Key → ℝ) : Integer.Sparse.eval row8294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8294, Integer.Sparse.eval_collectBalanced, rawRowCheck8294]

def rawRow8295 : Integer.Sparse Key := [(key1235, -6), (key1232, -6), (key1232, -6), (key1242, -6), (key1015, 2), (key1001, 2), (key1001, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1150, 2), (key1150, 2), (key1071, 2)]

theorem rawRowCheck8295 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form2 = rawRow8295 := by decide +kernel

def row8295 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8295 : row8295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8295 := by decide +kernel

theorem rowEval8295 (x : Key → ℝ) : Integer.Sparse.eval row8295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8295, Integer.Sparse.eval_collectBalanced, rawRowCheck8295]

def rawRow8296 : Integer.Sparse Key := [(key1232, -6), (key1232, -6), (key1242, -6), (key1235, -6), (key1036, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1150, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1123, 2)]

theorem rawRowCheck8296 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form2 = rawRow8296 := by decide +kernel

def row8296 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8296 : row8296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8296 := by decide +kernel

theorem rowEval8296 (x : Key → ℝ) : Integer.Sparse.eval row8296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8296, Integer.Sparse.eval_collectBalanced, rawRowCheck8296]

def rawRow8297 : Integer.Sparse Key := [(key1232, -6), (key1242, -6), (key1232, -6), (key1235, -6), (key1036, 2), (key1071, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1015, 2), (key1123, 2)]

theorem rawRowCheck8297 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form2 = rawRow8297 := by decide +kernel

def row8297 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8297 : row8297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8297 := by decide +kernel

theorem rowEval8297 (x : Key → ℝ) : Integer.Sparse.eval row8297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8297, Integer.Sparse.eval_collectBalanced, rawRowCheck8297]

def rawRow8298 : Integer.Sparse Key := [(key1242, -6), (key1232, -6), (key1232, -6), (key1235, -6), (key1071, 2), (key1036, 2), (key1036, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1123, 2), (key1123, 2), (key1015, 2)]

theorem rawRowCheck8298 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form2 = rawRow8298 := by decide +kernel

def row8298 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8298 : row8298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8298 := by decide +kernel

theorem rowEval8298 (x : Key → ℝ) : Integer.Sparse.eval row8298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8298, Integer.Sparse.eval_collectBalanced, rawRowCheck8298]

def rawRow8299 : Integer.Sparse Key := [(key1232, -6), (key1235, -6), (key1242, -6), (key1232, -6), (key1114, 2), (key1123, 2), (key1150, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1123, 2), (key1071, 2), (key1150, 2), (key1001, 2), (key1036, 2), (key1114, 2)]

theorem rawRowCheck8299 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form2 = rawRow8299 := by decide +kernel

def row8299 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8299 : row8299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8299 := by decide +kernel

theorem rowEval8299 (x : Key → ℝ) : Integer.Sparse.eval row8299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8299, Integer.Sparse.eval_collectBalanced, rawRowCheck8299]

def rawRow8300 : Integer.Sparse Key := [(key1235, -6), (key1232, -6), (key1242, -6), (key1232, -6), (key1123, 2), (key1114, 2), (key1150, 2), (key1015, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1071, 2), (key1001, 2), (key1114, 2), (key1036, 2)]

theorem rawRowCheck8300 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form2 = rawRow8300 := by decide +kernel

def row8300 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8300 : row8300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8300 := by decide +kernel

theorem rowEval8300 (x : Key → ℝ) : Integer.Sparse.eval row8300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8300, Integer.Sparse.eval_collectBalanced, rawRowCheck8300]

def rawRow8301 : Integer.Sparse Key := [(key1232, -6), (key1242, -6), (key1235, -6), (key1232, -6), (key1114, 2), (key1150, 2), (key1123, 2), (key1036, 2), (key1071, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1001, 2), (key1114, 2)]

theorem rawRowCheck8301 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form2 = rawRow8301 := by decide +kernel

def row8301 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8301 : row8301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8301 := by decide +kernel

theorem rowEval8301 (x : Key → ℝ) : Integer.Sparse.eval row8301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8301, Integer.Sparse.eval_collectBalanced, rawRowCheck8301]

def rawRow8302 : Integer.Sparse Key := [(key1242, -6), (key1232, -6), (key1235, -6), (key1232, -6), (key1150, 2), (key1114, 2), (key1123, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1114, 2), (key1001, 2)]

theorem rawRowCheck8302 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form2 = rawRow8302 := by decide +kernel

def row8302 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8302 : row8302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8302 := by decide +kernel

theorem rowEval8302 (x : Key → ℝ) : Integer.Sparse.eval row8302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8302, Integer.Sparse.eval_collectBalanced, rawRowCheck8302]

def rawRow8303 : Integer.Sparse Key := [(key1235, -6), (key1242, -6), (key1232, -6), (key1232, -6), (key1123, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1001, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2)]

theorem rawRowCheck8303 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form2 = rawRow8303 := by decide +kernel

def row8303 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8303 : row8303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8303 := by decide +kernel

theorem rowEval8303 (x : Key → ℝ) : Integer.Sparse.eval row8303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8303, Integer.Sparse.eval_collectBalanced, rawRowCheck8303]

def rawRow8304 : Integer.Sparse Key := [(key1242, -6), (key1235, -6), (key1232, -6), (key1232, -6), (key1150, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1071, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1001, 2)]

theorem rawRowCheck8304 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form2 = rawRow8304 := by decide +kernel

def row8304 : Integer.Sparse Key := [(key1001, 4), (key1015, 2), (key1036, 4), (key1071, 2), (key1114, 4), (key1123, 4), (key1150, 4), (key1232, -12), (key1235, -6), (key1242, -6)]

theorem rowCheck8304 : row8304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8304 := by decide +kernel

theorem rowEval8304 (x : Key → ℝ) : Integer.Sparse.eval row8304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8304, Integer.Sparse.eval_collectBalanced, rawRowCheck8304]

def rawRow8305 : Integer.Sparse Key := [(key2635, -6), (key2789, -6), (key2855, -6), (key2855, -6), (key2610, 2), (key2626, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2700, 2), (key2780, 2), (key2780, 2), (key2803, 2), (key2803, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck8305 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form3 = rawRow8305 := by decide +kernel

def row8305 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8305 : row8305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8305 := by decide +kernel

theorem rowEval8305 (x : Key → ℝ) : Integer.Sparse.eval row8305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8305, Integer.Sparse.eval_collectBalanced, rawRowCheck8305]

def rawRow8306 : Integer.Sparse Key := [(key2635, -6), (key2855, -6), (key2789, -6), (key2855, -6), (key2626, 2), (key2610, 2), (key2626, 2), (key2700, 2), (key2665, 2), (key2700, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2853, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck8306 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form3 = rawRow8306 := by decide +kernel

def row8306 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8306 : row8306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8306 := by decide +kernel

theorem rowEval8306 (x : Key → ℝ) : Integer.Sparse.eval row8306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8306, Integer.Sparse.eval_collectBalanced, rawRowCheck8306]

def rawRow8307 : Integer.Sparse Key := [(key2635, -6), (key2855, -6), (key2855, -6), (key2789, -6), (key2626, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2700, 2), (key2665, 2), (key2853, 2), (key2803, 2), (key2853, 2), (key2780, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck8307 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form3 = rawRow8307 := by decide +kernel

def row8307 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8307 : row8307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8307 := by decide +kernel

theorem rowEval8307 (x : Key → ℝ) : Integer.Sparse.eval row8307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8307, Integer.Sparse.eval_collectBalanced, rawRowCheck8307]

def rawRow8308 : Integer.Sparse Key := [(key2789, -6), (key2635, -6), (key2855, -6), (key2855, -6), (key2665, 2), (key2780, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2803, 2), (key2626, 2), (key2626, 2), (key2700, 2), (key2700, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck8308 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form3 = rawRow8308 := by decide +kernel

def row8308 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8308 : row8308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8308 := by decide +kernel

theorem rowEval8308 (x : Key → ℝ) : Integer.Sparse.eval row8308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8308, Integer.Sparse.eval_collectBalanced, rawRowCheck8308]

def rawRow8309 : Integer.Sparse Key := [(key2789, -6), (key2855, -6), (key2635, -6), (key2855, -6), (key2780, 2), (key2665, 2), (key2780, 2), (key2803, 2), (key2610, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2853, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck8309 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form3 = rawRow8309 := by decide +kernel

def row8309 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8309 : row8309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8309 := by decide +kernel

theorem rowEval8309 (x : Key → ℝ) : Integer.Sparse.eval row8309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8309, Integer.Sparse.eval_collectBalanced, rawRowCheck8309]

def rawRow8310 : Integer.Sparse Key := [(key2789, -6), (key2855, -6), (key2855, -6), (key2635, -6), (key2780, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2803, 2), (key2610, 2), (key2853, 2), (key2700, 2), (key2853, 2), (key2626, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck8310 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form3 = rawRow8310 := by decide +kernel

def row8310 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8310 : row8310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8310 := by decide +kernel

theorem rowEval8310 (x : Key → ℝ) : Integer.Sparse.eval row8310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8310, Integer.Sparse.eval_collectBalanced, rawRowCheck8310]

def rawRow8311 : Integer.Sparse Key := [(key2855, -6), (key2635, -6), (key2789, -6), (key2855, -6), (key2700, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2853, 2), (key2610, 2), (key2626, 2), (key2665, 2), (key2700, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck8311 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form3 = rawRow8311 := by decide +kernel

def row8311 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8311 : row8311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8311 := by decide +kernel

theorem rowEval8311 (x : Key → ℝ) : Integer.Sparse.eval row8311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8311, Integer.Sparse.eval_collectBalanced, rawRowCheck8311]

def rawRow8312 : Integer.Sparse Key := [(key2855, -6), (key2635, -6), (key2855, -6), (key2789, -6), (key2700, 2), (key2853, 2), (key2803, 2), (key2626, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2610, 2), (key2700, 2), (key2665, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck8312 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form3 = rawRow8312 := by decide +kernel

def row8312 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8312 : row8312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8312 := by decide +kernel

theorem rowEval8312 (x : Key → ℝ) : Integer.Sparse.eval row8312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8312, Integer.Sparse.eval_collectBalanced, rawRowCheck8312]

def rawRow8313 : Integer.Sparse Key := [(key2855, -6), (key2789, -6), (key2635, -6), (key2855, -6), (key2803, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2853, 2), (key2665, 2), (key2780, 2), (key2610, 2), (key2803, 2), (key2626, 2), (key2700, 2)]

theorem rawRowCheck8313 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form3 = rawRow8313 := by decide +kernel

def row8313 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8313 : row8313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8313 := by decide +kernel

theorem rowEval8313 (x : Key → ℝ) : Integer.Sparse.eval row8313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8313, Integer.Sparse.eval_collectBalanced, rawRowCheck8313]

def rawRow8314 : Integer.Sparse Key := [(key2855, -6), (key2789, -6), (key2855, -6), (key2635, -6), (key2803, 2), (key2853, 2), (key2700, 2), (key2780, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2665, 2), (key2803, 2), (key2610, 2), (key2700, 2), (key2626, 2)]

theorem rawRowCheck8314 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form3 = rawRow8314 := by decide +kernel

def row8314 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8314 : row8314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8314 := by decide +kernel

theorem rowEval8314 (x : Key → ℝ) : Integer.Sparse.eval row8314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8314, Integer.Sparse.eval_collectBalanced, rawRowCheck8314]

def rawRow8315 : Integer.Sparse Key := [(key2855, -6), (key2855, -6), (key2635, -6), (key2789, -6), (key2853, 2), (key2700, 2), (key2803, 2), (key2853, 2), (key2626, 2), (key2780, 2), (key2700, 2), (key2803, 2), (key2626, 2), (key2780, 2), (key2610, 2), (key2665, 2)]

theorem rawRowCheck8315 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form3 = rawRow8315 := by decide +kernel

def row8315 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8315 : row8315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8315 := by decide +kernel

theorem rowEval8315 (x : Key → ℝ) : Integer.Sparse.eval row8315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8315, Integer.Sparse.eval_collectBalanced, rawRowCheck8315]

def rawRow8316 : Integer.Sparse Key := [(key2855, -6), (key2855, -6), (key2789, -6), (key2635, -6), (key2853, 2), (key2803, 2), (key2700, 2), (key2853, 2), (key2780, 2), (key2626, 2), (key2803, 2), (key2700, 2), (key2780, 2), (key2626, 2), (key2665, 2), (key2610, 2)]

theorem rawRowCheck8316 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form3 = rawRow8316 := by decide +kernel

def row8316 : Integer.Sparse Key := [(key2610, 2), (key2626, 4), (key2635, -6), (key2665, 2), (key2700, 4), (key2780, 4), (key2789, -6), (key2803, 4), (key2853, 4), (key2855, -12)]

theorem rowCheck8316 : row8316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8316 := by decide +kernel

theorem rowEval8316 (x : Key → ℝ) : Integer.Sparse.eval row8316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8316, Integer.Sparse.eval_collectBalanced, rawRowCheck8316]

def rawRow8317 : Integer.Sparse Key := [(key2568, -6), (key2568, -6), (key2570, -6), (key2575, -6), (key2376, 2), (key2376, 2), (key2388, 2), (key2404, 2), (key2404, 2), (key2470, 2), (key2470, 2), (key2478, 2), (key2478, 2), (key2435, 2), (key2501, 2), (key2501, 2)]

theorem rawRowCheck8317 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form4 = rawRow8317 := by decide +kernel

def row8317 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8317 : row8317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8317 := by decide +kernel

theorem rowEval8317 (x : Key → ℝ) : Integer.Sparse.eval row8317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8317, Integer.Sparse.eval_collectBalanced, rawRowCheck8317]

def rawRow8318 : Integer.Sparse Key := [(key2568, -6), (key2570, -6), (key2568, -6), (key2575, -6), (key2376, 2), (key2388, 2), (key2376, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2501, 2), (key2435, 2), (key2501, 2)]

theorem rawRowCheck8318 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form4 = rawRow8318 := by decide +kernel

def row8318 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8318 : row8318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8318 := by decide +kernel

theorem rowEval8318 (x : Key → ℝ) : Integer.Sparse.eval row8318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8318, Integer.Sparse.eval_collectBalanced, rawRowCheck8318]

def rawRow8319 : Integer.Sparse Key := [(key2570, -6), (key2568, -6), (key2568, -6), (key2575, -6), (key2388, 2), (key2376, 2), (key2376, 2), (key2478, 2), (key2470, 2), (key2478, 2), (key2404, 2), (key2470, 2), (key2404, 2), (key2501, 2), (key2501, 2), (key2435, 2)]

theorem rawRowCheck8319 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form4 = rawRow8319 := by decide +kernel

def row8319 : Integer.Sparse Key := [(key2376, 4), (key2388, 2), (key2404, 4), (key2435, 2), (key2470, 4), (key2478, 4), (key2501, 4), (key2568, -12), (key2570, -6), (key2575, -6)]

theorem rowCheck8319 : row8319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8319 := by decide +kernel

theorem rowEval8319 (x : Key → ℝ) : Integer.Sparse.eval row8319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8319, Integer.Sparse.eval_collectBalanced, rawRowCheck8319]

end MUB6.Certificate.GramRows

end OAI
