import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8064 : Integer.Sparse Key := [(key1590, -6), (key1570, -6), (key1570, -6), (key1293, -6), (key1630, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1621, 2), (key1323, 2), (key1619, 2), (key1421, 2), (key1619, 2), (key1313, 2), (key1421, 2), (key1313, 2)]

theorem rawRowCheck8064 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form3 = rawRow8064 := by decide +kernel

def row8064 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8064 : row8064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8064 := by decide +kernel

theorem rowEval8064 (x : Key → ℝ) : Integer.Sparse.eval row8064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8064, Integer.Sparse.eval_collectBalanced, rawRowCheck8064]

def rawRow8065 : Integer.Sparse Key := [(key1313, -6), (key1543, -6), (key1619, -6), (key1630, -6), (key1293, 2), (key1313, 2), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, 2), (key1553, 2), (key1570, 2), (key1590, 2), (key1621, 2), (key1630, 2)]

theorem rawRowCheck8065 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form3 = rawRow8065 := by decide +kernel

def row8065 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8065 : row8065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8065 := by decide +kernel

theorem rowEval8065 (x : Key → ℝ) : Integer.Sparse.eval row8065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8065, Integer.Sparse.eval_collectBalanced, rawRowCheck8065]

def rawRow8066 : Integer.Sparse Key := [(key1313, -6), (key1543, -6), (key1630, -6), (key1619, -6), (key1293, 2), (key1323, 2), (key1313, 2), (key1388, 2), (key1441, 2), (key1421, 2), (key1553, 2), (key1543, 2), (key1590, 2), (key1570, 2), (key1630, 2), (key1621, 2)]

theorem rawRowCheck8066 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form3 = rawRow8066 := by decide +kernel

def row8066 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8066 : row8066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8066 := by decide +kernel

theorem rowEval8066 (x : Key → ℝ) : Integer.Sparse.eval row8066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8066, Integer.Sparse.eval_collectBalanced, rawRowCheck8066]

def rawRow8067 : Integer.Sparse Key := [(key1313, -6), (key1619, -6), (key1543, -6), (key1630, -6), (key1313, 2), (key1293, 2), (key1323, 2), (key1421, 2), (key1388, 2), (key1441, 2), (key1570, 2), (key1621, 2), (key1543, 2), (key1630, 2), (key1553, 2), (key1590, 2)]

theorem rawRowCheck8067 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form3 = rawRow8067 := by decide +kernel

def row8067 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8067 : row8067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8067 := by decide +kernel

theorem rowEval8067 (x : Key → ℝ) : Integer.Sparse.eval row8067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8067, Integer.Sparse.eval_collectBalanced, rawRowCheck8067]

def rawRow8068 : Integer.Sparse Key := [(key1313, -6), (key1619, -6), (key1630, -6), (key1543, -6), (key1313, 2), (key1323, 2), (key1293, 2), (key1421, 2), (key1441, 2), (key1388, 2), (key1621, 2), (key1570, 2), (key1630, 2), (key1543, 2), (key1590, 2), (key1553, 2)]

theorem rawRowCheck8068 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form3 = rawRow8068 := by decide +kernel

def row8068 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8068 : row8068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8068 := by decide +kernel

theorem rowEval8068 (x : Key → ℝ) : Integer.Sparse.eval row8068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8068, Integer.Sparse.eval_collectBalanced, rawRowCheck8068]

def rawRow8069 : Integer.Sparse Key := [(key1313, -6), (key1630, -6), (key1543, -6), (key1619, -6), (key1323, 2), (key1293, 2), (key1313, 2), (key1441, 2), (key1388, 2), (key1421, 2), (key1590, 2), (key1630, 2), (key1553, 2), (key1621, 2), (key1543, 2), (key1570, 2)]

theorem rawRowCheck8069 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form3 = rawRow8069 := by decide +kernel

def row8069 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8069 : row8069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8069 := by decide +kernel

theorem rowEval8069 (x : Key → ℝ) : Integer.Sparse.eval row8069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8069, Integer.Sparse.eval_collectBalanced, rawRowCheck8069]

def rawRow8070 : Integer.Sparse Key := [(key1313, -6), (key1630, -6), (key1619, -6), (key1543, -6), (key1323, 2), (key1313, 2), (key1293, 2), (key1441, 2), (key1421, 2), (key1388, 2), (key1630, 2), (key1590, 2), (key1621, 2), (key1553, 2), (key1570, 2), (key1543, 2)]

theorem rawRowCheck8070 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form3 = rawRow8070 := by decide +kernel

def row8070 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8070 : row8070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8070 := by decide +kernel

theorem rowEval8070 (x : Key → ℝ) : Integer.Sparse.eval row8070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8070, Integer.Sparse.eval_collectBalanced, rawRowCheck8070]

def rawRow8071 : Integer.Sparse Key := [(key1543, -6), (key1313, -6), (key1619, -6), (key1630, -6), (key1388, 2), (key1543, 2), (key1553, 2), (key1293, 2), (key1570, 2), (key1590, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1441, 2), (key1621, 2), (key1630, 2)]

theorem rawRowCheck8071 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form3 = rawRow8071 := by decide +kernel

def row8071 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8071 : row8071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8071 := by decide +kernel

theorem rowEval8071 (x : Key → ℝ) : Integer.Sparse.eval row8071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8071, Integer.Sparse.eval_collectBalanced, rawRowCheck8071]

def rawRow8072 : Integer.Sparse Key := [(key1543, -6), (key1313, -6), (key1630, -6), (key1619, -6), (key1388, 2), (key1553, 2), (key1543, 2), (key1293, 2), (key1590, 2), (key1570, 2), (key1323, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1630, 2), (key1621, 2)]

theorem rawRowCheck8072 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form3 = rawRow8072 := by decide +kernel

def row8072 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8072 : row8072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8072 := by decide +kernel

theorem rowEval8072 (x : Key → ℝ) : Integer.Sparse.eval row8072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8072, Integer.Sparse.eval_collectBalanced, rawRowCheck8072]

def rawRow8073 : Integer.Sparse Key := [(key1543, -6), (key1619, -6), (key1313, -6), (key1630, -6), (key1543, 2), (key1388, 2), (key1553, 2), (key1570, 2), (key1293, 2), (key1590, 2), (key1421, 2), (key1621, 2), (key1313, 2), (key1630, 2), (key1323, 2), (key1441, 2)]

theorem rawRowCheck8073 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form3 = rawRow8073 := by decide +kernel

def row8073 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8073 : row8073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8073 := by decide +kernel

theorem rowEval8073 (x : Key → ℝ) : Integer.Sparse.eval row8073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8073, Integer.Sparse.eval_collectBalanced, rawRowCheck8073]

def rawRow8074 : Integer.Sparse Key := [(key1543, -6), (key1619, -6), (key1630, -6), (key1313, -6), (key1543, 2), (key1553, 2), (key1388, 2), (key1570, 2), (key1590, 2), (key1293, 2), (key1621, 2), (key1421, 2), (key1630, 2), (key1313, 2), (key1441, 2), (key1323, 2)]

theorem rawRowCheck8074 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form3 = rawRow8074 := by decide +kernel

def row8074 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8074 : row8074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8074 := by decide +kernel

theorem rowEval8074 (x : Key → ℝ) : Integer.Sparse.eval row8074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8074, Integer.Sparse.eval_collectBalanced, rawRowCheck8074]

def rawRow8075 : Integer.Sparse Key := [(key1543, -6), (key1630, -6), (key1313, -6), (key1619, -6), (key1553, 2), (key1388, 2), (key1543, 2), (key1590, 2), (key1293, 2), (key1570, 2), (key1441, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1313, 2), (key1421, 2)]

theorem rawRowCheck8075 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form3 = rawRow8075 := by decide +kernel

def row8075 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8075 : row8075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8075 := by decide +kernel

theorem rowEval8075 (x : Key → ℝ) : Integer.Sparse.eval row8075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8075, Integer.Sparse.eval_collectBalanced, rawRowCheck8075]

def rawRow8076 : Integer.Sparse Key := [(key1543, -6), (key1630, -6), (key1619, -6), (key1313, -6), (key1553, 2), (key1543, 2), (key1388, 2), (key1590, 2), (key1570, 2), (key1293, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1323, 2), (key1421, 2), (key1313, 2)]

theorem rawRowCheck8076 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form3 = rawRow8076 := by decide +kernel

def row8076 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8076 : row8076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8076 := by decide +kernel

theorem rowEval8076 (x : Key → ℝ) : Integer.Sparse.eval row8076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8076, Integer.Sparse.eval_collectBalanced, rawRowCheck8076]

def rawRow8077 : Integer.Sparse Key := [(key1619, -6), (key1313, -6), (key1543, -6), (key1630, -6), (key1421, 2), (key1570, 2), (key1621, 2), (key1313, 2), (key1543, 2), (key1630, 2), (key1293, 2), (key1323, 2), (key1388, 2), (key1441, 2), (key1553, 2), (key1590, 2)]

theorem rawRowCheck8077 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form3 = rawRow8077 := by decide +kernel

def row8077 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8077 : row8077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8077 := by decide +kernel

theorem rowEval8077 (x : Key → ℝ) : Integer.Sparse.eval row8077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8077, Integer.Sparse.eval_collectBalanced, rawRowCheck8077]

def rawRow8078 : Integer.Sparse Key := [(key1619, -6), (key1313, -6), (key1630, -6), (key1543, -6), (key1421, 2), (key1621, 2), (key1570, 2), (key1313, 2), (key1630, 2), (key1543, 2), (key1323, 2), (key1293, 2), (key1441, 2), (key1388, 2), (key1590, 2), (key1553, 2)]

theorem rawRowCheck8078 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form3 = rawRow8078 := by decide +kernel

def row8078 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8078 : row8078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8078 := by decide +kernel

theorem rowEval8078 (x : Key → ℝ) : Integer.Sparse.eval row8078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8078, Integer.Sparse.eval_collectBalanced, rawRowCheck8078]

def rawRow8079 : Integer.Sparse Key := [(key1619, -6), (key1543, -6), (key1313, -6), (key1630, -6), (key1570, 2), (key1421, 2), (key1621, 2), (key1543, 2), (key1313, 2), (key1630, 2), (key1388, 2), (key1553, 2), (key1293, 2), (key1590, 2), (key1323, 2), (key1441, 2)]

theorem rawRowCheck8079 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form3 = rawRow8079 := by decide +kernel

def row8079 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8079 : row8079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8079 := by decide +kernel

theorem rowEval8079 (x : Key → ℝ) : Integer.Sparse.eval row8079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8079, Integer.Sparse.eval_collectBalanced, rawRowCheck8079]

def rawRow8080 : Integer.Sparse Key := [(key1619, -6), (key1543, -6), (key1630, -6), (key1313, -6), (key1570, 2), (key1621, 2), (key1421, 2), (key1543, 2), (key1630, 2), (key1313, 2), (key1553, 2), (key1388, 2), (key1590, 2), (key1293, 2), (key1441, 2), (key1323, 2)]

theorem rawRowCheck8080 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form3 = rawRow8080 := by decide +kernel

def row8080 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8080 : row8080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8080 := by decide +kernel

theorem rowEval8080 (x : Key → ℝ) : Integer.Sparse.eval row8080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8080, Integer.Sparse.eval_collectBalanced, rawRowCheck8080]

def rawRow8081 : Integer.Sparse Key := [(key1619, -6), (key1630, -6), (key1313, -6), (key1543, -6), (key1621, 2), (key1421, 2), (key1570, 2), (key1630, 2), (key1313, 2), (key1543, 2), (key1441, 2), (key1590, 2), (key1323, 2), (key1553, 2), (key1293, 2), (key1388, 2)]

theorem rawRowCheck8081 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form3 = rawRow8081 := by decide +kernel

def row8081 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8081 : row8081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8081 := by decide +kernel

theorem rowEval8081 (x : Key → ℝ) : Integer.Sparse.eval row8081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8081, Integer.Sparse.eval_collectBalanced, rawRowCheck8081]

def rawRow8082 : Integer.Sparse Key := [(key1619, -6), (key1630, -6), (key1543, -6), (key1313, -6), (key1621, 2), (key1570, 2), (key1421, 2), (key1630, 2), (key1543, 2), (key1313, 2), (key1590, 2), (key1441, 2), (key1553, 2), (key1323, 2), (key1388, 2), (key1293, 2)]

theorem rawRowCheck8082 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form3 = rawRow8082 := by decide +kernel

def row8082 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8082 : row8082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8082 := by decide +kernel

theorem rowEval8082 (x : Key → ℝ) : Integer.Sparse.eval row8082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8082, Integer.Sparse.eval_collectBalanced, rawRowCheck8082]

def rawRow8083 : Integer.Sparse Key := [(key1630, -6), (key1313, -6), (key1543, -6), (key1619, -6), (key1441, 2), (key1590, 2), (key1630, 2), (key1323, 2), (key1553, 2), (key1621, 2), (key1293, 2), (key1313, 2), (key1388, 2), (key1421, 2), (key1543, 2), (key1570, 2)]

theorem rawRowCheck8083 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form3 = rawRow8083 := by decide +kernel

def row8083 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8083 : row8083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8083 := by decide +kernel

theorem rowEval8083 (x : Key → ℝ) : Integer.Sparse.eval row8083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8083, Integer.Sparse.eval_collectBalanced, rawRowCheck8083]

def rawRow8084 : Integer.Sparse Key := [(key1630, -6), (key1313, -6), (key1619, -6), (key1543, -6), (key1441, 2), (key1630, 2), (key1590, 2), (key1323, 2), (key1621, 2), (key1553, 2), (key1313, 2), (key1293, 2), (key1421, 2), (key1388, 2), (key1570, 2), (key1543, 2)]

theorem rawRowCheck8084 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form3 = rawRow8084 := by decide +kernel

def row8084 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8084 : row8084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8084 := by decide +kernel

theorem rowEval8084 (x : Key → ℝ) : Integer.Sparse.eval row8084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8084, Integer.Sparse.eval_collectBalanced, rawRowCheck8084]

def rawRow8085 : Integer.Sparse Key := [(key1630, -6), (key1543, -6), (key1313, -6), (key1619, -6), (key1590, 2), (key1441, 2), (key1630, 2), (key1553, 2), (key1323, 2), (key1621, 2), (key1388, 2), (key1543, 2), (key1293, 2), (key1570, 2), (key1313, 2), (key1421, 2)]

theorem rawRowCheck8085 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form3 = rawRow8085 := by decide +kernel

def row8085 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8085 : row8085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8085 := by decide +kernel

theorem rowEval8085 (x : Key → ℝ) : Integer.Sparse.eval row8085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8085, Integer.Sparse.eval_collectBalanced, rawRowCheck8085]

def rawRow8086 : Integer.Sparse Key := [(key1630, -6), (key1543, -6), (key1619, -6), (key1313, -6), (key1590, 2), (key1630, 2), (key1441, 2), (key1553, 2), (key1621, 2), (key1323, 2), (key1543, 2), (key1388, 2), (key1570, 2), (key1293, 2), (key1421, 2), (key1313, 2)]

theorem rawRowCheck8086 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form3 = rawRow8086 := by decide +kernel

def row8086 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8086 : row8086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8086 := by decide +kernel

theorem rowEval8086 (x : Key → ℝ) : Integer.Sparse.eval row8086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8086, Integer.Sparse.eval_collectBalanced, rawRowCheck8086]

def rawRow8087 : Integer.Sparse Key := [(key1630, -6), (key1619, -6), (key1313, -6), (key1543, -6), (key1630, 2), (key1441, 2), (key1590, 2), (key1621, 2), (key1323, 2), (key1553, 2), (key1421, 2), (key1570, 2), (key1313, 2), (key1543, 2), (key1293, 2), (key1388, 2)]

theorem rawRowCheck8087 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form3 = rawRow8087 := by decide +kernel

def row8087 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8087 : row8087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8087 := by decide +kernel

theorem rowEval8087 (x : Key → ℝ) : Integer.Sparse.eval row8087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck8087, Integer.Sparse.eval_collectBalanced, rawRowCheck8087]

def rawRow8088 : Integer.Sparse Key := [(key1630, -6), (key1619, -6), (key1543, -6), (key1313, -6), (key1630, 2), (key1590, 2), (key1441, 2), (key1621, 2), (key1553, 2), (key1323, 2), (key1570, 2), (key1421, 2), (key1543, 2), (key1313, 2), (key1388, 2), (key1293, 2)]

theorem rawRowCheck8088 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form3 = rawRow8088 := by decide +kernel

def row8088 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, 2), (key1421, 2), (key1441, 2), (key1543, -4), (key1553, 2), (key1570, 2), (key1590, 2), (key1619, -6), (key1621, 2), (key1630, -4)]

theorem rowCheck8088 : row8088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8088 := by decide +kernel

theorem rowEval8088 (x : Key → ℝ) : Integer.Sparse.eval row8088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8088, Integer.Sparse.eval_collectBalanced, rawRowCheck8088]

def rawRow8089 : Integer.Sparse Key := [(key1526, -6), (key1534, -6), (key1534, -6), (key1894, -6), (key1251, 2), (key1259, 2), (key1259, 2), (key1604, 2), (key1612, 2), (key1604, 2), (key1640, 2), (key1612, 2), (key1640, 2), (key1916, 2), (key1916, 2), (key1930, 2)]

theorem rawRowCheck8089 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form4 = rawRow8089 := by decide +kernel

def row8089 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8089 : row8089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8089 := by decide +kernel

theorem rowEval8089 (x : Key → ℝ) : Integer.Sparse.eval row8089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8089, Integer.Sparse.eval_collectBalanced, rawRowCheck8089]

def rawRow8090 : Integer.Sparse Key := [(key1534, -6), (key1526, -6), (key1534, -6), (key1894, -6), (key1259, 2), (key1251, 2), (key1259, 2), (key1612, 2), (key1604, 2), (key1640, 2), (key1604, 2), (key1640, 2), (key1612, 2), (key1916, 2), (key1930, 2), (key1916, 2)]

theorem rawRowCheck8090 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form4 = rawRow8090 := by decide +kernel

def row8090 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8090 : row8090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8090 := by decide +kernel

theorem rowEval8090 (x : Key → ℝ) : Integer.Sparse.eval row8090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8090, Integer.Sparse.eval_collectBalanced, rawRowCheck8090]

def rawRow8091 : Integer.Sparse Key := [(key1534, -6), (key1534, -6), (key1526, -6), (key1894, -6), (key1259, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1640, 2), (key1612, 2), (key1612, 2), (key1604, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1916, 2)]

theorem rawRowCheck8091 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form4 = rawRow8091 := by decide +kernel

def row8091 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8091 : row8091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8091 := by decide +kernel

theorem rowEval8091 (x : Key → ℝ) : Integer.Sparse.eval row8091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8091, Integer.Sparse.eval_collectBalanced, rawRowCheck8091]

def rawRow8092 : Integer.Sparse Key := [(key1526, -6), (key1534, -6), (key1894, -6), (key1534, -6), (key1604, 2), (key1612, 2), (key1916, 2), (key1251, 2), (key1259, 2), (key1604, 2), (key1640, 2), (key1916, 2), (key1930, 2), (key1259, 2), (key1612, 2), (key1640, 2)]

theorem rawRowCheck8092 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form4 = rawRow8092 := by decide +kernel

def row8092 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8092 : row8092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8092 := by decide +kernel

theorem rowEval8092 (x : Key → ℝ) : Integer.Sparse.eval row8092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8092, Integer.Sparse.eval_collectBalanced, rawRowCheck8092]

def rawRow8093 : Integer.Sparse Key := [(key1534, -6), (key1526, -6), (key1894, -6), (key1534, -6), (key1612, 2), (key1604, 2), (key1916, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1259, 2), (key1640, 2), (key1612, 2)]

theorem rawRowCheck8093 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form4 = rawRow8093 := by decide +kernel

def row8093 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8093 : row8093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8093 := by decide +kernel

theorem rowEval8093 (x : Key → ℝ) : Integer.Sparse.eval row8093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8093, Integer.Sparse.eval_collectBalanced, rawRowCheck8093]

def rawRow8094 : Integer.Sparse Key := [(key1526, -6), (key1894, -6), (key1534, -6), (key1534, -6), (key1604, 2), (key1916, 2), (key1612, 2), (key1604, 2), (key1916, 2), (key1251, 2), (key1930, 2), (key1259, 2), (key1640, 2), (key1612, 2), (key1259, 2), (key1640, 2)]

theorem rawRowCheck8094 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form4 = rawRow8094 := by decide +kernel

def row8094 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8094 : row8094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8094 := by decide +kernel

theorem rowEval8094 (x : Key → ℝ) : Integer.Sparse.eval row8094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8094, Integer.Sparse.eval_collectBalanced, rawRowCheck8094]

def rawRow8095 : Integer.Sparse Key := [(key1894, -6), (key1526, -6), (key1534, -6), (key1534, -6), (key1916, 2), (key1604, 2), (key1612, 2), (key1916, 2), (key1604, 2), (key1930, 2), (key1251, 2), (key1640, 2), (key1259, 2), (key1612, 2), (key1640, 2), (key1259, 2)]

theorem rawRowCheck8095 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form4 = rawRow8095 := by decide +kernel

def row8095 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8095 : row8095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8095 := by decide +kernel

theorem rowEval8095 (x : Key → ℝ) : Integer.Sparse.eval row8095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8095, Integer.Sparse.eval_collectBalanced, rawRowCheck8095]

def rawRow8096 : Integer.Sparse Key := [(key1534, -6), (key1894, -6), (key1526, -6), (key1534, -6), (key1612, 2), (key1916, 2), (key1604, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1640, 2), (key1259, 2), (key1612, 2)]

theorem rawRowCheck8096 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form4 = rawRow8096 := by decide +kernel

def row8096 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8096 : row8096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8096 := by decide +kernel

theorem rowEval8096 (x : Key → ℝ) : Integer.Sparse.eval row8096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8096, Integer.Sparse.eval_collectBalanced, rawRowCheck8096]

def rawRow8097 : Integer.Sparse Key := [(key1894, -6), (key1534, -6), (key1526, -6), (key1534, -6), (key1916, 2), (key1612, 2), (key1604, 2), (key1930, 2), (key1640, 2), (key1916, 2), (key1259, 2), (key1604, 2), (key1251, 2), (key1640, 2), (key1612, 2), (key1259, 2)]

theorem rawRowCheck8097 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form4 = rawRow8097 := by decide +kernel

def row8097 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8097 : row8097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8097 := by decide +kernel

theorem rowEval8097 (x : Key → ℝ) : Integer.Sparse.eval row8097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8097, Integer.Sparse.eval_collectBalanced, rawRowCheck8097]

def rawRow8098 : Integer.Sparse Key := [(key1534, -6), (key1534, -6), (key1894, -6), (key1526, -6), (key1640, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1259, 2), (key1612, 2), (key1612, 2), (key1916, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1604, 2)]

theorem rawRowCheck8098 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form4 = rawRow8098 := by decide +kernel

def row8098 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8098 : row8098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8098 := by decide +kernel

theorem rowEval8098 (x : Key → ℝ) : Integer.Sparse.eval row8098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8098, Integer.Sparse.eval_collectBalanced, rawRowCheck8098]

def rawRow8099 : Integer.Sparse Key := [(key1534, -6), (key1894, -6), (key1534, -6), (key1526, -6), (key1640, 2), (key1930, 2), (key1640, 2), (key1612, 2), (key1916, 2), (key1259, 2), (key1916, 2), (key1259, 2), (key1612, 2), (key1604, 2), (key1251, 2), (key1604, 2)]

theorem rawRowCheck8099 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form4 = rawRow8099 := by decide +kernel

def row8099 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8099 : row8099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8099 := by decide +kernel

theorem rowEval8099 (x : Key → ℝ) : Integer.Sparse.eval row8099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8099, Integer.Sparse.eval_collectBalanced, rawRowCheck8099]

def rawRow8100 : Integer.Sparse Key := [(key1894, -6), (key1534, -6), (key1534, -6), (key1526, -6), (key1930, 2), (key1640, 2), (key1640, 2), (key1916, 2), (key1612, 2), (key1916, 2), (key1259, 2), (key1612, 2), (key1259, 2), (key1604, 2), (key1604, 2), (key1251, 2)]

theorem rawRowCheck8100 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form4 = rawRow8100 := by decide +kernel

def row8100 : Integer.Sparse Key := [(key1251, 2), (key1259, 4), (key1526, -6), (key1534, -12), (key1604, 4), (key1612, 4), (key1640, 4), (key1894, -6), (key1916, 4), (key1930, 2)]

theorem rowCheck8100 : row8100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8100 := by decide +kernel

theorem rowEval8100 (x : Key → ℝ) : Integer.Sparse.eval row8100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8100, Integer.Sparse.eval_collectBalanced, rawRowCheck8100]

def rawRow8101 : Integer.Sparse Key := [(key1604, -6), (key1612, -6), (key1679, -6), (key1916, -6), (key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, 2), (key1640, 2), (key1679, 2), (key1693, 2), (key1894, 2), (key1916, 2), (key1930, 2)]

theorem rawRowCheck8101 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form4 = rawRow8101 := by decide +kernel

def row8101 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8101 : row8101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8101 := by decide +kernel

theorem rowEval8101 (x : Key → ℝ) : Integer.Sparse.eval row8101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8101, Integer.Sparse.eval_collectBalanced, rawRowCheck8101]

def rawRow8102 : Integer.Sparse Key := [(key1612, -6), (key1604, -6), (key1679, -6), (key1916, -6), (key1259, 2), (key1251, 2), (key1271, 2), (key1534, 2), (key1526, 2), (key1640, 2), (key1604, 2), (key1693, 2), (key1679, 2), (key1894, 2), (key1930, 2), (key1916, 2)]

theorem rawRowCheck8102 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form4 = rawRow8102 := by decide +kernel

def row8102 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8102 : row8102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8102 := by decide +kernel

theorem rowEval8102 (x : Key → ℝ) : Integer.Sparse.eval row8102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8102, Integer.Sparse.eval_collectBalanced, rawRowCheck8102]

def rawRow8103 : Integer.Sparse Key := [(key1604, -6), (key1679, -6), (key1612, -6), (key1916, -6), (key1251, 2), (key1271, 2), (key1259, 2), (key1604, 2), (key1679, 2), (key1526, 2), (key1693, 2), (key1534, 2), (key1640, 2), (key1916, 2), (key1894, 2), (key1930, 2)]

theorem rawRowCheck8103 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form4 = rawRow8103 := by decide +kernel

def row8103 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8103 : row8103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8103 := by decide +kernel

theorem rowEval8103 (x : Key → ℝ) : Integer.Sparse.eval row8103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8103, Integer.Sparse.eval_collectBalanced, rawRowCheck8103]

def rawRow8104 : Integer.Sparse Key := [(key1679, -6), (key1604, -6), (key1612, -6), (key1916, -6), (key1271, 2), (key1251, 2), (key1259, 2), (key1679, 2), (key1604, 2), (key1693, 2), (key1526, 2), (key1640, 2), (key1534, 2), (key1916, 2), (key1930, 2), (key1894, 2)]

theorem rawRowCheck8104 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form4 = rawRow8104 := by decide +kernel

def row8104 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8104 : row8104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8104 := by decide +kernel

theorem rowEval8104 (x : Key → ℝ) : Integer.Sparse.eval row8104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8104, Integer.Sparse.eval_collectBalanced, rawRowCheck8104]

def rawRow8105 : Integer.Sparse Key := [(key1612, -6), (key1679, -6), (key1604, -6), (key1916, -6), (key1259, 2), (key1271, 2), (key1251, 2), (key1640, 2), (key1693, 2), (key1534, 2), (key1679, 2), (key1526, 2), (key1604, 2), (key1930, 2), (key1894, 2), (key1916, 2)]

theorem rawRowCheck8105 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form4 = rawRow8105 := by decide +kernel

def row8105 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8105 : row8105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8105 := by decide +kernel

theorem rowEval8105 (x : Key → ℝ) : Integer.Sparse.eval row8105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8105, Integer.Sparse.eval_collectBalanced, rawRowCheck8105]

def rawRow8106 : Integer.Sparse Key := [(key1679, -6), (key1612, -6), (key1604, -6), (key1916, -6), (key1271, 2), (key1259, 2), (key1251, 2), (key1693, 2), (key1640, 2), (key1679, 2), (key1534, 2), (key1604, 2), (key1526, 2), (key1930, 2), (key1916, 2), (key1894, 2)]

theorem rawRowCheck8106 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form4 = rawRow8106 := by decide +kernel

def row8106 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8106 : row8106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8106 := by decide +kernel

theorem rowEval8106 (x : Key → ℝ) : Integer.Sparse.eval row8106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8106, Integer.Sparse.eval_collectBalanced, rawRowCheck8106]

def rawRow8107 : Integer.Sparse Key := [(key1604, -6), (key1612, -6), (key1916, -6), (key1679, -6), (key1526, 2), (key1534, 2), (key1894, 2), (key1251, 2), (key1259, 2), (key1604, 2), (key1640, 2), (key1916, 2), (key1930, 2), (key1271, 2), (key1679, 2), (key1693, 2)]

theorem rawRowCheck8107 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form4 = rawRow8107 := by decide +kernel

def row8107 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8107 : row8107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8107 := by decide +kernel

theorem rowEval8107 (x : Key → ℝ) : Integer.Sparse.eval row8107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8107, Integer.Sparse.eval_collectBalanced, rawRowCheck8107]

def rawRow8108 : Integer.Sparse Key := [(key1612, -6), (key1604, -6), (key1916, -6), (key1679, -6), (key1534, 2), (key1526, 2), (key1894, 2), (key1259, 2), (key1251, 2), (key1640, 2), (key1604, 2), (key1930, 2), (key1916, 2), (key1271, 2), (key1693, 2), (key1679, 2)]

theorem rawRowCheck8108 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form4 = rawRow8108 := by decide +kernel

def row8108 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8108 : row8108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8108 := by decide +kernel

theorem rowEval8108 (x : Key → ℝ) : Integer.Sparse.eval row8108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8108, Integer.Sparse.eval_collectBalanced, rawRowCheck8108]

def rawRow8109 : Integer.Sparse Key := [(key1604, -6), (key1916, -6), (key1612, -6), (key1679, -6), (key1526, 2), (key1894, 2), (key1534, 2), (key1604, 2), (key1916, 2), (key1251, 2), (key1930, 2), (key1259, 2), (key1640, 2), (key1679, 2), (key1271, 2), (key1693, 2)]

theorem rawRowCheck8109 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form4 = rawRow8109 := by decide +kernel

def row8109 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8109 : row8109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8109 := by decide +kernel

theorem rowEval8109 (x : Key → ℝ) : Integer.Sparse.eval row8109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8109, Integer.Sparse.eval_collectBalanced, rawRowCheck8109]

def rawRow8110 : Integer.Sparse Key := [(key1916, -6), (key1604, -6), (key1612, -6), (key1679, -6), (key1894, 2), (key1526, 2), (key1534, 2), (key1916, 2), (key1604, 2), (key1930, 2), (key1251, 2), (key1640, 2), (key1259, 2), (key1679, 2), (key1693, 2), (key1271, 2)]

theorem rawRowCheck8110 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form4 = rawRow8110 := by decide +kernel

def row8110 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8110 : row8110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8110 := by decide +kernel

theorem rowEval8110 (x : Key → ℝ) : Integer.Sparse.eval row8110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8110, Integer.Sparse.eval_collectBalanced, rawRowCheck8110]

def rawRow8111 : Integer.Sparse Key := [(key1612, -6), (key1916, -6), (key1604, -6), (key1679, -6), (key1534, 2), (key1894, 2), (key1526, 2), (key1640, 2), (key1930, 2), (key1259, 2), (key1916, 2), (key1251, 2), (key1604, 2), (key1693, 2), (key1271, 2), (key1679, 2)]

theorem rawRowCheck8111 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form4 = rawRow8111 := by decide +kernel

def row8111 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8111 : row8111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8111 := by decide +kernel

theorem rowEval8111 (x : Key → ℝ) : Integer.Sparse.eval row8111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8111, Integer.Sparse.eval_collectBalanced, rawRowCheck8111]

def rawRow8112 : Integer.Sparse Key := [(key1916, -6), (key1612, -6), (key1604, -6), (key1679, -6), (key1894, 2), (key1534, 2), (key1526, 2), (key1930, 2), (key1640, 2), (key1916, 2), (key1259, 2), (key1604, 2), (key1251, 2), (key1693, 2), (key1679, 2), (key1271, 2)]

theorem rawRowCheck8112 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form4 = rawRow8112 := by decide +kernel

def row8112 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8112 : row8112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8112 := by decide +kernel

theorem rowEval8112 (x : Key → ℝ) : Integer.Sparse.eval row8112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8112, Integer.Sparse.eval_collectBalanced, rawRowCheck8112]

def rawRow8113 : Integer.Sparse Key := [(key1604, -6), (key1679, -6), (key1916, -6), (key1612, -6), (key1604, 2), (key1679, 2), (key1916, 2), (key1251, 2), (key1271, 2), (key1526, 2), (key1693, 2), (key1894, 2), (key1930, 2), (key1259, 2), (key1534, 2), (key1640, 2)]

theorem rawRowCheck8113 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form4 = rawRow8113 := by decide +kernel

def row8113 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8113 : row8113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8113 := by decide +kernel

theorem rowEval8113 (x : Key → ℝ) : Integer.Sparse.eval row8113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8113, Integer.Sparse.eval_collectBalanced, rawRowCheck8113]

def rawRow8114 : Integer.Sparse Key := [(key1679, -6), (key1604, -6), (key1916, -6), (key1612, -6), (key1679, 2), (key1604, 2), (key1916, 2), (key1271, 2), (key1251, 2), (key1693, 2), (key1526, 2), (key1930, 2), (key1894, 2), (key1259, 2), (key1640, 2), (key1534, 2)]

theorem rawRowCheck8114 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form4 = rawRow8114 := by decide +kernel

def row8114 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8114 : row8114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8114 := by decide +kernel

theorem rowEval8114 (x : Key → ℝ) : Integer.Sparse.eval row8114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8114, Integer.Sparse.eval_collectBalanced, rawRowCheck8114]

def rawRow8115 : Integer.Sparse Key := [(key1604, -6), (key1916, -6), (key1679, -6), (key1612, -6), (key1604, 2), (key1916, 2), (key1679, 2), (key1526, 2), (key1894, 2), (key1251, 2), (key1930, 2), (key1271, 2), (key1693, 2), (key1534, 2), (key1259, 2), (key1640, 2)]

theorem rawRowCheck8115 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form4 = rawRow8115 := by decide +kernel

def row8115 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8115 : row8115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8115 := by decide +kernel

theorem rowEval8115 (x : Key → ℝ) : Integer.Sparse.eval row8115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8115, Integer.Sparse.eval_collectBalanced, rawRowCheck8115]

def rawRow8116 : Integer.Sparse Key := [(key1916, -6), (key1604, -6), (key1679, -6), (key1612, -6), (key1916, 2), (key1604, 2), (key1679, 2), (key1894, 2), (key1526, 2), (key1930, 2), (key1251, 2), (key1693, 2), (key1271, 2), (key1534, 2), (key1640, 2), (key1259, 2)]

theorem rawRowCheck8116 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form4 = rawRow8116 := by decide +kernel

def row8116 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8116 : row8116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8116 := by decide +kernel

theorem rowEval8116 (x : Key → ℝ) : Integer.Sparse.eval row8116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8116, Integer.Sparse.eval_collectBalanced, rawRowCheck8116]

def rawRow8117 : Integer.Sparse Key := [(key1679, -6), (key1916, -6), (key1604, -6), (key1612, -6), (key1679, 2), (key1916, 2), (key1604, 2), (key1693, 2), (key1930, 2), (key1271, 2), (key1894, 2), (key1251, 2), (key1526, 2), (key1640, 2), (key1259, 2), (key1534, 2)]

theorem rawRowCheck8117 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form4 = rawRow8117 := by decide +kernel

def row8117 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8117 : row8117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8117 := by decide +kernel

theorem rowEval8117 (x : Key → ℝ) : Integer.Sparse.eval row8117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8117, Integer.Sparse.eval_collectBalanced, rawRowCheck8117]

def rawRow8118 : Integer.Sparse Key := [(key1916, -6), (key1679, -6), (key1604, -6), (key1612, -6), (key1916, 2), (key1679, 2), (key1604, 2), (key1930, 2), (key1693, 2), (key1894, 2), (key1271, 2), (key1526, 2), (key1251, 2), (key1640, 2), (key1534, 2), (key1259, 2)]

theorem rawRowCheck8118 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form4 = rawRow8118 := by decide +kernel

def row8118 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8118 : row8118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8118 := by decide +kernel

theorem rowEval8118 (x : Key → ℝ) : Integer.Sparse.eval row8118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8118, Integer.Sparse.eval_collectBalanced, rawRowCheck8118]

def rawRow8119 : Integer.Sparse Key := [(key1612, -6), (key1679, -6), (key1916, -6), (key1604, -6), (key1640, 2), (key1693, 2), (key1930, 2), (key1259, 2), (key1271, 2), (key1534, 2), (key1679, 2), (key1894, 2), (key1916, 2), (key1251, 2), (key1526, 2), (key1604, 2)]

theorem rawRowCheck8119 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form4 = rawRow8119 := by decide +kernel

def row8119 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8119 : row8119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8119 := by decide +kernel

theorem rowEval8119 (x : Key → ℝ) : Integer.Sparse.eval row8119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8119, Integer.Sparse.eval_collectBalanced, rawRowCheck8119]

def rawRow8120 : Integer.Sparse Key := [(key1679, -6), (key1612, -6), (key1916, -6), (key1604, -6), (key1693, 2), (key1640, 2), (key1930, 2), (key1271, 2), (key1259, 2), (key1679, 2), (key1534, 2), (key1916, 2), (key1894, 2), (key1251, 2), (key1604, 2), (key1526, 2)]

theorem rawRowCheck8120 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form4 = rawRow8120 := by decide +kernel

def row8120 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8120 : row8120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8120 := by decide +kernel

theorem rowEval8120 (x : Key → ℝ) : Integer.Sparse.eval row8120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8120, Integer.Sparse.eval_collectBalanced, rawRowCheck8120]

def rawRow8121 : Integer.Sparse Key := [(key1612, -6), (key1916, -6), (key1679, -6), (key1604, -6), (key1640, 2), (key1930, 2), (key1693, 2), (key1534, 2), (key1894, 2), (key1259, 2), (key1916, 2), (key1271, 2), (key1679, 2), (key1526, 2), (key1251, 2), (key1604, 2)]

theorem rawRowCheck8121 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form4 = rawRow8121 := by decide +kernel

def row8121 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8121 : row8121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8121 := by decide +kernel

theorem rowEval8121 (x : Key → ℝ) : Integer.Sparse.eval row8121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck8121, Integer.Sparse.eval_collectBalanced, rawRowCheck8121]

def rawRow8122 : Integer.Sparse Key := [(key1916, -6), (key1612, -6), (key1679, -6), (key1604, -6), (key1930, 2), (key1640, 2), (key1693, 2), (key1894, 2), (key1534, 2), (key1916, 2), (key1259, 2), (key1679, 2), (key1271, 2), (key1526, 2), (key1604, 2), (key1251, 2)]

theorem rawRowCheck8122 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form4 = rawRow8122 := by decide +kernel

def row8122 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8122 : row8122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8122 := by decide +kernel

theorem rowEval8122 (x : Key → ℝ) : Integer.Sparse.eval row8122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8122, Integer.Sparse.eval_collectBalanced, rawRowCheck8122]

def rawRow8123 : Integer.Sparse Key := [(key1679, -6), (key1916, -6), (key1612, -6), (key1604, -6), (key1693, 2), (key1930, 2), (key1640, 2), (key1679, 2), (key1916, 2), (key1271, 2), (key1894, 2), (key1259, 2), (key1534, 2), (key1604, 2), (key1251, 2), (key1526, 2)]

theorem rawRowCheck8123 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form4 = rawRow8123 := by decide +kernel

def row8123 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8123 : row8123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8123 := by decide +kernel

theorem rowEval8123 (x : Key → ℝ) : Integer.Sparse.eval row8123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck8123, Integer.Sparse.eval_collectBalanced, rawRowCheck8123]

def rawRow8124 : Integer.Sparse Key := [(key1916, -6), (key1679, -6), (key1612, -6), (key1604, -6), (key1930, 2), (key1693, 2), (key1640, 2), (key1916, 2), (key1679, 2), (key1894, 2), (key1271, 2), (key1534, 2), (key1259, 2), (key1604, 2), (key1526, 2), (key1251, 2)]

theorem rawRowCheck8124 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form4 = rawRow8124 := by decide +kernel

def row8124 : Integer.Sparse Key := [(key1251, 2), (key1259, 2), (key1271, 2), (key1526, 2), (key1534, 2), (key1604, -4), (key1612, -6), (key1640, 2), (key1679, -4), (key1693, 2), (key1894, 2), (key1916, -4), (key1930, 2)]

theorem rowCheck8124 : row8124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8124 := by decide +kernel

theorem rowEval8124 (x : Key → ℝ) : Integer.Sparse.eval row8124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck8124, Integer.Sparse.eval_collectBalanced, rawRowCheck8124]

def rawRow8125 : Integer.Sparse Key := [(key1291, -2), (key1299, -2), (key1299, -2), (key1568, -2), (key1576, -2), (key1568, -2), (key1594, -2), (key1576, -2), (key1594, -2), (key1904, -2), (key1904, -2), (key1912, -2), (key1311, 1), (key1319, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1327, 1), (key1419, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1445, 1), (key1617, 1), (key1625, 1), (key1617, 1), (key1634, 1), (key1625, 1), (key1634, 1), (key1919, 1), (key1921, 1), (key1919, 1), (key1927, 1), (key1921, 1), (key1927, 1)]

theorem rawRowCheck8125 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form5 = rawRow8125 := by decide +kernel

def row8125 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8125 : row8125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8125 := by decide +kernel

theorem rowEval8125 (x : Key → ℝ) : Integer.Sparse.eval row8125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8125, Integer.Sparse.eval_collectBalanced, rawRowCheck8125]

def rawRow8126 : Integer.Sparse Key := [(key1299, -2), (key1291, -2), (key1299, -2), (key1576, -2), (key1568, -2), (key1594, -2), (key1568, -2), (key1594, -2), (key1576, -2), (key1904, -2), (key1912, -2), (key1904, -2), (key1319, 1), (key1311, 1), (key1327, 1), (key1311, 1), (key1327, 1), (key1319, 1), (key1427, 1), (key1419, 1), (key1445, 1), (key1419, 1), (key1445, 1), (key1427, 1), (key1625, 1), (key1617, 1), (key1634, 1), (key1617, 1), (key1634, 1), (key1625, 1), (key1921, 1), (key1919, 1), (key1927, 1), (key1919, 1), (key1927, 1), (key1921, 1)]

theorem rawRowCheck8126 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form5 = rawRow8126 := by decide +kernel

def row8126 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8126 : row8126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8126 := by decide +kernel

theorem rowEval8126 (x : Key → ℝ) : Integer.Sparse.eval row8126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8126, Integer.Sparse.eval_collectBalanced, rawRowCheck8126]

def rawRow8127 : Integer.Sparse Key := [(key1299, -2), (key1299, -2), (key1291, -2), (key1594, -2), (key1594, -2), (key1576, -2), (key1576, -2), (key1568, -2), (key1568, -2), (key1912, -2), (key1904, -2), (key1904, -2), (key1327, 1), (key1327, 1), (key1319, 1), (key1319, 1), (key1311, 1), (key1311, 1), (key1445, 1), (key1445, 1), (key1427, 1), (key1427, 1), (key1419, 1), (key1419, 1), (key1634, 1), (key1634, 1), (key1625, 1), (key1625, 1), (key1617, 1), (key1617, 1), (key1927, 1), (key1927, 1), (key1921, 1), (key1921, 1), (key1919, 1), (key1919, 1)]

theorem rawRowCheck8127 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form5 = rawRow8127 := by decide +kernel

def row8127 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8127 : row8127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8127 := by decide +kernel

theorem rowEval8127 (x : Key → ℝ) : Integer.Sparse.eval row8127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8127, Integer.Sparse.eval_collectBalanced, rawRowCheck8127]

def rawRow8128 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1904, -2), (key1291, -2), (key1299, -2), (key1568, -2), (key1594, -2), (key1904, -2), (key1912, -2), (key1299, -2), (key1576, -2), (key1594, -2), (key1419, 1), (key1427, 1), (key1617, 1), (key1625, 1), (key1919, 1), (key1921, 1), (key1311, 1), (key1319, 1), (key1617, 1), (key1634, 1), (key1919, 1), (key1927, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1921, 1), (key1927, 1), (key1319, 1), (key1327, 1), (key1427, 1), (key1445, 1), (key1625, 1), (key1634, 1)]

theorem rawRowCheck8128 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form5 = rawRow8128 := by decide +kernel

def row8128 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8128 : row8128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8128 := by decide +kernel

theorem rowEval8128 (x : Key → ℝ) : Integer.Sparse.eval row8128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8128, Integer.Sparse.eval_collectBalanced, rawRowCheck8128]

def rawRow8129 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1904, -2), (key1299, -2), (key1291, -2), (key1594, -2), (key1568, -2), (key1912, -2), (key1904, -2), (key1299, -2), (key1594, -2), (key1576, -2), (key1427, 1), (key1419, 1), (key1625, 1), (key1617, 1), (key1921, 1), (key1919, 1), (key1319, 1), (key1311, 1), (key1634, 1), (key1617, 1), (key1927, 1), (key1919, 1), (key1327, 1), (key1311, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1921, 1), (key1327, 1), (key1319, 1), (key1445, 1), (key1427, 1), (key1634, 1), (key1625, 1)]

theorem rawRowCheck8129 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form5 = rawRow8129 := by decide +kernel

def row8129 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8129 : row8129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8129 := by decide +kernel

theorem rowEval8129 (x : Key → ℝ) : Integer.Sparse.eval row8129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8129, Integer.Sparse.eval_collectBalanced, rawRowCheck8129]

def rawRow8130 : Integer.Sparse Key := [(key1568, -2), (key1904, -2), (key1576, -2), (key1568, -2), (key1904, -2), (key1291, -2), (key1912, -2), (key1299, -2), (key1594, -2), (key1576, -2), (key1299, -2), (key1594, -2), (key1617, 1), (key1919, 1), (key1419, 1), (key1921, 1), (key1427, 1), (key1625, 1), (key1617, 1), (key1919, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1419, 1), (key1921, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1427, 1), (key1625, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1445, 1)]

theorem rawRowCheck8130 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form5 = rawRow8130 := by decide +kernel

def row8130 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8130 : row8130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8130 := by decide +kernel

theorem rowEval8130 (x : Key → ℝ) : Integer.Sparse.eval row8130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8130, Integer.Sparse.eval_collectBalanced, rawRowCheck8130]

def rawRow8131 : Integer.Sparse Key := [(key1904, -2), (key1568, -2), (key1576, -2), (key1904, -2), (key1568, -2), (key1912, -2), (key1291, -2), (key1594, -2), (key1299, -2), (key1576, -2), (key1594, -2), (key1299, -2), (key1919, 1), (key1617, 1), (key1921, 1), (key1419, 1), (key1625, 1), (key1427, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1634, 1), (key1319, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1445, 1), (key1327, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1445, 1), (key1327, 1)]

theorem rawRowCheck8131 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form5 = rawRow8131 := by decide +kernel

def row8131 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8131 : row8131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8131 := by decide +kernel

theorem rowEval8131 (x : Key → ℝ) : Integer.Sparse.eval row8131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8131, Integer.Sparse.eval_collectBalanced, rawRowCheck8131]

def rawRow8132 : Integer.Sparse Key := [(key1576, -2), (key1904, -2), (key1568, -2), (key1594, -2), (key1912, -2), (key1299, -2), (key1904, -2), (key1291, -2), (key1568, -2), (key1594, -2), (key1299, -2), (key1576, -2), (key1625, 1), (key1921, 1), (key1427, 1), (key1919, 1), (key1419, 1), (key1617, 1), (key1634, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1311, 1), (key1617, 1), (key1445, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1311, 1), (key1419, 1), (key1445, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1319, 1), (key1427, 1)]

theorem rawRowCheck8132 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form5 = rawRow8132 := by decide +kernel

def row8132 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8132 : row8132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8132 := by decide +kernel

theorem rowEval8132 (x : Key → ℝ) : Integer.Sparse.eval row8132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8132, Integer.Sparse.eval_collectBalanced, rawRowCheck8132]

def rawRow8133 : Integer.Sparse Key := [(key1904, -2), (key1576, -2), (key1568, -2), (key1912, -2), (key1594, -2), (key1904, -2), (key1299, -2), (key1568, -2), (key1291, -2), (key1594, -2), (key1576, -2), (key1299, -2), (key1921, 1), (key1625, 1), (key1919, 1), (key1427, 1), (key1617, 1), (key1419, 1), (key1927, 1), (key1634, 1), (key1919, 1), (key1319, 1), (key1617, 1), (key1311, 1), (key1927, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1634, 1), (key1445, 1), (key1625, 1), (key1327, 1), (key1427, 1), (key1319, 1)]

theorem rawRowCheck8133 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form5 = rawRow8133 := by decide +kernel

def row8133 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8133 : row8133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8133 := by decide +kernel

theorem rowEval8133 (x : Key → ℝ) : Integer.Sparse.eval row8133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8133, Integer.Sparse.eval_collectBalanced, rawRowCheck8133]

def rawRow8134 : Integer.Sparse Key := [(key1594, -2), (key1594, -2), (key1912, -2), (key1299, -2), (key1299, -2), (key1576, -2), (key1576, -2), (key1904, -2), (key1904, -2), (key1291, -2), (key1568, -2), (key1568, -2), (key1445, 1), (key1445, 1), (key1634, 1), (key1634, 1), (key1927, 1), (key1927, 1), (key1327, 1), (key1327, 1), (key1625, 1), (key1625, 1), (key1921, 1), (key1921, 1), (key1319, 1), (key1319, 1), (key1427, 1), (key1427, 1), (key1919, 1), (key1919, 1), (key1311, 1), (key1311, 1), (key1419, 1), (key1419, 1), (key1617, 1), (key1617, 1)]

theorem rawRowCheck8134 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form5 = rawRow8134 := by decide +kernel

def row8134 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8134 : row8134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8134 := by decide +kernel

theorem rowEval8134 (x : Key → ℝ) : Integer.Sparse.eval row8134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8134, Integer.Sparse.eval_collectBalanced, rawRowCheck8134]

def rawRow8135 : Integer.Sparse Key := [(key1594, -2), (key1912, -2), (key1594, -2), (key1576, -2), (key1904, -2), (key1299, -2), (key1904, -2), (key1299, -2), (key1576, -2), (key1568, -2), (key1291, -2), (key1568, -2), (key1634, 1), (key1927, 1), (key1445, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1427, 1), (key1919, 1), (key1319, 1), (key1919, 1), (key1319, 1), (key1427, 1), (key1419, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1419, 1)]

theorem rawRowCheck8135 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form5 = rawRow8135 := by decide +kernel

def row8135 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8135 : row8135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8135 := by decide +kernel

theorem rowEval8135 (x : Key → ℝ) : Integer.Sparse.eval row8135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8135, Integer.Sparse.eval_collectBalanced, rawRowCheck8135]

def rawRow8136 : Integer.Sparse Key := [(key1912, -2), (key1594, -2), (key1594, -2), (key1904, -2), (key1576, -2), (key1904, -2), (key1299, -2), (key1576, -2), (key1299, -2), (key1568, -2), (key1568, -2), (key1291, -2), (key1927, 1), (key1634, 1), (key1927, 1), (key1445, 1), (key1634, 1), (key1445, 1), (key1921, 1), (key1625, 1), (key1921, 1), (key1327, 1), (key1625, 1), (key1327, 1), (key1919, 1), (key1427, 1), (key1919, 1), (key1319, 1), (key1427, 1), (key1319, 1), (key1617, 1), (key1419, 1), (key1617, 1), (key1311, 1), (key1419, 1), (key1311, 1)]

theorem rawRowCheck8136 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form5 = rawRow8136 := by decide +kernel

def row8136 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1419, 2), (key1427, 2), (key1445, 2), (key1568, -4), (key1576, -4), (key1594, -4), (key1617, 2), (key1625, 2), (key1634, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1921, 2), (key1927, 2)]

theorem rowCheck8136 : row8136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8136 := by decide +kernel

theorem rowEval8136 (x : Key → ℝ) : Integer.Sparse.eval row8136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8136, Integer.Sparse.eval_collectBalanced, rawRowCheck8136]

def rawRow8137 : Integer.Sparse Key := [(key1311, -2), (key1319, -2), (key1352, -2), (key1541, -2), (key1549, -2), (key1617, -2), (key1634, -2), (key1682, -2), (key1690, -2), (key1897, -2), (key1919, -2), (key1927, -2), (key1291, 1), (key1299, 1), (key1311, 1), (key1327, 1), (key1352, 1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, 1), (key1557, 1), (key1568, 1), (key1594, 1), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1921, 1), (key1927, 1)]

theorem rawRowCheck8137 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form5 = rawRow8137 := by decide +kernel

def row8137 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8137 : row8137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8137 := by decide +kernel

theorem rowEval8137 (x : Key → ℝ) : Integer.Sparse.eval row8137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8137, Integer.Sparse.eval_collectBalanced, rawRowCheck8137]

def rawRow8138 : Integer.Sparse Key := [(key1319, -2), (key1311, -2), (key1352, -2), (key1549, -2), (key1541, -2), (key1634, -2), (key1617, -2), (key1690, -2), (key1682, -2), (key1897, -2), (key1927, -2), (key1919, -2), (key1299, 1), (key1291, 1), (key1327, 1), (key1311, 1), (key1355, 1), (key1352, 1), (key1394, 1), (key1386, 1), (key1445, 1), (key1419, 1), (key1481, 1), (key1473, 1), (key1557, 1), (key1541, 1), (key1594, 1), (key1568, 1), (key1690, 1), (key1684, 1), (key1900, 1), (key1897, 1), (key1912, 1), (key1904, 1), (key1927, 1), (key1921, 1)]

theorem rawRowCheck8138 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form5 = rawRow8138 := by decide +kernel

def row8138 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8138 : row8138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8138 := by decide +kernel

theorem rowEval8138 (x : Key → ℝ) : Integer.Sparse.eval row8138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8138, Integer.Sparse.eval_collectBalanced, rawRowCheck8138]

def rawRow8139 : Integer.Sparse Key := [(key1311, -2), (key1352, -2), (key1319, -2), (key1617, -2), (key1682, -2), (key1541, -2), (key1690, -2), (key1549, -2), (key1634, -2), (key1919, -2), (key1897, -2), (key1927, -2), (key1311, 1), (key1352, 1), (key1291, 1), (key1355, 1), (key1299, 1), (key1327, 1), (key1419, 1), (key1473, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1568, 1), (key1684, 1), (key1541, 1), (key1690, 1), (key1557, 1), (key1594, 1), (key1904, 1), (key1921, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1912, 1)]

theorem rawRowCheck8139 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form5 = rawRow8139 := by decide +kernel

def row8139 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8139 : row8139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8139 := by decide +kernel

theorem rowEval8139 (x : Key → ℝ) : Integer.Sparse.eval row8139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8139, Integer.Sparse.eval_collectBalanced, rawRowCheck8139]

def rawRow8140 : Integer.Sparse Key := [(key1352, -2), (key1311, -2), (key1319, -2), (key1682, -2), (key1617, -2), (key1690, -2), (key1541, -2), (key1634, -2), (key1549, -2), (key1919, -2), (key1927, -2), (key1897, -2), (key1352, 1), (key1311, 1), (key1355, 1), (key1291, 1), (key1327, 1), (key1299, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1445, 1), (key1394, 1), (key1684, 1), (key1568, 1), (key1690, 1), (key1541, 1), (key1594, 1), (key1557, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1912, 1), (key1900, 1)]

theorem rawRowCheck8140 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form5 = rawRow8140 := by decide +kernel

def row8140 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8140 : row8140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8140 := by decide +kernel

theorem rowEval8140 (x : Key → ℝ) : Integer.Sparse.eval row8140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8140, Integer.Sparse.eval_collectBalanced, rawRowCheck8140]

def rawRow8141 : Integer.Sparse Key := [(key1319, -2), (key1352, -2), (key1311, -2), (key1634, -2), (key1690, -2), (key1549, -2), (key1682, -2), (key1541, -2), (key1617, -2), (key1927, -2), (key1897, -2), (key1919, -2), (key1327, 1), (key1355, 1), (key1299, 1), (key1352, 1), (key1291, 1), (key1311, 1), (key1445, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1386, 1), (key1419, 1), (key1594, 1), (key1690, 1), (key1557, 1), (key1684, 1), (key1541, 1), (key1568, 1), (key1912, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1897, 1), (key1904, 1)]

theorem rawRowCheck8141 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form5 = rawRow8141 := by decide +kernel

def row8141 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8141 : row8141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8141 := by decide +kernel

theorem rowEval8141 (x : Key → ℝ) : Integer.Sparse.eval row8141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8141, Integer.Sparse.eval_collectBalanced, rawRowCheck8141]

def rawRow8142 : Integer.Sparse Key := [(key1352, -2), (key1319, -2), (key1311, -2), (key1690, -2), (key1634, -2), (key1682, -2), (key1549, -2), (key1617, -2), (key1541, -2), (key1927, -2), (key1919, -2), (key1897, -2), (key1355, 1), (key1327, 1), (key1352, 1), (key1299, 1), (key1311, 1), (key1291, 1), (key1481, 1), (key1445, 1), (key1473, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1690, 1), (key1594, 1), (key1684, 1), (key1557, 1), (key1568, 1), (key1541, 1), (key1927, 1), (key1912, 1), (key1921, 1), (key1900, 1), (key1904, 1), (key1897, 1)]

theorem rawRowCheck8142 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form5 = rawRow8142 := by decide +kernel

def row8142 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8142 : row8142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8142 := by decide +kernel

theorem rowEval8142 (x : Key → ℝ) : Integer.Sparse.eval row8142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8142, Integer.Sparse.eval_collectBalanced, rawRowCheck8142]

def rawRow8143 : Integer.Sparse Key := [(key1541, -2), (key1549, -2), (key1897, -2), (key1311, -2), (key1319, -2), (key1617, -2), (key1634, -2), (key1919, -2), (key1927, -2), (key1352, -2), (key1682, -2), (key1690, -2), (key1386, 1), (key1394, 1), (key1541, 1), (key1557, 1), (key1897, 1), (key1900, 1), (key1291, 1), (key1299, 1), (key1568, 1), (key1594, 1), (key1904, 1), (key1912, 1), (key1311, 1), (key1327, 1), (key1419, 1), (key1445, 1), (key1921, 1), (key1927, 1), (key1352, 1), (key1355, 1), (key1473, 1), (key1481, 1), (key1684, 1), (key1690, 1)]

theorem rawRowCheck8143 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form5 = rawRow8143 := by decide +kernel

def row8143 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8143 : row8143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8143 := by decide +kernel

theorem rowEval8143 (x : Key → ℝ) : Integer.Sparse.eval row8143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8143, Integer.Sparse.eval_collectBalanced, rawRowCheck8143]

def rawRow8144 : Integer.Sparse Key := [(key1549, -2), (key1541, -2), (key1897, -2), (key1319, -2), (key1311, -2), (key1634, -2), (key1617, -2), (key1927, -2), (key1919, -2), (key1352, -2), (key1690, -2), (key1682, -2), (key1394, 1), (key1386, 1), (key1557, 1), (key1541, 1), (key1900, 1), (key1897, 1), (key1299, 1), (key1291, 1), (key1594, 1), (key1568, 1), (key1912, 1), (key1904, 1), (key1327, 1), (key1311, 1), (key1445, 1), (key1419, 1), (key1927, 1), (key1921, 1), (key1355, 1), (key1352, 1), (key1481, 1), (key1473, 1), (key1690, 1), (key1684, 1)]

theorem rawRowCheck8144 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form5 = rawRow8144 := by decide +kernel

def row8144 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8144 : row8144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8144 := by decide +kernel

theorem rowEval8144 (x : Key → ℝ) : Integer.Sparse.eval row8144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8144, Integer.Sparse.eval_collectBalanced, rawRowCheck8144]

def rawRow8145 : Integer.Sparse Key := [(key1541, -2), (key1897, -2), (key1549, -2), (key1617, -2), (key1919, -2), (key1311, -2), (key1927, -2), (key1319, -2), (key1634, -2), (key1682, -2), (key1352, -2), (key1690, -2), (key1541, 1), (key1897, 1), (key1386, 1), (key1900, 1), (key1394, 1), (key1557, 1), (key1568, 1), (key1904, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1419, 1), (key1921, 1), (key1311, 1), (key1927, 1), (key1327, 1), (key1445, 1), (key1473, 1), (key1684, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1481, 1)]

theorem rawRowCheck8145 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form5 = rawRow8145 := by decide +kernel

def row8145 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8145 : row8145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8145 := by decide +kernel

theorem rowEval8145 (x : Key → ℝ) : Integer.Sparse.eval row8145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8145, Integer.Sparse.eval_collectBalanced, rawRowCheck8145]

def rawRow8146 : Integer.Sparse Key := [(key1897, -2), (key1541, -2), (key1549, -2), (key1919, -2), (key1617, -2), (key1927, -2), (key1311, -2), (key1634, -2), (key1319, -2), (key1682, -2), (key1690, -2), (key1352, -2), (key1897, 1), (key1541, 1), (key1900, 1), (key1386, 1), (key1557, 1), (key1394, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1594, 1), (key1299, 1), (key1921, 1), (key1419, 1), (key1927, 1), (key1311, 1), (key1445, 1), (key1327, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1481, 1), (key1355, 1)]

theorem rawRowCheck8146 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form5 = rawRow8146 := by decide +kernel

def row8146 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8146 : row8146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8146 := by decide +kernel

theorem rowEval8146 (x : Key → ℝ) : Integer.Sparse.eval row8146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8146, Integer.Sparse.eval_collectBalanced, rawRowCheck8146]

def rawRow8147 : Integer.Sparse Key := [(key1549, -2), (key1897, -2), (key1541, -2), (key1634, -2), (key1927, -2), (key1319, -2), (key1919, -2), (key1311, -2), (key1617, -2), (key1690, -2), (key1352, -2), (key1682, -2), (key1557, 1), (key1900, 1), (key1394, 1), (key1897, 1), (key1386, 1), (key1541, 1), (key1594, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1291, 1), (key1568, 1), (key1445, 1), (key1927, 1), (key1327, 1), (key1921, 1), (key1311, 1), (key1419, 1), (key1481, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1352, 1), (key1473, 1)]

theorem rawRowCheck8147 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form5 = rawRow8147 := by decide +kernel

def row8147 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8147 : row8147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8147 := by decide +kernel

theorem rowEval8147 (x : Key → ℝ) : Integer.Sparse.eval row8147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8147, Integer.Sparse.eval_collectBalanced, rawRowCheck8147]

def rawRow8148 : Integer.Sparse Key := [(key1897, -2), (key1549, -2), (key1541, -2), (key1927, -2), (key1634, -2), (key1919, -2), (key1319, -2), (key1617, -2), (key1311, -2), (key1690, -2), (key1682, -2), (key1352, -2), (key1900, 1), (key1557, 1), (key1897, 1), (key1394, 1), (key1541, 1), (key1386, 1), (key1912, 1), (key1594, 1), (key1904, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1927, 1), (key1445, 1), (key1921, 1), (key1327, 1), (key1419, 1), (key1311, 1), (key1690, 1), (key1481, 1), (key1684, 1), (key1355, 1), (key1473, 1), (key1352, 1)]

theorem rawRowCheck8148 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form5 = rawRow8148 := by decide +kernel

def row8148 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8148 : row8148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8148 := by decide +kernel

theorem rowEval8148 (x : Key → ℝ) : Integer.Sparse.eval row8148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8148, Integer.Sparse.eval_collectBalanced, rawRowCheck8148]

def rawRow8149 : Integer.Sparse Key := [(key1617, -2), (key1682, -2), (key1919, -2), (key1311, -2), (key1352, -2), (key1541, -2), (key1690, -2), (key1897, -2), (key1927, -2), (key1319, -2), (key1549, -2), (key1634, -2), (key1419, 1), (key1473, 1), (key1568, 1), (key1684, 1), (key1904, 1), (key1921, 1), (key1311, 1), (key1352, 1), (key1541, 1), (key1690, 1), (key1897, 1), (key1927, 1), (key1291, 1), (key1355, 1), (key1386, 1), (key1481, 1), (key1900, 1), (key1912, 1), (key1299, 1), (key1327, 1), (key1394, 1), (key1445, 1), (key1557, 1), (key1594, 1)]

theorem rawRowCheck8149 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form5 = rawRow8149 := by decide +kernel

def row8149 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8149 : row8149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8149 := by decide +kernel

theorem rowEval8149 (x : Key → ℝ) : Integer.Sparse.eval row8149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8149, Integer.Sparse.eval_collectBalanced, rawRowCheck8149]

def rawRow8150 : Integer.Sparse Key := [(key1682, -2), (key1617, -2), (key1919, -2), (key1352, -2), (key1311, -2), (key1690, -2), (key1541, -2), (key1927, -2), (key1897, -2), (key1319, -2), (key1634, -2), (key1549, -2), (key1473, 1), (key1419, 1), (key1684, 1), (key1568, 1), (key1921, 1), (key1904, 1), (key1352, 1), (key1311, 1), (key1690, 1), (key1541, 1), (key1927, 1), (key1897, 1), (key1355, 1), (key1291, 1), (key1481, 1), (key1386, 1), (key1912, 1), (key1900, 1), (key1327, 1), (key1299, 1), (key1445, 1), (key1394, 1), (key1594, 1), (key1557, 1)]

theorem rawRowCheck8150 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form5 = rawRow8150 := by decide +kernel

def row8150 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8150 : row8150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8150 := by decide +kernel

theorem rowEval8150 (x : Key → ℝ) : Integer.Sparse.eval row8150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8150, Integer.Sparse.eval_collectBalanced, rawRowCheck8150]

def rawRow8151 : Integer.Sparse Key := [(key1617, -2), (key1919, -2), (key1682, -2), (key1541, -2), (key1897, -2), (key1311, -2), (key1927, -2), (key1352, -2), (key1690, -2), (key1549, -2), (key1319, -2), (key1634, -2), (key1568, 1), (key1904, 1), (key1419, 1), (key1921, 1), (key1473, 1), (key1684, 1), (key1541, 1), (key1897, 1), (key1311, 1), (key1927, 1), (key1352, 1), (key1690, 1), (key1386, 1), (key1900, 1), (key1291, 1), (key1912, 1), (key1355, 1), (key1481, 1), (key1394, 1), (key1557, 1), (key1299, 1), (key1594, 1), (key1327, 1), (key1445, 1)]

theorem rawRowCheck8151 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5 = rawRow8151 := by decide +kernel

def row8151 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8151 : row8151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8151 := by decide +kernel

theorem rowEval8151 (x : Key → ℝ) : Integer.Sparse.eval row8151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8151, Integer.Sparse.eval_collectBalanced, rawRowCheck8151]

def rawRow8152 : Integer.Sparse Key := [(key1919, -2), (key1617, -2), (key1682, -2), (key1897, -2), (key1541, -2), (key1927, -2), (key1311, -2), (key1690, -2), (key1352, -2), (key1549, -2), (key1634, -2), (key1319, -2), (key1904, 1), (key1568, 1), (key1921, 1), (key1419, 1), (key1684, 1), (key1473, 1), (key1897, 1), (key1541, 1), (key1927, 1), (key1311, 1), (key1690, 1), (key1352, 1), (key1900, 1), (key1386, 1), (key1912, 1), (key1291, 1), (key1481, 1), (key1355, 1), (key1557, 1), (key1394, 1), (key1594, 1), (key1299, 1), (key1445, 1), (key1327, 1)]

theorem rawRowCheck8152 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5 = rawRow8152 := by decide +kernel

def row8152 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8152 : row8152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8152 := by decide +kernel

theorem rowEval8152 (x : Key → ℝ) : Integer.Sparse.eval row8152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8152, Integer.Sparse.eval_collectBalanced, rawRowCheck8152]

def rawRow8153 : Integer.Sparse Key := [(key1682, -2), (key1919, -2), (key1617, -2), (key1690, -2), (key1927, -2), (key1352, -2), (key1897, -2), (key1311, -2), (key1541, -2), (key1634, -2), (key1319, -2), (key1549, -2), (key1684, 1), (key1921, 1), (key1473, 1), (key1904, 1), (key1419, 1), (key1568, 1), (key1690, 1), (key1927, 1), (key1352, 1), (key1897, 1), (key1311, 1), (key1541, 1), (key1481, 1), (key1912, 1), (key1355, 1), (key1900, 1), (key1291, 1), (key1386, 1), (key1445, 1), (key1594, 1), (key1327, 1), (key1557, 1), (key1299, 1), (key1394, 1)]

theorem rawRowCheck8153 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5 = rawRow8153 := by decide +kernel

def row8153 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8153 : row8153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8153 := by decide +kernel

theorem rowEval8153 (x : Key → ℝ) : Integer.Sparse.eval row8153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8153, Integer.Sparse.eval_collectBalanced, rawRowCheck8153]

def rawRow8154 : Integer.Sparse Key := [(key1919, -2), (key1682, -2), (key1617, -2), (key1927, -2), (key1690, -2), (key1897, -2), (key1352, -2), (key1541, -2), (key1311, -2), (key1634, -2), (key1549, -2), (key1319, -2), (key1921, 1), (key1684, 1), (key1904, 1), (key1473, 1), (key1568, 1), (key1419, 1), (key1927, 1), (key1690, 1), (key1897, 1), (key1352, 1), (key1541, 1), (key1311, 1), (key1912, 1), (key1481, 1), (key1900, 1), (key1355, 1), (key1386, 1), (key1291, 1), (key1594, 1), (key1445, 1), (key1557, 1), (key1327, 1), (key1394, 1), (key1299, 1)]

theorem rawRowCheck8154 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5 = rawRow8154 := by decide +kernel

def row8154 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8154 : row8154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8154 := by decide +kernel

theorem rowEval8154 (x : Key → ℝ) : Integer.Sparse.eval row8154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8154, Integer.Sparse.eval_collectBalanced, rawRowCheck8154]

def rawRow8155 : Integer.Sparse Key := [(key1634, -2), (key1690, -2), (key1927, -2), (key1319, -2), (key1352, -2), (key1549, -2), (key1682, -2), (key1897, -2), (key1919, -2), (key1311, -2), (key1541, -2), (key1617, -2), (key1445, 1), (key1481, 1), (key1594, 1), (key1690, 1), (key1912, 1), (key1927, 1), (key1327, 1), (key1355, 1), (key1557, 1), (key1684, 1), (key1900, 1), (key1921, 1), (key1299, 1), (key1352, 1), (key1394, 1), (key1473, 1), (key1897, 1), (key1904, 1), (key1291, 1), (key1311, 1), (key1386, 1), (key1419, 1), (key1541, 1), (key1568, 1)]

theorem rawRowCheck8155 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form5 = rawRow8155 := by decide +kernel

def row8155 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8155 : row8155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8155 := by decide +kernel

theorem rowEval8155 (x : Key → ℝ) : Integer.Sparse.eval row8155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8155, Integer.Sparse.eval_collectBalanced, rawRowCheck8155]

def rawRow8156 : Integer.Sparse Key := [(key1690, -2), (key1634, -2), (key1927, -2), (key1352, -2), (key1319, -2), (key1682, -2), (key1549, -2), (key1919, -2), (key1897, -2), (key1311, -2), (key1617, -2), (key1541, -2), (key1481, 1), (key1445, 1), (key1690, 1), (key1594, 1), (key1927, 1), (key1912, 1), (key1355, 1), (key1327, 1), (key1684, 1), (key1557, 1), (key1921, 1), (key1900, 1), (key1352, 1), (key1299, 1), (key1473, 1), (key1394, 1), (key1904, 1), (key1897, 1), (key1311, 1), (key1291, 1), (key1419, 1), (key1386, 1), (key1568, 1), (key1541, 1)]

theorem rawRowCheck8156 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form5 = rawRow8156 := by decide +kernel

def row8156 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8156 : row8156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8156 := by decide +kernel

theorem rowEval8156 (x : Key → ℝ) : Integer.Sparse.eval row8156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8156, Integer.Sparse.eval_collectBalanced, rawRowCheck8156]

def rawRow8157 : Integer.Sparse Key := [(key1634, -2), (key1927, -2), (key1690, -2), (key1549, -2), (key1897, -2), (key1319, -2), (key1919, -2), (key1352, -2), (key1682, -2), (key1541, -2), (key1311, -2), (key1617, -2), (key1594, 1), (key1912, 1), (key1445, 1), (key1927, 1), (key1481, 1), (key1690, 1), (key1557, 1), (key1900, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1394, 1), (key1897, 1), (key1299, 1), (key1904, 1), (key1352, 1), (key1473, 1), (key1386, 1), (key1541, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1419, 1)]

theorem rawRowCheck8157 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form5 = rawRow8157 := by decide +kernel

def row8157 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8157 : row8157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8157 := by decide +kernel

theorem rowEval8157 (x : Key → ℝ) : Integer.Sparse.eval row8157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck8157, Integer.Sparse.eval_collectBalanced, rawRowCheck8157]

def rawRow8158 : Integer.Sparse Key := [(key1927, -2), (key1634, -2), (key1690, -2), (key1897, -2), (key1549, -2), (key1919, -2), (key1319, -2), (key1682, -2), (key1352, -2), (key1541, -2), (key1617, -2), (key1311, -2), (key1912, 1), (key1594, 1), (key1927, 1), (key1445, 1), (key1690, 1), (key1481, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1684, 1), (key1355, 1), (key1897, 1), (key1394, 1), (key1904, 1), (key1299, 1), (key1473, 1), (key1352, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1419, 1), (key1311, 1)]

theorem rawRowCheck8158 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form5 = rawRow8158 := by decide +kernel

def row8158 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8158 : row8158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8158 := by decide +kernel

theorem rowEval8158 (x : Key → ℝ) : Integer.Sparse.eval row8158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8158, Integer.Sparse.eval_collectBalanced, rawRowCheck8158]

def rawRow8159 : Integer.Sparse Key := [(key1690, -2), (key1927, -2), (key1634, -2), (key1682, -2), (key1919, -2), (key1352, -2), (key1897, -2), (key1319, -2), (key1549, -2), (key1617, -2), (key1311, -2), (key1541, -2), (key1690, 1), (key1927, 1), (key1481, 1), (key1912, 1), (key1445, 1), (key1594, 1), (key1684, 1), (key1921, 1), (key1355, 1), (key1900, 1), (key1327, 1), (key1557, 1), (key1473, 1), (key1904, 1), (key1352, 1), (key1897, 1), (key1299, 1), (key1394, 1), (key1419, 1), (key1568, 1), (key1311, 1), (key1541, 1), (key1291, 1), (key1386, 1)]

theorem rawRowCheck8159 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form5 = rawRow8159 := by decide +kernel

def row8159 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8159 : row8159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8159 := by decide +kernel

theorem rowEval8159 (x : Key → ℝ) : Integer.Sparse.eval row8159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck8159, Integer.Sparse.eval_collectBalanced, rawRowCheck8159]

def rawRow8160 : Integer.Sparse Key := [(key1927, -2), (key1690, -2), (key1634, -2), (key1919, -2), (key1682, -2), (key1897, -2), (key1352, -2), (key1549, -2), (key1319, -2), (key1617, -2), (key1541, -2), (key1311, -2), (key1927, 1), (key1690, 1), (key1912, 1), (key1481, 1), (key1594, 1), (key1445, 1), (key1921, 1), (key1684, 1), (key1900, 1), (key1355, 1), (key1557, 1), (key1327, 1), (key1904, 1), (key1473, 1), (key1897, 1), (key1352, 1), (key1394, 1), (key1299, 1), (key1568, 1), (key1419, 1), (key1541, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

theorem rawRowCheck8160 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form5 = rawRow8160 := by decide +kernel

def row8160 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, 1), (key1394, 1), (key1419, 1), (key1445, 1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1594, 1), (key1617, -2), (key1634, -2), (key1682, -2), (key1684, 1), (key1690, -1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, 1), (key1927, -1)]

theorem rowCheck8160 : row8160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8160 := by decide +kernel

theorem rowEval8160 (x : Key → ℝ) : Integer.Sparse.eval row8160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck8160, Integer.Sparse.eval_collectBalanced, rawRowCheck8160]

def rawRow8161 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1606, 6), (key1606, 6), (key1636, 6)]

theorem rawRowCheck8161 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6 = rawRow8161 := by decide +kernel

def row8161 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8161 : row8161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8161 := by decide +kernel

theorem rowEval8161 (x : Key → ℝ) : Integer.Sparse.eval row8161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8161, Integer.Sparse.eval_collectBalanced, rawRowCheck8161]

def rawRow8162 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1606, 6), (key1636, 6), (key1606, 6)]

theorem rawRowCheck8162 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6 = rawRow8162 := by decide +kernel

def row8162 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8162 : row8162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8162 := by decide +kernel

theorem rowEval8162 (x : Key → ℝ) : Integer.Sparse.eval row8162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8162, Integer.Sparse.eval_collectBalanced, rawRowCheck8162]

def rawRow8163 : Integer.Sparse Key := [(key1528, -24), (key1253, 6), (key1636, 6), (key1606, 6), (key1606, 6)]

theorem rawRowCheck8163 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6 = rawRow8163 := by decide +kernel

def row8163 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8163 : row8163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8163 := by decide +kernel

theorem rowEval8163 (x : Key → ℝ) : Integer.Sparse.eval row8163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8163, Integer.Sparse.eval_collectBalanced, rawRowCheck8163]

def rawRow8164 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1253, 6), (key1606, 6), (key1636, 6)]

theorem rawRowCheck8164 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6 = rawRow8164 := by decide +kernel

def row8164 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8164 : row8164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8164 := by decide +kernel

theorem rowEval8164 (x : Key → ℝ) : Integer.Sparse.eval row8164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8164, Integer.Sparse.eval_collectBalanced, rawRowCheck8164]

def rawRow8165 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1253, 6), (key1636, 6), (key1606, 6)]

theorem rawRowCheck8165 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6 = rawRow8165 := by decide +kernel

def row8165 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8165 : row8165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8165 := by decide +kernel

theorem rowEval8165 (x : Key → ℝ) : Integer.Sparse.eval row8165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8165, Integer.Sparse.eval_collectBalanced, rawRowCheck8165]

def rawRow8166 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1606, 6), (key1253, 6), (key1636, 6)]

theorem rawRowCheck8166 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6 = rawRow8166 := by decide +kernel

def row8166 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8166 : row8166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8166 := by decide +kernel

theorem rowEval8166 (x : Key → ℝ) : Integer.Sparse.eval row8166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8166, Integer.Sparse.eval_collectBalanced, rawRowCheck8166]

def rawRow8167 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1606, 6), (key1636, 6), (key1253, 6)]

theorem rawRowCheck8167 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6 = rawRow8167 := by decide +kernel

def row8167 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8167 : row8167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8167 := by decide +kernel

theorem rowEval8167 (x : Key → ℝ) : Integer.Sparse.eval row8167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8167, Integer.Sparse.eval_collectBalanced, rawRowCheck8167]

def rawRow8168 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1636, 6), (key1253, 6), (key1606, 6)]

theorem rawRowCheck8168 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6 = rawRow8168 := by decide +kernel

def row8168 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8168 : row8168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8168 := by decide +kernel

theorem rowEval8168 (x : Key → ℝ) : Integer.Sparse.eval row8168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8168, Integer.Sparse.eval_collectBalanced, rawRowCheck8168]

def rawRow8169 : Integer.Sparse Key := [(key1528, -24), (key1606, 6), (key1636, 6), (key1606, 6), (key1253, 6)]

theorem rawRowCheck8169 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6 = rawRow8169 := by decide +kernel

def row8169 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8169 : row8169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8169 := by decide +kernel

theorem rowEval8169 (x : Key → ℝ) : Integer.Sparse.eval row8169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8169, Integer.Sparse.eval_collectBalanced, rawRowCheck8169]

def rawRow8170 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1253, 6), (key1606, 6), (key1606, 6)]

theorem rawRowCheck8170 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6 = rawRow8170 := by decide +kernel

def row8170 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8170 : row8170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8170 := by decide +kernel

theorem rowEval8170 (x : Key → ℝ) : Integer.Sparse.eval row8170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8170, Integer.Sparse.eval_collectBalanced, rawRowCheck8170]

def rawRow8171 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1606, 6), (key1253, 6), (key1606, 6)]

theorem rawRowCheck8171 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6 = rawRow8171 := by decide +kernel

def row8171 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8171 : row8171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8171 := by decide +kernel

theorem rowEval8171 (x : Key → ℝ) : Integer.Sparse.eval row8171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8171, Integer.Sparse.eval_collectBalanced, rawRowCheck8171]

def rawRow8172 : Integer.Sparse Key := [(key1528, -24), (key1636, 6), (key1606, 6), (key1606, 6), (key1253, 6)]

theorem rawRowCheck8172 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6 = rawRow8172 := by decide +kernel

def row8172 : Integer.Sparse Key := [(key1253, 6), (key1528, -24), (key1606, 12), (key1636, 6)]

theorem rowCheck8172 : row8172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8172 := by decide +kernel

theorem rowEval8172 (x : Key → ℝ) : Integer.Sparse.eval row8172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8172, Integer.Sparse.eval_collectBalanced, rawRowCheck8172]

def rawRow8173 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1528, 6), (key1606, 6), (key1636, 6)]

theorem rawRowCheck8173 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form6 = rawRow8173 := by decide +kernel

def row8173 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8173 : row8173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8173 := by decide +kernel

theorem rowEval8173 (x : Key → ℝ) : Integer.Sparse.eval row8173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8173, Integer.Sparse.eval_collectBalanced, rawRowCheck8173]

def rawRow8174 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1528, 6), (key1636, 6), (key1606, 6)]

theorem rawRowCheck8174 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form6 = rawRow8174 := by decide +kernel

def row8174 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8174 : row8174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8174 := by decide +kernel

theorem rowEval8174 (x : Key → ℝ) : Integer.Sparse.eval row8174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8174, Integer.Sparse.eval_collectBalanced, rawRowCheck8174]

def rawRow8175 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1606, 6), (key1528, 6), (key1636, 6)]

theorem rawRowCheck8175 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form6 = rawRow8175 := by decide +kernel

def row8175 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8175 : row8175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8175 := by decide +kernel

theorem rowEval8175 (x : Key → ℝ) : Integer.Sparse.eval row8175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8175, Integer.Sparse.eval_collectBalanced, rawRowCheck8175]

def rawRow8176 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1606, 6), (key1636, 6), (key1528, 6)]

theorem rawRowCheck8176 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form6 = rawRow8176 := by decide +kernel

def row8176 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8176 : row8176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8176 := by decide +kernel

theorem rowEval8176 (x : Key → ℝ) : Integer.Sparse.eval row8176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8176, Integer.Sparse.eval_collectBalanced, rawRowCheck8176]

def rawRow8177 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1636, 6), (key1528, 6), (key1606, 6)]

theorem rawRowCheck8177 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form6 = rawRow8177 := by decide +kernel

def row8177 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8177 : row8177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8177 := by decide +kernel

theorem rowEval8177 (x : Key → ℝ) : Integer.Sparse.eval row8177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8177, Integer.Sparse.eval_collectBalanced, rawRowCheck8177]

def rawRow8178 : Integer.Sparse Key := [(key1606, -24), (key1253, 6), (key1636, 6), (key1606, 6), (key1528, 6)]

theorem rawRowCheck8178 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form6 = rawRow8178 := by decide +kernel

def row8178 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8178 : row8178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8178 := by decide +kernel

theorem rowEval8178 (x : Key → ℝ) : Integer.Sparse.eval row8178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8178, Integer.Sparse.eval_collectBalanced, rawRowCheck8178]

def rawRow8179 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1253, 6), (key1606, 6), (key1636, 6)]

theorem rawRowCheck8179 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form6 = rawRow8179 := by decide +kernel

def row8179 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8179 : row8179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8179 := by decide +kernel

theorem rowEval8179 (x : Key → ℝ) : Integer.Sparse.eval row8179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8179, Integer.Sparse.eval_collectBalanced, rawRowCheck8179]

def rawRow8180 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1253, 6), (key1636, 6), (key1606, 6)]

theorem rawRowCheck8180 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form6 = rawRow8180 := by decide +kernel

def row8180 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8180 : row8180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8180 := by decide +kernel

theorem rowEval8180 (x : Key → ℝ) : Integer.Sparse.eval row8180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8180, Integer.Sparse.eval_collectBalanced, rawRowCheck8180]

def rawRow8181 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1606, 6), (key1253, 6), (key1636, 6)]

theorem rawRowCheck8181 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form6 = rawRow8181 := by decide +kernel

def row8181 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8181 : row8181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8181 := by decide +kernel

theorem rowEval8181 (x : Key → ℝ) : Integer.Sparse.eval row8181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8181, Integer.Sparse.eval_collectBalanced, rawRowCheck8181]

def rawRow8182 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1606, 6), (key1636, 6), (key1253, 6)]

theorem rawRowCheck8182 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form6 = rawRow8182 := by decide +kernel

def row8182 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8182 : row8182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8182 := by decide +kernel

theorem rowEval8182 (x : Key → ℝ) : Integer.Sparse.eval row8182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8182, Integer.Sparse.eval_collectBalanced, rawRowCheck8182]

def rawRow8183 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1636, 6), (key1253, 6), (key1606, 6)]

theorem rawRowCheck8183 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form6 = rawRow8183 := by decide +kernel

def row8183 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8183 : row8183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8183 := by decide +kernel

theorem rowEval8183 (x : Key → ℝ) : Integer.Sparse.eval row8183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8183, Integer.Sparse.eval_collectBalanced, rawRowCheck8183]

def rawRow8184 : Integer.Sparse Key := [(key1606, -24), (key1528, 6), (key1636, 6), (key1606, 6), (key1253, 6)]

theorem rawRowCheck8184 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form6 = rawRow8184 := by decide +kernel

def row8184 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8184 : row8184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8184 := by decide +kernel

theorem rowEval8184 (x : Key → ℝ) : Integer.Sparse.eval row8184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8184, Integer.Sparse.eval_collectBalanced, rawRowCheck8184]

def rawRow8185 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1253, 6), (key1528, 6), (key1636, 6)]

theorem rawRowCheck8185 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form6 = rawRow8185 := by decide +kernel

def row8185 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8185 : row8185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8185 := by decide +kernel

theorem rowEval8185 (x : Key → ℝ) : Integer.Sparse.eval row8185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8185, Integer.Sparse.eval_collectBalanced, rawRowCheck8185]

def rawRow8186 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1253, 6), (key1636, 6), (key1528, 6)]

theorem rawRowCheck8186 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form6 = rawRow8186 := by decide +kernel

def row8186 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8186 : row8186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8186 := by decide +kernel

theorem rowEval8186 (x : Key → ℝ) : Integer.Sparse.eval row8186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8186, Integer.Sparse.eval_collectBalanced, rawRowCheck8186]

def rawRow8187 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1528, 6), (key1253, 6), (key1636, 6)]

theorem rawRowCheck8187 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form6 = rawRow8187 := by decide +kernel

def row8187 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8187 : row8187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8187 := by decide +kernel

theorem rowEval8187 (x : Key → ℝ) : Integer.Sparse.eval row8187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8187, Integer.Sparse.eval_collectBalanced, rawRowCheck8187]

def rawRow8188 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1528, 6), (key1636, 6), (key1253, 6)]

theorem rawRowCheck8188 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form6 = rawRow8188 := by decide +kernel

def row8188 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8188 : row8188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8188 := by decide +kernel

theorem rowEval8188 (x : Key → ℝ) : Integer.Sparse.eval row8188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8188, Integer.Sparse.eval_collectBalanced, rawRowCheck8188]

def rawRow8189 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1636, 6), (key1253, 6), (key1528, 6)]

theorem rawRowCheck8189 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form6 = rawRow8189 := by decide +kernel

def row8189 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8189 : row8189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8189 := by decide +kernel

theorem rowEval8189 (x : Key → ℝ) : Integer.Sparse.eval row8189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck8189, Integer.Sparse.eval_collectBalanced, rawRowCheck8189]

def rawRow8190 : Integer.Sparse Key := [(key1606, -24), (key1606, 6), (key1636, 6), (key1528, 6), (key1253, 6)]

theorem rawRowCheck8190 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form6 = rawRow8190 := by decide +kernel

def row8190 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8190 : row8190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8190 := by decide +kernel

theorem rowEval8190 (x : Key → ℝ) : Integer.Sparse.eval row8190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck8190, Integer.Sparse.eval_collectBalanced, rawRowCheck8190]

def rawRow8191 : Integer.Sparse Key := [(key1606, -24), (key1636, 6), (key1253, 6), (key1528, 6), (key1606, 6)]

theorem rawRowCheck8191 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form6 = rawRow8191 := by decide +kernel

def row8191 : Integer.Sparse Key := [(key1253, 6), (key1528, 6), (key1606, -18), (key1636, 6)]

theorem rowCheck8191 : row8191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8191 := by decide +kernel

theorem rowEval8191 (x : Key → ℝ) : Integer.Sparse.eval row8191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck8191, Integer.Sparse.eval_collectBalanced, rawRowCheck8191]

end MUB6.Certificate.GramRows

end OAI
