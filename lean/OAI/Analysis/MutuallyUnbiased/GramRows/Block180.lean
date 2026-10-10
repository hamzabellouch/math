import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19968 : Integer.Sparse Key := [(key1257, 6), (key1252, 6), (key1266, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1766, 6), (key1830, 6), (key1807, 6)]

theorem rawRowCheck19968 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form6 = rawRow19968 := by decide +kernel

def row19968 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19968 : row19968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19968 := by decide +kernel

theorem rowEval19968 (x : Key → ℝ) : Integer.Sparse.eval row19968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19968, Integer.Sparse.eval_collectBalanced, rawRowCheck19968]

def rawRow19969 : Integer.Sparse Key := [(key1252, 6), (key1266, 6), (key1257, 6), (key1257, 6), (key1605, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1527, 6), (key1672, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1638, 6), (key1807, 6), (key1807, 6), (key1766, 6), (key1830, 6)]

theorem rawRowCheck19969 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form6 = rawRow19969 := by decide +kernel

def row19969 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19969 : row19969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19969 := by decide +kernel

theorem rowEval19969 (x : Key → ℝ) : Integer.Sparse.eval row19969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19969, Integer.Sparse.eval_collectBalanced, rawRowCheck19969]

def rawRow19970 : Integer.Sparse Key := [(key1266, 6), (key1252, 6), (key1257, 6), (key1257, 6), (key1649, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1672, 6), (key1527, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1532, 6), (key1807, 6), (key1807, 6), (key1830, 6), (key1766, 6)]

theorem rawRowCheck19970 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form6 = rawRow19970 := by decide +kernel

def row19970 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19970 : row19970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19970 := by decide +kernel

theorem rowEval19970 (x : Key → ℝ) : Integer.Sparse.eval row19970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19970, Integer.Sparse.eval_collectBalanced, rawRowCheck19970]

def rawRow19971 : Integer.Sparse Key := [(key1257, 6), (key1266, 6), (key1252, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1830, 6), (key1766, 6), (key1807, 6)]

theorem rawRowCheck19971 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form6 = rawRow19971 := by decide +kernel

def row19971 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19971 : row19971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19971 := by decide +kernel

theorem rowEval19971 (x : Key → ℝ) : Integer.Sparse.eval row19971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19971, Integer.Sparse.eval_collectBalanced, rawRowCheck19971]

def rawRow19972 : Integer.Sparse Key := [(key1266, 6), (key1257, 6), (key1252, 6), (key1257, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1672, 6), (key1638, 6), (key1649, 6), (key1532, 6), (key1605, 6), (key1527, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1807, 6), (key1830, 6), (key1807, 6), (key1766, 6)]

theorem rawRowCheck19972 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form6 = rawRow19972 := by decide +kernel

def row19972 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19972 : row19972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19972 := by decide +kernel

theorem rowEval19972 (x : Key → ℝ) : Integer.Sparse.eval row19972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19972, Integer.Sparse.eval_collectBalanced, rawRowCheck19972]

def rawRow19973 : Integer.Sparse Key := [(key1257, 6), (key1257, 6), (key1266, 6), (key1252, 6), (key1638, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1532, 6), (key1610, 6), (key1610, 6), (key1649, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1605, 6), (key1830, 6), (key1766, 6), (key1807, 6), (key1807, 6)]

theorem rawRowCheck19973 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19973 := by decide +kernel

def row19973 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19973 : row19973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19973 := by decide +kernel

theorem rowEval19973 (x : Key → ℝ) : Integer.Sparse.eval row19973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19973, Integer.Sparse.eval_collectBalanced, rawRowCheck19973]

def rawRow19974 : Integer.Sparse Key := [(key1257, 6), (key1266, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1672, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1527, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1766, 6), (key1807, 6)]

theorem rawRowCheck19974 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19974 := by decide +kernel

def row19974 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19974 : row19974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19974 := by decide +kernel

theorem rowEval19974 (x : Key → ℝ) : Integer.Sparse.eval row19974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19974, Integer.Sparse.eval_collectBalanced, rawRowCheck19974]

def rawRow19975 : Integer.Sparse Key := [(key1266, 6), (key1257, 6), (key1257, 6), (key1252, 6), (key1672, 6), (key1638, 6), (key1638, 6), (key1649, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1532, 6), (key1605, 6), (key1605, 6), (key1527, 6), (key1830, 6), (key1807, 6), (key1807, 6), (key1766, 6)]

theorem rawRowCheck19975 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19975 := by decide +kernel

def row19975 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19975 : row19975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19975 := by decide +kernel

theorem rowEval19975 (x : Key → ℝ) : Integer.Sparse.eval row19975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19975, Integer.Sparse.eval_collectBalanced, rawRowCheck19975]

def rawRow19976 : Integer.Sparse Key := [(key1527, 6), (key1532, 6), (key1532, 6), (key1766, 6), (key1252, 6), (key1257, 6), (key1257, 6), (key1605, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1638, 6), (key1807, 6), (key1807, 6), (key1830, 6), (key1266, 6), (key1649, 6), (key1649, 6), (key1672, 6)]

theorem rawRowCheck19976 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19976 := by decide +kernel

def row19976 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19976 : row19976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19976 := by decide +kernel

theorem rowEval19976 (x : Key → ℝ) : Integer.Sparse.eval row19976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19976, Integer.Sparse.eval_collectBalanced, rawRowCheck19976]

def rawRow19977 : Integer.Sparse Key := [(key1532, 6), (key1527, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1252, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1638, 6), (key1605, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1830, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1672, 6), (key1649, 6)]

theorem rawRowCheck19977 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19977 := by decide +kernel

def row19977 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19977 : row19977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19977 := by decide +kernel

theorem rowEval19977 (x : Key → ℝ) : Integer.Sparse.eval row19977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19977, Integer.Sparse.eval_collectBalanced, rawRowCheck19977]

def rawRow19978 : Integer.Sparse Key := [(key1532, 6), (key1532, 6), (key1527, 6), (key1766, 6), (key1257, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1638, 6), (key1610, 6), (key1610, 6), (key1605, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1807, 6), (key1266, 6), (key1672, 6), (key1649, 6), (key1649, 6)]

theorem rawRowCheck19978 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19978 := by decide +kernel

def row19978 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19978 : row19978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19978 := by decide +kernel

theorem rowEval19978 (x : Key → ℝ) : Integer.Sparse.eval row19978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19978, Integer.Sparse.eval_collectBalanced, rawRowCheck19978]

def rawRow19979 : Integer.Sparse Key := [(key1527, 6), (key1532, 6), (key1766, 6), (key1532, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1252, 6), (key1257, 6), (key1605, 6), (key1638, 6), (key1807, 6), (key1830, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1649, 6), (key1266, 6), (key1649, 6), (key1672, 6)]

theorem rawRowCheck19979 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19979 := by decide +kernel

def row19979 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19979 : row19979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19979 := by decide +kernel

theorem rowEval19979 (x : Key → ℝ) : Integer.Sparse.eval row19979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19979, Integer.Sparse.eval_collectBalanced, rawRowCheck19979]

def rawRow19980 : Integer.Sparse Key := [(key1532, 6), (key1527, 6), (key1766, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1266, 6), (key1672, 6), (key1649, 6)]

theorem rawRowCheck19980 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19980 := by decide +kernel

def row19980 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19980 : row19980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19980 := by decide +kernel

theorem rowEval19980 (x : Key → ℝ) : Integer.Sparse.eval row19980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19980, Integer.Sparse.eval_collectBalanced, rawRowCheck19980]

def rawRow19981 : Integer.Sparse Key := [(key1527, 6), (key1766, 6), (key1532, 6), (key1532, 6), (key1605, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1252, 6), (key1830, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1638, 6), (key1649, 6), (key1649, 6), (key1266, 6), (key1672, 6)]

theorem rawRowCheck19981 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19981 := by decide +kernel

def row19981 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19981 : row19981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19981 := by decide +kernel

theorem rowEval19981 (x : Key → ℝ) : Integer.Sparse.eval row19981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19981, Integer.Sparse.eval_collectBalanced, rawRowCheck19981]

def rawRow19982 : Integer.Sparse Key := [(key1766, 6), (key1527, 6), (key1532, 6), (key1532, 6), (key1807, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1830, 6), (key1252, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1257, 6), (key1649, 6), (key1649, 6), (key1672, 6), (key1266, 6)]

theorem rawRowCheck19982 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19982 := by decide +kernel

def row19982 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19982 : row19982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19982 := by decide +kernel

theorem rowEval19982 (x : Key → ℝ) : Integer.Sparse.eval row19982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19982, Integer.Sparse.eval_collectBalanced, rawRowCheck19982]

def rawRow19983 : Integer.Sparse Key := [(key1532, 6), (key1766, 6), (key1527, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1672, 6), (key1266, 6), (key1649, 6)]

theorem rawRowCheck19983 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19983 := by decide +kernel

def row19983 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19983 : row19983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19983 := by decide +kernel

theorem rowEval19983 (x : Key → ℝ) : Integer.Sparse.eval row19983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19983, Integer.Sparse.eval_collectBalanced, rawRowCheck19983]

def rawRow19984 : Integer.Sparse Key := [(key1766, 6), (key1532, 6), (key1527, 6), (key1532, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1830, 6), (key1638, 6), (key1807, 6), (key1257, 6), (key1605, 6), (key1252, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1649, 6), (key1672, 6), (key1649, 6), (key1266, 6)]

theorem rawRowCheck19984 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19984 := by decide +kernel

def row19984 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19984 : row19984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19984 := by decide +kernel

theorem rowEval19984 (x : Key → ℝ) : Integer.Sparse.eval row19984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19984, Integer.Sparse.eval_collectBalanced, rawRowCheck19984]

def rawRow19985 : Integer.Sparse Key := [(key1532, 6), (key1532, 6), (key1766, 6), (key1527, 6), (key1638, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1257, 6), (key1610, 6), (key1610, 6), (key1807, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1605, 6), (key1672, 6), (key1266, 6), (key1649, 6), (key1649, 6)]

theorem rawRowCheck19985 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19985 := by decide +kernel

def row19985 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19985 : row19985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19985 := by decide +kernel

theorem rowEval19985 (x : Key → ℝ) : Integer.Sparse.eval row19985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19985, Integer.Sparse.eval_collectBalanced, rawRowCheck19985]

def rawRow19986 : Integer.Sparse Key := [(key1532, 6), (key1766, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1830, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1252, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1266, 6), (key1649, 6)]

theorem rawRowCheck19986 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19986 := by decide +kernel

def row19986 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19986 : row19986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19986 := by decide +kernel

theorem rowEval19986 (x : Key → ℝ) : Integer.Sparse.eval row19986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19986, Integer.Sparse.eval_collectBalanced, rawRowCheck19986]

def rawRow19987 : Integer.Sparse Key := [(key1766, 6), (key1532, 6), (key1532, 6), (key1527, 6), (key1830, 6), (key1638, 6), (key1638, 6), (key1807, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1257, 6), (key1605, 6), (key1605, 6), (key1252, 6), (key1672, 6), (key1649, 6), (key1649, 6), (key1266, 6)]

theorem rawRowCheck19987 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19987 := by decide +kernel

def row19987 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19987 : row19987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19987 := by decide +kernel

theorem rowEval19987 (x : Key → ℝ) : Integer.Sparse.eval row19987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19987, Integer.Sparse.eval_collectBalanced, rawRowCheck19987]

def rawRow19988 : Integer.Sparse Key := [(key1605, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1252, 6), (key1257, 6), (key1266, 6), (key1527, 6), (key1532, 6), (key1605, 6), (key1638, 6), (key1649, 6), (key1672, 6), (key1766, 6), (key1807, 6), (key1830, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1638, 6)]

theorem rawRowCheck19988 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form6 = rawRow19988 := by decide +kernel

def row19988 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19988 : row19988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19988 := by decide +kernel

theorem rowEval19988 (x : Key → ℝ) : Integer.Sparse.eval row19988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19988, Integer.Sparse.eval_collectBalanced, rawRowCheck19988]

def rawRow19989 : Integer.Sparse Key := [(key1610, 6), (key1605, 6), (key1649, 6), (key1807, 6), (key1257, 6), (key1252, 6), (key1266, 6), (key1532, 6), (key1527, 6), (key1638, 6), (key1605, 6), (key1672, 6), (key1649, 6), (key1766, 6), (key1830, 6), (key1807, 6), (key1257, 6), (key1532, 6), (key1638, 6), (key1610, 6)]

theorem rawRowCheck19989 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form6 = rawRow19989 := by decide +kernel

def row19989 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19989 : row19989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19989 := by decide +kernel

theorem rowEval19989 (x : Key → ℝ) : Integer.Sparse.eval row19989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19989, Integer.Sparse.eval_collectBalanced, rawRowCheck19989]

def rawRow19990 : Integer.Sparse Key := [(key1605, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1252, 6), (key1266, 6), (key1257, 6), (key1605, 6), (key1649, 6), (key1527, 6), (key1672, 6), (key1532, 6), (key1638, 6), (key1807, 6), (key1766, 6), (key1830, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1638, 6)]

theorem rawRowCheck19990 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form6 = rawRow19990 := by decide +kernel

def row19990 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19990 : row19990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19990 := by decide +kernel

theorem rowEval19990 (x : Key → ℝ) : Integer.Sparse.eval row19990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19990, Integer.Sparse.eval_collectBalanced, rawRowCheck19990]

def rawRow19991 : Integer.Sparse Key := [(key1649, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1266, 6), (key1252, 6), (key1257, 6), (key1649, 6), (key1605, 6), (key1672, 6), (key1527, 6), (key1638, 6), (key1532, 6), (key1807, 6), (key1830, 6), (key1766, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1532, 6)]

theorem rawRowCheck19991 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form6 = rawRow19991 := by decide +kernel

def row19991 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19991 : row19991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19991 := by decide +kernel

theorem rowEval19991 (x : Key → ℝ) : Integer.Sparse.eval row19991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19991, Integer.Sparse.eval_collectBalanced, rawRowCheck19991]

def rawRow19992 : Integer.Sparse Key := [(key1610, 6), (key1649, 6), (key1605, 6), (key1807, 6), (key1257, 6), (key1266, 6), (key1252, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1830, 6), (key1766, 6), (key1807, 6), (key1257, 6), (key1638, 6), (key1532, 6), (key1610, 6)]

theorem rawRowCheck19992 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form6 = rawRow19992 := by decide +kernel

def row19992 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19992 : row19992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19992 := by decide +kernel

theorem rowEval19992 (x : Key → ℝ) : Integer.Sparse.eval row19992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19992, Integer.Sparse.eval_collectBalanced, rawRowCheck19992]

def rawRow19993 : Integer.Sparse Key := [(key1649, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1266, 6), (key1257, 6), (key1252, 6), (key1672, 6), (key1638, 6), (key1649, 6), (key1532, 6), (key1605, 6), (key1527, 6), (key1830, 6), (key1807, 6), (key1766, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1532, 6)]

theorem rawRowCheck19993 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form6 = rawRow19993 := by decide +kernel

def row19993 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19993 : row19993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19993 := by decide +kernel

theorem rowEval19993 (x : Key → ℝ) : Integer.Sparse.eval row19993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19993, Integer.Sparse.eval_collectBalanced, rawRowCheck19993]

def rawRow19994 : Integer.Sparse Key := [(key1605, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1527, 6), (key1532, 6), (key1766, 6), (key1252, 6), (key1257, 6), (key1605, 6), (key1638, 6), (key1807, 6), (key1830, 6), (key1266, 6), (key1649, 6), (key1672, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1638, 6)]

theorem rawRowCheck19994 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19994 := by decide +kernel

def row19994 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19994 : row19994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19994 := by decide +kernel

theorem rowEval19994 (x : Key → ℝ) : Integer.Sparse.eval row19994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19994, Integer.Sparse.eval_collectBalanced, rawRowCheck19994]

def rawRow19995 : Integer.Sparse Key := [(key1610, 6), (key1605, 6), (key1807, 6), (key1649, 6), (key1532, 6), (key1527, 6), (key1766, 6), (key1257, 6), (key1252, 6), (key1638, 6), (key1605, 6), (key1830, 6), (key1807, 6), (key1266, 6), (key1672, 6), (key1649, 6), (key1532, 6), (key1257, 6), (key1638, 6), (key1610, 6)]

theorem rawRowCheck19995 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19995 := by decide +kernel

def row19995 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19995 : row19995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19995 := by decide +kernel

theorem rowEval19995 (x : Key → ℝ) : Integer.Sparse.eval row19995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19995, Integer.Sparse.eval_collectBalanced, rawRowCheck19995]

def rawRow19996 : Integer.Sparse Key := [(key1605, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1527, 6), (key1766, 6), (key1532, 6), (key1605, 6), (key1807, 6), (key1252, 6), (key1830, 6), (key1257, 6), (key1638, 6), (key1649, 6), (key1266, 6), (key1672, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1638, 6)]

theorem rawRowCheck19996 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19996 := by decide +kernel

def row19996 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19996 : row19996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19996 := by decide +kernel

theorem rowEval19996 (x : Key → ℝ) : Integer.Sparse.eval row19996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19996, Integer.Sparse.eval_collectBalanced, rawRowCheck19996]

def rawRow19997 : Integer.Sparse Key := [(key1807, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1766, 6), (key1527, 6), (key1532, 6), (key1807, 6), (key1605, 6), (key1830, 6), (key1252, 6), (key1638, 6), (key1257, 6), (key1649, 6), (key1672, 6), (key1266, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1257, 6)]

theorem rawRowCheck19997 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19997 := by decide +kernel

def row19997 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19997 : row19997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19997 := by decide +kernel

theorem rowEval19997 (x : Key → ℝ) : Integer.Sparse.eval row19997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19997, Integer.Sparse.eval_collectBalanced, rawRowCheck19997]

def rawRow19998 : Integer.Sparse Key := [(key1610, 6), (key1807, 6), (key1605, 6), (key1649, 6), (key1532, 6), (key1766, 6), (key1527, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1672, 6), (key1266, 6), (key1649, 6), (key1532, 6), (key1638, 6), (key1257, 6), (key1610, 6)]

theorem rawRowCheck19998 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19998 := by decide +kernel

def row19998 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19998 : row19998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19998 := by decide +kernel

theorem rowEval19998 (x : Key → ℝ) : Integer.Sparse.eval row19998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19998, Integer.Sparse.eval_collectBalanced, rawRowCheck19998]

def rawRow19999 : Integer.Sparse Key := [(key1807, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1766, 6), (key1532, 6), (key1527, 6), (key1830, 6), (key1638, 6), (key1807, 6), (key1257, 6), (key1605, 6), (key1252, 6), (key1672, 6), (key1649, 6), (key1266, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1257, 6)]

theorem rawRowCheck19999 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19999 := by decide +kernel

def row19999 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck19999 : row19999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19999 := by decide +kernel

theorem rowEval19999 (x : Key → ℝ) : Integer.Sparse.eval row19999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19999, Integer.Sparse.eval_collectBalanced, rawRowCheck19999]

def rawRow20000 : Integer.Sparse Key := [(key1605, 6), (key1649, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1649, 6), (key1807, 6), (key1252, 6), (key1266, 6), (key1527, 6), (key1672, 6), (key1766, 6), (key1830, 6), (key1257, 6), (key1532, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1532, 6), (key1638, 6)]

theorem rawRowCheck20000 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form6 = rawRow20000 := by decide +kernel

def row20000 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20000 : row20000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20000 := by decide +kernel

theorem rowEval20000 (x : Key → ℝ) : Integer.Sparse.eval row20000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20000, Integer.Sparse.eval_collectBalanced, rawRowCheck20000]

def rawRow20001 : Integer.Sparse Key := [(key1649, 6), (key1605, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1807, 6), (key1266, 6), (key1252, 6), (key1672, 6), (key1527, 6), (key1830, 6), (key1766, 6), (key1257, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1638, 6), (key1532, 6)]

theorem rawRowCheck20001 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form6 = rawRow20001 := by decide +kernel

def row20001 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20001 : row20001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20001 := by decide +kernel

theorem rowEval20001 (x : Key → ℝ) : Integer.Sparse.eval row20001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20001, Integer.Sparse.eval_collectBalanced, rawRowCheck20001]

def rawRow20002 : Integer.Sparse Key := [(key1605, 6), (key1807, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1807, 6), (key1649, 6), (key1527, 6), (key1766, 6), (key1252, 6), (key1830, 6), (key1266, 6), (key1672, 6), (key1532, 6), (key1257, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1257, 6), (key1638, 6)]

theorem rawRowCheck20002 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form6 = rawRow20002 := by decide +kernel

def row20002 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20002 : row20002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20002 := by decide +kernel

theorem rowEval20002 (x : Key → ℝ) : Integer.Sparse.eval row20002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20002, Integer.Sparse.eval_collectBalanced, rawRowCheck20002]

def rawRow20003 : Integer.Sparse Key := [(key1807, 6), (key1605, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1649, 6), (key1766, 6), (key1527, 6), (key1830, 6), (key1252, 6), (key1672, 6), (key1266, 6), (key1532, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1638, 6), (key1257, 6)]

theorem rawRowCheck20003 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form6 = rawRow20003 := by decide +kernel

def row20003 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20003 : row20003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20003 := by decide +kernel

theorem rowEval20003 (x : Key → ℝ) : Integer.Sparse.eval row20003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20003, Integer.Sparse.eval_collectBalanced, rawRowCheck20003]

def rawRow20004 : Integer.Sparse Key := [(key1649, 6), (key1807, 6), (key1605, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1605, 6), (key1672, 6), (key1830, 6), (key1266, 6), (key1766, 6), (key1252, 6), (key1527, 6), (key1638, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1638, 6), (key1257, 6), (key1532, 6)]

theorem rawRowCheck20004 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form6 = rawRow20004 := by decide +kernel

def row20004 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20004 : row20004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20004 := by decide +kernel

theorem rowEval20004 (x : Key → ℝ) : Integer.Sparse.eval row20004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20004, Integer.Sparse.eval_collectBalanced, rawRowCheck20004]

def rawRow20005 : Integer.Sparse Key := [(key1807, 6), (key1649, 6), (key1605, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1605, 6), (key1830, 6), (key1672, 6), (key1766, 6), (key1266, 6), (key1527, 6), (key1252, 6), (key1638, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1638, 6), (key1532, 6), (key1257, 6)]

theorem rawRowCheck20005 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form6 = rawRow20005 := by decide +kernel

def row20005 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20005 : row20005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20005 := by decide +kernel

theorem rowEval20005 (x : Key → ℝ) : Integer.Sparse.eval row20005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20005, Integer.Sparse.eval_collectBalanced, rawRowCheck20005]

def rawRow20006 : Integer.Sparse Key := [(key1610, 6), (key1649, 6), (key1807, 6), (key1605, 6), (key1638, 6), (key1672, 6), (key1830, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1252, 6), (key1527, 6), (key1605, 6), (key1638, 6), (key1257, 6), (key1532, 6), (key1610, 6)]

theorem rawRowCheck20006 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form6 = rawRow20006 := by decide +kernel

def row20006 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20006 : row20006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20006 := by decide +kernel

theorem rowEval20006 (x : Key → ℝ) : Integer.Sparse.eval row20006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20006, Integer.Sparse.eval_collectBalanced, rawRowCheck20006]

def rawRow20007 : Integer.Sparse Key := [(key1649, 6), (key1610, 6), (key1807, 6), (key1605, 6), (key1672, 6), (key1638, 6), (key1830, 6), (key1266, 6), (key1257, 6), (key1649, 6), (key1532, 6), (key1807, 6), (key1766, 6), (key1252, 6), (key1605, 6), (key1527, 6), (key1638, 6), (key1257, 6), (key1610, 6), (key1532, 6)]

theorem rawRowCheck20007 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form6 = rawRow20007 := by decide +kernel

def row20007 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20007 : row20007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20007 := by decide +kernel

theorem rowEval20007 (x : Key → ℝ) : Integer.Sparse.eval row20007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20007, Integer.Sparse.eval_collectBalanced, rawRowCheck20007]

def rawRow20008 : Integer.Sparse Key := [(key1610, 6), (key1807, 6), (key1649, 6), (key1605, 6), (key1638, 6), (key1830, 6), (key1672, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1527, 6), (key1252, 6), (key1605, 6), (key1638, 6), (key1532, 6), (key1257, 6), (key1610, 6)]

theorem rawRowCheck20008 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form6 = rawRow20008 := by decide +kernel

def row20008 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20008 : row20008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20008 := by decide +kernel

theorem rowEval20008 (x : Key → ℝ) : Integer.Sparse.eval row20008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20008, Integer.Sparse.eval_collectBalanced, rawRowCheck20008]

def rawRow20009 : Integer.Sparse Key := [(key1807, 6), (key1610, 6), (key1649, 6), (key1605, 6), (key1830, 6), (key1638, 6), (key1672, 6), (key1766, 6), (key1532, 6), (key1807, 6), (key1257, 6), (key1649, 6), (key1266, 6), (key1527, 6), (key1605, 6), (key1252, 6), (key1638, 6), (key1532, 6), (key1610, 6), (key1257, 6)]

theorem rawRowCheck20009 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form6 = rawRow20009 := by decide +kernel

def row20009 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20009 : row20009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20009 := by decide +kernel

theorem rowEval20009 (x : Key → ℝ) : Integer.Sparse.eval row20009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20009, Integer.Sparse.eval_collectBalanced, rawRowCheck20009]

def rawRow20010 : Integer.Sparse Key := [(key1649, 6), (key1807, 6), (key1610, 6), (key1605, 6), (key1672, 6), (key1830, 6), (key1638, 6), (key1649, 6), (key1807, 6), (key1266, 6), (key1766, 6), (key1257, 6), (key1532, 6), (key1605, 6), (key1252, 6), (key1527, 6), (key1638, 6), (key1610, 6), (key1257, 6), (key1532, 6)]

theorem rawRowCheck20010 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form6 = rawRow20010 := by decide +kernel

def row20010 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20010 : row20010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20010 := by decide +kernel

theorem rowEval20010 (x : Key → ℝ) : Integer.Sparse.eval row20010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20010, Integer.Sparse.eval_collectBalanced, rawRowCheck20010]

def rawRow20011 : Integer.Sparse Key := [(key1807, 6), (key1649, 6), (key1610, 6), (key1605, 6), (key1830, 6), (key1672, 6), (key1638, 6), (key1807, 6), (key1649, 6), (key1766, 6), (key1266, 6), (key1532, 6), (key1257, 6), (key1605, 6), (key1527, 6), (key1252, 6), (key1638, 6), (key1610, 6), (key1532, 6), (key1257, 6)]

theorem rawRowCheck20011 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form6 = rawRow20011 := by decide +kernel

def row20011 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20011 : row20011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20011 := by decide +kernel

theorem rowEval20011 (x : Key → ℝ) : Integer.Sparse.eval row20011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20011, Integer.Sparse.eval_collectBalanced, rawRowCheck20011]

def rawRow20012 : Integer.Sparse Key := [(key1638, 6), (key1638, 6), (key1672, 6), (key1830, 6), (key1257, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1532, 6), (key1610, 6), (key1610, 6), (key1649, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1807, 6), (key1252, 6), (key1527, 6), (key1605, 6), (key1605, 6)]

theorem rawRowCheck20012 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow20012 := by decide +kernel

def row20012 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20012 : row20012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20012 := by decide +kernel

theorem rowEval20012 (x : Key → ℝ) : Integer.Sparse.eval row20012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20012, Integer.Sparse.eval_collectBalanced, rawRowCheck20012]

def rawRow20013 : Integer.Sparse Key := [(key1638, 6), (key1672, 6), (key1638, 6), (key1830, 6), (key1257, 6), (key1266, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1766, 6), (key1807, 6), (key1252, 6), (key1605, 6), (key1527, 6), (key1605, 6)]

theorem rawRowCheck20013 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow20013 := by decide +kernel

def row20013 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20013 : row20013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20013 := by decide +kernel

theorem rowEval20013 (x : Key → ℝ) : Integer.Sparse.eval row20013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20013, Integer.Sparse.eval_collectBalanced, rawRowCheck20013]

def rawRow20014 : Integer.Sparse Key := [(key1672, 6), (key1638, 6), (key1638, 6), (key1830, 6), (key1266, 6), (key1257, 6), (key1257, 6), (key1649, 6), (key1610, 6), (key1649, 6), (key1532, 6), (key1610, 6), (key1532, 6), (key1807, 6), (key1807, 6), (key1766, 6), (key1252, 6), (key1605, 6), (key1605, 6), (key1527, 6)]

theorem rawRowCheck20014 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow20014 := by decide +kernel

def row20014 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20014 : row20014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20014 := by decide +kernel

theorem rowEval20014 (x : Key → ℝ) : Integer.Sparse.eval row20014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20014, Integer.Sparse.eval_collectBalanced, rawRowCheck20014]

def rawRow20015 : Integer.Sparse Key := [(key1638, 6), (key1638, 6), (key1830, 6), (key1672, 6), (key1532, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1257, 6), (key1610, 6), (key1610, 6), (key1807, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1649, 6), (key1527, 6), (key1252, 6), (key1605, 6), (key1605, 6)]

theorem rawRowCheck20015 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form6 = rawRow20015 := by decide +kernel

def row20015 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20015 : row20015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20015 := by decide +kernel

theorem rowEval20015 (x : Key → ℝ) : Integer.Sparse.eval row20015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20015, Integer.Sparse.eval_collectBalanced, rawRowCheck20015]

def rawRow20016 : Integer.Sparse Key := [(key1638, 6), (key1830, 6), (key1638, 6), (key1672, 6), (key1532, 6), (key1766, 6), (key1532, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1649, 6), (key1266, 6), (key1649, 6), (key1527, 6), (key1605, 6), (key1252, 6), (key1605, 6)]

theorem rawRowCheck20016 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form6 = rawRow20016 := by decide +kernel

def row20016 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20016 : row20016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20016 := by decide +kernel

theorem rowEval20016 (x : Key → ℝ) : Integer.Sparse.eval row20016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20016, Integer.Sparse.eval_collectBalanced, rawRowCheck20016]

def rawRow20017 : Integer.Sparse Key := [(key1830, 6), (key1638, 6), (key1638, 6), (key1672, 6), (key1766, 6), (key1532, 6), (key1532, 6), (key1807, 6), (key1610, 6), (key1807, 6), (key1257, 6), (key1610, 6), (key1257, 6), (key1649, 6), (key1649, 6), (key1266, 6), (key1527, 6), (key1605, 6), (key1605, 6), (key1252, 6)]

theorem rawRowCheck20017 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form6 = rawRow20017 := by decide +kernel

def row20017 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20017 : row20017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20017 := by decide +kernel

theorem rowEval20017 (x : Key → ℝ) : Integer.Sparse.eval row20017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20017, Integer.Sparse.eval_collectBalanced, rawRowCheck20017]

def rawRow20018 : Integer.Sparse Key := [(key1638, 6), (key1672, 6), (key1830, 6), (key1638, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1257, 6), (key1266, 6), (key1532, 6), (key1649, 6), (key1766, 6), (key1807, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1605, 6), (key1252, 6), (key1527, 6), (key1605, 6)]

theorem rawRowCheck20018 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form6 = rawRow20018 := by decide +kernel

def row20018 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20018 : row20018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20018 := by decide +kernel

theorem rowEval20018 (x : Key → ℝ) : Integer.Sparse.eval row20018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20018, Integer.Sparse.eval_collectBalanced, rawRowCheck20018]

def rawRow20019 : Integer.Sparse Key := [(key1672, 6), (key1638, 6), (key1830, 6), (key1638, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1266, 6), (key1257, 6), (key1649, 6), (key1532, 6), (key1807, 6), (key1766, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1605, 6), (key1252, 6), (key1605, 6), (key1527, 6)]

theorem rawRowCheck20019 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form6 = rawRow20019 := by decide +kernel

def row20019 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20019 : row20019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20019 := by decide +kernel

theorem rowEval20019 (x : Key → ℝ) : Integer.Sparse.eval row20019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20019, Integer.Sparse.eval_collectBalanced, rawRowCheck20019]

def rawRow20020 : Integer.Sparse Key := [(key1638, 6), (key1830, 6), (key1672, 6), (key1638, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1532, 6), (key1766, 6), (key1257, 6), (key1807, 6), (key1266, 6), (key1649, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1605, 6), (key1527, 6), (key1252, 6), (key1605, 6)]

theorem rawRowCheck20020 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form6 = rawRow20020 := by decide +kernel

def row20020 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20020 : row20020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20020 := by decide +kernel

theorem rowEval20020 (x : Key → ℝ) : Integer.Sparse.eval row20020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20020, Integer.Sparse.eval_collectBalanced, rawRowCheck20020]

def rawRow20021 : Integer.Sparse Key := [(key1830, 6), (key1638, 6), (key1672, 6), (key1638, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1766, 6), (key1532, 6), (key1807, 6), (key1257, 6), (key1649, 6), (key1266, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1605, 6), (key1527, 6), (key1605, 6), (key1252, 6)]

theorem rawRowCheck20021 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form6 = rawRow20021 := by decide +kernel

def row20021 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20021 : row20021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20021 := by decide +kernel

theorem rowEval20021 (x : Key → ℝ) : Integer.Sparse.eval row20021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20021, Integer.Sparse.eval_collectBalanced, rawRowCheck20021]

def rawRow20022 : Integer.Sparse Key := [(key1672, 6), (key1830, 6), (key1638, 6), (key1638, 6), (key1649, 6), (key1807, 6), (key1610, 6), (key1649, 6), (key1807, 6), (key1266, 6), (key1766, 6), (key1257, 6), (key1532, 6), (key1610, 6), (key1257, 6), (key1532, 6), (key1605, 6), (key1605, 6), (key1252, 6), (key1527, 6)]

theorem rawRowCheck20022 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form6 = rawRow20022 := by decide +kernel

def row20022 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20022 : row20022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20022 := by decide +kernel

theorem rowEval20022 (x : Key → ℝ) : Integer.Sparse.eval row20022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20022, Integer.Sparse.eval_collectBalanced, rawRowCheck20022]

def rawRow20023 : Integer.Sparse Key := [(key1830, 6), (key1672, 6), (key1638, 6), (key1638, 6), (key1807, 6), (key1649, 6), (key1610, 6), (key1807, 6), (key1649, 6), (key1766, 6), (key1266, 6), (key1532, 6), (key1257, 6), (key1610, 6), (key1532, 6), (key1257, 6), (key1605, 6), (key1605, 6), (key1527, 6), (key1252, 6)]

theorem rawRowCheck20023 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form6 = rawRow20023 := by decide +kernel

def row20023 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

theorem rowCheck20023 : row20023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20023 := by decide +kernel

theorem rowEval20023 (x : Key → ℝ) : Integer.Sparse.eval row20023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20023, Integer.Sparse.eval_collectBalanced, rawRowCheck20023]

def rawRow20024 : Integer.Sparse Key := [(key1293, 6), (key1313, 6), (key1313, 6), (key1323, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1543, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1619, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1621, 6), (key1630, 6)]

theorem rawRowCheck20024 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form7 = rawRow20024 := by decide +kernel

def row20024 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20024 : row20024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20024 := by decide +kernel

theorem rowEval20024 (x : Key → ℝ) : Integer.Sparse.eval row20024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20024, Integer.Sparse.eval_collectBalanced, rawRowCheck20024]

def rawRow20025 : Integer.Sparse Key := [(key1293, 6), (key1313, 6), (key1323, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1543, 6), (key1553, 6), (key1543, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1619, 6), (key1630, 6), (key1621, 6)]

theorem rawRowCheck20025 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form7 = rawRow20025 := by decide +kernel

def row20025 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20025 : row20025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20025 := by decide +kernel

theorem rowEval20025 (x : Key → ℝ) : Integer.Sparse.eval row20025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20025, Integer.Sparse.eval_collectBalanced, rawRowCheck20025]

def rawRow20026 : Integer.Sparse Key := [(key1293, 6), (key1323, 6), (key1313, 6), (key1313, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1553, 6), (key1543, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1630, 6), (key1630, 6), (key1621, 6), (key1621, 6), (key1619, 6), (key1619, 6)]

theorem rawRowCheck20026 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form7 = rawRow20026 := by decide +kernel

def row20026 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20026 : row20026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20026 := by decide +kernel

theorem rowEval20026 (x : Key → ℝ) : Integer.Sparse.eval row20026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20026, Integer.Sparse.eval_collectBalanced, rawRowCheck20026]

def rawRow20027 : Integer.Sparse Key := [(key1313, 6), (key1293, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1570, 6), (key1619, 6), (key1621, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1590, 6), (key1621, 6), (key1630, 6)]

theorem rawRowCheck20027 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form7 = rawRow20027 := by decide +kernel

def row20027 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20027 : row20027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20027 := by decide +kernel

theorem rowEval20027 (x : Key → ℝ) : Integer.Sparse.eval row20027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20027, Integer.Sparse.eval_collectBalanced, rawRowCheck20027]

def rawRow20028 : Integer.Sparse Key := [(key1313, 6), (key1293, 6), (key1323, 6), (key1313, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1553, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1630, 6), (key1621, 6)]

theorem rawRowCheck20028 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form7 = rawRow20028 := by decide +kernel

def row20028 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20028 : row20028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20028 := by decide +kernel

theorem rowEval20028 (x : Key → ℝ) : Integer.Sparse.eval row20028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20028, Integer.Sparse.eval_collectBalanced, rawRowCheck20028]

def rawRow20029 : Integer.Sparse Key := [(key1313, 6), (key1313, 6), (key1293, 6), (key1323, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1619, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1570, 6), (key1621, 6), (key1543, 6), (key1630, 6), (key1553, 6), (key1590, 6)]

theorem rawRowCheck20029 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form7 = rawRow20029 := by decide +kernel

def row20029 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20029 : row20029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20029 := by decide +kernel

theorem rowEval20029 (x : Key → ℝ) : Integer.Sparse.eval row20029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20029, Integer.Sparse.eval_collectBalanced, rawRowCheck20029]

def rawRow20030 : Integer.Sparse Key := [(key1313, 6), (key1313, 6), (key1323, 6), (key1293, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1619, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1621, 6), (key1570, 6), (key1630, 6), (key1543, 6), (key1590, 6), (key1553, 6)]

theorem rawRowCheck20030 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form7 = rawRow20030 := by decide +kernel

def row20030 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20030 : row20030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20030 := by decide +kernel

theorem rowEval20030 (x : Key → ℝ) : Integer.Sparse.eval row20030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20030, Integer.Sparse.eval_collectBalanced, rawRowCheck20030]

def rawRow20031 : Integer.Sparse Key := [(key1313, 6), (key1323, 6), (key1293, 6), (key1313, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1590, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1543, 6), (key1570, 6)]

theorem rawRowCheck20031 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form7 = rawRow20031 := by decide +kernel

def row20031 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20031 : row20031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20031 := by decide +kernel

theorem rowEval20031 (x : Key → ℝ) : Integer.Sparse.eval row20031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20031, Integer.Sparse.eval_collectBalanced, rawRowCheck20031]

def rawRow20032 : Integer.Sparse Key := [(key1313, 6), (key1323, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1621, 6), (key1619, 6), (key1570, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1553, 6), (key1570, 6), (key1543, 6)]

theorem rawRowCheck20032 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form7 = rawRow20032 := by decide +kernel

def row20032 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20032 : row20032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20032 := by decide +kernel

theorem rowEval20032 (x : Key → ℝ) : Integer.Sparse.eval row20032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20032, Integer.Sparse.eval_collectBalanced, rawRowCheck20032]

def rawRow20033 : Integer.Sparse Key := [(key1323, 6), (key1293, 6), (key1313, 6), (key1313, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1590, 6), (key1630, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1543, 6), (key1543, 6), (key1570, 6), (key1570, 6), (key1619, 6), (key1619, 6)]

theorem rawRowCheck20033 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow20033 := by decide +kernel

def row20033 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20033 : row20033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20033 := by decide +kernel

theorem rowEval20033 (x : Key → ℝ) : Integer.Sparse.eval row20033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20033, Integer.Sparse.eval_collectBalanced, rawRowCheck20033]

def rawRow20034 : Integer.Sparse Key := [(key1323, 6), (key1313, 6), (key1293, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1630, 6), (key1590, 6), (key1630, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1619, 6), (key1543, 6), (key1570, 6)]

theorem rawRowCheck20034 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow20034 := by decide +kernel

def row20034 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20034 : row20034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20034 := by decide +kernel

theorem rowEval20034 (x : Key → ℝ) : Integer.Sparse.eval row20034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20034, Integer.Sparse.eval_collectBalanced, rawRowCheck20034]

def rawRow20035 : Integer.Sparse Key := [(key1323, 6), (key1313, 6), (key1313, 6), (key1293, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1630, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1619, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1570, 6), (key1543, 6)]

theorem rawRowCheck20035 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow20035 := by decide +kernel

def row20035 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20035 : row20035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20035 := by decide +kernel

theorem rowEval20035 (x : Key → ℝ) : Integer.Sparse.eval row20035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20035, Integer.Sparse.eval_collectBalanced, rawRowCheck20035]

def rawRow20036 : Integer.Sparse Key := [(key1388, 6), (key1543, 6), (key1543, 6), (key1553, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1313, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1421, 6), (key1441, 6), (key1619, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1621, 6), (key1630, 6)]

theorem rawRowCheck20036 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form7 = rawRow20036 := by decide +kernel

def row20036 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20036 : row20036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20036 := by decide +kernel

theorem rowEval20036 (x : Key → ℝ) : Integer.Sparse.eval row20036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20036, Integer.Sparse.eval_collectBalanced, rawRowCheck20036]

def rawRow20037 : Integer.Sparse Key := [(key1388, 6), (key1543, 6), (key1553, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1313, 6), (key1323, 6), (key1313, 6), (key1421, 6), (key1441, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1630, 6), (key1619, 6), (key1630, 6), (key1621, 6)]

theorem rawRowCheck20037 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form7 = rawRow20037 := by decide +kernel

def row20037 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20037 : row20037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20037 := by decide +kernel

theorem rowEval20037 (x : Key → ℝ) : Integer.Sparse.eval row20037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20037, Integer.Sparse.eval_collectBalanced, rawRowCheck20037]

def rawRow20038 : Integer.Sparse Key := [(key1388, 6), (key1553, 6), (key1543, 6), (key1543, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1323, 6), (key1313, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1421, 6), (key1630, 6), (key1630, 6), (key1621, 6), (key1621, 6), (key1619, 6), (key1619, 6)]

theorem rawRowCheck20038 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form7 = rawRow20038 := by decide +kernel

def row20038 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20038 : row20038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20038 := by decide +kernel

theorem rowEval20038 (x : Key → ℝ) : Integer.Sparse.eval row20038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20038, Integer.Sparse.eval_collectBalanced, rawRowCheck20038]

def rawRow20039 : Integer.Sparse Key := [(key1543, 6), (key1388, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1421, 6), (key1619, 6), (key1621, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1441, 6), (key1621, 6), (key1630, 6)]

theorem rawRowCheck20039 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form7 = rawRow20039 := by decide +kernel

def row20039 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20039 : row20039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20039 := by decide +kernel

theorem rowEval20039 (x : Key → ℝ) : Integer.Sparse.eval row20039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20039, Integer.Sparse.eval_collectBalanced, rawRowCheck20039]

def rawRow20040 : Integer.Sparse Key := [(key1543, 6), (key1388, 6), (key1553, 6), (key1543, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1323, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1630, 6), (key1621, 6)]

theorem rawRowCheck20040 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form7 = rawRow20040 := by decide +kernel

def row20040 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20040 : row20040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20040 := by decide +kernel

theorem rowEval20040 (x : Key → ℝ) : Integer.Sparse.eval row20040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20040, Integer.Sparse.eval_collectBalanced, rawRowCheck20040]

def rawRow20041 : Integer.Sparse Key := [(key1543, 6), (key1543, 6), (key1388, 6), (key1553, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1619, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1421, 6), (key1621, 6), (key1313, 6), (key1630, 6), (key1323, 6), (key1441, 6)]

theorem rawRowCheck20041 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form7 = rawRow20041 := by decide +kernel

def row20041 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20041 : row20041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20041 := by decide +kernel

theorem rowEval20041 (x : Key → ℝ) : Integer.Sparse.eval row20041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20041, Integer.Sparse.eval_collectBalanced, rawRowCheck20041]

def rawRow20042 : Integer.Sparse Key := [(key1543, 6), (key1543, 6), (key1553, 6), (key1388, 6), (key1570, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1619, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1621, 6), (key1421, 6), (key1630, 6), (key1313, 6), (key1441, 6), (key1323, 6)]

theorem rawRowCheck20042 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form7 = rawRow20042 := by decide +kernel

def row20042 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20042 : row20042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20042 := by decide +kernel

theorem rowEval20042 (x : Key → ℝ) : Integer.Sparse.eval row20042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20042, Integer.Sparse.eval_collectBalanced, rawRowCheck20042]

def rawRow20043 : Integer.Sparse Key := [(key1543, 6), (key1553, 6), (key1388, 6), (key1543, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1441, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1313, 6), (key1421, 6)]

theorem rawRowCheck20043 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form7 = rawRow20043 := by decide +kernel

def row20043 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20043 : row20043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20043 := by decide +kernel

theorem rowEval20043 (x : Key → ℝ) : Integer.Sparse.eval row20043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20043, Integer.Sparse.eval_collectBalanced, rawRowCheck20043]

def rawRow20044 : Integer.Sparse Key := [(key1543, 6), (key1553, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1621, 6), (key1619, 6), (key1421, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1323, 6), (key1421, 6), (key1313, 6)]

theorem rawRowCheck20044 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form7 = rawRow20044 := by decide +kernel

def row20044 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20044 : row20044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20044 := by decide +kernel

theorem rowEval20044 (x : Key → ℝ) : Integer.Sparse.eval row20044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20044, Integer.Sparse.eval_collectBalanced, rawRowCheck20044]

def rawRow20045 : Integer.Sparse Key := [(key1553, 6), (key1388, 6), (key1543, 6), (key1543, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1441, 6), (key1630, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1313, 6), (key1313, 6), (key1421, 6), (key1421, 6), (key1619, 6), (key1619, 6)]

theorem rawRowCheck20045 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form7 = rawRow20045 := by decide +kernel

def row20045 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20045 : row20045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20045 := by decide +kernel

theorem rowEval20045 (x : Key → ℝ) : Integer.Sparse.eval row20045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20045, Integer.Sparse.eval_collectBalanced, rawRowCheck20045]

def rawRow20046 : Integer.Sparse Key := [(key1553, 6), (key1543, 6), (key1388, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1630, 6), (key1441, 6), (key1630, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1619, 6), (key1313, 6), (key1421, 6)]

theorem rawRowCheck20046 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form7 = rawRow20046 := by decide +kernel

def row20046 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20046 : row20046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20046 := by decide +kernel

theorem rowEval20046 (x : Key → ℝ) : Integer.Sparse.eval row20046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20046, Integer.Sparse.eval_collectBalanced, rawRowCheck20046]

def rawRow20047 : Integer.Sparse Key := [(key1553, 6), (key1543, 6), (key1543, 6), (key1388, 6), (key1590, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1630, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1619, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1421, 6), (key1313, 6)]

theorem rawRowCheck20047 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form7 = rawRow20047 := by decide +kernel

def row20047 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20047 : row20047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20047 := by decide +kernel

theorem rowEval20047 (x : Key → ℝ) : Integer.Sparse.eval row20047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20047, Integer.Sparse.eval_collectBalanced, rawRowCheck20047]

def rawRow20048 : Integer.Sparse Key := [(key1421, 6), (key1570, 6), (key1619, 6), (key1621, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1293, 6), (key1313, 6), (key1323, 6), (key1388, 6), (key1421, 6), (key1441, 6), (key1543, 6), (key1553, 6), (key1570, 6), (key1590, 6), (key1621, 6), (key1630, 6)]

theorem rawRowCheck20048 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form7 = rawRow20048 := by decide +kernel

def row20048 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20048 : row20048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20048 := by decide +kernel

theorem rowEval20048 (x : Key → ℝ) : Integer.Sparse.eval row20048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20048, Integer.Sparse.eval_collectBalanced, rawRowCheck20048]

def rawRow20049 : Integer.Sparse Key := [(key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1293, 6), (key1323, 6), (key1313, 6), (key1388, 6), (key1441, 6), (key1421, 6), (key1553, 6), (key1543, 6), (key1590, 6), (key1570, 6), (key1630, 6), (key1621, 6)]

theorem rawRowCheck20049 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form7 = rawRow20049 := by decide +kernel

def row20049 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20049 : row20049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20049 := by decide +kernel

theorem rowEval20049 (x : Key → ℝ) : Integer.Sparse.eval row20049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20049, Integer.Sparse.eval_collectBalanced, rawRowCheck20049]

def rawRow20050 : Integer.Sparse Key := [(key1421, 6), (key1619, 6), (key1570, 6), (key1621, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1293, 6), (key1323, 6), (key1421, 6), (key1388, 6), (key1441, 6), (key1570, 6), (key1621, 6), (key1543, 6), (key1630, 6), (key1553, 6), (key1590, 6)]

theorem rawRowCheck20050 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form7 = rawRow20050 := by decide +kernel

def row20050 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20050 : row20050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20050 := by decide +kernel

theorem rowEval20050 (x : Key → ℝ) : Integer.Sparse.eval row20050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20050, Integer.Sparse.eval_collectBalanced, rawRowCheck20050]

def rawRow20051 : Integer.Sparse Key := [(key1421, 6), (key1619, 6), (key1621, 6), (key1570, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1323, 6), (key1293, 6), (key1421, 6), (key1441, 6), (key1388, 6), (key1621, 6), (key1570, 6), (key1630, 6), (key1543, 6), (key1590, 6), (key1553, 6)]

theorem rawRowCheck20051 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form7 = rawRow20051 := by decide +kernel

def row20051 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20051 : row20051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20051 := by decide +kernel

theorem rowEval20051 (x : Key → ℝ) : Integer.Sparse.eval row20051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20051, Integer.Sparse.eval_collectBalanced, rawRowCheck20051]

def rawRow20052 : Integer.Sparse Key := [(key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1323, 6), (key1293, 6), (key1313, 6), (key1441, 6), (key1388, 6), (key1421, 6), (key1590, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1543, 6), (key1570, 6)]

theorem rawRowCheck20052 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form7 = rawRow20052 := by decide +kernel

def row20052 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20052 : row20052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20052 := by decide +kernel

theorem rowEval20052 (x : Key → ℝ) : Integer.Sparse.eval row20052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20052, Integer.Sparse.eval_collectBalanced, rawRowCheck20052]

def rawRow20053 : Integer.Sparse Key := [(key1421, 6), (key1621, 6), (key1619, 6), (key1570, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1323, 6), (key1313, 6), (key1293, 6), (key1441, 6), (key1421, 6), (key1388, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1553, 6), (key1570, 6), (key1543, 6)]

theorem rawRowCheck20053 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form7 = rawRow20053 := by decide +kernel

def row20053 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20053 : row20053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20053 := by decide +kernel

theorem rowEval20053 (x : Key → ℝ) : Integer.Sparse.eval row20053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20053, Integer.Sparse.eval_collectBalanced, rawRowCheck20053]

def rawRow20054 : Integer.Sparse Key := [(key1570, 6), (key1421, 6), (key1619, 6), (key1621, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1630, 6), (key1388, 6), (key1543, 6), (key1553, 6), (key1293, 6), (key1570, 6), (key1590, 6), (key1313, 6), (key1323, 6), (key1421, 6), (key1441, 6), (key1621, 6), (key1630, 6)]

theorem rawRowCheck20054 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form7 = rawRow20054 := by decide +kernel

def row20054 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20054 : row20054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20054 := by decide +kernel

theorem rowEval20054 (x : Key → ℝ) : Integer.Sparse.eval row20054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20054, Integer.Sparse.eval_collectBalanced, rawRowCheck20054]

def rawRow20055 : Integer.Sparse Key := [(key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1619, 6), (key1388, 6), (key1553, 6), (key1543, 6), (key1293, 6), (key1590, 6), (key1570, 6), (key1323, 6), (key1313, 6), (key1441, 6), (key1421, 6), (key1630, 6), (key1621, 6)]

theorem rawRowCheck20055 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form7 = rawRow20055 := by decide +kernel

def row20055 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20055 : row20055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20055 := by decide +kernel

theorem rowEval20055 (x : Key → ℝ) : Integer.Sparse.eval row20055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20055, Integer.Sparse.eval_collectBalanced, rawRowCheck20055]

def rawRow20056 : Integer.Sparse Key := [(key1570, 6), (key1619, 6), (key1421, 6), (key1621, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1388, 6), (key1553, 6), (key1570, 6), (key1293, 6), (key1590, 6), (key1421, 6), (key1621, 6), (key1313, 6), (key1630, 6), (key1323, 6), (key1441, 6)]

theorem rawRowCheck20056 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form7 = rawRow20056 := by decide +kernel

def row20056 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20056 : row20056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20056 := by decide +kernel

theorem rowEval20056 (x : Key → ℝ) : Integer.Sparse.eval row20056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20056, Integer.Sparse.eval_collectBalanced, rawRowCheck20056]

def rawRow20057 : Integer.Sparse Key := [(key1570, 6), (key1619, 6), (key1621, 6), (key1421, 6), (key1543, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1553, 6), (key1388, 6), (key1570, 6), (key1590, 6), (key1293, 6), (key1621, 6), (key1421, 6), (key1630, 6), (key1313, 6), (key1441, 6), (key1323, 6)]

theorem rawRowCheck20057 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form7 = rawRow20057 := by decide +kernel

def row20057 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20057 : row20057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20057 := by decide +kernel

theorem rowEval20057 (x : Key → ℝ) : Integer.Sparse.eval row20057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20057, Integer.Sparse.eval_collectBalanced, rawRowCheck20057]

def rawRow20058 : Integer.Sparse Key := [(key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1553, 6), (key1388, 6), (key1543, 6), (key1590, 6), (key1293, 6), (key1570, 6), (key1441, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1313, 6), (key1421, 6)]

theorem rawRowCheck20058 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form7 = rawRow20058 := by decide +kernel

def row20058 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20058 : row20058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20058 := by decide +kernel

theorem rowEval20058 (x : Key → ℝ) : Integer.Sparse.eval row20058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20058, Integer.Sparse.eval_collectBalanced, rawRowCheck20058]

def rawRow20059 : Integer.Sparse Key := [(key1570, 6), (key1621, 6), (key1619, 6), (key1421, 6), (key1543, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1553, 6), (key1543, 6), (key1388, 6), (key1590, 6), (key1570, 6), (key1293, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1323, 6), (key1421, 6), (key1313, 6)]

theorem rawRowCheck20059 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form7 = rawRow20059 := by decide +kernel

def row20059 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20059 : row20059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20059 := by decide +kernel

theorem rowEval20059 (x : Key → ℝ) : Integer.Sparse.eval row20059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20059, Integer.Sparse.eval_collectBalanced, rawRowCheck20059]

def rawRow20060 : Integer.Sparse Key := [(key1619, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1421, 6), (key1570, 6), (key1621, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1293, 6), (key1323, 6), (key1388, 6), (key1441, 6), (key1553, 6), (key1590, 6)]

theorem rawRowCheck20060 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form7 = rawRow20060 := by decide +kernel

def row20060 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20060 : row20060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20060 := by decide +kernel

theorem rowEval20060 (x : Key → ℝ) : Integer.Sparse.eval row20060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20060, Integer.Sparse.eval_collectBalanced, rawRowCheck20060]

def rawRow20061 : Integer.Sparse Key := [(key1619, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1421, 6), (key1621, 6), (key1570, 6), (key1313, 6), (key1630, 6), (key1543, 6), (key1323, 6), (key1293, 6), (key1441, 6), (key1388, 6), (key1590, 6), (key1553, 6)]

theorem rawRowCheck20061 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form7 = rawRow20061 := by decide +kernel

def row20061 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20061 : row20061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20061 := by decide +kernel

theorem rowEval20061 (x : Key → ℝ) : Integer.Sparse.eval row20061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20061, Integer.Sparse.eval_collectBalanced, rawRowCheck20061]

def rawRow20062 : Integer.Sparse Key := [(key1619, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1570, 6), (key1421, 6), (key1621, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1388, 6), (key1553, 6), (key1293, 6), (key1590, 6), (key1323, 6), (key1441, 6)]

theorem rawRowCheck20062 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form7 = rawRow20062 := by decide +kernel

def row20062 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20062 : row20062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20062 := by decide +kernel

theorem rowEval20062 (x : Key → ℝ) : Integer.Sparse.eval row20062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20062, Integer.Sparse.eval_collectBalanced, rawRowCheck20062]

def rawRow20063 : Integer.Sparse Key := [(key1619, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1570, 6), (key1621, 6), (key1421, 6), (key1543, 6), (key1630, 6), (key1313, 6), (key1553, 6), (key1388, 6), (key1590, 6), (key1293, 6), (key1441, 6), (key1323, 6)]

theorem rawRowCheck20063 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form7 = rawRow20063 := by decide +kernel

def row20063 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20063 : row20063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20063 := by decide +kernel

theorem rowEval20063 (x : Key → ℝ) : Integer.Sparse.eval row20063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20063, Integer.Sparse.eval_collectBalanced, rawRowCheck20063]

def rawRow20064 : Integer.Sparse Key := [(key1619, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1441, 6), (key1590, 6), (key1323, 6), (key1553, 6), (key1293, 6), (key1388, 6)]

theorem rawRowCheck20064 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form7 = rawRow20064 := by decide +kernel

def row20064 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20064 : row20064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20064 := by decide +kernel

theorem rowEval20064 (x : Key → ℝ) : Integer.Sparse.eval row20064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20064, Integer.Sparse.eval_collectBalanced, rawRowCheck20064]

def rawRow20065 : Integer.Sparse Key := [(key1619, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1590, 6), (key1441, 6), (key1553, 6), (key1323, 6), (key1388, 6), (key1293, 6)]

theorem rawRowCheck20065 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form7 = rawRow20065 := by decide +kernel

def row20065 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20065 : row20065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20065 := by decide +kernel

theorem rowEval20065 (x : Key → ℝ) : Integer.Sparse.eval row20065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20065, Integer.Sparse.eval_collectBalanced, rawRowCheck20065]

def rawRow20066 : Integer.Sparse Key := [(key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1630, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1441, 6), (key1590, 6), (key1630, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1293, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1543, 6), (key1570, 6)]

theorem rawRowCheck20066 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form7 = rawRow20066 := by decide +kernel

def row20066 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20066 : row20066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20066 := by decide +kernel

theorem rowEval20066 (x : Key → ℝ) : Integer.Sparse.eval row20066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20066, Integer.Sparse.eval_collectBalanced, rawRowCheck20066]

def rawRow20067 : Integer.Sparse Key := [(key1621, 6), (key1421, 6), (key1619, 6), (key1570, 6), (key1630, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1441, 6), (key1630, 6), (key1590, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1388, 6), (key1570, 6), (key1543, 6)]

theorem rawRowCheck20067 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form7 = rawRow20067 := by decide +kernel

def row20067 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20067 : row20067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20067 := by decide +kernel

theorem rowEval20067 (x : Key → ℝ) : Integer.Sparse.eval row20067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20067, Integer.Sparse.eval_collectBalanced, rawRowCheck20067]

def rawRow20068 : Integer.Sparse Key := [(key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1630, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1590, 6), (key1441, 6), (key1630, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1388, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1313, 6), (key1421, 6)]

theorem rawRowCheck20068 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form7 = rawRow20068 := by decide +kernel

def row20068 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20068 : row20068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20068 := by decide +kernel

theorem rowEval20068 (x : Key → ℝ) : Integer.Sparse.eval row20068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20068, Integer.Sparse.eval_collectBalanced, rawRowCheck20068]

def rawRow20069 : Integer.Sparse Key := [(key1621, 6), (key1570, 6), (key1619, 6), (key1421, 6), (key1630, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1590, 6), (key1630, 6), (key1441, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1293, 6), (key1421, 6), (key1313, 6)]

theorem rawRowCheck20069 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form7 = rawRow20069 := by decide +kernel

def row20069 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20069 : row20069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20069 := by decide +kernel

theorem rowEval20069 (x : Key → ℝ) : Integer.Sparse.eval row20069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20069, Integer.Sparse.eval_collectBalanced, rawRowCheck20069]

def rawRow20070 : Integer.Sparse Key := [(key1621, 6), (key1619, 6), (key1421, 6), (key1570, 6), (key1630, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1630, 6), (key1441, 6), (key1590, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1421, 6), (key1570, 6), (key1313, 6), (key1543, 6), (key1293, 6), (key1388, 6)]

theorem rawRowCheck20070 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form7 = rawRow20070 := by decide +kernel

def row20070 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20070 : row20070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20070 := by decide +kernel

theorem rowEval20070 (x : Key → ℝ) : Integer.Sparse.eval row20070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20070, Integer.Sparse.eval_collectBalanced, rawRowCheck20070]

def rawRow20071 : Integer.Sparse Key := [(key1621, 6), (key1619, 6), (key1570, 6), (key1421, 6), (key1630, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1630, 6), (key1590, 6), (key1441, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1570, 6), (key1421, 6), (key1543, 6), (key1313, 6), (key1388, 6), (key1293, 6)]

theorem rawRowCheck20071 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form7 = rawRow20071 := by decide +kernel

def row20071 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20071 : row20071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20071 := by decide +kernel

theorem rowEval20071 (x : Key → ℝ) : Integer.Sparse.eval row20071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20071, Integer.Sparse.eval_collectBalanced, rawRowCheck20071]

def rawRow20072 : Integer.Sparse Key := [(key1441, 6), (key1590, 6), (key1630, 6), (key1630, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1293, 6), (key1313, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1421, 6), (key1543, 6), (key1543, 6), (key1570, 6), (key1570, 6), (key1619, 6), (key1619, 6)]

theorem rawRowCheck20072 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow20072 := by decide +kernel

def row20072 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20072 : row20072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20072 := by decide +kernel

theorem rowEval20072 (x : Key → ℝ) : Integer.Sparse.eval row20072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20072, Integer.Sparse.eval_collectBalanced, rawRowCheck20072]

def rawRow20073 : Integer.Sparse Key := [(key1441, 6), (key1630, 6), (key1590, 6), (key1630, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1313, 6), (key1293, 6), (key1313, 6), (key1421, 6), (key1388, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1619, 6), (key1543, 6), (key1570, 6)]

theorem rawRowCheck20073 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow20073 := by decide +kernel

def row20073 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20073 : row20073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20073 := by decide +kernel

theorem rowEval20073 (x : Key → ℝ) : Integer.Sparse.eval row20073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20073, Integer.Sparse.eval_collectBalanced, rawRowCheck20073]

def rawRow20074 : Integer.Sparse Key := [(key1441, 6), (key1630, 6), (key1630, 6), (key1590, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1313, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1421, 6), (key1388, 6), (key1619, 6), (key1570, 6), (key1619, 6), (key1543, 6), (key1570, 6), (key1543, 6)]

theorem rawRowCheck20074 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow20074 := by decide +kernel

def row20074 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20074 : row20074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20074 := by decide +kernel

theorem rowEval20074 (x : Key → ℝ) : Integer.Sparse.eval row20074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20074, Integer.Sparse.eval_collectBalanced, rawRowCheck20074]

def rawRow20075 : Integer.Sparse Key := [(key1590, 6), (key1441, 6), (key1630, 6), (key1630, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1621, 6), (key1388, 6), (key1543, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1570, 6), (key1313, 6), (key1313, 6), (key1421, 6), (key1421, 6), (key1619, 6), (key1619, 6)]

theorem rawRowCheck20075 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form7 = rawRow20075 := by decide +kernel

def row20075 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20075 : row20075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20075 := by decide +kernel

theorem rowEval20075 (x : Key → ℝ) : Integer.Sparse.eval row20075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20075, Integer.Sparse.eval_collectBalanced, rawRowCheck20075]

def rawRow20076 : Integer.Sparse Key := [(key1590, 6), (key1630, 6), (key1441, 6), (key1630, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1543, 6), (key1388, 6), (key1543, 6), (key1570, 6), (key1293, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1619, 6), (key1313, 6), (key1421, 6)]

theorem rawRowCheck20076 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form7 = rawRow20076 := by decide +kernel

def row20076 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20076 : row20076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20076 := by decide +kernel

theorem rowEval20076 (x : Key → ℝ) : Integer.Sparse.eval row20076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20076, Integer.Sparse.eval_collectBalanced, rawRowCheck20076]

def rawRow20077 : Integer.Sparse Key := [(key1590, 6), (key1630, 6), (key1630, 6), (key1441, 6), (key1553, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1543, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1570, 6), (key1293, 6), (key1619, 6), (key1421, 6), (key1619, 6), (key1313, 6), (key1421, 6), (key1313, 6)]

theorem rawRowCheck20077 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form7 = rawRow20077 := by decide +kernel

def row20077 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20077 : row20077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20077 := by decide +kernel

theorem rowEval20077 (x : Key → ℝ) : Integer.Sparse.eval row20077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20077, Integer.Sparse.eval_collectBalanced, rawRowCheck20077]

def rawRow20078 : Integer.Sparse Key := [(key1630, 6), (key1441, 6), (key1590, 6), (key1630, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1621, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1619, 6), (key1293, 6), (key1313, 6), (key1388, 6), (key1421, 6), (key1543, 6), (key1570, 6)]

theorem rawRowCheck20078 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form7 = rawRow20078 := by decide +kernel

def row20078 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20078 : row20078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20078 := by decide +kernel

theorem rowEval20078 (x : Key → ℝ) : Integer.Sparse.eval row20078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20078, Integer.Sparse.eval_collectBalanced, rawRowCheck20078]

def rawRow20079 : Integer.Sparse Key := [(key1630, 6), (key1441, 6), (key1630, 6), (key1590, 6), (key1621, 6), (key1323, 6), (key1621, 6), (key1553, 6), (key1421, 6), (key1619, 6), (key1570, 6), (key1313, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1293, 6), (key1421, 6), (key1388, 6), (key1570, 6), (key1543, 6)]

theorem rawRowCheck20079 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form7 = rawRow20079 := by decide +kernel

def row20079 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20079 : row20079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20079 := by decide +kernel

theorem rowEval20079 (x : Key → ℝ) : Integer.Sparse.eval row20079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20079, Integer.Sparse.eval_collectBalanced, rawRowCheck20079]

def rawRow20080 : Integer.Sparse Key := [(key1630, 6), (key1590, 6), (key1441, 6), (key1630, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1621, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1619, 6), (key1388, 6), (key1543, 6), (key1293, 6), (key1570, 6), (key1313, 6), (key1421, 6)]

theorem rawRowCheck20080 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form7 = rawRow20080 := by decide +kernel

def row20080 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20080 : row20080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20080 := by decide +kernel

theorem rowEval20080 (x : Key → ℝ) : Integer.Sparse.eval row20080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20080, Integer.Sparse.eval_collectBalanced, rawRowCheck20080]

def rawRow20081 : Integer.Sparse Key := [(key1630, 6), (key1590, 6), (key1630, 6), (key1441, 6), (key1621, 6), (key1553, 6), (key1621, 6), (key1323, 6), (key1570, 6), (key1619, 6), (key1421, 6), (key1543, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1388, 6), (key1570, 6), (key1293, 6), (key1421, 6), (key1313, 6)]

theorem rawRowCheck20081 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form7 = rawRow20081 := by decide +kernel

def row20081 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20081 : row20081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20081 := by decide +kernel

theorem rowEval20081 (x : Key → ℝ) : Integer.Sparse.eval row20081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20081, Integer.Sparse.eval_collectBalanced, rawRowCheck20081]

def rawRow20082 : Integer.Sparse Key := [(key1630, 6), (key1630, 6), (key1441, 6), (key1590, 6), (key1621, 6), (key1621, 6), (key1323, 6), (key1553, 6), (key1619, 6), (key1421, 6), (key1570, 6), (key1619, 6), (key1313, 6), (key1543, 6), (key1421, 6), (key1570, 6), (key1313, 6), (key1543, 6), (key1293, 6), (key1388, 6)]

theorem rawRowCheck20082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form7 = rawRow20082 := by decide +kernel

def row20082 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20082 : row20082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20082 := by decide +kernel

theorem rowEval20082 (x : Key → ℝ) : Integer.Sparse.eval row20082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20082, Integer.Sparse.eval_collectBalanced, rawRowCheck20082]

def rawRow20083 : Integer.Sparse Key := [(key1630, 6), (key1630, 6), (key1590, 6), (key1441, 6), (key1621, 6), (key1621, 6), (key1553, 6), (key1323, 6), (key1619, 6), (key1570, 6), (key1421, 6), (key1619, 6), (key1543, 6), (key1313, 6), (key1570, 6), (key1421, 6), (key1543, 6), (key1313, 6), (key1388, 6), (key1293, 6)]

theorem rawRowCheck20083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form7 = rawRow20083 := by decide +kernel

def row20083 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

theorem rowCheck20083 : row20083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20083 := by decide +kernel

theorem rowEval20083 (x : Key → ℝ) : Integer.Sparse.eval row20083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20083, Integer.Sparse.eval_collectBalanced, rawRowCheck20083]

def rawRow20084 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key627, 24), (key629, 24), (key640, 24)]

theorem rawRowCheck20084 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form8 = rawRow20084 := by decide +kernel

def row20084 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20084 : row20084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20084 := by decide +kernel

theorem rowEval20084 (x : Key → ℝ) : Integer.Sparse.eval row20084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20084, Integer.Sparse.eval_collectBalanced, rawRowCheck20084]

def rawRow20085 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key627, 24), (key629, 24), (key640, 24)]

theorem rawRowCheck20085 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form8 = rawRow20085 := by decide +kernel

def row20085 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20085 : row20085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20085 := by decide +kernel

theorem rowEval20085 (x : Key → ℝ) : Integer.Sparse.eval row20085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20085, Integer.Sparse.eval_collectBalanced, rawRowCheck20085]

def rawRow20086 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key626, 24), (key629, 24), (key640, 24)]

theorem rawRowCheck20086 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form8 = rawRow20086 := by decide +kernel

def row20086 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20086 : row20086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20086 := by decide +kernel

theorem rowEval20086 (x : Key → ℝ) : Integer.Sparse.eval row20086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20086, Integer.Sparse.eval_collectBalanced, rawRowCheck20086]

def rawRow20087 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key629, 24), (key627, 24), (key640, 24)]

theorem rawRowCheck20087 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form8 = rawRow20087 := by decide +kernel

def row20087 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20087 : row20087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20087 := by decide +kernel

theorem rowEval20087 (x : Key → ℝ) : Integer.Sparse.eval row20087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20087, Integer.Sparse.eval_collectBalanced, rawRowCheck20087]

def rawRow20088 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key629, 24), (key627, 24), (key640, 24)]

theorem rawRowCheck20088 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form8 = rawRow20088 := by decide +kernel

def row20088 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20088 : row20088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20088 := by decide +kernel

theorem rowEval20088 (x : Key → ℝ) : Integer.Sparse.eval row20088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20088, Integer.Sparse.eval_collectBalanced, rawRowCheck20088]

def rawRow20089 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key627, 24), (key627, 24), (key640, 24)]

theorem rawRowCheck20089 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form8 = rawRow20089 := by decide +kernel

def row20089 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20089 : row20089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20089 := by decide +kernel

theorem rowEval20089 (x : Key → ℝ) : Integer.Sparse.eval row20089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20089, Integer.Sparse.eval_collectBalanced, rawRowCheck20089]

def rawRow20090 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key627, 24), (key627, 24), (key640, 24)]

theorem rawRowCheck20090 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form8 = rawRow20090 := by decide +kernel

def row20090 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20090 : row20090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20090 := by decide +kernel

theorem rowEval20090 (x : Key → ℝ) : Integer.Sparse.eval row20090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20090, Integer.Sparse.eval_collectBalanced, rawRowCheck20090]

def rawRow20091 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key626, 24), (key627, 24), (key640, 24)]

theorem rawRowCheck20091 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form8 = rawRow20091 := by decide +kernel

def row20091 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20091 : row20091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20091 := by decide +kernel

theorem rowEval20091 (x : Key → ℝ) : Integer.Sparse.eval row20091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20091, Integer.Sparse.eval_collectBalanced, rawRowCheck20091]

def rawRow20092 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key626, 24), (key627, 24), (key640, 24)]

theorem rawRowCheck20092 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form8 = rawRow20092 := by decide +kernel

def row20092 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20092 : row20092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20092 := by decide +kernel

theorem rowEval20092 (x : Key → ℝ) : Integer.Sparse.eval row20092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20092, Integer.Sparse.eval_collectBalanced, rawRowCheck20092]

def rawRow20093 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key629, 24), (key626, 24), (key640, 24)]

theorem rawRowCheck20093 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form8 = rawRow20093 := by decide +kernel

def row20093 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20093 : row20093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20093 := by decide +kernel

theorem rowEval20093 (x : Key → ℝ) : Integer.Sparse.eval row20093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20093, Integer.Sparse.eval_collectBalanced, rawRowCheck20093]

def rawRow20094 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key627, 24), (key626, 24), (key640, 24)]

theorem rawRowCheck20094 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form8 = rawRow20094 := by decide +kernel

def row20094 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20094 : row20094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20094 := by decide +kernel

theorem rowEval20094 (x : Key → ℝ) : Integer.Sparse.eval row20094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20094, Integer.Sparse.eval_collectBalanced, rawRowCheck20094]

def rawRow20095 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key627, 24), (key626, 24), (key640, 24)]

theorem rawRowCheck20095 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form8 = rawRow20095 := by decide +kernel

def row20095 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20095 : row20095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20095 := by decide +kernel

theorem rowEval20095 (x : Key → ℝ) : Integer.Sparse.eval row20095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20095, Integer.Sparse.eval_collectBalanced, rawRowCheck20095]

end MUB6.Certificate.GramRows

end OAI
