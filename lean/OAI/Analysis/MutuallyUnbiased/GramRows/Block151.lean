import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16256 : Integer.Sparse Key := [(key1154, -2), (key1126, -2), (key1111, -2), (key1111, 6), (key1211, -2), (key1198, -2), (key1190, -2), (key1211, 2), (key1198, 2), (key1075, 2), (key1018, 2), (key1033, 2), (key998, 2), (key1190, -2), (key1033, -2), (key998, -2), (key1192, 6), (key1192, -2), (key1040, -2), (key1005, -2)]

theorem rawRowCheck16256 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form4 = rawRow16256 := by decide +kernel

def row16256 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16256 : row16256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16256 := by decide +kernel

theorem rowEval16256 (x : Key → ℝ) : Integer.Sparse.eval row16256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16256, Integer.Sparse.eval_collectBalanced, rawRowCheck16256]

def rawRow16257 : Integer.Sparse Key := [(key1190, -2), (key1192, -2), (key1211, -2), (key1198, 6), (key1033, -2), (key1040, -2), (key1075, -2), (key998, 2), (key1005, 2), (key1111, 2), (key1192, 2), (key1154, 2), (key1211, 2), (key1018, -2), (key1126, -2), (key1198, -2), (key1033, 6), (key998, -2), (key1111, -2), (key1190, -2)]

theorem rawRowCheck16257 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form4 = rawRow16257 := by decide +kernel

def row16257 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16257 : row16257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16257 := by decide +kernel

theorem rowEval16257 (x : Key → ℝ) : Integer.Sparse.eval row16257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16257, Integer.Sparse.eval_collectBalanced, rawRowCheck16257]

def rawRow16258 : Integer.Sparse Key := [(key1192, -2), (key1190, -2), (key1211, -2), (key1198, 6), (key1040, -2), (key1033, -2), (key1075, -2), (key1005, 2), (key998, 2), (key1192, 2), (key1111, 2), (key1211, 2), (key1154, 2), (key1018, -2), (key1198, -2), (key1126, -2), (key1033, 6), (key998, -2), (key1190, -2), (key1111, -2)]

theorem rawRowCheck16258 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form4 = rawRow16258 := by decide +kernel

def row16258 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16258 : row16258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16258 := by decide +kernel

theorem rowEval16258 (x : Key → ℝ) : Integer.Sparse.eval row16258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16258, Integer.Sparse.eval_collectBalanced, rawRowCheck16258]

def rawRow16259 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1192, -2), (key1198, 6), (key1033, -2), (key1075, -2), (key1040, -2), (key1111, 2), (key1154, 2), (key998, 2), (key1211, 2), (key1005, 2), (key1192, 2), (key1126, -2), (key1018, -2), (key1198, -2), (key1033, 6), (key1111, -2), (key998, -2), (key1190, -2)]

theorem rawRowCheck16259 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form4 = rawRow16259 := by decide +kernel

def row16259 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16259 : row16259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16259 := by decide +kernel

theorem rowEval16259 (x : Key → ℝ) : Integer.Sparse.eval row16259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16259, Integer.Sparse.eval_collectBalanced, rawRowCheck16259]

def rawRow16260 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1192, -2), (key1198, 6), (key1075, -2), (key1033, -2), (key1040, -2), (key1154, 2), (key1111, 2), (key1211, 2), (key998, 2), (key1192, 2), (key1005, 2), (key1126, -2), (key1198, -2), (key1018, -2), (key1033, 6), (key1111, -2), (key1190, -2), (key998, -2)]

theorem rawRowCheck16260 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form4 = rawRow16260 := by decide +kernel

def row16260 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16260 : row16260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16260 := by decide +kernel

theorem rowEval16260 (x : Key → ℝ) : Integer.Sparse.eval row16260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16260, Integer.Sparse.eval_collectBalanced, rawRowCheck16260]

def rawRow16261 : Integer.Sparse Key := [(key1192, -2), (key1211, -2), (key1190, -2), (key1198, 6), (key1040, -2), (key1075, -2), (key1033, -2), (key1192, 2), (key1211, 2), (key1005, 2), (key1154, 2), (key998, 2), (key1111, 2), (key1198, -2), (key1018, -2), (key1126, -2), (key1033, 6), (key1190, -2), (key998, -2), (key1111, -2)]

theorem rawRowCheck16261 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form4 = rawRow16261 := by decide +kernel

def row16261 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16261 : row16261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16261 := by decide +kernel

theorem rowEval16261 (x : Key → ℝ) : Integer.Sparse.eval row16261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16261, Integer.Sparse.eval_collectBalanced, rawRowCheck16261]

def rawRow16262 : Integer.Sparse Key := [(key1211, -2), (key1192, -2), (key1190, -2), (key1198, 6), (key1075, -2), (key1040, -2), (key1033, -2), (key1211, 2), (key1192, 2), (key1154, 2), (key1005, 2), (key1111, 2), (key998, 2), (key1198, -2), (key1126, -2), (key1018, -2), (key1033, 6), (key1190, -2), (key1111, -2), (key998, -2)]

theorem rawRowCheck16262 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form4 = rawRow16262 := by decide +kernel

def row16262 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -2), (key1075, -2), (key1126, -2), (key1154, 2), (key1190, -4), (key1198, 4)]

theorem rowCheck16262 : row16262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16262 := by decide +kernel

theorem rowEval16262 (x : Key → ℝ) : Integer.Sparse.eval row16262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16262, Integer.Sparse.eval_collectBalanced, rawRowCheck16262]

def rawRow16263 : Integer.Sparse Key := [(key1190, -2), (key1198, -2), (key1211, -2), (key1192, 6), (key1111, -2), (key1126, -2), (key1154, -2), (key998, 2), (key1018, 2), (key1033, 2), (key1198, 2), (key1075, 2), (key1211, 2), (key1005, -2), (key1040, -2), (key1192, -2), (key1111, 6), (key998, -2), (key1033, -2), (key1190, -2)]

theorem rawRowCheck16263 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form4 = rawRow16263 := by decide +kernel

def row16263 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16263 : row16263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16263 := by decide +kernel

theorem rowEval16263 (x : Key → ℝ) : Integer.Sparse.eval row16263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16263, Integer.Sparse.eval_collectBalanced, rawRowCheck16263]

def rawRow16264 : Integer.Sparse Key := [(key1198, -2), (key1190, -2), (key1211, -2), (key1192, 6), (key1126, -2), (key1111, -2), (key1154, -2), (key1018, 2), (key998, 2), (key1198, 2), (key1033, 2), (key1211, 2), (key1075, 2), (key1005, -2), (key1192, -2), (key1040, -2), (key1111, 6), (key998, -2), (key1190, -2), (key1033, -2)]

theorem rawRowCheck16264 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form4 = rawRow16264 := by decide +kernel

def row16264 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16264 : row16264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16264 := by decide +kernel

theorem rowEval16264 (x : Key → ℝ) : Integer.Sparse.eval row16264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16264, Integer.Sparse.eval_collectBalanced, rawRowCheck16264]

def rawRow16265 : Integer.Sparse Key := [(key1190, -2), (key1211, -2), (key1198, -2), (key1192, 6), (key1111, -2), (key1154, -2), (key1126, -2), (key1033, 2), (key1075, 2), (key998, 2), (key1211, 2), (key1018, 2), (key1198, 2), (key1040, -2), (key1005, -2), (key1192, -2), (key1111, 6), (key1033, -2), (key998, -2), (key1190, -2)]

theorem rawRowCheck16265 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form4 = rawRow16265 := by decide +kernel

def row16265 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16265 : row16265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16265 := by decide +kernel

theorem rowEval16265 (x : Key → ℝ) : Integer.Sparse.eval row16265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16265, Integer.Sparse.eval_collectBalanced, rawRowCheck16265]

def rawRow16266 : Integer.Sparse Key := [(key1211, -2), (key1190, -2), (key1198, -2), (key1192, 6), (key1154, -2), (key1111, -2), (key1126, -2), (key1075, 2), (key1033, 2), (key1211, 2), (key998, 2), (key1198, 2), (key1018, 2), (key1040, -2), (key1192, -2), (key1005, -2), (key1111, 6), (key1033, -2), (key1190, -2), (key998, -2)]

theorem rawRowCheck16266 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form4 = rawRow16266 := by decide +kernel

def row16266 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16266 : row16266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16266 := by decide +kernel

theorem rowEval16266 (x : Key → ℝ) : Integer.Sparse.eval row16266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16266, Integer.Sparse.eval_collectBalanced, rawRowCheck16266]

def rawRow16267 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1190, -2), (key1192, 6), (key1126, -2), (key1154, -2), (key1111, -2), (key1198, 2), (key1211, 2), (key1018, 2), (key1075, 2), (key998, 2), (key1033, 2), (key1192, -2), (key1005, -2), (key1040, -2), (key1111, 6), (key1190, -2), (key998, -2), (key1033, -2)]

theorem rawRowCheck16267 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form4 = rawRow16267 := by decide +kernel

def row16267 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16267 : row16267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16267 := by decide +kernel

theorem rowEval16267 (x : Key → ℝ) : Integer.Sparse.eval row16267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16267, Integer.Sparse.eval_collectBalanced, rawRowCheck16267]

def rawRow16268 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1190, -2), (key1192, 6), (key1154, -2), (key1126, -2), (key1111, -2), (key1211, 2), (key1198, 2), (key1075, 2), (key1018, 2), (key1033, 2), (key998, 2), (key1192, -2), (key1040, -2), (key1005, -2), (key1111, 6), (key1190, -2), (key1033, -2), (key998, -2)]

theorem rawRowCheck16268 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form4 = rawRow16268 := by decide +kernel

def row16268 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, -2), (key1154, -2), (key1190, -4), (key1192, 4)]

theorem rowCheck16268 : row16268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16268 := by decide +kernel

theorem rowEval16268 (x : Key → ℝ) : Integer.Sparse.eval row16268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16268, Integer.Sparse.eval_collectBalanced, rawRowCheck16268]

def rawRow16269 : Integer.Sparse Key := [(key1192, -2), (key1198, -2), (key1211, -2), (key1190, 6), (key1192, -2), (key1198, -2), (key1211, -2), (key1005, 2), (key1018, 2), (key1040, 2), (key1126, 2), (key1075, 2), (key1154, 2), (key998, -2), (key1033, -2), (key1111, -2), (key1190, 6), (key998, -2), (key1033, -2), (key1111, -2)]

theorem rawRowCheck16269 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form4 = rawRow16269 := by decide +kernel

def row16269 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

theorem rowCheck16269 : row16269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16269 := by decide +kernel

theorem rowEval16269 (x : Key → ℝ) : Integer.Sparse.eval row16269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16269, Integer.Sparse.eval_collectBalanced, rawRowCheck16269]

def rawRow16270 : Integer.Sparse Key := [(key1198, -2), (key1192, -2), (key1211, -2), (key1190, 6), (key1198, -2), (key1192, -2), (key1211, -2), (key1018, 2), (key1005, 2), (key1126, 2), (key1040, 2), (key1154, 2), (key1075, 2), (key998, -2), (key1111, -2), (key1033, -2), (key1190, 6), (key998, -2), (key1111, -2), (key1033, -2)]

theorem rawRowCheck16270 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form4 = rawRow16270 := by decide +kernel

def row16270 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

theorem rowCheck16270 : row16270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16270 := by decide +kernel

theorem rowEval16270 (x : Key → ℝ) : Integer.Sparse.eval row16270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16270, Integer.Sparse.eval_collectBalanced, rawRowCheck16270]

def rawRow16271 : Integer.Sparse Key := [(key1192, -2), (key1211, -2), (key1198, -2), (key1190, 6), (key1192, -2), (key1211, -2), (key1198, -2), (key1040, 2), (key1075, 2), (key1005, 2), (key1154, 2), (key1018, 2), (key1126, 2), (key1033, -2), (key998, -2), (key1111, -2), (key1190, 6), (key1033, -2), (key998, -2), (key1111, -2)]

theorem rawRowCheck16271 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form4 = rawRow16271 := by decide +kernel

def row16271 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

theorem rowCheck16271 : row16271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16271 := by decide +kernel

theorem rowEval16271 (x : Key → ℝ) : Integer.Sparse.eval row16271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck16271, Integer.Sparse.eval_collectBalanced, rawRowCheck16271]

def rawRow16272 : Integer.Sparse Key := [(key1211, -2), (key1192, -2), (key1198, -2), (key1190, 6), (key1211, -2), (key1192, -2), (key1198, -2), (key1075, 2), (key1040, 2), (key1154, 2), (key1005, 2), (key1126, 2), (key1018, 2), (key1033, -2), (key1111, -2), (key998, -2), (key1190, 6), (key1033, -2), (key1111, -2), (key998, -2)]

theorem rawRowCheck16272 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form4 = rawRow16272 := by decide +kernel

def row16272 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

theorem rowCheck16272 : row16272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16272 := by decide +kernel

theorem rowEval16272 (x : Key → ℝ) : Integer.Sparse.eval row16272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16272, Integer.Sparse.eval_collectBalanced, rawRowCheck16272]

def rawRow16273 : Integer.Sparse Key := [(key1198, -2), (key1211, -2), (key1192, -2), (key1190, 6), (key1198, -2), (key1211, -2), (key1192, -2), (key1126, 2), (key1154, 2), (key1018, 2), (key1075, 2), (key1005, 2), (key1040, 2), (key1111, -2), (key998, -2), (key1033, -2), (key1190, 6), (key1111, -2), (key998, -2), (key1033, -2)]

theorem rawRowCheck16273 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form4 = rawRow16273 := by decide +kernel

def row16273 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

theorem rowCheck16273 : row16273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16273 := by decide +kernel

theorem rowEval16273 (x : Key → ℝ) : Integer.Sparse.eval row16273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck16273, Integer.Sparse.eval_collectBalanced, rawRowCheck16273]

def rawRow16274 : Integer.Sparse Key := [(key1211, -2), (key1198, -2), (key1192, -2), (key1190, 6), (key1211, -2), (key1198, -2), (key1192, -2), (key1154, 2), (key1126, 2), (key1075, 2), (key1018, 2), (key1040, 2), (key1005, 2), (key1111, -2), (key1033, -2), (key998, -2), (key1190, 6), (key1111, -2), (key1033, -2), (key998, -2)]

theorem rawRowCheck16274 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form4 = rawRow16274 := by decide +kernel

def row16274 : Integer.Sparse Key := [(key998, -4), (key1005, 2), (key1018, 2), (key1033, -4), (key1040, 2), (key1075, 2), (key1111, -4), (key1126, 2), (key1154, 2), (key1190, 12), (key1192, -4), (key1198, -4), (key1211, -4)]

theorem rowCheck16274 : row16274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16274 := by decide +kernel

theorem rowEval16274 (x : Key → ℝ) : Integer.Sparse.eval row16274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form4) x := by
  rw [rowCheck16274, Integer.Sparse.eval_collectBalanced, rawRowCheck16274]

def rawRow16275 : Integer.Sparse Key := [(key1004, 4), (key1214, 4), (key1214, 4), (key1008, -2), (key1008, -2), (key1195, -2), (key1195, -2), (key1216, -2), (key1216, -2), (key1021, -2), (key1021, -2), (key1201, -2), (key1201, -2), (key1225, -2), (key1225, -2), (key1023, 4), (key1202, 4), (key1202, 4)]

theorem rawRowCheck16275 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form5 = rawRow16275 := by decide +kernel

def row16275 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

theorem rowCheck16275 : row16275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16275 := by decide +kernel

theorem rowEval16275 (x : Key → ℝ) : Integer.Sparse.eval row16275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16275, Integer.Sparse.eval_collectBalanced, rawRowCheck16275]

def rawRow16276 : Integer.Sparse Key := [(key1214, 4), (key1004, 4), (key1214, 4), (key1195, -2), (key1216, -2), (key1008, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1202, 4), (key1023, 4), (key1202, 4)]

theorem rawRowCheck16276 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form5 = rawRow16276 := by decide +kernel

def row16276 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

theorem rowCheck16276 : row16276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16276 := by decide +kernel

theorem rowEval16276 (x : Key → ℝ) : Integer.Sparse.eval row16276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16276, Integer.Sparse.eval_collectBalanced, rawRowCheck16276]

def rawRow16277 : Integer.Sparse Key := [(key1214, 4), (key1214, 4), (key1004, 4), (key1216, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1008, -2), (key1225, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1021, -2), (key1202, 4), (key1202, 4), (key1023, 4)]

theorem rawRowCheck16277 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form5 = rawRow16277 := by decide +kernel

def row16277 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

theorem rowCheck16277 : row16277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16277 := by decide +kernel

theorem rowEval16277 (x : Key → ℝ) : Integer.Sparse.eval row16277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16277, Integer.Sparse.eval_collectBalanced, rawRowCheck16277]

def rawRow16278 : Integer.Sparse Key := [(key1008, 4), (key1157, 4), (key1216, 4), (key1004, -2), (key1008, -2), (key1117, -2), (key1195, -2), (key1157, -2), (key1214, -2), (key1021, -2), (key1023, -2), (key1129, -2), (key1202, -2), (key1176, -2), (key1225, -2), (key1021, 4), (key1129, 4), (key1201, 4)]

theorem rawRowCheck16278 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form5 = rawRow16278 := by decide +kernel

def row16278 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16278 : row16278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16278 := by decide +kernel

theorem rowEval16278 (x : Key → ℝ) : Integer.Sparse.eval row16278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16278, Integer.Sparse.eval_collectBalanced, rawRowCheck16278]

def rawRow16279 : Integer.Sparse Key := [(key1008, 4), (key1216, 4), (key1157, 4), (key1008, -2), (key1004, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1157, -2), (key1023, -2), (key1021, -2), (key1202, -2), (key1129, -2), (key1225, -2), (key1176, -2), (key1021, 4), (key1201, 4), (key1129, 4)]

theorem rawRowCheck16279 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form5 = rawRow16279 := by decide +kernel

def row16279 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16279 : row16279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16279 := by decide +kernel

theorem rowEval16279 (x : Key → ℝ) : Integer.Sparse.eval row16279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16279, Integer.Sparse.eval_collectBalanced, rawRowCheck16279]

def rawRow16280 : Integer.Sparse Key := [(key1157, 4), (key1008, 4), (key1216, 4), (key1117, -2), (key1157, -2), (key1004, -2), (key1214, -2), (key1008, -2), (key1195, -2), (key1129, -2), (key1176, -2), (key1021, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1129, 4), (key1021, 4), (key1201, 4)]

theorem rawRowCheck16280 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form5 = rawRow16280 := by decide +kernel

def row16280 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16280 : row16280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16280 := by decide +kernel

theorem rowEval16280 (x : Key → ℝ) : Integer.Sparse.eval row16280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16280, Integer.Sparse.eval_collectBalanced, rawRowCheck16280]

def rawRow16281 : Integer.Sparse Key := [(key1157, 4), (key1216, 4), (key1008, 4), (key1157, -2), (key1117, -2), (key1214, -2), (key1004, -2), (key1195, -2), (key1008, -2), (key1176, -2), (key1129, -2), (key1225, -2), (key1021, -2), (key1202, -2), (key1023, -2), (key1129, 4), (key1201, 4), (key1021, 4)]

theorem rawRowCheck16281 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form5 = rawRow16281 := by decide +kernel

def row16281 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16281 : row16281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16281 := by decide +kernel

theorem rowEval16281 (x : Key → ℝ) : Integer.Sparse.eval row16281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16281, Integer.Sparse.eval_collectBalanced, rawRowCheck16281]

def rawRow16282 : Integer.Sparse Key := [(key1216, 4), (key1008, 4), (key1157, 4), (key1195, -2), (key1214, -2), (key1008, -2), (key1157, -2), (key1004, -2), (key1117, -2), (key1202, -2), (key1225, -2), (key1023, -2), (key1176, -2), (key1021, -2), (key1129, -2), (key1201, 4), (key1021, 4), (key1129, 4)]

theorem rawRowCheck16282 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form5 = rawRow16282 := by decide +kernel

def row16282 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16282 : row16282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16282 := by decide +kernel

theorem rowEval16282 (x : Key → ℝ) : Integer.Sparse.eval row16282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16282, Integer.Sparse.eval_collectBalanced, rawRowCheck16282]

def rawRow16283 : Integer.Sparse Key := [(key1216, 4), (key1157, 4), (key1008, 4), (key1214, -2), (key1195, -2), (key1157, -2), (key1008, -2), (key1117, -2), (key1004, -2), (key1225, -2), (key1202, -2), (key1176, -2), (key1023, -2), (key1129, -2), (key1021, -2), (key1201, 4), (key1129, 4), (key1021, 4)]

theorem rawRowCheck16283 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form5 = rawRow16283 := by decide +kernel

def row16283 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16283 : row16283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16283 := by decide +kernel

theorem rowEval16283 (x : Key → ℝ) : Integer.Sparse.eval row16283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16283, Integer.Sparse.eval_collectBalanced, rawRowCheck16283]

def rawRow16284 : Integer.Sparse Key := [(key1004, 4), (key1214, 4), (key1214, 4), (key1021, -2), (key1021, -2), (key1201, -2), (key1201, -2), (key1225, -2), (key1225, -2), (key1008, -2), (key1008, -2), (key1195, -2), (key1195, -2), (key1216, -2), (key1216, -2), (key1023, 4), (key1202, 4), (key1202, 4)]

theorem rawRowCheck16284 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form5 = rawRow16284 := by decide +kernel

def row16284 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

theorem rowCheck16284 : row16284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16284 := by decide +kernel

theorem rowEval16284 (x : Key → ℝ) : Integer.Sparse.eval row16284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16284, Integer.Sparse.eval_collectBalanced, rawRowCheck16284]

def rawRow16285 : Integer.Sparse Key := [(key1214, 4), (key1004, 4), (key1214, 4), (key1201, -2), (key1225, -2), (key1021, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1202, 4), (key1023, 4), (key1202, 4)]

theorem rawRowCheck16285 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form5 = rawRow16285 := by decide +kernel

def row16285 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

theorem rowCheck16285 : row16285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16285 := by decide +kernel

theorem rowEval16285 (x : Key → ℝ) : Integer.Sparse.eval row16285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16285, Integer.Sparse.eval_collectBalanced, rawRowCheck16285]

def rawRow16286 : Integer.Sparse Key := [(key1214, 4), (key1214, 4), (key1004, 4), (key1225, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1021, -2), (key1216, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1008, -2), (key1202, 4), (key1202, 4), (key1023, 4)]

theorem rawRowCheck16286 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form5 = rawRow16286 := by decide +kernel

def row16286 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1195, -4), (key1201, -4), (key1202, 8), (key1214, 8), (key1216, -4), (key1225, -4)]

theorem rowCheck16286 : row16286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16286 := by decide +kernel

theorem rowEval16286 (x : Key → ℝ) : Integer.Sparse.eval row16286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16286, Integer.Sparse.eval_collectBalanced, rawRowCheck16286]

def rawRow16287 : Integer.Sparse Key := [(key1021, 4), (key1078, 4), (key1225, 4), (key1004, -2), (key1021, -2), (key1039, -2), (key1201, -2), (key1078, -2), (key1214, -2), (key1008, -2), (key1023, -2), (key1043, -2), (key1202, -2), (key1081, -2), (key1216, -2), (key1008, 4), (key1043, 4), (key1195, 4)]

theorem rawRowCheck16287 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form5 = rawRow16287 := by decide +kernel

def row16287 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16287 : row16287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16287 := by decide +kernel

theorem rowEval16287 (x : Key → ℝ) : Integer.Sparse.eval row16287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16287, Integer.Sparse.eval_collectBalanced, rawRowCheck16287]

def rawRow16288 : Integer.Sparse Key := [(key1021, 4), (key1225, 4), (key1078, 4), (key1021, -2), (key1004, -2), (key1201, -2), (key1039, -2), (key1214, -2), (key1078, -2), (key1023, -2), (key1008, -2), (key1202, -2), (key1043, -2), (key1216, -2), (key1081, -2), (key1008, 4), (key1195, 4), (key1043, 4)]

theorem rawRowCheck16288 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form5 = rawRow16288 := by decide +kernel

def row16288 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16288 : row16288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16288 := by decide +kernel

theorem rowEval16288 (x : Key → ℝ) : Integer.Sparse.eval row16288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16288, Integer.Sparse.eval_collectBalanced, rawRowCheck16288]

def rawRow16289 : Integer.Sparse Key := [(key1078, 4), (key1021, 4), (key1225, 4), (key1039, -2), (key1078, -2), (key1004, -2), (key1214, -2), (key1021, -2), (key1201, -2), (key1043, -2), (key1081, -2), (key1008, -2), (key1216, -2), (key1023, -2), (key1202, -2), (key1043, 4), (key1008, 4), (key1195, 4)]

theorem rawRowCheck16289 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form5 = rawRow16289 := by decide +kernel

def row16289 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16289 : row16289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16289 := by decide +kernel

theorem rowEval16289 (x : Key → ℝ) : Integer.Sparse.eval row16289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16289, Integer.Sparse.eval_collectBalanced, rawRowCheck16289]

def rawRow16290 : Integer.Sparse Key := [(key1078, 4), (key1225, 4), (key1021, 4), (key1078, -2), (key1039, -2), (key1214, -2), (key1004, -2), (key1201, -2), (key1021, -2), (key1081, -2), (key1043, -2), (key1216, -2), (key1008, -2), (key1202, -2), (key1023, -2), (key1043, 4), (key1195, 4), (key1008, 4)]

theorem rawRowCheck16290 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form5 = rawRow16290 := by decide +kernel

def row16290 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16290 : row16290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16290 := by decide +kernel

theorem rowEval16290 (x : Key → ℝ) : Integer.Sparse.eval row16290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16290, Integer.Sparse.eval_collectBalanced, rawRowCheck16290]

def rawRow16291 : Integer.Sparse Key := [(key1225, 4), (key1021, 4), (key1078, 4), (key1201, -2), (key1214, -2), (key1021, -2), (key1078, -2), (key1004, -2), (key1039, -2), (key1202, -2), (key1216, -2), (key1023, -2), (key1081, -2), (key1008, -2), (key1043, -2), (key1195, 4), (key1008, 4), (key1043, 4)]

theorem rawRowCheck16291 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form5 = rawRow16291 := by decide +kernel

def row16291 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16291 : row16291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16291 := by decide +kernel

theorem rowEval16291 (x : Key → ℝ) : Integer.Sparse.eval row16291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16291, Integer.Sparse.eval_collectBalanced, rawRowCheck16291]

def rawRow16292 : Integer.Sparse Key := [(key1225, 4), (key1078, 4), (key1021, 4), (key1214, -2), (key1201, -2), (key1078, -2), (key1021, -2), (key1039, -2), (key1004, -2), (key1216, -2), (key1202, -2), (key1081, -2), (key1023, -2), (key1043, -2), (key1008, -2), (key1195, 4), (key1043, 4), (key1008, 4)]

theorem rawRowCheck16292 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form5 = rawRow16292 := by decide +kernel

def row16292 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16292 : row16292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16292 := by decide +kernel

theorem rowEval16292 (x : Key → ℝ) : Integer.Sparse.eval row16292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16292, Integer.Sparse.eval_collectBalanced, rawRowCheck16292]

def rawRow16293 : Integer.Sparse Key := [(key1008, 4), (key1157, 4), (key1216, 4), (key1021, -2), (key1023, -2), (key1129, -2), (key1202, -2), (key1176, -2), (key1225, -2), (key1004, -2), (key1008, -2), (key1117, -2), (key1195, -2), (key1157, -2), (key1214, -2), (key1021, 4), (key1129, 4), (key1201, 4)]

theorem rawRowCheck16293 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form5 = rawRow16293 := by decide +kernel

def row16293 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16293 : row16293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16293 := by decide +kernel

theorem rowEval16293 (x : Key → ℝ) : Integer.Sparse.eval row16293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16293, Integer.Sparse.eval_collectBalanced, rawRowCheck16293]

def rawRow16294 : Integer.Sparse Key := [(key1008, 4), (key1216, 4), (key1157, 4), (key1023, -2), (key1021, -2), (key1202, -2), (key1129, -2), (key1225, -2), (key1176, -2), (key1008, -2), (key1004, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1157, -2), (key1021, 4), (key1201, 4), (key1129, 4)]

theorem rawRowCheck16294 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form5 = rawRow16294 := by decide +kernel

def row16294 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16294 : row16294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16294 := by decide +kernel

theorem rowEval16294 (x : Key → ℝ) : Integer.Sparse.eval row16294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16294, Integer.Sparse.eval_collectBalanced, rawRowCheck16294]

def rawRow16295 : Integer.Sparse Key := [(key1157, 4), (key1008, 4), (key1216, 4), (key1129, -2), (key1176, -2), (key1021, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1117, -2), (key1157, -2), (key1004, -2), (key1214, -2), (key1008, -2), (key1195, -2), (key1129, 4), (key1021, 4), (key1201, 4)]

theorem rawRowCheck16295 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form5 = rawRow16295 := by decide +kernel

def row16295 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16295 : row16295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16295 := by decide +kernel

theorem rowEval16295 (x : Key → ℝ) : Integer.Sparse.eval row16295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16295, Integer.Sparse.eval_collectBalanced, rawRowCheck16295]

def rawRow16296 : Integer.Sparse Key := [(key1157, 4), (key1216, 4), (key1008, 4), (key1176, -2), (key1129, -2), (key1225, -2), (key1021, -2), (key1202, -2), (key1023, -2), (key1157, -2), (key1117, -2), (key1214, -2), (key1004, -2), (key1195, -2), (key1008, -2), (key1129, 4), (key1201, 4), (key1021, 4)]

theorem rawRowCheck16296 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form5 = rawRow16296 := by decide +kernel

def row16296 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16296 : row16296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16296 := by decide +kernel

theorem rowEval16296 (x : Key → ℝ) : Integer.Sparse.eval row16296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16296, Integer.Sparse.eval_collectBalanced, rawRowCheck16296]

def rawRow16297 : Integer.Sparse Key := [(key1216, 4), (key1008, 4), (key1157, 4), (key1202, -2), (key1225, -2), (key1023, -2), (key1176, -2), (key1021, -2), (key1129, -2), (key1195, -2), (key1214, -2), (key1008, -2), (key1157, -2), (key1004, -2), (key1117, -2), (key1201, 4), (key1021, 4), (key1129, 4)]

theorem rawRowCheck16297 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form5 = rawRow16297 := by decide +kernel

def row16297 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16297 : row16297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16297 := by decide +kernel

theorem rowEval16297 (x : Key → ℝ) : Integer.Sparse.eval row16297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16297, Integer.Sparse.eval_collectBalanced, rawRowCheck16297]

def rawRow16298 : Integer.Sparse Key := [(key1216, 4), (key1157, 4), (key1008, 4), (key1225, -2), (key1202, -2), (key1176, -2), (key1023, -2), (key1129, -2), (key1021, -2), (key1214, -2), (key1195, -2), (key1157, -2), (key1008, -2), (key1117, -2), (key1004, -2), (key1201, 4), (key1129, 4), (key1021, 4)]

theorem rawRowCheck16298 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form5 = rawRow16298 := by decide +kernel

def row16298 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1117, -2), (key1129, 2), (key1157, 2), (key1176, -2), (key1195, -2), (key1201, 4), (key1202, -2), (key1214, -2), (key1216, 4), (key1225, -2)]

theorem rowCheck16298 : row16298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16298 := by decide +kernel

theorem rowEval16298 (x : Key → ℝ) : Integer.Sparse.eval row16298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16298, Integer.Sparse.eval_collectBalanced, rawRowCheck16298]

def rawRow16299 : Integer.Sparse Key := [(key1021, 4), (key1078, 4), (key1225, 4), (key1008, -2), (key1023, -2), (key1043, -2), (key1202, -2), (key1081, -2), (key1216, -2), (key1004, -2), (key1021, -2), (key1039, -2), (key1201, -2), (key1078, -2), (key1214, -2), (key1008, 4), (key1043, 4), (key1195, 4)]

theorem rawRowCheck16299 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form5 = rawRow16299 := by decide +kernel

def row16299 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16299 : row16299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16299 := by decide +kernel

theorem rowEval16299 (x : Key → ℝ) : Integer.Sparse.eval row16299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16299, Integer.Sparse.eval_collectBalanced, rawRowCheck16299]

def rawRow16300 : Integer.Sparse Key := [(key1021, 4), (key1225, 4), (key1078, 4), (key1023, -2), (key1008, -2), (key1202, -2), (key1043, -2), (key1216, -2), (key1081, -2), (key1021, -2), (key1004, -2), (key1201, -2), (key1039, -2), (key1214, -2), (key1078, -2), (key1008, 4), (key1195, 4), (key1043, 4)]

theorem rawRowCheck16300 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form5 = rawRow16300 := by decide +kernel

def row16300 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16300 : row16300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16300 := by decide +kernel

theorem rowEval16300 (x : Key → ℝ) : Integer.Sparse.eval row16300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16300, Integer.Sparse.eval_collectBalanced, rawRowCheck16300]

def rawRow16301 : Integer.Sparse Key := [(key1078, 4), (key1021, 4), (key1225, 4), (key1043, -2), (key1081, -2), (key1008, -2), (key1216, -2), (key1023, -2), (key1202, -2), (key1039, -2), (key1078, -2), (key1004, -2), (key1214, -2), (key1021, -2), (key1201, -2), (key1043, 4), (key1008, 4), (key1195, 4)]

theorem rawRowCheck16301 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form5 = rawRow16301 := by decide +kernel

def row16301 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16301 : row16301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16301 := by decide +kernel

theorem rowEval16301 (x : Key → ℝ) : Integer.Sparse.eval row16301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16301, Integer.Sparse.eval_collectBalanced, rawRowCheck16301]

def rawRow16302 : Integer.Sparse Key := [(key1078, 4), (key1225, 4), (key1021, 4), (key1081, -2), (key1043, -2), (key1216, -2), (key1008, -2), (key1202, -2), (key1023, -2), (key1078, -2), (key1039, -2), (key1214, -2), (key1004, -2), (key1201, -2), (key1021, -2), (key1043, 4), (key1195, 4), (key1008, 4)]

theorem rawRowCheck16302 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form5 = rawRow16302 := by decide +kernel

def row16302 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16302 : row16302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16302 := by decide +kernel

theorem rowEval16302 (x : Key → ℝ) : Integer.Sparse.eval row16302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16302, Integer.Sparse.eval_collectBalanced, rawRowCheck16302]

def rawRow16303 : Integer.Sparse Key := [(key1225, 4), (key1021, 4), (key1078, 4), (key1202, -2), (key1216, -2), (key1023, -2), (key1081, -2), (key1008, -2), (key1043, -2), (key1201, -2), (key1214, -2), (key1021, -2), (key1078, -2), (key1004, -2), (key1039, -2), (key1195, 4), (key1008, 4), (key1043, 4)]

theorem rawRowCheck16303 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form5 = rawRow16303 := by decide +kernel

def row16303 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16303 : row16303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16303 := by decide +kernel

theorem rowEval16303 (x : Key → ℝ) : Integer.Sparse.eval row16303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16303, Integer.Sparse.eval_collectBalanced, rawRowCheck16303]

def rawRow16304 : Integer.Sparse Key := [(key1225, 4), (key1078, 4), (key1021, 4), (key1216, -2), (key1202, -2), (key1081, -2), (key1023, -2), (key1043, -2), (key1008, -2), (key1214, -2), (key1201, -2), (key1078, -2), (key1021, -2), (key1039, -2), (key1004, -2), (key1195, 4), (key1043, 4), (key1008, 4)]

theorem rawRowCheck16304 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form5 = rawRow16304 := by decide +kernel

def row16304 : Integer.Sparse Key := [(key1004, -2), (key1008, 2), (key1021, 2), (key1023, -2), (key1039, -2), (key1043, 2), (key1078, 2), (key1081, -2), (key1195, 4), (key1201, -2), (key1202, -2), (key1214, -2), (key1216, -2), (key1225, 4)]

theorem rowCheck16304 : row16304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16304 := by decide +kernel

theorem rowEval16304 (x : Key → ℝ) : Integer.Sparse.eval row16304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16304, Integer.Sparse.eval_collectBalanced, rawRowCheck16304]

def rawRow16305 : Integer.Sparse Key := [(key1023, 4), (key1081, 4), (key1176, 4), (key1008, -2), (key1021, -2), (key1043, -2), (key1129, -2), (key1078, -2), (key1157, -2), (key1008, -2), (key1021, -2), (key1043, -2), (key1129, -2), (key1078, -2), (key1157, -2), (key1004, 4), (key1039, 4), (key1117, 4)]

theorem rawRowCheck16305 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form5 = rawRow16305 := by decide +kernel

def row16305 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

theorem rowCheck16305 : row16305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16305 := by decide +kernel

theorem rowEval16305 (x : Key → ℝ) : Integer.Sparse.eval row16305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16305, Integer.Sparse.eval_collectBalanced, rawRowCheck16305]

def rawRow16306 : Integer.Sparse Key := [(key1023, 4), (key1176, 4), (key1081, 4), (key1021, -2), (key1008, -2), (key1129, -2), (key1043, -2), (key1157, -2), (key1078, -2), (key1021, -2), (key1008, -2), (key1129, -2), (key1043, -2), (key1157, -2), (key1078, -2), (key1004, 4), (key1117, 4), (key1039, 4)]

theorem rawRowCheck16306 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form5 = rawRow16306 := by decide +kernel

def row16306 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

theorem rowCheck16306 : row16306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16306 := by decide +kernel

theorem rowEval16306 (x : Key → ℝ) : Integer.Sparse.eval row16306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16306, Integer.Sparse.eval_collectBalanced, rawRowCheck16306]

def rawRow16307 : Integer.Sparse Key := [(key1081, 4), (key1023, 4), (key1176, 4), (key1043, -2), (key1078, -2), (key1008, -2), (key1157, -2), (key1021, -2), (key1129, -2), (key1043, -2), (key1078, -2), (key1008, -2), (key1157, -2), (key1021, -2), (key1129, -2), (key1039, 4), (key1004, 4), (key1117, 4)]

theorem rawRowCheck16307 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form5 = rawRow16307 := by decide +kernel

def row16307 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

theorem rowCheck16307 : row16307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16307 := by decide +kernel

theorem rowEval16307 (x : Key → ℝ) : Integer.Sparse.eval row16307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck16307, Integer.Sparse.eval_collectBalanced, rawRowCheck16307]

def rawRow16308 : Integer.Sparse Key := [(key1081, 4), (key1176, 4), (key1023, 4), (key1078, -2), (key1043, -2), (key1157, -2), (key1008, -2), (key1129, -2), (key1021, -2), (key1078, -2), (key1043, -2), (key1157, -2), (key1008, -2), (key1129, -2), (key1021, -2), (key1039, 4), (key1117, 4), (key1004, 4)]

theorem rawRowCheck16308 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form5 = rawRow16308 := by decide +kernel

def row16308 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

theorem rowCheck16308 : row16308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16308 := by decide +kernel

theorem rowEval16308 (x : Key → ℝ) : Integer.Sparse.eval row16308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16308, Integer.Sparse.eval_collectBalanced, rawRowCheck16308]

def rawRow16309 : Integer.Sparse Key := [(key1176, 4), (key1023, 4), (key1081, 4), (key1129, -2), (key1157, -2), (key1021, -2), (key1078, -2), (key1008, -2), (key1043, -2), (key1129, -2), (key1157, -2), (key1021, -2), (key1078, -2), (key1008, -2), (key1043, -2), (key1117, 4), (key1004, 4), (key1039, 4)]

theorem rawRowCheck16309 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form5 = rawRow16309 := by decide +kernel

def row16309 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

theorem rowCheck16309 : row16309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16309 := by decide +kernel

theorem rowEval16309 (x : Key → ℝ) : Integer.Sparse.eval row16309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck16309, Integer.Sparse.eval_collectBalanced, rawRowCheck16309]

def rawRow16310 : Integer.Sparse Key := [(key1176, 4), (key1081, 4), (key1023, 4), (key1157, -2), (key1129, -2), (key1078, -2), (key1021, -2), (key1043, -2), (key1008, -2), (key1157, -2), (key1129, -2), (key1078, -2), (key1021, -2), (key1043, -2), (key1008, -2), (key1117, 4), (key1039, 4), (key1004, 4)]

theorem rawRowCheck16310 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form5 = rawRow16310 := by decide +kernel

def row16310 : Integer.Sparse Key := [(key1004, 4), (key1008, -4), (key1021, -4), (key1023, 4), (key1039, 4), (key1043, -4), (key1078, -4), (key1081, 4), (key1117, 4), (key1129, -4), (key1157, -4), (key1176, 4)]

theorem rowCheck16310 : row16310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16310 := by decide +kernel

theorem rowEval16310 (x : Key → ℝ) : Integer.Sparse.eval row16310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form5) x := by
  rw [rowCheck16310, Integer.Sparse.eval_collectBalanced, rawRowCheck16310]

def rawRow16311 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key3026, -1), (key3026, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1), (key2658, 2), (key2923, 2), (key2923, 2), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1)]

theorem rawRowCheck16311 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form6 = rawRow16311 := by decide +kernel

def row16311 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -2), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key3017, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck16311 : row16311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16311 := by decide +kernel

theorem rowEval16311 (x : Key → ℝ) : Integer.Sparse.eval row16311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16311, Integer.Sparse.eval_collectBalanced, rawRowCheck16311]

def rawRow16312 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2870, -1), (key3026, -1), (key2632, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2923, 2), (key2658, 2), (key2923, 2), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1)]

theorem rawRowCheck16312 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form6 = rawRow16312 := by decide +kernel

def row16312 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key2948, -1), (key2960, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck16312 : row16312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16312 := by decide +kernel

theorem rowEval16312 (x : Key → ℝ) : Integer.Sparse.eval row16312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16312, Integer.Sparse.eval_collectBalanced, rawRowCheck16312]

def rawRow16313 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key3026, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1), (key2923, 2), (key2923, 2), (key2658, 2), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1)]

theorem rawRowCheck16313 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form6 = rawRow16313 := by decide +kernel

def row16313 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key2948, -1), (key2960, -2), (key3026, -2), (key3030, 4)]

theorem rowCheck16313 : row16313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16313 := by decide +kernel

theorem rowEval16313 (x : Key → ℝ) : Integer.Sparse.eval row16313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16313, Integer.Sparse.eval_collectBalanced, rawRowCheck16313]

def rawRow16314 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2640, -1), (key2644, -1), (key2860, -1), (key2885, -1), (key3023, -1), (key3030, -1), (key2632, 2), (key2644, 2), (key2706, 2), (key2732, 2), (key3023, 2), (key3026, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1), (key2660, 2), (key2920, 2), (key2927, 2), (key2658, -1), (key2660, -1), (key2753, -1), (key2758, -1), (key2920, -1), (key2923, -1)]

theorem rawRowCheck16314 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form6 = rawRow16314 := by decide +kernel

def row16314 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

theorem rowCheck16314 : row16314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16314 := by decide +kernel

theorem rowEval16314 (x : Key → ℝ) : Integer.Sparse.eval row16314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16314, Integer.Sparse.eval_collectBalanced, rawRowCheck16314]

def rawRow16315 : Integer.Sparse Key := [(key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2644, -1), (key2640, -1), (key2885, -1), (key2860, -1), (key3030, -1), (key3023, -1), (key2644, 2), (key2632, 2), (key2732, 2), (key2706, 2), (key3026, 2), (key3023, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1), (key2660, 2), (key2927, 2), (key2920, 2), (key2660, -1), (key2658, -1), (key2758, -1), (key2753, -1), (key2923, -1), (key2920, -1)]

theorem rawRowCheck16315 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form6 = rawRow16315 := by decide +kernel

def row16315 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

theorem rowCheck16315 : row16315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16315 := by decide +kernel

theorem rowEval16315 (x : Key → ℝ) : Integer.Sparse.eval row16315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16315, Integer.Sparse.eval_collectBalanced, rawRowCheck16315]

def rawRow16316 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2860, -1), (key3023, -1), (key2640, -1), (key3030, -1), (key2644, -1), (key2885, -1), (key2706, 2), (key3023, 2), (key2632, 2), (key3026, 2), (key2644, 2), (key2732, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2920, 2), (key2660, 2), (key2927, 2), (key2753, -1), (key2920, -1), (key2658, -1), (key2923, -1), (key2660, -1), (key2758, -1)]

theorem rawRowCheck16316 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form6 = rawRow16316 := by decide +kernel

def row16316 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

theorem rowCheck16316 : row16316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16316 := by decide +kernel

theorem rowEval16316 (x : Key → ℝ) : Integer.Sparse.eval row16316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16316, Integer.Sparse.eval_collectBalanced, rawRowCheck16316]

def rawRow16317 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key3023, -1), (key2860, -1), (key3030, -1), (key2640, -1), (key2885, -1), (key2644, -1), (key3023, 2), (key2706, 2), (key3026, 2), (key2632, 2), (key2732, 2), (key2644, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1), (key2920, 2), (key2927, 2), (key2660, 2), (key2920, -1), (key2753, -1), (key2923, -1), (key2658, -1), (key2758, -1), (key2660, -1)]

theorem rawRowCheck16317 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form6 = rawRow16317 := by decide +kernel

def row16317 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

theorem rowCheck16317 : row16317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16317 := by decide +kernel

theorem rowEval16317 (x : Key → ℝ) : Integer.Sparse.eval row16317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16317, Integer.Sparse.eval_collectBalanced, rawRowCheck16317]

def rawRow16318 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2885, -1), (key3030, -1), (key2644, -1), (key3023, -1), (key2640, -1), (key2860, -1), (key2732, 2), (key3026, 2), (key2644, 2), (key3023, 2), (key2632, 2), (key2706, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1), (key2927, 2), (key2660, 2), (key2920, 2), (key2758, -1), (key2923, -1), (key2660, -1), (key2920, -1), (key2658, -1), (key2753, -1)]

theorem rawRowCheck16318 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form6 = rawRow16318 := by decide +kernel

def row16318 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

theorem rowCheck16318 : row16318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16318 := by decide +kernel

theorem rowEval16318 (x : Key → ℝ) : Integer.Sparse.eval row16318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16318, Integer.Sparse.eval_collectBalanced, rawRowCheck16318]

def rawRow16319 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key3030, -1), (key2885, -1), (key3023, -1), (key2644, -1), (key2860, -1), (key2640, -1), (key3026, 2), (key2732, 2), (key3023, 2), (key2644, 2), (key2706, 2), (key2632, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2927, 2), (key2920, 2), (key2660, 2), (key2923, -1), (key2758, -1), (key2920, -1), (key2660, -1), (key2753, -1), (key2658, -1)]

theorem rawRowCheck16319 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form6 = rawRow16319 := by decide +kernel

def row16319 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

theorem rowCheck16319 : row16319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16319 := by decide +kernel

theorem rowEval16319 (x : Key → ℝ) : Integer.Sparse.eval row16319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16319, Integer.Sparse.eval_collectBalanced, rawRowCheck16319]

def rawRow16320 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, 2), (key2976, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1)]

theorem rawRowCheck16320 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form6 = rawRow16320 := by decide +kernel

def row16320 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -2), (key2835, 4), (key2885, -2), (key2927, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3017, -2), (key3030, 4)]

theorem rowCheck16320 : row16320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16320 := by decide +kernel

theorem rowEval16320 (x : Key → ℝ) : Integer.Sparse.eval row16320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16320, Integer.Sparse.eval_collectBalanced, rawRowCheck16320]

def rawRow16321 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2976, 2), (key2641, 2), (key2976, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1)]

theorem rawRowCheck16321 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form6 = rawRow16321 := by decide +kernel

def row16321 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2885, -2), (key2927, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3030, 4)]

theorem rowCheck16321 : row16321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16321 := by decide +kernel

theorem rowEval16321 (x : Key → ℝ) : Integer.Sparse.eval row16321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16321, Integer.Sparse.eval_collectBalanced, rawRowCheck16321]

def rawRow16322 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2976, 2), (key2976, 2), (key2641, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1)]

theorem rawRowCheck16322 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form6 = rawRow16322 := by decide +kernel

def row16322 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2885, -2), (key2927, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3030, 4)]

theorem rowCheck16322 : row16322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16322 := by decide +kernel

theorem rowEval16322 (x : Key → ℝ) : Integer.Sparse.eval row16322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16322, Integer.Sparse.eval_collectBalanced, rawRowCheck16322]

def rawRow16323 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2628, 2), (key2702, 2), (key2972, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1), (key2644, 2), (key2798, 2), (key2885, 2), (key2621, -1), (key2644, -1), (key2676, -1), (key2732, -1), (key2798, -1), (key2835, -1)]

theorem rawRowCheck16323 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form6 = rawRow16323 := by decide +kernel

def row16323 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

theorem rowCheck16323 : row16323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16323 := by decide +kernel

theorem rowEval16323 (x : Key → ℝ) : Integer.Sparse.eval row16323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16323, Integer.Sparse.eval_collectBalanced, rawRowCheck16323]

def rawRow16324 : Integer.Sparse Key := [(key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2628, 2), (key2972, 2), (key2702, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1), (key2644, 2), (key2885, 2), (key2798, 2), (key2644, -1), (key2621, -1), (key2732, -1), (key2676, -1), (key2835, -1), (key2798, -1)]

theorem rawRowCheck16324 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form6 = rawRow16324 := by decide +kernel

def row16324 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

theorem rowCheck16324 : row16324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16324 := by decide +kernel

theorem rowEval16324 (x : Key → ℝ) : Integer.Sparse.eval row16324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16324, Integer.Sparse.eval_collectBalanced, rawRowCheck16324]

def rawRow16325 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2702, 2), (key2628, 2), (key2972, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2798, 2), (key2644, 2), (key2885, 2), (key2676, -1), (key2798, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2732, -1)]

theorem rawRowCheck16325 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form6 = rawRow16325 := by decide +kernel

def row16325 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

theorem rowCheck16325 : row16325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16325 := by decide +kernel

theorem rowEval16325 (x : Key → ℝ) : Integer.Sparse.eval row16325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16325, Integer.Sparse.eval_collectBalanced, rawRowCheck16325]

def rawRow16326 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2702, 2), (key2972, 2), (key2628, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1), (key2798, 2), (key2885, 2), (key2644, 2), (key2798, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2732, -1), (key2644, -1)]

theorem rawRowCheck16326 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form6 = rawRow16326 := by decide +kernel

def row16326 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

theorem rowCheck16326 : row16326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16326 := by decide +kernel

theorem rowEval16326 (x : Key → ℝ) : Integer.Sparse.eval row16326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16326, Integer.Sparse.eval_collectBalanced, rawRowCheck16326]

def rawRow16327 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2972, 2), (key2628, 2), (key2702, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1), (key2885, 2), (key2644, 2), (key2798, 2), (key2732, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2621, -1), (key2676, -1)]

theorem rawRowCheck16327 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form6 = rawRow16327 := by decide +kernel

def row16327 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

theorem rowCheck16327 : row16327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16327 := by decide +kernel

theorem rowEval16327 (x : Key → ℝ) : Integer.Sparse.eval row16327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16327, Integer.Sparse.eval_collectBalanced, rawRowCheck16327]

def rawRow16328 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2972, 2), (key2702, 2), (key2628, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2885, 2), (key2798, 2), (key2644, 2), (key2835, -1), (key2732, -1), (key2798, -1), (key2644, -1), (key2676, -1), (key2621, -1)]

theorem rawRowCheck16328 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form6 = rawRow16328 := by decide +kernel

def row16328 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

theorem rowCheck16328 : row16328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16328 := by decide +kernel

theorem rowEval16328 (x : Key → ℝ) : Integer.Sparse.eval row16328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16328, Integer.Sparse.eval_collectBalanced, rawRowCheck16328]

def rawRow16329 : Integer.Sparse Key := [(key2646, -1), (key2648, -1), (key2893, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2653, 2), (key2897, 2), (key2998, 2), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2628, 2), (key2648, 2), (key2782, 2), (key2938, 2), (key2904, 2), (key2983, 2), (key2641, -1), (key2653, -1), (key2795, -1), (key2943, -1), (key2897, -1), (key2976, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1)]

theorem rawRowCheck16329 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form6 = rawRow16329 := by decide +kernel

def row16329 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

theorem rowCheck16329 : row16329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16329 := by decide +kernel

theorem rowEval16329 (x : Key → ℝ) : Integer.Sparse.eval row16329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16329, Integer.Sparse.eval_collectBalanced, rawRowCheck16329]

def rawRow16330 : Integer.Sparse Key := [(key2648, -1), (key2646, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2904, -1), (key2653, 2), (key2998, 2), (key2897, 2), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2648, 2), (key2628, 2), (key2938, 2), (key2782, 2), (key2983, 2), (key2904, 2), (key2653, -1), (key2641, -1), (key2943, -1), (key2795, -1), (key2976, -1), (key2897, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1)]

theorem rawRowCheck16330 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form6 = rawRow16330 := by decide +kernel

def row16330 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

theorem rowCheck16330 : row16330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16330 := by decide +kernel

theorem rowEval16330 (x : Key → ℝ) : Integer.Sparse.eval row16330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16330, Integer.Sparse.eval_collectBalanced, rawRowCheck16330]

def rawRow16331 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2897, 2), (key2653, 2), (key2998, 2), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2782, 2), (key2904, 2), (key2628, 2), (key2983, 2), (key2648, 2), (key2938, 2), (key2795, -1), (key2897, -1), (key2641, -1), (key2976, -1), (key2653, -1), (key2943, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1)]

theorem rawRowCheck16331 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form6 = rawRow16331 := by decide +kernel

def row16331 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

theorem rowCheck16331 : row16331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16331 := by decide +kernel

theorem rowEval16331 (x : Key → ℝ) : Integer.Sparse.eval row16331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16331, Integer.Sparse.eval_collectBalanced, rawRowCheck16331]

def rawRow16332 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2997, -1), (key2648, -1), (key2897, 2), (key2998, 2), (key2653, 2), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2904, 2), (key2782, 2), (key2983, 2), (key2628, 2), (key2938, 2), (key2648, 2), (key2897, -1), (key2795, -1), (key2976, -1), (key2641, -1), (key2943, -1), (key2653, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1)]

theorem rawRowCheck16332 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form6 = rawRow16332 := by decide +kernel

def row16332 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

theorem rowCheck16332 : row16332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16332 := by decide +kernel

theorem rowEval16332 (x : Key → ℝ) : Integer.Sparse.eval row16332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16332, Integer.Sparse.eval_collectBalanced, rawRowCheck16332]

def rawRow16333 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2646, -1), (key2893, -1), (key2998, 2), (key2653, 2), (key2897, 2), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2938, 2), (key2983, 2), (key2648, 2), (key2904, 2), (key2628, 2), (key2782, 2), (key2943, -1), (key2976, -1), (key2653, -1), (key2897, -1), (key2641, -1), (key2795, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1)]

theorem rawRowCheck16333 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form6 = rawRow16333 := by decide +kernel

def row16333 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

theorem rowCheck16333 : row16333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16333 := by decide +kernel

theorem rowEval16333 (x : Key → ℝ) : Integer.Sparse.eval row16333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16333, Integer.Sparse.eval_collectBalanced, rawRowCheck16333]

def rawRow16334 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2904, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key2998, 2), (key2897, 2), (key2653, 2), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 2), (key2938, 2), (key2904, 2), (key2648, 2), (key2782, 2), (key2628, 2), (key2976, -1), (key2943, -1), (key2897, -1), (key2653, -1), (key2795, -1), (key2641, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1)]

theorem rawRowCheck16334 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form6 = rawRow16334 := by decide +kernel

def row16334 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

theorem rowCheck16334 : row16334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16334 := by decide +kernel

theorem rowEval16334 (x : Key → ℝ) : Integer.Sparse.eval row16334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16334, Integer.Sparse.eval_collectBalanced, rawRowCheck16334]

def rawRow16335 : Integer.Sparse Key := [(key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2648, 2), (key2737, 2), (key2997, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2), (key2618, -1), (key2648, -1), (key2673, -1), (key2938, -1), (key2737, -1), (key2950, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1)]

theorem rawRowCheck16335 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form6 = rawRow16335 := by decide +kernel

def row16335 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

theorem rowCheck16335 : row16335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16335 := by decide +kernel

theorem rowEval16335 (x : Key → ℝ) : Integer.Sparse.eval row16335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16335, Integer.Sparse.eval_collectBalanced, rawRowCheck16335]

def rawRow16336 : Integer.Sparse Key := [(key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2648, 2), (key2997, 2), (key2737, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2), (key2648, -1), (key2618, -1), (key2938, -1), (key2673, -1), (key2950, -1), (key2737, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1)]

theorem rawRowCheck16336 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form6 = rawRow16336 := by decide +kernel

def row16336 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

theorem rowCheck16336 : row16336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16336 := by decide +kernel

theorem rowEval16336 (x : Key → ℝ) : Integer.Sparse.eval row16336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16336, Integer.Sparse.eval_collectBalanced, rawRowCheck16336]

def rawRow16337 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2737, 2), (key2648, 2), (key2997, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2), (key2673, -1), (key2737, -1), (key2618, -1), (key2950, -1), (key2648, -1), (key2938, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1)]

theorem rawRowCheck16337 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form6 = rawRow16337 := by decide +kernel

def row16337 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

theorem rowCheck16337 : row16337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16337 := by decide +kernel

theorem rowEval16337 (x : Key → ℝ) : Integer.Sparse.eval row16337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16337, Integer.Sparse.eval_collectBalanced, rawRowCheck16337]

def rawRow16338 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2737, 2), (key2997, 2), (key2648, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2), (key2737, -1), (key2673, -1), (key2950, -1), (key2618, -1), (key2938, -1), (key2648, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1)]

theorem rawRowCheck16338 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form6 = rawRow16338 := by decide +kernel

def row16338 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

theorem rowCheck16338 : row16338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16338 := by decide +kernel

theorem rowEval16338 (x : Key → ℝ) : Integer.Sparse.eval row16338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16338, Integer.Sparse.eval_collectBalanced, rawRowCheck16338]

def rawRow16339 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2997, 2), (key2648, 2), (key2737, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2), (key2938, -1), (key2950, -1), (key2648, -1), (key2737, -1), (key2618, -1), (key2673, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1)]

theorem rawRowCheck16339 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form6 = rawRow16339 := by decide +kernel

def row16339 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

theorem rowCheck16339 : row16339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16339 := by decide +kernel

theorem rowEval16339 (x : Key → ℝ) : Integer.Sparse.eval row16339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16339, Integer.Sparse.eval_collectBalanced, rawRowCheck16339]

def rawRow16340 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2997, 2), (key2737, 2), (key2648, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2), (key2950, -1), (key2938, -1), (key2737, -1), (key2648, -1), (key2673, -1), (key2618, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1)]

theorem rawRowCheck16340 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form6 = rawRow16340 := by decide +kernel

def row16340 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

theorem rowCheck16340 : row16340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16340 := by decide +kernel

theorem rowEval16340 (x : Key → ℝ) : Integer.Sparse.eval row16340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16340, Integer.Sparse.eval_collectBalanced, rawRowCheck16340]

def rawRow16341 : Integer.Sparse Key := [(key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2646, 2), (key2735, 2), (key2893, 2), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2618, 2), (key2641, 2), (key2673, 2), (key2795, 2), (key2728, 2), (key2831, 2), (key2612, -1), (key2628, -1), (key2667, -1), (key2782, -1), (key2702, -1), (key2805, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1)]

theorem rawRowCheck16341 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form6 = rawRow16341 := by decide +kernel

def row16341 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

theorem rowCheck16341 : row16341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16341 := by decide +kernel

theorem rowEval16341 (x : Key → ℝ) : Integer.Sparse.eval row16341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16341, Integer.Sparse.eval_collectBalanced, rawRowCheck16341]

def rawRow16342 : Integer.Sparse Key := [(key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2646, 2), (key2893, 2), (key2735, 2), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2641, 2), (key2618, 2), (key2795, 2), (key2673, 2), (key2831, 2), (key2728, 2), (key2628, -1), (key2612, -1), (key2782, -1), (key2667, -1), (key2805, -1), (key2702, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1)]

theorem rawRowCheck16342 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form6 = rawRow16342 := by decide +kernel

def row16342 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

theorem rowCheck16342 : row16342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16342 := by decide +kernel

theorem rowEval16342 (x : Key → ℝ) : Integer.Sparse.eval row16342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16342, Integer.Sparse.eval_collectBalanced, rawRowCheck16342]

def rawRow16343 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2735, 2), (key2646, 2), (key2893, 2), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2673, 2), (key2728, 2), (key2618, 2), (key2831, 2), (key2641, 2), (key2795, 2), (key2667, -1), (key2702, -1), (key2612, -1), (key2805, -1), (key2628, -1), (key2782, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1)]

theorem rawRowCheck16343 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form6 = rawRow16343 := by decide +kernel

def row16343 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

theorem rowCheck16343 : row16343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16343 := by decide +kernel

theorem rowEval16343 (x : Key → ℝ) : Integer.Sparse.eval row16343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck16343, Integer.Sparse.eval_collectBalanced, rawRowCheck16343]

def rawRow16344 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2735, 2), (key2893, 2), (key2646, 2), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2728, 2), (key2673, 2), (key2831, 2), (key2618, 2), (key2795, 2), (key2641, 2), (key2702, -1), (key2667, -1), (key2805, -1), (key2612, -1), (key2782, -1), (key2628, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1)]

theorem rawRowCheck16344 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form6 = rawRow16344 := by decide +kernel

def row16344 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

theorem rowCheck16344 : row16344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16344 := by decide +kernel

theorem rowEval16344 (x : Key → ℝ) : Integer.Sparse.eval row16344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16344, Integer.Sparse.eval_collectBalanced, rawRowCheck16344]

def rawRow16345 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2893, 2), (key2646, 2), (key2735, 2), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2795, 2), (key2831, 2), (key2641, 2), (key2728, 2), (key2618, 2), (key2673, 2), (key2782, -1), (key2805, -1), (key2628, -1), (key2702, -1), (key2612, -1), (key2667, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1)]

theorem rawRowCheck16345 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form6 = rawRow16345 := by decide +kernel

def row16345 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

theorem rowCheck16345 : row16345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16345 := by decide +kernel

theorem rowEval16345 (x : Key → ℝ) : Integer.Sparse.eval row16345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck16345, Integer.Sparse.eval_collectBalanced, rawRowCheck16345]

def rawRow16346 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2893, 2), (key2735, 2), (key2646, 2), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2831, 2), (key2795, 2), (key2728, 2), (key2641, 2), (key2673, 2), (key2618, 2), (key2805, -1), (key2782, -1), (key2702, -1), (key2628, -1), (key2667, -1), (key2612, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1)]

theorem rawRowCheck16346 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form6 = rawRow16346 := by decide +kernel

def row16346 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

theorem rowCheck16346 : row16346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16346 := by decide +kernel

theorem rowEval16346 (x : Key → ℝ) : Integer.Sparse.eval row16346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form6) x := by
  rw [rowCheck16346, Integer.Sparse.eval_collectBalanced, rawRowCheck16346]

def rawRow16347 : Integer.Sparse Key := [(key2685, 4), (key2821, 4), (key2821, 4), (key2692, -4), (key2692, -4), (key2830, -4), (key2718, -4), (key2718, -4), (key2871, -4), (key2727, 12)]

theorem rawRowCheck16347 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form7 = rawRow16347 := by decide +kernel

def row16347 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

theorem rowCheck16347 : row16347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16347 := by decide +kernel

theorem rowEval16347 (x : Key → ℝ) : Integer.Sparse.eval row16347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16347, Integer.Sparse.eval_collectBalanced, rawRowCheck16347]

def rawRow16348 : Integer.Sparse Key := [(key2821, 4), (key2685, 4), (key2821, 4), (key2692, -4), (key2830, -4), (key2692, -4), (key2718, -4), (key2871, -4), (key2718, -4), (key2727, 12)]

theorem rawRowCheck16348 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form7 = rawRow16348 := by decide +kernel

def row16348 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

theorem rowCheck16348 : row16348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16348 := by decide +kernel

theorem rowEval16348 (x : Key → ℝ) : Integer.Sparse.eval row16348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16348, Integer.Sparse.eval_collectBalanced, rawRowCheck16348]

def rawRow16349 : Integer.Sparse Key := [(key2821, 4), (key2821, 4), (key2685, 4), (key2830, -4), (key2692, -4), (key2692, -4), (key2871, -4), (key2718, -4), (key2718, -4), (key2727, 12)]

theorem rawRowCheck16349 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form7 = rawRow16349 := by decide +kernel

def row16349 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

theorem rowCheck16349 : row16349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16349 := by decide +kernel

theorem rowEval16349 (x : Key → ℝ) : Integer.Sparse.eval row16349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16349, Integer.Sparse.eval_collectBalanced, rawRowCheck16349]

def rawRow16350 : Integer.Sparse Key := [(key2692, 4), (key2821, 4), (key2830, 4), (key2685, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2727, -4), (key2871, -4), (key2718, 12)]

theorem rawRowCheck16350 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form7 = rawRow16350 := by decide +kernel

def row16350 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16350 : row16350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16350 := by decide +kernel

theorem rowEval16350 (x : Key → ℝ) : Integer.Sparse.eval row16350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16350, Integer.Sparse.eval_collectBalanced, rawRowCheck16350]

def rawRow16351 : Integer.Sparse Key := [(key2692, 4), (key2830, 4), (key2821, 4), (key2692, -4), (key2685, -4), (key2821, -4), (key2727, -4), (key2718, -4), (key2871, -4), (key2718, 12)]

theorem rawRowCheck16351 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form7 = rawRow16351 := by decide +kernel

def row16351 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16351 : row16351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16351 := by decide +kernel

theorem rowEval16351 (x : Key → ℝ) : Integer.Sparse.eval row16351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16351, Integer.Sparse.eval_collectBalanced, rawRowCheck16351]

def rawRow16352 : Integer.Sparse Key := [(key2821, 4), (key2692, 4), (key2830, 4), (key2685, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2871, -4), (key2727, -4), (key2718, 12)]

theorem rawRowCheck16352 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form7 = rawRow16352 := by decide +kernel

def row16352 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16352 : row16352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16352 := by decide +kernel

theorem rowEval16352 (x : Key → ℝ) : Integer.Sparse.eval row16352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16352, Integer.Sparse.eval_collectBalanced, rawRowCheck16352]

def rawRow16353 : Integer.Sparse Key := [(key2821, 4), (key2830, 4), (key2692, 4), (key2821, -4), (key2685, -4), (key2692, -4), (key2871, -4), (key2718, -4), (key2727, -4), (key2718, 12)]

theorem rawRowCheck16353 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form7 = rawRow16353 := by decide +kernel

def row16353 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16353 : row16353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16353 := by decide +kernel

theorem rowEval16353 (x : Key → ℝ) : Integer.Sparse.eval row16353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16353, Integer.Sparse.eval_collectBalanced, rawRowCheck16353]

def rawRow16354 : Integer.Sparse Key := [(key2830, 4), (key2692, 4), (key2821, 4), (key2692, -4), (key2821, -4), (key2685, -4), (key2727, -4), (key2871, -4), (key2718, -4), (key2718, 12)]

theorem rawRowCheck16354 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form7 = rawRow16354 := by decide +kernel

def row16354 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16354 : row16354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16354 := by decide +kernel

theorem rowEval16354 (x : Key → ℝ) : Integer.Sparse.eval row16354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16354, Integer.Sparse.eval_collectBalanced, rawRowCheck16354]

def rawRow16355 : Integer.Sparse Key := [(key2830, 4), (key2821, 4), (key2692, 4), (key2821, -4), (key2692, -4), (key2685, -4), (key2871, -4), (key2727, -4), (key2718, -4), (key2718, 12)]

theorem rawRowCheck16355 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form7 = rawRow16355 := by decide +kernel

def row16355 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16355 : row16355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16355 := by decide +kernel

theorem rowEval16355 (x : Key → ℝ) : Integer.Sparse.eval row16355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16355, Integer.Sparse.eval_collectBalanced, rawRowCheck16355]

def rawRow16356 : Integer.Sparse Key := [(key2685, 4), (key2821, 4), (key2821, 4), (key2718, -4), (key2718, -4), (key2871, -4), (key2692, -4), (key2692, -4), (key2830, -4), (key2727, 12)]

theorem rawRowCheck16356 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form7 = rawRow16356 := by decide +kernel

def row16356 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

theorem rowCheck16356 : row16356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16356 := by decide +kernel

theorem rowEval16356 (x : Key → ℝ) : Integer.Sparse.eval row16356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16356, Integer.Sparse.eval_collectBalanced, rawRowCheck16356]

def rawRow16357 : Integer.Sparse Key := [(key2821, 4), (key2685, 4), (key2821, 4), (key2718, -4), (key2871, -4), (key2718, -4), (key2692, -4), (key2830, -4), (key2692, -4), (key2727, 12)]

theorem rawRowCheck16357 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form7 = rawRow16357 := by decide +kernel

def row16357 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

theorem rowCheck16357 : row16357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16357 := by decide +kernel

theorem rowEval16357 (x : Key → ℝ) : Integer.Sparse.eval row16357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16357, Integer.Sparse.eval_collectBalanced, rawRowCheck16357]

def rawRow16358 : Integer.Sparse Key := [(key2821, 4), (key2821, 4), (key2685, 4), (key2871, -4), (key2718, -4), (key2718, -4), (key2830, -4), (key2692, -4), (key2692, -4), (key2727, 12)]

theorem rawRowCheck16358 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form7 = rawRow16358 := by decide +kernel

def row16358 : Integer.Sparse Key := [(key2685, 4), (key2692, -8), (key2718, -8), (key2727, 12), (key2821, 8), (key2830, -4), (key2871, -4)]

theorem rowCheck16358 : row16358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16358 := by decide +kernel

theorem rowEval16358 (x : Key → ℝ) : Integer.Sparse.eval row16358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16358, Integer.Sparse.eval_collectBalanced, rawRowCheck16358]

def rawRow16359 : Integer.Sparse Key := [(key2718, 4), (key2821, 4), (key2871, 4), (key2685, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2727, -4), (key2830, -4), (key2692, 12)]

theorem rawRowCheck16359 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form7 = rawRow16359 := by decide +kernel

def row16359 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16359 : row16359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16359 := by decide +kernel

theorem rowEval16359 (x : Key → ℝ) : Integer.Sparse.eval row16359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16359, Integer.Sparse.eval_collectBalanced, rawRowCheck16359]

def rawRow16360 : Integer.Sparse Key := [(key2718, 4), (key2871, 4), (key2821, 4), (key2718, -4), (key2685, -4), (key2821, -4), (key2727, -4), (key2692, -4), (key2830, -4), (key2692, 12)]

theorem rawRowCheck16360 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form7 = rawRow16360 := by decide +kernel

def row16360 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16360 : row16360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16360 := by decide +kernel

theorem rowEval16360 (x : Key → ℝ) : Integer.Sparse.eval row16360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16360, Integer.Sparse.eval_collectBalanced, rawRowCheck16360]

def rawRow16361 : Integer.Sparse Key := [(key2821, 4), (key2718, 4), (key2871, 4), (key2685, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2830, -4), (key2727, -4), (key2692, 12)]

theorem rawRowCheck16361 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form7 = rawRow16361 := by decide +kernel

def row16361 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16361 : row16361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16361 := by decide +kernel

theorem rowEval16361 (x : Key → ℝ) : Integer.Sparse.eval row16361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16361, Integer.Sparse.eval_collectBalanced, rawRowCheck16361]

def rawRow16362 : Integer.Sparse Key := [(key2821, 4), (key2871, 4), (key2718, 4), (key2821, -4), (key2685, -4), (key2718, -4), (key2830, -4), (key2692, -4), (key2727, -4), (key2692, 12)]

theorem rawRowCheck16362 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form7 = rawRow16362 := by decide +kernel

def row16362 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16362 : row16362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16362 := by decide +kernel

theorem rowEval16362 (x : Key → ℝ) : Integer.Sparse.eval row16362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16362, Integer.Sparse.eval_collectBalanced, rawRowCheck16362]

def rawRow16363 : Integer.Sparse Key := [(key2871, 4), (key2718, 4), (key2821, 4), (key2718, -4), (key2821, -4), (key2685, -4), (key2727, -4), (key2830, -4), (key2692, -4), (key2692, 12)]

theorem rawRowCheck16363 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form7 = rawRow16363 := by decide +kernel

def row16363 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16363 : row16363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16363 := by decide +kernel

theorem rowEval16363 (x : Key → ℝ) : Integer.Sparse.eval row16363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16363, Integer.Sparse.eval_collectBalanced, rawRowCheck16363]

def rawRow16364 : Integer.Sparse Key := [(key2871, 4), (key2821, 4), (key2718, 4), (key2821, -4), (key2718, -4), (key2685, -4), (key2830, -4), (key2727, -4), (key2692, -4), (key2692, 12)]

theorem rawRowCheck16364 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form7 = rawRow16364 := by decide +kernel

def row16364 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16364 : row16364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16364 := by decide +kernel

theorem rowEval16364 (x : Key → ℝ) : Integer.Sparse.eval row16364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16364, Integer.Sparse.eval_collectBalanced, rawRowCheck16364]

def rawRow16365 : Integer.Sparse Key := [(key2692, 4), (key2821, 4), (key2830, 4), (key2718, -4), (key2727, -4), (key2871, -4), (key2685, -4), (key2692, -4), (key2821, -4), (key2718, 12)]

theorem rawRowCheck16365 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form7 = rawRow16365 := by decide +kernel

def row16365 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16365 : row16365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16365 := by decide +kernel

theorem rowEval16365 (x : Key → ℝ) : Integer.Sparse.eval row16365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16365, Integer.Sparse.eval_collectBalanced, rawRowCheck16365]

def rawRow16366 : Integer.Sparse Key := [(key2692, 4), (key2830, 4), (key2821, 4), (key2727, -4), (key2718, -4), (key2871, -4), (key2692, -4), (key2685, -4), (key2821, -4), (key2718, 12)]

theorem rawRowCheck16366 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form7 = rawRow16366 := by decide +kernel

def row16366 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16366 : row16366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16366 := by decide +kernel

theorem rowEval16366 (x : Key → ℝ) : Integer.Sparse.eval row16366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16366, Integer.Sparse.eval_collectBalanced, rawRowCheck16366]

def rawRow16367 : Integer.Sparse Key := [(key2821, 4), (key2692, 4), (key2830, 4), (key2718, -4), (key2871, -4), (key2727, -4), (key2685, -4), (key2821, -4), (key2692, -4), (key2718, 12)]

theorem rawRowCheck16367 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form7 = rawRow16367 := by decide +kernel

def row16367 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16367 : row16367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16367 := by decide +kernel

theorem rowEval16367 (x : Key → ℝ) : Integer.Sparse.eval row16367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16367, Integer.Sparse.eval_collectBalanced, rawRowCheck16367]

def rawRow16368 : Integer.Sparse Key := [(key2821, 4), (key2830, 4), (key2692, 4), (key2871, -4), (key2718, -4), (key2727, -4), (key2821, -4), (key2685, -4), (key2692, -4), (key2718, 12)]

theorem rawRowCheck16368 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form7 = rawRow16368 := by decide +kernel

def row16368 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16368 : row16368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16368 := by decide +kernel

theorem rowEval16368 (x : Key → ℝ) : Integer.Sparse.eval row16368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16368, Integer.Sparse.eval_collectBalanced, rawRowCheck16368]

def rawRow16369 : Integer.Sparse Key := [(key2830, 4), (key2692, 4), (key2821, 4), (key2727, -4), (key2871, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2685, -4), (key2718, 12)]

theorem rawRowCheck16369 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form7 = rawRow16369 := by decide +kernel

def row16369 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16369 : row16369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16369 := by decide +kernel

theorem rowEval16369 (x : Key → ℝ) : Integer.Sparse.eval row16369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16369, Integer.Sparse.eval_collectBalanced, rawRowCheck16369]

def rawRow16370 : Integer.Sparse Key := [(key2830, 4), (key2821, 4), (key2692, 4), (key2871, -4), (key2727, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2685, -4), (key2718, 12)]

theorem rawRowCheck16370 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form7 = rawRow16370 := by decide +kernel

def row16370 : Integer.Sparse Key := [(key2685, -4), (key2718, 8), (key2727, -4), (key2830, 4), (key2871, -4)]

theorem rowCheck16370 : row16370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16370 := by decide +kernel

theorem rowEval16370 (x : Key → ℝ) : Integer.Sparse.eval row16370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16370, Integer.Sparse.eval_collectBalanced, rawRowCheck16370]

def rawRow16371 : Integer.Sparse Key := [(key2718, 4), (key2821, 4), (key2871, 4), (key2692, -4), (key2727, -4), (key2830, -4), (key2685, -4), (key2718, -4), (key2821, -4), (key2692, 12)]

theorem rawRowCheck16371 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form7 = rawRow16371 := by decide +kernel

def row16371 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16371 : row16371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16371 := by decide +kernel

theorem rowEval16371 (x : Key → ℝ) : Integer.Sparse.eval row16371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16371, Integer.Sparse.eval_collectBalanced, rawRowCheck16371]

def rawRow16372 : Integer.Sparse Key := [(key2718, 4), (key2871, 4), (key2821, 4), (key2727, -4), (key2692, -4), (key2830, -4), (key2718, -4), (key2685, -4), (key2821, -4), (key2692, 12)]

theorem rawRowCheck16372 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form7 = rawRow16372 := by decide +kernel

def row16372 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16372 : row16372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16372 := by decide +kernel

theorem rowEval16372 (x : Key → ℝ) : Integer.Sparse.eval row16372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16372, Integer.Sparse.eval_collectBalanced, rawRowCheck16372]

def rawRow16373 : Integer.Sparse Key := [(key2821, 4), (key2718, 4), (key2871, 4), (key2692, -4), (key2830, -4), (key2727, -4), (key2685, -4), (key2821, -4), (key2718, -4), (key2692, 12)]

theorem rawRowCheck16373 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form7 = rawRow16373 := by decide +kernel

def row16373 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16373 : row16373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16373 := by decide +kernel

theorem rowEval16373 (x : Key → ℝ) : Integer.Sparse.eval row16373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16373, Integer.Sparse.eval_collectBalanced, rawRowCheck16373]

def rawRow16374 : Integer.Sparse Key := [(key2821, 4), (key2871, 4), (key2718, 4), (key2830, -4), (key2692, -4), (key2727, -4), (key2821, -4), (key2685, -4), (key2718, -4), (key2692, 12)]

theorem rawRowCheck16374 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form7 = rawRow16374 := by decide +kernel

def row16374 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16374 : row16374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16374 := by decide +kernel

theorem rowEval16374 (x : Key → ℝ) : Integer.Sparse.eval row16374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16374, Integer.Sparse.eval_collectBalanced, rawRowCheck16374]

def rawRow16375 : Integer.Sparse Key := [(key2871, 4), (key2718, 4), (key2821, 4), (key2727, -4), (key2830, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2685, -4), (key2692, 12)]

theorem rawRowCheck16375 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form7 = rawRow16375 := by decide +kernel

def row16375 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16375 : row16375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16375 := by decide +kernel

theorem rowEval16375 (x : Key → ℝ) : Integer.Sparse.eval row16375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16375, Integer.Sparse.eval_collectBalanced, rawRowCheck16375]

def rawRow16376 : Integer.Sparse Key := [(key2871, 4), (key2821, 4), (key2718, 4), (key2830, -4), (key2727, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2685, -4), (key2692, 12)]

theorem rawRowCheck16376 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form7 = rawRow16376 := by decide +kernel

def row16376 : Integer.Sparse Key := [(key2685, -4), (key2692, 8), (key2727, -4), (key2830, -4), (key2871, 4)]

theorem rowCheck16376 : row16376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16376 := by decide +kernel

theorem rowEval16376 (x : Key → ℝ) : Integer.Sparse.eval row16376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16376, Integer.Sparse.eval_collectBalanced, rawRowCheck16376]

def rawRow16377 : Integer.Sparse Key := [(key2727, 4), (key2830, 4), (key2871, 4), (key2692, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2685, 12)]

theorem rawRowCheck16377 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form7 = rawRow16377 := by decide +kernel

def row16377 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

theorem rowCheck16377 : row16377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16377 := by decide +kernel

theorem rowEval16377 (x : Key → ℝ) : Integer.Sparse.eval row16377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16377, Integer.Sparse.eval_collectBalanced, rawRowCheck16377]

def rawRow16378 : Integer.Sparse Key := [(key2727, 4), (key2871, 4), (key2830, 4), (key2718, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2685, 12)]

theorem rawRowCheck16378 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form7 = rawRow16378 := by decide +kernel

def row16378 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

theorem rowCheck16378 : row16378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16378 := by decide +kernel

theorem rowEval16378 (x : Key → ℝ) : Integer.Sparse.eval row16378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16378, Integer.Sparse.eval_collectBalanced, rawRowCheck16378]

def rawRow16379 : Integer.Sparse Key := [(key2830, 4), (key2727, 4), (key2871, 4), (key2692, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2685, 12)]

theorem rawRowCheck16379 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form7 = rawRow16379 := by decide +kernel

def row16379 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

theorem rowCheck16379 : row16379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16379 := by decide +kernel

theorem rowEval16379 (x : Key → ℝ) : Integer.Sparse.eval row16379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck16379, Integer.Sparse.eval_collectBalanced, rawRowCheck16379]

def rawRow16380 : Integer.Sparse Key := [(key2830, 4), (key2871, 4), (key2727, 4), (key2821, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2685, 12)]

theorem rawRowCheck16380 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form7 = rawRow16380 := by decide +kernel

def row16380 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

theorem rowCheck16380 : row16380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16380 := by decide +kernel

theorem rowEval16380 (x : Key → ℝ) : Integer.Sparse.eval row16380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16380, Integer.Sparse.eval_collectBalanced, rawRowCheck16380]

def rawRow16381 : Integer.Sparse Key := [(key2871, 4), (key2727, 4), (key2830, 4), (key2718, -4), (key2821, -4), (key2692, -4), (key2718, -4), (key2821, -4), (key2692, -4), (key2685, 12)]

theorem rawRowCheck16381 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form7 = rawRow16381 := by decide +kernel

def row16381 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

theorem rowCheck16381 : row16381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16381 := by decide +kernel

theorem rowEval16381 (x : Key → ℝ) : Integer.Sparse.eval row16381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck16381, Integer.Sparse.eval_collectBalanced, rawRowCheck16381]

def rawRow16382 : Integer.Sparse Key := [(key2871, 4), (key2830, 4), (key2727, 4), (key2821, -4), (key2718, -4), (key2692, -4), (key2821, -4), (key2718, -4), (key2692, -4), (key2685, 12)]

theorem rawRowCheck16382 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form7 = rawRow16382 := by decide +kernel

def row16382 : Integer.Sparse Key := [(key2685, 12), (key2692, -8), (key2718, -8), (key2727, 4), (key2821, -8), (key2830, 4), (key2871, 4)]

theorem rowCheck16382 : row16382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16382 := by decide +kernel

theorem rowEval16382 (x : Key → ℝ) : Integer.Sparse.eval row16382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck16382, Integer.Sparse.eval_collectBalanced, rawRowCheck16382]

def rawRow16383 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2773, 6), (key2847, -2), (key2847, -2), (key2969, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2594, -2), (key2881, -2), (key2881, -2), (key2890, 6), (key2601, -2), (key2911, -2), (key2911, -2)]

theorem rawRowCheck16383 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form8 = rawRow16383 := by decide +kernel

def row16383 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

theorem rowCheck16383 : row16383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16383 := by decide +kernel

theorem rowEval16383 (x : Key → ℝ) : Integer.Sparse.eval row16383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16383, Integer.Sparse.eval_collectBalanced, rawRowCheck16383]

end MUB6.Certificate.GramRows

end OAI
