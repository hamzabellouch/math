import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20224 : Integer.Sparse Key := [(key369, 6), (key352, 6), (key349, 6), (key352, 6), (key541, 6), (key509, 6), (key506, 6), (key677, 6), (key667, 6), (key541, 6), (key283, 6), (key506, 6), (key280, 6), (key667, 6), (key509, 6), (key283, 6), (key520, 6), (key671, 6), (key520, 6), (key292, 6)]

theorem rawRowCheck20224 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form10 = rawRow20224 := by decide +kernel

def row20224 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20224 : row20224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20224 := by decide +kernel

theorem rowEval20224 (x : Key → ℝ) : Integer.Sparse.eval row20224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20224, Integer.Sparse.eval_collectBalanced, rawRowCheck20224]

def rawRow20225 : Integer.Sparse Key := [(key352, 6), (key352, 6), (key369, 6), (key349, 6), (key667, 6), (key667, 6), (key677, 6), (key283, 6), (key283, 6), (key509, 6), (key509, 6), (key541, 6), (key541, 6), (key280, 6), (key506, 6), (key506, 6), (key671, 6), (key292, 6), (key520, 6), (key520, 6)]

theorem rawRowCheck20225 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form10 = rawRow20225 := by decide +kernel

def row20225 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20225 : row20225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20225 := by decide +kernel

theorem rowEval20225 (x : Key → ℝ) : Integer.Sparse.eval row20225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20225, Integer.Sparse.eval_collectBalanced, rawRowCheck20225]

def rawRow20226 : Integer.Sparse Key := [(key352, 6), (key369, 6), (key352, 6), (key349, 6), (key667, 6), (key677, 6), (key667, 6), (key509, 6), (key541, 6), (key283, 6), (key541, 6), (key283, 6), (key509, 6), (key506, 6), (key280, 6), (key506, 6), (key671, 6), (key520, 6), (key292, 6), (key520, 6)]

theorem rawRowCheck20226 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form10 = rawRow20226 := by decide +kernel

def row20226 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20226 : row20226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20226 := by decide +kernel

theorem rowEval20226 (x : Key → ℝ) : Integer.Sparse.eval row20226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20226, Integer.Sparse.eval_collectBalanced, rawRowCheck20226]

def rawRow20227 : Integer.Sparse Key := [(key369, 6), (key352, 6), (key352, 6), (key349, 6), (key677, 6), (key667, 6), (key667, 6), (key541, 6), (key509, 6), (key541, 6), (key283, 6), (key509, 6), (key283, 6), (key506, 6), (key506, 6), (key280, 6), (key671, 6), (key520, 6), (key520, 6), (key292, 6)]

theorem rawRowCheck20227 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form10 = rawRow20227 := by decide +kernel

def row20227 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20227 : row20227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20227 := by decide +kernel

theorem rowEval20227 (x : Key → ℝ) : Integer.Sparse.eval row20227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20227, Integer.Sparse.eval_collectBalanced, rawRowCheck20227]

def rawRow20228 : Integer.Sparse Key := [(key506, 6), (key509, 6), (key520, 6), (key541, 6), (key280, 6), (key283, 6), (key292, 6), (key349, 6), (key352, 6), (key506, 6), (key667, 6), (key520, 6), (key671, 6), (key369, 6), (key541, 6), (key677, 6), (key283, 6), (key352, 6), (key509, 6), (key667, 6)]

theorem rawRowCheck20228 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form10 = rawRow20228 := by decide +kernel

def row20228 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20228 : row20228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20228 := by decide +kernel

theorem rowEval20228 (x : Key → ℝ) : Integer.Sparse.eval row20228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20228, Integer.Sparse.eval_collectBalanced, rawRowCheck20228]

def rawRow20229 : Integer.Sparse Key := [(key509, 6), (key506, 6), (key520, 6), (key541, 6), (key283, 6), (key280, 6), (key292, 6), (key352, 6), (key349, 6), (key667, 6), (key506, 6), (key671, 6), (key520, 6), (key369, 6), (key677, 6), (key541, 6), (key283, 6), (key352, 6), (key667, 6), (key509, 6)]

theorem rawRowCheck20229 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form10 = rawRow20229 := by decide +kernel

def row20229 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20229 : row20229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20229 := by decide +kernel

theorem rowEval20229 (x : Key → ℝ) : Integer.Sparse.eval row20229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20229, Integer.Sparse.eval_collectBalanced, rawRowCheck20229]

def rawRow20230 : Integer.Sparse Key := [(key506, 6), (key520, 6), (key509, 6), (key541, 6), (key280, 6), (key292, 6), (key283, 6), (key506, 6), (key520, 6), (key349, 6), (key671, 6), (key352, 6), (key667, 6), (key541, 6), (key369, 6), (key677, 6), (key283, 6), (key509, 6), (key352, 6), (key667, 6)]

theorem rawRowCheck20230 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form10 = rawRow20230 := by decide +kernel

def row20230 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20230 : row20230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20230 := by decide +kernel

theorem rowEval20230 (x : Key → ℝ) : Integer.Sparse.eval row20230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20230, Integer.Sparse.eval_collectBalanced, rawRowCheck20230]

def rawRow20231 : Integer.Sparse Key := [(key520, 6), (key506, 6), (key509, 6), (key541, 6), (key292, 6), (key280, 6), (key283, 6), (key520, 6), (key506, 6), (key671, 6), (key349, 6), (key667, 6), (key352, 6), (key541, 6), (key677, 6), (key369, 6), (key283, 6), (key509, 6), (key667, 6), (key352, 6)]

theorem rawRowCheck20231 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form10 = rawRow20231 := by decide +kernel

def row20231 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20231 : row20231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20231 := by decide +kernel

theorem rowEval20231 (x : Key → ℝ) : Integer.Sparse.eval row20231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20231, Integer.Sparse.eval_collectBalanced, rawRowCheck20231]

def rawRow20232 : Integer.Sparse Key := [(key509, 6), (key520, 6), (key506, 6), (key541, 6), (key283, 6), (key292, 6), (key280, 6), (key667, 6), (key671, 6), (key352, 6), (key520, 6), (key349, 6), (key506, 6), (key677, 6), (key369, 6), (key541, 6), (key283, 6), (key667, 6), (key352, 6), (key509, 6)]

theorem rawRowCheck20232 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form10 = rawRow20232 := by decide +kernel

def row20232 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20232 : row20232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20232 := by decide +kernel

theorem rowEval20232 (x : Key → ℝ) : Integer.Sparse.eval row20232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20232, Integer.Sparse.eval_collectBalanced, rawRowCheck20232]

def rawRow20233 : Integer.Sparse Key := [(key520, 6), (key509, 6), (key506, 6), (key541, 6), (key292, 6), (key283, 6), (key280, 6), (key671, 6), (key667, 6), (key520, 6), (key352, 6), (key506, 6), (key349, 6), (key677, 6), (key541, 6), (key369, 6), (key283, 6), (key667, 6), (key509, 6), (key352, 6)]

theorem rawRowCheck20233 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form10 = rawRow20233 := by decide +kernel

def row20233 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20233 : row20233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20233 := by decide +kernel

theorem rowEval20233 (x : Key → ℝ) : Integer.Sparse.eval row20233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20233, Integer.Sparse.eval_collectBalanced, rawRowCheck20233]

def rawRow20234 : Integer.Sparse Key := [(key506, 6), (key509, 6), (key541, 6), (key520, 6), (key349, 6), (key352, 6), (key369, 6), (key280, 6), (key283, 6), (key506, 6), (key667, 6), (key541, 6), (key677, 6), (key292, 6), (key520, 6), (key671, 6), (key352, 6), (key283, 6), (key509, 6), (key667, 6)]

theorem rawRowCheck20234 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form10 = rawRow20234 := by decide +kernel

def row20234 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20234 : row20234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20234 := by decide +kernel

theorem rowEval20234 (x : Key → ℝ) : Integer.Sparse.eval row20234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20234, Integer.Sparse.eval_collectBalanced, rawRowCheck20234]

def rawRow20235 : Integer.Sparse Key := [(key509, 6), (key506, 6), (key541, 6), (key520, 6), (key352, 6), (key349, 6), (key369, 6), (key283, 6), (key280, 6), (key667, 6), (key506, 6), (key677, 6), (key541, 6), (key292, 6), (key671, 6), (key520, 6), (key352, 6), (key283, 6), (key667, 6), (key509, 6)]

theorem rawRowCheck20235 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form10 = rawRow20235 := by decide +kernel

def row20235 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20235 : row20235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20235 := by decide +kernel

theorem rowEval20235 (x : Key → ℝ) : Integer.Sparse.eval row20235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20235, Integer.Sparse.eval_collectBalanced, rawRowCheck20235]

def rawRow20236 : Integer.Sparse Key := [(key506, 6), (key541, 6), (key509, 6), (key520, 6), (key349, 6), (key369, 6), (key352, 6), (key506, 6), (key541, 6), (key280, 6), (key677, 6), (key283, 6), (key667, 6), (key520, 6), (key292, 6), (key671, 6), (key352, 6), (key509, 6), (key283, 6), (key667, 6)]

theorem rawRowCheck20236 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form10 = rawRow20236 := by decide +kernel

def row20236 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20236 : row20236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20236 := by decide +kernel

theorem rowEval20236 (x : Key → ℝ) : Integer.Sparse.eval row20236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20236, Integer.Sparse.eval_collectBalanced, rawRowCheck20236]

def rawRow20237 : Integer.Sparse Key := [(key541, 6), (key506, 6), (key509, 6), (key520, 6), (key369, 6), (key349, 6), (key352, 6), (key541, 6), (key506, 6), (key677, 6), (key280, 6), (key667, 6), (key283, 6), (key520, 6), (key671, 6), (key292, 6), (key352, 6), (key509, 6), (key667, 6), (key283, 6)]

theorem rawRowCheck20237 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form10 = rawRow20237 := by decide +kernel

def row20237 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20237 : row20237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20237 := by decide +kernel

theorem rowEval20237 (x : Key → ℝ) : Integer.Sparse.eval row20237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20237, Integer.Sparse.eval_collectBalanced, rawRowCheck20237]

def rawRow20238 : Integer.Sparse Key := [(key509, 6), (key541, 6), (key506, 6), (key520, 6), (key352, 6), (key369, 6), (key349, 6), (key667, 6), (key677, 6), (key283, 6), (key541, 6), (key280, 6), (key506, 6), (key671, 6), (key292, 6), (key520, 6), (key352, 6), (key667, 6), (key283, 6), (key509, 6)]

theorem rawRowCheck20238 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form10 = rawRow20238 := by decide +kernel

def row20238 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20238 : row20238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20238 := by decide +kernel

theorem rowEval20238 (x : Key → ℝ) : Integer.Sparse.eval row20238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20238, Integer.Sparse.eval_collectBalanced, rawRowCheck20238]

def rawRow20239 : Integer.Sparse Key := [(key541, 6), (key509, 6), (key506, 6), (key520, 6), (key369, 6), (key352, 6), (key349, 6), (key677, 6), (key667, 6), (key541, 6), (key283, 6), (key506, 6), (key280, 6), (key671, 6), (key520, 6), (key292, 6), (key352, 6), (key667, 6), (key509, 6), (key283, 6)]

theorem rawRowCheck20239 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form10 = rawRow20239 := by decide +kernel

def row20239 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20239 : row20239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20239 := by decide +kernel

theorem rowEval20239 (x : Key → ℝ) : Integer.Sparse.eval row20239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20239, Integer.Sparse.eval_collectBalanced, rawRowCheck20239]

def rawRow20240 : Integer.Sparse Key := [(key506, 6), (key520, 6), (key541, 6), (key509, 6), (key506, 6), (key520, 6), (key541, 6), (key280, 6), (key292, 6), (key349, 6), (key671, 6), (key369, 6), (key677, 6), (key283, 6), (key352, 6), (key667, 6), (key509, 6), (key283, 6), (key352, 6), (key667, 6)]

theorem rawRowCheck20240 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form10 = rawRow20240 := by decide +kernel

def row20240 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20240 : row20240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20240 := by decide +kernel

theorem rowEval20240 (x : Key → ℝ) : Integer.Sparse.eval row20240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20240, Integer.Sparse.eval_collectBalanced, rawRowCheck20240]

def rawRow20241 : Integer.Sparse Key := [(key520, 6), (key506, 6), (key541, 6), (key509, 6), (key520, 6), (key506, 6), (key541, 6), (key292, 6), (key280, 6), (key671, 6), (key349, 6), (key677, 6), (key369, 6), (key283, 6), (key667, 6), (key352, 6), (key509, 6), (key283, 6), (key667, 6), (key352, 6)]

theorem rawRowCheck20241 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form10 = rawRow20241 := by decide +kernel

def row20241 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20241 : row20241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20241 := by decide +kernel

theorem rowEval20241 (x : Key → ℝ) : Integer.Sparse.eval row20241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20241, Integer.Sparse.eval_collectBalanced, rawRowCheck20241]

def rawRow20242 : Integer.Sparse Key := [(key506, 6), (key541, 6), (key520, 6), (key509, 6), (key506, 6), (key541, 6), (key520, 6), (key349, 6), (key369, 6), (key280, 6), (key677, 6), (key292, 6), (key671, 6), (key352, 6), (key283, 6), (key667, 6), (key509, 6), (key352, 6), (key283, 6), (key667, 6)]

theorem rawRowCheck20242 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form10 = rawRow20242 := by decide +kernel

def row20242 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20242 : row20242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20242 := by decide +kernel

theorem rowEval20242 (x : Key → ℝ) : Integer.Sparse.eval row20242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20242, Integer.Sparse.eval_collectBalanced, rawRowCheck20242]

def rawRow20243 : Integer.Sparse Key := [(key541, 6), (key506, 6), (key520, 6), (key509, 6), (key541, 6), (key506, 6), (key520, 6), (key369, 6), (key349, 6), (key677, 6), (key280, 6), (key671, 6), (key292, 6), (key352, 6), (key667, 6), (key283, 6), (key509, 6), (key352, 6), (key667, 6), (key283, 6)]

theorem rawRowCheck20243 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form10 = rawRow20243 := by decide +kernel

def row20243 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20243 : row20243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20243 := by decide +kernel

theorem rowEval20243 (x : Key → ℝ) : Integer.Sparse.eval row20243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20243, Integer.Sparse.eval_collectBalanced, rawRowCheck20243]

def rawRow20244 : Integer.Sparse Key := [(key520, 6), (key541, 6), (key506, 6), (key509, 6), (key520, 6), (key541, 6), (key506, 6), (key671, 6), (key677, 6), (key292, 6), (key369, 6), (key280, 6), (key349, 6), (key667, 6), (key283, 6), (key352, 6), (key509, 6), (key667, 6), (key283, 6), (key352, 6)]

theorem rawRowCheck20244 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form10 = rawRow20244 := by decide +kernel

def row20244 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20244 : row20244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20244 := by decide +kernel

theorem rowEval20244 (x : Key → ℝ) : Integer.Sparse.eval row20244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20244, Integer.Sparse.eval_collectBalanced, rawRowCheck20244]

def rawRow20245 : Integer.Sparse Key := [(key541, 6), (key520, 6), (key506, 6), (key509, 6), (key541, 6), (key520, 6), (key506, 6), (key677, 6), (key671, 6), (key369, 6), (key292, 6), (key349, 6), (key280, 6), (key667, 6), (key352, 6), (key283, 6), (key509, 6), (key667, 6), (key352, 6), (key283, 6)]

theorem rawRowCheck20245 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form10 = rawRow20245 := by decide +kernel

def row20245 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20245 : row20245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20245 := by decide +kernel

theorem rowEval20245 (x : Key → ℝ) : Integer.Sparse.eval row20245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20245, Integer.Sparse.eval_collectBalanced, rawRowCheck20245]

def rawRow20246 : Integer.Sparse Key := [(key509, 6), (key520, 6), (key541, 6), (key506, 6), (key667, 6), (key671, 6), (key677, 6), (key283, 6), (key292, 6), (key352, 6), (key520, 6), (key369, 6), (key541, 6), (key280, 6), (key349, 6), (key506, 6), (key667, 6), (key283, 6), (key352, 6), (key509, 6)]

theorem rawRowCheck20246 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form10 = rawRow20246 := by decide +kernel

def row20246 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20246 : row20246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20246 := by decide +kernel

theorem rowEval20246 (x : Key → ℝ) : Integer.Sparse.eval row20246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20246, Integer.Sparse.eval_collectBalanced, rawRowCheck20246]

def rawRow20247 : Integer.Sparse Key := [(key520, 6), (key509, 6), (key541, 6), (key506, 6), (key671, 6), (key667, 6), (key677, 6), (key292, 6), (key283, 6), (key520, 6), (key352, 6), (key541, 6), (key369, 6), (key280, 6), (key506, 6), (key349, 6), (key667, 6), (key283, 6), (key509, 6), (key352, 6)]

theorem rawRowCheck20247 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form10 = rawRow20247 := by decide +kernel

def row20247 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20247 : row20247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20247 := by decide +kernel

theorem rowEval20247 (x : Key → ℝ) : Integer.Sparse.eval row20247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20247, Integer.Sparse.eval_collectBalanced, rawRowCheck20247]

def rawRow20248 : Integer.Sparse Key := [(key509, 6), (key541, 6), (key520, 6), (key506, 6), (key667, 6), (key677, 6), (key671, 6), (key352, 6), (key369, 6), (key283, 6), (key541, 6), (key292, 6), (key520, 6), (key349, 6), (key280, 6), (key506, 6), (key667, 6), (key352, 6), (key283, 6), (key509, 6)]

theorem rawRowCheck20248 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form10 = rawRow20248 := by decide +kernel

def row20248 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20248 : row20248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20248 := by decide +kernel

theorem rowEval20248 (x : Key → ℝ) : Integer.Sparse.eval row20248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20248, Integer.Sparse.eval_collectBalanced, rawRowCheck20248]

def rawRow20249 : Integer.Sparse Key := [(key541, 6), (key509, 6), (key520, 6), (key506, 6), (key677, 6), (key667, 6), (key671, 6), (key369, 6), (key352, 6), (key541, 6), (key283, 6), (key520, 6), (key292, 6), (key349, 6), (key506, 6), (key280, 6), (key667, 6), (key352, 6), (key509, 6), (key283, 6)]

theorem rawRowCheck20249 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form10 = rawRow20249 := by decide +kernel

def row20249 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20249 : row20249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20249 := by decide +kernel

theorem rowEval20249 (x : Key → ℝ) : Integer.Sparse.eval row20249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20249, Integer.Sparse.eval_collectBalanced, rawRowCheck20249]

def rawRow20250 : Integer.Sparse Key := [(key520, 6), (key541, 6), (key509, 6), (key506, 6), (key671, 6), (key677, 6), (key667, 6), (key520, 6), (key541, 6), (key292, 6), (key369, 6), (key283, 6), (key352, 6), (key506, 6), (key280, 6), (key349, 6), (key667, 6), (key509, 6), (key283, 6), (key352, 6)]

theorem rawRowCheck20250 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form10 = rawRow20250 := by decide +kernel

def row20250 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20250 : row20250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20250 := by decide +kernel

theorem rowEval20250 (x : Key → ℝ) : Integer.Sparse.eval row20250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20250, Integer.Sparse.eval_collectBalanced, rawRowCheck20250]

def rawRow20251 : Integer.Sparse Key := [(key541, 6), (key520, 6), (key509, 6), (key506, 6), (key677, 6), (key671, 6), (key667, 6), (key541, 6), (key520, 6), (key369, 6), (key292, 6), (key352, 6), (key283, 6), (key506, 6), (key349, 6), (key280, 6), (key667, 6), (key509, 6), (key352, 6), (key283, 6)]

theorem rawRowCheck20251 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form10 = rawRow20251 := by decide +kernel

def row20251 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20251 : row20251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20251 := by decide +kernel

theorem rowEval20251 (x : Key → ℝ) : Integer.Sparse.eval row20251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20251, Integer.Sparse.eval_collectBalanced, rawRowCheck20251]

def rawRow20252 : Integer.Sparse Key := [(key667, 6), (key667, 6), (key671, 6), (key677, 6), (key283, 6), (key283, 6), (key292, 6), (key352, 6), (key352, 6), (key509, 6), (key509, 6), (key520, 6), (key520, 6), (key369, 6), (key541, 6), (key541, 6), (key280, 6), (key349, 6), (key506, 6), (key506, 6)]

theorem rawRowCheck20252 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form10 = rawRow20252 := by decide +kernel

def row20252 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20252 : row20252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20252 := by decide +kernel

theorem rowEval20252 (x : Key → ℝ) : Integer.Sparse.eval row20252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20252, Integer.Sparse.eval_collectBalanced, rawRowCheck20252]

def rawRow20253 : Integer.Sparse Key := [(key667, 6), (key671, 6), (key667, 6), (key677, 6), (key283, 6), (key292, 6), (key283, 6), (key509, 6), (key520, 6), (key352, 6), (key520, 6), (key352, 6), (key509, 6), (key541, 6), (key369, 6), (key541, 6), (key280, 6), (key506, 6), (key349, 6), (key506, 6)]

theorem rawRowCheck20253 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form10 = rawRow20253 := by decide +kernel

def row20253 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20253 : row20253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20253 := by decide +kernel

theorem rowEval20253 (x : Key → ℝ) : Integer.Sparse.eval row20253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20253, Integer.Sparse.eval_collectBalanced, rawRowCheck20253]

def rawRow20254 : Integer.Sparse Key := [(key671, 6), (key667, 6), (key667, 6), (key677, 6), (key292, 6), (key283, 6), (key283, 6), (key520, 6), (key509, 6), (key520, 6), (key352, 6), (key509, 6), (key352, 6), (key541, 6), (key541, 6), (key369, 6), (key280, 6), (key506, 6), (key506, 6), (key349, 6)]

theorem rawRowCheck20254 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form10 = rawRow20254 := by decide +kernel

def row20254 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20254 : row20254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20254 := by decide +kernel

theorem rowEval20254 (x : Key → ℝ) : Integer.Sparse.eval row20254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20254, Integer.Sparse.eval_collectBalanced, rawRowCheck20254]

def rawRow20255 : Integer.Sparse Key := [(key667, 6), (key667, 6), (key677, 6), (key671, 6), (key352, 6), (key352, 6), (key369, 6), (key283, 6), (key283, 6), (key509, 6), (key509, 6), (key541, 6), (key541, 6), (key292, 6), (key520, 6), (key520, 6), (key349, 6), (key280, 6), (key506, 6), (key506, 6)]

theorem rawRowCheck20255 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form10 = rawRow20255 := by decide +kernel

def row20255 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20255 : row20255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20255 := by decide +kernel

theorem rowEval20255 (x : Key → ℝ) : Integer.Sparse.eval row20255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20255, Integer.Sparse.eval_collectBalanced, rawRowCheck20255]

def rawRow20256 : Integer.Sparse Key := [(key667, 6), (key677, 6), (key667, 6), (key671, 6), (key352, 6), (key369, 6), (key352, 6), (key509, 6), (key541, 6), (key283, 6), (key541, 6), (key283, 6), (key509, 6), (key520, 6), (key292, 6), (key520, 6), (key349, 6), (key506, 6), (key280, 6), (key506, 6)]

theorem rawRowCheck20256 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form10 = rawRow20256 := by decide +kernel

def row20256 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20256 : row20256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20256 := by decide +kernel

theorem rowEval20256 (x : Key → ℝ) : Integer.Sparse.eval row20256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20256, Integer.Sparse.eval_collectBalanced, rawRowCheck20256]

def rawRow20257 : Integer.Sparse Key := [(key677, 6), (key667, 6), (key667, 6), (key671, 6), (key369, 6), (key352, 6), (key352, 6), (key541, 6), (key509, 6), (key541, 6), (key283, 6), (key509, 6), (key283, 6), (key520, 6), (key520, 6), (key292, 6), (key349, 6), (key506, 6), (key506, 6), (key280, 6)]

theorem rawRowCheck20257 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form10 = rawRow20257 := by decide +kernel

def row20257 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20257 : row20257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20257 := by decide +kernel

theorem rowEval20257 (x : Key → ℝ) : Integer.Sparse.eval row20257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20257, Integer.Sparse.eval_collectBalanced, rawRowCheck20257]

def rawRow20258 : Integer.Sparse Key := [(key667, 6), (key671, 6), (key677, 6), (key667, 6), (key509, 6), (key520, 6), (key541, 6), (key283, 6), (key292, 6), (key352, 6), (key520, 6), (key369, 6), (key541, 6), (key283, 6), (key352, 6), (key509, 6), (key506, 6), (key280, 6), (key349, 6), (key506, 6)]

theorem rawRowCheck20258 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form10 = rawRow20258 := by decide +kernel

def row20258 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20258 : row20258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20258 := by decide +kernel

theorem rowEval20258 (x : Key → ℝ) : Integer.Sparse.eval row20258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20258, Integer.Sparse.eval_collectBalanced, rawRowCheck20258]

def rawRow20259 : Integer.Sparse Key := [(key671, 6), (key667, 6), (key677, 6), (key667, 6), (key520, 6), (key509, 6), (key541, 6), (key292, 6), (key283, 6), (key520, 6), (key352, 6), (key541, 6), (key369, 6), (key283, 6), (key509, 6), (key352, 6), (key506, 6), (key280, 6), (key506, 6), (key349, 6)]

theorem rawRowCheck20259 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form10 = rawRow20259 := by decide +kernel

def row20259 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20259 : row20259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20259 := by decide +kernel

theorem rowEval20259 (x : Key → ℝ) : Integer.Sparse.eval row20259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20259, Integer.Sparse.eval_collectBalanced, rawRowCheck20259]

def rawRow20260 : Integer.Sparse Key := [(key667, 6), (key677, 6), (key671, 6), (key667, 6), (key509, 6), (key541, 6), (key520, 6), (key352, 6), (key369, 6), (key283, 6), (key541, 6), (key292, 6), (key520, 6), (key352, 6), (key283, 6), (key509, 6), (key506, 6), (key349, 6), (key280, 6), (key506, 6)]

theorem rawRowCheck20260 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form10 = rawRow20260 := by decide +kernel

def row20260 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20260 : row20260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20260 := by decide +kernel

theorem rowEval20260 (x : Key → ℝ) : Integer.Sparse.eval row20260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20260, Integer.Sparse.eval_collectBalanced, rawRowCheck20260]

def rawRow20261 : Integer.Sparse Key := [(key677, 6), (key667, 6), (key671, 6), (key667, 6), (key541, 6), (key509, 6), (key520, 6), (key369, 6), (key352, 6), (key541, 6), (key283, 6), (key520, 6), (key292, 6), (key352, 6), (key509, 6), (key283, 6), (key506, 6), (key349, 6), (key506, 6), (key280, 6)]

theorem rawRowCheck20261 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form10 = rawRow20261 := by decide +kernel

def row20261 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20261 : row20261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20261 := by decide +kernel

theorem rowEval20261 (x : Key → ℝ) : Integer.Sparse.eval row20261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20261, Integer.Sparse.eval_collectBalanced, rawRowCheck20261]

def rawRow20262 : Integer.Sparse Key := [(key671, 6), (key677, 6), (key667, 6), (key667, 6), (key520, 6), (key541, 6), (key509, 6), (key520, 6), (key541, 6), (key292, 6), (key369, 6), (key283, 6), (key352, 6), (key509, 6), (key283, 6), (key352, 6), (key506, 6), (key506, 6), (key280, 6), (key349, 6)]

theorem rawRowCheck20262 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form10 = rawRow20262 := by decide +kernel

def row20262 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20262 : row20262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20262 := by decide +kernel

theorem rowEval20262 (x : Key → ℝ) : Integer.Sparse.eval row20262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20262, Integer.Sparse.eval_collectBalanced, rawRowCheck20262]

def rawRow20263 : Integer.Sparse Key := [(key677, 6), (key671, 6), (key667, 6), (key667, 6), (key541, 6), (key520, 6), (key509, 6), (key541, 6), (key520, 6), (key369, 6), (key292, 6), (key352, 6), (key283, 6), (key509, 6), (key352, 6), (key283, 6), (key506, 6), (key506, 6), (key349, 6), (key280, 6)]

theorem rawRowCheck20263 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form10 = rawRow20263 := by decide +kernel

def row20263 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20263 : row20263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20263 := by decide +kernel

theorem rowEval20263 (x : Key → ℝ) : Integer.Sparse.eval row20263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20263, Integer.Sparse.eval_collectBalanced, rawRowCheck20263]

def rawRow20264 : Integer.Sparse Key := [(key236, 2), (key241, 2), (key241, 2), (key248, 2), (key253, 2), (key248, 2), (key263, 2), (key253, 2), (key263, 2), (key277, 2), (key277, 2), (key278, 2), (key302, 2), (key307, 2), (key307, 2), (key316, 2), (key321, 2), (key316, 2), (key331, 2), (key321, 2), (key331, 2), (key346, 2), (key346, 2), (key347, 2), (key385, 2), (key390, 2), (key385, 2), (key400, 2), (key390, 2), (key400, 2), (key406, 2), (key411, 2), (key406, 2), (key421, 2), (key411, 2), (key421, 2), (key435, 2), (key445, 2), (key435, 2), (key453, 2), (key445, 2), (key453, 2), (key487, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key489, 2), (key655, 2), (key655, 2), (key656, 2), (key657, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key662, 2)]

theorem rawRowCheck20264 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form11 = rawRow20264 := by decide +kernel

def row20264 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20264 : row20264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20264 := by decide +kernel

theorem rowEval20264 (x : Key → ℝ) : Integer.Sparse.eval row20264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20264, Integer.Sparse.eval_collectBalanced, rawRowCheck20264]

def rawRow20265 : Integer.Sparse Key := [(key241, 2), (key236, 2), (key241, 2), (key253, 2), (key248, 2), (key263, 2), (key248, 2), (key263, 2), (key253, 2), (key277, 2), (key278, 2), (key277, 2), (key307, 2), (key302, 2), (key307, 2), (key321, 2), (key316, 2), (key331, 2), (key316, 2), (key331, 2), (key321, 2), (key346, 2), (key347, 2), (key346, 2), (key390, 2), (key385, 2), (key400, 2), (key385, 2), (key400, 2), (key390, 2), (key411, 2), (key406, 2), (key421, 2), (key406, 2), (key421, 2), (key411, 2), (key445, 2), (key435, 2), (key453, 2), (key435, 2), (key453, 2), (key445, 2), (key488, 2), (key487, 2), (key489, 2), (key487, 2), (key489, 2), (key488, 2), (key655, 2), (key656, 2), (key655, 2), (key657, 2), (key658, 2), (key657, 2), (key661, 2), (key660, 2), (key662, 2), (key660, 2), (key662, 2), (key661, 2)]

theorem rawRowCheck20265 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form11 = rawRow20265 := by decide +kernel

def row20265 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20265 : row20265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20265 := by decide +kernel

theorem rowEval20265 (x : Key → ℝ) : Integer.Sparse.eval row20265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20265, Integer.Sparse.eval_collectBalanced, rawRowCheck20265]

def rawRow20266 : Integer.Sparse Key := [(key241, 2), (key241, 2), (key236, 2), (key263, 2), (key263, 2), (key253, 2), (key253, 2), (key248, 2), (key248, 2), (key278, 2), (key277, 2), (key277, 2), (key307, 2), (key307, 2), (key302, 2), (key331, 2), (key331, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key347, 2), (key346, 2), (key346, 2), (key400, 2), (key400, 2), (key390, 2), (key390, 2), (key385, 2), (key385, 2), (key421, 2), (key421, 2), (key411, 2), (key411, 2), (key406, 2), (key406, 2), (key453, 2), (key453, 2), (key445, 2), (key445, 2), (key435, 2), (key435, 2), (key489, 2), (key489, 2), (key488, 2), (key488, 2), (key487, 2), (key487, 2), (key656, 2), (key655, 2), (key655, 2), (key658, 2), (key657, 2), (key657, 2), (key662, 2), (key662, 2), (key661, 2), (key661, 2), (key660, 2), (key660, 2)]

theorem rawRowCheck20266 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form11 = rawRow20266 := by decide +kernel

def row20266 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20266 : row20266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20266 := by decide +kernel

theorem rowEval20266 (x : Key → ℝ) : Integer.Sparse.eval row20266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20266, Integer.Sparse.eval_collectBalanced, rawRowCheck20266]

def rawRow20267 : Integer.Sparse Key := [(key248, 2), (key253, 2), (key263, 2), (key236, 2), (key241, 2), (key248, 2), (key263, 2), (key277, 2), (key278, 2), (key241, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key346, 2), (key302, 2), (key307, 2), (key316, 2), (key331, 2), (key346, 2), (key347, 2), (key307, 2), (key321, 2), (key331, 2), (key406, 2), (key411, 2), (key435, 2), (key445, 2), (key487, 2), (key488, 2), (key385, 2), (key390, 2), (key435, 2), (key453, 2), (key487, 2), (key489, 2), (key385, 2), (key400, 2), (key406, 2), (key421, 2), (key488, 2), (key489, 2), (key390, 2), (key400, 2), (key411, 2), (key421, 2), (key445, 2), (key453, 2), (key657, 2), (key660, 2), (key661, 2), (key655, 2), (key660, 2), (key662, 2), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key661, 2), (key662, 2)]

theorem rawRowCheck20267 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form11 = rawRow20267 := by decide +kernel

def row20267 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20267 : row20267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20267 := by decide +kernel

theorem rowEval20267 (x : Key → ℝ) : Integer.Sparse.eval row20267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20267, Integer.Sparse.eval_collectBalanced, rawRowCheck20267]

def rawRow20268 : Integer.Sparse Key := [(key253, 2), (key248, 2), (key263, 2), (key241, 2), (key236, 2), (key263, 2), (key248, 2), (key278, 2), (key277, 2), (key241, 2), (key263, 2), (key253, 2), (key321, 2), (key316, 2), (key346, 2), (key307, 2), (key302, 2), (key331, 2), (key316, 2), (key347, 2), (key346, 2), (key307, 2), (key331, 2), (key321, 2), (key411, 2), (key406, 2), (key445, 2), (key435, 2), (key488, 2), (key487, 2), (key390, 2), (key385, 2), (key453, 2), (key435, 2), (key489, 2), (key487, 2), (key400, 2), (key385, 2), (key421, 2), (key406, 2), (key489, 2), (key488, 2), (key400, 2), (key390, 2), (key421, 2), (key411, 2), (key453, 2), (key445, 2), (key657, 2), (key661, 2), (key660, 2), (key655, 2), (key662, 2), (key660, 2), (key656, 2), (key655, 2), (key658, 2), (key657, 2), (key662, 2), (key661, 2)]

theorem rawRowCheck20268 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form11 = rawRow20268 := by decide +kernel

def row20268 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20268 : row20268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20268 := by decide +kernel

theorem rowEval20268 (x : Key → ℝ) : Integer.Sparse.eval row20268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20268, Integer.Sparse.eval_collectBalanced, rawRowCheck20268]

def rawRow20269 : Integer.Sparse Key := [(key248, 2), (key263, 2), (key253, 2), (key248, 2), (key263, 2), (key236, 2), (key278, 2), (key241, 2), (key263, 2), (key253, 2), (key241, 2), (key263, 2), (key316, 2), (key346, 2), (key321, 2), (key316, 2), (key346, 2), (key302, 2), (key347, 2), (key307, 2), (key331, 2), (key321, 2), (key307, 2), (key331, 2), (key435, 2), (key487, 2), (key406, 2), (key488, 2), (key411, 2), (key445, 2), (key435, 2), (key487, 2), (key385, 2), (key489, 2), (key390, 2), (key453, 2), (key406, 2), (key488, 2), (key385, 2), (key489, 2), (key400, 2), (key421, 2), (key411, 2), (key445, 2), (key390, 2), (key453, 2), (key400, 2), (key421, 2), (key660, 2), (key657, 2), (key661, 2), (key660, 2), (key655, 2), (key662, 2), (key657, 2), (key661, 2), (key655, 2), (key662, 2), (key656, 2), (key658, 2)]

theorem rawRowCheck20269 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form11 = rawRow20269 := by decide +kernel

def row20269 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20269 : row20269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20269 := by decide +kernel

theorem rowEval20269 (x : Key → ℝ) : Integer.Sparse.eval row20269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20269, Integer.Sparse.eval_collectBalanced, rawRowCheck20269]

def rawRow20270 : Integer.Sparse Key := [(key263, 2), (key248, 2), (key253, 2), (key263, 2), (key248, 2), (key278, 2), (key236, 2), (key263, 2), (key241, 2), (key253, 2), (key263, 2), (key241, 2), (key346, 2), (key316, 2), (key321, 2), (key346, 2), (key316, 2), (key347, 2), (key302, 2), (key331, 2), (key307, 2), (key321, 2), (key331, 2), (key307, 2), (key487, 2), (key435, 2), (key488, 2), (key406, 2), (key445, 2), (key411, 2), (key487, 2), (key435, 2), (key489, 2), (key385, 2), (key453, 2), (key390, 2), (key488, 2), (key406, 2), (key489, 2), (key385, 2), (key421, 2), (key400, 2), (key445, 2), (key411, 2), (key453, 2), (key390, 2), (key421, 2), (key400, 2), (key660, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key655, 2), (key658, 2), (key656, 2)]

theorem rawRowCheck20270 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form11 = rawRow20270 := by decide +kernel

def row20270 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20270 : row20270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20270 := by decide +kernel

theorem rowEval20270 (x : Key → ℝ) : Integer.Sparse.eval row20270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20270, Integer.Sparse.eval_collectBalanced, rawRowCheck20270]

def rawRow20271 : Integer.Sparse Key := [(key253, 2), (key263, 2), (key248, 2), (key277, 2), (key278, 2), (key241, 2), (key263, 2), (key236, 2), (key248, 2), (key263, 2), (key241, 2), (key253, 2), (key321, 2), (key346, 2), (key316, 2), (key331, 2), (key347, 2), (key307, 2), (key346, 2), (key302, 2), (key316, 2), (key331, 2), (key307, 2), (key321, 2), (key445, 2), (key488, 2), (key411, 2), (key487, 2), (key406, 2), (key435, 2), (key453, 2), (key489, 2), (key390, 2), (key487, 2), (key385, 2), (key435, 2), (key421, 2), (key489, 2), (key400, 2), (key488, 2), (key385, 2), (key406, 2), (key421, 2), (key453, 2), (key400, 2), (key445, 2), (key390, 2), (key411, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key660, 2), (key658, 2), (key662, 2), (key656, 2), (key661, 2), (key655, 2), (key657, 2)]

theorem rawRowCheck20271 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form11 = rawRow20271 := by decide +kernel

def row20271 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20271 : row20271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20271 := by decide +kernel

theorem rowEval20271 (x : Key → ℝ) : Integer.Sparse.eval row20271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20271, Integer.Sparse.eval_collectBalanced, rawRowCheck20271]

def rawRow20272 : Integer.Sparse Key := [(key263, 2), (key253, 2), (key248, 2), (key278, 2), (key277, 2), (key263, 2), (key241, 2), (key248, 2), (key236, 2), (key263, 2), (key253, 2), (key241, 2), (key346, 2), (key321, 2), (key316, 2), (key347, 2), (key331, 2), (key346, 2), (key307, 2), (key316, 2), (key302, 2), (key331, 2), (key321, 2), (key307, 2), (key488, 2), (key445, 2), (key487, 2), (key411, 2), (key435, 2), (key406, 2), (key489, 2), (key453, 2), (key487, 2), (key390, 2), (key435, 2), (key385, 2), (key489, 2), (key421, 2), (key488, 2), (key400, 2), (key406, 2), (key385, 2), (key453, 2), (key421, 2), (key445, 2), (key400, 2), (key411, 2), (key390, 2), (key661, 2), (key660, 2), (key657, 2), (key662, 2), (key660, 2), (key655, 2), (key662, 2), (key658, 2), (key661, 2), (key656, 2), (key657, 2), (key655, 2)]

theorem rawRowCheck20272 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form11 = rawRow20272 := by decide +kernel

def row20272 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20272 : row20272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20272 := by decide +kernel

theorem rowEval20272 (x : Key → ℝ) : Integer.Sparse.eval row20272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20272, Integer.Sparse.eval_collectBalanced, rawRowCheck20272]

def rawRow20273 : Integer.Sparse Key := [(key277, 2), (key277, 2), (key278, 2), (key241, 2), (key241, 2), (key253, 2), (key253, 2), (key263, 2), (key263, 2), (key236, 2), (key248, 2), (key248, 2), (key331, 2), (key331, 2), (key347, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key346, 2), (key346, 2), (key302, 2), (key316, 2), (key316, 2), (key421, 2), (key421, 2), (key453, 2), (key453, 2), (key489, 2), (key489, 2), (key400, 2), (key400, 2), (key445, 2), (key445, 2), (key488, 2), (key488, 2), (key390, 2), (key390, 2), (key411, 2), (key411, 2), (key487, 2), (key487, 2), (key385, 2), (key385, 2), (key406, 2), (key406, 2), (key435, 2), (key435, 2), (key658, 2), (key662, 2), (key662, 2), (key656, 2), (key661, 2), (key661, 2), (key655, 2), (key655, 2), (key657, 2), (key657, 2), (key660, 2), (key660, 2)]

theorem rawRowCheck20273 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form11 = rawRow20273 := by decide +kernel

def row20273 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20273 : row20273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20273 := by decide +kernel

theorem rowEval20273 (x : Key → ℝ) : Integer.Sparse.eval row20273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20273, Integer.Sparse.eval_collectBalanced, rawRowCheck20273]

def rawRow20274 : Integer.Sparse Key := [(key277, 2), (key278, 2), (key277, 2), (key253, 2), (key263, 2), (key241, 2), (key263, 2), (key241, 2), (key253, 2), (key248, 2), (key236, 2), (key248, 2), (key331, 2), (key347, 2), (key331, 2), (key321, 2), (key346, 2), (key307, 2), (key346, 2), (key307, 2), (key321, 2), (key316, 2), (key302, 2), (key316, 2), (key453, 2), (key489, 2), (key421, 2), (key489, 2), (key421, 2), (key453, 2), (key445, 2), (key488, 2), (key400, 2), (key488, 2), (key400, 2), (key445, 2), (key411, 2), (key487, 2), (key390, 2), (key487, 2), (key390, 2), (key411, 2), (key406, 2), (key435, 2), (key385, 2), (key435, 2), (key385, 2), (key406, 2), (key662, 2), (key658, 2), (key662, 2), (key661, 2), (key656, 2), (key661, 2), (key657, 2), (key660, 2), (key655, 2), (key660, 2), (key655, 2), (key657, 2)]

theorem rawRowCheck20274 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form11 = rawRow20274 := by decide +kernel

def row20274 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20274 : row20274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20274 := by decide +kernel

theorem rowEval20274 (x : Key → ℝ) : Integer.Sparse.eval row20274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20274, Integer.Sparse.eval_collectBalanced, rawRowCheck20274]

def rawRow20275 : Integer.Sparse Key := [(key278, 2), (key277, 2), (key277, 2), (key263, 2), (key253, 2), (key263, 2), (key241, 2), (key253, 2), (key241, 2), (key248, 2), (key248, 2), (key236, 2), (key347, 2), (key331, 2), (key331, 2), (key346, 2), (key321, 2), (key346, 2), (key307, 2), (key321, 2), (key307, 2), (key316, 2), (key316, 2), (key302, 2), (key489, 2), (key453, 2), (key489, 2), (key421, 2), (key453, 2), (key421, 2), (key488, 2), (key445, 2), (key488, 2), (key400, 2), (key445, 2), (key400, 2), (key487, 2), (key411, 2), (key487, 2), (key390, 2), (key411, 2), (key390, 2), (key435, 2), (key406, 2), (key435, 2), (key385, 2), (key406, 2), (key385, 2), (key662, 2), (key662, 2), (key658, 2), (key661, 2), (key661, 2), (key656, 2), (key660, 2), (key657, 2), (key660, 2), (key655, 2), (key657, 2), (key655, 2)]

theorem rawRowCheck20275 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form11 = rawRow20275 := by decide +kernel

def row20275 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20275 : row20275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20275 := by decide +kernel

theorem rowEval20275 (x : Key → ℝ) : Integer.Sparse.eval row20275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20275, Integer.Sparse.eval_collectBalanced, rawRowCheck20275]

def rawRow20276 : Integer.Sparse Key := [(key302, 2), (key307, 2), (key307, 2), (key316, 2), (key321, 2), (key316, 2), (key346, 2), (key321, 2), (key346, 2), (key331, 2), (key331, 2), (key347, 2), (key236, 2), (key241, 2), (key241, 2), (key406, 2), (key411, 2), (key406, 2), (key421, 2), (key411, 2), (key421, 2), (key657, 2), (key657, 2), (key658, 2), (key248, 2), (key253, 2), (key248, 2), (key263, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key316, 2), (key331, 2), (key321, 2), (key331, 2), (key435, 2), (key445, 2), (key435, 2), (key453, 2), (key445, 2), (key453, 2), (key660, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key662, 2), (key277, 2), (key277, 2), (key278, 2), (key346, 2), (key346, 2), (key347, 2), (key487, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key489, 2)]

theorem rawRowCheck20276 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form11 = rawRow20276 := by decide +kernel

def row20276 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20276 : row20276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20276 := by decide +kernel

theorem rowEval20276 (x : Key → ℝ) : Integer.Sparse.eval row20276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20276, Integer.Sparse.eval_collectBalanced, rawRowCheck20276]

def rawRow20277 : Integer.Sparse Key := [(key307, 2), (key302, 2), (key307, 2), (key321, 2), (key316, 2), (key346, 2), (key316, 2), (key346, 2), (key321, 2), (key331, 2), (key347, 2), (key331, 2), (key241, 2), (key236, 2), (key241, 2), (key411, 2), (key406, 2), (key421, 2), (key406, 2), (key421, 2), (key411, 2), (key657, 2), (key658, 2), (key657, 2), (key253, 2), (key248, 2), (key263, 2), (key248, 2), (key263, 2), (key253, 2), (key321, 2), (key316, 2), (key331, 2), (key316, 2), (key331, 2), (key321, 2), (key445, 2), (key435, 2), (key453, 2), (key435, 2), (key453, 2), (key445, 2), (key661, 2), (key660, 2), (key662, 2), (key660, 2), (key662, 2), (key661, 2), (key277, 2), (key278, 2), (key277, 2), (key346, 2), (key347, 2), (key346, 2), (key488, 2), (key487, 2), (key489, 2), (key487, 2), (key489, 2), (key488, 2)]

theorem rawRowCheck20277 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form11 = rawRow20277 := by decide +kernel

def row20277 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20277 : row20277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20277 := by decide +kernel

theorem rowEval20277 (x : Key → ℝ) : Integer.Sparse.eval row20277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20277, Integer.Sparse.eval_collectBalanced, rawRowCheck20277]

def rawRow20278 : Integer.Sparse Key := [(key307, 2), (key307, 2), (key302, 2), (key346, 2), (key346, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key347, 2), (key331, 2), (key331, 2), (key241, 2), (key241, 2), (key236, 2), (key421, 2), (key421, 2), (key411, 2), (key411, 2), (key406, 2), (key406, 2), (key658, 2), (key657, 2), (key657, 2), (key263, 2), (key263, 2), (key253, 2), (key253, 2), (key248, 2), (key248, 2), (key331, 2), (key331, 2), (key321, 2), (key321, 2), (key316, 2), (key316, 2), (key453, 2), (key453, 2), (key445, 2), (key445, 2), (key435, 2), (key435, 2), (key662, 2), (key662, 2), (key661, 2), (key661, 2), (key660, 2), (key660, 2), (key278, 2), (key277, 2), (key277, 2), (key347, 2), (key346, 2), (key346, 2), (key489, 2), (key489, 2), (key488, 2), (key488, 2), (key487, 2), (key487, 2)]

theorem rawRowCheck20278 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form11 = rawRow20278 := by decide +kernel

def row20278 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20278 : row20278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20278 := by decide +kernel

theorem rowEval20278 (x : Key → ℝ) : Integer.Sparse.eval row20278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20278, Integer.Sparse.eval_collectBalanced, rawRowCheck20278]

def rawRow20279 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key302, 2), (key307, 2), (key316, 2), (key346, 2), (key331, 2), (key347, 2), (key307, 2), (key321, 2), (key346, 2), (key406, 2), (key411, 2), (key421, 2), (key236, 2), (key241, 2), (key406, 2), (key421, 2), (key657, 2), (key658, 2), (key241, 2), (key411, 2), (key421, 2), (key316, 2), (key321, 2), (key435, 2), (key445, 2), (key660, 2), (key661, 2), (key248, 2), (key253, 2), (key435, 2), (key453, 2), (key660, 2), (key662, 2), (key248, 2), (key263, 2), (key316, 2), (key331, 2), (key661, 2), (key662, 2), (key253, 2), (key263, 2), (key321, 2), (key331, 2), (key445, 2), (key453, 2), (key346, 2), (key487, 2), (key488, 2), (key277, 2), (key487, 2), (key489, 2), (key277, 2), (key278, 2), (key346, 2), (key347, 2), (key488, 2), (key489, 2)]

theorem rawRowCheck20279 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form11 = rawRow20279 := by decide +kernel

def row20279 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20279 : row20279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20279 := by decide +kernel

theorem rowEval20279 (x : Key → ℝ) : Integer.Sparse.eval row20279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20279, Integer.Sparse.eval_collectBalanced, rawRowCheck20279]

def rawRow20280 : Integer.Sparse Key := [(key321, 2), (key316, 2), (key331, 2), (key307, 2), (key302, 2), (key346, 2), (key316, 2), (key347, 2), (key331, 2), (key307, 2), (key346, 2), (key321, 2), (key411, 2), (key406, 2), (key421, 2), (key241, 2), (key236, 2), (key421, 2), (key406, 2), (key658, 2), (key657, 2), (key241, 2), (key421, 2), (key411, 2), (key321, 2), (key316, 2), (key445, 2), (key435, 2), (key661, 2), (key660, 2), (key253, 2), (key248, 2), (key453, 2), (key435, 2), (key662, 2), (key660, 2), (key263, 2), (key248, 2), (key331, 2), (key316, 2), (key662, 2), (key661, 2), (key263, 2), (key253, 2), (key331, 2), (key321, 2), (key453, 2), (key445, 2), (key346, 2), (key488, 2), (key487, 2), (key277, 2), (key489, 2), (key487, 2), (key278, 2), (key277, 2), (key347, 2), (key346, 2), (key489, 2), (key488, 2)]

theorem rawRowCheck20280 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form11 = rawRow20280 := by decide +kernel

def row20280 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20280 : row20280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20280 := by decide +kernel

theorem rowEval20280 (x : Key → ℝ) : Integer.Sparse.eval row20280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20280, Integer.Sparse.eval_collectBalanced, rawRowCheck20280]

def rawRow20281 : Integer.Sparse Key := [(key316, 2), (key331, 2), (key321, 2), (key316, 2), (key331, 2), (key302, 2), (key347, 2), (key307, 2), (key346, 2), (key321, 2), (key307, 2), (key346, 2), (key406, 2), (key421, 2), (key411, 2), (key406, 2), (key421, 2), (key236, 2), (key658, 2), (key241, 2), (key421, 2), (key411, 2), (key241, 2), (key421, 2), (key435, 2), (key660, 2), (key316, 2), (key661, 2), (key321, 2), (key445, 2), (key435, 2), (key660, 2), (key248, 2), (key662, 2), (key253, 2), (key453, 2), (key316, 2), (key661, 2), (key248, 2), (key662, 2), (key263, 2), (key331, 2), (key321, 2), (key445, 2), (key253, 2), (key453, 2), (key263, 2), (key331, 2), (key487, 2), (key346, 2), (key488, 2), (key487, 2), (key277, 2), (key489, 2), (key346, 2), (key488, 2), (key277, 2), (key489, 2), (key278, 2), (key347, 2)]

theorem rawRowCheck20281 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form11 = rawRow20281 := by decide +kernel

def row20281 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20281 : row20281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20281 := by decide +kernel

theorem rowEval20281 (x : Key → ℝ) : Integer.Sparse.eval row20281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20281, Integer.Sparse.eval_collectBalanced, rawRowCheck20281]

def rawRow20282 : Integer.Sparse Key := [(key331, 2), (key316, 2), (key321, 2), (key331, 2), (key316, 2), (key347, 2), (key302, 2), (key346, 2), (key307, 2), (key321, 2), (key346, 2), (key307, 2), (key421, 2), (key406, 2), (key411, 2), (key421, 2), (key406, 2), (key658, 2), (key236, 2), (key421, 2), (key241, 2), (key411, 2), (key421, 2), (key241, 2), (key660, 2), (key435, 2), (key661, 2), (key316, 2), (key445, 2), (key321, 2), (key660, 2), (key435, 2), (key662, 2), (key248, 2), (key453, 2), (key253, 2), (key661, 2), (key316, 2), (key662, 2), (key248, 2), (key331, 2), (key263, 2), (key445, 2), (key321, 2), (key453, 2), (key253, 2), (key331, 2), (key263, 2), (key487, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key277, 2), (key347, 2), (key278, 2)]

theorem rawRowCheck20282 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form11 = rawRow20282 := by decide +kernel

def row20282 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20282 : row20282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20282 := by decide +kernel

theorem rowEval20282 (x : Key → ℝ) : Integer.Sparse.eval row20282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20282, Integer.Sparse.eval_collectBalanced, rawRowCheck20282]

def rawRow20283 : Integer.Sparse Key := [(key321, 2), (key331, 2), (key316, 2), (key346, 2), (key347, 2), (key307, 2), (key331, 2), (key302, 2), (key316, 2), (key346, 2), (key307, 2), (key321, 2), (key411, 2), (key421, 2), (key406, 2), (key657, 2), (key658, 2), (key241, 2), (key421, 2), (key236, 2), (key406, 2), (key421, 2), (key241, 2), (key411, 2), (key445, 2), (key661, 2), (key321, 2), (key660, 2), (key316, 2), (key435, 2), (key453, 2), (key662, 2), (key253, 2), (key660, 2), (key248, 2), (key435, 2), (key331, 2), (key662, 2), (key263, 2), (key661, 2), (key248, 2), (key316, 2), (key331, 2), (key453, 2), (key263, 2), (key445, 2), (key253, 2), (key321, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key487, 2), (key347, 2), (key489, 2), (key278, 2), (key488, 2), (key277, 2), (key346, 2)]

theorem rawRowCheck20283 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form11 = rawRow20283 := by decide +kernel

def row20283 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20283 : row20283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20283 := by decide +kernel

theorem rowEval20283 (x : Key → ℝ) : Integer.Sparse.eval row20283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20283, Integer.Sparse.eval_collectBalanced, rawRowCheck20283]

def rawRow20284 : Integer.Sparse Key := [(key331, 2), (key321, 2), (key316, 2), (key347, 2), (key346, 2), (key331, 2), (key307, 2), (key316, 2), (key302, 2), (key346, 2), (key321, 2), (key307, 2), (key421, 2), (key411, 2), (key406, 2), (key658, 2), (key657, 2), (key421, 2), (key241, 2), (key406, 2), (key236, 2), (key421, 2), (key411, 2), (key241, 2), (key661, 2), (key445, 2), (key660, 2), (key321, 2), (key435, 2), (key316, 2), (key662, 2), (key453, 2), (key660, 2), (key253, 2), (key435, 2), (key248, 2), (key662, 2), (key331, 2), (key661, 2), (key263, 2), (key316, 2), (key248, 2), (key453, 2), (key331, 2), (key445, 2), (key263, 2), (key321, 2), (key253, 2), (key488, 2), (key487, 2), (key346, 2), (key489, 2), (key487, 2), (key277, 2), (key489, 2), (key347, 2), (key488, 2), (key278, 2), (key346, 2), (key277, 2)]

theorem rawRowCheck20284 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form11 = rawRow20284 := by decide +kernel

def row20284 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20284 : row20284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20284 := by decide +kernel

theorem rowEval20284 (x : Key → ℝ) : Integer.Sparse.eval row20284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20284, Integer.Sparse.eval_collectBalanced, rawRowCheck20284]

def rawRow20285 : Integer.Sparse Key := [(key346, 2), (key346, 2), (key347, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key331, 2), (key331, 2), (key302, 2), (key316, 2), (key316, 2), (key657, 2), (key657, 2), (key658, 2), (key241, 2), (key241, 2), (key411, 2), (key411, 2), (key421, 2), (key421, 2), (key236, 2), (key406, 2), (key406, 2), (key331, 2), (key331, 2), (key453, 2), (key453, 2), (key662, 2), (key662, 2), (key263, 2), (key263, 2), (key445, 2), (key445, 2), (key661, 2), (key661, 2), (key253, 2), (key253, 2), (key321, 2), (key321, 2), (key660, 2), (key660, 2), (key248, 2), (key248, 2), (key316, 2), (key316, 2), (key435, 2), (key435, 2), (key347, 2), (key489, 2), (key489, 2), (key278, 2), (key488, 2), (key488, 2), (key277, 2), (key277, 2), (key346, 2), (key346, 2), (key487, 2), (key487, 2)]

theorem rawRowCheck20285 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form11 = rawRow20285 := by decide +kernel

def row20285 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20285 : row20285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20285 := by decide +kernel

theorem rowEval20285 (x : Key → ℝ) : Integer.Sparse.eval row20285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20285, Integer.Sparse.eval_collectBalanced, rawRowCheck20285]

def rawRow20286 : Integer.Sparse Key := [(key346, 2), (key347, 2), (key346, 2), (key321, 2), (key331, 2), (key307, 2), (key331, 2), (key307, 2), (key321, 2), (key316, 2), (key302, 2), (key316, 2), (key657, 2), (key658, 2), (key657, 2), (key411, 2), (key421, 2), (key241, 2), (key421, 2), (key241, 2), (key411, 2), (key406, 2), (key236, 2), (key406, 2), (key453, 2), (key662, 2), (key331, 2), (key662, 2), (key331, 2), (key453, 2), (key445, 2), (key661, 2), (key263, 2), (key661, 2), (key263, 2), (key445, 2), (key321, 2), (key660, 2), (key253, 2), (key660, 2), (key253, 2), (key321, 2), (key316, 2), (key435, 2), (key248, 2), (key435, 2), (key248, 2), (key316, 2), (key489, 2), (key347, 2), (key489, 2), (key488, 2), (key278, 2), (key488, 2), (key346, 2), (key487, 2), (key277, 2), (key487, 2), (key277, 2), (key346, 2)]

theorem rawRowCheck20286 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form11 = rawRow20286 := by decide +kernel

def row20286 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20286 : row20286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20286 := by decide +kernel

theorem rowEval20286 (x : Key → ℝ) : Integer.Sparse.eval row20286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20286, Integer.Sparse.eval_collectBalanced, rawRowCheck20286]

def rawRow20287 : Integer.Sparse Key := [(key347, 2), (key346, 2), (key346, 2), (key331, 2), (key321, 2), (key331, 2), (key307, 2), (key321, 2), (key307, 2), (key316, 2), (key316, 2), (key302, 2), (key658, 2), (key657, 2), (key657, 2), (key421, 2), (key411, 2), (key421, 2), (key241, 2), (key411, 2), (key241, 2), (key406, 2), (key406, 2), (key236, 2), (key662, 2), (key453, 2), (key662, 2), (key331, 2), (key453, 2), (key331, 2), (key661, 2), (key445, 2), (key661, 2), (key263, 2), (key445, 2), (key263, 2), (key660, 2), (key321, 2), (key660, 2), (key253, 2), (key321, 2), (key253, 2), (key435, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key248, 2), (key489, 2), (key489, 2), (key347, 2), (key488, 2), (key488, 2), (key278, 2), (key487, 2), (key346, 2), (key487, 2), (key277, 2), (key346, 2), (key277, 2)]

theorem rawRowCheck20287 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form11 = rawRow20287 := by decide +kernel

def row20287 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 8), (key331, 8), (key346, 8), (key347, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20287 : row20287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20287 := by decide +kernel

theorem rowEval20287 (x : Key → ℝ) : Integer.Sparse.eval row20287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20287, Integer.Sparse.eval_collectBalanced, rawRowCheck20287]

def rawRow20288 : Integer.Sparse Key := [(key385, 2), (key390, 2), (key400, 2), (key406, 2), (key411, 2), (key435, 2), (key487, 2), (key445, 2), (key488, 2), (key421, 2), (key453, 2), (key489, 2), (key248, 2), (key253, 2), (key263, 2), (key316, 2), (key321, 2), (key435, 2), (key660, 2), (key445, 2), (key661, 2), (key331, 2), (key453, 2), (key662, 2), (key236, 2), (key241, 2), (key248, 2), (key263, 2), (key277, 2), (key278, 2), (key302, 2), (key307, 2), (key316, 2), (key331, 2), (key346, 2), (key347, 2), (key385, 2), (key400, 2), (key406, 2), (key421, 2), (key488, 2), (key489, 2), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key661, 2), (key662, 2), (key241, 2), (key253, 2), (key263, 2), (key307, 2), (key321, 2), (key331, 2), (key390, 2), (key400, 2), (key411, 2), (key421, 2), (key445, 2), (key453, 2)]

theorem rawRowCheck20288 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form11 = rawRow20288 := by decide +kernel

def row20288 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20288 : row20288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20288 := by decide +kernel

theorem rowEval20288 (x : Key → ℝ) : Integer.Sparse.eval row20288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20288, Integer.Sparse.eval_collectBalanced, rawRowCheck20288]

def rawRow20289 : Integer.Sparse Key := [(key390, 2), (key385, 2), (key400, 2), (key411, 2), (key406, 2), (key487, 2), (key435, 2), (key488, 2), (key445, 2), (key421, 2), (key489, 2), (key453, 2), (key253, 2), (key248, 2), (key263, 2), (key321, 2), (key316, 2), (key660, 2), (key435, 2), (key661, 2), (key445, 2), (key331, 2), (key662, 2), (key453, 2), (key241, 2), (key236, 2), (key263, 2), (key248, 2), (key278, 2), (key277, 2), (key307, 2), (key302, 2), (key331, 2), (key316, 2), (key347, 2), (key346, 2), (key400, 2), (key385, 2), (key421, 2), (key406, 2), (key489, 2), (key488, 2), (key656, 2), (key655, 2), (key658, 2), (key657, 2), (key662, 2), (key661, 2), (key241, 2), (key263, 2), (key253, 2), (key307, 2), (key331, 2), (key321, 2), (key400, 2), (key390, 2), (key421, 2), (key411, 2), (key453, 2), (key445, 2)]

theorem rawRowCheck20289 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form11 = rawRow20289 := by decide +kernel

def row20289 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20289 : row20289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20289 := by decide +kernel

theorem rowEval20289 (x : Key → ℝ) : Integer.Sparse.eval row20289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20289, Integer.Sparse.eval_collectBalanced, rawRowCheck20289]

def rawRow20290 : Integer.Sparse Key := [(key385, 2), (key400, 2), (key390, 2), (key435, 2), (key445, 2), (key406, 2), (key488, 2), (key411, 2), (key487, 2), (key453, 2), (key421, 2), (key489, 2), (key248, 2), (key263, 2), (key253, 2), (key435, 2), (key445, 2), (key316, 2), (key661, 2), (key321, 2), (key660, 2), (key453, 2), (key331, 2), (key662, 2), (key248, 2), (key263, 2), (key236, 2), (key278, 2), (key241, 2), (key263, 2), (key316, 2), (key346, 2), (key302, 2), (key347, 2), (key307, 2), (key331, 2), (key406, 2), (key488, 2), (key385, 2), (key489, 2), (key400, 2), (key421, 2), (key657, 2), (key661, 2), (key655, 2), (key662, 2), (key656, 2), (key658, 2), (key253, 2), (key241, 2), (key263, 2), (key321, 2), (key307, 2), (key331, 2), (key411, 2), (key445, 2), (key390, 2), (key453, 2), (key400, 2), (key421, 2)]

theorem rawRowCheck20290 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form11 = rawRow20290 := by decide +kernel

def row20290 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20290 : row20290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20290 := by decide +kernel

theorem rowEval20290 (x : Key → ℝ) : Integer.Sparse.eval row20290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20290, Integer.Sparse.eval_collectBalanced, rawRowCheck20290]

def rawRow20291 : Integer.Sparse Key := [(key400, 2), (key385, 2), (key390, 2), (key445, 2), (key435, 2), (key488, 2), (key406, 2), (key487, 2), (key411, 2), (key453, 2), (key489, 2), (key421, 2), (key263, 2), (key248, 2), (key253, 2), (key445, 2), (key435, 2), (key661, 2), (key316, 2), (key660, 2), (key321, 2), (key453, 2), (key662, 2), (key331, 2), (key263, 2), (key248, 2), (key278, 2), (key236, 2), (key263, 2), (key241, 2), (key346, 2), (key316, 2), (key347, 2), (key302, 2), (key331, 2), (key307, 2), (key488, 2), (key406, 2), (key489, 2), (key385, 2), (key421, 2), (key400, 2), (key661, 2), (key657, 2), (key662, 2), (key655, 2), (key658, 2), (key656, 2), (key253, 2), (key263, 2), (key241, 2), (key321, 2), (key331, 2), (key307, 2), (key445, 2), (key411, 2), (key453, 2), (key390, 2), (key421, 2), (key400, 2)]

theorem rawRowCheck20291 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form11 = rawRow20291 := by decide +kernel

def row20291 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20291 : row20291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20291 := by decide +kernel

theorem rowEval20291 (x : Key → ℝ) : Integer.Sparse.eval row20291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20291, Integer.Sparse.eval_collectBalanced, rawRowCheck20291]

def rawRow20292 : Integer.Sparse Key := [(key390, 2), (key400, 2), (key385, 2), (key487, 2), (key488, 2), (key411, 2), (key445, 2), (key406, 2), (key435, 2), (key489, 2), (key421, 2), (key453, 2), (key253, 2), (key263, 2), (key248, 2), (key660, 2), (key661, 2), (key321, 2), (key445, 2), (key316, 2), (key435, 2), (key662, 2), (key331, 2), (key453, 2), (key277, 2), (key278, 2), (key241, 2), (key263, 2), (key236, 2), (key248, 2), (key331, 2), (key347, 2), (key307, 2), (key346, 2), (key302, 2), (key316, 2), (key421, 2), (key489, 2), (key400, 2), (key488, 2), (key385, 2), (key406, 2), (key658, 2), (key662, 2), (key656, 2), (key661, 2), (key655, 2), (key657, 2), (key263, 2), (key241, 2), (key253, 2), (key331, 2), (key307, 2), (key321, 2), (key421, 2), (key453, 2), (key400, 2), (key445, 2), (key390, 2), (key411, 2)]

theorem rawRowCheck20292 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form11 = rawRow20292 := by decide +kernel

def row20292 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20292 : row20292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20292 := by decide +kernel

theorem rowEval20292 (x : Key → ℝ) : Integer.Sparse.eval row20292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20292, Integer.Sparse.eval_collectBalanced, rawRowCheck20292]

def rawRow20293 : Integer.Sparse Key := [(key400, 2), (key390, 2), (key385, 2), (key488, 2), (key487, 2), (key445, 2), (key411, 2), (key435, 2), (key406, 2), (key489, 2), (key453, 2), (key421, 2), (key263, 2), (key253, 2), (key248, 2), (key661, 2), (key660, 2), (key445, 2), (key321, 2), (key435, 2), (key316, 2), (key662, 2), (key453, 2), (key331, 2), (key278, 2), (key277, 2), (key263, 2), (key241, 2), (key248, 2), (key236, 2), (key347, 2), (key331, 2), (key346, 2), (key307, 2), (key316, 2), (key302, 2), (key489, 2), (key421, 2), (key488, 2), (key400, 2), (key406, 2), (key385, 2), (key662, 2), (key658, 2), (key661, 2), (key656, 2), (key657, 2), (key655, 2), (key263, 2), (key253, 2), (key241, 2), (key331, 2), (key321, 2), (key307, 2), (key453, 2), (key421, 2), (key445, 2), (key400, 2), (key411, 2), (key390, 2)]

theorem rawRowCheck20293 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form11 = rawRow20293 := by decide +kernel

def row20293 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20293 : row20293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20293 := by decide +kernel

theorem rowEval20293 (x : Key → ℝ) : Integer.Sparse.eval row20293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20293, Integer.Sparse.eval_collectBalanced, rawRowCheck20293]

def rawRow20294 : Integer.Sparse Key := [(key406, 2), (key411, 2), (key421, 2), (key385, 2), (key390, 2), (key435, 2), (key487, 2), (key453, 2), (key489, 2), (key400, 2), (key445, 2), (key488, 2), (key316, 2), (key321, 2), (key331, 2), (key248, 2), (key253, 2), (key435, 2), (key660, 2), (key453, 2), (key662, 2), (key263, 2), (key445, 2), (key661, 2), (key302, 2), (key307, 2), (key316, 2), (key346, 2), (key331, 2), (key347, 2), (key236, 2), (key241, 2), (key406, 2), (key421, 2), (key657, 2), (key658, 2), (key248, 2), (key263, 2), (key316, 2), (key331, 2), (key661, 2), (key662, 2), (key277, 2), (key278, 2), (key346, 2), (key347, 2), (key488, 2), (key489, 2), (key307, 2), (key390, 2), (key400, 2), (key241, 2), (key411, 2), (key421, 2), (key253, 2), (key263, 2), (key321, 2), (key331, 2), (key445, 2), (key453, 2)]

theorem rawRowCheck20294 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form11 = rawRow20294 := by decide +kernel

def row20294 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20294 : row20294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20294 := by decide +kernel

theorem rowEval20294 (x : Key → ℝ) : Integer.Sparse.eval row20294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20294, Integer.Sparse.eval_collectBalanced, rawRowCheck20294]

def rawRow20295 : Integer.Sparse Key := [(key411, 2), (key406, 2), (key421, 2), (key390, 2), (key385, 2), (key487, 2), (key435, 2), (key489, 2), (key453, 2), (key400, 2), (key488, 2), (key445, 2), (key321, 2), (key316, 2), (key331, 2), (key253, 2), (key248, 2), (key660, 2), (key435, 2), (key662, 2), (key453, 2), (key263, 2), (key661, 2), (key445, 2), (key307, 2), (key302, 2), (key346, 2), (key316, 2), (key347, 2), (key331, 2), (key241, 2), (key236, 2), (key421, 2), (key406, 2), (key658, 2), (key657, 2), (key263, 2), (key248, 2), (key331, 2), (key316, 2), (key662, 2), (key661, 2), (key278, 2), (key277, 2), (key347, 2), (key346, 2), (key489, 2), (key488, 2), (key307, 2), (key400, 2), (key390, 2), (key241, 2), (key421, 2), (key411, 2), (key263, 2), (key253, 2), (key331, 2), (key321, 2), (key453, 2), (key445, 2)]

theorem rawRowCheck20295 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form11 = rawRow20295 := by decide +kernel

def row20295 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20295 : row20295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20295 := by decide +kernel

theorem rowEval20295 (x : Key → ℝ) : Integer.Sparse.eval row20295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20295, Integer.Sparse.eval_collectBalanced, rawRowCheck20295]

def rawRow20296 : Integer.Sparse Key := [(key406, 2), (key421, 2), (key411, 2), (key435, 2), (key453, 2), (key385, 2), (key489, 2), (key390, 2), (key487, 2), (key445, 2), (key400, 2), (key488, 2), (key316, 2), (key331, 2), (key321, 2), (key435, 2), (key453, 2), (key248, 2), (key662, 2), (key253, 2), (key660, 2), (key445, 2), (key263, 2), (key661, 2), (key316, 2), (key331, 2), (key302, 2), (key347, 2), (key307, 2), (key346, 2), (key406, 2), (key421, 2), (key236, 2), (key658, 2), (key241, 2), (key421, 2), (key316, 2), (key661, 2), (key248, 2), (key662, 2), (key263, 2), (key331, 2), (key346, 2), (key488, 2), (key277, 2), (key489, 2), (key278, 2), (key347, 2), (key390, 2), (key307, 2), (key400, 2), (key411, 2), (key241, 2), (key421, 2), (key321, 2), (key445, 2), (key253, 2), (key453, 2), (key263, 2), (key331, 2)]

theorem rawRowCheck20296 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form11 = rawRow20296 := by decide +kernel

def row20296 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20296 : row20296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20296 := by decide +kernel

theorem rowEval20296 (x : Key → ℝ) : Integer.Sparse.eval row20296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20296, Integer.Sparse.eval_collectBalanced, rawRowCheck20296]

def rawRow20297 : Integer.Sparse Key := [(key421, 2), (key406, 2), (key411, 2), (key453, 2), (key435, 2), (key489, 2), (key385, 2), (key487, 2), (key390, 2), (key445, 2), (key488, 2), (key400, 2), (key331, 2), (key316, 2), (key321, 2), (key453, 2), (key435, 2), (key662, 2), (key248, 2), (key660, 2), (key253, 2), (key445, 2), (key661, 2), (key263, 2), (key331, 2), (key316, 2), (key347, 2), (key302, 2), (key346, 2), (key307, 2), (key421, 2), (key406, 2), (key658, 2), (key236, 2), (key421, 2), (key241, 2), (key661, 2), (key316, 2), (key662, 2), (key248, 2), (key331, 2), (key263, 2), (key488, 2), (key346, 2), (key489, 2), (key277, 2), (key347, 2), (key278, 2), (key390, 2), (key400, 2), (key307, 2), (key411, 2), (key421, 2), (key241, 2), (key445, 2), (key321, 2), (key453, 2), (key253, 2), (key331, 2), (key263, 2)]

theorem rawRowCheck20297 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form11 = rawRow20297 := by decide +kernel

def row20297 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20297 : row20297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20297 := by decide +kernel

theorem rowEval20297 (x : Key → ℝ) : Integer.Sparse.eval row20297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20297, Integer.Sparse.eval_collectBalanced, rawRowCheck20297]

def rawRow20298 : Integer.Sparse Key := [(key411, 2), (key421, 2), (key406, 2), (key487, 2), (key489, 2), (key390, 2), (key453, 2), (key385, 2), (key435, 2), (key488, 2), (key400, 2), (key445, 2), (key321, 2), (key331, 2), (key316, 2), (key660, 2), (key662, 2), (key253, 2), (key453, 2), (key248, 2), (key435, 2), (key661, 2), (key263, 2), (key445, 2), (key346, 2), (key347, 2), (key307, 2), (key331, 2), (key302, 2), (key316, 2), (key657, 2), (key658, 2), (key241, 2), (key421, 2), (key236, 2), (key406, 2), (key331, 2), (key662, 2), (key263, 2), (key661, 2), (key248, 2), (key316, 2), (key347, 2), (key489, 2), (key278, 2), (key488, 2), (key277, 2), (key346, 2), (key400, 2), (key307, 2), (key390, 2), (key421, 2), (key241, 2), (key411, 2), (key331, 2), (key453, 2), (key263, 2), (key445, 2), (key253, 2), (key321, 2)]

theorem rawRowCheck20298 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form11 = rawRow20298 := by decide +kernel

def row20298 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20298 : row20298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20298 := by decide +kernel

theorem rowEval20298 (x : Key → ℝ) : Integer.Sparse.eval row20298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20298, Integer.Sparse.eval_collectBalanced, rawRowCheck20298]

def rawRow20299 : Integer.Sparse Key := [(key421, 2), (key411, 2), (key406, 2), (key489, 2), (key487, 2), (key453, 2), (key390, 2), (key435, 2), (key385, 2), (key488, 2), (key445, 2), (key400, 2), (key331, 2), (key321, 2), (key316, 2), (key662, 2), (key660, 2), (key453, 2), (key253, 2), (key435, 2), (key248, 2), (key661, 2), (key445, 2), (key263, 2), (key347, 2), (key346, 2), (key331, 2), (key307, 2), (key316, 2), (key302, 2), (key658, 2), (key657, 2), (key421, 2), (key241, 2), (key406, 2), (key236, 2), (key662, 2), (key331, 2), (key661, 2), (key263, 2), (key316, 2), (key248, 2), (key489, 2), (key347, 2), (key488, 2), (key278, 2), (key346, 2), (key277, 2), (key400, 2), (key390, 2), (key307, 2), (key421, 2), (key411, 2), (key241, 2), (key453, 2), (key331, 2), (key445, 2), (key263, 2), (key321, 2), (key253, 2)]

theorem rawRowCheck20299 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form11 = rawRow20299 := by decide +kernel

def row20299 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 8), (key346, 4), (key347, 4), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20299 : row20299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20299 := by decide +kernel

theorem rowEval20299 (x : Key → ℝ) : Integer.Sparse.eval row20299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20299, Integer.Sparse.eval_collectBalanced, rawRowCheck20299]

def rawRow20300 : Integer.Sparse Key := [(key435, 2), (key445, 2), (key453, 2), (key385, 2), (key400, 2), (key406, 2), (key488, 2), (key421, 2), (key489, 2), (key390, 2), (key411, 2), (key487, 2), (key435, 2), (key445, 2), (key453, 2), (key248, 2), (key263, 2), (key316, 2), (key661, 2), (key331, 2), (key662, 2), (key253, 2), (key321, 2), (key660, 2), (key385, 2), (key400, 2), (key406, 2), (key488, 2), (key421, 2), (key489, 2), (key248, 2), (key263, 2), (key316, 2), (key661, 2), (key331, 2), (key662, 2), (key236, 2), (key278, 2), (key302, 2), (key347, 2), (key656, 2), (key658, 2), (key241, 2), (key263, 2), (key307, 2), (key331, 2), (key400, 2), (key421, 2), (key321, 2), (key411, 2), (key445, 2), (key253, 2), (key390, 2), (key453, 2), (key241, 2), (key263, 2), (key307, 2), (key331, 2), (key400, 2), (key421, 2)]

theorem rawRowCheck20300 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form11 = rawRow20300 := by decide +kernel

def row20300 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20300 : row20300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20300 := by decide +kernel

theorem rowEval20300 (x : Key → ℝ) : Integer.Sparse.eval row20300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20300, Integer.Sparse.eval_collectBalanced, rawRowCheck20300]

def rawRow20301 : Integer.Sparse Key := [(key445, 2), (key435, 2), (key453, 2), (key400, 2), (key385, 2), (key488, 2), (key406, 2), (key489, 2), (key421, 2), (key390, 2), (key487, 2), (key411, 2), (key445, 2), (key435, 2), (key453, 2), (key263, 2), (key248, 2), (key661, 2), (key316, 2), (key662, 2), (key331, 2), (key253, 2), (key660, 2), (key321, 2), (key400, 2), (key385, 2), (key488, 2), (key406, 2), (key489, 2), (key421, 2), (key263, 2), (key248, 2), (key661, 2), (key316, 2), (key662, 2), (key331, 2), (key278, 2), (key236, 2), (key347, 2), (key302, 2), (key658, 2), (key656, 2), (key263, 2), (key241, 2), (key331, 2), (key307, 2), (key421, 2), (key400, 2), (key321, 2), (key445, 2), (key411, 2), (key253, 2), (key453, 2), (key390, 2), (key263, 2), (key241, 2), (key331, 2), (key307, 2), (key421, 2), (key400, 2)]

theorem rawRowCheck20301 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form11 = rawRow20301 := by decide +kernel

def row20301 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20301 : row20301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20301 := by decide +kernel

theorem rowEval20301 (x : Key → ℝ) : Integer.Sparse.eval row20301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20301, Integer.Sparse.eval_collectBalanced, rawRowCheck20301]

def rawRow20302 : Integer.Sparse Key := [(key435, 2), (key453, 2), (key445, 2), (key406, 2), (key421, 2), (key385, 2), (key489, 2), (key400, 2), (key488, 2), (key411, 2), (key390, 2), (key487, 2), (key435, 2), (key453, 2), (key445, 2), (key316, 2), (key331, 2), (key248, 2), (key662, 2), (key263, 2), (key661, 2), (key321, 2), (key253, 2), (key660, 2), (key406, 2), (key421, 2), (key385, 2), (key489, 2), (key400, 2), (key488, 2), (key316, 2), (key331, 2), (key248, 2), (key662, 2), (key263, 2), (key661, 2), (key302, 2), (key347, 2), (key236, 2), (key658, 2), (key278, 2), (key347, 2), (key307, 2), (key400, 2), (key241, 2), (key421, 2), (key263, 2), (key331, 2), (key411, 2), (key321, 2), (key445, 2), (key390, 2), (key253, 2), (key453, 2), (key307, 2), (key400, 2), (key241, 2), (key421, 2), (key263, 2), (key331, 2)]

theorem rawRowCheck20302 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form11 = rawRow20302 := by decide +kernel

def row20302 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 4), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20302 : row20302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20302 := by decide +kernel

theorem rowEval20302 (x : Key → ℝ) : Integer.Sparse.eval row20302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20302, Integer.Sparse.eval_collectBalanced, rawRowCheck20302]

def rawRow20303 : Integer.Sparse Key := [(key453, 2), (key435, 2), (key445, 2), (key421, 2), (key406, 2), (key489, 2), (key385, 2), (key488, 2), (key400, 2), (key411, 2), (key487, 2), (key390, 2), (key453, 2), (key435, 2), (key445, 2), (key331, 2), (key316, 2), (key662, 2), (key248, 2), (key661, 2), (key263, 2), (key321, 2), (key660, 2), (key253, 2), (key421, 2), (key406, 2), (key489, 2), (key385, 2), (key488, 2), (key400, 2), (key331, 2), (key316, 2), (key662, 2), (key248, 2), (key661, 2), (key263, 2), (key347, 2), (key302, 2), (key658, 2), (key236, 2), (key347, 2), (key278, 2), (key400, 2), (key307, 2), (key421, 2), (key241, 2), (key331, 2), (key263, 2), (key411, 2), (key445, 2), (key321, 2), (key390, 2), (key453, 2), (key253, 2), (key400, 2), (key307, 2), (key421, 2), (key241, 2), (key331, 2), (key263, 2)]

theorem rawRowCheck20303 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form11 = rawRow20303 := by decide +kernel

def row20303 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 4), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20303 : row20303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20303 := by decide +kernel

theorem rowEval20303 (x : Key → ℝ) : Integer.Sparse.eval row20303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20303, Integer.Sparse.eval_collectBalanced, rawRowCheck20303]

def rawRow20304 : Integer.Sparse Key := [(key445, 2), (key453, 2), (key435, 2), (key488, 2), (key489, 2), (key400, 2), (key421, 2), (key385, 2), (key406, 2), (key487, 2), (key390, 2), (key411, 2), (key445, 2), (key453, 2), (key435, 2), (key661, 2), (key662, 2), (key263, 2), (key331, 2), (key248, 2), (key316, 2), (key660, 2), (key253, 2), (key321, 2), (key488, 2), (key489, 2), (key400, 2), (key421, 2), (key385, 2), (key406, 2), (key661, 2), (key662, 2), (key263, 2), (key331, 2), (key248, 2), (key316, 2), (key656, 2), (key658, 2), (key278, 2), (key347, 2), (key236, 2), (key302, 2), (key331, 2), (key421, 2), (key263, 2), (key400, 2), (key241, 2), (key307, 2), (key445, 2), (key321, 2), (key411, 2), (key453, 2), (key253, 2), (key390, 2), (key331, 2), (key421, 2), (key263, 2), (key400, 2), (key241, 2), (key307, 2)]

theorem rawRowCheck20304 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form11 = rawRow20304 := by decide +kernel

def row20304 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20304 : row20304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20304 := by decide +kernel

theorem rowEval20304 (x : Key → ℝ) : Integer.Sparse.eval row20304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20304, Integer.Sparse.eval_collectBalanced, rawRowCheck20304]

def rawRow20305 : Integer.Sparse Key := [(key453, 2), (key445, 2), (key435, 2), (key489, 2), (key488, 2), (key421, 2), (key400, 2), (key406, 2), (key385, 2), (key487, 2), (key411, 2), (key390, 2), (key453, 2), (key445, 2), (key435, 2), (key662, 2), (key661, 2), (key331, 2), (key263, 2), (key316, 2), (key248, 2), (key660, 2), (key321, 2), (key253, 2), (key489, 2), (key488, 2), (key421, 2), (key400, 2), (key406, 2), (key385, 2), (key662, 2), (key661, 2), (key331, 2), (key263, 2), (key316, 2), (key248, 2), (key658, 2), (key656, 2), (key347, 2), (key278, 2), (key302, 2), (key236, 2), (key421, 2), (key331, 2), (key400, 2), (key263, 2), (key307, 2), (key241, 2), (key445, 2), (key411, 2), (key321, 2), (key453, 2), (key390, 2), (key253, 2), (key421, 2), (key331, 2), (key400, 2), (key263, 2), (key307, 2), (key241, 2)]

theorem rawRowCheck20305 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form11 = rawRow20305 := by decide +kernel

def row20305 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20305 : row20305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20305 := by decide +kernel

theorem rowEval20305 (x : Key → ℝ) : Integer.Sparse.eval row20305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20305, Integer.Sparse.eval_collectBalanced, rawRowCheck20305]

def rawRow20306 : Integer.Sparse Key := [(key487, 2), (key488, 2), (key489, 2), (key390, 2), (key400, 2), (key411, 2), (key445, 2), (key421, 2), (key453, 2), (key385, 2), (key406, 2), (key435, 2), (key660, 2), (key661, 2), (key662, 2), (key253, 2), (key263, 2), (key321, 2), (key445, 2), (key331, 2), (key453, 2), (key248, 2), (key316, 2), (key435, 2), (key655, 2), (key656, 2), (key657, 2), (key661, 2), (key658, 2), (key662, 2), (key277, 2), (key278, 2), (key346, 2), (key488, 2), (key347, 2), (key489, 2), (key241, 2), (key263, 2), (key307, 2), (key400, 2), (key331, 2), (key421, 2), (key236, 2), (key248, 2), (key302, 2), (key316, 2), (key385, 2), (key406, 2), (key331, 2), (key421, 2), (key453, 2), (key263, 2), (key400, 2), (key445, 2), (key241, 2), (key253, 2), (key307, 2), (key321, 2), (key390, 2), (key411, 2)]

theorem rawRowCheck20306 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form11 = rawRow20306 := by decide +kernel

def row20306 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20306 : row20306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20306 := by decide +kernel

theorem rowEval20306 (x : Key → ℝ) : Integer.Sparse.eval row20306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20306, Integer.Sparse.eval_collectBalanced, rawRowCheck20306]

def rawRow20307 : Integer.Sparse Key := [(key488, 2), (key487, 2), (key489, 2), (key400, 2), (key390, 2), (key445, 2), (key411, 2), (key453, 2), (key421, 2), (key385, 2), (key435, 2), (key406, 2), (key661, 2), (key660, 2), (key662, 2), (key263, 2), (key253, 2), (key445, 2), (key321, 2), (key453, 2), (key331, 2), (key248, 2), (key435, 2), (key316, 2), (key656, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key658, 2), (key278, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key347, 2), (key263, 2), (key241, 2), (key400, 2), (key307, 2), (key421, 2), (key331, 2), (key248, 2), (key236, 2), (key316, 2), (key302, 2), (key406, 2), (key385, 2), (key331, 2), (key453, 2), (key421, 2), (key263, 2), (key445, 2), (key400, 2), (key253, 2), (key241, 2), (key321, 2), (key307, 2), (key411, 2), (key390, 2)]

theorem rawRowCheck20307 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form11 = rawRow20307 := by decide +kernel

def row20307 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20307 : row20307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20307 := by decide +kernel

theorem rowEval20307 (x : Key → ℝ) : Integer.Sparse.eval row20307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20307, Integer.Sparse.eval_collectBalanced, rawRowCheck20307]

def rawRow20308 : Integer.Sparse Key := [(key487, 2), (key489, 2), (key488, 2), (key411, 2), (key421, 2), (key390, 2), (key453, 2), (key400, 2), (key445, 2), (key406, 2), (key385, 2), (key435, 2), (key660, 2), (key662, 2), (key661, 2), (key321, 2), (key331, 2), (key253, 2), (key453, 2), (key263, 2), (key445, 2), (key316, 2), (key248, 2), (key435, 2), (key657, 2), (key658, 2), (key655, 2), (key662, 2), (key656, 2), (key661, 2), (key346, 2), (key347, 2), (key277, 2), (key489, 2), (key278, 2), (key488, 2), (key307, 2), (key331, 2), (key241, 2), (key421, 2), (key263, 2), (key400, 2), (key302, 2), (key316, 2), (key236, 2), (key406, 2), (key248, 2), (key316, 2), (key421, 2), (key331, 2), (key453, 2), (key400, 2), (key263, 2), (key445, 2), (key307, 2), (key390, 2), (key241, 2), (key411, 2), (key253, 2), (key321, 2)]

theorem rawRowCheck20308 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form11 = rawRow20308 := by decide +kernel

def row20308 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 2), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20308 : row20308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20308 := by decide +kernel

theorem rowEval20308 (x : Key → ℝ) : Integer.Sparse.eval row20308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20308, Integer.Sparse.eval_collectBalanced, rawRowCheck20308]

def rawRow20309 : Integer.Sparse Key := [(key489, 2), (key487, 2), (key488, 2), (key421, 2), (key411, 2), (key453, 2), (key390, 2), (key445, 2), (key400, 2), (key406, 2), (key435, 2), (key385, 2), (key662, 2), (key660, 2), (key661, 2), (key331, 2), (key321, 2), (key453, 2), (key253, 2), (key445, 2), (key263, 2), (key316, 2), (key435, 2), (key248, 2), (key658, 2), (key657, 2), (key662, 2), (key655, 2), (key661, 2), (key656, 2), (key347, 2), (key346, 2), (key489, 2), (key277, 2), (key488, 2), (key278, 2), (key331, 2), (key307, 2), (key421, 2), (key241, 2), (key400, 2), (key263, 2), (key316, 2), (key302, 2), (key406, 2), (key236, 2), (key316, 2), (key248, 2), (key421, 2), (key453, 2), (key331, 2), (key400, 2), (key445, 2), (key263, 2), (key390, 2), (key307, 2), (key411, 2), (key241, 2), (key321, 2), (key253, 2)]

theorem rawRowCheck20309 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form11 = rawRow20309 := by decide +kernel

def row20309 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 2), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20309 : row20309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20309 := by decide +kernel

theorem rowEval20309 (x : Key → ℝ) : Integer.Sparse.eval row20309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20309, Integer.Sparse.eval_collectBalanced, rawRowCheck20309]

def rawRow20310 : Integer.Sparse Key := [(key488, 2), (key489, 2), (key487, 2), (key445, 2), (key453, 2), (key400, 2), (key421, 2), (key390, 2), (key411, 2), (key435, 2), (key385, 2), (key406, 2), (key661, 2), (key662, 2), (key660, 2), (key445, 2), (key453, 2), (key263, 2), (key331, 2), (key253, 2), (key321, 2), (key435, 2), (key248, 2), (key316, 2), (key661, 2), (key662, 2), (key656, 2), (key658, 2), (key655, 2), (key657, 2), (key488, 2), (key489, 2), (key278, 2), (key347, 2), (key277, 2), (key346, 2), (key400, 2), (key421, 2), (key263, 2), (key331, 2), (key241, 2), (key307, 2), (key385, 2), (key406, 2), (key248, 2), (key316, 2), (key236, 2), (key302, 2), (key453, 2), (key331, 2), (key421, 2), (key445, 2), (key263, 2), (key400, 2), (key321, 2), (key411, 2), (key253, 2), (key390, 2), (key241, 2), (key307, 2)]

theorem rawRowCheck20310 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form11 = rawRow20310 := by decide +kernel

def row20310 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20310 : row20310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20310 := by decide +kernel

theorem rowEval20310 (x : Key → ℝ) : Integer.Sparse.eval row20310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20310, Integer.Sparse.eval_collectBalanced, rawRowCheck20310]

def rawRow20311 : Integer.Sparse Key := [(key489, 2), (key488, 2), (key487, 2), (key453, 2), (key445, 2), (key421, 2), (key400, 2), (key411, 2), (key390, 2), (key435, 2), (key406, 2), (key385, 2), (key662, 2), (key661, 2), (key660, 2), (key453, 2), (key445, 2), (key331, 2), (key263, 2), (key321, 2), (key253, 2), (key435, 2), (key316, 2), (key248, 2), (key662, 2), (key661, 2), (key658, 2), (key656, 2), (key657, 2), (key655, 2), (key489, 2), (key488, 2), (key347, 2), (key278, 2), (key346, 2), (key277, 2), (key421, 2), (key400, 2), (key331, 2), (key263, 2), (key307, 2), (key241, 2), (key406, 2), (key385, 2), (key316, 2), (key248, 2), (key302, 2), (key236, 2), (key453, 2), (key421, 2), (key331, 2), (key445, 2), (key400, 2), (key263, 2), (key411, 2), (key321, 2), (key390, 2), (key253, 2), (key307, 2), (key241, 2)]

theorem rawRowCheck20311 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form11 = rawRow20311 := by decide +kernel

def row20311 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

theorem rowCheck20311 : row20311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20311 := by decide +kernel

theorem rowEval20311 (x : Key → ℝ) : Integer.Sparse.eval row20311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20311, Integer.Sparse.eval_collectBalanced, rawRowCheck20311]

def rawRow20312 : Integer.Sparse Key := [(key655, 2), (key655, 2), (key656, 2), (key657, 2), (key657, 2), (key660, 2), (key660, 2), (key661, 2), (key661, 2), (key658, 2), (key662, 2), (key662, 2), (key277, 2), (key277, 2), (key278, 2), (key346, 2), (key346, 2), (key487, 2), (key487, 2), (key488, 2), (key488, 2), (key347, 2), (key489, 2), (key489, 2), (key241, 2), (key241, 2), (key253, 2), (key253, 2), (key263, 2), (key263, 2), (key307, 2), (key307, 2), (key390, 2), (key390, 2), (key400, 2), (key400, 2), (key321, 2), (key321, 2), (key411, 2), (key411, 2), (key445, 2), (key445, 2), (key331, 2), (key331, 2), (key421, 2), (key421, 2), (key453, 2), (key453, 2), (key236, 2), (key248, 2), (key248, 2), (key302, 2), (key316, 2), (key316, 2), (key385, 2), (key385, 2), (key406, 2), (key406, 2), (key435, 2), (key435, 2)]

theorem rawRowCheck20312 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form11 = rawRow20312 := by decide +kernel

def row20312 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20312 : row20312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20312 := by decide +kernel

theorem rowEval20312 (x : Key → ℝ) : Integer.Sparse.eval row20312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20312, Integer.Sparse.eval_collectBalanced, rawRowCheck20312]

def rawRow20313 : Integer.Sparse Key := [(key655, 2), (key656, 2), (key655, 2), (key660, 2), (key661, 2), (key657, 2), (key661, 2), (key657, 2), (key660, 2), (key662, 2), (key658, 2), (key662, 2), (key277, 2), (key278, 2), (key277, 2), (key487, 2), (key488, 2), (key346, 2), (key488, 2), (key346, 2), (key487, 2), (key489, 2), (key347, 2), (key489, 2), (key253, 2), (key263, 2), (key241, 2), (key263, 2), (key241, 2), (key253, 2), (key390, 2), (key400, 2), (key307, 2), (key400, 2), (key307, 2), (key390, 2), (key411, 2), (key445, 2), (key321, 2), (key445, 2), (key321, 2), (key411, 2), (key421, 2), (key453, 2), (key331, 2), (key453, 2), (key331, 2), (key421, 2), (key248, 2), (key236, 2), (key248, 2), (key316, 2), (key302, 2), (key316, 2), (key406, 2), (key435, 2), (key385, 2), (key435, 2), (key385, 2), (key406, 2)]

theorem rawRowCheck20313 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form11 = rawRow20313 := by decide +kernel

def row20313 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20313 : row20313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20313 := by decide +kernel

theorem rowEval20313 (x : Key → ℝ) : Integer.Sparse.eval row20313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20313, Integer.Sparse.eval_collectBalanced, rawRowCheck20313]

def rawRow20314 : Integer.Sparse Key := [(key656, 2), (key655, 2), (key655, 2), (key661, 2), (key660, 2), (key661, 2), (key657, 2), (key660, 2), (key657, 2), (key662, 2), (key662, 2), (key658, 2), (key278, 2), (key277, 2), (key277, 2), (key488, 2), (key487, 2), (key488, 2), (key346, 2), (key487, 2), (key346, 2), (key489, 2), (key489, 2), (key347, 2), (key263, 2), (key253, 2), (key263, 2), (key241, 2), (key253, 2), (key241, 2), (key400, 2), (key390, 2), (key400, 2), (key307, 2), (key390, 2), (key307, 2), (key445, 2), (key411, 2), (key445, 2), (key321, 2), (key411, 2), (key321, 2), (key453, 2), (key421, 2), (key453, 2), (key331, 2), (key421, 2), (key331, 2), (key248, 2), (key248, 2), (key236, 2), (key316, 2), (key316, 2), (key302, 2), (key435, 2), (key406, 2), (key435, 2), (key385, 2), (key406, 2), (key385, 2)]

theorem rawRowCheck20314 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form11 = rawRow20314 := by decide +kernel

def row20314 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20314 : row20314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20314 := by decide +kernel

theorem rowEval20314 (x : Key → ℝ) : Integer.Sparse.eval row20314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20314, Integer.Sparse.eval_collectBalanced, rawRowCheck20314]

def rawRow20315 : Integer.Sparse Key := [(key657, 2), (key657, 2), (key658, 2), (key655, 2), (key655, 2), (key660, 2), (key660, 2), (key662, 2), (key662, 2), (key656, 2), (key661, 2), (key661, 2), (key346, 2), (key346, 2), (key347, 2), (key277, 2), (key277, 2), (key487, 2), (key487, 2), (key489, 2), (key489, 2), (key278, 2), (key488, 2), (key488, 2), (key307, 2), (key307, 2), (key321, 2), (key321, 2), (key331, 2), (key331, 2), (key241, 2), (key241, 2), (key411, 2), (key411, 2), (key421, 2), (key421, 2), (key253, 2), (key253, 2), (key390, 2), (key390, 2), (key453, 2), (key453, 2), (key263, 2), (key263, 2), (key400, 2), (key400, 2), (key445, 2), (key445, 2), (key302, 2), (key316, 2), (key316, 2), (key236, 2), (key406, 2), (key406, 2), (key248, 2), (key248, 2), (key316, 2), (key316, 2), (key435, 2), (key435, 2)]

theorem rawRowCheck20315 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form11 = rawRow20315 := by decide +kernel

def row20315 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20315 : row20315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20315 := by decide +kernel

theorem rowEval20315 (x : Key → ℝ) : Integer.Sparse.eval row20315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20315, Integer.Sparse.eval_collectBalanced, rawRowCheck20315]

def rawRow20316 : Integer.Sparse Key := [(key657, 2), (key658, 2), (key657, 2), (key660, 2), (key662, 2), (key655, 2), (key662, 2), (key655, 2), (key660, 2), (key661, 2), (key656, 2), (key661, 2), (key346, 2), (key347, 2), (key346, 2), (key487, 2), (key489, 2), (key277, 2), (key489, 2), (key277, 2), (key487, 2), (key488, 2), (key278, 2), (key488, 2), (key321, 2), (key331, 2), (key307, 2), (key331, 2), (key307, 2), (key321, 2), (key411, 2), (key421, 2), (key241, 2), (key421, 2), (key241, 2), (key411, 2), (key390, 2), (key453, 2), (key253, 2), (key453, 2), (key253, 2), (key390, 2), (key400, 2), (key445, 2), (key263, 2), (key445, 2), (key263, 2), (key400, 2), (key316, 2), (key302, 2), (key316, 2), (key406, 2), (key236, 2), (key406, 2), (key316, 2), (key435, 2), (key248, 2), (key435, 2), (key248, 2), (key316, 2)]

theorem rawRowCheck20316 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form11 = rawRow20316 := by decide +kernel

def row20316 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20316 : row20316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20316 := by decide +kernel

theorem rowEval20316 (x : Key → ℝ) : Integer.Sparse.eval row20316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20316, Integer.Sparse.eval_collectBalanced, rawRowCheck20316]

def rawRow20317 : Integer.Sparse Key := [(key658, 2), (key657, 2), (key657, 2), (key662, 2), (key660, 2), (key662, 2), (key655, 2), (key660, 2), (key655, 2), (key661, 2), (key661, 2), (key656, 2), (key347, 2), (key346, 2), (key346, 2), (key489, 2), (key487, 2), (key489, 2), (key277, 2), (key487, 2), (key277, 2), (key488, 2), (key488, 2), (key278, 2), (key331, 2), (key321, 2), (key331, 2), (key307, 2), (key321, 2), (key307, 2), (key421, 2), (key411, 2), (key421, 2), (key241, 2), (key411, 2), (key241, 2), (key453, 2), (key390, 2), (key453, 2), (key253, 2), (key390, 2), (key253, 2), (key445, 2), (key400, 2), (key445, 2), (key263, 2), (key400, 2), (key263, 2), (key316, 2), (key316, 2), (key302, 2), (key406, 2), (key406, 2), (key236, 2), (key435, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key248, 2)]

theorem rawRowCheck20317 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form11 = rawRow20317 := by decide +kernel

def row20317 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20317 : row20317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20317 := by decide +kernel

theorem rowEval20317 (x : Key → ℝ) : Integer.Sparse.eval row20317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20317, Integer.Sparse.eval_collectBalanced, rawRowCheck20317]

def rawRow20318 : Integer.Sparse Key := [(key660, 2), (key661, 2), (key662, 2), (key655, 2), (key656, 2), (key657, 2), (key661, 2), (key658, 2), (key662, 2), (key655, 2), (key657, 2), (key660, 2), (key487, 2), (key488, 2), (key489, 2), (key277, 2), (key278, 2), (key346, 2), (key488, 2), (key347, 2), (key489, 2), (key277, 2), (key346, 2), (key487, 2), (key390, 2), (key400, 2), (key411, 2), (key445, 2), (key421, 2), (key453, 2), (key253, 2), (key263, 2), (key321, 2), (key445, 2), (key331, 2), (key453, 2), (key241, 2), (key263, 2), (key307, 2), (key400, 2), (key331, 2), (key421, 2), (key241, 2), (key253, 2), (key307, 2), (key390, 2), (key321, 2), (key411, 2), (key385, 2), (key406, 2), (key435, 2), (key248, 2), (key316, 2), (key435, 2), (key236, 2), (key248, 2), (key302, 2), (key316, 2), (key385, 2), (key406, 2)]

theorem rawRowCheck20318 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form11 = rawRow20318 := by decide +kernel

def row20318 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20318 : row20318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20318 := by decide +kernel

theorem rowEval20318 (x : Key → ℝ) : Integer.Sparse.eval row20318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20318, Integer.Sparse.eval_collectBalanced, rawRowCheck20318]

def rawRow20319 : Integer.Sparse Key := [(key661, 2), (key660, 2), (key662, 2), (key656, 2), (key655, 2), (key661, 2), (key657, 2), (key662, 2), (key658, 2), (key655, 2), (key660, 2), (key657, 2), (key488, 2), (key487, 2), (key489, 2), (key278, 2), (key277, 2), (key488, 2), (key346, 2), (key489, 2), (key347, 2), (key277, 2), (key487, 2), (key346, 2), (key400, 2), (key390, 2), (key445, 2), (key411, 2), (key453, 2), (key421, 2), (key263, 2), (key253, 2), (key445, 2), (key321, 2), (key453, 2), (key331, 2), (key263, 2), (key241, 2), (key400, 2), (key307, 2), (key421, 2), (key331, 2), (key253, 2), (key241, 2), (key390, 2), (key307, 2), (key411, 2), (key321, 2), (key385, 2), (key435, 2), (key406, 2), (key248, 2), (key435, 2), (key316, 2), (key248, 2), (key236, 2), (key316, 2), (key302, 2), (key406, 2), (key385, 2)]

theorem rawRowCheck20319 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form11 = rawRow20319 := by decide +kernel

def row20319 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20319 : row20319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20319 := by decide +kernel

theorem rowEval20319 (x : Key → ℝ) : Integer.Sparse.eval row20319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20319, Integer.Sparse.eval_collectBalanced, rawRowCheck20319]

def rawRow20320 : Integer.Sparse Key := [(key660, 2), (key662, 2), (key661, 2), (key657, 2), (key658, 2), (key655, 2), (key662, 2), (key656, 2), (key661, 2), (key657, 2), (key655, 2), (key660, 2), (key487, 2), (key489, 2), (key488, 2), (key346, 2), (key347, 2), (key277, 2), (key489, 2), (key278, 2), (key488, 2), (key346, 2), (key277, 2), (key487, 2), (key411, 2), (key421, 2), (key390, 2), (key453, 2), (key400, 2), (key445, 2), (key321, 2), (key331, 2), (key253, 2), (key453, 2), (key263, 2), (key445, 2), (key307, 2), (key331, 2), (key241, 2), (key421, 2), (key263, 2), (key400, 2), (key307, 2), (key321, 2), (key241, 2), (key411, 2), (key253, 2), (key390, 2), (key406, 2), (key385, 2), (key435, 2), (key316, 2), (key248, 2), (key435, 2), (key302, 2), (key316, 2), (key236, 2), (key406, 2), (key248, 2), (key316, 2)]

theorem rawRowCheck20320 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form11 = rawRow20320 := by decide +kernel

def row20320 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20320 : row20320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20320 := by decide +kernel

theorem rowEval20320 (x : Key → ℝ) : Integer.Sparse.eval row20320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form11) x := by
  rw [rowCheck20320, Integer.Sparse.eval_collectBalanced, rawRowCheck20320]

def rawRow20321 : Integer.Sparse Key := [(key662, 2), (key660, 2), (key661, 2), (key658, 2), (key657, 2), (key662, 2), (key655, 2), (key661, 2), (key656, 2), (key657, 2), (key660, 2), (key655, 2), (key489, 2), (key487, 2), (key488, 2), (key347, 2), (key346, 2), (key489, 2), (key277, 2), (key488, 2), (key278, 2), (key346, 2), (key487, 2), (key277, 2), (key421, 2), (key411, 2), (key453, 2), (key390, 2), (key445, 2), (key400, 2), (key331, 2), (key321, 2), (key453, 2), (key253, 2), (key445, 2), (key263, 2), (key331, 2), (key307, 2), (key421, 2), (key241, 2), (key400, 2), (key263, 2), (key321, 2), (key307, 2), (key411, 2), (key241, 2), (key390, 2), (key253, 2), (key406, 2), (key435, 2), (key385, 2), (key316, 2), (key435, 2), (key248, 2), (key316, 2), (key302, 2), (key406, 2), (key236, 2), (key316, 2), (key248, 2)]

theorem rawRowCheck20321 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form11 = rawRow20321 := by decide +kernel

def row20321 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20321 : row20321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20321 := by decide +kernel

theorem rowEval20321 (x : Key → ℝ) : Integer.Sparse.eval row20321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20321, Integer.Sparse.eval_collectBalanced, rawRowCheck20321]

def rawRow20322 : Integer.Sparse Key := [(key661, 2), (key662, 2), (key660, 2), (key661, 2), (key662, 2), (key656, 2), (key658, 2), (key655, 2), (key657, 2), (key660, 2), (key655, 2), (key657, 2), (key488, 2), (key489, 2), (key487, 2), (key488, 2), (key489, 2), (key278, 2), (key347, 2), (key277, 2), (key346, 2), (key487, 2), (key277, 2), (key346, 2), (key445, 2), (key453, 2), (key400, 2), (key421, 2), (key390, 2), (key411, 2), (key445, 2), (key453, 2), (key263, 2), (key331, 2), (key253, 2), (key321, 2), (key400, 2), (key421, 2), (key263, 2), (key331, 2), (key241, 2), (key307, 2), (key390, 2), (key411, 2), (key253, 2), (key321, 2), (key241, 2), (key307, 2), (key435, 2), (key385, 2), (key406, 2), (key435, 2), (key248, 2), (key316, 2), (key385, 2), (key406, 2), (key248, 2), (key316, 2), (key236, 2), (key302, 2)]

theorem rawRowCheck20322 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form11 = rawRow20322 := by decide +kernel

def row20322 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20322 : row20322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20322 := by decide +kernel

theorem rowEval20322 (x : Key → ℝ) : Integer.Sparse.eval row20322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form11) x := by
  rw [rowCheck20322, Integer.Sparse.eval_collectBalanced, rawRowCheck20322]

def rawRow20323 : Integer.Sparse Key := [(key662, 2), (key661, 2), (key660, 2), (key662, 2), (key661, 2), (key658, 2), (key656, 2), (key657, 2), (key655, 2), (key660, 2), (key657, 2), (key655, 2), (key489, 2), (key488, 2), (key487, 2), (key489, 2), (key488, 2), (key347, 2), (key278, 2), (key346, 2), (key277, 2), (key487, 2), (key346, 2), (key277, 2), (key453, 2), (key445, 2), (key421, 2), (key400, 2), (key411, 2), (key390, 2), (key453, 2), (key445, 2), (key331, 2), (key263, 2), (key321, 2), (key253, 2), (key421, 2), (key400, 2), (key331, 2), (key263, 2), (key307, 2), (key241, 2), (key411, 2), (key390, 2), (key321, 2), (key253, 2), (key307, 2), (key241, 2), (key435, 2), (key406, 2), (key385, 2), (key435, 2), (key316, 2), (key248, 2), (key406, 2), (key385, 2), (key316, 2), (key248, 2), (key302, 2), (key236, 2)]

theorem rawRowCheck20323 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form11 = rawRow20323 := by decide +kernel

def row20323 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

theorem rowCheck20323 : row20323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20323 := by decide +kernel

theorem rowEval20323 (x : Key → ℝ) : Integer.Sparse.eval row20323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form11) x := by
  rw [rowCheck20323, Integer.Sparse.eval_collectBalanced, rawRowCheck20323]

end MUB6.Certificate.GramRows

end OAI
