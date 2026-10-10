import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
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

def rawRow4096 : Integer.Sparse Key := [(key830, -2), (key840, -2), (key831, -2), (key831, 6), (key924, 2), (key935, 2), (key925, 2), (key925, -2), (key747, -2), (key960, -2), (key928, -6), (key928, 2), (key751, 2), (key962, 2)]

theorem rawRowCheck4096 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form13 = rawRow4096 := by decide +kernel

def row4096 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

theorem rowCheck4096 : row4096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4096 := by decide +kernel

theorem rowEval4096 (x : Key → ℝ) : Integer.Sparse.eval row4096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4096, Integer.Sparse.eval_collectBalanced, rawRowCheck4096]

def rawRow4097 : Integer.Sparse Key := [(key840, -2), (key830, -2), (key831, -2), (key831, 6), (key935, 2), (key924, 2), (key925, 2), (key925, -2), (key960, -2), (key747, -2), (key928, -6), (key928, 2), (key962, 2), (key751, 2)]

theorem rawRowCheck4097 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form13 = rawRow4097 := by decide +kernel

def row4097 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

theorem rowCheck4097 : row4097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4097 := by decide +kernel

theorem rowEval4097 (x : Key → ℝ) : Integer.Sparse.eval row4097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4097, Integer.Sparse.eval_collectBalanced, rawRowCheck4097]

def rawRow4098 : Integer.Sparse Key := [(key831, -2), (key840, -2), (key830, -2), (key831, 6), (key925, 2), (key935, 2), (key924, 2), (key960, -2), (key747, -2), (key925, -2), (key928, -6), (key962, 2), (key751, 2), (key928, 2)]

theorem rawRowCheck4098 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form13 = rawRow4098 := by decide +kernel

def row4098 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

theorem rowCheck4098 : row4098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4098 := by decide +kernel

theorem rowEval4098 (x : Key → ℝ) : Integer.Sparse.eval row4098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4098, Integer.Sparse.eval_collectBalanced, rawRowCheck4098]

def rawRow4099 : Integer.Sparse Key := [(key840, -2), (key831, -2), (key830, -2), (key831, 6), (key935, 2), (key925, 2), (key924, 2), (key960, -2), (key925, -2), (key747, -2), (key928, -6), (key962, 2), (key928, 2), (key751, 2)]

theorem rawRowCheck4099 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form13 = rawRow4099 := by decide +kernel

def row4099 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

theorem rowCheck4099 : row4099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4099 := by decide +kernel

theorem rowEval4099 (x : Key → ℝ) : Integer.Sparse.eval row4099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4099, Integer.Sparse.eval_collectBalanced, rawRowCheck4099]

def rawRow4100 : Integer.Sparse Key := [(key831, -2), (key831, -2), (key840, -2), (key830, 6), (key960, 2), (key960, 2), (key964, 2), (key746, -2), (key924, -2), (key924, -2), (key962, -6), (key751, 2), (key928, 2), (key928, 2)]

theorem rawRowCheck4100 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow4100 := by decide +kernel

def row4100 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

theorem rowCheck4100 : row4100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4100 := by decide +kernel

theorem rowEval4100 (x : Key → ℝ) : Integer.Sparse.eval row4100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4100, Integer.Sparse.eval_collectBalanced, rawRowCheck4100]

def rawRow4101 : Integer.Sparse Key := [(key831, -2), (key840, -2), (key831, -2), (key830, 6), (key960, 2), (key964, 2), (key960, 2), (key924, -2), (key746, -2), (key924, -2), (key962, -6), (key928, 2), (key751, 2), (key928, 2)]

theorem rawRowCheck4101 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow4101 := by decide +kernel

def row4101 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

theorem rowCheck4101 : row4101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4101 := by decide +kernel

theorem rowEval4101 (x : Key → ℝ) : Integer.Sparse.eval row4101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4101, Integer.Sparse.eval_collectBalanced, rawRowCheck4101]

def rawRow4102 : Integer.Sparse Key := [(key840, -2), (key831, -2), (key831, -2), (key830, 6), (key964, 2), (key960, 2), (key960, 2), (key924, -2), (key924, -2), (key746, -2), (key962, -6), (key928, 2), (key928, 2), (key751, 2)]

theorem rawRowCheck4102 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow4102 := by decide +kernel

def row4102 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

theorem rowCheck4102 : row4102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4102 := by decide +kernel

theorem rowEval4102 (x : Key → ℝ) : Integer.Sparse.eval row4102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4102, Integer.Sparse.eval_collectBalanced, rawRowCheck4102]

def rawRow4103 : Integer.Sparse Key := [(key924, -2), (key925, -2), (key935, -2), (key928, 6), (key830, 2), (key831, 2), (key840, 2), (key751, -2), (key928, -2), (key962, -2), (key831, -6), (key747, 2), (key925, 2), (key960, 2)]

theorem rawRowCheck4103 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form13 = rawRow4103 := by decide +kernel

def row4103 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

theorem rowCheck4103 : row4103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4103 := by decide +kernel

theorem rowEval4103 (x : Key → ℝ) : Integer.Sparse.eval row4103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4103, Integer.Sparse.eval_collectBalanced, rawRowCheck4103]

def rawRow4104 : Integer.Sparse Key := [(key925, -2), (key924, -2), (key935, -2), (key928, 6), (key831, 2), (key830, 2), (key840, 2), (key751, -2), (key962, -2), (key928, -2), (key831, -6), (key747, 2), (key960, 2), (key925, 2)]

theorem rawRowCheck4104 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form13 = rawRow4104 := by decide +kernel

def row4104 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

theorem rowCheck4104 : row4104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4104 := by decide +kernel

theorem rowEval4104 (x : Key → ℝ) : Integer.Sparse.eval row4104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4104, Integer.Sparse.eval_collectBalanced, rawRowCheck4104]

def rawRow4105 : Integer.Sparse Key := [(key924, -2), (key935, -2), (key925, -2), (key928, 6), (key830, 2), (key840, 2), (key831, 2), (key928, -2), (key751, -2), (key962, -2), (key831, -6), (key925, 2), (key747, 2), (key960, 2)]

theorem rawRowCheck4105 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form13 = rawRow4105 := by decide +kernel

def row4105 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

theorem rowCheck4105 : row4105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4105 := by decide +kernel

theorem rowEval4105 (x : Key → ℝ) : Integer.Sparse.eval row4105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4105, Integer.Sparse.eval_collectBalanced, rawRowCheck4105]

def rawRow4106 : Integer.Sparse Key := [(key935, -2), (key924, -2), (key925, -2), (key928, 6), (key840, 2), (key830, 2), (key831, 2), (key928, -2), (key962, -2), (key751, -2), (key831, -6), (key925, 2), (key960, 2), (key747, 2)]

theorem rawRowCheck4106 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form13 = rawRow4106 := by decide +kernel

def row4106 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

theorem rowCheck4106 : row4106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4106 := by decide +kernel

theorem rowEval4106 (x : Key → ℝ) : Integer.Sparse.eval row4106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4106, Integer.Sparse.eval_collectBalanced, rawRowCheck4106]

def rawRow4107 : Integer.Sparse Key := [(key925, -2), (key935, -2), (key924, -2), (key928, 6), (key831, 2), (key840, 2), (key830, 2), (key962, -2), (key751, -2), (key928, -2), (key831, -6), (key960, 2), (key747, 2), (key925, 2)]

theorem rawRowCheck4107 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form13 = rawRow4107 := by decide +kernel

def row4107 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

theorem rowCheck4107 : row4107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4107 := by decide +kernel

theorem rowEval4107 (x : Key → ℝ) : Integer.Sparse.eval row4107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4107, Integer.Sparse.eval_collectBalanced, rawRowCheck4107]

def rawRow4108 : Integer.Sparse Key := [(key935, -2), (key925, -2), (key924, -2), (key928, 6), (key840, 2), (key831, 2), (key830, 2), (key962, -2), (key928, -2), (key751, -2), (key831, -6), (key960, 2), (key925, 2), (key747, 2)]

theorem rawRowCheck4108 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form13 = rawRow4108 := by decide +kernel

def row4108 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

theorem rowCheck4108 : row4108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4108 := by decide +kernel

theorem rowEval4108 (x : Key → ℝ) : Integer.Sparse.eval row4108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4108, Integer.Sparse.eval_collectBalanced, rawRowCheck4108]

def rawRow4109 : Integer.Sparse Key := [(key925, -2), (key928, -2), (key935, -2), (key924, 6), (key960, 2), (key962, 2), (key964, 2), (key746, -2), (key830, -2), (key924, -2), (key960, -6), (key747, 2), (key831, 2), (key925, 2)]

theorem rawRowCheck4109 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form13 = rawRow4109 := by decide +kernel

def row4109 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

theorem rowCheck4109 : row4109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4109 := by decide +kernel

theorem rowEval4109 (x : Key → ℝ) : Integer.Sparse.eval row4109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4109, Integer.Sparse.eval_collectBalanced, rawRowCheck4109]

def rawRow4110 : Integer.Sparse Key := [(key928, -2), (key925, -2), (key935, -2), (key924, 6), (key962, 2), (key960, 2), (key964, 2), (key746, -2), (key924, -2), (key830, -2), (key960, -6), (key747, 2), (key925, 2), (key831, 2)]

theorem rawRowCheck4110 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form13 = rawRow4110 := by decide +kernel

def row4110 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

theorem rowCheck4110 : row4110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4110 := by decide +kernel

theorem rowEval4110 (x : Key → ℝ) : Integer.Sparse.eval row4110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4110, Integer.Sparse.eval_collectBalanced, rawRowCheck4110]

def rawRow4111 : Integer.Sparse Key := [(key925, -2), (key935, -2), (key928, -2), (key924, 6), (key960, 2), (key964, 2), (key962, 2), (key830, -2), (key746, -2), (key924, -2), (key960, -6), (key831, 2), (key747, 2), (key925, 2)]

theorem rawRowCheck4111 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form13 = rawRow4111 := by decide +kernel

def row4111 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

theorem rowCheck4111 : row4111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4111 := by decide +kernel

theorem rowEval4111 (x : Key → ℝ) : Integer.Sparse.eval row4111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4111, Integer.Sparse.eval_collectBalanced, rawRowCheck4111]

def rawRow4112 : Integer.Sparse Key := [(key935, -2), (key925, -2), (key928, -2), (key924, 6), (key964, 2), (key960, 2), (key962, 2), (key830, -2), (key924, -2), (key746, -2), (key960, -6), (key831, 2), (key925, 2), (key747, 2)]

theorem rawRowCheck4112 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form13 = rawRow4112 := by decide +kernel

def row4112 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

theorem rowCheck4112 : row4112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4112 := by decide +kernel

theorem rowEval4112 (x : Key → ℝ) : Integer.Sparse.eval row4112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4112, Integer.Sparse.eval_collectBalanced, rawRowCheck4112]

def rawRow4113 : Integer.Sparse Key := [(key928, -2), (key935, -2), (key925, -2), (key924, 6), (key962, 2), (key964, 2), (key960, 2), (key924, -2), (key746, -2), (key830, -2), (key960, -6), (key925, 2), (key747, 2), (key831, 2)]

theorem rawRowCheck4113 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form13 = rawRow4113 := by decide +kernel

def row4113 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

theorem rowCheck4113 : row4113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4113 := by decide +kernel

theorem rowEval4113 (x : Key → ℝ) : Integer.Sparse.eval row4113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4113, Integer.Sparse.eval_collectBalanced, rawRowCheck4113]

def rawRow4114 : Integer.Sparse Key := [(key935, -2), (key928, -2), (key925, -2), (key924, 6), (key964, 2), (key962, 2), (key960, 2), (key924, -2), (key830, -2), (key746, -2), (key960, -6), (key925, 2), (key831, 2), (key747, 2)]

theorem rawRowCheck4114 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form13 = rawRow4114 := by decide +kernel

def row4114 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

theorem rowCheck4114 : row4114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4114 := by decide +kernel

theorem rowEval4114 (x : Key → ℝ) : Integer.Sparse.eval row4114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4114, Integer.Sparse.eval_collectBalanced, rawRowCheck4114]

def rawRow4115 : Integer.Sparse Key := [(key960, -2), (key960, -2), (key964, -2), (key962, 6), (key831, 2), (key831, 2), (key840, 2), (key751, -2), (key928, -2), (key928, -2), (key830, -6), (key746, 2), (key924, 2), (key924, 2)]

theorem rawRowCheck4115 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13 = rawRow4115 := by decide +kernel

def row4115 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

theorem rowCheck4115 : row4115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4115 := by decide +kernel

theorem rowEval4115 (x : Key → ℝ) : Integer.Sparse.eval row4115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4115, Integer.Sparse.eval_collectBalanced, rawRowCheck4115]

def rawRow4116 : Integer.Sparse Key := [(key960, -2), (key964, -2), (key960, -2), (key962, 6), (key831, 2), (key840, 2), (key831, 2), (key928, -2), (key751, -2), (key928, -2), (key830, -6), (key924, 2), (key746, 2), (key924, 2)]

theorem rawRowCheck4116 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13 = rawRow4116 := by decide +kernel

def row4116 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

theorem rowCheck4116 : row4116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4116 := by decide +kernel

theorem rowEval4116 (x : Key → ℝ) : Integer.Sparse.eval row4116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4116, Integer.Sparse.eval_collectBalanced, rawRowCheck4116]

def rawRow4117 : Integer.Sparse Key := [(key964, -2), (key960, -2), (key960, -2), (key962, 6), (key840, 2), (key831, 2), (key831, 2), (key928, -2), (key928, -2), (key751, -2), (key830, -6), (key924, 2), (key924, 2), (key746, 2)]

theorem rawRowCheck4117 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13 = rawRow4117 := by decide +kernel

def row4117 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

theorem rowCheck4117 : row4117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4117 := by decide +kernel

theorem rowEval4117 (x : Key → ℝ) : Integer.Sparse.eval row4117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4117, Integer.Sparse.eval_collectBalanced, rawRowCheck4117]

def rawRow4118 : Integer.Sparse Key := [(key960, -2), (key962, -2), (key964, -2), (key960, 6), (key925, 2), (key928, 2), (key935, 2), (key747, -2), (key831, -2), (key925, -2), (key924, -6), (key746, 2), (key830, 2), (key924, 2)]

theorem rawRowCheck4118 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form13 = rawRow4118 := by decide +kernel

def row4118 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

theorem rowCheck4118 : row4118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4118 := by decide +kernel

theorem rowEval4118 (x : Key → ℝ) : Integer.Sparse.eval row4118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4118, Integer.Sparse.eval_collectBalanced, rawRowCheck4118]

def rawRow4119 : Integer.Sparse Key := [(key962, -2), (key960, -2), (key964, -2), (key960, 6), (key928, 2), (key925, 2), (key935, 2), (key747, -2), (key925, -2), (key831, -2), (key924, -6), (key746, 2), (key924, 2), (key830, 2)]

theorem rawRowCheck4119 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form13 = rawRow4119 := by decide +kernel

def row4119 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

theorem rowCheck4119 : row4119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4119 := by decide +kernel

theorem rowEval4119 (x : Key → ℝ) : Integer.Sparse.eval row4119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4119, Integer.Sparse.eval_collectBalanced, rawRowCheck4119]

def rawRow4120 : Integer.Sparse Key := [(key960, -2), (key964, -2), (key962, -2), (key960, 6), (key925, 2), (key935, 2), (key928, 2), (key831, -2), (key747, -2), (key925, -2), (key924, -6), (key830, 2), (key746, 2), (key924, 2)]

theorem rawRowCheck4120 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form13 = rawRow4120 := by decide +kernel

def row4120 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

theorem rowCheck4120 : row4120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4120 := by decide +kernel

theorem rowEval4120 (x : Key → ℝ) : Integer.Sparse.eval row4120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck4120, Integer.Sparse.eval_collectBalanced, rawRowCheck4120]

def rawRow4121 : Integer.Sparse Key := [(key964, -2), (key960, -2), (key962, -2), (key960, 6), (key935, 2), (key925, 2), (key928, 2), (key831, -2), (key925, -2), (key747, -2), (key924, -6), (key830, 2), (key924, 2), (key746, 2)]

theorem rawRowCheck4121 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form13 = rawRow4121 := by decide +kernel

def row4121 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

theorem rowCheck4121 : row4121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4121 := by decide +kernel

theorem rowEval4121 (x : Key → ℝ) : Integer.Sparse.eval row4121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4121, Integer.Sparse.eval_collectBalanced, rawRowCheck4121]

def rawRow4122 : Integer.Sparse Key := [(key962, -2), (key964, -2), (key960, -2), (key960, 6), (key928, 2), (key935, 2), (key925, 2), (key925, -2), (key747, -2), (key831, -2), (key924, -6), (key924, 2), (key746, 2), (key830, 2)]

theorem rawRowCheck4122 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form13 = rawRow4122 := by decide +kernel

def row4122 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

theorem rowCheck4122 : row4122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4122 := by decide +kernel

theorem rowEval4122 (x : Key → ℝ) : Integer.Sparse.eval row4122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form13) x := by
  rw [rowCheck4122, Integer.Sparse.eval_collectBalanced, rawRowCheck4122]

def rawRow4123 : Integer.Sparse Key := [(key964, -2), (key962, -2), (key960, -2), (key960, 6), (key935, 2), (key928, 2), (key925, 2), (key925, -2), (key831, -2), (key747, -2), (key924, -6), (key924, 2), (key830, 2), (key746, 2)]

theorem rawRowCheck4123 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form13 = rawRow4123 := by decide +kernel

def row4123 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

theorem rowCheck4123 : row4123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4123 := by decide +kernel

theorem rowEval4123 (x : Key → ℝ) : Integer.Sparse.eval row4123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form13) x := by
  rw [rowCheck4123, Integer.Sparse.eval_collectBalanced, rawRowCheck4123]

def rawRow4124 : Integer.Sparse Key := [(key1531, -2), (key1765, -2), (key1767, -2), (key1531, 2), (key1535, 2), (key1767, 2), (key1609, 2), (key1806, 2), (key1808, 2), (key1256, -1), (key1260, -1), (key1609, -1), (key1641, -1), (key1808, -1), (key1831, -1), (key1648, -2), (key1650, -2), (key1836, -2), (key1265, 1), (key1267, 1), (key1648, 1), (key1673, 1), (key1836, 1), (key1847, 1)]

theorem rawRowCheck4124 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form14 = rawRow4124 := by decide +kernel

def row4124 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

theorem rowCheck4124 : row4124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4124 := by decide +kernel

theorem rowEval4124 (x : Key → ℝ) : Integer.Sparse.eval row4124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4124, Integer.Sparse.eval_collectBalanced, rawRowCheck4124]

def rawRow4125 : Integer.Sparse Key := [(key1531, -2), (key1767, -2), (key1765, -2), (key1535, 2), (key1531, 2), (key1767, 2), (key1609, 2), (key1808, 2), (key1806, 2), (key1260, -1), (key1256, -1), (key1641, -1), (key1609, -1), (key1831, -1), (key1808, -1), (key1650, -2), (key1648, -2), (key1836, -2), (key1267, 1), (key1265, 1), (key1673, 1), (key1648, 1), (key1847, 1), (key1836, 1)]

theorem rawRowCheck4125 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form14 = rawRow4125 := by decide +kernel

def row4125 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

theorem rowCheck4125 : row4125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4125 := by decide +kernel

theorem rowEval4125 (x : Key → ℝ) : Integer.Sparse.eval row4125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4125, Integer.Sparse.eval_collectBalanced, rawRowCheck4125]

def rawRow4126 : Integer.Sparse Key := [(key1765, -2), (key1531, -2), (key1767, -2), (key1531, 2), (key1767, 2), (key1535, 2), (key1806, 2), (key1609, 2), (key1808, 2), (key1609, -1), (key1808, -1), (key1256, -1), (key1831, -1), (key1260, -1), (key1641, -1), (key1648, -2), (key1836, -2), (key1650, -2), (key1648, 1), (key1836, 1), (key1265, 1), (key1847, 1), (key1267, 1), (key1673, 1)]

theorem rawRowCheck4126 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form14 = rawRow4126 := by decide +kernel

def row4126 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

theorem rowCheck4126 : row4126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4126 := by decide +kernel

theorem rowEval4126 (x : Key → ℝ) : Integer.Sparse.eval row4126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4126, Integer.Sparse.eval_collectBalanced, rawRowCheck4126]

def rawRow4127 : Integer.Sparse Key := [(key1765, -2), (key1767, -2), (key1531, -2), (key1767, 2), (key1531, 2), (key1535, 2), (key1806, 2), (key1808, 2), (key1609, 2), (key1808, -1), (key1609, -1), (key1831, -1), (key1256, -1), (key1641, -1), (key1260, -1), (key1836, -2), (key1648, -2), (key1650, -2), (key1836, 1), (key1648, 1), (key1847, 1), (key1265, 1), (key1673, 1), (key1267, 1)]

theorem rawRowCheck4127 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form14 = rawRow4127 := by decide +kernel

def row4127 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

theorem rowCheck4127 : row4127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4127 := by decide +kernel

theorem rowEval4127 (x : Key → ℝ) : Integer.Sparse.eval row4127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4127, Integer.Sparse.eval_collectBalanced, rawRowCheck4127]

def rawRow4128 : Integer.Sparse Key := [(key1767, -2), (key1531, -2), (key1765, -2), (key1535, 2), (key1767, 2), (key1531, 2), (key1808, 2), (key1609, 2), (key1806, 2), (key1641, -1), (key1831, -1), (key1260, -1), (key1808, -1), (key1256, -1), (key1609, -1), (key1650, -2), (key1836, -2), (key1648, -2), (key1673, 1), (key1847, 1), (key1267, 1), (key1836, 1), (key1265, 1), (key1648, 1)]

theorem rawRowCheck4128 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form14 = rawRow4128 := by decide +kernel

def row4128 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

theorem rowCheck4128 : row4128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4128 := by decide +kernel

theorem rowEval4128 (x : Key → ℝ) : Integer.Sparse.eval row4128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4128, Integer.Sparse.eval_collectBalanced, rawRowCheck4128]

def rawRow4129 : Integer.Sparse Key := [(key1767, -2), (key1765, -2), (key1531, -2), (key1767, 2), (key1535, 2), (key1531, 2), (key1808, 2), (key1806, 2), (key1609, 2), (key1831, -1), (key1641, -1), (key1808, -1), (key1260, -1), (key1609, -1), (key1256, -1), (key1836, -2), (key1650, -2), (key1648, -2), (key1847, 1), (key1673, 1), (key1836, 1), (key1267, 1), (key1648, 1), (key1265, 1)]

theorem rawRowCheck4129 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form14 = rawRow4129 := by decide +kernel

def row4129 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

theorem rowCheck4129 : row4129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4129 := by decide +kernel

theorem rowEval4129 (x : Key → ℝ) : Integer.Sparse.eval row4129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4129, Integer.Sparse.eval_collectBalanced, rawRowCheck4129]

def rawRow4130 : Integer.Sparse Key := [(key1535, -2), (key1767, -2), (key1767, -2), (key1531, 2), (key1531, 2), (key1765, 2), (key1641, 2), (key1831, 2), (key1831, 2), (key1256, -1), (key1256, -1), (key1609, -1), (key1609, -1), (key1806, -1), (key1806, -1), (key1673, -2), (key1673, -2), (key1847, -2), (key1267, 1), (key1267, 1), (key1650, 1), (key1650, 1), (key1836, 1), (key1836, 1)]

theorem rawRowCheck4130 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4130 := by decide +kernel

def row4130 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

theorem rowCheck4130 : row4130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4130 := by decide +kernel

theorem rowEval4130 (x : Key → ℝ) : Integer.Sparse.eval row4130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4130, Integer.Sparse.eval_collectBalanced, rawRowCheck4130]

def rawRow4131 : Integer.Sparse Key := [(key1767, -2), (key1535, -2), (key1767, -2), (key1531, 2), (key1765, 2), (key1531, 2), (key1831, 2), (key1641, 2), (key1831, 2), (key1609, -1), (key1806, -1), (key1256, -1), (key1806, -1), (key1256, -1), (key1609, -1), (key1673, -2), (key1847, -2), (key1673, -2), (key1650, 1), (key1836, 1), (key1267, 1), (key1836, 1), (key1267, 1), (key1650, 1)]

theorem rawRowCheck4131 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4131 := by decide +kernel

def row4131 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

theorem rowCheck4131 : row4131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4131 := by decide +kernel

theorem rowEval4131 (x : Key → ℝ) : Integer.Sparse.eval row4131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4131, Integer.Sparse.eval_collectBalanced, rawRowCheck4131]

def rawRow4132 : Integer.Sparse Key := [(key1767, -2), (key1767, -2), (key1535, -2), (key1765, 2), (key1531, 2), (key1531, 2), (key1831, 2), (key1831, 2), (key1641, 2), (key1806, -1), (key1609, -1), (key1806, -1), (key1256, -1), (key1609, -1), (key1256, -1), (key1847, -2), (key1673, -2), (key1673, -2), (key1836, 1), (key1650, 1), (key1836, 1), (key1267, 1), (key1650, 1), (key1267, 1)]

theorem rawRowCheck4132 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4132 := by decide +kernel

def row4132 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

theorem rowCheck4132 : row4132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4132 := by decide +kernel

theorem rowEval4132 (x : Key → ℝ) : Integer.Sparse.eval row4132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4132, Integer.Sparse.eval_collectBalanced, rawRowCheck4132]

def rawRow4133 : Integer.Sparse Key := [(key1609, -2), (key1806, -2), (key1808, -2), (key1648, 2), (key1650, 2), (key1836, 2), (key1531, 2), (key1765, 2), (key1767, 2), (key1265, -1), (key1267, -1), (key1648, -1), (key1673, -1), (key1836, -1), (key1847, -1), (key1531, -2), (key1535, -2), (key1767, -2), (key1256, 1), (key1260, 1), (key1609, 1), (key1641, 1), (key1808, 1), (key1831, 1)]

theorem rawRowCheck4133 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form14 = rawRow4133 := by decide +kernel

def row4133 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck4133 : row4133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4133 := by decide +kernel

theorem rowEval4133 (x : Key → ℝ) : Integer.Sparse.eval row4133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4133, Integer.Sparse.eval_collectBalanced, rawRowCheck4133]

def rawRow4134 : Integer.Sparse Key := [(key1609, -2), (key1808, -2), (key1806, -2), (key1650, 2), (key1648, 2), (key1836, 2), (key1531, 2), (key1767, 2), (key1765, 2), (key1267, -1), (key1265, -1), (key1673, -1), (key1648, -1), (key1847, -1), (key1836, -1), (key1535, -2), (key1531, -2), (key1767, -2), (key1260, 1), (key1256, 1), (key1641, 1), (key1609, 1), (key1831, 1), (key1808, 1)]

theorem rawRowCheck4134 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form14 = rawRow4134 := by decide +kernel

def row4134 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck4134 : row4134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4134 := by decide +kernel

theorem rowEval4134 (x : Key → ℝ) : Integer.Sparse.eval row4134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4134, Integer.Sparse.eval_collectBalanced, rawRowCheck4134]

def rawRow4135 : Integer.Sparse Key := [(key1806, -2), (key1609, -2), (key1808, -2), (key1648, 2), (key1836, 2), (key1650, 2), (key1765, 2), (key1531, 2), (key1767, 2), (key1648, -1), (key1836, -1), (key1265, -1), (key1847, -1), (key1267, -1), (key1673, -1), (key1531, -2), (key1767, -2), (key1535, -2), (key1609, 1), (key1808, 1), (key1256, 1), (key1831, 1), (key1260, 1), (key1641, 1)]

theorem rawRowCheck4135 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form14 = rawRow4135 := by decide +kernel

def row4135 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck4135 : row4135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4135 := by decide +kernel

theorem rowEval4135 (x : Key → ℝ) : Integer.Sparse.eval row4135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4135, Integer.Sparse.eval_collectBalanced, rawRowCheck4135]

def rawRow4136 : Integer.Sparse Key := [(key1806, -2), (key1808, -2), (key1609, -2), (key1836, 2), (key1648, 2), (key1650, 2), (key1765, 2), (key1767, 2), (key1531, 2), (key1836, -1), (key1648, -1), (key1847, -1), (key1265, -1), (key1673, -1), (key1267, -1), (key1767, -2), (key1531, -2), (key1535, -2), (key1808, 1), (key1609, 1), (key1831, 1), (key1256, 1), (key1641, 1), (key1260, 1)]

theorem rawRowCheck4136 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form14 = rawRow4136 := by decide +kernel

def row4136 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck4136 : row4136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4136 := by decide +kernel

theorem rowEval4136 (x : Key → ℝ) : Integer.Sparse.eval row4136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4136, Integer.Sparse.eval_collectBalanced, rawRowCheck4136]

def rawRow4137 : Integer.Sparse Key := [(key1808, -2), (key1609, -2), (key1806, -2), (key1650, 2), (key1836, 2), (key1648, 2), (key1767, 2), (key1531, 2), (key1765, 2), (key1673, -1), (key1847, -1), (key1267, -1), (key1836, -1), (key1265, -1), (key1648, -1), (key1535, -2), (key1767, -2), (key1531, -2), (key1641, 1), (key1831, 1), (key1260, 1), (key1808, 1), (key1256, 1), (key1609, 1)]

theorem rawRowCheck4137 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form14 = rawRow4137 := by decide +kernel

def row4137 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck4137 : row4137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4137 := by decide +kernel

theorem rowEval4137 (x : Key → ℝ) : Integer.Sparse.eval row4137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4137, Integer.Sparse.eval_collectBalanced, rawRowCheck4137]

def rawRow4138 : Integer.Sparse Key := [(key1808, -2), (key1806, -2), (key1609, -2), (key1836, 2), (key1650, 2), (key1648, 2), (key1767, 2), (key1765, 2), (key1531, 2), (key1847, -1), (key1673, -1), (key1836, -1), (key1267, -1), (key1648, -1), (key1265, -1), (key1767, -2), (key1535, -2), (key1531, -2), (key1831, 1), (key1641, 1), (key1808, 1), (key1260, 1), (key1609, 1), (key1256, 1)]

theorem rawRowCheck4138 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form14 = rawRow4138 := by decide +kernel

def row4138 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

theorem rowCheck4138 : row4138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4138 := by decide +kernel

theorem rowEval4138 (x : Key → ℝ) : Integer.Sparse.eval row4138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4138, Integer.Sparse.eval_collectBalanced, rawRowCheck4138]

def rawRow4139 : Integer.Sparse Key := [(key1650, -2), (key1808, -2), (key1836, -2), (key1609, 2), (key1648, 2), (key1806, 2), (key1673, 2), (key1831, 2), (key1847, 2), (key1256, -1), (key1265, -1), (key1531, -1), (key1648, -1), (key1765, -1), (key1806, -1), (key1641, -2), (key1673, -2), (key1831, -2), (key1260, 1), (key1267, 1), (key1535, 1), (key1650, 1), (key1767, 1), (key1808, 1)]

theorem rawRowCheck4139 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form14 = rawRow4139 := by decide +kernel

def row4139 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

theorem rowCheck4139 : row4139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4139 := by decide +kernel

theorem rowEval4139 (x : Key → ℝ) : Integer.Sparse.eval row4139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4139, Integer.Sparse.eval_collectBalanced, rawRowCheck4139]

def rawRow4140 : Integer.Sparse Key := [(key1650, -2), (key1836, -2), (key1808, -2), (key1648, 2), (key1609, 2), (key1806, 2), (key1673, 2), (key1847, 2), (key1831, 2), (key1265, -1), (key1256, -1), (key1648, -1), (key1531, -1), (key1806, -1), (key1765, -1), (key1673, -2), (key1641, -2), (key1831, -2), (key1267, 1), (key1260, 1), (key1650, 1), (key1535, 1), (key1808, 1), (key1767, 1)]

theorem rawRowCheck4140 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form14 = rawRow4140 := by decide +kernel

def row4140 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

theorem rowCheck4140 : row4140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4140 := by decide +kernel

theorem rowEval4140 (x : Key → ℝ) : Integer.Sparse.eval row4140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4140, Integer.Sparse.eval_collectBalanced, rawRowCheck4140]

def rawRow4141 : Integer.Sparse Key := [(key1808, -2), (key1650, -2), (key1836, -2), (key1609, 2), (key1806, 2), (key1648, 2), (key1831, 2), (key1673, 2), (key1847, 2), (key1531, -1), (key1765, -1), (key1256, -1), (key1806, -1), (key1265, -1), (key1648, -1), (key1641, -2), (key1831, -2), (key1673, -2), (key1535, 1), (key1767, 1), (key1260, 1), (key1808, 1), (key1267, 1), (key1650, 1)]

theorem rawRowCheck4141 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form14 = rawRow4141 := by decide +kernel

def row4141 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

theorem rowCheck4141 : row4141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4141 := by decide +kernel

theorem rowEval4141 (x : Key → ℝ) : Integer.Sparse.eval row4141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4141, Integer.Sparse.eval_collectBalanced, rawRowCheck4141]

def rawRow4142 : Integer.Sparse Key := [(key1808, -2), (key1836, -2), (key1650, -2), (key1806, 2), (key1609, 2), (key1648, 2), (key1831, 2), (key1847, 2), (key1673, 2), (key1765, -1), (key1531, -1), (key1806, -1), (key1256, -1), (key1648, -1), (key1265, -1), (key1831, -2), (key1641, -2), (key1673, -2), (key1767, 1), (key1535, 1), (key1808, 1), (key1260, 1), (key1650, 1), (key1267, 1)]

theorem rawRowCheck4142 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form14 = rawRow4142 := by decide +kernel

def row4142 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

theorem rowCheck4142 : row4142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4142 := by decide +kernel

theorem rowEval4142 (x : Key → ℝ) : Integer.Sparse.eval row4142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4142, Integer.Sparse.eval_collectBalanced, rawRowCheck4142]

def rawRow4143 : Integer.Sparse Key := [(key1836, -2), (key1650, -2), (key1808, -2), (key1648, 2), (key1806, 2), (key1609, 2), (key1847, 2), (key1673, 2), (key1831, 2), (key1648, -1), (key1806, -1), (key1265, -1), (key1765, -1), (key1256, -1), (key1531, -1), (key1673, -2), (key1831, -2), (key1641, -2), (key1650, 1), (key1808, 1), (key1267, 1), (key1767, 1), (key1260, 1), (key1535, 1)]

theorem rawRowCheck4143 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form14 = rawRow4143 := by decide +kernel

def row4143 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

theorem rowCheck4143 : row4143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4143 := by decide +kernel

theorem rowEval4143 (x : Key → ℝ) : Integer.Sparse.eval row4143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4143, Integer.Sparse.eval_collectBalanced, rawRowCheck4143]

def rawRow4144 : Integer.Sparse Key := [(key1836, -2), (key1808, -2), (key1650, -2), (key1806, 2), (key1648, 2), (key1609, 2), (key1847, 2), (key1831, 2), (key1673, 2), (key1806, -1), (key1648, -1), (key1765, -1), (key1265, -1), (key1531, -1), (key1256, -1), (key1831, -2), (key1673, -2), (key1641, -2), (key1808, 1), (key1650, 1), (key1767, 1), (key1267, 1), (key1535, 1), (key1260, 1)]

theorem rawRowCheck4144 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form14 = rawRow4144 := by decide +kernel

def row4144 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

theorem rowCheck4144 : row4144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4144 := by decide +kernel

theorem rowEval4144 (x : Key → ℝ) : Integer.Sparse.eval row4144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4144, Integer.Sparse.eval_collectBalanced, rawRowCheck4144]

def rawRow4145 : Integer.Sparse Key := [(key1641, -2), (key1831, -2), (key1831, -2), (key1673, 2), (key1673, 2), (key1847, 2), (key1535, 2), (key1767, 2), (key1767, 2), (key1267, -1), (key1267, -1), (key1650, -1), (key1650, -1), (key1836, -1), (key1836, -1), (key1531, -2), (key1531, -2), (key1765, -2), (key1256, 1), (key1256, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1)]

theorem rawRowCheck4145 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form14 = rawRow4145 := by decide +kernel

def row4145 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

theorem rowCheck4145 : row4145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4145 := by decide +kernel

theorem rowEval4145 (x : Key → ℝ) : Integer.Sparse.eval row4145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4145, Integer.Sparse.eval_collectBalanced, rawRowCheck4145]

def rawRow4146 : Integer.Sparse Key := [(key1831, -2), (key1641, -2), (key1831, -2), (key1673, 2), (key1847, 2), (key1673, 2), (key1767, 2), (key1535, 2), (key1767, 2), (key1650, -1), (key1836, -1), (key1267, -1), (key1836, -1), (key1267, -1), (key1650, -1), (key1531, -2), (key1765, -2), (key1531, -2), (key1609, 1), (key1806, 1), (key1256, 1), (key1806, 1), (key1256, 1), (key1609, 1)]

theorem rawRowCheck4146 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form14 = rawRow4146 := by decide +kernel

def row4146 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

theorem rowCheck4146 : row4146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4146 := by decide +kernel

theorem rowEval4146 (x : Key → ℝ) : Integer.Sparse.eval row4146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4146, Integer.Sparse.eval_collectBalanced, rawRowCheck4146]

def rawRow4147 : Integer.Sparse Key := [(key1831, -2), (key1831, -2), (key1641, -2), (key1847, 2), (key1673, 2), (key1673, 2), (key1767, 2), (key1767, 2), (key1535, 2), (key1836, -1), (key1650, -1), (key1836, -1), (key1267, -1), (key1650, -1), (key1267, -1), (key1765, -2), (key1531, -2), (key1531, -2), (key1806, 1), (key1609, 1), (key1806, 1), (key1256, 1), (key1609, 1), (key1256, 1)]

theorem rawRowCheck4147 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form14 = rawRow4147 := by decide +kernel

def row4147 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

theorem rowCheck4147 : row4147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4147 := by decide +kernel

theorem rowEval4147 (x : Key → ℝ) : Integer.Sparse.eval row4147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4147, Integer.Sparse.eval_collectBalanced, rawRowCheck4147]

def rawRow4148 : Integer.Sparse Key := [(key1673, -2), (key1831, -2), (key1847, -2), (key1641, 2), (key1673, 2), (key1831, 2), (key1650, 2), (key1808, 2), (key1836, 2), (key1260, -1), (key1267, -1), (key1535, -1), (key1650, -1), (key1767, -1), (key1808, -1), (key1609, -2), (key1648, -2), (key1806, -2), (key1256, 1), (key1265, 1), (key1531, 1), (key1648, 1), (key1765, 1), (key1806, 1)]

theorem rawRowCheck4148 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form14 = rawRow4148 := by decide +kernel

def row4148 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

theorem rowCheck4148 : row4148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4148 := by decide +kernel

theorem rowEval4148 (x : Key → ℝ) : Integer.Sparse.eval row4148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4148, Integer.Sparse.eval_collectBalanced, rawRowCheck4148]

def rawRow4149 : Integer.Sparse Key := [(key1673, -2), (key1847, -2), (key1831, -2), (key1673, 2), (key1641, 2), (key1831, 2), (key1650, 2), (key1836, 2), (key1808, 2), (key1267, -1), (key1260, -1), (key1650, -1), (key1535, -1), (key1808, -1), (key1767, -1), (key1648, -2), (key1609, -2), (key1806, -2), (key1265, 1), (key1256, 1), (key1648, 1), (key1531, 1), (key1806, 1), (key1765, 1)]

theorem rawRowCheck4149 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form14 = rawRow4149 := by decide +kernel

def row4149 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

theorem rowCheck4149 : row4149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4149 := by decide +kernel

theorem rowEval4149 (x : Key → ℝ) : Integer.Sparse.eval row4149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4149, Integer.Sparse.eval_collectBalanced, rawRowCheck4149]

def rawRow4150 : Integer.Sparse Key := [(key1831, -2), (key1673, -2), (key1847, -2), (key1641, 2), (key1831, 2), (key1673, 2), (key1808, 2), (key1650, 2), (key1836, 2), (key1535, -1), (key1767, -1), (key1260, -1), (key1808, -1), (key1267, -1), (key1650, -1), (key1609, -2), (key1806, -2), (key1648, -2), (key1531, 1), (key1765, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1648, 1)]

theorem rawRowCheck4150 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form14 = rawRow4150 := by decide +kernel

def row4150 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

theorem rowCheck4150 : row4150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4150 := by decide +kernel

theorem rowEval4150 (x : Key → ℝ) : Integer.Sparse.eval row4150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form14) x := by
  rw [rowCheck4150, Integer.Sparse.eval_collectBalanced, rawRowCheck4150]

def rawRow4151 : Integer.Sparse Key := [(key1831, -2), (key1847, -2), (key1673, -2), (key1831, 2), (key1641, 2), (key1673, 2), (key1808, 2), (key1836, 2), (key1650, 2), (key1767, -1), (key1535, -1), (key1808, -1), (key1260, -1), (key1650, -1), (key1267, -1), (key1806, -2), (key1609, -2), (key1648, -2), (key1765, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1648, 1), (key1265, 1)]

theorem rawRowCheck4151 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form14 = rawRow4151 := by decide +kernel

def row4151 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

theorem rowCheck4151 : row4151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4151 := by decide +kernel

theorem rowEval4151 (x : Key → ℝ) : Integer.Sparse.eval row4151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4151, Integer.Sparse.eval_collectBalanced, rawRowCheck4151]

def rawRow4152 : Integer.Sparse Key := [(key1847, -2), (key1673, -2), (key1831, -2), (key1673, 2), (key1831, 2), (key1641, 2), (key1836, 2), (key1650, 2), (key1808, 2), (key1650, -1), (key1808, -1), (key1267, -1), (key1767, -1), (key1260, -1), (key1535, -1), (key1648, -2), (key1806, -2), (key1609, -2), (key1648, 1), (key1806, 1), (key1265, 1), (key1765, 1), (key1256, 1), (key1531, 1)]

theorem rawRowCheck4152 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form14 = rawRow4152 := by decide +kernel

def row4152 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

theorem rowCheck4152 : row4152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4152 := by decide +kernel

theorem rowEval4152 (x : Key → ℝ) : Integer.Sparse.eval row4152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form14) x := by
  rw [rowCheck4152, Integer.Sparse.eval_collectBalanced, rawRowCheck4152]

def rawRow4153 : Integer.Sparse Key := [(key1847, -2), (key1831, -2), (key1673, -2), (key1831, 2), (key1673, 2), (key1641, 2), (key1836, 2), (key1808, 2), (key1650, 2), (key1808, -1), (key1650, -1), (key1767, -1), (key1267, -1), (key1535, -1), (key1260, -1), (key1806, -2), (key1648, -2), (key1609, -2), (key1806, 1), (key1648, 1), (key1765, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

theorem rawRowCheck4153 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form14 = rawRow4153 := by decide +kernel

def row4153 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

theorem rowCheck4153 : row4153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4153 := by decide +kernel

theorem rowEval4153 (x : Key → ℝ) : Integer.Sparse.eval row4153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form14) x := by
  rw [rowCheck4153, Integer.Sparse.eval_collectBalanced, rawRowCheck4153]

def rawRow4154 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1569, -1), (key1593, -1), (key1903, -1), (key1911, -1), (key1298, 2), (key1575, 2), (key1593, 2), (key1312, 1), (key1318, 1), (key1618, 1), (key1633, 1), (key1918, 1), (key1926, 1), (key1318, -1), (key1326, -1), (key1426, -1), (key1444, -1), (key1624, -1), (key1633, -1), (key1351, -2), (key1681, -2), (key1689, -2), (key1351, 1), (key1354, 1), (key1472, 1), (key1480, 1), (key1683, 1), (key1689, 1)]

theorem rawRowCheck4154 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form15 = rawRow4154 := by decide +kernel

def row4154 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

theorem rowCheck4154 : row4154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4154 := by decide +kernel

theorem rowEval4154 (x : Key → ℝ) : Integer.Sparse.eval row4154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4154, Integer.Sparse.eval_collectBalanced, rawRowCheck4154]

def rawRow4155 : Integer.Sparse Key := [(key1298, -1), (key1292, -1), (key1593, -1), (key1569, -1), (key1911, -1), (key1903, -1), (key1298, 2), (key1593, 2), (key1575, 2), (key1318, 1), (key1312, 1), (key1633, 1), (key1618, 1), (key1926, 1), (key1918, 1), (key1326, -1), (key1318, -1), (key1444, -1), (key1426, -1), (key1633, -1), (key1624, -1), (key1351, -2), (key1689, -2), (key1681, -2), (key1354, 1), (key1351, 1), (key1480, 1), (key1472, 1), (key1689, 1), (key1683, 1)]

theorem rawRowCheck4155 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form15 = rawRow4155 := by decide +kernel

def row4155 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

theorem rowCheck4155 : row4155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4155 := by decide +kernel

theorem rowEval4155 (x : Key → ℝ) : Integer.Sparse.eval row4155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4155, Integer.Sparse.eval_collectBalanced, rawRowCheck4155]

def rawRow4156 : Integer.Sparse Key := [(key1569, -1), (key1903, -1), (key1292, -1), (key1911, -1), (key1298, -1), (key1593, -1), (key1575, 2), (key1298, 2), (key1593, 2), (key1618, 1), (key1918, 1), (key1312, 1), (key1926, 1), (key1318, 1), (key1633, 1), (key1426, -1), (key1624, -1), (key1318, -1), (key1633, -1), (key1326, -1), (key1444, -1), (key1681, -2), (key1351, -2), (key1689, -2), (key1472, 1), (key1683, 1), (key1351, 1), (key1689, 1), (key1354, 1), (key1480, 1)]

theorem rawRowCheck4156 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form15 = rawRow4156 := by decide +kernel

def row4156 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

theorem rowCheck4156 : row4156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4156 := by decide +kernel

theorem rowEval4156 (x : Key → ℝ) : Integer.Sparse.eval row4156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4156, Integer.Sparse.eval_collectBalanced, rawRowCheck4156]

def rawRow4157 : Integer.Sparse Key := [(key1903, -1), (key1569, -1), (key1911, -1), (key1292, -1), (key1593, -1), (key1298, -1), (key1575, 2), (key1593, 2), (key1298, 2), (key1918, 1), (key1618, 1), (key1926, 1), (key1312, 1), (key1633, 1), (key1318, 1), (key1624, -1), (key1426, -1), (key1633, -1), (key1318, -1), (key1444, -1), (key1326, -1), (key1681, -2), (key1689, -2), (key1351, -2), (key1683, 1), (key1472, 1), (key1689, 1), (key1351, 1), (key1480, 1), (key1354, 1)]

theorem rawRowCheck4157 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form15 = rawRow4157 := by decide +kernel

def row4157 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

theorem rowCheck4157 : row4157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4157 := by decide +kernel

theorem rowEval4157 (x : Key → ℝ) : Integer.Sparse.eval row4157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4157, Integer.Sparse.eval_collectBalanced, rawRowCheck4157]

def rawRow4158 : Integer.Sparse Key := [(key1593, -1), (key1911, -1), (key1298, -1), (key1903, -1), (key1292, -1), (key1569, -1), (key1593, 2), (key1298, 2), (key1575, 2), (key1633, 1), (key1926, 1), (key1318, 1), (key1918, 1), (key1312, 1), (key1618, 1), (key1444, -1), (key1633, -1), (key1326, -1), (key1624, -1), (key1318, -1), (key1426, -1), (key1689, -2), (key1351, -2), (key1681, -2), (key1480, 1), (key1689, 1), (key1354, 1), (key1683, 1), (key1351, 1), (key1472, 1)]

theorem rawRowCheck4158 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form15 = rawRow4158 := by decide +kernel

def row4158 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

theorem rowCheck4158 : row4158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4158 := by decide +kernel

theorem rowEval4158 (x : Key → ℝ) : Integer.Sparse.eval row4158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4158, Integer.Sparse.eval_collectBalanced, rawRowCheck4158]

def rawRow4159 : Integer.Sparse Key := [(key1911, -1), (key1593, -1), (key1903, -1), (key1298, -1), (key1569, -1), (key1292, -1), (key1593, 2), (key1575, 2), (key1298, 2), (key1926, 1), (key1633, 1), (key1918, 1), (key1318, 1), (key1618, 1), (key1312, 1), (key1633, -1), (key1444, -1), (key1624, -1), (key1326, -1), (key1426, -1), (key1318, -1), (key1689, -2), (key1681, -2), (key1351, -2), (key1689, 1), (key1480, 1), (key1683, 1), (key1354, 1), (key1472, 1), (key1351, 1)]

theorem rawRowCheck4159 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form15 = rawRow4159 := by decide +kernel

def row4159 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

theorem rowCheck4159 : row4159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4159 := by decide +kernel

theorem rowEval4159 (x : Key → ℝ) : Integer.Sparse.eval row4159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4159, Integer.Sparse.eval_collectBalanced, rawRowCheck4159]

def rawRow4160 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1575, -1), (key1575, -1), (key1903, -1), (key1903, -1), (key1292, 2), (key1569, 2), (key1569, 2), (key1326, 1), (key1326, 1), (key1624, 1), (key1624, 1), (key1920, 1), (key1920, 1), (key1312, -1), (key1312, -1), (key1420, -1), (key1420, -1), (key1618, -1), (key1618, -1), (key1354, -2), (key1683, -2), (key1683, -2), (key1351, 1), (key1351, 1), (key1472, 1), (key1472, 1), (key1681, 1), (key1681, 1)]

theorem rawRowCheck4160 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow4160 := by decide +kernel

def row4160 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

theorem rowCheck4160 : row4160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4160 := by decide +kernel

theorem rowEval4160 (x : Key → ℝ) : Integer.Sparse.eval row4160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4160, Integer.Sparse.eval_collectBalanced, rawRowCheck4160]

def rawRow4161 : Integer.Sparse Key := [(key1575, -1), (key1903, -1), (key1298, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1569, 2), (key1292, 2), (key1569, 2), (key1624, 1), (key1920, 1), (key1326, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1420, -1), (key1618, -1), (key1312, -1), (key1618, -1), (key1312, -1), (key1420, -1), (key1683, -2), (key1354, -2), (key1683, -2), (key1472, 1), (key1681, 1), (key1351, 1), (key1681, 1), (key1351, 1), (key1472, 1)]

theorem rawRowCheck4161 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow4161 := by decide +kernel

def row4161 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

theorem rowCheck4161 : row4161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4161 := by decide +kernel

theorem rowEval4161 (x : Key → ℝ) : Integer.Sparse.eval row4161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4161, Integer.Sparse.eval_collectBalanced, rawRowCheck4161]

def rawRow4162 : Integer.Sparse Key := [(key1903, -1), (key1575, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1298, -1), (key1569, 2), (key1569, 2), (key1292, 2), (key1920, 1), (key1624, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1326, 1), (key1618, -1), (key1420, -1), (key1618, -1), (key1312, -1), (key1420, -1), (key1312, -1), (key1683, -2), (key1683, -2), (key1354, -2), (key1681, 1), (key1472, 1), (key1681, 1), (key1351, 1), (key1472, 1), (key1351, 1)]

theorem rawRowCheck4162 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow4162 := by decide +kernel

def row4162 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

theorem rowCheck4162 : row4162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4162 := by decide +kernel

theorem rowEval4162 (x : Key → ℝ) : Integer.Sparse.eval row4162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4162, Integer.Sparse.eval_collectBalanced, rawRowCheck4162]

def rawRow4163 : Integer.Sparse Key := [(key1312, -1), (key1318, -1), (key1618, -1), (key1633, -1), (key1918, -1), (key1926, -1), (key1351, 2), (key1681, 2), (key1689, 2), (key1292, 1), (key1298, 1), (key1569, 1), (key1593, 1), (key1903, 1), (key1911, 1), (key1351, -1), (key1354, -1), (key1472, -1), (key1480, -1), (key1683, -1), (key1689, -1), (key1298, -2), (key1575, -2), (key1593, -2), (key1318, 1), (key1326, 1), (key1426, 1), (key1444, 1), (key1624, 1), (key1633, 1)]

theorem rawRowCheck4163 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form15 = rawRow4163 := by decide +kernel

def row4163 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

theorem rowCheck4163 : row4163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4163 := by decide +kernel

theorem rowEval4163 (x : Key → ℝ) : Integer.Sparse.eval row4163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4163, Integer.Sparse.eval_collectBalanced, rawRowCheck4163]

def rawRow4164 : Integer.Sparse Key := [(key1318, -1), (key1312, -1), (key1633, -1), (key1618, -1), (key1926, -1), (key1918, -1), (key1351, 2), (key1689, 2), (key1681, 2), (key1298, 1), (key1292, 1), (key1593, 1), (key1569, 1), (key1911, 1), (key1903, 1), (key1354, -1), (key1351, -1), (key1480, -1), (key1472, -1), (key1689, -1), (key1683, -1), (key1298, -2), (key1593, -2), (key1575, -2), (key1326, 1), (key1318, 1), (key1444, 1), (key1426, 1), (key1633, 1), (key1624, 1)]

theorem rawRowCheck4164 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form15 = rawRow4164 := by decide +kernel

def row4164 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

theorem rowCheck4164 : row4164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4164 := by decide +kernel

theorem rowEval4164 (x : Key → ℝ) : Integer.Sparse.eval row4164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4164, Integer.Sparse.eval_collectBalanced, rawRowCheck4164]

def rawRow4165 : Integer.Sparse Key := [(key1618, -1), (key1918, -1), (key1312, -1), (key1926, -1), (key1318, -1), (key1633, -1), (key1681, 2), (key1351, 2), (key1689, 2), (key1569, 1), (key1903, 1), (key1292, 1), (key1911, 1), (key1298, 1), (key1593, 1), (key1472, -1), (key1683, -1), (key1351, -1), (key1689, -1), (key1354, -1), (key1480, -1), (key1575, -2), (key1298, -2), (key1593, -2), (key1426, 1), (key1624, 1), (key1318, 1), (key1633, 1), (key1326, 1), (key1444, 1)]

theorem rawRowCheck4165 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form15 = rawRow4165 := by decide +kernel

def row4165 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

theorem rowCheck4165 : row4165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4165 := by decide +kernel

theorem rowEval4165 (x : Key → ℝ) : Integer.Sparse.eval row4165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4165, Integer.Sparse.eval_collectBalanced, rawRowCheck4165]

def rawRow4166 : Integer.Sparse Key := [(key1918, -1), (key1618, -1), (key1926, -1), (key1312, -1), (key1633, -1), (key1318, -1), (key1681, 2), (key1689, 2), (key1351, 2), (key1903, 1), (key1569, 1), (key1911, 1), (key1292, 1), (key1593, 1), (key1298, 1), (key1683, -1), (key1472, -1), (key1689, -1), (key1351, -1), (key1480, -1), (key1354, -1), (key1575, -2), (key1593, -2), (key1298, -2), (key1624, 1), (key1426, 1), (key1633, 1), (key1318, 1), (key1444, 1), (key1326, 1)]

theorem rawRowCheck4166 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form15 = rawRow4166 := by decide +kernel

def row4166 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

theorem rowCheck4166 : row4166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4166 := by decide +kernel

theorem rowEval4166 (x : Key → ℝ) : Integer.Sparse.eval row4166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4166, Integer.Sparse.eval_collectBalanced, rawRowCheck4166]

def rawRow4167 : Integer.Sparse Key := [(key1633, -1), (key1926, -1), (key1318, -1), (key1918, -1), (key1312, -1), (key1618, -1), (key1689, 2), (key1351, 2), (key1681, 2), (key1593, 1), (key1911, 1), (key1298, 1), (key1903, 1), (key1292, 1), (key1569, 1), (key1480, -1), (key1689, -1), (key1354, -1), (key1683, -1), (key1351, -1), (key1472, -1), (key1593, -2), (key1298, -2), (key1575, -2), (key1444, 1), (key1633, 1), (key1326, 1), (key1624, 1), (key1318, 1), (key1426, 1)]

theorem rawRowCheck4167 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form15 = rawRow4167 := by decide +kernel

def row4167 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

theorem rowCheck4167 : row4167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4167 := by decide +kernel

theorem rowEval4167 (x : Key → ℝ) : Integer.Sparse.eval row4167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4167, Integer.Sparse.eval_collectBalanced, rawRowCheck4167]

def rawRow4168 : Integer.Sparse Key := [(key1926, -1), (key1633, -1), (key1918, -1), (key1318, -1), (key1618, -1), (key1312, -1), (key1689, 2), (key1681, 2), (key1351, 2), (key1911, 1), (key1593, 1), (key1903, 1), (key1298, 1), (key1569, 1), (key1292, 1), (key1689, -1), (key1480, -1), (key1683, -1), (key1354, -1), (key1472, -1), (key1351, -1), (key1593, -2), (key1575, -2), (key1298, -2), (key1633, 1), (key1444, 1), (key1624, 1), (key1326, 1), (key1426, 1), (key1318, 1)]

theorem rawRowCheck4168 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form15 = rawRow4168 := by decide +kernel

def row4168 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

theorem rowCheck4168 : row4168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4168 := by decide +kernel

theorem rowEval4168 (x : Key → ℝ) : Integer.Sparse.eval row4168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4168, Integer.Sparse.eval_collectBalanced, rawRowCheck4168]

def rawRow4169 : Integer.Sparse Key := [(key1318, -1), (key1351, -1), (key1548, -1), (key1681, -1), (key1896, -1), (key1918, -1), (key1312, 2), (key1542, 2), (key1618, 2), (key1326, 1), (key1354, 1), (key1556, 1), (key1683, 1), (key1899, 1), (key1920, 1), (key1292, -1), (key1312, -1), (key1387, -1), (key1420, -1), (key1542, -1), (key1569, -1), (key1326, -2), (key1556, -2), (key1624, -2), (key1298, 1), (key1318, 1), (key1393, 1), (key1426, 1), (key1548, 1), (key1575, 1)]

theorem rawRowCheck4169 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form15 = rawRow4169 := by decide +kernel

def row4169 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

theorem rowCheck4169 : row4169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4169 := by decide +kernel

theorem rowEval4169 (x : Key → ℝ) : Integer.Sparse.eval row4169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4169, Integer.Sparse.eval_collectBalanced, rawRowCheck4169]

def rawRow4170 : Integer.Sparse Key := [(key1351, -1), (key1318, -1), (key1681, -1), (key1548, -1), (key1918, -1), (key1896, -1), (key1312, 2), (key1618, 2), (key1542, 2), (key1354, 1), (key1326, 1), (key1683, 1), (key1556, 1), (key1920, 1), (key1899, 1), (key1312, -1), (key1292, -1), (key1420, -1), (key1387, -1), (key1569, -1), (key1542, -1), (key1326, -2), (key1624, -2), (key1556, -2), (key1318, 1), (key1298, 1), (key1426, 1), (key1393, 1), (key1575, 1), (key1548, 1)]

theorem rawRowCheck4170 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form15 = rawRow4170 := by decide +kernel

def row4170 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

theorem rowCheck4170 : row4170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4170 := by decide +kernel

theorem rowEval4170 (x : Key → ℝ) : Integer.Sparse.eval row4170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4170, Integer.Sparse.eval_collectBalanced, rawRowCheck4170]

def rawRow4171 : Integer.Sparse Key := [(key1548, -1), (key1896, -1), (key1318, -1), (key1918, -1), (key1351, -1), (key1681, -1), (key1542, 2), (key1312, 2), (key1618, 2), (key1556, 1), (key1899, 1), (key1326, 1), (key1920, 1), (key1354, 1), (key1683, 1), (key1387, -1), (key1542, -1), (key1292, -1), (key1569, -1), (key1312, -1), (key1420, -1), (key1556, -2), (key1326, -2), (key1624, -2), (key1393, 1), (key1548, 1), (key1298, 1), (key1575, 1), (key1318, 1), (key1426, 1)]

theorem rawRowCheck4171 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form15 = rawRow4171 := by decide +kernel

def row4171 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

theorem rowCheck4171 : row4171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4171 := by decide +kernel

theorem rowEval4171 (x : Key → ℝ) : Integer.Sparse.eval row4171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4171, Integer.Sparse.eval_collectBalanced, rawRowCheck4171]

def rawRow4172 : Integer.Sparse Key := [(key1896, -1), (key1548, -1), (key1918, -1), (key1318, -1), (key1681, -1), (key1351, -1), (key1542, 2), (key1618, 2), (key1312, 2), (key1899, 1), (key1556, 1), (key1920, 1), (key1326, 1), (key1683, 1), (key1354, 1), (key1542, -1), (key1387, -1), (key1569, -1), (key1292, -1), (key1420, -1), (key1312, -1), (key1556, -2), (key1624, -2), (key1326, -2), (key1548, 1), (key1393, 1), (key1575, 1), (key1298, 1), (key1426, 1), (key1318, 1)]

theorem rawRowCheck4172 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form15 = rawRow4172 := by decide +kernel

def row4172 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

theorem rowCheck4172 : row4172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4172 := by decide +kernel

theorem rowEval4172 (x : Key → ℝ) : Integer.Sparse.eval row4172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4172, Integer.Sparse.eval_collectBalanced, rawRowCheck4172]

def rawRow4173 : Integer.Sparse Key := [(key1681, -1), (key1918, -1), (key1351, -1), (key1896, -1), (key1318, -1), (key1548, -1), (key1618, 2), (key1312, 2), (key1542, 2), (key1683, 1), (key1920, 1), (key1354, 1), (key1899, 1), (key1326, 1), (key1556, 1), (key1420, -1), (key1569, -1), (key1312, -1), (key1542, -1), (key1292, -1), (key1387, -1), (key1624, -2), (key1326, -2), (key1556, -2), (key1426, 1), (key1575, 1), (key1318, 1), (key1548, 1), (key1298, 1), (key1393, 1)]

theorem rawRowCheck4173 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form15 = rawRow4173 := by decide +kernel

def row4173 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

theorem rowCheck4173 : row4173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4173 := by decide +kernel

theorem rowEval4173 (x : Key → ℝ) : Integer.Sparse.eval row4173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4173, Integer.Sparse.eval_collectBalanced, rawRowCheck4173]

def rawRow4174 : Integer.Sparse Key := [(key1918, -1), (key1681, -1), (key1896, -1), (key1351, -1), (key1548, -1), (key1318, -1), (key1618, 2), (key1542, 2), (key1312, 2), (key1920, 1), (key1683, 1), (key1899, 1), (key1354, 1), (key1556, 1), (key1326, 1), (key1569, -1), (key1420, -1), (key1542, -1), (key1312, -1), (key1387, -1), (key1292, -1), (key1624, -2), (key1556, -2), (key1326, -2), (key1575, 1), (key1426, 1), (key1548, 1), (key1318, 1), (key1393, 1), (key1298, 1)]

theorem rawRowCheck4174 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form15 = rawRow4174 := by decide +kernel

def row4174 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

theorem rowCheck4174 : row4174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4174 := by decide +kernel

theorem rowEval4174 (x : Key → ℝ) : Integer.Sparse.eval row4174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4174, Integer.Sparse.eval_collectBalanced, rawRowCheck4174]

def rawRow4175 : Integer.Sparse Key := [(key1326, -1), (key1326, -1), (key1624, -1), (key1624, -1), (key1920, -1), (key1920, -1), (key1354, 2), (key1683, 2), (key1683, 2), (key1298, 1), (key1298, 1), (key1575, 1), (key1575, 1), (key1903, 1), (key1903, 1), (key1351, -1), (key1351, -1), (key1472, -1), (key1472, -1), (key1681, -1), (key1681, -1), (key1292, -2), (key1569, -2), (key1569, -2), (key1312, 1), (key1312, 1), (key1420, 1), (key1420, 1), (key1618, 1), (key1618, 1)]

theorem rawRowCheck4175 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form15 = rawRow4175 := by decide +kernel

def row4175 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

theorem rowCheck4175 : row4175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4175 := by decide +kernel

theorem rowEval4175 (x : Key → ℝ) : Integer.Sparse.eval row4175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4175, Integer.Sparse.eval_collectBalanced, rawRowCheck4175]

def rawRow4176 : Integer.Sparse Key := [(key1624, -1), (key1920, -1), (key1326, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1683, 2), (key1354, 2), (key1683, 2), (key1575, 1), (key1903, 1), (key1298, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1472, -1), (key1681, -1), (key1351, -1), (key1681, -1), (key1351, -1), (key1472, -1), (key1569, -2), (key1292, -2), (key1569, -2), (key1420, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1420, 1)]

theorem rawRowCheck4176 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form15 = rawRow4176 := by decide +kernel

def row4176 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

theorem rowCheck4176 : row4176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4176 := by decide +kernel

theorem rowEval4176 (x : Key → ℝ) : Integer.Sparse.eval row4176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4176, Integer.Sparse.eval_collectBalanced, rawRowCheck4176]

def rawRow4177 : Integer.Sparse Key := [(key1920, -1), (key1624, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1326, -1), (key1683, 2), (key1683, 2), (key1354, 2), (key1903, 1), (key1575, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1298, 1), (key1681, -1), (key1472, -1), (key1681, -1), (key1351, -1), (key1472, -1), (key1351, -1), (key1569, -2), (key1569, -2), (key1292, -2), (key1618, 1), (key1420, 1), (key1618, 1), (key1312, 1), (key1420, 1), (key1312, 1)]

theorem rawRowCheck4177 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form15 = rawRow4177 := by decide +kernel

def row4177 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

theorem rowCheck4177 : row4177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4177 := by decide +kernel

theorem rowEval4177 (x : Key → ℝ) : Integer.Sparse.eval row4177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4177, Integer.Sparse.eval_collectBalanced, rawRowCheck4177]

def rawRow4178 : Integer.Sparse Key := [(key1326, -1), (key1354, -1), (key1556, -1), (key1683, -1), (key1899, -1), (key1920, -1), (key1326, 2), (key1556, 2), (key1624, 2), (key1318, 1), (key1351, 1), (key1548, 1), (key1681, 1), (key1896, 1), (key1918, 1), (key1298, -1), (key1318, -1), (key1393, -1), (key1426, -1), (key1548, -1), (key1575, -1), (key1312, -2), (key1542, -2), (key1618, -2), (key1292, 1), (key1312, 1), (key1387, 1), (key1420, 1), (key1542, 1), (key1569, 1)]

theorem rawRowCheck4178 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form15 = rawRow4178 := by decide +kernel

def row4178 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

theorem rowCheck4178 : row4178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4178 := by decide +kernel

theorem rowEval4178 (x : Key → ℝ) : Integer.Sparse.eval row4178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4178, Integer.Sparse.eval_collectBalanced, rawRowCheck4178]

def rawRow4179 : Integer.Sparse Key := [(key1354, -1), (key1326, -1), (key1683, -1), (key1556, -1), (key1920, -1), (key1899, -1), (key1326, 2), (key1624, 2), (key1556, 2), (key1351, 1), (key1318, 1), (key1681, 1), (key1548, 1), (key1918, 1), (key1896, 1), (key1318, -1), (key1298, -1), (key1426, -1), (key1393, -1), (key1575, -1), (key1548, -1), (key1312, -2), (key1618, -2), (key1542, -2), (key1312, 1), (key1292, 1), (key1420, 1), (key1387, 1), (key1569, 1), (key1542, 1)]

theorem rawRowCheck4179 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form15 = rawRow4179 := by decide +kernel

def row4179 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

theorem rowCheck4179 : row4179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4179 := by decide +kernel

theorem rowEval4179 (x : Key → ℝ) : Integer.Sparse.eval row4179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4179, Integer.Sparse.eval_collectBalanced, rawRowCheck4179]

def rawRow4180 : Integer.Sparse Key := [(key1556, -1), (key1899, -1), (key1326, -1), (key1920, -1), (key1354, -1), (key1683, -1), (key1556, 2), (key1326, 2), (key1624, 2), (key1548, 1), (key1896, 1), (key1318, 1), (key1918, 1), (key1351, 1), (key1681, 1), (key1393, -1), (key1548, -1), (key1298, -1), (key1575, -1), (key1318, -1), (key1426, -1), (key1542, -2), (key1312, -2), (key1618, -2), (key1387, 1), (key1542, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1420, 1)]

theorem rawRowCheck4180 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form15 = rawRow4180 := by decide +kernel

def row4180 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

theorem rowCheck4180 : row4180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4180 := by decide +kernel

theorem rowEval4180 (x : Key → ℝ) : Integer.Sparse.eval row4180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form15) x := by
  rw [rowCheck4180, Integer.Sparse.eval_collectBalanced, rawRowCheck4180]

def rawRow4181 : Integer.Sparse Key := [(key1899, -1), (key1556, -1), (key1920, -1), (key1326, -1), (key1683, -1), (key1354, -1), (key1556, 2), (key1624, 2), (key1326, 2), (key1896, 1), (key1548, 1), (key1918, 1), (key1318, 1), (key1681, 1), (key1351, 1), (key1548, -1), (key1393, -1), (key1575, -1), (key1298, -1), (key1426, -1), (key1318, -1), (key1542, -2), (key1618, -2), (key1312, -2), (key1542, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1420, 1), (key1312, 1)]

theorem rawRowCheck4181 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form15 = rawRow4181 := by decide +kernel

def row4181 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

theorem rowCheck4181 : row4181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4181 := by decide +kernel

theorem rowEval4181 (x : Key → ℝ) : Integer.Sparse.eval row4181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4181, Integer.Sparse.eval_collectBalanced, rawRowCheck4181]

def rawRow4182 : Integer.Sparse Key := [(key1683, -1), (key1920, -1), (key1354, -1), (key1899, -1), (key1326, -1), (key1556, -1), (key1624, 2), (key1326, 2), (key1556, 2), (key1681, 1), (key1918, 1), (key1351, 1), (key1896, 1), (key1318, 1), (key1548, 1), (key1426, -1), (key1575, -1), (key1318, -1), (key1548, -1), (key1298, -1), (key1393, -1), (key1618, -2), (key1312, -2), (key1542, -2), (key1420, 1), (key1569, 1), (key1312, 1), (key1542, 1), (key1292, 1), (key1387, 1)]

theorem rawRowCheck4182 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form15 = rawRow4182 := by decide +kernel

def row4182 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

theorem rowCheck4182 : row4182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4182 := by decide +kernel

theorem rowEval4182 (x : Key → ℝ) : Integer.Sparse.eval row4182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form15) x := by
  rw [rowCheck4182, Integer.Sparse.eval_collectBalanced, rawRowCheck4182]

def rawRow4183 : Integer.Sparse Key := [(key1920, -1), (key1683, -1), (key1899, -1), (key1354, -1), (key1556, -1), (key1326, -1), (key1624, 2), (key1556, 2), (key1326, 2), (key1918, 1), (key1681, 1), (key1896, 1), (key1351, 1), (key1548, 1), (key1318, 1), (key1575, -1), (key1426, -1), (key1548, -1), (key1318, -1), (key1393, -1), (key1298, -1), (key1618, -2), (key1542, -2), (key1312, -2), (key1569, 1), (key1420, 1), (key1542, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

theorem rawRowCheck4183 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form15 = rawRow4183 := by decide +kernel

def row4183 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

theorem rowCheck4183 : row4183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4183 := by decide +kernel

theorem rowEval4183 (x : Key → ℝ) : Integer.Sparse.eval row4183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form15) x := by
  rw [rowCheck4183, Integer.Sparse.eval_collectBalanced, rawRowCheck4183]

def rawRow4184 : Integer.Sparse Key := [(key1541, -2), (key1545, -2), (key1771, -2), (key1390, 2), (key1545, 2), (key1554, 2), (key1568, 2), (key1572, 2), (key1787, 2), (key1295, -2), (key1572, -2), (key1591, -2), (key1454, -2), (key1654, -2), (key1657, -2), (key1336, 2), (key1654, 2), (key1665, 2)]

theorem rawRowCheck4184 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form16 = rawRow4184 := by decide +kernel

def row4184 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

theorem rowCheck4184 : row4184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4184 := by decide +kernel

theorem rowEval4184 (x : Key → ℝ) : Integer.Sparse.eval row4184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4184, Integer.Sparse.eval_collectBalanced, rawRowCheck4184]

def rawRow4185 : Integer.Sparse Key := [(key1545, -2), (key1541, -2), (key1771, -2), (key1390, 2), (key1554, 2), (key1545, 2), (key1572, 2), (key1568, 2), (key1787, 2), (key1295, -2), (key1591, -2), (key1572, -2), (key1454, -2), (key1657, -2), (key1654, -2), (key1336, 2), (key1665, 2), (key1654, 2)]

theorem rawRowCheck4185 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form16 = rawRow4185 := by decide +kernel

def row4185 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

theorem rowCheck4185 : row4185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4185 := by decide +kernel

theorem rowEval4185 (x : Key → ℝ) : Integer.Sparse.eval row4185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4185, Integer.Sparse.eval_collectBalanced, rawRowCheck4185]

def rawRow4186 : Integer.Sparse Key := [(key1541, -2), (key1771, -2), (key1545, -2), (key1545, 2), (key1390, 2), (key1554, 2), (key1568, 2), (key1787, 2), (key1572, 2), (key1572, -2), (key1295, -2), (key1591, -2), (key1654, -2), (key1454, -2), (key1657, -2), (key1654, 2), (key1336, 2), (key1665, 2)]

theorem rawRowCheck4186 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form16 = rawRow4186 := by decide +kernel

def row4186 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

theorem rowCheck4186 : row4186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4186 := by decide +kernel

theorem rowEval4186 (x : Key → ℝ) : Integer.Sparse.eval row4186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4186, Integer.Sparse.eval_collectBalanced, rawRowCheck4186]

def rawRow4187 : Integer.Sparse Key := [(key1771, -2), (key1541, -2), (key1545, -2), (key1545, 2), (key1554, 2), (key1390, 2), (key1787, 2), (key1568, 2), (key1572, 2), (key1572, -2), (key1591, -2), (key1295, -2), (key1654, -2), (key1657, -2), (key1454, -2), (key1654, 2), (key1665, 2), (key1336, 2)]

theorem rawRowCheck4187 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form16 = rawRow4187 := by decide +kernel

def row4187 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

theorem rowCheck4187 : row4187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4187 := by decide +kernel

theorem rowEval4187 (x : Key → ℝ) : Integer.Sparse.eval row4187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4187, Integer.Sparse.eval_collectBalanced, rawRowCheck4187]

def rawRow4188 : Integer.Sparse Key := [(key1545, -2), (key1771, -2), (key1541, -2), (key1554, 2), (key1390, 2), (key1545, 2), (key1572, 2), (key1787, 2), (key1568, 2), (key1591, -2), (key1295, -2), (key1572, -2), (key1657, -2), (key1454, -2), (key1654, -2), (key1665, 2), (key1336, 2), (key1654, 2)]

theorem rawRowCheck4188 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form16 = rawRow4188 := by decide +kernel

def row4188 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

theorem rowCheck4188 : row4188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4188 := by decide +kernel

theorem rowEval4188 (x : Key → ℝ) : Integer.Sparse.eval row4188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4188, Integer.Sparse.eval_collectBalanced, rawRowCheck4188]

def rawRow4189 : Integer.Sparse Key := [(key1771, -2), (key1545, -2), (key1541, -2), (key1554, 2), (key1545, 2), (key1390, 2), (key1787, 2), (key1572, 2), (key1568, 2), (key1591, -2), (key1572, -2), (key1295, -2), (key1657, -2), (key1654, -2), (key1454, -2), (key1665, 2), (key1654, 2), (key1336, 2)]

theorem rawRowCheck4189 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form16 = rawRow4189 := by decide +kernel

def row4189 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

theorem rowCheck4189 : row4189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4189 := by decide +kernel

theorem rowEval4189 (x : Key → ℝ) : Integer.Sparse.eval row4189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4189, Integer.Sparse.eval_collectBalanced, rawRowCheck4189]

def rawRow4190 : Integer.Sparse Key := [(key1554, -2), (key1554, -2), (key1778, -2), (key1386, 2), (key1541, 2), (key1541, 2), (key1591, 2), (key1591, 2), (key1796, 2), (key1291, -2), (key1568, -2), (key1568, -2), (key1464, -2), (key1665, -2), (key1665, -2), (key1343, 2), (key1657, 2), (key1657, 2)]

theorem rawRowCheck4190 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4190 := by decide +kernel

def row4190 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

theorem rowCheck4190 : row4190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4190 := by decide +kernel

theorem rowEval4190 (x : Key → ℝ) : Integer.Sparse.eval row4190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4190, Integer.Sparse.eval_collectBalanced, rawRowCheck4190]

def rawRow4191 : Integer.Sparse Key := [(key1554, -2), (key1778, -2), (key1554, -2), (key1541, 2), (key1386, 2), (key1541, 2), (key1591, 2), (key1796, 2), (key1591, 2), (key1568, -2), (key1291, -2), (key1568, -2), (key1665, -2), (key1464, -2), (key1665, -2), (key1657, 2), (key1343, 2), (key1657, 2)]

theorem rawRowCheck4191 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4191 := by decide +kernel

def row4191 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

theorem rowCheck4191 : row4191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4191 := by decide +kernel

theorem rowEval4191 (x : Key → ℝ) : Integer.Sparse.eval row4191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4191, Integer.Sparse.eval_collectBalanced, rawRowCheck4191]

def rawRow4192 : Integer.Sparse Key := [(key1778, -2), (key1554, -2), (key1554, -2), (key1541, 2), (key1541, 2), (key1386, 2), (key1796, 2), (key1591, 2), (key1591, 2), (key1568, -2), (key1568, -2), (key1291, -2), (key1665, -2), (key1665, -2), (key1464, -2), (key1657, 2), (key1657, 2), (key1343, 2)]

theorem rawRowCheck4192 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4192 := by decide +kernel

def row4192 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

theorem rowCheck4192 : row4192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4192 := by decide +kernel

theorem rowEval4192 (x : Key → ℝ) : Integer.Sparse.eval row4192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4192, Integer.Sparse.eval_collectBalanced, rawRowCheck4192]

def rawRow4193 : Integer.Sparse Key := [(key1568, -2), (key1572, -2), (key1787, -2), (key1454, 2), (key1654, 2), (key1657, 2), (key1541, 2), (key1545, 2), (key1771, 2), (key1336, -2), (key1654, -2), (key1665, -2), (key1390, -2), (key1545, -2), (key1554, -2), (key1295, 2), (key1572, 2), (key1591, 2)]

theorem rawRowCheck4193 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form16 = rawRow4193 := by decide +kernel

def row4193 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

theorem rowCheck4193 : row4193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4193 := by decide +kernel

theorem rowEval4193 (x : Key → ℝ) : Integer.Sparse.eval row4193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4193, Integer.Sparse.eval_collectBalanced, rawRowCheck4193]

def rawRow4194 : Integer.Sparse Key := [(key1572, -2), (key1568, -2), (key1787, -2), (key1454, 2), (key1657, 2), (key1654, 2), (key1545, 2), (key1541, 2), (key1771, 2), (key1336, -2), (key1665, -2), (key1654, -2), (key1390, -2), (key1554, -2), (key1545, -2), (key1295, 2), (key1591, 2), (key1572, 2)]

theorem rawRowCheck4194 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form16 = rawRow4194 := by decide +kernel

def row4194 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

theorem rowCheck4194 : row4194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4194 := by decide +kernel

theorem rowEval4194 (x : Key → ℝ) : Integer.Sparse.eval row4194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4194, Integer.Sparse.eval_collectBalanced, rawRowCheck4194]

def rawRow4195 : Integer.Sparse Key := [(key1568, -2), (key1787, -2), (key1572, -2), (key1654, 2), (key1454, 2), (key1657, 2), (key1541, 2), (key1771, 2), (key1545, 2), (key1654, -2), (key1336, -2), (key1665, -2), (key1545, -2), (key1390, -2), (key1554, -2), (key1572, 2), (key1295, 2), (key1591, 2)]

theorem rawRowCheck4195 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form16 = rawRow4195 := by decide +kernel

def row4195 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

theorem rowCheck4195 : row4195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4195 := by decide +kernel

theorem rowEval4195 (x : Key → ℝ) : Integer.Sparse.eval row4195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4195, Integer.Sparse.eval_collectBalanced, rawRowCheck4195]

def rawRow4196 : Integer.Sparse Key := [(key1787, -2), (key1568, -2), (key1572, -2), (key1654, 2), (key1657, 2), (key1454, 2), (key1771, 2), (key1541, 2), (key1545, 2), (key1654, -2), (key1665, -2), (key1336, -2), (key1545, -2), (key1554, -2), (key1390, -2), (key1572, 2), (key1591, 2), (key1295, 2)]

theorem rawRowCheck4196 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form16 = rawRow4196 := by decide +kernel

def row4196 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

theorem rowCheck4196 : row4196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4196 := by decide +kernel

theorem rowEval4196 (x : Key → ℝ) : Integer.Sparse.eval row4196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4196, Integer.Sparse.eval_collectBalanced, rawRowCheck4196]

def rawRow4197 : Integer.Sparse Key := [(key1572, -2), (key1787, -2), (key1568, -2), (key1657, 2), (key1454, 2), (key1654, 2), (key1545, 2), (key1771, 2), (key1541, 2), (key1665, -2), (key1336, -2), (key1654, -2), (key1554, -2), (key1390, -2), (key1545, -2), (key1591, 2), (key1295, 2), (key1572, 2)]

theorem rawRowCheck4197 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form16 = rawRow4197 := by decide +kernel

def row4197 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

theorem rowCheck4197 : row4197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4197 := by decide +kernel

theorem rowEval4197 (x : Key → ℝ) : Integer.Sparse.eval row4197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4197, Integer.Sparse.eval_collectBalanced, rawRowCheck4197]

def rawRow4198 : Integer.Sparse Key := [(key1787, -2), (key1572, -2), (key1568, -2), (key1657, 2), (key1654, 2), (key1454, 2), (key1771, 2), (key1545, 2), (key1541, 2), (key1665, -2), (key1654, -2), (key1336, -2), (key1554, -2), (key1545, -2), (key1390, -2), (key1591, 2), (key1572, 2), (key1295, 2)]

theorem rawRowCheck4198 : GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form16 = rawRow4198 := by decide +kernel

def row4198 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

theorem rowCheck4198 : row4198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4198 := by decide +kernel

theorem rowEval4198 (x : Key → ℝ) : Integer.Sparse.eval row4198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4198, Integer.Sparse.eval_collectBalanced, rawRowCheck4198]

def rawRow4199 : Integer.Sparse Key := [(key1622, -2), (key1657, -2), (key1815, -2), (key1419, 2), (key1568, 2), (key1617, 2), (key1631, 2), (key1665, 2), (key1823, 2), (key1311, -2), (key1541, -2), (key1617, -2), (key1442, -2), (key1591, -2), (key1631, -2), (key1324, 2), (key1554, 2), (key1622, 2)]

theorem rawRowCheck4199 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form16 = rawRow4199 := by decide +kernel

def row4199 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

theorem rowCheck4199 : row4199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4199 := by decide +kernel

theorem rowEval4199 (x : Key → ℝ) : Integer.Sparse.eval row4199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4199, Integer.Sparse.eval_collectBalanced, rawRowCheck4199]

def rawRow4200 : Integer.Sparse Key := [(key1657, -2), (key1622, -2), (key1815, -2), (key1419, 2), (key1617, 2), (key1568, 2), (key1665, 2), (key1631, 2), (key1823, 2), (key1311, -2), (key1617, -2), (key1541, -2), (key1442, -2), (key1631, -2), (key1591, -2), (key1324, 2), (key1622, 2), (key1554, 2)]

theorem rawRowCheck4200 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form16 = rawRow4200 := by decide +kernel

def row4200 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

theorem rowCheck4200 : row4200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4200 := by decide +kernel

theorem rowEval4200 (x : Key → ℝ) : Integer.Sparse.eval row4200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4200, Integer.Sparse.eval_collectBalanced, rawRowCheck4200]

def rawRow4201 : Integer.Sparse Key := [(key1622, -2), (key1815, -2), (key1657, -2), (key1568, 2), (key1419, 2), (key1617, 2), (key1631, 2), (key1823, 2), (key1665, 2), (key1541, -2), (key1311, -2), (key1617, -2), (key1591, -2), (key1442, -2), (key1631, -2), (key1554, 2), (key1324, 2), (key1622, 2)]

theorem rawRowCheck4201 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form16 = rawRow4201 := by decide +kernel

def row4201 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

theorem rowCheck4201 : row4201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4201 := by decide +kernel

theorem rowEval4201 (x : Key → ℝ) : Integer.Sparse.eval row4201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4201, Integer.Sparse.eval_collectBalanced, rawRowCheck4201]

def rawRow4202 : Integer.Sparse Key := [(key1815, -2), (key1622, -2), (key1657, -2), (key1568, 2), (key1617, 2), (key1419, 2), (key1823, 2), (key1631, 2), (key1665, 2), (key1541, -2), (key1617, -2), (key1311, -2), (key1591, -2), (key1631, -2), (key1442, -2), (key1554, 2), (key1622, 2), (key1324, 2)]

theorem rawRowCheck4202 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form16 = rawRow4202 := by decide +kernel

def row4202 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

theorem rowCheck4202 : row4202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4202 := by decide +kernel

theorem rowEval4202 (x : Key → ℝ) : Integer.Sparse.eval row4202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4202, Integer.Sparse.eval_collectBalanced, rawRowCheck4202]

def rawRow4203 : Integer.Sparse Key := [(key1657, -2), (key1815, -2), (key1622, -2), (key1617, 2), (key1419, 2), (key1568, 2), (key1665, 2), (key1823, 2), (key1631, 2), (key1617, -2), (key1311, -2), (key1541, -2), (key1631, -2), (key1442, -2), (key1591, -2), (key1622, 2), (key1324, 2), (key1554, 2)]

theorem rawRowCheck4203 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form16 = rawRow4203 := by decide +kernel

def row4203 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

theorem rowCheck4203 : row4203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4203 := by decide +kernel

theorem rowEval4203 (x : Key → ℝ) : Integer.Sparse.eval row4203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4203, Integer.Sparse.eval_collectBalanced, rawRowCheck4203]

def rawRow4204 : Integer.Sparse Key := [(key1815, -2), (key1657, -2), (key1622, -2), (key1617, 2), (key1568, 2), (key1419, 2), (key1823, 2), (key1665, 2), (key1631, 2), (key1617, -2), (key1541, -2), (key1311, -2), (key1631, -2), (key1591, -2), (key1442, -2), (key1622, 2), (key1554, 2), (key1324, 2)]

theorem rawRowCheck4204 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form16 = rawRow4204 := by decide +kernel

def row4204 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

theorem rowCheck4204 : row4204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4204 := by decide +kernel

theorem rowEval4204 (x : Key → ℝ) : Integer.Sparse.eval row4204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4204, Integer.Sparse.eval_collectBalanced, rawRowCheck4204]

def rawRow4205 : Integer.Sparse Key := [(key1591, -2), (key1591, -2), (key1796, -2), (key1464, 2), (key1665, 2), (key1665, 2), (key1554, 2), (key1554, 2), (key1778, 2), (key1343, -2), (key1657, -2), (key1657, -2), (key1386, -2), (key1541, -2), (key1541, -2), (key1291, 2), (key1568, 2), (key1568, 2)]

theorem rawRowCheck4205 : GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form16 = rawRow4205 := by decide +kernel

def row4205 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

theorem rowCheck4205 : row4205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4205 := by decide +kernel

theorem rowEval4205 (x : Key → ℝ) : Integer.Sparse.eval row4205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4205, Integer.Sparse.eval_collectBalanced, rawRowCheck4205]

def rawRow4206 : Integer.Sparse Key := [(key1591, -2), (key1796, -2), (key1591, -2), (key1665, 2), (key1464, 2), (key1665, 2), (key1554, 2), (key1778, 2), (key1554, 2), (key1657, -2), (key1343, -2), (key1657, -2), (key1541, -2), (key1386, -2), (key1541, -2), (key1568, 2), (key1291, 2), (key1568, 2)]

theorem rawRowCheck4206 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form16 = rawRow4206 := by decide +kernel

def row4206 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

theorem rowCheck4206 : row4206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4206 := by decide +kernel

theorem rowEval4206 (x : Key → ℝ) : Integer.Sparse.eval row4206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4206, Integer.Sparse.eval_collectBalanced, rawRowCheck4206]

def rawRow4207 : Integer.Sparse Key := [(key1796, -2), (key1591, -2), (key1591, -2), (key1665, 2), (key1665, 2), (key1464, 2), (key1778, 2), (key1554, 2), (key1554, 2), (key1657, -2), (key1657, -2), (key1343, -2), (key1541, -2), (key1541, -2), (key1386, -2), (key1568, 2), (key1568, 2), (key1291, 2)]

theorem rawRowCheck4207 : GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form16 = rawRow4207 := by decide +kernel

def row4207 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

theorem rowCheck4207 : row4207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4207 := by decide +kernel

theorem rowEval4207 (x : Key → ℝ) : Integer.Sparse.eval row4207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4207, Integer.Sparse.eval_collectBalanced, rawRowCheck4207]

def rawRow4208 : Integer.Sparse Key := [(key1631, -2), (key1665, -2), (key1823, -2), (key1442, 2), (key1591, 2), (key1631, 2), (key1622, 2), (key1657, 2), (key1815, 2), (key1324, -2), (key1554, -2), (key1622, -2), (key1419, -2), (key1568, -2), (key1617, -2), (key1311, 2), (key1541, 2), (key1617, 2)]

theorem rawRowCheck4208 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form16 = rawRow4208 := by decide +kernel

def row4208 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

theorem rowCheck4208 : row4208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4208 := by decide +kernel

theorem rowEval4208 (x : Key → ℝ) : Integer.Sparse.eval row4208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4208, Integer.Sparse.eval_collectBalanced, rawRowCheck4208]

def rawRow4209 : Integer.Sparse Key := [(key1665, -2), (key1631, -2), (key1823, -2), (key1442, 2), (key1631, 2), (key1591, 2), (key1657, 2), (key1622, 2), (key1815, 2), (key1324, -2), (key1622, -2), (key1554, -2), (key1419, -2), (key1617, -2), (key1568, -2), (key1311, 2), (key1617, 2), (key1541, 2)]

theorem rawRowCheck4209 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form16 = rawRow4209 := by decide +kernel

def row4209 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

theorem rowCheck4209 : row4209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4209 := by decide +kernel

theorem rowEval4209 (x : Key → ℝ) : Integer.Sparse.eval row4209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4209, Integer.Sparse.eval_collectBalanced, rawRowCheck4209]

def rawRow4210 : Integer.Sparse Key := [(key1631, -2), (key1823, -2), (key1665, -2), (key1591, 2), (key1442, 2), (key1631, 2), (key1622, 2), (key1815, 2), (key1657, 2), (key1554, -2), (key1324, -2), (key1622, -2), (key1568, -2), (key1419, -2), (key1617, -2), (key1541, 2), (key1311, 2), (key1617, 2)]

theorem rawRowCheck4210 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form16 = rawRow4210 := by decide +kernel

def row4210 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

theorem rowCheck4210 : row4210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4210 := by decide +kernel

theorem rowEval4210 (x : Key → ℝ) : Integer.Sparse.eval row4210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4210, Integer.Sparse.eval_collectBalanced, rawRowCheck4210]

def rawRow4211 : Integer.Sparse Key := [(key1823, -2), (key1631, -2), (key1665, -2), (key1591, 2), (key1631, 2), (key1442, 2), (key1815, 2), (key1622, 2), (key1657, 2), (key1554, -2), (key1622, -2), (key1324, -2), (key1568, -2), (key1617, -2), (key1419, -2), (key1541, 2), (key1617, 2), (key1311, 2)]

theorem rawRowCheck4211 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form16 = rawRow4211 := by decide +kernel

def row4211 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

theorem rowCheck4211 : row4211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4211 := by decide +kernel

theorem rowEval4211 (x : Key → ℝ) : Integer.Sparse.eval row4211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4211, Integer.Sparse.eval_collectBalanced, rawRowCheck4211]

def rawRow4212 : Integer.Sparse Key := [(key1665, -2), (key1823, -2), (key1631, -2), (key1631, 2), (key1442, 2), (key1591, 2), (key1657, 2), (key1815, 2), (key1622, 2), (key1622, -2), (key1324, -2), (key1554, -2), (key1617, -2), (key1419, -2), (key1568, -2), (key1617, 2), (key1311, 2), (key1541, 2)]

theorem rawRowCheck4212 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form16 = rawRow4212 := by decide +kernel

def row4212 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

theorem rowCheck4212 : row4212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4212 := by decide +kernel

theorem rowEval4212 (x : Key → ℝ) : Integer.Sparse.eval row4212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4212, Integer.Sparse.eval_collectBalanced, rawRowCheck4212]

def rawRow4213 : Integer.Sparse Key := [(key1823, -2), (key1665, -2), (key1631, -2), (key1631, 2), (key1591, 2), (key1442, 2), (key1815, 2), (key1657, 2), (key1622, 2), (key1622, -2), (key1554, -2), (key1324, -2), (key1617, -2), (key1568, -2), (key1419, -2), (key1617, 2), (key1541, 2), (key1311, 2)]

theorem rawRowCheck4213 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form16 = rawRow4213 := by decide +kernel

def row4213 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

theorem rowCheck4213 : row4213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4213 := by decide +kernel

theorem rowEval4213 (x : Key → ℝ) : Integer.Sparse.eval row4213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4213, Integer.Sparse.eval_collectBalanced, rawRowCheck4213]

def rawRow4214 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key406, -1), (key418, -1), (key578, -1), (key583, -1), (key239, 2), (key409, 2), (key418, 2), (key248, 1), (key251, 1), (key435, 1), (key450, 1), (key593, 1), (key601, 1), (key251, -1), (key260, -1), (key319, -1), (key328, -1), (key442, -1), (key450, -1), (key267, -2), (key467, -2), (key475, -2), (key267, 1), (key271, 1), (key335, 1), (key340, 1), (key469, 1), (key475, 1)]

theorem rawRowCheck4214 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form17 = rawRow4214 := by decide +kernel

def row4214 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

theorem rowCheck4214 : row4214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4214 := by decide +kernel

theorem rowEval4214 (x : Key → ℝ) : Integer.Sparse.eval row4214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4214, Integer.Sparse.eval_collectBalanced, rawRowCheck4214]

def rawRow4215 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key418, -1), (key406, -1), (key583, -1), (key578, -1), (key239, 2), (key418, 2), (key409, 2), (key251, 1), (key248, 1), (key450, 1), (key435, 1), (key601, 1), (key593, 1), (key260, -1), (key251, -1), (key328, -1), (key319, -1), (key450, -1), (key442, -1), (key267, -2), (key475, -2), (key467, -2), (key271, 1), (key267, 1), (key340, 1), (key335, 1), (key475, 1), (key469, 1)]

theorem rawRowCheck4215 : GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form17 = rawRow4215 := by decide +kernel

def row4215 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

theorem rowCheck4215 : row4215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4215 := by decide +kernel

theorem rowEval4215 (x : Key → ℝ) : Integer.Sparse.eval row4215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4215, Integer.Sparse.eval_collectBalanced, rawRowCheck4215]

def rawRow4216 : Integer.Sparse Key := [(key406, -1), (key418, -1), (key236, -1), (key583, -1), (key239, -1), (key418, -1), (key409, 2), (key239, 2), (key418, 2), (key435, 1), (key593, 1), (key248, 1), (key601, 1), (key251, 1), (key450, 1), (key319, -1), (key442, -1), (key251, -1), (key450, -1), (key260, -1), (key328, -1), (key467, -2), (key267, -2), (key475, -2), (key335, 1), (key469, 1), (key267, 1), (key475, 1), (key271, 1), (key340, 1)]

theorem rawRowCheck4216 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form17 = rawRow4216 := by decide +kernel

def row4216 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key583, -1), (key593, 1), (key601, 1)]

theorem rowCheck4216 : row4216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4216 := by decide +kernel

theorem rowEval4216 (x : Key → ℝ) : Integer.Sparse.eval row4216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4216, Integer.Sparse.eval_collectBalanced, rawRowCheck4216]

def rawRow4217 : Integer.Sparse Key := [(key418, -1), (key406, -1), (key583, -1), (key236, -1), (key418, -1), (key239, -1), (key409, 2), (key418, 2), (key239, 2), (key593, 1), (key435, 1), (key601, 1), (key248, 1), (key450, 1), (key251, 1), (key442, -1), (key319, -1), (key450, -1), (key251, -1), (key328, -1), (key260, -1), (key467, -2), (key475, -2), (key267, -2), (key469, 1), (key335, 1), (key475, 1), (key267, 1), (key340, 1), (key271, 1)]

theorem rawRowCheck4217 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form17 = rawRow4217 := by decide +kernel

def row4217 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key583, -1), (key593, 1), (key601, 1)]

theorem rowCheck4217 : row4217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4217 := by decide +kernel

theorem rowEval4217 (x : Key → ℝ) : Integer.Sparse.eval row4217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4217, Integer.Sparse.eval_collectBalanced, rawRowCheck4217]

def rawRow4218 : Integer.Sparse Key := [(key578, -1), (key583, -1), (key239, -1), (key418, -1), (key236, -1), (key406, -1), (key418, 2), (key239, 2), (key409, 2), (key450, 1), (key601, 1), (key251, 1), (key593, 1), (key248, 1), (key435, 1), (key328, -1), (key450, -1), (key260, -1), (key442, -1), (key251, -1), (key319, -1), (key475, -2), (key267, -2), (key467, -2), (key340, 1), (key475, 1), (key271, 1), (key469, 1), (key267, 1), (key335, 1)]

theorem rawRowCheck4218 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form17 = rawRow4218 := by decide +kernel

def row4218 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

theorem rowCheck4218 : row4218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4218 := by decide +kernel

theorem rowEval4218 (x : Key → ℝ) : Integer.Sparse.eval row4218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4218, Integer.Sparse.eval_collectBalanced, rawRowCheck4218]

def rawRow4219 : Integer.Sparse Key := [(key583, -1), (key578, -1), (key418, -1), (key239, -1), (key406, -1), (key236, -1), (key418, 2), (key409, 2), (key239, 2), (key601, 1), (key450, 1), (key593, 1), (key251, 1), (key435, 1), (key248, 1), (key450, -1), (key328, -1), (key442, -1), (key260, -1), (key319, -1), (key251, -1), (key475, -2), (key467, -2), (key267, -2), (key475, 1), (key340, 1), (key469, 1), (key271, 1), (key335, 1), (key267, 1)]

theorem rawRowCheck4219 : GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form17 = rawRow4219 := by decide +kernel

def row4219 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

theorem rowCheck4219 : row4219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4219 := by decide +kernel

theorem rowEval4219 (x : Key → ℝ) : Integer.Sparse.eval row4219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4219, Integer.Sparse.eval_collectBalanced, rawRowCheck4219]

def rawRow4220 : Integer.Sparse Key := [(key239, -1), (key239, -1), (key409, -1), (key409, -1), (key418, -1), (key418, -1), (key236, 2), (key406, 2), (key406, 2), (key260, 1), (key260, 1), (key442, 1), (key442, 1), (key595, 1), (key595, 1), (key248, -1), (key248, -1), (key316, -1), (key316, -1), (key435, -1), (key435, -1), (key271, -2), (key469, -2), (key469, -2), (key267, 1), (key267, 1), (key335, 1), (key335, 1), (key467, 1), (key467, 1)]

theorem rawRowCheck4220 : GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4220 := by decide +kernel

def row4220 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

theorem rowCheck4220 : row4220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4220 := by decide +kernel

theorem rowEval4220 (x : Key → ℝ) : Integer.Sparse.eval row4220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4220, Integer.Sparse.eval_collectBalanced, rawRowCheck4220]

def rawRow4221 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key239, -1), (key418, -1), (key239, -1), (key409, -1), (key406, 2), (key236, 2), (key406, 2), (key442, 1), (key595, 1), (key260, 1), (key595, 1), (key260, 1), (key442, 1), (key316, -1), (key435, -1), (key248, -1), (key435, -1), (key248, -1), (key316, -1), (key469, -2), (key271, -2), (key469, -2), (key335, 1), (key467, 1), (key267, 1), (key467, 1), (key267, 1), (key335, 1)]

theorem rawRowCheck4221 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4221 := by decide +kernel

def row4221 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

theorem rowCheck4221 : row4221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4221 := by decide +kernel

theorem rowEval4221 (x : Key → ℝ) : Integer.Sparse.eval row4221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4221, Integer.Sparse.eval_collectBalanced, rawRowCheck4221]

def rawRow4222 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key418, -1), (key239, -1), (key409, -1), (key239, -1), (key406, 2), (key406, 2), (key236, 2), (key595, 1), (key442, 1), (key595, 1), (key260, 1), (key442, 1), (key260, 1), (key435, -1), (key316, -1), (key435, -1), (key248, -1), (key316, -1), (key248, -1), (key469, -2), (key469, -2), (key271, -2), (key467, 1), (key335, 1), (key467, 1), (key267, 1), (key335, 1), (key267, 1)]

theorem rawRowCheck4222 : GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4222 := by decide +kernel

def row4222 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

theorem rowCheck4222 : row4222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4222 := by decide +kernel

theorem rowEval4222 (x : Key → ℝ) : Integer.Sparse.eval row4222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4222, Integer.Sparse.eval_collectBalanced, rawRowCheck4222]

def rawRow4223 : Integer.Sparse Key := [(key248, -1), (key251, -1), (key435, -1), (key593, -1), (key450, -1), (key601, -1), (key260, 2), (key442, 2), (key595, 2), (key236, 1), (key239, 1), (key406, 1), (key418, 1), (key578, 1), (key583, 1), (key267, -1), (key271, -1), (key335, -1), (key340, -1), (key469, -1), (key475, -1), (key239, -2), (key409, -2), (key418, -2), (key251, 1), (key260, 1), (key319, 1), (key328, 1), (key442, 1), (key450, 1)]

theorem rawRowCheck4223 : GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form17 = rawRow4223 := by decide +kernel

def row4223 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

theorem rowCheck4223 : row4223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4223 := by decide +kernel

theorem rowEval4223 (x : Key → ℝ) : Integer.Sparse.eval row4223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4223, Integer.Sparse.eval_collectBalanced, rawRowCheck4223]

end MUB6.Certificate.GramRows

end OAI
