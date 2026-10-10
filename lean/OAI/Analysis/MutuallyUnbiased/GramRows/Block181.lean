import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow20096 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key627, 24), (key640, 24), (key629, 24)]

theorem rawRowCheck20096 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form8 = rawRow20096 := by decide +kernel

def row20096 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20096 : row20096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20096 := by decide +kernel

theorem rowEval20096 (x : Key → ℝ) : Integer.Sparse.eval row20096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20096, Integer.Sparse.eval_collectBalanced, rawRowCheck20096]

def rawRow20097 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key627, 24), (key640, 24), (key629, 24)]

theorem rawRowCheck20097 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form8 = rawRow20097 := by decide +kernel

def row20097 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20097 : row20097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20097 := by decide +kernel

theorem rowEval20097 (x : Key → ℝ) : Integer.Sparse.eval row20097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20097, Integer.Sparse.eval_collectBalanced, rawRowCheck20097]

def rawRow20098 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key626, 24), (key640, 24), (key629, 24)]

theorem rawRowCheck20098 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form8 = rawRow20098 := by decide +kernel

def row20098 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20098 : row20098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20098 := by decide +kernel

theorem rowEval20098 (x : Key → ℝ) : Integer.Sparse.eval row20098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20098, Integer.Sparse.eval_collectBalanced, rawRowCheck20098]

def rawRow20099 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key640, 24), (key627, 24), (key629, 24)]

theorem rawRowCheck20099 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form8 = rawRow20099 := by decide +kernel

def row20099 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20099 : row20099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20099 := by decide +kernel

theorem rowEval20099 (x : Key → ℝ) : Integer.Sparse.eval row20099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20099, Integer.Sparse.eval_collectBalanced, rawRowCheck20099]

def rawRow20100 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key640, 24), (key627, 24), (key629, 24)]

theorem rawRowCheck20100 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form8 = rawRow20100 := by decide +kernel

def row20100 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20100 : row20100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20100 := by decide +kernel

theorem rowEval20100 (x : Key → ℝ) : Integer.Sparse.eval row20100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20100, Integer.Sparse.eval_collectBalanced, rawRowCheck20100]

def rawRow20101 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key627, 24), (key627, 24), (key629, 24)]

theorem rawRowCheck20101 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form8 = rawRow20101 := by decide +kernel

def row20101 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20101 : row20101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20101 := by decide +kernel

theorem rowEval20101 (x : Key → ℝ) : Integer.Sparse.eval row20101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20101, Integer.Sparse.eval_collectBalanced, rawRowCheck20101]

def rawRow20102 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key627, 24), (key627, 24), (key629, 24)]

theorem rawRowCheck20102 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form8 = rawRow20102 := by decide +kernel

def row20102 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20102 : row20102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20102 := by decide +kernel

theorem rowEval20102 (x : Key → ℝ) : Integer.Sparse.eval row20102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20102, Integer.Sparse.eval_collectBalanced, rawRowCheck20102]

def rawRow20103 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key626, 24), (key627, 24), (key629, 24)]

theorem rawRowCheck20103 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form8 = rawRow20103 := by decide +kernel

def row20103 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20103 : row20103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20103 := by decide +kernel

theorem rowEval20103 (x : Key → ℝ) : Integer.Sparse.eval row20103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20103, Integer.Sparse.eval_collectBalanced, rawRowCheck20103]

def rawRow20104 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key626, 24), (key627, 24), (key629, 24)]

theorem rawRowCheck20104 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form8 = rawRow20104 := by decide +kernel

def row20104 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20104 : row20104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20104 := by decide +kernel

theorem rowEval20104 (x : Key → ℝ) : Integer.Sparse.eval row20104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20104, Integer.Sparse.eval_collectBalanced, rawRowCheck20104]

def rawRow20105 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key640, 24), (key626, 24), (key629, 24)]

theorem rawRowCheck20105 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form8 = rawRow20105 := by decide +kernel

def row20105 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20105 : row20105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20105 := by decide +kernel

theorem rowEval20105 (x : Key → ℝ) : Integer.Sparse.eval row20105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20105, Integer.Sparse.eval_collectBalanced, rawRowCheck20105]

def rawRow20106 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key627, 24), (key626, 24), (key629, 24)]

theorem rawRowCheck20106 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form8 = rawRow20106 := by decide +kernel

def row20106 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20106 : row20106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20106 := by decide +kernel

theorem rowEval20106 (x : Key → ℝ) : Integer.Sparse.eval row20106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20106, Integer.Sparse.eval_collectBalanced, rawRowCheck20106]

def rawRow20107 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key627, 24), (key626, 24), (key629, 24)]

theorem rawRowCheck20107 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form8 = rawRow20107 := by decide +kernel

def row20107 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20107 : row20107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20107 := by decide +kernel

theorem rowEval20107 (x : Key → ℝ) : Integer.Sparse.eval row20107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20107, Integer.Sparse.eval_collectBalanced, rawRowCheck20107]

def rawRow20108 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key629, 24), (key640, 24), (key627, 24)]

theorem rawRowCheck20108 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form8 = rawRow20108 := by decide +kernel

def row20108 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20108 : row20108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20108 := by decide +kernel

theorem rowEval20108 (x : Key → ℝ) : Integer.Sparse.eval row20108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20108, Integer.Sparse.eval_collectBalanced, rawRowCheck20108]

def rawRow20109 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key629, 24), (key640, 24), (key627, 24)]

theorem rawRowCheck20109 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form8 = rawRow20109 := by decide +kernel

def row20109 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20109 : row20109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20109 := by decide +kernel

theorem rowEval20109 (x : Key → ℝ) : Integer.Sparse.eval row20109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20109, Integer.Sparse.eval_collectBalanced, rawRowCheck20109]

def rawRow20110 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key627, 24), (key640, 24), (key627, 24)]

theorem rawRowCheck20110 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form8 = rawRow20110 := by decide +kernel

def row20110 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20110 : row20110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20110 := by decide +kernel

theorem rowEval20110 (x : Key → ℝ) : Integer.Sparse.eval row20110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20110, Integer.Sparse.eval_collectBalanced, rawRowCheck20110]

def rawRow20111 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key627, 24), (key640, 24), (key627, 24)]

theorem rawRowCheck20111 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form8 = rawRow20111 := by decide +kernel

def row20111 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20111 : row20111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20111 := by decide +kernel

theorem rowEval20111 (x : Key → ℝ) : Integer.Sparse.eval row20111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20111, Integer.Sparse.eval_collectBalanced, rawRowCheck20111]

def rawRow20112 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key626, 24), (key640, 24), (key627, 24)]

theorem rawRowCheck20112 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form8 = rawRow20112 := by decide +kernel

def row20112 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20112 : row20112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20112 := by decide +kernel

theorem rowEval20112 (x : Key → ℝ) : Integer.Sparse.eval row20112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20112, Integer.Sparse.eval_collectBalanced, rawRowCheck20112]

def rawRow20113 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key626, 24), (key640, 24), (key627, 24)]

theorem rawRowCheck20113 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form8 = rawRow20113 := by decide +kernel

def row20113 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20113 : row20113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20113 := by decide +kernel

theorem rowEval20113 (x : Key → ℝ) : Integer.Sparse.eval row20113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20113, Integer.Sparse.eval_collectBalanced, rawRowCheck20113]

def rawRow20114 : Integer.Sparse Key := [(key626, 24), (key627, 24), (key640, 24), (key629, 24), (key627, 24)]

theorem rawRowCheck20114 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form8 = rawRow20114 := by decide +kernel

def row20114 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20114 : row20114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20114 := by decide +kernel

theorem rowEval20114 (x : Key → ℝ) : Integer.Sparse.eval row20114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20114, Integer.Sparse.eval_collectBalanced, rawRowCheck20114]

def rawRow20115 : Integer.Sparse Key := [(key627, 24), (key626, 24), (key640, 24), (key629, 24), (key627, 24)]

theorem rawRowCheck20115 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form8 = rawRow20115 := by decide +kernel

def row20115 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20115 : row20115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20115 := by decide +kernel

theorem rowEval20115 (x : Key → ℝ) : Integer.Sparse.eval row20115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20115, Integer.Sparse.eval_collectBalanced, rawRowCheck20115]

def rawRow20116 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key627, 24), (key629, 24), (key627, 24)]

theorem rawRowCheck20116 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form8 = rawRow20116 := by decide +kernel

def row20116 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20116 : row20116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20116 := by decide +kernel

theorem rowEval20116 (x : Key → ℝ) : Integer.Sparse.eval row20116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20116, Integer.Sparse.eval_collectBalanced, rawRowCheck20116]

def rawRow20117 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key627, 24), (key629, 24), (key627, 24)]

theorem rawRowCheck20117 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form8 = rawRow20117 := by decide +kernel

def row20117 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20117 : row20117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20117 := by decide +kernel

theorem rowEval20117 (x : Key → ℝ) : Integer.Sparse.eval row20117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20117, Integer.Sparse.eval_collectBalanced, rawRowCheck20117]

def rawRow20118 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key626, 24), (key629, 24), (key627, 24)]

theorem rawRowCheck20118 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form8 = rawRow20118 := by decide +kernel

def row20118 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20118 : row20118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20118 := by decide +kernel

theorem rowEval20118 (x : Key → ℝ) : Integer.Sparse.eval row20118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20118, Integer.Sparse.eval_collectBalanced, rawRowCheck20118]

def rawRow20119 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key626, 24), (key629, 24), (key627, 24)]

theorem rawRowCheck20119 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form8 = rawRow20119 := by decide +kernel

def row20119 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20119 : row20119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20119 := by decide +kernel

theorem rowEval20119 (x : Key → ℝ) : Integer.Sparse.eval row20119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20119, Integer.Sparse.eval_collectBalanced, rawRowCheck20119]

def rawRow20120 : Integer.Sparse Key := [(key626, 24), (key629, 24), (key640, 24), (key627, 24), (key627, 24)]

theorem rawRowCheck20120 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form8 = rawRow20120 := by decide +kernel

def row20120 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20120 : row20120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20120 := by decide +kernel

theorem rowEval20120 (x : Key → ℝ) : Integer.Sparse.eval row20120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20120, Integer.Sparse.eval_collectBalanced, rawRowCheck20120]

def rawRow20121 : Integer.Sparse Key := [(key629, 24), (key626, 24), (key640, 24), (key627, 24), (key627, 24)]

theorem rawRowCheck20121 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form8 = rawRow20121 := by decide +kernel

def row20121 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20121 : row20121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20121 := by decide +kernel

theorem rowEval20121 (x : Key → ℝ) : Integer.Sparse.eval row20121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20121, Integer.Sparse.eval_collectBalanced, rawRowCheck20121]

def rawRow20122 : Integer.Sparse Key := [(key626, 24), (key640, 24), (key629, 24), (key627, 24), (key627, 24)]

theorem rawRowCheck20122 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form8 = rawRow20122 := by decide +kernel

def row20122 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20122 : row20122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20122 := by decide +kernel

theorem rowEval20122 (x : Key → ℝ) : Integer.Sparse.eval row20122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20122, Integer.Sparse.eval_collectBalanced, rawRowCheck20122]

def rawRow20123 : Integer.Sparse Key := [(key640, 24), (key626, 24), (key629, 24), (key627, 24), (key627, 24)]

theorem rawRowCheck20123 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form8 = rawRow20123 := by decide +kernel

def row20123 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20123 : row20123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20123 := by decide +kernel

theorem rowEval20123 (x : Key → ℝ) : Integer.Sparse.eval row20123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20123, Integer.Sparse.eval_collectBalanced, rawRowCheck20123]

def rawRow20124 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key626, 24), (key627, 24), (key627, 24)]

theorem rawRowCheck20124 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form8 = rawRow20124 := by decide +kernel

def row20124 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20124 : row20124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20124 := by decide +kernel

theorem rowEval20124 (x : Key → ℝ) : Integer.Sparse.eval row20124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20124, Integer.Sparse.eval_collectBalanced, rawRowCheck20124]

def rawRow20125 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key626, 24), (key627, 24), (key627, 24)]

theorem rawRowCheck20125 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form8 = rawRow20125 := by decide +kernel

def row20125 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20125 : row20125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20125 := by decide +kernel

theorem rowEval20125 (x : Key → ℝ) : Integer.Sparse.eval row20125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20125, Integer.Sparse.eval_collectBalanced, rawRowCheck20125]

def rawRow20126 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key640, 24), (key626, 24), (key627, 24)]

theorem rawRowCheck20126 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form8 = rawRow20126 := by decide +kernel

def row20126 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20126 : row20126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20126 := by decide +kernel

theorem rowEval20126 (x : Key → ℝ) : Integer.Sparse.eval row20126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20126, Integer.Sparse.eval_collectBalanced, rawRowCheck20126]

def rawRow20127 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key640, 24), (key626, 24), (key627, 24)]

theorem rawRowCheck20127 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form8 = rawRow20127 := by decide +kernel

def row20127 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20127 : row20127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20127 := by decide +kernel

theorem rowEval20127 (x : Key → ℝ) : Integer.Sparse.eval row20127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20127, Integer.Sparse.eval_collectBalanced, rawRowCheck20127]

def rawRow20128 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key629, 24), (key626, 24), (key627, 24)]

theorem rawRowCheck20128 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form8 = rawRow20128 := by decide +kernel

def row20128 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20128 : row20128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20128 := by decide +kernel

theorem rowEval20128 (x : Key → ℝ) : Integer.Sparse.eval row20128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20128, Integer.Sparse.eval_collectBalanced, rawRowCheck20128]

def rawRow20129 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key629, 24), (key626, 24), (key627, 24)]

theorem rawRowCheck20129 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form8 = rawRow20129 := by decide +kernel

def row20129 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20129 : row20129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20129 := by decide +kernel

theorem rowEval20129 (x : Key → ℝ) : Integer.Sparse.eval row20129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20129, Integer.Sparse.eval_collectBalanced, rawRowCheck20129]

def rawRow20130 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key627, 24), (key626, 24), (key627, 24)]

theorem rawRowCheck20130 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form8 = rawRow20130 := by decide +kernel

def row20130 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20130 : row20130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20130 := by decide +kernel

theorem rowEval20130 (x : Key → ℝ) : Integer.Sparse.eval row20130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20130, Integer.Sparse.eval_collectBalanced, rawRowCheck20130]

def rawRow20131 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key627, 24), (key626, 24), (key627, 24)]

theorem rawRowCheck20131 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form8 = rawRow20131 := by decide +kernel

def row20131 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20131 : row20131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20131 := by decide +kernel

theorem rowEval20131 (x : Key → ℝ) : Integer.Sparse.eval row20131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20131, Integer.Sparse.eval_collectBalanced, rawRowCheck20131]

def rawRow20132 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key629, 24), (key640, 24), (key626, 24)]

theorem rawRowCheck20132 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form8 = rawRow20132 := by decide +kernel

def row20132 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20132 : row20132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20132 := by decide +kernel

theorem rowEval20132 (x : Key → ℝ) : Integer.Sparse.eval row20132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20132, Integer.Sparse.eval_collectBalanced, rawRowCheck20132]

def rawRow20133 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key627, 24), (key640, 24), (key626, 24)]

theorem rawRowCheck20133 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form8 = rawRow20133 := by decide +kernel

def row20133 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20133 : row20133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20133 := by decide +kernel

theorem rowEval20133 (x : Key → ℝ) : Integer.Sparse.eval row20133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20133, Integer.Sparse.eval_collectBalanced, rawRowCheck20133]

def rawRow20134 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key627, 24), (key640, 24), (key626, 24)]

theorem rawRowCheck20134 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form8 = rawRow20134 := by decide +kernel

def row20134 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20134 : row20134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20134 := by decide +kernel

theorem rowEval20134 (x : Key → ℝ) : Integer.Sparse.eval row20134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20134, Integer.Sparse.eval_collectBalanced, rawRowCheck20134]

def rawRow20135 : Integer.Sparse Key := [(key627, 24), (key627, 24), (key640, 24), (key629, 24), (key626, 24)]

theorem rawRowCheck20135 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form8 = rawRow20135 := by decide +kernel

def row20135 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20135 : row20135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20135 := by decide +kernel

theorem rowEval20135 (x : Key → ℝ) : Integer.Sparse.eval row20135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20135, Integer.Sparse.eval_collectBalanced, rawRowCheck20135]

def rawRow20136 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key627, 24), (key629, 24), (key626, 24)]

theorem rawRowCheck20136 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form8 = rawRow20136 := by decide +kernel

def row20136 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20136 : row20136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20136 := by decide +kernel

theorem rowEval20136 (x : Key → ℝ) : Integer.Sparse.eval row20136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20136, Integer.Sparse.eval_collectBalanced, rawRowCheck20136]

def rawRow20137 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key627, 24), (key629, 24), (key626, 24)]

theorem rawRowCheck20137 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form8 = rawRow20137 := by decide +kernel

def row20137 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20137 : row20137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20137 := by decide +kernel

theorem rowEval20137 (x : Key → ℝ) : Integer.Sparse.eval row20137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20137, Integer.Sparse.eval_collectBalanced, rawRowCheck20137]

def rawRow20138 : Integer.Sparse Key := [(key627, 24), (key629, 24), (key640, 24), (key627, 24), (key626, 24)]

theorem rawRowCheck20138 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form8 = rawRow20138 := by decide +kernel

def row20138 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20138 : row20138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20138 := by decide +kernel

theorem rowEval20138 (x : Key → ℝ) : Integer.Sparse.eval row20138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20138, Integer.Sparse.eval_collectBalanced, rawRowCheck20138]

def rawRow20139 : Integer.Sparse Key := [(key629, 24), (key627, 24), (key640, 24), (key627, 24), (key626, 24)]

theorem rawRowCheck20139 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form8 = rawRow20139 := by decide +kernel

def row20139 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20139 : row20139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20139 := by decide +kernel

theorem rowEval20139 (x : Key → ℝ) : Integer.Sparse.eval row20139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20139, Integer.Sparse.eval_collectBalanced, rawRowCheck20139]

def rawRow20140 : Integer.Sparse Key := [(key627, 24), (key640, 24), (key629, 24), (key627, 24), (key626, 24)]

theorem rawRowCheck20140 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form8 = rawRow20140 := by decide +kernel

def row20140 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20140 : row20140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20140 := by decide +kernel

theorem rowEval20140 (x : Key → ℝ) : Integer.Sparse.eval row20140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20140, Integer.Sparse.eval_collectBalanced, rawRowCheck20140]

def rawRow20141 : Integer.Sparse Key := [(key640, 24), (key627, 24), (key629, 24), (key627, 24), (key626, 24)]

theorem rawRowCheck20141 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form8 = rawRow20141 := by decide +kernel

def row20141 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20141 : row20141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20141 := by decide +kernel

theorem rowEval20141 (x : Key → ℝ) : Integer.Sparse.eval row20141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20141, Integer.Sparse.eval_collectBalanced, rawRowCheck20141]

def rawRow20142 : Integer.Sparse Key := [(key629, 24), (key640, 24), (key627, 24), (key627, 24), (key626, 24)]

theorem rawRowCheck20142 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form8 = rawRow20142 := by decide +kernel

def row20142 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20142 : row20142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20142 := by decide +kernel

theorem rowEval20142 (x : Key → ℝ) : Integer.Sparse.eval row20142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20142, Integer.Sparse.eval_collectBalanced, rawRowCheck20142]

def rawRow20143 : Integer.Sparse Key := [(key640, 24), (key629, 24), (key627, 24), (key627, 24), (key626, 24)]

theorem rawRowCheck20143 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form8 = rawRow20143 := by decide +kernel

def row20143 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

theorem rowCheck20143 : row20143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20143 := by decide +kernel

theorem rowEval20143 (x : Key → ℝ) : Integer.Sparse.eval row20143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20143, Integer.Sparse.eval_collectBalanced, rawRowCheck20143]

def rawRow20144 : Integer.Sparse Key := [(key1407, 12), (key1407, 12), (key1411, 12), (key1435, 12), (key1436, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1585, 12), (key1628, 12)]

theorem rawRowCheck20144 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form9 = rawRow20144 := by decide +kernel

def row20144 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20144 : row20144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20144 := by decide +kernel

theorem rowEval20144 (x : Key → ℝ) : Integer.Sparse.eval row20144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20144, Integer.Sparse.eval_collectBalanced, rawRowCheck20144]

def rawRow20145 : Integer.Sparse Key := [(key1407, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1435, 12), (key1436, 12), (key1585, 12), (key1584, 12), (key1585, 12), (key1628, 12)]

theorem rawRowCheck20145 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form9 = rawRow20145 := by decide +kernel

def row20145 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20145 : row20145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20145 := by decide +kernel

theorem rowEval20145 (x : Key → ℝ) : Integer.Sparse.eval row20145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20145, Integer.Sparse.eval_collectBalanced, rawRowCheck20145]

def rawRow20146 : Integer.Sparse Key := [(key1411, 12), (key1407, 12), (key1407, 12), (key1436, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1585, 12), (key1584, 12), (key1628, 12)]

theorem rawRowCheck20146 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form9 = rawRow20146 := by decide +kernel

def row20146 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20146 : row20146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20146 := by decide +kernel

theorem rowEval20146 (x : Key → ℝ) : Integer.Sparse.eval row20146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20146, Integer.Sparse.eval_collectBalanced, rawRowCheck20146]

def rawRow20147 : Integer.Sparse Key := [(key1407, 12), (key1435, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1628, 12), (key1585, 12)]

theorem rawRowCheck20147 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form9 = rawRow20147 := by decide +kernel

def row20147 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20147 : row20147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20147 := by decide +kernel

theorem rowEval20147 (x : Key → ℝ) : Integer.Sparse.eval row20147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20147, Integer.Sparse.eval_collectBalanced, rawRowCheck20147]

def rawRow20148 : Integer.Sparse Key := [(key1407, 12), (key1436, 12), (key1435, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1584, 12), (key1628, 12), (key1585, 12)]

theorem rawRowCheck20148 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form9 = rawRow20148 := by decide +kernel

def row20148 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20148 : row20148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20148 := by decide +kernel

theorem rowEval20148 (x : Key → ℝ) : Integer.Sparse.eval row20148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20148, Integer.Sparse.eval_collectBalanced, rawRowCheck20148]

def rawRow20149 : Integer.Sparse Key := [(key1435, 12), (key1407, 12), (key1436, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1584, 12), (key1628, 12), (key1585, 12), (key1585, 12)]

theorem rawRowCheck20149 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form9 = rawRow20149 := by decide +kernel

def row20149 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20149 : row20149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20149 := by decide +kernel

theorem rowEval20149 (x : Key → ℝ) : Integer.Sparse.eval row20149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20149, Integer.Sparse.eval_collectBalanced, rawRowCheck20149]

def rawRow20150 : Integer.Sparse Key := [(key1435, 12), (key1436, 12), (key1407, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1628, 12), (key1584, 12), (key1585, 12), (key1585, 12)]

theorem rawRowCheck20150 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form9 = rawRow20150 := by decide +kernel

def row20150 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20150 : row20150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20150 := by decide +kernel

theorem rowEval20150 (x : Key → ℝ) : Integer.Sparse.eval row20150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20150, Integer.Sparse.eval_collectBalanced, rawRowCheck20150]

def rawRow20151 : Integer.Sparse Key := [(key1436, 12), (key1407, 12), (key1435, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1628, 12), (key1584, 12), (key1585, 12)]

theorem rawRowCheck20151 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form9 = rawRow20151 := by decide +kernel

def row20151 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20151 : row20151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20151 := by decide +kernel

theorem rowEval20151 (x : Key → ℝ) : Integer.Sparse.eval row20151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20151, Integer.Sparse.eval_collectBalanced, rawRowCheck20151]

def rawRow20152 : Integer.Sparse Key := [(key1436, 12), (key1435, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1584, 12), (key1585, 12)]

theorem rawRowCheck20152 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form9 = rawRow20152 := by decide +kernel

def row20152 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20152 : row20152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20152 := by decide +kernel

theorem rowEval20152 (x : Key → ℝ) : Integer.Sparse.eval row20152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20152, Integer.Sparse.eval_collectBalanced, rawRowCheck20152]

def rawRow20153 : Integer.Sparse Key := [(key1411, 12), (key1436, 12), (key1436, 12), (key1407, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1585, 12), (key1628, 12), (key1584, 12)]

theorem rawRowCheck20153 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form9 = rawRow20153 := by decide +kernel

def row20153 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20153 : row20153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20153 := by decide +kernel

theorem rowEval20153 (x : Key → ℝ) : Integer.Sparse.eval row20153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20153, Integer.Sparse.eval_collectBalanced, rawRowCheck20153]

def rawRow20154 : Integer.Sparse Key := [(key1436, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1435, 12), (key1407, 12), (key1585, 12), (key1628, 12), (key1585, 12), (key1584, 12)]

theorem rawRowCheck20154 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form9 = rawRow20154 := by decide +kernel

def row20154 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20154 : row20154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20154 := by decide +kernel

theorem rowEval20154 (x : Key → ℝ) : Integer.Sparse.eval row20154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20154, Integer.Sparse.eval_collectBalanced, rawRowCheck20154]

def rawRow20155 : Integer.Sparse Key := [(key1436, 12), (key1436, 12), (key1411, 12), (key1435, 12), (key1407, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1585, 12), (key1584, 12)]

theorem rawRowCheck20155 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form9 = rawRow20155 := by decide +kernel

def row20155 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20155 : row20155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20155 := by decide +kernel

theorem rowEval20155 (x : Key → ℝ) : Integer.Sparse.eval row20155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20155, Integer.Sparse.eval_collectBalanced, rawRowCheck20155]

def rawRow20156 : Integer.Sparse Key := [(key1407, 12), (key1407, 12), (key1411, 12), (key1584, 12), (key1585, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1436, 12), (key1628, 12)]

theorem rawRowCheck20156 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form9 = rawRow20156 := by decide +kernel

def row20156 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20156 : row20156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20156 := by decide +kernel

theorem rowEval20156 (x : Key → ℝ) : Integer.Sparse.eval row20156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20156, Integer.Sparse.eval_collectBalanced, rawRowCheck20156]

def rawRow20157 : Integer.Sparse Key := [(key1407, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1584, 12), (key1585, 12), (key1436, 12), (key1435, 12), (key1436, 12), (key1628, 12)]

theorem rawRowCheck20157 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form9 = rawRow20157 := by decide +kernel

def row20157 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20157 : row20157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20157 := by decide +kernel

theorem rowEval20157 (x : Key → ℝ) : Integer.Sparse.eval row20157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20157, Integer.Sparse.eval_collectBalanced, rawRowCheck20157]

def rawRow20158 : Integer.Sparse Key := [(key1411, 12), (key1407, 12), (key1407, 12), (key1585, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1436, 12), (key1435, 12), (key1628, 12)]

theorem rawRowCheck20158 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form9 = rawRow20158 := by decide +kernel

def row20158 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20158 : row20158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20158 := by decide +kernel

theorem rowEval20158 (x : Key → ℝ) : Integer.Sparse.eval row20158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20158, Integer.Sparse.eval_collectBalanced, rawRowCheck20158]

def rawRow20159 : Integer.Sparse Key := [(key1407, 12), (key1584, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1628, 12), (key1436, 12)]

theorem rawRowCheck20159 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form9 = rawRow20159 := by decide +kernel

def row20159 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20159 : row20159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20159 := by decide +kernel

theorem rowEval20159 (x : Key → ℝ) : Integer.Sparse.eval row20159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20159, Integer.Sparse.eval_collectBalanced, rawRowCheck20159]

def rawRow20160 : Integer.Sparse Key := [(key1407, 12), (key1585, 12), (key1584, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1435, 12), (key1628, 12), (key1436, 12)]

theorem rawRowCheck20160 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form9 = rawRow20160 := by decide +kernel

def row20160 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20160 : row20160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20160 := by decide +kernel

theorem rowEval20160 (x : Key → ℝ) : Integer.Sparse.eval row20160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20160, Integer.Sparse.eval_collectBalanced, rawRowCheck20160]

def rawRow20161 : Integer.Sparse Key := [(key1584, 12), (key1407, 12), (key1585, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1435, 12), (key1628, 12), (key1436, 12), (key1436, 12)]

theorem rawRowCheck20161 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form9 = rawRow20161 := by decide +kernel

def row20161 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20161 : row20161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20161 := by decide +kernel

theorem rowEval20161 (x : Key → ℝ) : Integer.Sparse.eval row20161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20161, Integer.Sparse.eval_collectBalanced, rawRowCheck20161]

def rawRow20162 : Integer.Sparse Key := [(key1584, 12), (key1585, 12), (key1407, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1628, 12), (key1435, 12), (key1436, 12), (key1436, 12)]

theorem rawRowCheck20162 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form9 = rawRow20162 := by decide +kernel

def row20162 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20162 : row20162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20162 := by decide +kernel

theorem rowEval20162 (x : Key → ℝ) : Integer.Sparse.eval row20162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20162, Integer.Sparse.eval_collectBalanced, rawRowCheck20162]

def rawRow20163 : Integer.Sparse Key := [(key1585, 12), (key1407, 12), (key1584, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1628, 12), (key1435, 12), (key1436, 12)]

theorem rawRowCheck20163 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form9 = rawRow20163 := by decide +kernel

def row20163 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20163 : row20163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20163 := by decide +kernel

theorem rowEval20163 (x : Key → ℝ) : Integer.Sparse.eval row20163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20163, Integer.Sparse.eval_collectBalanced, rawRowCheck20163]

def rawRow20164 : Integer.Sparse Key := [(key1585, 12), (key1584, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1435, 12), (key1436, 12)]

theorem rawRowCheck20164 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form9 = rawRow20164 := by decide +kernel

def row20164 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20164 : row20164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20164 := by decide +kernel

theorem rowEval20164 (x : Key → ℝ) : Integer.Sparse.eval row20164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20164, Integer.Sparse.eval_collectBalanced, rawRowCheck20164]

def rawRow20165 : Integer.Sparse Key := [(key1411, 12), (key1585, 12), (key1585, 12), (key1407, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1436, 12), (key1628, 12), (key1435, 12)]

theorem rawRowCheck20165 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form9 = rawRow20165 := by decide +kernel

def row20165 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20165 : row20165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20165 := by decide +kernel

theorem rowEval20165 (x : Key → ℝ) : Integer.Sparse.eval row20165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20165, Integer.Sparse.eval_collectBalanced, rawRowCheck20165]

def rawRow20166 : Integer.Sparse Key := [(key1585, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1584, 12), (key1407, 12), (key1436, 12), (key1628, 12), (key1436, 12), (key1435, 12)]

theorem rawRowCheck20166 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form9 = rawRow20166 := by decide +kernel

def row20166 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20166 : row20166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20166 := by decide +kernel

theorem rowEval20166 (x : Key → ℝ) : Integer.Sparse.eval row20166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20166, Integer.Sparse.eval_collectBalanced, rawRowCheck20166]

def rawRow20167 : Integer.Sparse Key := [(key1585, 12), (key1585, 12), (key1411, 12), (key1584, 12), (key1407, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1436, 12), (key1435, 12)]

theorem rawRowCheck20167 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form9 = rawRow20167 := by decide +kernel

def row20167 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20167 : row20167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20167 := by decide +kernel

theorem rowEval20167 (x : Key → ℝ) : Integer.Sparse.eval row20167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20167, Integer.Sparse.eval_collectBalanced, rawRowCheck20167]

def rawRow20168 : Integer.Sparse Key := [(key1407, 12), (key1435, 12), (key1436, 12), (key1584, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1411, 12), (key1436, 12), (key1585, 12)]

theorem rawRowCheck20168 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form9 = rawRow20168 := by decide +kernel

def row20168 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20168 : row20168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20168 := by decide +kernel

theorem rowEval20168 (x : Key → ℝ) : Integer.Sparse.eval row20168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20168, Integer.Sparse.eval_collectBalanced, rawRowCheck20168]

def rawRow20169 : Integer.Sparse Key := [(key1407, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1584, 12), (key1628, 12), (key1411, 12), (key1407, 12), (key1436, 12), (key1585, 12)]

theorem rawRowCheck20169 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form9 = rawRow20169 := by decide +kernel

def row20169 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20169 : row20169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20169 := by decide +kernel

theorem rowEval20169 (x : Key → ℝ) : Integer.Sparse.eval row20169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20169, Integer.Sparse.eval_collectBalanced, rawRowCheck20169]

def rawRow20170 : Integer.Sparse Key := [(key1435, 12), (key1407, 12), (key1436, 12), (key1584, 12), (key1628, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1411, 12), (key1585, 12)]

theorem rawRowCheck20170 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form9 = rawRow20170 := by decide +kernel

def row20170 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20170 : row20170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20170 := by decide +kernel

theorem rowEval20170 (x : Key → ℝ) : Integer.Sparse.eval row20170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20170, Integer.Sparse.eval_collectBalanced, rawRowCheck20170]

def rawRow20171 : Integer.Sparse Key := [(key1435, 12), (key1436, 12), (key1407, 12), (key1628, 12), (key1584, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1411, 12), (key1585, 12)]

theorem rawRowCheck20171 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form9 = rawRow20171 := by decide +kernel

def row20171 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20171 : row20171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20171 := by decide +kernel

theorem rowEval20171 (x : Key → ℝ) : Integer.Sparse.eval row20171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20171, Integer.Sparse.eval_collectBalanced, rawRowCheck20171]

def rawRow20172 : Integer.Sparse Key := [(key1436, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1628, 12), (key1584, 12), (key1411, 12), (key1436, 12), (key1407, 12), (key1585, 12)]

theorem rawRowCheck20172 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form9 = rawRow20172 := by decide +kernel

def row20172 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20172 : row20172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20172 := by decide +kernel

theorem rowEval20172 (x : Key → ℝ) : Integer.Sparse.eval row20172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20172, Integer.Sparse.eval_collectBalanced, rawRowCheck20172]

def rawRow20173 : Integer.Sparse Key := [(key1436, 12), (key1435, 12), (key1407, 12), (key1628, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1411, 12), (key1407, 12), (key1585, 12)]

theorem rawRowCheck20173 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form9 = rawRow20173 := by decide +kernel

def row20173 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20173 : row20173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20173 := by decide +kernel

theorem rowEval20173 (x : Key → ℝ) : Integer.Sparse.eval row20173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20173, Integer.Sparse.eval_collectBalanced, rawRowCheck20173]

def rawRow20174 : Integer.Sparse Key := [(key1407, 12), (key1584, 12), (key1585, 12), (key1435, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1411, 12), (key1585, 12), (key1436, 12)]

theorem rawRowCheck20174 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form9 = rawRow20174 := by decide +kernel

def row20174 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20174 : row20174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20174 := by decide +kernel

theorem rowEval20174 (x : Key → ℝ) : Integer.Sparse.eval row20174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20174, Integer.Sparse.eval_collectBalanced, rawRowCheck20174]

def rawRow20175 : Integer.Sparse Key := [(key1407, 12), (key1585, 12), (key1584, 12), (key1436, 12), (key1435, 12), (key1628, 12), (key1411, 12), (key1407, 12), (key1585, 12), (key1436, 12)]

theorem rawRowCheck20175 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form9 = rawRow20175 := by decide +kernel

def row20175 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20175 : row20175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20175 := by decide +kernel

theorem rowEval20175 (x : Key → ℝ) : Integer.Sparse.eval row20175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20175, Integer.Sparse.eval_collectBalanced, rawRowCheck20175]

def rawRow20176 : Integer.Sparse Key := [(key1584, 12), (key1407, 12), (key1585, 12), (key1435, 12), (key1628, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1411, 12), (key1436, 12)]

theorem rawRowCheck20176 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form9 = rawRow20176 := by decide +kernel

def row20176 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20176 : row20176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20176 := by decide +kernel

theorem rowEval20176 (x : Key → ℝ) : Integer.Sparse.eval row20176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20176, Integer.Sparse.eval_collectBalanced, rawRowCheck20176]

def rawRow20177 : Integer.Sparse Key := [(key1584, 12), (key1585, 12), (key1407, 12), (key1628, 12), (key1435, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1411, 12), (key1436, 12)]

theorem rawRowCheck20177 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form9 = rawRow20177 := by decide +kernel

def row20177 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20177 : row20177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20177 := by decide +kernel

theorem rowEval20177 (x : Key → ℝ) : Integer.Sparse.eval row20177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20177, Integer.Sparse.eval_collectBalanced, rawRowCheck20177]

def rawRow20178 : Integer.Sparse Key := [(key1585, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1628, 12), (key1435, 12), (key1411, 12), (key1585, 12), (key1407, 12), (key1436, 12)]

theorem rawRowCheck20178 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form9 = rawRow20178 := by decide +kernel

def row20178 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20178 : row20178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20178 := by decide +kernel

theorem rowEval20178 (x : Key → ℝ) : Integer.Sparse.eval row20178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20178, Integer.Sparse.eval_collectBalanced, rawRowCheck20178]

def rawRow20179 : Integer.Sparse Key := [(key1585, 12), (key1584, 12), (key1407, 12), (key1628, 12), (key1436, 12), (key1435, 12), (key1585, 12), (key1411, 12), (key1407, 12), (key1436, 12)]

theorem rawRowCheck20179 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form9 = rawRow20179 := by decide +kernel

def row20179 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20179 : row20179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20179 := by decide +kernel

theorem rowEval20179 (x : Key → ℝ) : Integer.Sparse.eval row20179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20179, Integer.Sparse.eval_collectBalanced, rawRowCheck20179]

def rawRow20180 : Integer.Sparse Key := [(key1435, 12), (key1584, 12), (key1628, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1411, 12)]

theorem rawRowCheck20180 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form9 = rawRow20180 := by decide +kernel

def row20180 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20180 : row20180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20180 := by decide +kernel

theorem rowEval20180 (x : Key → ℝ) : Integer.Sparse.eval row20180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20180, Integer.Sparse.eval_collectBalanced, rawRowCheck20180]

def rawRow20181 : Integer.Sparse Key := [(key1435, 12), (key1628, 12), (key1584, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1411, 12)]

theorem rawRowCheck20181 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form9 = rawRow20181 := by decide +kernel

def row20181 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20181 : row20181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20181 := by decide +kernel

theorem rowEval20181 (x : Key → ℝ) : Integer.Sparse.eval row20181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20181, Integer.Sparse.eval_collectBalanced, rawRowCheck20181]

def rawRow20182 : Integer.Sparse Key := [(key1584, 12), (key1435, 12), (key1628, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1411, 12)]

theorem rawRowCheck20182 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form9 = rawRow20182 := by decide +kernel

def row20182 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20182 : row20182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20182 := by decide +kernel

theorem rowEval20182 (x : Key → ℝ) : Integer.Sparse.eval row20182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20182, Integer.Sparse.eval_collectBalanced, rawRowCheck20182]

def rawRow20183 : Integer.Sparse Key := [(key1584, 12), (key1628, 12), (key1435, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1411, 12)]

theorem rawRowCheck20183 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form9 = rawRow20183 := by decide +kernel

def row20183 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20183 : row20183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20183 := by decide +kernel

theorem rowEval20183 (x : Key → ℝ) : Integer.Sparse.eval row20183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20183, Integer.Sparse.eval_collectBalanced, rawRowCheck20183]

def rawRow20184 : Integer.Sparse Key := [(key1628, 12), (key1435, 12), (key1584, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1411, 12)]

theorem rawRowCheck20184 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form9 = rawRow20184 := by decide +kernel

def row20184 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20184 : row20184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20184 := by decide +kernel

theorem rowEval20184 (x : Key → ℝ) : Integer.Sparse.eval row20184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20184, Integer.Sparse.eval_collectBalanced, rawRowCheck20184]

def rawRow20185 : Integer.Sparse Key := [(key1628, 12), (key1584, 12), (key1435, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1411, 12)]

theorem rawRowCheck20185 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form9 = rawRow20185 := by decide +kernel

def row20185 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20185 : row20185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20185 := by decide +kernel

theorem rowEval20185 (x : Key → ℝ) : Integer.Sparse.eval row20185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20185, Integer.Sparse.eval_collectBalanced, rawRowCheck20185]

def rawRow20186 : Integer.Sparse Key := [(key1436, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1435, 12), (key1584, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1407, 12)]

theorem rawRowCheck20186 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form9 = rawRow20186 := by decide +kernel

def row20186 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20186 : row20186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20186 := by decide +kernel

theorem rowEval20186 (x : Key → ℝ) : Integer.Sparse.eval row20186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20186, Integer.Sparse.eval_collectBalanced, rawRowCheck20186]

def rawRow20187 : Integer.Sparse Key := [(key1436, 12), (key1628, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1584, 12), (key1436, 12), (key1411, 12), (key1585, 12), (key1407, 12)]

theorem rawRowCheck20187 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form9 = rawRow20187 := by decide +kernel

def row20187 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20187 : row20187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20187 := by decide +kernel

theorem rowEval20187 (x : Key → ℝ) : Integer.Sparse.eval row20187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20187, Integer.Sparse.eval_collectBalanced, rawRowCheck20187]

def rawRow20188 : Integer.Sparse Key := [(key1585, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1584, 12), (key1435, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1407, 12)]

theorem rawRowCheck20188 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form9 = rawRow20188 := by decide +kernel

def row20188 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20188 : row20188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20188 := by decide +kernel

theorem rowEval20188 (x : Key → ℝ) : Integer.Sparse.eval row20188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20188, Integer.Sparse.eval_collectBalanced, rawRowCheck20188]

def rawRow20189 : Integer.Sparse Key := [(key1585, 12), (key1628, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1435, 12), (key1585, 12), (key1411, 12), (key1436, 12), (key1407, 12)]

theorem rawRowCheck20189 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form9 = rawRow20189 := by decide +kernel

def row20189 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20189 : row20189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20189 := by decide +kernel

theorem rowEval20189 (x : Key → ℝ) : Integer.Sparse.eval row20189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20189, Integer.Sparse.eval_collectBalanced, rawRowCheck20189]

def rawRow20190 : Integer.Sparse Key := [(key1628, 12), (key1436, 12), (key1585, 12), (key1435, 12), (key1584, 12), (key1407, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1407, 12)]

theorem rawRowCheck20190 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form9 = rawRow20190 := by decide +kernel

def row20190 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20190 : row20190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20190 := by decide +kernel

theorem rowEval20190 (x : Key → ℝ) : Integer.Sparse.eval row20190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20190, Integer.Sparse.eval_collectBalanced, rawRowCheck20190]

def rawRow20191 : Integer.Sparse Key := [(key1628, 12), (key1585, 12), (key1436, 12), (key1584, 12), (key1435, 12), (key1407, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1407, 12)]

theorem rawRowCheck20191 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form9 = rawRow20191 := by decide +kernel

def row20191 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20191 : row20191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20191 := by decide +kernel

theorem rowEval20191 (x : Key → ℝ) : Integer.Sparse.eval row20191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20191, Integer.Sparse.eval_collectBalanced, rawRowCheck20191]

def rawRow20192 : Integer.Sparse Key := [(key1411, 12), (key1436, 12), (key1436, 12), (key1585, 12), (key1585, 12), (key1628, 12), (key1407, 12), (key1407, 12), (key1435, 12), (key1584, 12)]

theorem rawRowCheck20192 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form9 = rawRow20192 := by decide +kernel

def row20192 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20192 : row20192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20192 := by decide +kernel

theorem rowEval20192 (x : Key → ℝ) : Integer.Sparse.eval row20192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20192, Integer.Sparse.eval_collectBalanced, rawRowCheck20192]

def rawRow20193 : Integer.Sparse Key := [(key1436, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1628, 12), (key1585, 12), (key1407, 12), (key1435, 12), (key1407, 12), (key1584, 12)]

theorem rawRowCheck20193 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form9 = rawRow20193 := by decide +kernel

def row20193 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20193 : row20193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20193 := by decide +kernel

theorem rowEval20193 (x : Key → ℝ) : Integer.Sparse.eval row20193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20193, Integer.Sparse.eval_collectBalanced, rawRowCheck20193]

def rawRow20194 : Integer.Sparse Key := [(key1436, 12), (key1436, 12), (key1411, 12), (key1628, 12), (key1585, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1407, 12), (key1584, 12)]

theorem rawRowCheck20194 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form9 = rawRow20194 := by decide +kernel

def row20194 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20194 : row20194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20194 := by decide +kernel

theorem rowEval20194 (x : Key → ℝ) : Integer.Sparse.eval row20194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20194, Integer.Sparse.eval_collectBalanced, rawRowCheck20194]

def rawRow20195 : Integer.Sparse Key := [(key1411, 12), (key1585, 12), (key1585, 12), (key1436, 12), (key1436, 12), (key1628, 12), (key1407, 12), (key1407, 12), (key1584, 12), (key1435, 12)]

theorem rawRowCheck20195 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form9 = rawRow20195 := by decide +kernel

def row20195 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20195 : row20195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20195 := by decide +kernel

theorem rowEval20195 (x : Key → ℝ) : Integer.Sparse.eval row20195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20195, Integer.Sparse.eval_collectBalanced, rawRowCheck20195]

def rawRow20196 : Integer.Sparse Key := [(key1585, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1628, 12), (key1436, 12), (key1407, 12), (key1584, 12), (key1407, 12), (key1435, 12)]

theorem rawRowCheck20196 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form9 = rawRow20196 := by decide +kernel

def row20196 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20196 : row20196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20196 := by decide +kernel

theorem rowEval20196 (x : Key → ℝ) : Integer.Sparse.eval row20196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20196, Integer.Sparse.eval_collectBalanced, rawRowCheck20196]

def rawRow20197 : Integer.Sparse Key := [(key1585, 12), (key1585, 12), (key1411, 12), (key1628, 12), (key1436, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1407, 12), (key1435, 12)]

theorem rawRowCheck20197 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form9 = rawRow20197 := by decide +kernel

def row20197 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20197 : row20197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20197 := by decide +kernel

theorem rowEval20197 (x : Key → ℝ) : Integer.Sparse.eval row20197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20197, Integer.Sparse.eval_collectBalanced, rawRowCheck20197]

def rawRow20198 : Integer.Sparse Key := [(key1436, 12), (key1585, 12), (key1628, 12), (key1411, 12), (key1436, 12), (key1585, 12), (key1407, 12), (key1435, 12), (key1584, 12), (key1407, 12)]

theorem rawRowCheck20198 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form9 = rawRow20198 := by decide +kernel

def row20198 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20198 : row20198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20198 := by decide +kernel

theorem rowEval20198 (x : Key → ℝ) : Integer.Sparse.eval row20198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20198, Integer.Sparse.eval_collectBalanced, rawRowCheck20198]

def rawRow20199 : Integer.Sparse Key := [(key1436, 12), (key1628, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1585, 12), (key1435, 12), (key1407, 12), (key1584, 12), (key1407, 12)]

theorem rawRowCheck20199 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form9 = rawRow20199 := by decide +kernel

def row20199 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20199 : row20199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20199 := by decide +kernel

theorem rowEval20199 (x : Key → ℝ) : Integer.Sparse.eval row20199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20199, Integer.Sparse.eval_collectBalanced, rawRowCheck20199]

def rawRow20200 : Integer.Sparse Key := [(key1585, 12), (key1436, 12), (key1628, 12), (key1411, 12), (key1585, 12), (key1436, 12), (key1407, 12), (key1584, 12), (key1435, 12), (key1407, 12)]

theorem rawRowCheck20200 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form9 = rawRow20200 := by decide +kernel

def row20200 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20200 : row20200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20200 := by decide +kernel

theorem rowEval20200 (x : Key → ℝ) : Integer.Sparse.eval row20200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20200, Integer.Sparse.eval_collectBalanced, rawRowCheck20200]

def rawRow20201 : Integer.Sparse Key := [(key1585, 12), (key1628, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1436, 12), (key1584, 12), (key1407, 12), (key1435, 12), (key1407, 12)]

theorem rawRowCheck20201 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form9 = rawRow20201 := by decide +kernel

def row20201 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20201 : row20201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20201 := by decide +kernel

theorem rowEval20201 (x : Key → ℝ) : Integer.Sparse.eval row20201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20201, Integer.Sparse.eval_collectBalanced, rawRowCheck20201]

def rawRow20202 : Integer.Sparse Key := [(key1628, 12), (key1436, 12), (key1585, 12), (key1436, 12), (key1585, 12), (key1411, 12), (key1435, 12), (key1584, 12), (key1407, 12), (key1407, 12)]

theorem rawRowCheck20202 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form9 = rawRow20202 := by decide +kernel

def row20202 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20202 : row20202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20202 := by decide +kernel

theorem rowEval20202 (x : Key → ℝ) : Integer.Sparse.eval row20202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20202, Integer.Sparse.eval_collectBalanced, rawRowCheck20202]

def rawRow20203 : Integer.Sparse Key := [(key1628, 12), (key1585, 12), (key1436, 12), (key1585, 12), (key1436, 12), (key1411, 12), (key1584, 12), (key1435, 12), (key1407, 12), (key1407, 12)]

theorem rawRowCheck20203 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form9 = rawRow20203 := by decide +kernel

def row20203 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

theorem rowCheck20203 : row20203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20203 := by decide +kernel

theorem rowEval20203 (x : Key → ℝ) : Integer.Sparse.eval row20203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20203, Integer.Sparse.eval_collectBalanced, rawRowCheck20203]

def rawRow20204 : Integer.Sparse Key := [(key280, 6), (key283, 6), (key283, 6), (key292, 6), (key349, 6), (key352, 6), (key352, 6), (key506, 6), (key509, 6), (key506, 6), (key667, 6), (key509, 6), (key667, 6), (key520, 6), (key520, 6), (key671, 6), (key369, 6), (key541, 6), (key541, 6), (key677, 6)]

theorem rawRowCheck20204 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form10 = rawRow20204 := by decide +kernel

def row20204 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20204 : row20204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20204 := by decide +kernel

theorem rowEval20204 (x : Key → ℝ) : Integer.Sparse.eval row20204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20204, Integer.Sparse.eval_collectBalanced, rawRowCheck20204]

def rawRow20205 : Integer.Sparse Key := [(key283, 6), (key280, 6), (key283, 6), (key292, 6), (key352, 6), (key349, 6), (key352, 6), (key509, 6), (key506, 6), (key667, 6), (key506, 6), (key667, 6), (key509, 6), (key520, 6), (key671, 6), (key520, 6), (key369, 6), (key541, 6), (key677, 6), (key541, 6)]

theorem rawRowCheck20205 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form10 = rawRow20205 := by decide +kernel

def row20205 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20205 : row20205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20205 := by decide +kernel

theorem rowEval20205 (x : Key → ℝ) : Integer.Sparse.eval row20205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20205, Integer.Sparse.eval_collectBalanced, rawRowCheck20205]

def rawRow20206 : Integer.Sparse Key := [(key283, 6), (key283, 6), (key280, 6), (key292, 6), (key352, 6), (key352, 6), (key349, 6), (key667, 6), (key667, 6), (key509, 6), (key509, 6), (key506, 6), (key506, 6), (key671, 6), (key520, 6), (key520, 6), (key369, 6), (key677, 6), (key541, 6), (key541, 6)]

theorem rawRowCheck20206 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form10 = rawRow20206 := by decide +kernel

def row20206 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20206 : row20206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20206 := by decide +kernel

theorem rowEval20206 (x : Key → ℝ) : Integer.Sparse.eval row20206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20206, Integer.Sparse.eval_collectBalanced, rawRowCheck20206]

def rawRow20207 : Integer.Sparse Key := [(key280, 6), (key283, 6), (key292, 6), (key283, 6), (key506, 6), (key509, 6), (key520, 6), (key349, 6), (key352, 6), (key506, 6), (key667, 6), (key520, 6), (key671, 6), (key352, 6), (key509, 6), (key667, 6), (key541, 6), (key369, 6), (key541, 6), (key677, 6)]

theorem rawRowCheck20207 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form10 = rawRow20207 := by decide +kernel

def row20207 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20207 : row20207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20207 := by decide +kernel

theorem rowEval20207 (x : Key → ℝ) : Integer.Sparse.eval row20207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20207, Integer.Sparse.eval_collectBalanced, rawRowCheck20207]

def rawRow20208 : Integer.Sparse Key := [(key283, 6), (key280, 6), (key292, 6), (key283, 6), (key509, 6), (key506, 6), (key520, 6), (key352, 6), (key349, 6), (key667, 6), (key506, 6), (key671, 6), (key520, 6), (key352, 6), (key667, 6), (key509, 6), (key541, 6), (key369, 6), (key677, 6), (key541, 6)]

theorem rawRowCheck20208 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form10 = rawRow20208 := by decide +kernel

def row20208 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20208 : row20208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20208 := by decide +kernel

theorem rowEval20208 (x : Key → ℝ) : Integer.Sparse.eval row20208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20208, Integer.Sparse.eval_collectBalanced, rawRowCheck20208]

def rawRow20209 : Integer.Sparse Key := [(key280, 6), (key292, 6), (key283, 6), (key283, 6), (key506, 6), (key520, 6), (key509, 6), (key506, 6), (key520, 6), (key349, 6), (key671, 6), (key352, 6), (key667, 6), (key509, 6), (key352, 6), (key667, 6), (key541, 6), (key541, 6), (key369, 6), (key677, 6)]

theorem rawRowCheck20209 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form10 = rawRow20209 := by decide +kernel

def row20209 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20209 : row20209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20209 := by decide +kernel

theorem rowEval20209 (x : Key → ℝ) : Integer.Sparse.eval row20209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20209, Integer.Sparse.eval_collectBalanced, rawRowCheck20209]

def rawRow20210 : Integer.Sparse Key := [(key292, 6), (key280, 6), (key283, 6), (key283, 6), (key520, 6), (key506, 6), (key509, 6), (key520, 6), (key506, 6), (key671, 6), (key349, 6), (key667, 6), (key352, 6), (key509, 6), (key667, 6), (key352, 6), (key541, 6), (key541, 6), (key677, 6), (key369, 6)]

theorem rawRowCheck20210 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form10 = rawRow20210 := by decide +kernel

def row20210 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20210 : row20210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20210 := by decide +kernel

theorem rowEval20210 (x : Key → ℝ) : Integer.Sparse.eval row20210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20210, Integer.Sparse.eval_collectBalanced, rawRowCheck20210]

def rawRow20211 : Integer.Sparse Key := [(key283, 6), (key292, 6), (key280, 6), (key283, 6), (key509, 6), (key520, 6), (key506, 6), (key667, 6), (key671, 6), (key352, 6), (key520, 6), (key349, 6), (key506, 6), (key667, 6), (key352, 6), (key509, 6), (key541, 6), (key677, 6), (key369, 6), (key541, 6)]

theorem rawRowCheck20211 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form10 = rawRow20211 := by decide +kernel

def row20211 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20211 : row20211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20211 := by decide +kernel

theorem rowEval20211 (x : Key → ℝ) : Integer.Sparse.eval row20211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20211, Integer.Sparse.eval_collectBalanced, rawRowCheck20211]

def rawRow20212 : Integer.Sparse Key := [(key292, 6), (key283, 6), (key280, 6), (key283, 6), (key520, 6), (key509, 6), (key506, 6), (key671, 6), (key667, 6), (key520, 6), (key352, 6), (key506, 6), (key349, 6), (key667, 6), (key509, 6), (key352, 6), (key541, 6), (key677, 6), (key541, 6), (key369, 6)]

theorem rawRowCheck20212 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form10 = rawRow20212 := by decide +kernel

def row20212 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20212 : row20212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20212 := by decide +kernel

theorem rowEval20212 (x : Key → ℝ) : Integer.Sparse.eval row20212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20212, Integer.Sparse.eval_collectBalanced, rawRowCheck20212]

def rawRow20213 : Integer.Sparse Key := [(key283, 6), (key283, 6), (key292, 6), (key280, 6), (key667, 6), (key667, 6), (key671, 6), (key352, 6), (key352, 6), (key509, 6), (key509, 6), (key520, 6), (key520, 6), (key349, 6), (key506, 6), (key506, 6), (key677, 6), (key369, 6), (key541, 6), (key541, 6)]

theorem rawRowCheck20213 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form10 = rawRow20213 := by decide +kernel

def row20213 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20213 : row20213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20213 := by decide +kernel

theorem rowEval20213 (x : Key → ℝ) : Integer.Sparse.eval row20213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20213, Integer.Sparse.eval_collectBalanced, rawRowCheck20213]

def rawRow20214 : Integer.Sparse Key := [(key283, 6), (key292, 6), (key283, 6), (key280, 6), (key667, 6), (key671, 6), (key667, 6), (key509, 6), (key520, 6), (key352, 6), (key520, 6), (key352, 6), (key509, 6), (key506, 6), (key349, 6), (key506, 6), (key677, 6), (key541, 6), (key369, 6), (key541, 6)]

theorem rawRowCheck20214 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form10 = rawRow20214 := by decide +kernel

def row20214 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20214 : row20214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20214 := by decide +kernel

theorem rowEval20214 (x : Key → ℝ) : Integer.Sparse.eval row20214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20214, Integer.Sparse.eval_collectBalanced, rawRowCheck20214]

def rawRow20215 : Integer.Sparse Key := [(key292, 6), (key283, 6), (key283, 6), (key280, 6), (key671, 6), (key667, 6), (key667, 6), (key520, 6), (key509, 6), (key520, 6), (key352, 6), (key509, 6), (key352, 6), (key506, 6), (key506, 6), (key349, 6), (key677, 6), (key541, 6), (key541, 6), (key369, 6)]

theorem rawRowCheck20215 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form10 = rawRow20215 := by decide +kernel

def row20215 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20215 : row20215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20215 := by decide +kernel

theorem rowEval20215 (x : Key → ℝ) : Integer.Sparse.eval row20215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form10) x := by
  rw [rowCheck20215, Integer.Sparse.eval_collectBalanced, rawRowCheck20215]

def rawRow20216 : Integer.Sparse Key := [(key349, 6), (key352, 6), (key352, 6), (key369, 6), (key280, 6), (key283, 6), (key283, 6), (key506, 6), (key509, 6), (key506, 6), (key667, 6), (key509, 6), (key667, 6), (key541, 6), (key541, 6), (key677, 6), (key292, 6), (key520, 6), (key520, 6), (key671, 6)]

theorem rawRowCheck20216 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form10 = rawRow20216 := by decide +kernel

def row20216 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20216 : row20216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20216 := by decide +kernel

theorem rowEval20216 (x : Key → ℝ) : Integer.Sparse.eval row20216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20216, Integer.Sparse.eval_collectBalanced, rawRowCheck20216]

def rawRow20217 : Integer.Sparse Key := [(key352, 6), (key349, 6), (key352, 6), (key369, 6), (key283, 6), (key280, 6), (key283, 6), (key509, 6), (key506, 6), (key667, 6), (key506, 6), (key667, 6), (key509, 6), (key541, 6), (key677, 6), (key541, 6), (key292, 6), (key520, 6), (key671, 6), (key520, 6)]

theorem rawRowCheck20217 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form10 = rawRow20217 := by decide +kernel

def row20217 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20217 : row20217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20217 := by decide +kernel

theorem rowEval20217 (x : Key → ℝ) : Integer.Sparse.eval row20217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20217, Integer.Sparse.eval_collectBalanced, rawRowCheck20217]

def rawRow20218 : Integer.Sparse Key := [(key352, 6), (key352, 6), (key349, 6), (key369, 6), (key283, 6), (key283, 6), (key280, 6), (key667, 6), (key667, 6), (key509, 6), (key509, 6), (key506, 6), (key506, 6), (key677, 6), (key541, 6), (key541, 6), (key292, 6), (key671, 6), (key520, 6), (key520, 6)]

theorem rawRowCheck20218 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form10 = rawRow20218 := by decide +kernel

def row20218 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20218 : row20218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20218 := by decide +kernel

theorem rowEval20218 (x : Key → ℝ) : Integer.Sparse.eval row20218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20218, Integer.Sparse.eval_collectBalanced, rawRowCheck20218]

def rawRow20219 : Integer.Sparse Key := [(key349, 6), (key352, 6), (key369, 6), (key352, 6), (key506, 6), (key509, 6), (key541, 6), (key280, 6), (key283, 6), (key506, 6), (key667, 6), (key541, 6), (key677, 6), (key283, 6), (key509, 6), (key667, 6), (key520, 6), (key292, 6), (key520, 6), (key671, 6)]

theorem rawRowCheck20219 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form10 = rawRow20219 := by decide +kernel

def row20219 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20219 : row20219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20219 := by decide +kernel

theorem rowEval20219 (x : Key → ℝ) : Integer.Sparse.eval row20219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20219, Integer.Sparse.eval_collectBalanced, rawRowCheck20219]

def rawRow20220 : Integer.Sparse Key := [(key352, 6), (key349, 6), (key369, 6), (key352, 6), (key509, 6), (key506, 6), (key541, 6), (key283, 6), (key280, 6), (key667, 6), (key506, 6), (key677, 6), (key541, 6), (key283, 6), (key667, 6), (key509, 6), (key520, 6), (key292, 6), (key671, 6), (key520, 6)]

theorem rawRowCheck20220 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form10 = rawRow20220 := by decide +kernel

def row20220 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20220 : row20220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20220 := by decide +kernel

theorem rowEval20220 (x : Key → ℝ) : Integer.Sparse.eval row20220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20220, Integer.Sparse.eval_collectBalanced, rawRowCheck20220]

def rawRow20221 : Integer.Sparse Key := [(key349, 6), (key369, 6), (key352, 6), (key352, 6), (key506, 6), (key541, 6), (key509, 6), (key506, 6), (key541, 6), (key280, 6), (key677, 6), (key283, 6), (key667, 6), (key509, 6), (key283, 6), (key667, 6), (key520, 6), (key520, 6), (key292, 6), (key671, 6)]

theorem rawRowCheck20221 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form10 = rawRow20221 := by decide +kernel

def row20221 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20221 : row20221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20221 := by decide +kernel

theorem rowEval20221 (x : Key → ℝ) : Integer.Sparse.eval row20221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20221, Integer.Sparse.eval_collectBalanced, rawRowCheck20221]

def rawRow20222 : Integer.Sparse Key := [(key369, 6), (key349, 6), (key352, 6), (key352, 6), (key541, 6), (key506, 6), (key509, 6), (key541, 6), (key506, 6), (key677, 6), (key280, 6), (key667, 6), (key283, 6), (key509, 6), (key667, 6), (key283, 6), (key520, 6), (key520, 6), (key671, 6), (key292, 6)]

theorem rawRowCheck20222 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form10 = rawRow20222 := by decide +kernel

def row20222 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20222 : row20222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20222 := by decide +kernel

theorem rowEval20222 (x : Key → ℝ) : Integer.Sparse.eval row20222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form10) x := by
  rw [rowCheck20222, Integer.Sparse.eval_collectBalanced, rawRowCheck20222]

def rawRow20223 : Integer.Sparse Key := [(key352, 6), (key369, 6), (key349, 6), (key352, 6), (key509, 6), (key541, 6), (key506, 6), (key667, 6), (key677, 6), (key283, 6), (key541, 6), (key280, 6), (key506, 6), (key667, 6), (key283, 6), (key509, 6), (key520, 6), (key671, 6), (key292, 6), (key520, 6)]

theorem rawRowCheck20223 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form10 = rawRow20223 := by decide +kernel

def row20223 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

theorem rowCheck20223 : row20223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20223 := by decide +kernel

theorem rowEval20223 (x : Key → ℝ) : Integer.Sparse.eval row20223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form10) x := by
  rw [rowCheck20223, Integer.Sparse.eval_collectBalanced, rawRowCheck20223]

end MUB6.Certificate.GramRows

end OAI
