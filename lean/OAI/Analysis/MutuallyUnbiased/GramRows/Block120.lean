import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
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

def rawRow12288 : Integer.Sparse Key := [(key1709, -6), (key1483, -6), (key1709, -6), (key1709, -6), (key1709, 6), (key1357, 6), (key1709, 6), (key1709, 6)]

theorem rawRowCheck12288 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form16 = rawRow12288 := by decide +kernel

def row12288 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

theorem rowCheck12288 : row12288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12288 := by decide +kernel

theorem rowEval12288 (x : Key → ℝ) : Integer.Sparse.eval row12288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12288, Integer.Sparse.eval_collectBalanced, rawRowCheck12288]

def rawRow12289 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1483, -6), (key1709, -6), (key1709, 6), (key1709, 6), (key1357, 6), (key1709, 6)]

theorem rawRowCheck12289 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form16 = rawRow12289 := by decide +kernel

def row12289 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

theorem rowCheck12289 : row12289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12289 := by decide +kernel

theorem rowEval12289 (x : Key → ℝ) : Integer.Sparse.eval row12289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12289, Integer.Sparse.eval_collectBalanced, rawRowCheck12289]

def rawRow12290 : Integer.Sparse Key := [(key1709, -6), (key1709, -6), (key1709, -6), (key1483, -6), (key1709, 6), (key1709, 6), (key1709, 6), (key1357, 6)]

theorem rawRowCheck12290 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form16 = rawRow12290 := by decide +kernel

def row12290 : Integer.Sparse Key := [(key1357, 6), (key1483, -6)]

theorem rowCheck12290 : row12290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12290 := by decide +kernel

theorem rowEval12290 (x : Key → ℝ) : Integer.Sparse.eval row12290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12290, Integer.Sparse.eval_collectBalanced, rawRowCheck12290]

def rawRow12291 : Integer.Sparse Key := [(key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1489, -2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2), (key1715, 2)]

theorem rawRowCheck12291 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form17 = rawRow12291 := by decide +kernel

def row12291 : Integer.Sparse Key := [(key1489, -24), (key1715, 24)]

theorem rowCheck12291 : row12291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12291 := by decide +kernel

theorem rowEval12291 (x : Key → ℝ) : Integer.Sparse.eval row12291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12291, Integer.Sparse.eval_collectBalanced, rawRowCheck12291]

def rawRow12292 : Integer.Sparse Key := [(key1363, -2), (key1363, -2), (key1363, -2), (key1715, -2), (key1715, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1363, 2), (key1363, 2), (key1363, 2), (key1489, 2), (key1489, 2), (key1489, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2)]

theorem rawRowCheck12292 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form17 = rawRow12292 := by decide +kernel

def row12292 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

theorem rowCheck12292 : row12292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12292 := by decide +kernel

theorem rowEval12292 (x : Key → ℝ) : Integer.Sparse.eval row12292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12292, Integer.Sparse.eval_collectBalanced, rawRowCheck12292]

def rawRow12293 : Integer.Sparse Key := [(key1715, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1363, -2), (key1715, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1489, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1363, 2), (key1489, 2), (key1489, 2), (key1860, 2), (key1860, 2)]

theorem rawRowCheck12293 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form17 = rawRow12293 := by decide +kernel

def row12293 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

theorem rowCheck12293 : row12293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12293 := by decide +kernel

theorem rowEval12293 (x : Key → ℝ) : Integer.Sparse.eval row12293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12293, Integer.Sparse.eval_collectBalanced, rawRowCheck12293]

def rawRow12294 : Integer.Sparse Key := [(key1860, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1715, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1363, -2), (key1715, -2), (key1860, 2), (key1489, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1489, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1363, 2), (key1489, 2)]

theorem rawRowCheck12294 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form17 = rawRow12294 := by decide +kernel

def row12294 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

theorem rowCheck12294 : row12294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12294 := by decide +kernel

theorem rowEval12294 (x : Key → ℝ) : Integer.Sparse.eval row12294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12294, Integer.Sparse.eval_collectBalanced, rawRowCheck12294]

def rawRow12295 : Integer.Sparse Key := [(key1860, -2), (key1860, -2), (key1715, -2), (key1860, -2), (key1860, -2), (key1363, -2), (key1860, -2), (key1715, -2), (key1860, -2), (key1363, -2), (key1715, -2), (key1363, -2), (key1860, 2), (key1860, 2), (key1489, 2), (key1860, 2), (key1860, 2), (key1363, 2), (key1860, 2), (key1489, 2), (key1860, 2), (key1363, 2), (key1489, 2), (key1363, 2)]

theorem rawRowCheck12295 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form17 = rawRow12295 := by decide +kernel

def row12295 : Integer.Sparse Key := [(key1489, 6), (key1715, -6)]

theorem rowCheck12295 : row12295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12295 := by decide +kernel

theorem rowEval12295 (x : Key → ℝ) : Integer.Sparse.eval row12295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12295, Integer.Sparse.eval_collectBalanced, rawRowCheck12295]

def rawRow12296 : Integer.Sparse Key := [(key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key118, 2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2), (key155, -2)]

theorem rawRowCheck12296 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form18 = rawRow12296 := by decide +kernel

def row12296 : Integer.Sparse Key := [(key118, 24), (key155, -24)]

theorem rowCheck12296 : row12296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12296 := by decide +kernel

theorem rowEval12296 (x : Key → ℝ) : Integer.Sparse.eval row12296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12296, Integer.Sparse.eval_collectBalanced, rawRowCheck12296]

def rawRow12297 : Integer.Sparse Key := [(key38, 2), (key38, 2), (key38, 2), (key118, 2), (key118, 2), (key118, 2), (key155, 2), (key155, 2), (key155, 2), (key155, 2), (key155, 2), (key155, 2), (key38, -2), (key38, -2), (key38, -2), (key118, -2), (key118, -2), (key118, -2), (key118, -2), (key118, -2), (key118, -2), (key155, -2), (key155, -2), (key155, -2)]

theorem rawRowCheck12297 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form18 = rawRow12297 := by decide +kernel

def row12297 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

theorem rowCheck12297 : row12297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12297 := by decide +kernel

theorem rowEval12297 (x : Key → ℝ) : Integer.Sparse.eval row12297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12297, Integer.Sparse.eval_collectBalanced, rawRowCheck12297]

def rawRow12298 : Integer.Sparse Key := [(key118, 2), (key155, 2), (key155, 2), (key38, 2), (key155, 2), (key155, 2), (key38, 2), (key38, 2), (key118, 2), (key118, 2), (key155, 2), (key155, 2), (key118, -2), (key118, -2), (key155, -2), (key38, -2), (key38, -2), (key118, -2), (key118, -2), (key155, -2), (key155, -2), (key38, -2), (key118, -2), (key118, -2)]

theorem rawRowCheck12298 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form18 = rawRow12298 := by decide +kernel

def row12298 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

theorem rowCheck12298 : row12298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12298 := by decide +kernel

theorem rowEval12298 (x : Key → ℝ) : Integer.Sparse.eval row12298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12298, Integer.Sparse.eval_collectBalanced, rawRowCheck12298]

def rawRow12299 : Integer.Sparse Key := [(key155, 2), (key118, 2), (key155, 2), (key155, 2), (key38, 2), (key155, 2), (key118, 2), (key155, 2), (key38, 2), (key155, 2), (key38, 2), (key118, 2), (key118, -2), (key155, -2), (key118, -2), (key118, -2), (key155, -2), (key38, -2), (key155, -2), (key38, -2), (key118, -2), (key118, -2), (key38, -2), (key118, -2)]

theorem rawRowCheck12299 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form18 = rawRow12299 := by decide +kernel

def row12299 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

theorem rowCheck12299 : row12299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12299 := by decide +kernel

theorem rowEval12299 (x : Key → ℝ) : Integer.Sparse.eval row12299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12299, Integer.Sparse.eval_collectBalanced, rawRowCheck12299]

def rawRow12300 : Integer.Sparse Key := [(key155, 2), (key155, 2), (key118, 2), (key155, 2), (key155, 2), (key38, 2), (key155, 2), (key118, 2), (key155, 2), (key38, 2), (key118, 2), (key38, 2), (key155, -2), (key118, -2), (key118, -2), (key155, -2), (key118, -2), (key155, -2), (key38, -2), (key118, -2), (key38, -2), (key118, -2), (key118, -2), (key38, -2)]

theorem rawRowCheck12300 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form18 = rawRow12300 := by decide +kernel

def row12300 : Integer.Sparse Key := [(key118, -6), (key155, 6)]

theorem rowCheck12300 : row12300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12300 := by decide +kernel

theorem rowEval12300 (x : Key → ℝ) : Integer.Sparse.eval row12300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12300, Integer.Sparse.eval_collectBalanced, rawRowCheck12300]

def rawRow12301 : Integer.Sparse Key := [(key1498, -4), (key1498, -4), (key1498, -4), (key1498, -4), (key1498, -4), (key1498, -4), (key1730, 6), (key1730, 6), (key1730, 6), (key1730, 6)]

theorem rawRowCheck12301 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form19 = rawRow12301 := by decide +kernel

def row12301 : Integer.Sparse Key := [(key1498, -24), (key1730, 24)]

theorem rowCheck12301 : row12301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12301 := by decide +kernel

theorem rowEval12301 (x : Key → ℝ) : Integer.Sparse.eval row12301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12301, Integer.Sparse.eval_collectBalanced, rawRowCheck12301]

def rawRow12302 : Integer.Sparse Key := [(key1498, -4), (key1498, -4), (key1498, -4), (key1730, -4), (key1730, -4), (key1730, -4), (key1498, 6), (key1498, 6), (key1498, 6), (key1730, 6)]

theorem rawRowCheck12302 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form19 = rawRow12302 := by decide +kernel

def row12302 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

theorem rowCheck12302 : row12302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12302 := by decide +kernel

theorem rowEval12302 (x : Key → ℝ) : Integer.Sparse.eval row12302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12302, Integer.Sparse.eval_collectBalanced, rawRowCheck12302]

def rawRow12303 : Integer.Sparse Key := [(key1498, -4), (key1730, -4), (key1730, -4), (key1498, -4), (key1498, -4), (key1730, -4), (key1498, 6), (key1498, 6), (key1730, 6), (key1498, 6)]

theorem rawRowCheck12303 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form19 = rawRow12303 := by decide +kernel

def row12303 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

theorem rowCheck12303 : row12303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12303 := by decide +kernel

theorem rowEval12303 (x : Key → ℝ) : Integer.Sparse.eval row12303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12303, Integer.Sparse.eval_collectBalanced, rawRowCheck12303]

def rawRow12304 : Integer.Sparse Key := [(key1730, -4), (key1498, -4), (key1730, -4), (key1498, -4), (key1730, -4), (key1498, -4), (key1498, 6), (key1730, 6), (key1498, 6), (key1498, 6)]

theorem rawRowCheck12304 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form19 = rawRow12304 := by decide +kernel

def row12304 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

theorem rowCheck12304 : row12304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12304 := by decide +kernel

theorem rowEval12304 (x : Key → ℝ) : Integer.Sparse.eval row12304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12304, Integer.Sparse.eval_collectBalanced, rawRowCheck12304]

def rawRow12305 : Integer.Sparse Key := [(key1730, -4), (key1730, -4), (key1498, -4), (key1730, -4), (key1498, -4), (key1498, -4), (key1730, 6), (key1498, 6), (key1498, 6), (key1498, 6)]

theorem rawRowCheck12305 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form19 = rawRow12305 := by decide +kernel

def row12305 : Integer.Sparse Key := [(key1498, 6), (key1730, -6)]

theorem rowCheck12305 : row12305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12305 := by decide +kernel

theorem rowEval12305 (x : Key → ℝ) : Integer.Sparse.eval row12305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck12305, Integer.Sparse.eval_collectBalanced, rawRowCheck12305]

def rawRow12306 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key670, 6), (key680, -24)]

theorem rawRowCheck12306 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form20 = rawRow12306 := by decide +kernel

def row12306 : Integer.Sparse Key := [(key670, 24), (key680, -24)]

theorem rowCheck12306 : row12306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12306 := by decide +kernel

theorem rowEval12306 (x : Key → ℝ) : Integer.Sparse.eval row12306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12306, Integer.Sparse.eval_collectBalanced, rawRowCheck12306]

def rawRow12307 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key670, 6), (key680, 6), (key670, -24)]

theorem rawRowCheck12307 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form20 = rawRow12307 := by decide +kernel

def row12307 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

theorem rowCheck12307 : row12307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12307 := by decide +kernel

theorem rowEval12307 (x : Key → ℝ) : Integer.Sparse.eval row12307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12307, Integer.Sparse.eval_collectBalanced, rawRowCheck12307]

def rawRow12308 : Integer.Sparse Key := [(key670, 6), (key670, 6), (key680, 6), (key670, 6), (key670, -24)]

theorem rawRowCheck12308 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form20 = rawRow12308 := by decide +kernel

def row12308 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

theorem rowCheck12308 : row12308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12308 := by decide +kernel

theorem rowEval12308 (x : Key → ℝ) : Integer.Sparse.eval row12308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12308, Integer.Sparse.eval_collectBalanced, rawRowCheck12308]

def rawRow12309 : Integer.Sparse Key := [(key670, 6), (key680, 6), (key670, 6), (key670, 6), (key670, -24)]

theorem rawRowCheck12309 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form20 = rawRow12309 := by decide +kernel

def row12309 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

theorem rowCheck12309 : row12309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12309 := by decide +kernel

theorem rowEval12309 (x : Key → ℝ) : Integer.Sparse.eval row12309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12309, Integer.Sparse.eval_collectBalanced, rawRowCheck12309]

def rawRow12310 : Integer.Sparse Key := [(key680, 6), (key670, 6), (key670, 6), (key670, 6), (key670, -24)]

theorem rawRowCheck12310 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form20 = rawRow12310 := by decide +kernel

def row12310 : Integer.Sparse Key := [(key670, -6), (key680, 6)]

theorem rowCheck12310 : row12310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12310 := by decide +kernel

theorem rowEval12310 (x : Key → ℝ) : Integer.Sparse.eval row12310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck12310, Integer.Sparse.eval_collectBalanced, rawRowCheck12310]

def rawRow12311 : Integer.Sparse Key := [(key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2)]

theorem rawRowCheck12311 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form21 = rawRow12311 := by decide +kernel

def row12311 : Integer.Sparse Key := [(key1710, 24), (key1859, -24)]

theorem rowCheck12311 : row12311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12311 := by decide +kernel

theorem rowEval12311 (x : Key → ℝ) : Integer.Sparse.eval row12311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12311, Integer.Sparse.eval_collectBalanced, rawRowCheck12311]

def rawRow12312 : Integer.Sparse Key := [(key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1358, -2), (key1358, -2), (key1358, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2)]

theorem rawRowCheck12312 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form21 = rawRow12312 := by decide +kernel

def row12312 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

theorem rowCheck12312 : row12312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12312 := by decide +kernel

theorem rowEval12312 (x : Key → ℝ) : Integer.Sparse.eval row12312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12312, Integer.Sparse.eval_collectBalanced, rawRowCheck12312]

def rawRow12313 : Integer.Sparse Key := [(key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1484, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1358, -2), (key1484, -2), (key1484, -2), (key1710, -2), (key1710, -2)]

theorem rawRowCheck12313 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form21 = rawRow12313 := by decide +kernel

def row12313 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

theorem rowCheck12313 : row12313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12313 := by decide +kernel

theorem rowEval12313 (x : Key → ℝ) : Integer.Sparse.eval row12313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12313, Integer.Sparse.eval_collectBalanced, rawRowCheck12313]

def rawRow12314 : Integer.Sparse Key := [(key1710, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1484, 1), (key1710, -2), (key1484, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1484, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1358, -2), (key1484, -2)]

theorem rawRowCheck12314 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form21 = rawRow12314 := by decide +kernel

def row12314 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

theorem rowCheck12314 : row12314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12314 := by decide +kernel

theorem rowEval12314 (x : Key → ℝ) : Integer.Sparse.eval row12314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12314, Integer.Sparse.eval_collectBalanced, rawRowCheck12314]

def rawRow12315 : Integer.Sparse Key := [(key1859, 1), (key1710, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1484, 1), (key1358, 1), (key1710, -2), (key1710, -2), (key1484, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1484, -2), (key1710, -2), (key1358, -2), (key1484, -2), (key1358, -2)]

theorem rawRowCheck12315 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form21 = rawRow12315 := by decide +kernel

def row12315 : Integer.Sparse Key := [(key1710, -6), (key1859, 6)]

theorem rowCheck12315 : row12315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12315 := by decide +kernel

theorem rowEval12315 (x : Key → ℝ) : Integer.Sparse.eval row12315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck12315, Integer.Sparse.eval_collectBalanced, rawRowCheck12315]

def rawRow12316 : Integer.Sparse Key := [(key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1484, -2), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1)]

theorem rawRowCheck12316 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form22 = rawRow12316 := by decide +kernel

def row12316 : Integer.Sparse Key := [(key1484, -24), (key1710, 24)]

theorem rowCheck12316 : row12316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12316 := by decide +kernel

theorem rowEval12316 (x : Key → ℝ) : Integer.Sparse.eval row12316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12316, Integer.Sparse.eval_collectBalanced, rawRowCheck12316]

def rawRow12317 : Integer.Sparse Key := [(key1358, -2), (key1358, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1)]

theorem rawRowCheck12317 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form22 = rawRow12317 := by decide +kernel

def row12317 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

theorem rowCheck12317 : row12317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12317 := by decide +kernel

theorem rowEval12317 (x : Key → ℝ) : Integer.Sparse.eval row12317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12317, Integer.Sparse.eval_collectBalanced, rawRowCheck12317]

def rawRow12318 : Integer.Sparse Key := [(key1710, -2), (key1710, -2), (key1859, -2), (key1358, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1859, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1859, 1), (key1859, 1), (key1358, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1710, 1)]

theorem rawRowCheck12318 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form22 = rawRow12318 := by decide +kernel

def row12318 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

theorem rowCheck12318 : row12318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12318 := by decide +kernel

theorem rowEval12318 (x : Key → ℝ) : Integer.Sparse.eval row12318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12318, Integer.Sparse.eval_collectBalanced, rawRowCheck12318]

def rawRow12319 : Integer.Sparse Key := [(key1710, -2), (key1859, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1358, -2), (key1859, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1710, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1484, 1)]

theorem rawRowCheck12319 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form22 = rawRow12319 := by decide +kernel

def row12319 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

theorem rowCheck12319 : row12319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12319 := by decide +kernel

theorem rowEval12319 (x : Key → ℝ) : Integer.Sparse.eval row12319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12319, Integer.Sparse.eval_collectBalanced, rawRowCheck12319]

def rawRow12320 : Integer.Sparse Key := [(key1859, -2), (key1710, -2), (key1710, -2), (key1859, -2), (key1710, -2), (key1859, -2), (key1358, -2), (key1710, -2), (key1358, -2), (key1710, -2), (key1710, -2), (key1358, -2), (key1859, 1), (key1710, 1), (key1859, 1), (key1484, 1), (key1710, 1), (key1484, 1), (key1859, 1), (key1710, 1), (key1859, 1), (key1358, 1), (key1710, 1), (key1358, 1), (key1859, 1), (key1484, 1), (key1859, 1), (key1358, 1), (key1484, 1), (key1358, 1), (key1710, 1), (key1484, 1), (key1710, 1), (key1358, 1), (key1484, 1), (key1358, 1)]

theorem rawRowCheck12320 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form22 = rawRow12320 := by decide +kernel

def row12320 : Integer.Sparse Key := [(key1484, 6), (key1710, -6)]

theorem rowCheck12320 : row12320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12320 := by decide +kernel

theorem rowEval12320 (x : Key → ℝ) : Integer.Sparse.eval row12320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck12320, Integer.Sparse.eval_collectBalanced, rawRowCheck12320]

def rawRow12321 : Integer.Sparse Key := [(key1277, -4), (key1277, -4), (key1277, -4), (key1277, -4), (key1277, -4), (key1277, -4), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1700, 2)]

theorem rawRowCheck12321 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form23 = rawRow12321 := by decide +kernel

def row12321 : Integer.Sparse Key := [(key1277, -24), (key1700, 24)]

theorem rowCheck12321 : row12321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12321 := by decide +kernel

theorem rowEval12321 (x : Key → ℝ) : Integer.Sparse.eval row12321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12321, Integer.Sparse.eval_collectBalanced, rawRowCheck12321]

def rawRow12322 : Integer.Sparse Key := [(key1700, -4), (key1700, -4), (key1700, -4), (key1851, -4), (key1851, -4), (key1851, -4), (key1277, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2)]

theorem rawRowCheck12322 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form23 = rawRow12322 := by decide +kernel

def row12322 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

theorem rowCheck12322 : row12322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12322 := by decide +kernel

theorem rowEval12322 (x : Key → ℝ) : Integer.Sparse.eval row12322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12322, Integer.Sparse.eval_collectBalanced, rawRowCheck12322]

def rawRow12323 : Integer.Sparse Key := [(key1700, -4), (key1851, -4), (key1851, -4), (key1700, -4), (key1700, -4), (key1851, -4), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1277, 2), (key1700, 2), (key1700, 2), (key1851, 2), (key1851, 2)]

theorem rawRowCheck12323 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form23 = rawRow12323 := by decide +kernel

def row12323 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

theorem rowCheck12323 : row12323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12323 := by decide +kernel

theorem rowEval12323 (x : Key → ℝ) : Integer.Sparse.eval row12323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12323, Integer.Sparse.eval_collectBalanced, rawRowCheck12323]

def rawRow12324 : Integer.Sparse Key := [(key1851, -4), (key1700, -4), (key1851, -4), (key1700, -4), (key1851, -4), (key1700, -4), (key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1277, 2), (key1700, 2)]

theorem rawRowCheck12324 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form23 = rawRow12324 := by decide +kernel

def row12324 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

theorem rowCheck12324 : row12324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12324 := by decide +kernel

theorem rowEval12324 (x : Key → ℝ) : Integer.Sparse.eval row12324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12324, Integer.Sparse.eval_collectBalanced, rawRowCheck12324]

def rawRow12325 : Integer.Sparse Key := [(key1851, -4), (key1851, -4), (key1700, -4), (key1851, -4), (key1700, -4), (key1700, -4), (key1851, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1851, 2), (key1277, 2), (key1851, 2), (key1700, 2), (key1851, 2), (key1277, 2), (key1700, 2), (key1277, 2)]

theorem rawRowCheck12325 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form23 = rawRow12325 := by decide +kernel

def row12325 : Integer.Sparse Key := [(key1277, 6), (key1700, -6)]

theorem rowCheck12325 : row12325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12325 := by decide +kernel

theorem rowEval12325 (x : Key → ℝ) : Integer.Sparse.eval row12325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck12325, Integer.Sparse.eval_collectBalanced, rawRowCheck12325]

def rawRow12326 : Integer.Sparse Key := [(key288, -24), (key513, 6), (key513, 6), (key513, 6), (key513, 6)]

theorem rawRowCheck12326 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form24 = rawRow12326 := by decide +kernel

def row12326 : Integer.Sparse Key := [(key288, -24), (key513, 24)]

theorem rowCheck12326 : row12326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12326 := by decide +kernel

theorem rowEval12326 (x : Key → ℝ) : Integer.Sparse.eval row12326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12326, Integer.Sparse.eval_collectBalanced, rawRowCheck12326]

def rawRow12327 : Integer.Sparse Key := [(key513, -24), (key288, 6), (key513, 6), (key513, 6), (key513, 6)]

theorem rawRowCheck12327 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form24 = rawRow12327 := by decide +kernel

def row12327 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

theorem rowCheck12327 : row12327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12327 := by decide +kernel

theorem rowEval12327 (x : Key → ℝ) : Integer.Sparse.eval row12327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12327, Integer.Sparse.eval_collectBalanced, rawRowCheck12327]

def rawRow12328 : Integer.Sparse Key := [(key513, -24), (key513, 6), (key288, 6), (key513, 6), (key513, 6)]

theorem rawRowCheck12328 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form24 = rawRow12328 := by decide +kernel

def row12328 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

theorem rowCheck12328 : row12328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12328 := by decide +kernel

theorem rowEval12328 (x : Key → ℝ) : Integer.Sparse.eval row12328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12328, Integer.Sparse.eval_collectBalanced, rawRowCheck12328]

def rawRow12329 : Integer.Sparse Key := [(key513, -24), (key513, 6), (key513, 6), (key288, 6), (key513, 6)]

theorem rawRowCheck12329 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form24 = rawRow12329 := by decide +kernel

def row12329 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

theorem rowCheck12329 : row12329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12329 := by decide +kernel

theorem rowEval12329 (x : Key → ℝ) : Integer.Sparse.eval row12329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12329, Integer.Sparse.eval_collectBalanced, rawRowCheck12329]

def rawRow12330 : Integer.Sparse Key := [(key513, -24), (key513, 6), (key513, 6), (key513, 6), (key288, 6)]

theorem rawRowCheck12330 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form24 = rawRow12330 := by decide +kernel

def row12330 : Integer.Sparse Key := [(key288, 6), (key513, -6)]

theorem rowCheck12330 : row12330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12330 := by decide +kernel

theorem rowEval12330 (x : Key → ℝ) : Integer.Sparse.eval row12330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck12330, Integer.Sparse.eval_collectBalanced, rawRowCheck12330]

def rawRow12331 : Integer.Sparse Key := [(key2428, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2442, 2), (key2556, 2), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2550, -2)]

theorem rawRowCheck12331 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form0 = rawRow12331 := by decide +kernel

def row12331 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

theorem rowCheck12331 : row12331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12331 := by decide +kernel

theorem rowEval12331 (x : Key → ℝ) : Integer.Sparse.eval row12331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12331, Integer.Sparse.eval_collectBalanced, rawRowCheck12331]

def rawRow12332 : Integer.Sparse Key := [(key2428, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2442, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2556, 2), (key2442, 2), (key2429, -2), (key2421, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2550, -2), (key2429, -2)]

theorem rawRowCheck12332 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form0 = rawRow12332 := by decide +kernel

def row12332 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

theorem rowCheck12332 : row12332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12332 := by decide +kernel

theorem rowEval12332 (x : Key → ℝ) : Integer.Sparse.eval row12332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12332, Integer.Sparse.eval_collectBalanced, rawRowCheck12332]

def rawRow12333 : Integer.Sparse Key := [(key2442, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2428, 2), (key2428, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2429, -2), (key2429, -2), (key2421, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2550, -2), (key2429, -2), (key2429, -2)]

theorem rawRowCheck12333 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form0 = rawRow12333 := by decide +kernel

def row12333 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

theorem rowCheck12333 : row12333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12333 := by decide +kernel

theorem rowEval12333 (x : Key → ℝ) : Integer.Sparse.eval row12333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12333, Integer.Sparse.eval_collectBalanced, rawRowCheck12333]

def rawRow12334 : Integer.Sparse Key := [(key2556, 2), (key2556, 2), (key2556, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2428, 2), (key2550, -2), (key2550, -2), (key2550, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2429, -2), (key2421, -2), (key2421, -2), (key2421, -2)]

theorem rawRowCheck12334 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form0 = rawRow12334 := by decide +kernel

def row12334 : Integer.Sparse Key := [(key2421, -6), (key2428, 12), (key2429, -12), (key2442, 6), (key2550, -6), (key2556, 6)]

theorem rowCheck12334 : row12334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12334 := by decide +kernel

theorem rowEval12334 (x : Key → ℝ) : Integer.Sparse.eval row12334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12334, Integer.Sparse.eval_collectBalanced, rawRowCheck12334]

def rawRow12335 : Integer.Sparse Key := [(key2429, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2442, 2), (key2508, 2), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2496, -2)]

theorem rawRowCheck12335 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form0 = rawRow12335 := by decide +kernel

def row12335 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

theorem rowCheck12335 : row12335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12335 := by decide +kernel

theorem rowEval12335 (x : Key → ℝ) : Integer.Sparse.eval row12335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12335, Integer.Sparse.eval_collectBalanced, rawRowCheck12335]

def rawRow12336 : Integer.Sparse Key := [(key2429, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2442, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2508, 2), (key2442, 2), (key2428, -2), (key2421, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2496, -2), (key2428, -2)]

theorem rawRowCheck12336 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form0 = rawRow12336 := by decide +kernel

def row12336 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

theorem rowCheck12336 : row12336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12336 := by decide +kernel

theorem rowEval12336 (x : Key → ℝ) : Integer.Sparse.eval row12336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12336, Integer.Sparse.eval_collectBalanced, rawRowCheck12336]

def rawRow12337 : Integer.Sparse Key := [(key2442, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2429, 2), (key2429, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2428, -2), (key2428, -2), (key2421, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2496, -2), (key2428, -2), (key2428, -2)]

theorem rawRowCheck12337 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form0 = rawRow12337 := by decide +kernel

def row12337 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

theorem rowCheck12337 : row12337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12337 := by decide +kernel

theorem rowEval12337 (x : Key → ℝ) : Integer.Sparse.eval row12337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12337, Integer.Sparse.eval_collectBalanced, rawRowCheck12337]

def rawRow12338 : Integer.Sparse Key := [(key2508, 2), (key2508, 2), (key2508, 2), (key2442, 2), (key2442, 2), (key2442, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2429, 2), (key2496, -2), (key2496, -2), (key2496, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2428, -2), (key2421, -2), (key2421, -2), (key2421, -2)]

theorem rawRowCheck12338 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form0 = rawRow12338 := by decide +kernel

def row12338 : Integer.Sparse Key := [(key2421, -6), (key2428, -12), (key2429, 12), (key2442, 6), (key2496, -6), (key2508, 6)]

theorem rowCheck12338 : row12338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12338 := by decide +kernel

theorem rowEval12338 (x : Key → ℝ) : Integer.Sparse.eval row12338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck12338, Integer.Sparse.eval_collectBalanced, rawRowCheck12338]

def rawRow12339 : Integer.Sparse Key := [(key1132, -24), (key1046, 6), (key1046, 6), (key1046, 6), (key1203, 6)]

theorem rawRowCheck12339 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form1 = rawRow12339 := by decide +kernel

def row12339 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

theorem rowCheck12339 : row12339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12339 := by decide +kernel

theorem rowEval12339 (x : Key → ℝ) : Integer.Sparse.eval row12339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12339, Integer.Sparse.eval_collectBalanced, rawRowCheck12339]

def rawRow12340 : Integer.Sparse Key := [(key1132, -24), (key1046, 6), (key1046, 6), (key1203, 6), (key1046, 6)]

theorem rawRowCheck12340 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form1 = rawRow12340 := by decide +kernel

def row12340 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

theorem rowCheck12340 : row12340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12340 := by decide +kernel

theorem rowEval12340 (x : Key → ℝ) : Integer.Sparse.eval row12340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12340, Integer.Sparse.eval_collectBalanced, rawRowCheck12340]

def rawRow12341 : Integer.Sparse Key := [(key1132, -24), (key1046, 6), (key1203, 6), (key1046, 6), (key1046, 6)]

theorem rawRowCheck12341 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form1 = rawRow12341 := by decide +kernel

def row12341 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

theorem rowCheck12341 : row12341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12341 := by decide +kernel

theorem rowEval12341 (x : Key → ℝ) : Integer.Sparse.eval row12341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12341, Integer.Sparse.eval_collectBalanced, rawRowCheck12341]

def rawRow12342 : Integer.Sparse Key := [(key1132, -24), (key1203, 6), (key1046, 6), (key1046, 6), (key1046, 6)]

theorem rawRowCheck12342 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form1 = rawRow12342 := by decide +kernel

def row12342 : Integer.Sparse Key := [(key1046, 18), (key1132, -24), (key1203, 6)]

theorem rowCheck12342 : row12342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12342 := by decide +kernel

theorem rowEval12342 (x : Key → ℝ) : Integer.Sparse.eval row12342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12342, Integer.Sparse.eval_collectBalanced, rawRowCheck12342]

def rawRow12343 : Integer.Sparse Key := [(key1203, -24), (key1046, 6), (key1046, 6), (key1046, 6), (key1132, 6)]

theorem rawRowCheck12343 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form1 = rawRow12343 := by decide +kernel

def row12343 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

theorem rowCheck12343 : row12343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12343 := by decide +kernel

theorem rowEval12343 (x : Key → ℝ) : Integer.Sparse.eval row12343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12343, Integer.Sparse.eval_collectBalanced, rawRowCheck12343]

def rawRow12344 : Integer.Sparse Key := [(key1203, -24), (key1046, 6), (key1046, 6), (key1132, 6), (key1046, 6)]

theorem rawRowCheck12344 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form1 = rawRow12344 := by decide +kernel

def row12344 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

theorem rowCheck12344 : row12344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12344 := by decide +kernel

theorem rowEval12344 (x : Key → ℝ) : Integer.Sparse.eval row12344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12344, Integer.Sparse.eval_collectBalanced, rawRowCheck12344]

def rawRow12345 : Integer.Sparse Key := [(key1203, -24), (key1046, 6), (key1132, 6), (key1046, 6), (key1046, 6)]

theorem rawRowCheck12345 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form1 = rawRow12345 := by decide +kernel

def row12345 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

theorem rowCheck12345 : row12345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12345 := by decide +kernel

theorem rowEval12345 (x : Key → ℝ) : Integer.Sparse.eval row12345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12345, Integer.Sparse.eval_collectBalanced, rawRowCheck12345]

def rawRow12346 : Integer.Sparse Key := [(key1203, -24), (key1132, 6), (key1046, 6), (key1046, 6), (key1046, 6)]

theorem rawRowCheck12346 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form1 = rawRow12346 := by decide +kernel

def row12346 : Integer.Sparse Key := [(key1046, 18), (key1132, 6), (key1203, -24)]

theorem rowCheck12346 : row12346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12346 := by decide +kernel

theorem rowEval12346 (x : Key → ℝ) : Integer.Sparse.eval row12346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck12346, Integer.Sparse.eval_collectBalanced, rawRowCheck12346]

def rawRow12347 : Integer.Sparse Key := [(key1135, -6), (key1140, -6), (key1140, -6), (key1140, -6), (key1049, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1207, 2)]

theorem rawRowCheck12347 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form2 = rawRow12347 := by decide +kernel

def row12347 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

theorem rowCheck12347 : row12347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12347 := by decide +kernel

theorem rowEval12347 (x : Key → ℝ) : Integer.Sparse.eval row12347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12347, Integer.Sparse.eval_collectBalanced, rawRowCheck12347]

def rawRow12348 : Integer.Sparse Key := [(key1140, -6), (key1135, -6), (key1140, -6), (key1140, -6), (key1060, 2), (key1049, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1207, 2), (key1060, 2)]

theorem rawRowCheck12348 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form2 = rawRow12348 := by decide +kernel

def row12348 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

theorem rowCheck12348 : row12348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12348 := by decide +kernel

theorem rowEval12348 (x : Key → ℝ) : Integer.Sparse.eval row12348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12348, Integer.Sparse.eval_collectBalanced, rawRowCheck12348]

def rawRow12349 : Integer.Sparse Key := [(key1140, -6), (key1140, -6), (key1135, -6), (key1140, -6), (key1060, 2), (key1060, 2), (key1049, 2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1207, 2), (key1060, 2), (key1060, 2)]

theorem rawRowCheck12349 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form2 = rawRow12349 := by decide +kernel

def row12349 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

theorem rowCheck12349 : row12349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12349 := by decide +kernel

theorem rowEval12349 (x : Key → ℝ) : Integer.Sparse.eval row12349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12349, Integer.Sparse.eval_collectBalanced, rawRowCheck12349]

def rawRow12350 : Integer.Sparse Key := [(key1140, -6), (key1140, -6), (key1140, -6), (key1135, -6), (key1207, 2), (key1207, 2), (key1207, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1049, 2), (key1049, 2), (key1049, 2)]

theorem rawRowCheck12350 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form2 = rawRow12350 := by decide +kernel

def row12350 : Integer.Sparse Key := [(key1049, 6), (key1060, 12), (key1135, -6), (key1140, -18), (key1207, 6)]

theorem rowCheck12350 : row12350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12350 := by decide +kernel

theorem rowEval12350 (x : Key → ℝ) : Integer.Sparse.eval row12350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12350, Integer.Sparse.eval_collectBalanced, rawRowCheck12350]

def rawRow12351 : Integer.Sparse Key := [(key1205, -6), (key1207, -6), (key1207, -6), (key1207, -6), (key1052, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1140, 2)]

theorem rawRowCheck12351 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form2 = rawRow12351 := by decide +kernel

def row12351 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

theorem rowCheck12351 : row12351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12351 := by decide +kernel

theorem rowEval12351 (x : Key → ℝ) : Integer.Sparse.eval row12351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12351, Integer.Sparse.eval_collectBalanced, rawRowCheck12351]

def rawRow12352 : Integer.Sparse Key := [(key1207, -6), (key1205, -6), (key1207, -6), (key1207, -6), (key1060, 2), (key1052, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1140, 2), (key1060, 2)]

theorem rawRowCheck12352 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form2 = rawRow12352 := by decide +kernel

def row12352 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

theorem rowCheck12352 : row12352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12352 := by decide +kernel

theorem rowEval12352 (x : Key → ℝ) : Integer.Sparse.eval row12352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12352, Integer.Sparse.eval_collectBalanced, rawRowCheck12352]

def rawRow12353 : Integer.Sparse Key := [(key1207, -6), (key1207, -6), (key1205, -6), (key1207, -6), (key1060, 2), (key1060, 2), (key1052, 2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1140, 2), (key1060, 2), (key1060, 2)]

theorem rawRowCheck12353 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form2 = rawRow12353 := by decide +kernel

def row12353 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

theorem rowCheck12353 : row12353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12353 := by decide +kernel

theorem rowEval12353 (x : Key → ℝ) : Integer.Sparse.eval row12353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12353, Integer.Sparse.eval_collectBalanced, rawRowCheck12353]

def rawRow12354 : Integer.Sparse Key := [(key1207, -6), (key1207, -6), (key1207, -6), (key1205, -6), (key1140, 2), (key1140, 2), (key1140, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1060, 2), (key1052, 2), (key1052, 2), (key1052, 2)]

theorem rawRowCheck12354 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form2 = rawRow12354 := by decide +kernel

def row12354 : Integer.Sparse Key := [(key1052, 6), (key1060, 12), (key1140, 6), (key1205, -6), (key1207, -18)]

theorem rowCheck12354 : row12354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12354 := by decide +kernel

theorem rowEval12354 (x : Key → ℝ) : Integer.Sparse.eval row12354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck12354, Integer.Sparse.eval_collectBalanced, rawRowCheck12354]

def rawRow12355 : Integer.Sparse Key := [(key3060, -6), (key3060, -6), (key3060, -6), (key3125, -6), (key3046, 2), (key3046, 2), (key3064, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3064, 2), (key3101, 2)]

theorem rawRowCheck12355 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form3 = rawRow12355 := by decide +kernel

def row12355 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

theorem rowCheck12355 : row12355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12355 := by decide +kernel

theorem rowEval12355 (x : Key → ℝ) : Integer.Sparse.eval row12355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12355, Integer.Sparse.eval_collectBalanced, rawRowCheck12355]

def rawRow12356 : Integer.Sparse Key := [(key3060, -6), (key3060, -6), (key3125, -6), (key3060, -6), (key3046, 2), (key3064, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3064, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3101, 2), (key3064, 2)]

theorem rawRowCheck12356 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form3 = rawRow12356 := by decide +kernel

def row12356 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

theorem rowCheck12356 : row12356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12356 := by decide +kernel

theorem rowEval12356 (x : Key → ℝ) : Integer.Sparse.eval row12356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12356, Integer.Sparse.eval_collectBalanced, rawRowCheck12356]

def rawRow12357 : Integer.Sparse Key := [(key3060, -6), (key3125, -6), (key3060, -6), (key3060, -6), (key3064, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3046, 2), (key3046, 2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck12357 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form3 = rawRow12357 := by decide +kernel

def row12357 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

theorem rowCheck12357 : row12357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12357 := by decide +kernel

theorem rowEval12357 (x : Key → ℝ) : Integer.Sparse.eval row12357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12357, Integer.Sparse.eval_collectBalanced, rawRowCheck12357]

def rawRow12358 : Integer.Sparse Key := [(key3125, -6), (key3060, -6), (key3060, -6), (key3060, -6), (key3101, 2), (key3101, 2), (key3101, 2), (key3064, 2), (key3064, 2), (key3064, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck12358 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form3 = rawRow12358 := by decide +kernel

def row12358 : Integer.Sparse Key := [(key3046, 12), (key3060, -18), (key3064, 6), (key3101, 6), (key3125, -6)]

theorem rowCheck12358 : row12358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12358 := by decide +kernel

theorem rowEval12358 (x : Key → ℝ) : Integer.Sparse.eval row12358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12358, Integer.Sparse.eval_collectBalanced, rawRowCheck12358]

def rawRow12359 : Integer.Sparse Key := [(key3064, -6), (key3064, -6), (key3064, -6), (key3123, -6), (key3046, 2), (key3046, 2), (key3060, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3060, 2), (key3095, 2)]

theorem rawRowCheck12359 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form3 = rawRow12359 := by decide +kernel

def row12359 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

theorem rowCheck12359 : row12359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12359 := by decide +kernel

theorem rowEval12359 (x : Key → ℝ) : Integer.Sparse.eval row12359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12359, Integer.Sparse.eval_collectBalanced, rawRowCheck12359]

def rawRow12360 : Integer.Sparse Key := [(key3064, -6), (key3064, -6), (key3123, -6), (key3064, -6), (key3046, 2), (key3060, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3060, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3095, 2), (key3060, 2)]

theorem rawRowCheck12360 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form3 = rawRow12360 := by decide +kernel

def row12360 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

theorem rowCheck12360 : row12360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12360 := by decide +kernel

theorem rowEval12360 (x : Key → ℝ) : Integer.Sparse.eval row12360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12360, Integer.Sparse.eval_collectBalanced, rawRowCheck12360]

def rawRow12361 : Integer.Sparse Key := [(key3064, -6), (key3123, -6), (key3064, -6), (key3064, -6), (key3060, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3046, 2), (key3046, 2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck12361 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form3 = rawRow12361 := by decide +kernel

def row12361 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

theorem rowCheck12361 : row12361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12361 := by decide +kernel

theorem rowEval12361 (x : Key → ℝ) : Integer.Sparse.eval row12361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12361, Integer.Sparse.eval_collectBalanced, rawRowCheck12361]

def rawRow12362 : Integer.Sparse Key := [(key3123, -6), (key3064, -6), (key3064, -6), (key3064, -6), (key3095, 2), (key3095, 2), (key3095, 2), (key3060, 2), (key3060, 2), (key3060, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2), (key3046, 2)]

theorem rawRowCheck12362 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form3 = rawRow12362 := by decide +kernel

def row12362 : Integer.Sparse Key := [(key3046, 12), (key3060, 6), (key3064, -18), (key3095, 6), (key3123, -6)]

theorem rowCheck12362 : row12362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12362 := by decide +kernel

theorem rowEval12362 (x : Key → ℝ) : Integer.Sparse.eval row12362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck12362, Integer.Sparse.eval_collectBalanced, rawRowCheck12362]

def rawRow12363 : Integer.Sparse Key := [(key2488, -6), (key2493, -6), (key2493, -6), (key2493, -6), (key2415, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2549, 2)]

theorem rawRowCheck12363 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form4 = rawRow12363 := by decide +kernel

def row12363 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

theorem rowCheck12363 : row12363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12363 := by decide +kernel

theorem rowEval12363 (x : Key → ℝ) : Integer.Sparse.eval row12363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12363, Integer.Sparse.eval_collectBalanced, rawRowCheck12363]

def rawRow12364 : Integer.Sparse Key := [(key2493, -6), (key2488, -6), (key2493, -6), (key2493, -6), (key2425, 2), (key2415, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2549, 2), (key2425, 2)]

theorem rawRowCheck12364 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form4 = rawRow12364 := by decide +kernel

def row12364 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

theorem rowCheck12364 : row12364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12364 := by decide +kernel

theorem rowEval12364 (x : Key → ℝ) : Integer.Sparse.eval row12364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12364, Integer.Sparse.eval_collectBalanced, rawRowCheck12364]

def rawRow12365 : Integer.Sparse Key := [(key2493, -6), (key2493, -6), (key2488, -6), (key2493, -6), (key2425, 2), (key2425, 2), (key2415, 2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2549, 2), (key2425, 2), (key2425, 2)]

theorem rawRowCheck12365 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form4 = rawRow12365 := by decide +kernel

def row12365 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

theorem rowCheck12365 : row12365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12365 := by decide +kernel

theorem rowEval12365 (x : Key → ℝ) : Integer.Sparse.eval row12365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12365, Integer.Sparse.eval_collectBalanced, rawRowCheck12365]

def rawRow12366 : Integer.Sparse Key := [(key2493, -6), (key2493, -6), (key2493, -6), (key2488, -6), (key2549, 2), (key2549, 2), (key2549, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2415, 2), (key2415, 2), (key2415, 2)]

theorem rawRowCheck12366 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form4 = rawRow12366 := by decide +kernel

def row12366 : Integer.Sparse Key := [(key2415, 6), (key2425, 12), (key2488, -6), (key2493, -18), (key2549, 6)]

theorem rowCheck12366 : row12366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12366 := by decide +kernel

theorem rowEval12366 (x : Key → ℝ) : Integer.Sparse.eval row12366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12366, Integer.Sparse.eval_collectBalanced, rawRowCheck12366]

def rawRow12367 : Integer.Sparse Key := [(key2547, -6), (key2549, -6), (key2549, -6), (key2549, -6), (key2418, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2493, 2)]

theorem rawRowCheck12367 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form4 = rawRow12367 := by decide +kernel

def row12367 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

theorem rowCheck12367 : row12367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12367 := by decide +kernel

theorem rowEval12367 (x : Key → ℝ) : Integer.Sparse.eval row12367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12367, Integer.Sparse.eval_collectBalanced, rawRowCheck12367]

def rawRow12368 : Integer.Sparse Key := [(key2549, -6), (key2547, -6), (key2549, -6), (key2549, -6), (key2425, 2), (key2418, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2493, 2), (key2425, 2)]

theorem rawRowCheck12368 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form4 = rawRow12368 := by decide +kernel

def row12368 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

theorem rowCheck12368 : row12368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12368 := by decide +kernel

theorem rowEval12368 (x : Key → ℝ) : Integer.Sparse.eval row12368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12368, Integer.Sparse.eval_collectBalanced, rawRowCheck12368]

def rawRow12369 : Integer.Sparse Key := [(key2549, -6), (key2549, -6), (key2547, -6), (key2549, -6), (key2425, 2), (key2425, 2), (key2418, 2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2493, 2), (key2425, 2), (key2425, 2)]

theorem rawRowCheck12369 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form4 = rawRow12369 := by decide +kernel

def row12369 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

theorem rowCheck12369 : row12369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12369 := by decide +kernel

theorem rowEval12369 (x : Key → ℝ) : Integer.Sparse.eval row12369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12369, Integer.Sparse.eval_collectBalanced, rawRowCheck12369]

def rawRow12370 : Integer.Sparse Key := [(key2549, -6), (key2549, -6), (key2549, -6), (key2547, -6), (key2493, 2), (key2493, 2), (key2493, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2425, 2), (key2418, 2), (key2418, 2), (key2418, 2)]

theorem rawRowCheck12370 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form4 = rawRow12370 := by decide +kernel

def row12370 : Integer.Sparse Key := [(key2418, 6), (key2425, 12), (key2493, 6), (key2547, -6), (key2549, -18)]

theorem rowCheck12370 : row12370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12370 := by decide +kernel

theorem rowEval12370 (x : Key → ℝ) : Integer.Sparse.eval row12370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck12370, Integer.Sparse.eval_collectBalanced, rawRowCheck12370]

def rawRow12371 : Integer.Sparse Key := [(key2711, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2716, -2), (key2711, -2), (key2980, -2), (key2716, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2980, -2), (key2680, 1), (key2690, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2743, 1), (key2956, 1)]

theorem rawRowCheck12371 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form5 = rawRow12371 := by decide +kernel

def row12371 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

theorem rowCheck12371 : row12371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12371 := by decide +kernel

theorem rowEval12371 (x : Key → ℝ) : Integer.Sparse.eval row12371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12371, Integer.Sparse.eval_collectBalanced, rawRowCheck12371]

def rawRow12372 : Integer.Sparse Key := [(key2716, -2), (key2711, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2980, -2), (key2711, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2980, -2), (key2716, -2), (key2690, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2743, 1)]

theorem rawRowCheck12372 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form5 = rawRow12372 := by decide +kernel

def row12372 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

theorem rowCheck12372 : row12372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12372 := by decide +kernel

theorem rowEval12372 (x : Key → ℝ) : Integer.Sparse.eval row12372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12372, Integer.Sparse.eval_collectBalanced, rawRowCheck12372]

def rawRow12373 : Integer.Sparse Key := [(key2716, -2), (key2716, -2), (key2711, -2), (key2980, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2711, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1)]

theorem rawRowCheck12373 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form5 = rawRow12373 := by decide +kernel

def row12373 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

theorem rowCheck12373 : row12373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12373 := by decide +kernel

theorem rowEval12373 (x : Key → ℝ) : Integer.Sparse.eval row12373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12373, Integer.Sparse.eval_collectBalanced, rawRowCheck12373]

def rawRow12374 : Integer.Sparse Key := [(key2980, -2), (key2980, -2), (key2980, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2716, -2), (key2711, -2), (key2711, -2), (key2711, -2), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1)]

theorem rawRowCheck12374 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form5 = rawRow12374 := by decide +kernel

def row12374 : Integer.Sparse Key := [(key2680, 6), (key2690, 6), (key2711, -6), (key2716, -12), (key2743, 6), (key2956, 6), (key2980, -6)]

theorem rowCheck12374 : row12374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12374 := by decide +kernel

theorem rowEval12374 (x : Key → ℝ) : Integer.Sparse.eval row12374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12374, Integer.Sparse.eval_collectBalanced, rawRowCheck12374]

def rawRow12375 : Integer.Sparse Key := [(key2741, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2743, -2), (key2741, -2), (key2901, -2), (key2743, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2901, -2), (key2683, 1), (key2690, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2716, 1), (key2819, 1)]

theorem rawRowCheck12375 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form5 = rawRow12375 := by decide +kernel

def row12375 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

theorem rowCheck12375 : row12375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12375 := by decide +kernel

theorem rowEval12375 (x : Key → ℝ) : Integer.Sparse.eval row12375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12375, Integer.Sparse.eval_collectBalanced, rawRowCheck12375]

def rawRow12376 : Integer.Sparse Key := [(key2743, -2), (key2741, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2901, -2), (key2741, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2901, -2), (key2743, -2), (key2690, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2716, 1)]

theorem rawRowCheck12376 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form5 = rawRow12376 := by decide +kernel

def row12376 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

theorem rowCheck12376 : row12376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12376 := by decide +kernel

theorem rowEval12376 (x : Key → ℝ) : Integer.Sparse.eval row12376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12376, Integer.Sparse.eval_collectBalanced, rawRowCheck12376]

def rawRow12377 : Integer.Sparse Key := [(key2743, -2), (key2743, -2), (key2741, -2), (key2901, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2741, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1)]

theorem rawRowCheck12377 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form5 = rawRow12377 := by decide +kernel

def row12377 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

theorem rowCheck12377 : row12377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12377 := by decide +kernel

theorem rowEval12377 (x : Key → ℝ) : Integer.Sparse.eval row12377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12377, Integer.Sparse.eval_collectBalanced, rawRowCheck12377]

def rawRow12378 : Integer.Sparse Key := [(key2901, -2), (key2901, -2), (key2901, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2743, -2), (key2741, -2), (key2741, -2), (key2741, -2), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1)]

theorem rawRowCheck12378 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form5 = rawRow12378 := by decide +kernel

def row12378 : Integer.Sparse Key := [(key2683, 6), (key2690, 6), (key2716, 6), (key2741, -6), (key2743, -12), (key2819, 6), (key2901, -6)]

theorem rowCheck12378 : row12378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12378 := by decide +kernel

theorem rowEval12378 (x : Key → ℝ) : Integer.Sparse.eval row12378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck12378, Integer.Sparse.eval_collectBalanced, rawRowCheck12378]

def rawRow12379 : Integer.Sparse Key := [(key3119, -24), (key3032, 6), (key3032, 6), (key3032, 6), (key3127, 6)]

theorem rawRowCheck12379 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form6 = rawRow12379 := by decide +kernel

def row12379 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

theorem rowCheck12379 : row12379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12379 := by decide +kernel

theorem rowEval12379 (x : Key → ℝ) : Integer.Sparse.eval row12379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12379, Integer.Sparse.eval_collectBalanced, rawRowCheck12379]

def rawRow12380 : Integer.Sparse Key := [(key3119, -24), (key3032, 6), (key3032, 6), (key3127, 6), (key3032, 6)]

theorem rawRowCheck12380 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form6 = rawRow12380 := by decide +kernel

def row12380 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

theorem rowCheck12380 : row12380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12380 := by decide +kernel

theorem rowEval12380 (x : Key → ℝ) : Integer.Sparse.eval row12380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12380, Integer.Sparse.eval_collectBalanced, rawRowCheck12380]

def rawRow12381 : Integer.Sparse Key := [(key3119, -24), (key3032, 6), (key3127, 6), (key3032, 6), (key3032, 6)]

theorem rawRowCheck12381 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form6 = rawRow12381 := by decide +kernel

def row12381 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

theorem rowCheck12381 : row12381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12381 := by decide +kernel

theorem rowEval12381 (x : Key → ℝ) : Integer.Sparse.eval row12381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12381, Integer.Sparse.eval_collectBalanced, rawRowCheck12381]

def rawRow12382 : Integer.Sparse Key := [(key3119, -24), (key3127, 6), (key3032, 6), (key3032, 6), (key3032, 6)]

theorem rawRowCheck12382 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form6 = rawRow12382 := by decide +kernel

def row12382 : Integer.Sparse Key := [(key3032, 18), (key3119, -24), (key3127, 6)]

theorem rowCheck12382 : row12382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12382 := by decide +kernel

theorem rowEval12382 (x : Key → ℝ) : Integer.Sparse.eval row12382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12382, Integer.Sparse.eval_collectBalanced, rawRowCheck12382]

def rawRow12383 : Integer.Sparse Key := [(key3127, -24), (key3032, 6), (key3032, 6), (key3032, 6), (key3119, 6)]

theorem rawRowCheck12383 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form6 = rawRow12383 := by decide +kernel

def row12383 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

theorem rowCheck12383 : row12383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12383 := by decide +kernel

theorem rowEval12383 (x : Key → ℝ) : Integer.Sparse.eval row12383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12383, Integer.Sparse.eval_collectBalanced, rawRowCheck12383]

def rawRow12384 : Integer.Sparse Key := [(key3127, -24), (key3032, 6), (key3032, 6), (key3119, 6), (key3032, 6)]

theorem rawRowCheck12384 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form6 = rawRow12384 := by decide +kernel

def row12384 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

theorem rowCheck12384 : row12384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12384 := by decide +kernel

theorem rowEval12384 (x : Key → ℝ) : Integer.Sparse.eval row12384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12384, Integer.Sparse.eval_collectBalanced, rawRowCheck12384]

def rawRow12385 : Integer.Sparse Key := [(key3127, -24), (key3032, 6), (key3119, 6), (key3032, 6), (key3032, 6)]

theorem rawRowCheck12385 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form6 = rawRow12385 := by decide +kernel

def row12385 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

theorem rowCheck12385 : row12385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12385 := by decide +kernel

theorem rowEval12385 (x : Key → ℝ) : Integer.Sparse.eval row12385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12385, Integer.Sparse.eval_collectBalanced, rawRowCheck12385]

def rawRow12386 : Integer.Sparse Key := [(key3127, -24), (key3119, 6), (key3032, 6), (key3032, 6), (key3032, 6)]

theorem rawRowCheck12386 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form6 = rawRow12386 := by decide +kernel

def row12386 : Integer.Sparse Key := [(key3032, 18), (key3119, 6), (key3127, -24)]

theorem rowCheck12386 : row12386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12386 := by decide +kernel

theorem rowEval12386 (x : Key → ℝ) : Integer.Sparse.eval row12386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck12386, Integer.Sparse.eval_collectBalanced, rawRowCheck12386]

def rawRow12387 : Integer.Sparse Key := [(key2814, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2819, -2), (key2814, -2), (key2901, -2), (key2819, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2901, -2), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2716, 2), (key2711, 2), (key2980, 2), (key2716, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2980, 2)]

theorem rawRowCheck12387 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form7 = rawRow12387 := by decide +kernel

def row12387 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

theorem rowCheck12387 : row12387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12387 := by decide +kernel

theorem rowEval12387 (x : Key → ℝ) : Integer.Sparse.eval row12387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12387, Integer.Sparse.eval_collectBalanced, rawRowCheck12387]

def rawRow12388 : Integer.Sparse Key := [(key2819, -2), (key2814, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2901, -2), (key2814, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2901, -2), (key2819, -2), (key2716, 2), (key2711, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, 2), (key2711, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2980, 2), (key2716, 2)]

theorem rawRowCheck12388 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form7 = rawRow12388 := by decide +kernel

def row12388 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

theorem rowCheck12388 : row12388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12388 := by decide +kernel

theorem rowEval12388 (x : Key → ℝ) : Integer.Sparse.eval row12388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12388, Integer.Sparse.eval_collectBalanced, rawRowCheck12388]

def rawRow12389 : Integer.Sparse Key := [(key2819, -2), (key2819, -2), (key2814, -2), (key2901, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2814, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2716, 2), (key2716, 2), (key2711, 2), (key2980, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2711, 2), (key2980, 2), (key2716, 2), (key2716, 2)]

theorem rawRowCheck12389 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form7 = rawRow12389 := by decide +kernel

def row12389 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

theorem rowCheck12389 : row12389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12389 := by decide +kernel

theorem rowEval12389 (x : Key → ℝ) : Integer.Sparse.eval row12389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12389, Integer.Sparse.eval_collectBalanced, rawRowCheck12389]

def rawRow12390 : Integer.Sparse Key := [(key2901, -2), (key2901, -2), (key2901, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2819, -2), (key2814, -2), (key2814, -2), (key2814, -2), (key2980, 2), (key2980, 2), (key2980, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2716, 2), (key2711, 2), (key2711, 2), (key2711, 2)]

theorem rawRowCheck12390 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form7 = rawRow12390 := by decide +kernel

def row12390 : Integer.Sparse Key := [(key2711, 6), (key2716, 12), (key2814, -6), (key2819, -12), (key2901, -6), (key2980, 6)]

theorem rowCheck12390 : row12390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12390 := by decide +kernel

theorem rowEval12390 (x : Key → ℝ) : Integer.Sparse.eval row12390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12390, Integer.Sparse.eval_collectBalanced, rawRowCheck12390]

def rawRow12391 : Integer.Sparse Key := [(key2954, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2956, -2), (key2954, -2), (key2980, -2), (key2956, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2980, -2), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2743, 2), (key2741, 2), (key2901, 2), (key2743, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2901, 2)]

theorem rawRowCheck12391 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form7 = rawRow12391 := by decide +kernel

def row12391 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

theorem rowCheck12391 : row12391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12391 := by decide +kernel

theorem rowEval12391 (x : Key → ℝ) : Integer.Sparse.eval row12391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12391, Integer.Sparse.eval_collectBalanced, rawRowCheck12391]

def rawRow12392 : Integer.Sparse Key := [(key2956, -2), (key2954, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2980, -2), (key2954, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2980, -2), (key2956, -2), (key2743, 2), (key2741, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, 2), (key2741, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2901, 2), (key2743, 2)]

theorem rawRowCheck12392 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form7 = rawRow12392 := by decide +kernel

def row12392 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

theorem rowCheck12392 : row12392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12392 := by decide +kernel

theorem rowEval12392 (x : Key → ℝ) : Integer.Sparse.eval row12392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12392, Integer.Sparse.eval_collectBalanced, rawRowCheck12392]

def rawRow12393 : Integer.Sparse Key := [(key2956, -2), (key2956, -2), (key2954, -2), (key2980, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2954, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2743, 2), (key2743, 2), (key2741, 2), (key2901, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2741, 2), (key2901, 2), (key2743, 2), (key2743, 2)]

theorem rawRowCheck12393 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form7 = rawRow12393 := by decide +kernel

def row12393 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

theorem rowCheck12393 : row12393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12393 := by decide +kernel

theorem rowEval12393 (x : Key → ℝ) : Integer.Sparse.eval row12393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12393, Integer.Sparse.eval_collectBalanced, rawRowCheck12393]

def rawRow12394 : Integer.Sparse Key := [(key2980, -2), (key2980, -2), (key2980, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2956, -2), (key2954, -2), (key2954, -2), (key2954, -2), (key2901, 2), (key2901, 2), (key2901, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2743, 2), (key2741, 2), (key2741, 2), (key2741, 2)]

theorem rawRowCheck12394 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form7 = rawRow12394 := by decide +kernel

def row12394 : Integer.Sparse Key := [(key2741, 6), (key2743, 12), (key2901, 6), (key2954, -6), (key2956, -12), (key2980, -6)]

theorem rowCheck12394 : row12394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12394 := by decide +kernel

theorem rowEval12394 (x : Key → ℝ) : Integer.Sparse.eval row12394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck12394, Integer.Sparse.eval_collectBalanced, rawRowCheck12394]

def rawRow12395 : Integer.Sparse Key := [(key1434, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1437, -2), (key1434, -2), (key1822, -2), (key1437, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1822, -2), (key1406, 1), (key1412, 1), (key1406, 1), (key1463, 1), (key1412, 1), (key1463, 1), (key1406, 1), (key1412, 1), (key1406, 1), (key1795, 1), (key1412, 1), (key1795, 1), (key1406, 1), (key1463, 1), (key1406, 1), (key1795, 1), (key1463, 1), (key1795, 1), (key1412, 1), (key1463, 1), (key1412, 1), (key1795, 1), (key1463, 1), (key1795, 1)]

theorem rawRowCheck12395 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form8 = rawRow12395 := by decide +kernel

def row12395 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

theorem rowCheck12395 : row12395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12395 := by decide +kernel

theorem rowEval12395 (x : Key → ℝ) : Integer.Sparse.eval row12395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12395, Integer.Sparse.eval_collectBalanced, rawRowCheck12395]

def rawRow12396 : Integer.Sparse Key := [(key1437, -2), (key1434, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1822, -2), (key1434, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1822, -2), (key1437, -2), (key1412, 1), (key1406, 1), (key1463, 1), (key1406, 1), (key1463, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1795, 1), (key1406, 1), (key1795, 1), (key1412, 1), (key1463, 1), (key1406, 1), (key1795, 1), (key1406, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1412, 1), (key1795, 1), (key1412, 1), (key1795, 1), (key1463, 1)]

theorem rawRowCheck12396 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form8 = rawRow12396 := by decide +kernel

def row12396 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

theorem rowCheck12396 : row12396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12396 := by decide +kernel

theorem rowEval12396 (x : Key → ℝ) : Integer.Sparse.eval row12396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12396, Integer.Sparse.eval_collectBalanced, rawRowCheck12396]

def rawRow12397 : Integer.Sparse Key := [(key1437, -2), (key1437, -2), (key1434, -2), (key1822, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1434, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1463, 1), (key1463, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1406, 1), (key1795, 1), (key1795, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1406, 1), (key1795, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1406, 1), (key1406, 1), (key1795, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1412, 1), (key1412, 1)]

theorem rawRowCheck12397 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form8 = rawRow12397 := by decide +kernel

def row12397 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

theorem rowCheck12397 : row12397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12397 := by decide +kernel

theorem rowEval12397 (x : Key → ℝ) : Integer.Sparse.eval row12397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12397, Integer.Sparse.eval_collectBalanced, rawRowCheck12397]

def rawRow12398 : Integer.Sparse Key := [(key1822, -2), (key1822, -2), (key1822, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1437, -2), (key1434, -2), (key1434, -2), (key1434, -2), (key1795, 1), (key1795, 1), (key1795, 1), (key1795, 1), (key1795, 1), (key1795, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1463, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1406, 1), (key1406, 1), (key1406, 1), (key1406, 1), (key1406, 1), (key1406, 1)]

theorem rawRowCheck12398 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form8 = rawRow12398 := by decide +kernel

def row12398 : Integer.Sparse Key := [(key1406, 6), (key1412, 6), (key1434, -6), (key1437, -12), (key1463, 6), (key1795, 6), (key1822, -6)]

theorem rowCheck12398 : row12398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12398 := by decide +kernel

theorem rowEval12398 (x : Key → ℝ) : Integer.Sparse.eval row12398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12398, Integer.Sparse.eval_collectBalanced, rawRowCheck12398]

def rawRow12399 : Integer.Sparse Key := [(key1462, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1463, -2), (key1462, -2), (key1664, -2), (key1463, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1664, -2), (key1408, 1), (key1412, 1), (key1408, 1), (key1437, 1), (key1412, 1), (key1437, 1), (key1408, 1), (key1412, 1), (key1408, 1), (key1586, 1), (key1412, 1), (key1586, 1), (key1408, 1), (key1437, 1), (key1408, 1), (key1586, 1), (key1437, 1), (key1586, 1), (key1412, 1), (key1437, 1), (key1412, 1), (key1586, 1), (key1437, 1), (key1586, 1)]

theorem rawRowCheck12399 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form8 = rawRow12399 := by decide +kernel

def row12399 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

theorem rowCheck12399 : row12399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12399 := by decide +kernel

theorem rowEval12399 (x : Key → ℝ) : Integer.Sparse.eval row12399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12399, Integer.Sparse.eval_collectBalanced, rawRowCheck12399]

def rawRow12400 : Integer.Sparse Key := [(key1463, -2), (key1462, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1664, -2), (key1462, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1664, -2), (key1463, -2), (key1412, 1), (key1408, 1), (key1437, 1), (key1408, 1), (key1437, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1586, 1), (key1408, 1), (key1586, 1), (key1412, 1), (key1437, 1), (key1408, 1), (key1586, 1), (key1408, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1412, 1), (key1586, 1), (key1412, 1), (key1586, 1), (key1437, 1)]

theorem rawRowCheck12400 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form8 = rawRow12400 := by decide +kernel

def row12400 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

theorem rowCheck12400 : row12400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12400 := by decide +kernel

theorem rowEval12400 (x : Key → ℝ) : Integer.Sparse.eval row12400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12400, Integer.Sparse.eval_collectBalanced, rawRowCheck12400]

def rawRow12401 : Integer.Sparse Key := [(key1463, -2), (key1463, -2), (key1462, -2), (key1664, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1462, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1437, 1), (key1437, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1408, 1), (key1586, 1), (key1586, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1408, 1), (key1586, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1408, 1), (key1408, 1), (key1586, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1412, 1), (key1412, 1)]

theorem rawRowCheck12401 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form8 = rawRow12401 := by decide +kernel

def row12401 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

theorem rowCheck12401 : row12401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12401 := by decide +kernel

theorem rowEval12401 (x : Key → ℝ) : Integer.Sparse.eval row12401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12401, Integer.Sparse.eval_collectBalanced, rawRowCheck12401]

def rawRow12402 : Integer.Sparse Key := [(key1664, -2), (key1664, -2), (key1664, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1463, -2), (key1462, -2), (key1462, -2), (key1462, -2), (key1586, 1), (key1586, 1), (key1586, 1), (key1586, 1), (key1586, 1), (key1586, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1437, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1412, 1), (key1408, 1), (key1408, 1), (key1408, 1), (key1408, 1), (key1408, 1), (key1408, 1)]

theorem rawRowCheck12402 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form8 = rawRow12402 := by decide +kernel

def row12402 : Integer.Sparse Key := [(key1408, 6), (key1412, 6), (key1437, 6), (key1462, -6), (key1463, -12), (key1586, 6), (key1664, -6)]

theorem rowCheck12402 : row12402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12402 := by decide +kernel

theorem rowEval12402 (x : Key → ℝ) : Integer.Sparse.eval row12402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck12402, Integer.Sparse.eval_collectBalanced, rawRowCheck12402]

def rawRow12403 : Integer.Sparse Key := [(key2680, 1), (key2690, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2743, 1), (key2956, 1), (key2683, -2), (key2683, -2), (key2741, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2741, -2), (key2683, -2), (key2954, -2), (key2741, -2), (key2954, -2)]

theorem rawRowCheck12403 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form9 = rawRow12403 := by decide +kernel

def row12403 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

theorem rowCheck12403 : row12403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12403 := by decide +kernel

theorem rowEval12403 (x : Key → ℝ) : Integer.Sparse.eval row12403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12403, Integer.Sparse.eval_collectBalanced, rawRowCheck12403]

def rawRow12404 : Integer.Sparse Key := [(key2690, 1), (key2680, 1), (key2743, 1), (key2680, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2690, 1), (key2743, 1), (key2680, 1), (key2956, 1), (key2680, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2956, 1), (key2690, 1), (key2956, 1), (key2743, 1), (key2683, -2), (key2741, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2741, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2954, -2), (key2741, -2)]

theorem rawRowCheck12404 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form9 = rawRow12404 := by decide +kernel

def row12404 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

theorem rowCheck12404 : row12404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12404 := by decide +kernel

theorem rowEval12404 (x : Key → ℝ) : Integer.Sparse.eval row12404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12404, Integer.Sparse.eval_collectBalanced, rawRowCheck12404]

def rawRow12405 : Integer.Sparse Key := [(key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2680, 1), (key2680, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2741, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2683, -2), (key2683, -2), (key2954, -2), (key2954, -2), (key2741, -2), (key2741, -2), (key2683, -2), (key2683, -2)]

theorem rawRowCheck12405 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form9 = rawRow12405 := by decide +kernel

def row12405 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

theorem rowCheck12405 : row12405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12405 := by decide +kernel

theorem rowEval12405 (x : Key → ℝ) : Integer.Sparse.eval row12405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12405, Integer.Sparse.eval_collectBalanced, rawRowCheck12405]

def rawRow12406 : Integer.Sparse Key := [(key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2956, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2743, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2680, 1), (key2954, -2), (key2954, -2), (key2954, -2), (key2741, -2), (key2741, -2), (key2741, -2), (key2683, -2), (key2683, -2), (key2683, -2), (key2683, -2), (key2683, -2), (key2683, -2)]

theorem rawRowCheck12406 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form9 = rawRow12406 := by decide +kernel

def row12406 : Integer.Sparse Key := [(key2680, 6), (key2683, -12), (key2690, 6), (key2741, -6), (key2743, 6), (key2954, -6), (key2956, 6)]

theorem rowCheck12406 : row12406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12406 := by decide +kernel

theorem rowEval12406 (x : Key → ℝ) : Integer.Sparse.eval row12406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12406, Integer.Sparse.eval_collectBalanced, rawRowCheck12406]

def rawRow12407 : Integer.Sparse Key := [(key2683, 1), (key2690, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2716, 1), (key2819, 1), (key2680, -2), (key2680, -2), (key2711, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2711, -2), (key2680, -2), (key2814, -2), (key2711, -2), (key2814, -2)]

theorem rawRowCheck12407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form9 = rawRow12407 := by decide +kernel

def row12407 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

theorem rowCheck12407 : row12407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12407 := by decide +kernel

theorem rowEval12407 (x : Key → ℝ) : Integer.Sparse.eval row12407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12407, Integer.Sparse.eval_collectBalanced, rawRowCheck12407]

def rawRow12408 : Integer.Sparse Key := [(key2690, 1), (key2683, 1), (key2716, 1), (key2683, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2690, 1), (key2716, 1), (key2683, 1), (key2819, 1), (key2683, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2819, 1), (key2690, 1), (key2819, 1), (key2716, 1), (key2680, -2), (key2711, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2711, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2814, -2), (key2711, -2)]

theorem rawRowCheck12408 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form9 = rawRow12408 := by decide +kernel

def row12408 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

theorem rowCheck12408 : row12408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12408 := by decide +kernel

theorem rowEval12408 (x : Key → ℝ) : Integer.Sparse.eval row12408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12408, Integer.Sparse.eval_collectBalanced, rawRowCheck12408]

def rawRow12409 : Integer.Sparse Key := [(key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2683, 1), (key2683, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2711, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2680, -2), (key2680, -2), (key2814, -2), (key2814, -2), (key2711, -2), (key2711, -2), (key2680, -2), (key2680, -2)]

theorem rawRowCheck12409 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form9 = rawRow12409 := by decide +kernel

def row12409 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

theorem rowCheck12409 : row12409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12409 := by decide +kernel

theorem rowEval12409 (x : Key → ℝ) : Integer.Sparse.eval row12409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12409, Integer.Sparse.eval_collectBalanced, rawRowCheck12409]

def rawRow12410 : Integer.Sparse Key := [(key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2819, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2716, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2690, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2683, 1), (key2814, -2), (key2814, -2), (key2814, -2), (key2711, -2), (key2711, -2), (key2711, -2), (key2680, -2), (key2680, -2), (key2680, -2), (key2680, -2), (key2680, -2), (key2680, -2)]

theorem rawRowCheck12410 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form9 = rawRow12410 := by decide +kernel

def row12410 : Integer.Sparse Key := [(key2680, -12), (key2683, 6), (key2690, 6), (key2711, -6), (key2716, 6), (key2814, -6), (key2819, 6)]

theorem rowCheck12410 : row12410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12410 := by decide +kernel

theorem rowEval12410 (x : Key → ℝ) : Integer.Sparse.eval row12410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck12410, Integer.Sparse.eval_collectBalanced, rawRowCheck12410]

def rawRow12411 : Integer.Sparse Key := [(key1431, -6), (key1431, -6), (key1431, -6), (key1821, -6), (key1403, 2), (key1403, 2), (key1461, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1461, 2), (key1403, 2), (key1794, 2), (key1461, 2), (key1794, 2)]

theorem rawRowCheck12411 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form10 = rawRow12411 := by decide +kernel

def row12411 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

theorem rowCheck12411 : row12411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12411 := by decide +kernel

theorem rowEval12411 (x : Key → ℝ) : Integer.Sparse.eval row12411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12411, Integer.Sparse.eval_collectBalanced, rawRowCheck12411]

def rawRow12412 : Integer.Sparse Key := [(key1431, -6), (key1431, -6), (key1821, -6), (key1431, -6), (key1403, 2), (key1461, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1461, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1794, 2), (key1461, 2)]

theorem rawRowCheck12412 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form10 = rawRow12412 := by decide +kernel

def row12412 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

theorem rowCheck12412 : row12412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12412 := by decide +kernel

theorem rowEval12412 (x : Key → ℝ) : Integer.Sparse.eval row12412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12412, Integer.Sparse.eval_collectBalanced, rawRowCheck12412]

def rawRow12413 : Integer.Sparse Key := [(key1431, -6), (key1821, -6), (key1431, -6), (key1431, -6), (key1461, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1403, 2), (key1403, 2), (key1794, 2), (key1794, 2), (key1461, 2), (key1461, 2), (key1403, 2), (key1403, 2)]

theorem rawRowCheck12413 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form10 = rawRow12413 := by decide +kernel

def row12413 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

theorem rowCheck12413 : row12413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12413 := by decide +kernel

theorem rowEval12413 (x : Key → ℝ) : Integer.Sparse.eval row12413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12413, Integer.Sparse.eval_collectBalanced, rawRowCheck12413]

def rawRow12414 : Integer.Sparse Key := [(key1821, -6), (key1431, -6), (key1431, -6), (key1431, -6), (key1794, 2), (key1794, 2), (key1794, 2), (key1461, 2), (key1461, 2), (key1461, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2), (key1403, 2)]

theorem rawRowCheck12414 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form10 = rawRow12414 := by decide +kernel

def row12414 : Integer.Sparse Key := [(key1403, 12), (key1431, -18), (key1461, 6), (key1794, 6), (key1821, -6)]

theorem rowCheck12414 : row12414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12414 := by decide +kernel

theorem rowEval12414 (x : Key → ℝ) : Integer.Sparse.eval row12414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck12414, Integer.Sparse.eval_collectBalanced, rawRowCheck12414]

def rawRow12415 : Integer.Sparse Key := [(key1461, -6), (key1461, -6), (key1461, -6), (key1663, -6), (key1403, 2), (key1403, 2), (key1431, 2), (key1403, 2), (key1403, 2), (key1580, 2), (key1403, 2), (key1431, 2), (key1403, 2), (key1580, 2), (key1431, 2), (key1580, 2)]

theorem rawRowCheck12415 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form10 = rawRow12415 := by decide +kernel

def row12415 : Integer.Sparse Key := [(key1403, 12), (key1431, 6), (key1461, -18), (key1580, 6), (key1663, -6)]

theorem rowCheck12415 : row12415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12415 := by decide +kernel

theorem rowEval12415 (x : Key → ℝ) : Integer.Sparse.eval row12415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12415, Integer.Sparse.eval_collectBalanced, rawRowCheck12415]

end MUB6.Certificate.GramRows

end OAI
