import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow5248 : Integer.Sparse Key := [(key331, -1), (key321, -1), (key316, 2), (key347, -1), (key346, -1), (key331, 2), (key307, 2), (key316, -1), (key302, -1), (key346, 2), (key321, -1), (key307, -1), (key421, 1), (key411, 1), (key406, -2), (key658, 1), (key657, 1), (key421, -2), (key241, -2), (key406, 1), (key236, 1), (key421, -2), (key411, 1), (key241, 1), (key660, -1), (key321, -1), (key435, 1), (key316, 1), (key660, 1), (key253, 1), (key435, -1), (key248, -1), (key662, -1), (key331, -1), (key661, 1), (key263, 1), (key453, 1), (key331, 1), (key445, -1), (key263, -1)]

theorem rawRowCheck5248 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form1 = rawRow5248 := by decide +kernel

def row5248 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -3), (key445, -1), (key453, 1), (key657, 1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5248 : row5248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5248 := by decide +kernel

theorem rowEval5248 (x : Key → ℝ) : Integer.Sparse.eval row5248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5248, Integer.Sparse.eval_collectBalanced, rawRowCheck5248]

def rawRow5249 : Integer.Sparse Key := [(key346, -1), (key346, -1), (key347, 2), (key307, -1), (key307, -1), (key321, 2), (key321, 2), (key331, -1), (key331, -1), (key302, 2), (key316, -1), (key316, -1), (key657, 1), (key657, 1), (key658, -2), (key241, 1), (key241, 1), (key411, -2), (key411, -2), (key421, 1), (key421, 1), (key236, -2), (key406, 1), (key406, 1), (key453, -1), (key453, -1), (key662, 1), (key662, 1), (key445, 1), (key445, 1), (key661, -1), (key661, -1), (key253, -1), (key253, -1), (key321, 1), (key321, 1), (key248, 1), (key248, 1), (key316, -1), (key316, -1)]

theorem rawRowCheck5249 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form1 = rawRow5249 := by decide +kernel

def row5249 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key253, -2), (key302, 2), (key307, -2), (key316, -4), (key321, 6), (key331, -2), (key346, -2), (key347, 2), (key406, 2), (key411, -4), (key421, 2), (key445, 2), (key453, -2), (key657, 2), (key658, -2), (key661, -2), (key662, 2)]

theorem rowCheck5249 : row5249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5249 := by decide +kernel

theorem rowEval5249 (x : Key → ℝ) : Integer.Sparse.eval row5249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5249, Integer.Sparse.eval_collectBalanced, rawRowCheck5249]

def rawRow5250 : Integer.Sparse Key := [(key346, -1), (key347, -1), (key346, 2), (key321, -1), (key331, -1), (key307, 2), (key331, 2), (key307, -1), (key321, -1), (key316, 2), (key302, -1), (key316, -1), (key657, 1), (key658, 1), (key657, -2), (key411, 1), (key421, 1), (key241, -2), (key421, -2), (key241, 1), (key411, 1), (key406, -2), (key236, 1), (key406, 1), (key331, -1), (key662, -1), (key331, 1), (key453, 1), (key263, 1), (key661, 1), (key263, -1), (key445, -1), (key321, -1), (key660, -1), (key253, 1), (key660, 1), (key316, 1), (key435, 1), (key248, -1), (key435, -1)]

theorem rawRowCheck5250 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form1 = rawRow5250 := by decide +kernel

def row5250 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5250 : row5250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5250 := by decide +kernel

theorem rowEval5250 (x : Key → ℝ) : Integer.Sparse.eval row5250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5250, Integer.Sparse.eval_collectBalanced, rawRowCheck5250]

def rawRow5251 : Integer.Sparse Key := [(key347, -1), (key346, -1), (key346, 2), (key331, -1), (key321, -1), (key331, 2), (key307, 2), (key321, -1), (key307, -1), (key316, 2), (key316, -1), (key302, -1), (key658, 1), (key657, 1), (key657, -2), (key421, 1), (key411, 1), (key421, -2), (key241, -2), (key411, 1), (key241, 1), (key406, -2), (key406, 1), (key236, 1), (key662, -1), (key331, -1), (key453, 1), (key331, 1), (key661, 1), (key263, 1), (key445, -1), (key263, -1), (key660, -1), (key321, -1), (key660, 1), (key253, 1), (key435, 1), (key316, 1), (key435, -1), (key248, -1)]

theorem rawRowCheck5251 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form1 = rawRow5251 := by decide +kernel

def row5251 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 2), (key321, -3), (key331, 1), (key346, 1), (key347, -1), (key406, -1), (key411, 2), (key421, -1), (key445, -1), (key453, 1), (key657, -1), (key658, 1), (key661, 1), (key662, -1)]

theorem rowCheck5251 : row5251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5251 := by decide +kernel

theorem rowEval5251 (x : Key → ℝ) : Integer.Sparse.eval row5251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5251, Integer.Sparse.eval_collectBalanced, rawRowCheck5251]

def rawRow5252 : Integer.Sparse Key := [(key385, -1), (key400, -1), (key390, 2), (key435, -1), (key445, -1), (key406, 2), (key488, 2), (key411, -1), (key487, -1), (key453, 2), (key421, -1), (key489, -1), (key248, 1), (key263, 1), (key253, -2), (key435, 1), (key445, 1), (key316, -2), (key661, -2), (key321, 1), (key660, 1), (key453, -2), (key331, 1), (key662, 1), (key236, -1), (key278, -1), (key241, 1), (key263, 1), (key302, 1), (key347, 1), (key307, -1), (key331, -1), (key406, -1), (key488, -1), (key385, 1), (key489, 1), (key657, 1), (key661, 1), (key655, -1), (key662, -1)]

theorem rawRowCheck5252 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block2.form1 = rawRow5252 := by decide +kernel

def row5252 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -2), (key321, 1), (key347, 1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key421, -1), (key487, -1), (key488, 1), (key655, -1), (key657, 1), (key660, 1), (key661, -1)]

theorem rowCheck5252 : row5252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5252 := by decide +kernel

theorem rowEval5252 (x : Key → ℝ) : Integer.Sparse.eval row5252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5252, Integer.Sparse.eval_collectBalanced, rawRowCheck5252]

def rawRow5253 : Integer.Sparse Key := [(key400, -1), (key385, -1), (key390, 2), (key445, -1), (key435, -1), (key488, 2), (key406, 2), (key487, -1), (key411, -1), (key453, 2), (key489, -1), (key421, -1), (key263, 1), (key248, 1), (key253, -2), (key445, 1), (key435, 1), (key661, -2), (key316, -2), (key660, 1), (key321, 1), (key453, -2), (key662, 1), (key331, 1), (key278, -1), (key236, -1), (key263, 1), (key241, 1), (key347, 1), (key302, 1), (key331, -1), (key307, -1), (key488, -1), (key406, -1), (key489, 1), (key385, 1), (key661, 1), (key657, 1), (key662, -1), (key655, -1)]

theorem rawRowCheck5253 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block2.form1 = rawRow5253 := by decide +kernel

def row5253 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -2), (key321, 1), (key347, 1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key421, -1), (key487, -1), (key488, 1), (key655, -1), (key657, 1), (key660, 1), (key661, -1)]

theorem rowCheck5253 : row5253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5253 := by decide +kernel

theorem rowEval5253 (x : Key → ℝ) : Integer.Sparse.eval row5253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5253, Integer.Sparse.eval_collectBalanced, rawRowCheck5253]

def rawRow5254 : Integer.Sparse Key := [(key390, -1), (key400, -1), (key385, 2), (key487, -1), (key488, -1), (key411, 2), (key445, 2), (key406, -1), (key435, -1), (key489, 2), (key421, -1), (key453, -1), (key253, 1), (key263, 1), (key248, -2), (key660, 1), (key661, 1), (key321, -2), (key445, -2), (key316, 1), (key435, 1), (key662, -2), (key331, 1), (key453, 1), (key241, -1), (key263, -1), (key236, 1), (key248, 1), (key307, 1), (key346, 1), (key302, -1), (key316, -1), (key421, -1), (key489, -1), (key400, 1), (key488, 1), (key658, 1), (key662, 1), (key656, -1), (key661, -1)]

theorem rawRowCheck5254 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form1 = rawRow5254 := by decide +kernel

def row5254 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key656, -1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5254 : row5254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5254 := by decide +kernel

theorem rowEval5254 (x : Key → ℝ) : Integer.Sparse.eval row5254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5254, Integer.Sparse.eval_collectBalanced, rawRowCheck5254]

def rawRow5255 : Integer.Sparse Key := [(key400, -1), (key390, -1), (key385, 2), (key488, -1), (key487, -1), (key445, 2), (key411, 2), (key435, -1), (key406, -1), (key489, 2), (key453, -1), (key421, -1), (key263, 1), (key253, 1), (key248, -2), (key661, 1), (key660, 1), (key445, -2), (key321, -2), (key435, 1), (key316, 1), (key662, -2), (key453, 1), (key331, 1), (key263, -1), (key241, -1), (key248, 1), (key236, 1), (key346, 1), (key307, 1), (key316, -1), (key302, -1), (key489, -1), (key421, -1), (key488, 1), (key400, 1), (key662, 1), (key658, 1), (key661, -1), (key656, -1)]

theorem rawRowCheck5255 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form1 = rawRow5255 := by decide +kernel

def row5255 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key656, -1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5255 : row5255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5255 := by decide +kernel

theorem rowEval5255 (x : Key → ℝ) : Integer.Sparse.eval row5255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5255, Integer.Sparse.eval_collectBalanced, rawRowCheck5255]

def rawRow5256 : Integer.Sparse Key := [(key406, -1), (key421, -1), (key411, 2), (key435, -1), (key453, -1), (key385, 2), (key489, 2), (key390, -1), (key487, -1), (key445, 2), (key400, -1), (key488, -1), (key316, 1), (key331, 1), (key321, -2), (key435, 1), (key453, 1), (key248, -2), (key662, -2), (key253, 1), (key660, 1), (key445, -2), (key263, 1), (key661, 1), (key302, -1), (key347, -1), (key307, 1), (key346, 1), (key236, 1), (key658, 1), (key241, -1), (key421, -1), (key316, -1), (key661, -1), (key248, 1), (key662, 1), (key346, 1), (key488, 1), (key277, -1), (key489, -1)]

theorem rawRowCheck5256 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form1 = rawRow5256 := by decide +kernel

def row5256 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key263, 1), (key277, -1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 2), (key347, -1), (key385, 2), (key390, -1), (key400, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5256 : row5256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5256 := by decide +kernel

theorem rowEval5256 (x : Key → ℝ) : Integer.Sparse.eval row5256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5256, Integer.Sparse.eval_collectBalanced, rawRowCheck5256]

def rawRow5257 : Integer.Sparse Key := [(key421, -1), (key406, -1), (key411, 2), (key453, -1), (key435, -1), (key489, 2), (key385, 2), (key487, -1), (key390, -1), (key445, 2), (key488, -1), (key400, -1), (key331, 1), (key316, 1), (key321, -2), (key453, 1), (key435, 1), (key662, -2), (key248, -2), (key660, 1), (key253, 1), (key445, -2), (key661, 1), (key263, 1), (key347, -1), (key302, -1), (key346, 1), (key307, 1), (key658, 1), (key236, 1), (key421, -1), (key241, -1), (key661, -1), (key316, -1), (key662, 1), (key248, 1), (key488, 1), (key346, 1), (key489, -1), (key277, -1)]

theorem rawRowCheck5257 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form1 = rawRow5257 := by decide +kernel

def row5257 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key263, 1), (key277, -1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 2), (key347, -1), (key385, 2), (key390, -1), (key400, -1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5257 : row5257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5257 := by decide +kernel

theorem rowEval5257 (x : Key → ℝ) : Integer.Sparse.eval row5257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5257, Integer.Sparse.eval_collectBalanced, rawRowCheck5257]

def rawRow5258 : Integer.Sparse Key := [(key411, -1), (key421, -1), (key406, 2), (key487, -1), (key489, -1), (key390, 2), (key453, 2), (key385, -1), (key435, -1), (key488, 2), (key400, -1), (key445, -1), (key321, 1), (key331, 1), (key316, -2), (key660, 1), (key662, 1), (key253, -2), (key453, -2), (key248, 1), (key435, 1), (key661, -2), (key263, 1), (key445, 1), (key307, -1), (key331, -1), (key302, 1), (key316, 1), (key241, 1), (key421, 1), (key236, -1), (key406, -1), (key331, -1), (key662, -1), (key263, 1), (key661, 1), (key347, 1), (key489, 1), (key278, -1), (key488, -1)]

theorem rawRowCheck5258 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block2.form1 = rawRow5258 := by decide +kernel

def row5258 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

theorem rowCheck5258 : row5258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5258 := by decide +kernel

theorem rowEval5258 (x : Key → ℝ) : Integer.Sparse.eval row5258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5258, Integer.Sparse.eval_collectBalanced, rawRowCheck5258]

def rawRow5259 : Integer.Sparse Key := [(key421, -1), (key411, -1), (key406, 2), (key489, -1), (key487, -1), (key453, 2), (key390, 2), (key435, -1), (key385, -1), (key488, 2), (key445, -1), (key400, -1), (key331, 1), (key321, 1), (key316, -2), (key662, 1), (key660, 1), (key453, -2), (key253, -2), (key435, 1), (key248, 1), (key661, -2), (key445, 1), (key263, 1), (key331, -1), (key307, -1), (key316, 1), (key302, 1), (key421, 1), (key241, 1), (key406, -1), (key236, -1), (key662, -1), (key331, -1), (key661, 1), (key263, 1), (key489, 1), (key347, 1), (key488, -1), (key278, -1)]

theorem rawRowCheck5259 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block2.form1 = rawRow5259 := by decide +kernel

def row5259 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

theorem rowCheck5259 : row5259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5259 := by decide +kernel

theorem rowEval5259 (x : Key → ℝ) : Integer.Sparse.eval row5259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5259, Integer.Sparse.eval_collectBalanced, rawRowCheck5259]

def rawRow5260 : Integer.Sparse Key := [(key435, -1), (key445, -1), (key453, 2), (key385, -1), (key400, -1), (key406, 2), (key488, 2), (key421, -1), (key489, -1), (key390, 2), (key411, -1), (key487, -1), (key435, 1), (key445, 1), (key453, -2), (key248, 1), (key263, 1), (key316, -2), (key661, -2), (key331, 1), (key662, 1), (key253, -2), (key321, 1), (key660, 1), (key406, -1), (key488, -1), (key421, 1), (key489, 1), (key316, 1), (key661, 1), (key331, -1), (key662, -1), (key236, -1), (key278, -1), (key302, 1), (key347, 1), (key241, 1), (key263, 1), (key307, -1), (key331, -1)]

theorem rawRowCheck5260 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block2.form1 = rawRow5260 := by decide +kernel

def row5260 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

theorem rowCheck5260 : row5260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5260 := by decide +kernel

theorem rowEval5260 (x : Key → ℝ) : Integer.Sparse.eval row5260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5260, Integer.Sparse.eval_collectBalanced, rawRowCheck5260]

def rawRow5261 : Integer.Sparse Key := [(key445, -1), (key435, -1), (key453, 2), (key400, -1), (key385, -1), (key488, 2), (key406, 2), (key489, -1), (key421, -1), (key390, 2), (key487, -1), (key411, -1), (key445, 1), (key435, 1), (key453, -2), (key263, 1), (key248, 1), (key661, -2), (key316, -2), (key662, 1), (key331, 1), (key253, -2), (key660, 1), (key321, 1), (key488, -1), (key406, -1), (key489, 1), (key421, 1), (key661, 1), (key316, 1), (key662, -1), (key331, -1), (key278, -1), (key236, -1), (key347, 1), (key302, 1), (key263, 1), (key241, 1), (key331, -1), (key307, -1)]

theorem rawRowCheck5261 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block2.form1 = rawRow5261 := by decide +kernel

def row5261 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 2), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key331, -1), (key347, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key660, 1), (key661, -1)]

theorem rowCheck5261 : row5261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5261 := by decide +kernel

theorem rowEval5261 (x : Key → ℝ) : Integer.Sparse.eval row5261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5261, Integer.Sparse.eval_collectBalanced, rawRowCheck5261]

def rawRow5262 : Integer.Sparse Key := [(key435, -1), (key453, -1), (key445, 2), (key406, -1), (key421, -1), (key385, 2), (key489, 2), (key400, -1), (key488, -1), (key411, 2), (key390, -1), (key487, -1), (key435, 1), (key453, 1), (key445, -2), (key316, 1), (key331, 1), (key248, -2), (key662, -2), (key263, 1), (key661, 1), (key321, -2), (key253, 1), (key660, 1), (key385, -1), (key489, -1), (key400, 1), (key488, 1), (key248, 1), (key662, 1), (key263, -1), (key661, -1), (key302, -1), (key347, -1), (key236, 1), (key658, 1), (key307, 1), (key400, 1), (key241, -1), (key421, -1)]

theorem rawRowCheck5262 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form1 = rawRow5262 := by decide +kernel

def row5262 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 1), (key321, -2), (key331, 1), (key347, -1), (key385, 1), (key390, -1), (key400, 1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5262 : row5262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5262 := by decide +kernel

theorem rowEval5262 (x : Key → ℝ) : Integer.Sparse.eval row5262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5262, Integer.Sparse.eval_collectBalanced, rawRowCheck5262]

def rawRow5263 : Integer.Sparse Key := [(key453, -1), (key435, -1), (key445, 2), (key421, -1), (key406, -1), (key489, 2), (key385, 2), (key488, -1), (key400, -1), (key411, 2), (key487, -1), (key390, -1), (key453, 1), (key435, 1), (key445, -2), (key331, 1), (key316, 1), (key662, -2), (key248, -2), (key661, 1), (key263, 1), (key321, -2), (key660, 1), (key253, 1), (key489, -1), (key385, -1), (key488, 1), (key400, 1), (key662, 1), (key248, 1), (key661, -1), (key263, -1), (key347, -1), (key302, -1), (key658, 1), (key236, 1), (key400, 1), (key307, 1), (key421, -1), (key241, -1)]

theorem rawRowCheck5263 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form1 = rawRow5263 := by decide +kernel

def row5263 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key316, 1), (key321, -2), (key331, 1), (key347, -1), (key385, 1), (key390, -1), (key400, 1), (key406, -1), (key411, 2), (key421, -2), (key487, -1), (key489, 1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5263 : row5263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5263 := by decide +kernel

theorem rowEval5263 (x : Key → ℝ) : Integer.Sparse.eval row5263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5263, Integer.Sparse.eval_collectBalanced, rawRowCheck5263]

def rawRow5264 : Integer.Sparse Key := [(key487, -1), (key488, -1), (key489, 2), (key390, -1), (key400, -1), (key411, 2), (key445, 2), (key421, -1), (key453, -1), (key385, 2), (key406, -1), (key435, -1), (key660, 1), (key661, 1), (key662, -2), (key253, 1), (key263, 1), (key321, -2), (key445, -2), (key331, 1), (key453, 1), (key248, -2), (key316, 1), (key435, 1), (key657, -1), (key661, -1), (key658, 1), (key662, 1), (key346, 1), (key488, 1), (key347, -1), (key489, -1), (key241, -1), (key263, -1), (key307, 1), (key400, 1), (key236, 1), (key248, 1), (key302, -1), (key316, -1)]

theorem rawRowCheck5264 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form1 = rawRow5264 := by decide +kernel

def row5264 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key347, -1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -1), (key487, -1), (key489, 1), (key657, -1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5264 : row5264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5264 := by decide +kernel

theorem rowEval5264 (x : Key → ℝ) : Integer.Sparse.eval row5264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5264, Integer.Sparse.eval_collectBalanced, rawRowCheck5264]

def rawRow5265 : Integer.Sparse Key := [(key488, -1), (key487, -1), (key489, 2), (key400, -1), (key390, -1), (key445, 2), (key411, 2), (key453, -1), (key421, -1), (key385, 2), (key435, -1), (key406, -1), (key661, 1), (key660, 1), (key662, -2), (key263, 1), (key253, 1), (key445, -2), (key321, -2), (key453, 1), (key331, 1), (key248, -2), (key435, 1), (key316, 1), (key661, -1), (key657, -1), (key662, 1), (key658, 1), (key488, 1), (key346, 1), (key489, -1), (key347, -1), (key263, -1), (key241, -1), (key400, 1), (key307, 1), (key248, 1), (key236, 1), (key316, -1), (key302, -1)]

theorem rawRowCheck5265 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form1 = rawRow5265 := by decide +kernel

def row5265 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key253, 1), (key302, -1), (key307, 1), (key321, -2), (key331, 1), (key346, 1), (key347, -1), (key385, 2), (key390, -1), (key406, -1), (key411, 2), (key421, -1), (key487, -1), (key489, 1), (key657, -1), (key658, 1), (key660, 1), (key662, -1)]

theorem rowCheck5265 : row5265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5265 := by decide +kernel

theorem rowEval5265 (x : Key → ℝ) : Integer.Sparse.eval row5265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5265, Integer.Sparse.eval_collectBalanced, rawRowCheck5265]

def rawRow5266 : Integer.Sparse Key := [(key487, -1), (key489, -1), (key488, 2), (key411, -1), (key421, -1), (key390, 2), (key453, 2), (key400, -1), (key445, -1), (key406, 2), (key385, -1), (key435, -1), (key660, 1), (key662, 1), (key661, -2), (key321, 1), (key331, 1), (key253, -2), (key453, -2), (key263, 1), (key445, 1), (key316, -2), (key248, 1), (key435, 1), (key655, -1), (key662, -1), (key656, 1), (key661, 1), (key277, 1), (key489, 1), (key278, -1), (key488, -1), (key307, -1), (key331, -1), (key241, 1), (key421, 1), (key302, 1), (key316, 1), (key236, -1), (key406, -1)]

theorem rawRowCheck5266 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block2.form1 = rawRow5266 := by decide +kernel

def row5266 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key655, -1), (key656, 1), (key660, 1), (key661, -1)]

theorem rowCheck5266 : row5266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5266 := by decide +kernel

theorem rowEval5266 (x : Key → ℝ) : Integer.Sparse.eval row5266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5266, Integer.Sparse.eval_collectBalanced, rawRowCheck5266]

def rawRow5267 : Integer.Sparse Key := [(key489, -1), (key487, -1), (key488, 2), (key421, -1), (key411, -1), (key453, 2), (key390, 2), (key445, -1), (key400, -1), (key406, 2), (key435, -1), (key385, -1), (key662, 1), (key660, 1), (key661, -2), (key331, 1), (key321, 1), (key453, -2), (key253, -2), (key445, 1), (key263, 1), (key316, -2), (key435, 1), (key248, 1), (key662, -1), (key655, -1), (key661, 1), (key656, 1), (key489, 1), (key277, 1), (key488, -1), (key278, -1), (key331, -1), (key307, -1), (key421, 1), (key241, 1), (key316, 1), (key302, 1), (key406, -1), (key236, -1)]

theorem rawRowCheck5267 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block2.form1 = rawRow5267 := by decide +kernel

def row5267 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key253, -2), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key321, 1), (key385, -1), (key390, 2), (key400, -1), (key406, 1), (key411, -1), (key487, -1), (key488, 1), (key655, -1), (key656, 1), (key660, 1), (key661, -1)]

theorem rowCheck5267 : row5267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5267 := by decide +kernel

theorem rowEval5267 (x : Key → ℝ) : Integer.Sparse.eval row5267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5267, Integer.Sparse.eval_collectBalanced, rawRowCheck5267]

def rawRow5268 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2613, 2), (key2625, -1), (key2629, -1), (key2625, 2), (key2647, 2), (key2629, -1), (key2647, -1), (key2637, 2), (key2637, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2668, -2), (key2779, 1), (key2783, 1), (key2779, -2), (key2937, -2), (key2783, 1), (key2937, 1), (key2791, -2), (key2791, 1), (key2942, 1), (key2699, -1), (key2736, -1), (key2703, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2806, -1), (key2949, -1), (key2852, -1), (key2894, -1), (key2852, 1), (key2973, 1), (key2857, 1), (key2896, 1), (key2857, -1), (key2975, -1)]

theorem rawRowCheck5268 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5268 := by decide +kernel

def row5268 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5268 : row5268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5268 := by decide +kernel

theorem rowEval5268 (x : Key → ℝ) : Integer.Sparse.eval row5268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5268, Integer.Sparse.eval_collectBalanced, rawRowCheck5268]

def rawRow5269 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2613, 2), (key2629, -1), (key2625, -1), (key2647, 2), (key2625, 2), (key2647, -1), (key2629, -1), (key2637, 2), (key2652, -1), (key2637, -1), (key2668, 1), (key2664, 1), (key2668, -2), (key2783, 1), (key2779, 1), (key2937, -2), (key2779, -2), (key2937, 1), (key2783, 1), (key2791, -2), (key2942, 1), (key2791, 1), (key2736, -1), (key2699, -1), (key2736, 1), (key2703, 1), (key2949, 1), (key2802, 1), (key2949, -1), (key2806, -1), (key2894, -1), (key2852, -1), (key2973, 1), (key2852, 1), (key2896, 1), (key2857, 1), (key2975, -1), (key2857, -1)]

theorem rawRowCheck5269 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5269 := by decide +kernel

def row5269 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5269 : row5269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5269 := by decide +kernel

theorem rowEval5269 (x : Key → ℝ) : Integer.Sparse.eval row5269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5269, Integer.Sparse.eval_collectBalanced, rawRowCheck5269]

def rawRow5270 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2609, 2), (key2647, -1), (key2647, -1), (key2629, 2), (key2629, 2), (key2625, -1), (key2625, -1), (key2652, 2), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2664, -2), (key2937, 1), (key2937, 1), (key2783, -2), (key2783, -2), (key2779, 1), (key2779, 1), (key2942, -2), (key2791, 1), (key2791, 1), (key2703, -1), (key2703, -1), (key2699, 1), (key2699, 1), (key2806, 1), (key2806, 1), (key2802, -1), (key2802, -1), (key2973, -1), (key2973, -1), (key2894, 1), (key2894, 1), (key2975, 1), (key2975, 1), (key2896, -1), (key2896, -1)]

theorem rawRowCheck5270 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5270 := by decide +kernel

def row5270 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

theorem rowCheck5270 : row5270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5270 := by decide +kernel

theorem rowEval5270 (x : Key → ℝ) : Integer.Sparse.eval row5270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5270, Integer.Sparse.eval_collectBalanced, rawRowCheck5270]

def rawRow5271 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2637, 2), (key2609, -1), (key2613, -1), (key2625, 2), (key2647, 2), (key2637, -1), (key2652, -1), (key2613, 2), (key2629, -1), (key2647, -1), (key2779, 1), (key2783, 1), (key2791, -2), (key2664, 1), (key2668, 1), (key2779, -2), (key2937, -2), (key2791, 1), (key2942, 1), (key2668, -2), (key2783, 1), (key2937, 1), (key2852, -1), (key2894, -1), (key2857, 1), (key2896, 1), (key2852, 1), (key2973, 1), (key2857, -1), (key2975, -1), (key2699, -1), (key2736, -1), (key2802, 1), (key2949, 1), (key2703, 1), (key2736, 1), (key2806, -1), (key2949, -1)]

theorem rawRowCheck5271 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form0 = rawRow5271 := by decide +kernel

def row5271 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5271 : row5271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5271 := by decide +kernel

theorem rowEval5271 (x : Key → ℝ) : Integer.Sparse.eval row5271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5271, Integer.Sparse.eval_collectBalanced, rawRowCheck5271]

def rawRow5272 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2637, 2), (key2613, -1), (key2609, -1), (key2647, 2), (key2625, 2), (key2652, -1), (key2637, -1), (key2613, 2), (key2647, -1), (key2629, -1), (key2783, 1), (key2779, 1), (key2791, -2), (key2668, 1), (key2664, 1), (key2937, -2), (key2779, -2), (key2942, 1), (key2791, 1), (key2668, -2), (key2937, 1), (key2783, 1), (key2894, -1), (key2852, -1), (key2896, 1), (key2857, 1), (key2973, 1), (key2852, 1), (key2975, -1), (key2857, -1), (key2736, -1), (key2699, -1), (key2949, 1), (key2802, 1), (key2736, 1), (key2703, 1), (key2949, -1), (key2806, -1)]

theorem rawRowCheck5272 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form0 = rawRow5272 := by decide +kernel

def row5272 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5272 : row5272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5272 := by decide +kernel

theorem rowEval5272 (x : Key → ℝ) : Integer.Sparse.eval row5272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5272, Integer.Sparse.eval_collectBalanced, rawRowCheck5272]

def rawRow5273 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2629, 2), (key2625, -1), (key2637, -1), (key2609, 2), (key2652, 2), (key2613, -1), (key2647, -1), (key2629, 2), (key2613, -1), (key2647, -1), (key2779, 1), (key2791, 1), (key2783, -2), (key2779, 1), (key2791, 1), (key2664, -2), (key2942, -2), (key2668, 1), (key2937, 1), (key2783, -2), (key2668, 1), (key2937, 1), (key2802, -1), (key2896, -1), (key2806, 1), (key2894, 1), (key2699, 1), (key2975, 1), (key2703, -1), (key2973, -1), (key2802, -1), (key2896, -1), (key2699, 1), (key2975, 1), (key2806, 1), (key2894, 1), (key2703, -1), (key2973, -1)]

theorem rawRowCheck5273 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form0 = rawRow5273 := by decide +kernel

def row5273 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

theorem rowCheck5273 : row5273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5273 := by decide +kernel

theorem rowEval5273 (x : Key → ℝ) : Integer.Sparse.eval row5273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5273, Integer.Sparse.eval_collectBalanced, rawRowCheck5273]

def rawRow5274 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2629, 2), (key2637, -1), (key2625, -1), (key2652, 2), (key2609, 2), (key2647, -1), (key2613, -1), (key2629, 2), (key2647, -1), (key2613, -1), (key2791, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2779, 1), (key2942, -2), (key2664, -2), (key2937, 1), (key2668, 1), (key2783, -2), (key2937, 1), (key2668, 1), (key2896, -1), (key2802, -1), (key2894, 1), (key2806, 1), (key2975, 1), (key2699, 1), (key2973, -1), (key2703, -1), (key2896, -1), (key2802, -1), (key2975, 1), (key2699, 1), (key2894, 1), (key2806, 1), (key2973, -1), (key2703, -1)]

theorem rawRowCheck5274 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form0 = rawRow5274 := by decide +kernel

def row5274 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

theorem rowCheck5274 : row5274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5274 := by decide +kernel

theorem rowEval5274 (x : Key → ℝ) : Integer.Sparse.eval row5274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5274, Integer.Sparse.eval_collectBalanced, rawRowCheck5274]

def rawRow5275 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2625, 2), (key2647, -1), (key2652, -1), (key2613, 2), (key2637, 2), (key2609, -1), (key2625, -1), (key2647, 2), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2779, -2), (key2937, 1), (key2942, 1), (key2668, -2), (key2791, -2), (key2664, 1), (key2779, 1), (key2937, -2), (key2668, 1), (key2783, 1), (key2806, -1), (key2857, -1), (key2802, 1), (key2852, 1), (key2703, 1), (key2857, 1), (key2699, -1), (key2852, -1), (key2949, -1), (key2975, -1), (key2736, 1), (key2896, 1), (key2949, 1), (key2973, 1), (key2736, -1), (key2894, -1)]

theorem rawRowCheck5275 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form0 = rawRow5275 := by decide +kernel

def row5275 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5275 : row5275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5275 := by decide +kernel

theorem rowEval5275 (x : Key → ℝ) : Integer.Sparse.eval row5275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5275, Integer.Sparse.eval_collectBalanced, rawRowCheck5275]

def rawRow5276 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2625, 2), (key2652, -1), (key2647, -1), (key2637, 2), (key2613, 2), (key2625, -1), (key2609, -1), (key2647, 2), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2779, -2), (key2942, 1), (key2937, 1), (key2791, -2), (key2668, -2), (key2779, 1), (key2664, 1), (key2937, -2), (key2783, 1), (key2668, 1), (key2857, -1), (key2806, -1), (key2852, 1), (key2802, 1), (key2857, 1), (key2703, 1), (key2852, -1), (key2699, -1), (key2975, -1), (key2949, -1), (key2896, 1), (key2736, 1), (key2973, 1), (key2949, 1), (key2894, -1), (key2736, -1)]

theorem rawRowCheck5276 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form0 = rawRow5276 := by decide +kernel

def row5276 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5276 : row5276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5276 := by decide +kernel

theorem rowEval5276 (x : Key → ℝ) : Integer.Sparse.eval row5276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5276, Integer.Sparse.eval_collectBalanced, rawRowCheck5276]

def rawRow5277 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2652, 2), (key2613, -1), (key2613, -1), (key2629, 2), (key2629, 2), (key2637, -1), (key2637, -1), (key2609, 2), (key2625, -1), (key2625, -1), (key2937, 1), (key2937, 1), (key2942, -2), (key2668, 1), (key2668, 1), (key2783, -2), (key2783, -2), (key2791, 1), (key2791, 1), (key2664, -2), (key2779, 1), (key2779, 1), (key2973, -1), (key2973, -1), (key2975, 1), (key2975, 1), (key2894, 1), (key2894, 1), (key2896, -1), (key2896, -1), (key2703, -1), (key2703, -1), (key2806, 1), (key2806, 1), (key2699, 1), (key2699, 1), (key2802, -1), (key2802, -1)]

theorem rawRowCheck5277 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form0 = rawRow5277 := by decide +kernel

def row5277 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

theorem rowCheck5277 : row5277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5277 := by decide +kernel

theorem rowEval5277 (x : Key → ℝ) : Integer.Sparse.eval row5277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5277, Integer.Sparse.eval_collectBalanced, rawRowCheck5277]

def rawRow5278 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2647, 2), (key2629, -1), (key2637, -1), (key2613, 2), (key2637, 2), (key2613, -1), (key2629, -1), (key2625, 2), (key2609, -1), (key2625, -1), (key2937, 1), (key2942, 1), (key2937, -2), (key2783, 1), (key2791, 1), (key2668, -2), (key2791, -2), (key2668, 1), (key2783, 1), (key2779, -2), (key2664, 1), (key2779, 1), (key2949, -1), (key2975, -1), (key2949, 1), (key2973, 1), (key2736, 1), (key2896, 1), (key2736, -1), (key2894, -1), (key2806, -1), (key2857, -1), (key2703, 1), (key2857, 1), (key2802, 1), (key2852, 1), (key2699, -1), (key2852, -1)]

theorem rawRowCheck5278 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form0 = rawRow5278 := by decide +kernel

def row5278 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5278 : row5278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5278 := by decide +kernel

theorem rowEval5278 (x : Key → ℝ) : Integer.Sparse.eval row5278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5278, Integer.Sparse.eval_collectBalanced, rawRowCheck5278]

def rawRow5279 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2647, 2), (key2637, -1), (key2629, -1), (key2637, 2), (key2613, 2), (key2629, -1), (key2613, -1), (key2625, 2), (key2625, -1), (key2609, -1), (key2942, 1), (key2937, 1), (key2937, -2), (key2791, 1), (key2783, 1), (key2791, -2), (key2668, -2), (key2783, 1), (key2668, 1), (key2779, -2), (key2779, 1), (key2664, 1), (key2975, -1), (key2949, -1), (key2973, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2894, -1), (key2736, -1), (key2857, -1), (key2806, -1), (key2857, 1), (key2703, 1), (key2852, 1), (key2802, 1), (key2852, -1), (key2699, -1)]

theorem rawRowCheck5279 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form0 = rawRow5279 := by decide +kernel

def row5279 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5279 : row5279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5279 := by decide +kernel

theorem rowEval5279 (x : Key → ℝ) : Integer.Sparse.eval row5279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5279, Integer.Sparse.eval_collectBalanced, rawRowCheck5279]

def rawRow5280 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2668, 2), (key2699, -1), (key2703, -1), (key2699, 2), (key2736, 2), (key2703, -1), (key2736, -1), (key2723, 2), (key2723, -1), (key2746, -1), (key2609, 1), (key2613, 1), (key2613, -2), (key2802, 1), (key2806, 1), (key2802, -2), (key2949, -2), (key2806, 1), (key2949, 1), (key2826, -2), (key2826, 1), (key2959, 1), (key2625, -1), (key2647, -1), (key2629, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2783, -1), (key2937, -1), (key2852, -1), (key2894, -1), (key2852, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, -1), (key2982, -1)]

theorem rawRowCheck5280 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5280 := by decide +kernel

def row5280 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5280 : row5280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5280 := by decide +kernel

theorem rowEval5280 (x : Key → ℝ) : Integer.Sparse.eval row5280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5280, Integer.Sparse.eval_collectBalanced, rawRowCheck5280]

def rawRow5281 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2668, 2), (key2703, -1), (key2699, -1), (key2736, 2), (key2699, 2), (key2736, -1), (key2703, -1), (key2723, 2), (key2746, -1), (key2723, -1), (key2613, 1), (key2609, 1), (key2613, -2), (key2806, 1), (key2802, 1), (key2949, -2), (key2802, -2), (key2949, 1), (key2806, 1), (key2826, -2), (key2959, 1), (key2826, 1), (key2647, -1), (key2625, -1), (key2647, 1), (key2629, 1), (key2937, 1), (key2779, 1), (key2937, -1), (key2783, -1), (key2894, -1), (key2852, -1), (key2973, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2982, -1), (key2867, -1)]

theorem rawRowCheck5281 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5281 := by decide +kernel

def row5281 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5281 : row5281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5281 := by decide +kernel

theorem rowEval5281 (x : Key → ℝ) : Integer.Sparse.eval row5281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5281, Integer.Sparse.eval_collectBalanced, rawRowCheck5281]

def rawRow5282 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2664, 2), (key2736, -1), (key2736, -1), (key2703, 2), (key2703, 2), (key2699, -1), (key2699, -1), (key2746, 2), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2609, -2), (key2949, 1), (key2949, 1), (key2806, -2), (key2806, -2), (key2802, 1), (key2802, 1), (key2959, -2), (key2826, 1), (key2826, 1), (key2629, -1), (key2629, -1), (key2625, 1), (key2625, 1), (key2783, 1), (key2783, 1), (key2779, -1), (key2779, -1), (key2973, -1), (key2973, -1), (key2894, 1), (key2894, 1), (key2982, 1), (key2982, 1), (key2903, -1), (key2903, -1)]

theorem rawRowCheck5282 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5282 := by decide +kernel

def row5282 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

theorem rowCheck5282 : row5282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5282 := by decide +kernel

theorem rowEval5282 (x : Key → ℝ) : Integer.Sparse.eval row5282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5282, Integer.Sparse.eval_collectBalanced, rawRowCheck5282]

def rawRow5283 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2723, 2), (key2664, -1), (key2668, -1), (key2699, 2), (key2736, 2), (key2723, -1), (key2746, -1), (key2668, 2), (key2703, -1), (key2736, -1), (key2802, 1), (key2806, 1), (key2826, -2), (key2609, 1), (key2613, 1), (key2802, -2), (key2949, -2), (key2826, 1), (key2959, 1), (key2613, -2), (key2806, 1), (key2949, 1), (key2852, -1), (key2894, -1), (key2867, 1), (key2903, 1), (key2852, 1), (key2973, 1), (key2867, -1), (key2982, -1), (key2625, -1), (key2647, -1), (key2779, 1), (key2937, 1), (key2629, 1), (key2647, 1), (key2783, -1), (key2937, -1)]

theorem rawRowCheck5283 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form0 = rawRow5283 := by decide +kernel

def row5283 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5283 : row5283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5283 := by decide +kernel

theorem rowEval5283 (x : Key → ℝ) : Integer.Sparse.eval row5283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5283, Integer.Sparse.eval_collectBalanced, rawRowCheck5283]

def rawRow5284 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2723, 2), (key2668, -1), (key2664, -1), (key2736, 2), (key2699, 2), (key2746, -1), (key2723, -1), (key2668, 2), (key2736, -1), (key2703, -1), (key2806, 1), (key2802, 1), (key2826, -2), (key2613, 1), (key2609, 1), (key2949, -2), (key2802, -2), (key2959, 1), (key2826, 1), (key2613, -2), (key2949, 1), (key2806, 1), (key2894, -1), (key2852, -1), (key2903, 1), (key2867, 1), (key2973, 1), (key2852, 1), (key2982, -1), (key2867, -1), (key2647, -1), (key2625, -1), (key2937, 1), (key2779, 1), (key2647, 1), (key2629, 1), (key2937, -1), (key2783, -1)]

theorem rawRowCheck5284 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form0 = rawRow5284 := by decide +kernel

def row5284 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5284 : row5284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5284 := by decide +kernel

theorem rowEval5284 (x : Key → ℝ) : Integer.Sparse.eval row5284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5284, Integer.Sparse.eval_collectBalanced, rawRowCheck5284]

def rawRow5285 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2703, 2), (key2699, -1), (key2723, -1), (key2664, 2), (key2746, 2), (key2668, -1), (key2736, -1), (key2703, 2), (key2668, -1), (key2736, -1), (key2802, 1), (key2826, 1), (key2806, -2), (key2802, 1), (key2826, 1), (key2609, -2), (key2959, -2), (key2613, 1), (key2949, 1), (key2806, -2), (key2613, 1), (key2949, 1), (key2779, -1), (key2903, -1), (key2783, 1), (key2894, 1), (key2625, 1), (key2982, 1), (key2629, -1), (key2973, -1), (key2779, -1), (key2903, -1), (key2625, 1), (key2982, 1), (key2783, 1), (key2894, 1), (key2629, -1), (key2973, -1)]

theorem rawRowCheck5285 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form0 = rawRow5285 := by decide +kernel

def row5285 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

theorem rowCheck5285 : row5285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5285 := by decide +kernel

theorem rowEval5285 (x : Key → ℝ) : Integer.Sparse.eval row5285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5285, Integer.Sparse.eval_collectBalanced, rawRowCheck5285]

def rawRow5286 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2703, 2), (key2723, -1), (key2699, -1), (key2746, 2), (key2664, 2), (key2736, -1), (key2668, -1), (key2703, 2), (key2736, -1), (key2668, -1), (key2826, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2802, 1), (key2959, -2), (key2609, -2), (key2949, 1), (key2613, 1), (key2806, -2), (key2949, 1), (key2613, 1), (key2903, -1), (key2779, -1), (key2894, 1), (key2783, 1), (key2982, 1), (key2625, 1), (key2973, -1), (key2629, -1), (key2903, -1), (key2779, -1), (key2982, 1), (key2625, 1), (key2894, 1), (key2783, 1), (key2973, -1), (key2629, -1)]

theorem rawRowCheck5286 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form0 = rawRow5286 := by decide +kernel

def row5286 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

theorem rowCheck5286 : row5286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5286 := by decide +kernel

theorem rowEval5286 (x : Key → ℝ) : Integer.Sparse.eval row5286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5286, Integer.Sparse.eval_collectBalanced, rawRowCheck5286]

def rawRow5287 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2699, 2), (key2736, -1), (key2746, -1), (key2668, 2), (key2723, 2), (key2664, -1), (key2699, -1), (key2736, 2), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2802, -2), (key2949, 1), (key2959, 1), (key2613, -2), (key2826, -2), (key2609, 1), (key2802, 1), (key2949, -2), (key2613, 1), (key2806, 1), (key2783, -1), (key2867, -1), (key2779, 1), (key2852, 1), (key2629, 1), (key2867, 1), (key2625, -1), (key2852, -1), (key2937, -1), (key2982, -1), (key2647, 1), (key2903, 1), (key2937, 1), (key2973, 1), (key2647, -1), (key2894, -1)]

theorem rawRowCheck5287 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form0 = rawRow5287 := by decide +kernel

def row5287 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5287 : row5287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5287 := by decide +kernel

theorem rowEval5287 (x : Key → ℝ) : Integer.Sparse.eval row5287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5287, Integer.Sparse.eval_collectBalanced, rawRowCheck5287]

def rawRow5288 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2699, 2), (key2746, -1), (key2736, -1), (key2723, 2), (key2668, 2), (key2699, -1), (key2664, -1), (key2736, 2), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2802, -2), (key2959, 1), (key2949, 1), (key2826, -2), (key2613, -2), (key2802, 1), (key2609, 1), (key2949, -2), (key2806, 1), (key2613, 1), (key2867, -1), (key2783, -1), (key2852, 1), (key2779, 1), (key2867, 1), (key2629, 1), (key2852, -1), (key2625, -1), (key2982, -1), (key2937, -1), (key2903, 1), (key2647, 1), (key2973, 1), (key2937, 1), (key2894, -1), (key2647, -1)]

theorem rawRowCheck5288 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form0 = rawRow5288 := by decide +kernel

def row5288 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5288 : row5288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5288 := by decide +kernel

theorem rowEval5288 (x : Key → ℝ) : Integer.Sparse.eval row5288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5288, Integer.Sparse.eval_collectBalanced, rawRowCheck5288]

def rawRow5289 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2746, 2), (key2668, -1), (key2668, -1), (key2703, 2), (key2703, 2), (key2723, -1), (key2723, -1), (key2664, 2), (key2699, -1), (key2699, -1), (key2949, 1), (key2949, 1), (key2959, -2), (key2613, 1), (key2613, 1), (key2806, -2), (key2806, -2), (key2826, 1), (key2826, 1), (key2609, -2), (key2802, 1), (key2802, 1), (key2973, -1), (key2973, -1), (key2982, 1), (key2982, 1), (key2894, 1), (key2894, 1), (key2903, -1), (key2903, -1), (key2629, -1), (key2629, -1), (key2783, 1), (key2783, 1), (key2625, 1), (key2625, 1), (key2779, -1), (key2779, -1)]

theorem rawRowCheck5289 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form0 = rawRow5289 := by decide +kernel

def row5289 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

theorem rowCheck5289 : row5289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5289 := by decide +kernel

theorem rowEval5289 (x : Key → ℝ) : Integer.Sparse.eval row5289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5289, Integer.Sparse.eval_collectBalanced, rawRowCheck5289]

def rawRow5290 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2736, 2), (key2703, -1), (key2723, -1), (key2668, 2), (key2723, 2), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, -1), (key2699, -1), (key2949, 1), (key2959, 1), (key2949, -2), (key2806, 1), (key2826, 1), (key2613, -2), (key2826, -2), (key2613, 1), (key2806, 1), (key2802, -2), (key2609, 1), (key2802, 1), (key2937, -1), (key2982, -1), (key2937, 1), (key2973, 1), (key2647, 1), (key2903, 1), (key2647, -1), (key2894, -1), (key2783, -1), (key2867, -1), (key2629, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2625, -1), (key2852, -1)]

theorem rawRowCheck5290 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form0 = rawRow5290 := by decide +kernel

def row5290 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5290 : row5290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5290 := by decide +kernel

theorem rowEval5290 (x : Key → ℝ) : Integer.Sparse.eval row5290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5290, Integer.Sparse.eval_collectBalanced, rawRowCheck5290]

def rawRow5291 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2736, 2), (key2723, -1), (key2703, -1), (key2723, 2), (key2668, 2), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, -1), (key2664, -1), (key2959, 1), (key2949, 1), (key2949, -2), (key2826, 1), (key2806, 1), (key2826, -2), (key2613, -2), (key2806, 1), (key2613, 1), (key2802, -2), (key2802, 1), (key2609, 1), (key2982, -1), (key2937, -1), (key2973, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2894, -1), (key2647, -1), (key2867, -1), (key2783, -1), (key2867, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, -1), (key2625, -1)]

theorem rawRowCheck5291 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form0 = rawRow5291 := by decide +kernel

def row5291 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5291 : row5291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5291 := by decide +kernel

theorem rowEval5291 (x : Key → ℝ) : Integer.Sparse.eval row5291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5291, Integer.Sparse.eval_collectBalanced, rawRowCheck5291]

def rawRow5292 : Integer.Sparse Key := [(key2779, -1), (key2791, -1), (key2783, 2), (key2852, -1), (key2857, -1), (key2802, 2), (key2896, 2), (key2806, -1), (key2894, -1), (key2867, 2), (key2826, -1), (key2903, -1), (key2625, 1), (key2637, 1), (key2629, -2), (key2852, 1), (key2857, 1), (key2699, -2), (key2975, -2), (key2703, 1), (key2973, 1), (key2867, -2), (key2723, 1), (key2982, 1), (key2609, -1), (key2652, -1), (key2613, 1), (key2647, 1), (key2664, 1), (key2942, 1), (key2668, -1), (key2937, -1), (key2802, -1), (key2896, -1), (key2699, 1), (key2975, 1), (key2826, 1), (key2903, 1), (key2723, -1), (key2982, -1)]

theorem rawRowCheck5292 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form0 = rawRow5292 := by decide +kernel

def row5292 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5292 : row5292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5292 := by decide +kernel

theorem rowEval5292 (x : Key → ℝ) : Integer.Sparse.eval row5292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5292, Integer.Sparse.eval_collectBalanced, rawRowCheck5292]

def rawRow5293 : Integer.Sparse Key := [(key2791, -1), (key2779, -1), (key2783, 2), (key2857, -1), (key2852, -1), (key2896, 2), (key2802, 2), (key2894, -1), (key2806, -1), (key2867, 2), (key2903, -1), (key2826, -1), (key2637, 1), (key2625, 1), (key2629, -2), (key2857, 1), (key2852, 1), (key2975, -2), (key2699, -2), (key2973, 1), (key2703, 1), (key2867, -2), (key2982, 1), (key2723, 1), (key2652, -1), (key2609, -1), (key2647, 1), (key2613, 1), (key2942, 1), (key2664, 1), (key2937, -1), (key2668, -1), (key2896, -1), (key2802, -1), (key2975, 1), (key2699, 1), (key2903, 1), (key2826, 1), (key2982, -1), (key2723, -1)]

theorem rawRowCheck5293 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form0 = rawRow5293 := by decide +kernel

def row5293 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5293 : row5293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5293 := by decide +kernel

theorem rowEval5293 (x : Key → ℝ) : Integer.Sparse.eval row5293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5293, Integer.Sparse.eval_collectBalanced, rawRowCheck5293]

def rawRow5294 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2779, 2), (key2894, -1), (key2896, -1), (key2806, 2), (key2857, 2), (key2802, -1), (key2852, -1), (key2903, 2), (key2826, -1), (key2867, -1), (key2629, 1), (key2637, 1), (key2625, -2), (key2973, 1), (key2975, 1), (key2703, -2), (key2857, -2), (key2699, 1), (key2852, 1), (key2982, -2), (key2723, 1), (key2867, 1), (key2613, -1), (key2637, -1), (key2609, 1), (key2625, 1), (key2668, 1), (key2791, 1), (key2664, -1), (key2779, -1), (key2949, -1), (key2975, -1), (key2736, 1), (key2896, 1), (key2959, 1), (key2982, 1), (key2746, -1), (key2903, -1)]

theorem rawRowCheck5294 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form0 = rawRow5294 := by decide +kernel

def row5294 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5294 : row5294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5294 := by decide +kernel

theorem rowEval5294 (x : Key → ℝ) : Integer.Sparse.eval row5294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5294, Integer.Sparse.eval_collectBalanced, rawRowCheck5294]

def rawRow5295 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2779, 2), (key2896, -1), (key2894, -1), (key2857, 2), (key2806, 2), (key2852, -1), (key2802, -1), (key2903, 2), (key2867, -1), (key2826, -1), (key2637, 1), (key2629, 1), (key2625, -2), (key2975, 1), (key2973, 1), (key2857, -2), (key2703, -2), (key2852, 1), (key2699, 1), (key2982, -2), (key2867, 1), (key2723, 1), (key2637, -1), (key2613, -1), (key2625, 1), (key2609, 1), (key2791, 1), (key2668, 1), (key2779, -1), (key2664, -1), (key2975, -1), (key2949, -1), (key2896, 1), (key2736, 1), (key2982, 1), (key2959, 1), (key2903, -1), (key2746, -1)]

theorem rawRowCheck5295 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form0 = rawRow5295 := by decide +kernel

def row5295 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5295 : row5295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5295 := by decide +kernel

theorem rowEval5295 (x : Key → ℝ) : Integer.Sparse.eval row5295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5295, Integer.Sparse.eval_collectBalanced, rawRowCheck5295]

def rawRow5296 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2806, 2), (key2852, -1), (key2867, -1), (key2779, 2), (key2903, 2), (key2783, -1), (key2894, -1), (key2857, 2), (key2791, -1), (key2896, -1), (key2699, 1), (key2723, 1), (key2703, -2), (key2852, 1), (key2867, 1), (key2625, -2), (key2982, -2), (key2629, 1), (key2973, 1), (key2857, -2), (key2637, 1), (key2975, 1), (key2664, -1), (key2746, -1), (key2668, 1), (key2736, 1), (key2609, 1), (key2959, 1), (key2613, -1), (key2949, -1), (key2779, -1), (key2903, -1), (key2625, 1), (key2982, 1), (key2791, 1), (key2896, 1), (key2637, -1), (key2975, -1)]

theorem rawRowCheck5296 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form0 = rawRow5296 := by decide +kernel

def row5296 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5296 : row5296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5296 := by decide +kernel

theorem rowEval5296 (x : Key → ℝ) : Integer.Sparse.eval row5296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5296, Integer.Sparse.eval_collectBalanced, rawRowCheck5296]

def rawRow5297 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2806, 2), (key2867, -1), (key2852, -1), (key2903, 2), (key2779, 2), (key2894, -1), (key2783, -1), (key2857, 2), (key2896, -1), (key2791, -1), (key2723, 1), (key2699, 1), (key2703, -2), (key2867, 1), (key2852, 1), (key2982, -2), (key2625, -2), (key2973, 1), (key2629, 1), (key2857, -2), (key2975, 1), (key2637, 1), (key2746, -1), (key2664, -1), (key2736, 1), (key2668, 1), (key2959, 1), (key2609, 1), (key2949, -1), (key2613, -1), (key2903, -1), (key2779, -1), (key2982, 1), (key2625, 1), (key2896, 1), (key2791, 1), (key2975, -1), (key2637, -1)]

theorem rawRowCheck5297 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form0 = rawRow5297 := by decide +kernel

def row5297 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5297 : row5297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5297 := by decide +kernel

theorem rowEval5297 (x : Key → ℝ) : Integer.Sparse.eval row5297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5297, Integer.Sparse.eval_collectBalanced, rawRowCheck5297]

def rawRow5298 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2802, 2), (key2894, -1), (key2903, -1), (key2783, 2), (key2867, 2), (key2779, -1), (key2852, -1), (key2896, 2), (key2791, -1), (key2857, -1), (key2703, 1), (key2723, 1), (key2699, -2), (key2973, 1), (key2982, 1), (key2629, -2), (key2867, -2), (key2625, 1), (key2852, 1), (key2975, -2), (key2637, 1), (key2857, 1), (key2668, -1), (key2723, -1), (key2664, 1), (key2699, 1), (key2613, 1), (key2826, 1), (key2609, -1), (key2802, -1), (key2937, -1), (key2982, -1), (key2647, 1), (key2903, 1), (key2942, 1), (key2975, 1), (key2652, -1), (key2896, -1)]

theorem rawRowCheck5298 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form0 = rawRow5298 := by decide +kernel

def row5298 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5298 : row5298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5298 := by decide +kernel

theorem rowEval5298 (x : Key → ℝ) : Integer.Sparse.eval row5298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5298, Integer.Sparse.eval_collectBalanced, rawRowCheck5298]

def rawRow5299 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2802, 2), (key2903, -1), (key2894, -1), (key2867, 2), (key2783, 2), (key2852, -1), (key2779, -1), (key2896, 2), (key2857, -1), (key2791, -1), (key2723, 1), (key2703, 1), (key2699, -2), (key2982, 1), (key2973, 1), (key2867, -2), (key2629, -2), (key2852, 1), (key2625, 1), (key2975, -2), (key2857, 1), (key2637, 1), (key2723, -1), (key2668, -1), (key2699, 1), (key2664, 1), (key2826, 1), (key2613, 1), (key2802, -1), (key2609, -1), (key2982, -1), (key2937, -1), (key2903, 1), (key2647, 1), (key2975, 1), (key2942, 1), (key2896, -1), (key2652, -1)]

theorem rawRowCheck5299 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form0 = rawRow5299 := by decide +kernel

def row5299 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5299 : row5299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5299 := by decide +kernel

theorem rowEval5299 (x : Key → ℝ) : Integer.Sparse.eval row5299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5299, Integer.Sparse.eval_collectBalanced, rawRowCheck5299]

def rawRow5300 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2867, 2), (key2779, -1), (key2791, -1), (key2802, 2), (key2896, 2), (key2826, -1), (key2903, -1), (key2783, 2), (key2806, -1), (key2894, -1), (key2852, 1), (key2857, 1), (key2867, -2), (key2625, 1), (key2637, 1), (key2699, -2), (key2975, -2), (key2723, 1), (key2982, 1), (key2629, -2), (key2703, 1), (key2973, 1), (key2802, -1), (key2896, -1), (key2826, 1), (key2903, 1), (key2699, 1), (key2975, 1), (key2723, -1), (key2982, -1), (key2609, -1), (key2652, -1), (key2664, 1), (key2942, 1), (key2613, 1), (key2647, 1), (key2668, -1), (key2937, -1)]

theorem rawRowCheck5300 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form0 = rawRow5300 := by decide +kernel

def row5300 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5300 : row5300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5300 := by decide +kernel

theorem rowEval5300 (x : Key → ℝ) : Integer.Sparse.eval row5300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5300, Integer.Sparse.eval_collectBalanced, rawRowCheck5300]

def rawRow5301 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2867, 2), (key2791, -1), (key2779, -1), (key2896, 2), (key2802, 2), (key2903, -1), (key2826, -1), (key2783, 2), (key2894, -1), (key2806, -1), (key2857, 1), (key2852, 1), (key2867, -2), (key2637, 1), (key2625, 1), (key2975, -2), (key2699, -2), (key2982, 1), (key2723, 1), (key2629, -2), (key2973, 1), (key2703, 1), (key2896, -1), (key2802, -1), (key2903, 1), (key2826, 1), (key2975, 1), (key2699, 1), (key2982, -1), (key2723, -1), (key2652, -1), (key2609, -1), (key2942, 1), (key2664, 1), (key2647, 1), (key2613, 1), (key2937, -1), (key2668, -1)]

theorem rawRowCheck5301 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form0 = rawRow5301 := by decide +kernel

def row5301 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5301 : row5301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5301 := by decide +kernel

theorem rowEval5301 (x : Key → ℝ) : Integer.Sparse.eval row5301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5301, Integer.Sparse.eval_collectBalanced, rawRowCheck5301]

def rawRow5302 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2857, 2), (key2802, -1), (key2826, -1), (key2779, 2), (key2903, 2), (key2791, -1), (key2896, -1), (key2806, 2), (key2783, -1), (key2894, -1), (key2852, 1), (key2867, 1), (key2857, -2), (key2699, 1), (key2723, 1), (key2625, -2), (key2982, -2), (key2637, 1), (key2975, 1), (key2703, -2), (key2629, 1), (key2973, 1), (key2779, -1), (key2903, -1), (key2791, 1), (key2896, 1), (key2625, 1), (key2982, 1), (key2637, -1), (key2975, -1), (key2664, -1), (key2746, -1), (key2609, 1), (key2959, 1), (key2668, 1), (key2736, 1), (key2613, -1), (key2949, -1)]

theorem rawRowCheck5302 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form0 = rawRow5302 := by decide +kernel

def row5302 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5302 : row5302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5302 := by decide +kernel

theorem rowEval5302 (x : Key → ℝ) : Integer.Sparse.eval row5302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5302, Integer.Sparse.eval_collectBalanced, rawRowCheck5302]

def rawRow5303 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2857, 2), (key2826, -1), (key2802, -1), (key2903, 2), (key2779, 2), (key2896, -1), (key2791, -1), (key2806, 2), (key2894, -1), (key2783, -1), (key2867, 1), (key2852, 1), (key2857, -2), (key2723, 1), (key2699, 1), (key2982, -2), (key2625, -2), (key2975, 1), (key2637, 1), (key2703, -2), (key2973, 1), (key2629, 1), (key2903, -1), (key2779, -1), (key2896, 1), (key2791, 1), (key2982, 1), (key2625, 1), (key2975, -1), (key2637, -1), (key2746, -1), (key2664, -1), (key2959, 1), (key2609, 1), (key2736, 1), (key2668, 1), (key2949, -1), (key2613, -1)]

theorem rawRowCheck5303 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form0 = rawRow5303 := by decide +kernel

def row5303 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5303 : row5303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5303 := by decide +kernel

theorem rowEval5303 (x : Key → ℝ) : Integer.Sparse.eval row5303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5303, Integer.Sparse.eval_collectBalanced, rawRowCheck5303]

def rawRow5304 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2903, 2), (key2783, -1), (key2791, -1), (key2806, 2), (key2857, 2), (key2826, -1), (key2867, -1), (key2779, 2), (key2802, -1), (key2852, -1), (key2973, 1), (key2975, 1), (key2982, -2), (key2629, 1), (key2637, 1), (key2703, -2), (key2857, -2), (key2723, 1), (key2867, 1), (key2625, -2), (key2699, 1), (key2852, 1), (key2949, -1), (key2975, -1), (key2959, 1), (key2982, 1), (key2736, 1), (key2896, 1), (key2746, -1), (key2903, -1), (key2613, -1), (key2637, -1), (key2668, 1), (key2791, 1), (key2609, 1), (key2625, 1), (key2664, -1), (key2779, -1)]

theorem rawRowCheck5304 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form0 = rawRow5304 := by decide +kernel

def row5304 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5304 : row5304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5304 := by decide +kernel

theorem rowEval5304 (x : Key → ℝ) : Integer.Sparse.eval row5304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5304, Integer.Sparse.eval_collectBalanced, rawRowCheck5304]

def rawRow5305 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2903, 2), (key2791, -1), (key2783, -1), (key2857, 2), (key2806, 2), (key2867, -1), (key2826, -1), (key2779, 2), (key2852, -1), (key2802, -1), (key2975, 1), (key2973, 1), (key2982, -2), (key2637, 1), (key2629, 1), (key2857, -2), (key2703, -2), (key2867, 1), (key2723, 1), (key2625, -2), (key2852, 1), (key2699, 1), (key2975, -1), (key2949, -1), (key2982, 1), (key2959, 1), (key2896, 1), (key2736, 1), (key2903, -1), (key2746, -1), (key2637, -1), (key2613, -1), (key2791, 1), (key2668, 1), (key2625, 1), (key2609, 1), (key2779, -1), (key2664, -1)]

theorem rawRowCheck5305 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form0 = rawRow5305 := by decide +kernel

def row5305 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

theorem rowCheck5305 : row5305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5305 := by decide +kernel

theorem rowEval5305 (x : Key → ℝ) : Integer.Sparse.eval row5305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5305, Integer.Sparse.eval_collectBalanced, rawRowCheck5305]

def rawRow5306 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2896, 2), (key2806, -1), (key2826, -1), (key2783, 2), (key2867, 2), (key2791, -1), (key2857, -1), (key2802, 2), (key2779, -1), (key2852, -1), (key2973, 1), (key2982, 1), (key2975, -2), (key2703, 1), (key2723, 1), (key2629, -2), (key2867, -2), (key2637, 1), (key2857, 1), (key2699, -2), (key2625, 1), (key2852, 1), (key2937, -1), (key2982, -1), (key2942, 1), (key2975, 1), (key2647, 1), (key2903, 1), (key2652, -1), (key2896, -1), (key2668, -1), (key2723, -1), (key2613, 1), (key2826, 1), (key2664, 1), (key2699, 1), (key2609, -1), (key2802, -1)]

theorem rawRowCheck5306 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form0 = rawRow5306 := by decide +kernel

def row5306 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5306 : row5306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5306 := by decide +kernel

theorem rowEval5306 (x : Key → ℝ) : Integer.Sparse.eval row5306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5306, Integer.Sparse.eval_collectBalanced, rawRowCheck5306]

def rawRow5307 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2896, 2), (key2826, -1), (key2806, -1), (key2867, 2), (key2783, 2), (key2857, -1), (key2791, -1), (key2802, 2), (key2852, -1), (key2779, -1), (key2982, 1), (key2973, 1), (key2975, -2), (key2723, 1), (key2703, 1), (key2867, -2), (key2629, -2), (key2857, 1), (key2637, 1), (key2699, -2), (key2852, 1), (key2625, 1), (key2982, -1), (key2937, -1), (key2975, 1), (key2942, 1), (key2903, 1), (key2647, 1), (key2896, -1), (key2652, -1), (key2723, -1), (key2668, -1), (key2826, 1), (key2613, 1), (key2699, 1), (key2664, 1), (key2802, -1), (key2609, -1)]

theorem rawRowCheck5307 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form0 = rawRow5307 := by decide +kernel

def row5307 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

theorem rowCheck5307 : row5307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5307 := by decide +kernel

theorem rowEval5307 (x : Key → ℝ) : Integer.Sparse.eval row5307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form0) x := by
  rw [rowCheck5307, Integer.Sparse.eval_collectBalanced, rawRowCheck5307]

def rawRow5308 : Integer.Sparse Key := [(key1292, -1), (key1297, -1), (key1297, 2), (key1312, -1), (key1317, -1), (key1312, 2), (key1338, 2), (key1317, -1), (key1338, -1), (key1325, 2), (key1325, -1), (key1344, -1), (key1387, 1), (key1392, 1), (key1392, -2), (key1542, 1), (key1547, 1), (key1542, -2), (key1773, -2), (key1547, 1), (key1773, 1), (key1555, -2), (key1555, 1), (key1779, 1), (key1420, -1), (key1456, -1), (key1425, 1), (key1456, 1), (key1569, 1), (key1789, 1), (key1574, -1), (key1789, -1), (key1618, -1), (key1656, -1), (key1618, 1), (key1814, 1), (key1623, 1), (key1658, 1), (key1623, -1), (key1816, -1)]

theorem rawRowCheck5308 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5308 := by decide +kernel

def row5308 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5308 : row5308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5308 := by decide +kernel

theorem rowEval5308 (x : Key → ℝ) : Integer.Sparse.eval row5308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5308, Integer.Sparse.eval_collectBalanced, rawRowCheck5308]

def rawRow5309 : Integer.Sparse Key := [(key1297, -1), (key1292, -1), (key1297, 2), (key1317, -1), (key1312, -1), (key1338, 2), (key1312, 2), (key1338, -1), (key1317, -1), (key1325, 2), (key1344, -1), (key1325, -1), (key1392, 1), (key1387, 1), (key1392, -2), (key1547, 1), (key1542, 1), (key1773, -2), (key1542, -2), (key1773, 1), (key1547, 1), (key1555, -2), (key1779, 1), (key1555, 1), (key1456, -1), (key1420, -1), (key1456, 1), (key1425, 1), (key1789, 1), (key1569, 1), (key1789, -1), (key1574, -1), (key1656, -1), (key1618, -1), (key1814, 1), (key1618, 1), (key1658, 1), (key1623, 1), (key1816, -1), (key1623, -1)]

theorem rawRowCheck5309 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5309 := by decide +kernel

def row5309 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5309 : row5309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5309 := by decide +kernel

theorem rowEval5309 (x : Key → ℝ) : Integer.Sparse.eval row5309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5309, Integer.Sparse.eval_collectBalanced, rawRowCheck5309]

def rawRow5310 : Integer.Sparse Key := [(key1297, -1), (key1297, -1), (key1292, 2), (key1338, -1), (key1338, -1), (key1317, 2), (key1317, 2), (key1312, -1), (key1312, -1), (key1344, 2), (key1325, -1), (key1325, -1), (key1392, 1), (key1392, 1), (key1387, -2), (key1773, 1), (key1773, 1), (key1547, -2), (key1547, -2), (key1542, 1), (key1542, 1), (key1779, -2), (key1555, 1), (key1555, 1), (key1425, -1), (key1425, -1), (key1420, 1), (key1420, 1), (key1574, 1), (key1574, 1), (key1569, -1), (key1569, -1), (key1814, -1), (key1814, -1), (key1656, 1), (key1656, 1), (key1816, 1), (key1816, 1), (key1658, -1), (key1658, -1)]

theorem rawRowCheck5310 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5310 := by decide +kernel

def row5310 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

theorem rowCheck5310 : row5310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5310 := by decide +kernel

theorem rowEval5310 (x : Key → ℝ) : Integer.Sparse.eval row5310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5310, Integer.Sparse.eval_collectBalanced, rawRowCheck5310]

def rawRow5311 : Integer.Sparse Key := [(key1312, -1), (key1317, -1), (key1325, 2), (key1292, -1), (key1297, -1), (key1312, 2), (key1338, 2), (key1325, -1), (key1344, -1), (key1297, 2), (key1317, -1), (key1338, -1), (key1542, 1), (key1547, 1), (key1555, -2), (key1387, 1), (key1392, 1), (key1542, -2), (key1773, -2), (key1555, 1), (key1779, 1), (key1392, -2), (key1547, 1), (key1773, 1), (key1618, -1), (key1656, -1), (key1623, 1), (key1658, 1), (key1618, 1), (key1814, 1), (key1623, -1), (key1816, -1), (key1420, -1), (key1456, -1), (key1569, 1), (key1789, 1), (key1425, 1), (key1456, 1), (key1574, -1), (key1789, -1)]

theorem rawRowCheck5311 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form1 = rawRow5311 := by decide +kernel

def row5311 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5311 : row5311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5311 := by decide +kernel

theorem rowEval5311 (x : Key → ℝ) : Integer.Sparse.eval row5311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5311, Integer.Sparse.eval_collectBalanced, rawRowCheck5311]

def rawRow5312 : Integer.Sparse Key := [(key1317, -1), (key1312, -1), (key1325, 2), (key1297, -1), (key1292, -1), (key1338, 2), (key1312, 2), (key1344, -1), (key1325, -1), (key1297, 2), (key1338, -1), (key1317, -1), (key1547, 1), (key1542, 1), (key1555, -2), (key1392, 1), (key1387, 1), (key1773, -2), (key1542, -2), (key1779, 1), (key1555, 1), (key1392, -2), (key1773, 1), (key1547, 1), (key1656, -1), (key1618, -1), (key1658, 1), (key1623, 1), (key1814, 1), (key1618, 1), (key1816, -1), (key1623, -1), (key1456, -1), (key1420, -1), (key1789, 1), (key1569, 1), (key1456, 1), (key1425, 1), (key1789, -1), (key1574, -1)]

theorem rawRowCheck5312 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form1 = rawRow5312 := by decide +kernel

def row5312 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5312 : row5312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5312 := by decide +kernel

theorem rowEval5312 (x : Key → ℝ) : Integer.Sparse.eval row5312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5312, Integer.Sparse.eval_collectBalanced, rawRowCheck5312]

def rawRow5313 : Integer.Sparse Key := [(key1312, -1), (key1325, -1), (key1317, 2), (key1312, -1), (key1325, -1), (key1292, 2), (key1344, 2), (key1297, -1), (key1338, -1), (key1317, 2), (key1297, -1), (key1338, -1), (key1542, 1), (key1555, 1), (key1547, -2), (key1542, 1), (key1555, 1), (key1387, -2), (key1779, -2), (key1392, 1), (key1773, 1), (key1547, -2), (key1392, 1), (key1773, 1), (key1569, -1), (key1658, -1), (key1574, 1), (key1656, 1), (key1420, 1), (key1816, 1), (key1425, -1), (key1814, -1), (key1569, -1), (key1658, -1), (key1420, 1), (key1816, 1), (key1574, 1), (key1656, 1), (key1425, -1), (key1814, -1)]

theorem rawRowCheck5313 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form1 = rawRow5313 := by decide +kernel

def row5313 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

theorem rowCheck5313 : row5313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5313 := by decide +kernel

theorem rowEval5313 (x : Key → ℝ) : Integer.Sparse.eval row5313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5313, Integer.Sparse.eval_collectBalanced, rawRowCheck5313]

def rawRow5314 : Integer.Sparse Key := [(key1325, -1), (key1312, -1), (key1317, 2), (key1325, -1), (key1312, -1), (key1344, 2), (key1292, 2), (key1338, -1), (key1297, -1), (key1317, 2), (key1338, -1), (key1297, -1), (key1555, 1), (key1542, 1), (key1547, -2), (key1555, 1), (key1542, 1), (key1779, -2), (key1387, -2), (key1773, 1), (key1392, 1), (key1547, -2), (key1773, 1), (key1392, 1), (key1658, -1), (key1569, -1), (key1656, 1), (key1574, 1), (key1816, 1), (key1420, 1), (key1814, -1), (key1425, -1), (key1658, -1), (key1569, -1), (key1816, 1), (key1420, 1), (key1656, 1), (key1574, 1), (key1814, -1), (key1425, -1)]

theorem rawRowCheck5314 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form1 = rawRow5314 := by decide +kernel

def row5314 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

theorem rowCheck5314 : row5314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5314 := by decide +kernel

theorem rowEval5314 (x : Key → ℝ) : Integer.Sparse.eval row5314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5314, Integer.Sparse.eval_collectBalanced, rawRowCheck5314]

def rawRow5315 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1312, 2), (key1338, -1), (key1344, -1), (key1297, 2), (key1325, 2), (key1292, -1), (key1312, -1), (key1338, 2), (key1297, -1), (key1317, -1), (key1547, 1), (key1555, 1), (key1542, -2), (key1773, 1), (key1779, 1), (key1392, -2), (key1555, -2), (key1387, 1), (key1542, 1), (key1773, -2), (key1392, 1), (key1547, 1), (key1574, -1), (key1623, -1), (key1569, 1), (key1618, 1), (key1425, 1), (key1623, 1), (key1420, -1), (key1618, -1), (key1789, -1), (key1816, -1), (key1456, 1), (key1658, 1), (key1789, 1), (key1814, 1), (key1456, -1), (key1656, -1)]

theorem rawRowCheck5315 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form1 = rawRow5315 := by decide +kernel

def row5315 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5315 : row5315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5315 := by decide +kernel

theorem rowEval5315 (x : Key → ℝ) : Integer.Sparse.eval row5315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5315, Integer.Sparse.eval_collectBalanced, rawRowCheck5315]

def rawRow5316 : Integer.Sparse Key := [(key1325, -1), (key1317, -1), (key1312, 2), (key1344, -1), (key1338, -1), (key1325, 2), (key1297, 2), (key1312, -1), (key1292, -1), (key1338, 2), (key1317, -1), (key1297, -1), (key1555, 1), (key1547, 1), (key1542, -2), (key1779, 1), (key1773, 1), (key1555, -2), (key1392, -2), (key1542, 1), (key1387, 1), (key1773, -2), (key1547, 1), (key1392, 1), (key1623, -1), (key1574, -1), (key1618, 1), (key1569, 1), (key1623, 1), (key1425, 1), (key1618, -1), (key1420, -1), (key1816, -1), (key1789, -1), (key1658, 1), (key1456, 1), (key1814, 1), (key1789, 1), (key1656, -1), (key1456, -1)]

theorem rawRowCheck5316 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form1 = rawRow5316 := by decide +kernel

def row5316 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5316 : row5316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5316 := by decide +kernel

theorem rowEval5316 (x : Key → ℝ) : Integer.Sparse.eval row5316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5316, Integer.Sparse.eval_collectBalanced, rawRowCheck5316]

def rawRow5317 : Integer.Sparse Key := [(key1338, -1), (key1338, -1), (key1344, 2), (key1297, -1), (key1297, -1), (key1317, 2), (key1317, 2), (key1325, -1), (key1325, -1), (key1292, 2), (key1312, -1), (key1312, -1), (key1773, 1), (key1773, 1), (key1779, -2), (key1392, 1), (key1392, 1), (key1547, -2), (key1547, -2), (key1555, 1), (key1555, 1), (key1387, -2), (key1542, 1), (key1542, 1), (key1814, -1), (key1814, -1), (key1816, 1), (key1816, 1), (key1656, 1), (key1656, 1), (key1658, -1), (key1658, -1), (key1425, -1), (key1425, -1), (key1574, 1), (key1574, 1), (key1420, 1), (key1420, 1), (key1569, -1), (key1569, -1)]

theorem rawRowCheck5317 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow5317 := by decide +kernel

def row5317 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

theorem rowCheck5317 : row5317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5317 := by decide +kernel

theorem rowEval5317 (x : Key → ℝ) : Integer.Sparse.eval row5317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5317, Integer.Sparse.eval_collectBalanced, rawRowCheck5317]

def rawRow5318 : Integer.Sparse Key := [(key1338, -1), (key1344, -1), (key1338, 2), (key1317, -1), (key1325, -1), (key1297, 2), (key1325, 2), (key1297, -1), (key1317, -1), (key1312, 2), (key1292, -1), (key1312, -1), (key1773, 1), (key1779, 1), (key1773, -2), (key1547, 1), (key1555, 1), (key1392, -2), (key1555, -2), (key1392, 1), (key1547, 1), (key1542, -2), (key1387, 1), (key1542, 1), (key1789, -1), (key1816, -1), (key1789, 1), (key1814, 1), (key1456, 1), (key1658, 1), (key1456, -1), (key1656, -1), (key1574, -1), (key1623, -1), (key1425, 1), (key1623, 1), (key1569, 1), (key1618, 1), (key1420, -1), (key1618, -1)]

theorem rawRowCheck5318 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow5318 := by decide +kernel

def row5318 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5318 : row5318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5318 := by decide +kernel

theorem rowEval5318 (x : Key → ℝ) : Integer.Sparse.eval row5318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5318, Integer.Sparse.eval_collectBalanced, rawRowCheck5318]

def rawRow5319 : Integer.Sparse Key := [(key1344, -1), (key1338, -1), (key1338, 2), (key1325, -1), (key1317, -1), (key1325, 2), (key1297, 2), (key1317, -1), (key1297, -1), (key1312, 2), (key1312, -1), (key1292, -1), (key1779, 1), (key1773, 1), (key1773, -2), (key1555, 1), (key1547, 1), (key1555, -2), (key1392, -2), (key1547, 1), (key1392, 1), (key1542, -2), (key1542, 1), (key1387, 1), (key1816, -1), (key1789, -1), (key1814, 1), (key1789, 1), (key1658, 1), (key1456, 1), (key1656, -1), (key1456, -1), (key1623, -1), (key1574, -1), (key1623, 1), (key1425, 1), (key1618, 1), (key1569, 1), (key1618, -1), (key1420, -1)]

theorem rawRowCheck5319 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow5319 := by decide +kernel

def row5319 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5319 : row5319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5319 := by decide +kernel

theorem rowEval5319 (x : Key → ℝ) : Integer.Sparse.eval row5319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5319, Integer.Sparse.eval_collectBalanced, rawRowCheck5319]

def rawRow5320 : Integer.Sparse Key := [(key1387, -1), (key1392, -1), (key1392, 2), (key1420, -1), (key1425, -1), (key1420, 2), (key1456, 2), (key1425, -1), (key1456, -1), (key1443, 2), (key1443, -1), (key1465, -1), (key1292, 1), (key1297, 1), (key1297, -2), (key1569, 1), (key1574, 1), (key1569, -2), (key1789, -2), (key1574, 1), (key1789, 1), (key1592, -2), (key1592, 1), (key1797, 1), (key1312, -1), (key1338, -1), (key1317, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1547, -1), (key1773, -1), (key1618, -1), (key1656, -1), (key1618, 1), (key1814, 1), (key1632, 1), (key1666, 1), (key1632, -1), (key1824, -1)]

theorem rawRowCheck5320 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5320 := by decide +kernel

def row5320 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5320 : row5320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5320 := by decide +kernel

theorem rowEval5320 (x : Key → ℝ) : Integer.Sparse.eval row5320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5320, Integer.Sparse.eval_collectBalanced, rawRowCheck5320]

def rawRow5321 : Integer.Sparse Key := [(key1392, -1), (key1387, -1), (key1392, 2), (key1425, -1), (key1420, -1), (key1456, 2), (key1420, 2), (key1456, -1), (key1425, -1), (key1443, 2), (key1465, -1), (key1443, -1), (key1297, 1), (key1292, 1), (key1297, -2), (key1574, 1), (key1569, 1), (key1789, -2), (key1569, -2), (key1789, 1), (key1574, 1), (key1592, -2), (key1797, 1), (key1592, 1), (key1338, -1), (key1312, -1), (key1338, 1), (key1317, 1), (key1773, 1), (key1542, 1), (key1773, -1), (key1547, -1), (key1656, -1), (key1618, -1), (key1814, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1824, -1), (key1632, -1)]

theorem rawRowCheck5321 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5321 := by decide +kernel

def row5321 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5321 : row5321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5321 := by decide +kernel

theorem rowEval5321 (x : Key → ℝ) : Integer.Sparse.eval row5321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5321, Integer.Sparse.eval_collectBalanced, rawRowCheck5321]

def rawRow5322 : Integer.Sparse Key := [(key1392, -1), (key1392, -1), (key1387, 2), (key1456, -1), (key1456, -1), (key1425, 2), (key1425, 2), (key1420, -1), (key1420, -1), (key1465, 2), (key1443, -1), (key1443, -1), (key1297, 1), (key1297, 1), (key1292, -2), (key1789, 1), (key1789, 1), (key1574, -2), (key1574, -2), (key1569, 1), (key1569, 1), (key1797, -2), (key1592, 1), (key1592, 1), (key1317, -1), (key1317, -1), (key1312, 1), (key1312, 1), (key1547, 1), (key1547, 1), (key1542, -1), (key1542, -1), (key1814, -1), (key1814, -1), (key1656, 1), (key1656, 1), (key1824, 1), (key1824, 1), (key1666, -1), (key1666, -1)]

theorem rawRowCheck5322 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5322 := by decide +kernel

def row5322 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

theorem rowCheck5322 : row5322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5322 := by decide +kernel

theorem rowEval5322 (x : Key → ℝ) : Integer.Sparse.eval row5322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5322, Integer.Sparse.eval_collectBalanced, rawRowCheck5322]

def rawRow5323 : Integer.Sparse Key := [(key1420, -1), (key1425, -1), (key1443, 2), (key1387, -1), (key1392, -1), (key1420, 2), (key1456, 2), (key1443, -1), (key1465, -1), (key1392, 2), (key1425, -1), (key1456, -1), (key1569, 1), (key1574, 1), (key1592, -2), (key1292, 1), (key1297, 1), (key1569, -2), (key1789, -2), (key1592, 1), (key1797, 1), (key1297, -2), (key1574, 1), (key1789, 1), (key1618, -1), (key1656, -1), (key1632, 1), (key1666, 1), (key1618, 1), (key1814, 1), (key1632, -1), (key1824, -1), (key1312, -1), (key1338, -1), (key1542, 1), (key1773, 1), (key1317, 1), (key1338, 1), (key1547, -1), (key1773, -1)]

theorem rawRowCheck5323 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form1 = rawRow5323 := by decide +kernel

def row5323 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5323 : row5323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5323 := by decide +kernel

theorem rowEval5323 (x : Key → ℝ) : Integer.Sparse.eval row5323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5323, Integer.Sparse.eval_collectBalanced, rawRowCheck5323]

def rawRow5324 : Integer.Sparse Key := [(key1425, -1), (key1420, -1), (key1443, 2), (key1392, -1), (key1387, -1), (key1456, 2), (key1420, 2), (key1465, -1), (key1443, -1), (key1392, 2), (key1456, -1), (key1425, -1), (key1574, 1), (key1569, 1), (key1592, -2), (key1297, 1), (key1292, 1), (key1789, -2), (key1569, -2), (key1797, 1), (key1592, 1), (key1297, -2), (key1789, 1), (key1574, 1), (key1656, -1), (key1618, -1), (key1666, 1), (key1632, 1), (key1814, 1), (key1618, 1), (key1824, -1), (key1632, -1), (key1338, -1), (key1312, -1), (key1773, 1), (key1542, 1), (key1338, 1), (key1317, 1), (key1773, -1), (key1547, -1)]

theorem rawRowCheck5324 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form1 = rawRow5324 := by decide +kernel

def row5324 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5324 : row5324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5324 := by decide +kernel

theorem rowEval5324 (x : Key → ℝ) : Integer.Sparse.eval row5324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5324, Integer.Sparse.eval_collectBalanced, rawRowCheck5324]

def rawRow5325 : Integer.Sparse Key := [(key1420, -1), (key1443, -1), (key1425, 2), (key1420, -1), (key1443, -1), (key1387, 2), (key1465, 2), (key1392, -1), (key1456, -1), (key1425, 2), (key1392, -1), (key1456, -1), (key1569, 1), (key1592, 1), (key1574, -2), (key1569, 1), (key1592, 1), (key1292, -2), (key1797, -2), (key1297, 1), (key1789, 1), (key1574, -2), (key1297, 1), (key1789, 1), (key1542, -1), (key1666, -1), (key1547, 1), (key1656, 1), (key1312, 1), (key1824, 1), (key1317, -1), (key1814, -1), (key1542, -1), (key1666, -1), (key1312, 1), (key1824, 1), (key1547, 1), (key1656, 1), (key1317, -1), (key1814, -1)]

theorem rawRowCheck5325 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form1 = rawRow5325 := by decide +kernel

def row5325 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

theorem rowCheck5325 : row5325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5325 := by decide +kernel

theorem rowEval5325 (x : Key → ℝ) : Integer.Sparse.eval row5325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5325, Integer.Sparse.eval_collectBalanced, rawRowCheck5325]

def rawRow5326 : Integer.Sparse Key := [(key1443, -1), (key1420, -1), (key1425, 2), (key1443, -1), (key1420, -1), (key1465, 2), (key1387, 2), (key1456, -1), (key1392, -1), (key1425, 2), (key1456, -1), (key1392, -1), (key1592, 1), (key1569, 1), (key1574, -2), (key1592, 1), (key1569, 1), (key1797, -2), (key1292, -2), (key1789, 1), (key1297, 1), (key1574, -2), (key1789, 1), (key1297, 1), (key1666, -1), (key1542, -1), (key1656, 1), (key1547, 1), (key1824, 1), (key1312, 1), (key1814, -1), (key1317, -1), (key1666, -1), (key1542, -1), (key1824, 1), (key1312, 1), (key1656, 1), (key1547, 1), (key1814, -1), (key1317, -1)]

theorem rawRowCheck5326 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form1 = rawRow5326 := by decide +kernel

def row5326 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

theorem rowCheck5326 : row5326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5326 := by decide +kernel

theorem rowEval5326 (x : Key → ℝ) : Integer.Sparse.eval row5326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5326, Integer.Sparse.eval_collectBalanced, rawRowCheck5326]

def rawRow5327 : Integer.Sparse Key := [(key1425, -1), (key1443, -1), (key1420, 2), (key1456, -1), (key1465, -1), (key1392, 2), (key1443, 2), (key1387, -1), (key1420, -1), (key1456, 2), (key1392, -1), (key1425, -1), (key1574, 1), (key1592, 1), (key1569, -2), (key1789, 1), (key1797, 1), (key1297, -2), (key1592, -2), (key1292, 1), (key1569, 1), (key1789, -2), (key1297, 1), (key1574, 1), (key1547, -1), (key1632, -1), (key1542, 1), (key1618, 1), (key1317, 1), (key1632, 1), (key1312, -1), (key1618, -1), (key1773, -1), (key1824, -1), (key1338, 1), (key1666, 1), (key1773, 1), (key1814, 1), (key1338, -1), (key1656, -1)]

theorem rawRowCheck5327 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form1 = rawRow5327 := by decide +kernel

def row5327 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5327 : row5327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5327 := by decide +kernel

theorem rowEval5327 (x : Key → ℝ) : Integer.Sparse.eval row5327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5327, Integer.Sparse.eval_collectBalanced, rawRowCheck5327]

def rawRow5328 : Integer.Sparse Key := [(key1443, -1), (key1425, -1), (key1420, 2), (key1465, -1), (key1456, -1), (key1443, 2), (key1392, 2), (key1420, -1), (key1387, -1), (key1456, 2), (key1425, -1), (key1392, -1), (key1592, 1), (key1574, 1), (key1569, -2), (key1797, 1), (key1789, 1), (key1592, -2), (key1297, -2), (key1569, 1), (key1292, 1), (key1789, -2), (key1574, 1), (key1297, 1), (key1632, -1), (key1547, -1), (key1618, 1), (key1542, 1), (key1632, 1), (key1317, 1), (key1618, -1), (key1312, -1), (key1824, -1), (key1773, -1), (key1666, 1), (key1338, 1), (key1814, 1), (key1773, 1), (key1656, -1), (key1338, -1)]

theorem rawRowCheck5328 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form1 = rawRow5328 := by decide +kernel

def row5328 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5328 : row5328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5328 := by decide +kernel

theorem rowEval5328 (x : Key → ℝ) : Integer.Sparse.eval row5328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5328, Integer.Sparse.eval_collectBalanced, rawRowCheck5328]

def rawRow5329 : Integer.Sparse Key := [(key1456, -1), (key1456, -1), (key1465, 2), (key1392, -1), (key1392, -1), (key1425, 2), (key1425, 2), (key1443, -1), (key1443, -1), (key1387, 2), (key1420, -1), (key1420, -1), (key1789, 1), (key1789, 1), (key1797, -2), (key1297, 1), (key1297, 1), (key1574, -2), (key1574, -2), (key1592, 1), (key1592, 1), (key1292, -2), (key1569, 1), (key1569, 1), (key1814, -1), (key1814, -1), (key1824, 1), (key1824, 1), (key1656, 1), (key1656, 1), (key1666, -1), (key1666, -1), (key1317, -1), (key1317, -1), (key1547, 1), (key1547, 1), (key1312, 1), (key1312, 1), (key1542, -1), (key1542, -1)]

theorem rawRowCheck5329 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form1 = rawRow5329 := by decide +kernel

def row5329 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

theorem rowCheck5329 : row5329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5329 := by decide +kernel

theorem rowEval5329 (x : Key → ℝ) : Integer.Sparse.eval row5329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5329, Integer.Sparse.eval_collectBalanced, rawRowCheck5329]

def rawRow5330 : Integer.Sparse Key := [(key1456, -1), (key1465, -1), (key1456, 2), (key1425, -1), (key1443, -1), (key1392, 2), (key1443, 2), (key1392, -1), (key1425, -1), (key1420, 2), (key1387, -1), (key1420, -1), (key1789, 1), (key1797, 1), (key1789, -2), (key1574, 1), (key1592, 1), (key1297, -2), (key1592, -2), (key1297, 1), (key1574, 1), (key1569, -2), (key1292, 1), (key1569, 1), (key1773, -1), (key1824, -1), (key1773, 1), (key1814, 1), (key1338, 1), (key1666, 1), (key1338, -1), (key1656, -1), (key1547, -1), (key1632, -1), (key1317, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

theorem rawRowCheck5330 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form1 = rawRow5330 := by decide +kernel

def row5330 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5330 : row5330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5330 := by decide +kernel

theorem rowEval5330 (x : Key → ℝ) : Integer.Sparse.eval row5330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5330, Integer.Sparse.eval_collectBalanced, rawRowCheck5330]

def rawRow5331 : Integer.Sparse Key := [(key1465, -1), (key1456, -1), (key1456, 2), (key1443, -1), (key1425, -1), (key1443, 2), (key1392, 2), (key1425, -1), (key1392, -1), (key1420, 2), (key1420, -1), (key1387, -1), (key1797, 1), (key1789, 1), (key1789, -2), (key1592, 1), (key1574, 1), (key1592, -2), (key1297, -2), (key1574, 1), (key1297, 1), (key1569, -2), (key1569, 1), (key1292, 1), (key1824, -1), (key1773, -1), (key1814, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1656, -1), (key1338, -1), (key1632, -1), (key1547, -1), (key1632, 1), (key1317, 1), (key1618, 1), (key1542, 1), (key1618, -1), (key1312, -1)]

theorem rawRowCheck5331 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form1 = rawRow5331 := by decide +kernel

def row5331 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5331 : row5331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5331 := by decide +kernel

theorem rowEval5331 (x : Key → ℝ) : Integer.Sparse.eval row5331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5331, Integer.Sparse.eval_collectBalanced, rawRowCheck5331]

def rawRow5332 : Integer.Sparse Key := [(key1542, -1), (key1555, -1), (key1547, 2), (key1618, -1), (key1623, -1), (key1569, 2), (key1658, 2), (key1574, -1), (key1656, -1), (key1632, 2), (key1592, -1), (key1666, -1), (key1312, 1), (key1325, 1), (key1317, -2), (key1618, 1), (key1623, 1), (key1420, -2), (key1816, -2), (key1425, 1), (key1814, 1), (key1632, -2), (key1443, 1), (key1824, 1), (key1292, -1), (key1344, -1), (key1297, 1), (key1338, 1), (key1387, 1), (key1779, 1), (key1392, -1), (key1773, -1), (key1569, -1), (key1658, -1), (key1420, 1), (key1816, 1), (key1592, 1), (key1666, 1), (key1443, -1), (key1824, -1)]

theorem rawRowCheck5332 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form1 = rawRow5332 := by decide +kernel

def row5332 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5332 : row5332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5332 := by decide +kernel

theorem rowEval5332 (x : Key → ℝ) : Integer.Sparse.eval row5332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5332, Integer.Sparse.eval_collectBalanced, rawRowCheck5332]

def rawRow5333 : Integer.Sparse Key := [(key1555, -1), (key1542, -1), (key1547, 2), (key1623, -1), (key1618, -1), (key1658, 2), (key1569, 2), (key1656, -1), (key1574, -1), (key1632, 2), (key1666, -1), (key1592, -1), (key1325, 1), (key1312, 1), (key1317, -2), (key1623, 1), (key1618, 1), (key1816, -2), (key1420, -2), (key1814, 1), (key1425, 1), (key1632, -2), (key1824, 1), (key1443, 1), (key1344, -1), (key1292, -1), (key1338, 1), (key1297, 1), (key1779, 1), (key1387, 1), (key1773, -1), (key1392, -1), (key1658, -1), (key1569, -1), (key1816, 1), (key1420, 1), (key1666, 1), (key1592, 1), (key1824, -1), (key1443, -1)]

theorem rawRowCheck5333 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form1 = rawRow5333 := by decide +kernel

def row5333 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5333 : row5333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5333 := by decide +kernel

theorem rowEval5333 (x : Key → ℝ) : Integer.Sparse.eval row5333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5333, Integer.Sparse.eval_collectBalanced, rawRowCheck5333]

def rawRow5334 : Integer.Sparse Key := [(key1547, -1), (key1555, -1), (key1542, 2), (key1656, -1), (key1658, -1), (key1574, 2), (key1623, 2), (key1569, -1), (key1618, -1), (key1666, 2), (key1592, -1), (key1632, -1), (key1317, 1), (key1325, 1), (key1312, -2), (key1814, 1), (key1816, 1), (key1425, -2), (key1623, -2), (key1420, 1), (key1618, 1), (key1824, -2), (key1443, 1), (key1632, 1), (key1297, -1), (key1325, -1), (key1292, 1), (key1312, 1), (key1392, 1), (key1555, 1), (key1387, -1), (key1542, -1), (key1789, -1), (key1816, -1), (key1456, 1), (key1658, 1), (key1797, 1), (key1824, 1), (key1465, -1), (key1666, -1)]

theorem rawRowCheck5334 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form1 = rawRow5334 := by decide +kernel

def row5334 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5334 : row5334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5334 := by decide +kernel

theorem rowEval5334 (x : Key → ℝ) : Integer.Sparse.eval row5334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5334, Integer.Sparse.eval_collectBalanced, rawRowCheck5334]

def rawRow5335 : Integer.Sparse Key := [(key1555, -1), (key1547, -1), (key1542, 2), (key1658, -1), (key1656, -1), (key1623, 2), (key1574, 2), (key1618, -1), (key1569, -1), (key1666, 2), (key1632, -1), (key1592, -1), (key1325, 1), (key1317, 1), (key1312, -2), (key1816, 1), (key1814, 1), (key1623, -2), (key1425, -2), (key1618, 1), (key1420, 1), (key1824, -2), (key1632, 1), (key1443, 1), (key1325, -1), (key1297, -1), (key1312, 1), (key1292, 1), (key1555, 1), (key1392, 1), (key1542, -1), (key1387, -1), (key1816, -1), (key1789, -1), (key1658, 1), (key1456, 1), (key1824, 1), (key1797, 1), (key1666, -1), (key1465, -1)]

theorem rawRowCheck5335 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form1 = rawRow5335 := by decide +kernel

def row5335 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5335 : row5335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5335 := by decide +kernel

theorem rowEval5335 (x : Key → ℝ) : Integer.Sparse.eval row5335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5335, Integer.Sparse.eval_collectBalanced, rawRowCheck5335]

def rawRow5336 : Integer.Sparse Key := [(key1569, -1), (key1592, -1), (key1574, 2), (key1618, -1), (key1632, -1), (key1542, 2), (key1666, 2), (key1547, -1), (key1656, -1), (key1623, 2), (key1555, -1), (key1658, -1), (key1420, 1), (key1443, 1), (key1425, -2), (key1618, 1), (key1632, 1), (key1312, -2), (key1824, -2), (key1317, 1), (key1814, 1), (key1623, -2), (key1325, 1), (key1816, 1), (key1387, -1), (key1465, -1), (key1392, 1), (key1456, 1), (key1292, 1), (key1797, 1), (key1297, -1), (key1789, -1), (key1542, -1), (key1666, -1), (key1312, 1), (key1824, 1), (key1555, 1), (key1658, 1), (key1325, -1), (key1816, -1)]

theorem rawRowCheck5336 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form1 = rawRow5336 := by decide +kernel

def row5336 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5336 : row5336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5336 := by decide +kernel

theorem rowEval5336 (x : Key → ℝ) : Integer.Sparse.eval row5336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5336, Integer.Sparse.eval_collectBalanced, rawRowCheck5336]

def rawRow5337 : Integer.Sparse Key := [(key1592, -1), (key1569, -1), (key1574, 2), (key1632, -1), (key1618, -1), (key1666, 2), (key1542, 2), (key1656, -1), (key1547, -1), (key1623, 2), (key1658, -1), (key1555, -1), (key1443, 1), (key1420, 1), (key1425, -2), (key1632, 1), (key1618, 1), (key1824, -2), (key1312, -2), (key1814, 1), (key1317, 1), (key1623, -2), (key1816, 1), (key1325, 1), (key1465, -1), (key1387, -1), (key1456, 1), (key1392, 1), (key1797, 1), (key1292, 1), (key1789, -1), (key1297, -1), (key1666, -1), (key1542, -1), (key1824, 1), (key1312, 1), (key1658, 1), (key1555, 1), (key1816, -1), (key1325, -1)]

theorem rawRowCheck5337 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form1 = rawRow5337 := by decide +kernel

def row5337 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5337 : row5337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5337 := by decide +kernel

theorem rowEval5337 (x : Key → ℝ) : Integer.Sparse.eval row5337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5337, Integer.Sparse.eval_collectBalanced, rawRowCheck5337]

def rawRow5338 : Integer.Sparse Key := [(key1574, -1), (key1592, -1), (key1569, 2), (key1656, -1), (key1666, -1), (key1547, 2), (key1632, 2), (key1542, -1), (key1618, -1), (key1658, 2), (key1555, -1), (key1623, -1), (key1425, 1), (key1443, 1), (key1420, -2), (key1814, 1), (key1824, 1), (key1317, -2), (key1632, -2), (key1312, 1), (key1618, 1), (key1816, -2), (key1325, 1), (key1623, 1), (key1392, -1), (key1443, -1), (key1387, 1), (key1420, 1), (key1297, 1), (key1592, 1), (key1292, -1), (key1569, -1), (key1773, -1), (key1824, -1), (key1338, 1), (key1666, 1), (key1779, 1), (key1816, 1), (key1344, -1), (key1658, -1)]

theorem rawRowCheck5338 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form1 = rawRow5338 := by decide +kernel

def row5338 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5338 : row5338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5338 := by decide +kernel

theorem rowEval5338 (x : Key → ℝ) : Integer.Sparse.eval row5338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5338, Integer.Sparse.eval_collectBalanced, rawRowCheck5338]

def rawRow5339 : Integer.Sparse Key := [(key1592, -1), (key1574, -1), (key1569, 2), (key1666, -1), (key1656, -1), (key1632, 2), (key1547, 2), (key1618, -1), (key1542, -1), (key1658, 2), (key1623, -1), (key1555, -1), (key1443, 1), (key1425, 1), (key1420, -2), (key1824, 1), (key1814, 1), (key1632, -2), (key1317, -2), (key1618, 1), (key1312, 1), (key1816, -2), (key1623, 1), (key1325, 1), (key1443, -1), (key1392, -1), (key1420, 1), (key1387, 1), (key1592, 1), (key1297, 1), (key1569, -1), (key1292, -1), (key1824, -1), (key1773, -1), (key1666, 1), (key1338, 1), (key1816, 1), (key1779, 1), (key1658, -1), (key1344, -1)]

theorem rawRowCheck5339 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form1 = rawRow5339 := by decide +kernel

def row5339 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5339 : row5339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5339 := by decide +kernel

theorem rowEval5339 (x : Key → ℝ) : Integer.Sparse.eval row5339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5339, Integer.Sparse.eval_collectBalanced, rawRowCheck5339]

def rawRow5340 : Integer.Sparse Key := [(key1618, -1), (key1623, -1), (key1632, 2), (key1542, -1), (key1555, -1), (key1569, 2), (key1658, 2), (key1592, -1), (key1666, -1), (key1547, 2), (key1574, -1), (key1656, -1), (key1618, 1), (key1623, 1), (key1632, -2), (key1312, 1), (key1325, 1), (key1420, -2), (key1816, -2), (key1443, 1), (key1824, 1), (key1317, -2), (key1425, 1), (key1814, 1), (key1569, -1), (key1658, -1), (key1592, 1), (key1666, 1), (key1420, 1), (key1816, 1), (key1443, -1), (key1824, -1), (key1292, -1), (key1344, -1), (key1387, 1), (key1779, 1), (key1297, 1), (key1338, 1), (key1392, -1), (key1773, -1)]

theorem rawRowCheck5340 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form1 = rawRow5340 := by decide +kernel

def row5340 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5340 : row5340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5340 := by decide +kernel

theorem rowEval5340 (x : Key → ℝ) : Integer.Sparse.eval row5340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5340, Integer.Sparse.eval_collectBalanced, rawRowCheck5340]

def rawRow5341 : Integer.Sparse Key := [(key1623, -1), (key1618, -1), (key1632, 2), (key1555, -1), (key1542, -1), (key1658, 2), (key1569, 2), (key1666, -1), (key1592, -1), (key1547, 2), (key1656, -1), (key1574, -1), (key1623, 1), (key1618, 1), (key1632, -2), (key1325, 1), (key1312, 1), (key1816, -2), (key1420, -2), (key1824, 1), (key1443, 1), (key1317, -2), (key1814, 1), (key1425, 1), (key1658, -1), (key1569, -1), (key1666, 1), (key1592, 1), (key1816, 1), (key1420, 1), (key1824, -1), (key1443, -1), (key1344, -1), (key1292, -1), (key1779, 1), (key1387, 1), (key1338, 1), (key1297, 1), (key1773, -1), (key1392, -1)]

theorem rawRowCheck5341 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form1 = rawRow5341 := by decide +kernel

def row5341 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5341 : row5341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5341 := by decide +kernel

theorem rowEval5341 (x : Key → ℝ) : Integer.Sparse.eval row5341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5341, Integer.Sparse.eval_collectBalanced, rawRowCheck5341]

def rawRow5342 : Integer.Sparse Key := [(key1618, -1), (key1632, -1), (key1623, 2), (key1569, -1), (key1592, -1), (key1542, 2), (key1666, 2), (key1555, -1), (key1658, -1), (key1574, 2), (key1547, -1), (key1656, -1), (key1618, 1), (key1632, 1), (key1623, -2), (key1420, 1), (key1443, 1), (key1312, -2), (key1824, -2), (key1325, 1), (key1816, 1), (key1425, -2), (key1317, 1), (key1814, 1), (key1542, -1), (key1666, -1), (key1555, 1), (key1658, 1), (key1312, 1), (key1824, 1), (key1325, -1), (key1816, -1), (key1387, -1), (key1465, -1), (key1292, 1), (key1797, 1), (key1392, 1), (key1456, 1), (key1297, -1), (key1789, -1)]

theorem rawRowCheck5342 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form1 = rawRow5342 := by decide +kernel

def row5342 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5342 : row5342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5342 := by decide +kernel

theorem rowEval5342 (x : Key → ℝ) : Integer.Sparse.eval row5342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5342, Integer.Sparse.eval_collectBalanced, rawRowCheck5342]

def rawRow5343 : Integer.Sparse Key := [(key1632, -1), (key1618, -1), (key1623, 2), (key1592, -1), (key1569, -1), (key1666, 2), (key1542, 2), (key1658, -1), (key1555, -1), (key1574, 2), (key1656, -1), (key1547, -1), (key1632, 1), (key1618, 1), (key1623, -2), (key1443, 1), (key1420, 1), (key1824, -2), (key1312, -2), (key1816, 1), (key1325, 1), (key1425, -2), (key1814, 1), (key1317, 1), (key1666, -1), (key1542, -1), (key1658, 1), (key1555, 1), (key1824, 1), (key1312, 1), (key1816, -1), (key1325, -1), (key1465, -1), (key1387, -1), (key1797, 1), (key1292, 1), (key1456, 1), (key1392, 1), (key1789, -1), (key1297, -1)]

theorem rawRowCheck5343 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form1 = rawRow5343 := by decide +kernel

def row5343 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5343 : row5343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5343 := by decide +kernel

theorem rowEval5343 (x : Key → ℝ) : Integer.Sparse.eval row5343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5343, Integer.Sparse.eval_collectBalanced, rawRowCheck5343]

def rawRow5344 : Integer.Sparse Key := [(key1656, -1), (key1658, -1), (key1666, 2), (key1547, -1), (key1555, -1), (key1574, 2), (key1623, 2), (key1592, -1), (key1632, -1), (key1542, 2), (key1569, -1), (key1618, -1), (key1814, 1), (key1816, 1), (key1824, -2), (key1317, 1), (key1325, 1), (key1425, -2), (key1623, -2), (key1443, 1), (key1632, 1), (key1312, -2), (key1420, 1), (key1618, 1), (key1789, -1), (key1816, -1), (key1797, 1), (key1824, 1), (key1456, 1), (key1658, 1), (key1465, -1), (key1666, -1), (key1297, -1), (key1325, -1), (key1392, 1), (key1555, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1542, -1)]

theorem rawRowCheck5344 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form1 = rawRow5344 := by decide +kernel

def row5344 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5344 : row5344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5344 := by decide +kernel

theorem rowEval5344 (x : Key → ℝ) : Integer.Sparse.eval row5344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5344, Integer.Sparse.eval_collectBalanced, rawRowCheck5344]

def rawRow5345 : Integer.Sparse Key := [(key1658, -1), (key1656, -1), (key1666, 2), (key1555, -1), (key1547, -1), (key1623, 2), (key1574, 2), (key1632, -1), (key1592, -1), (key1542, 2), (key1618, -1), (key1569, -1), (key1816, 1), (key1814, 1), (key1824, -2), (key1325, 1), (key1317, 1), (key1623, -2), (key1425, -2), (key1632, 1), (key1443, 1), (key1312, -2), (key1618, 1), (key1420, 1), (key1816, -1), (key1789, -1), (key1824, 1), (key1797, 1), (key1658, 1), (key1456, 1), (key1666, -1), (key1465, -1), (key1325, -1), (key1297, -1), (key1555, 1), (key1392, 1), (key1312, 1), (key1292, 1), (key1542, -1), (key1387, -1)]

theorem rawRowCheck5345 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form1 = rawRow5345 := by decide +kernel

def row5345 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

theorem rowCheck5345 : row5345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5345 := by decide +kernel

theorem rowEval5345 (x : Key → ℝ) : Integer.Sparse.eval row5345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5345, Integer.Sparse.eval_collectBalanced, rawRowCheck5345]

def rawRow5346 : Integer.Sparse Key := [(key1656, -1), (key1666, -1), (key1658, 2), (key1574, -1), (key1592, -1), (key1547, 2), (key1632, 2), (key1555, -1), (key1623, -1), (key1569, 2), (key1542, -1), (key1618, -1), (key1814, 1), (key1824, 1), (key1816, -2), (key1425, 1), (key1443, 1), (key1317, -2), (key1632, -2), (key1325, 1), (key1623, 1), (key1420, -2), (key1312, 1), (key1618, 1), (key1773, -1), (key1824, -1), (key1779, 1), (key1816, 1), (key1338, 1), (key1666, 1), (key1344, -1), (key1658, -1), (key1392, -1), (key1443, -1), (key1297, 1), (key1592, 1), (key1387, 1), (key1420, 1), (key1292, -1), (key1569, -1)]

theorem rawRowCheck5346 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form1 = rawRow5346 := by decide +kernel

def row5346 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5346 : row5346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5346 := by decide +kernel

theorem rowEval5346 (x : Key → ℝ) : Integer.Sparse.eval row5346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5346, Integer.Sparse.eval_collectBalanced, rawRowCheck5346]

def rawRow5347 : Integer.Sparse Key := [(key1666, -1), (key1656, -1), (key1658, 2), (key1592, -1), (key1574, -1), (key1632, 2), (key1547, 2), (key1623, -1), (key1555, -1), (key1569, 2), (key1618, -1), (key1542, -1), (key1824, 1), (key1814, 1), (key1816, -2), (key1443, 1), (key1425, 1), (key1632, -2), (key1317, -2), (key1623, 1), (key1325, 1), (key1420, -2), (key1618, 1), (key1312, 1), (key1824, -1), (key1773, -1), (key1816, 1), (key1779, 1), (key1666, 1), (key1338, 1), (key1658, -1), (key1344, -1), (key1443, -1), (key1392, -1), (key1592, 1), (key1297, 1), (key1420, 1), (key1387, 1), (key1569, -1), (key1292, -1)]

theorem rawRowCheck5347 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form1 = rawRow5347 := by decide +kernel

def row5347 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

theorem rowCheck5347 : row5347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5347 := by decide +kernel

theorem rowEval5347 (x : Key → ℝ) : Integer.Sparse.eval row5347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form1) x := by
  rw [rowCheck5347, Integer.Sparse.eval_collectBalanced, rawRowCheck5347]

def rawRow5348 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2611, 2), (key2624, -1), (key2627, -1), (key2624, 2), (key2636, 2), (key2627, -1), (key2636, -1), (key2645, 2), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2666, -2), (key2698, 1), (key2701, 1), (key2698, -2), (key2722, -2), (key2701, 1), (key2722, 1), (key2734, -2), (key2734, 1), (key2745, 1), (key2778, -1), (key2790, -1), (key2781, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2804, -1), (key2825, -1), (key2851, -1), (key2856, -1), (key2851, 1), (key2866, 1), (key2892, 1), (key2895, 1), (key2892, -1), (key2902, -1)]

theorem rawRowCheck5348 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5348 := by decide +kernel

def row5348 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5348 : row5348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5348 := by decide +kernel

theorem rowEval5348 (x : Key → ℝ) : Integer.Sparse.eval row5348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5348, Integer.Sparse.eval_collectBalanced, rawRowCheck5348]

def rawRow5349 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2611, 2), (key2627, -1), (key2624, -1), (key2636, 2), (key2624, 2), (key2636, -1), (key2627, -1), (key2645, 2), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2666, -2), (key2701, 1), (key2698, 1), (key2722, -2), (key2698, -2), (key2722, 1), (key2701, 1), (key2734, -2), (key2745, 1), (key2734, 1), (key2790, -1), (key2778, -1), (key2790, 1), (key2781, 1), (key2825, 1), (key2801, 1), (key2825, -1), (key2804, -1), (key2856, -1), (key2851, -1), (key2866, 1), (key2851, 1), (key2895, 1), (key2892, 1), (key2902, -1), (key2892, -1)]

theorem rawRowCheck5349 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5349 := by decide +kernel

def row5349 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5349 : row5349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5349 := by decide +kernel

theorem rowEval5349 (x : Key → ℝ) : Integer.Sparse.eval row5349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5349, Integer.Sparse.eval_collectBalanced, rawRowCheck5349]

def rawRow5350 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2608, 2), (key2636, -1), (key2636, -1), (key2627, 2), (key2627, 2), (key2624, -1), (key2624, -1), (key2651, 2), (key2645, -1), (key2645, -1), (key2666, 1), (key2666, 1), (key2663, -2), (key2722, 1), (key2722, 1), (key2701, -2), (key2701, -2), (key2698, 1), (key2698, 1), (key2745, -2), (key2734, 1), (key2734, 1), (key2781, -1), (key2781, -1), (key2778, 1), (key2778, 1), (key2804, 1), (key2804, 1), (key2801, -1), (key2801, -1), (key2866, -1), (key2866, -1), (key2856, 1), (key2856, 1), (key2902, 1), (key2902, 1), (key2895, -1), (key2895, -1)]

theorem rawRowCheck5350 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5350 := by decide +kernel

def row5350 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

theorem rowCheck5350 : row5350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5350 := by decide +kernel

theorem rowEval5350 (x : Key → ℝ) : Integer.Sparse.eval row5350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5350, Integer.Sparse.eval_collectBalanced, rawRowCheck5350]

def rawRow5351 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2636, 2), (key2608, -1), (key2611, -1), (key2624, 2), (key2636, 2), (key2645, -1), (key2651, -1), (key2611, 2), (key2627, -1), (key2636, -1), (key2698, 1), (key2701, 1), (key2734, -2), (key2663, 1), (key2666, 1), (key2698, -2), (key2722, -2), (key2734, 1), (key2745, 1), (key2666, -2), (key2701, 1), (key2722, 1), (key2851, -1), (key2856, -1), (key2892, 1), (key2895, 1), (key2851, 1), (key2866, 1), (key2892, -1), (key2902, -1), (key2778, -1), (key2790, -1), (key2801, 1), (key2825, 1), (key2781, 1), (key2790, 1), (key2804, -1), (key2825, -1)]

theorem rawRowCheck5351 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form2 = rawRow5351 := by decide +kernel

def row5351 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5351 : row5351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5351 := by decide +kernel

theorem rowEval5351 (x : Key → ℝ) : Integer.Sparse.eval row5351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5351, Integer.Sparse.eval_collectBalanced, rawRowCheck5351]

def rawRow5352 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2636, 2), (key2611, -1), (key2608, -1), (key2636, 2), (key2624, 2), (key2651, -1), (key2645, -1), (key2611, 2), (key2636, -1), (key2627, -1), (key2701, 1), (key2698, 1), (key2734, -2), (key2666, 1), (key2663, 1), (key2722, -2), (key2698, -2), (key2745, 1), (key2734, 1), (key2666, -2), (key2722, 1), (key2701, 1), (key2856, -1), (key2851, -1), (key2895, 1), (key2892, 1), (key2866, 1), (key2851, 1), (key2902, -1), (key2892, -1), (key2790, -1), (key2778, -1), (key2825, 1), (key2801, 1), (key2790, 1), (key2781, 1), (key2825, -1), (key2804, -1)]

theorem rawRowCheck5352 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form2 = rawRow5352 := by decide +kernel

def row5352 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5352 : row5352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5352 := by decide +kernel

theorem rowEval5352 (x : Key → ℝ) : Integer.Sparse.eval row5352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5352, Integer.Sparse.eval_collectBalanced, rawRowCheck5352]

def rawRow5353 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2627, 2), (key2624, -1), (key2636, -1), (key2608, 2), (key2651, 2), (key2611, -1), (key2636, -1), (key2627, 2), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2701, -2), (key2698, 1), (key2734, 1), (key2663, -2), (key2745, -2), (key2666, 1), (key2722, 1), (key2701, -2), (key2666, 1), (key2722, 1), (key2801, -1), (key2895, -1), (key2804, 1), (key2856, 1), (key2778, 1), (key2902, 1), (key2781, -1), (key2866, -1), (key2801, -1), (key2895, -1), (key2778, 1), (key2902, 1), (key2804, 1), (key2856, 1), (key2781, -1), (key2866, -1)]

theorem rawRowCheck5353 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form2 = rawRow5353 := by decide +kernel

def row5353 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

theorem rowCheck5353 : row5353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5353 := by decide +kernel

theorem rowEval5353 (x : Key → ℝ) : Integer.Sparse.eval row5353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5353, Integer.Sparse.eval_collectBalanced, rawRowCheck5353]

def rawRow5354 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2627, 2), (key2636, -1), (key2624, -1), (key2651, 2), (key2608, 2), (key2636, -1), (key2611, -1), (key2627, 2), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2701, -2), (key2734, 1), (key2698, 1), (key2745, -2), (key2663, -2), (key2722, 1), (key2666, 1), (key2701, -2), (key2722, 1), (key2666, 1), (key2895, -1), (key2801, -1), (key2856, 1), (key2804, 1), (key2902, 1), (key2778, 1), (key2866, -1), (key2781, -1), (key2895, -1), (key2801, -1), (key2902, 1), (key2778, 1), (key2856, 1), (key2804, 1), (key2866, -1), (key2781, -1)]

theorem rawRowCheck5354 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form2 = rawRow5354 := by decide +kernel

def row5354 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

theorem rowCheck5354 : row5354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5354 := by decide +kernel

theorem rowEval5354 (x : Key → ℝ) : Integer.Sparse.eval row5354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5354, Integer.Sparse.eval_collectBalanced, rawRowCheck5354]

def rawRow5355 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2624, 2), (key2645, -1), (key2651, -1), (key2611, 2), (key2636, 2), (key2608, -1), (key2624, -1), (key2636, 2), (key2611, -1), (key2627, -1), (key2701, 1), (key2734, 1), (key2698, -2), (key2722, 1), (key2745, 1), (key2666, -2), (key2734, -2), (key2663, 1), (key2698, 1), (key2722, -2), (key2666, 1), (key2701, 1), (key2804, -1), (key2892, -1), (key2801, 1), (key2851, 1), (key2781, 1), (key2892, 1), (key2778, -1), (key2851, -1), (key2825, -1), (key2902, -1), (key2790, 1), (key2895, 1), (key2825, 1), (key2866, 1), (key2790, -1), (key2856, -1)]

theorem rawRowCheck5355 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form2 = rawRow5355 := by decide +kernel

def row5355 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5355 : row5355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5355 := by decide +kernel

theorem rowEval5355 (x : Key → ℝ) : Integer.Sparse.eval row5355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5355, Integer.Sparse.eval_collectBalanced, rawRowCheck5355]

def rawRow5356 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2624, 2), (key2651, -1), (key2645, -1), (key2636, 2), (key2611, 2), (key2624, -1), (key2608, -1), (key2636, 2), (key2627, -1), (key2611, -1), (key2734, 1), (key2701, 1), (key2698, -2), (key2745, 1), (key2722, 1), (key2734, -2), (key2666, -2), (key2698, 1), (key2663, 1), (key2722, -2), (key2701, 1), (key2666, 1), (key2892, -1), (key2804, -1), (key2851, 1), (key2801, 1), (key2892, 1), (key2781, 1), (key2851, -1), (key2778, -1), (key2902, -1), (key2825, -1), (key2895, 1), (key2790, 1), (key2866, 1), (key2825, 1), (key2856, -1), (key2790, -1)]

theorem rawRowCheck5356 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form2 = rawRow5356 := by decide +kernel

def row5356 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5356 : row5356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5356 := by decide +kernel

theorem rowEval5356 (x : Key → ℝ) : Integer.Sparse.eval row5356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5356, Integer.Sparse.eval_collectBalanced, rawRowCheck5356]

def rawRow5357 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2651, 2), (key2611, -1), (key2611, -1), (key2627, 2), (key2627, 2), (key2636, -1), (key2636, -1), (key2608, 2), (key2624, -1), (key2624, -1), (key2722, 1), (key2722, 1), (key2745, -2), (key2666, 1), (key2666, 1), (key2701, -2), (key2701, -2), (key2734, 1), (key2734, 1), (key2663, -2), (key2698, 1), (key2698, 1), (key2866, -1), (key2866, -1), (key2902, 1), (key2902, 1), (key2856, 1), (key2856, 1), (key2895, -1), (key2895, -1), (key2781, -1), (key2781, -1), (key2804, 1), (key2804, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

theorem rawRowCheck5357 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form2 = rawRow5357 := by decide +kernel

def row5357 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

theorem rowCheck5357 : row5357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5357 := by decide +kernel

theorem rowEval5357 (x : Key → ℝ) : Integer.Sparse.eval row5357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5357, Integer.Sparse.eval_collectBalanced, rawRowCheck5357]

def rawRow5358 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2645, 2), (key2627, -1), (key2636, -1), (key2611, 2), (key2636, 2), (key2611, -1), (key2627, -1), (key2624, 2), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2722, -2), (key2701, 1), (key2734, 1), (key2666, -2), (key2734, -2), (key2666, 1), (key2701, 1), (key2698, -2), (key2663, 1), (key2698, 1), (key2825, -1), (key2902, -1), (key2825, 1), (key2866, 1), (key2790, 1), (key2895, 1), (key2790, -1), (key2856, -1), (key2804, -1), (key2892, -1), (key2781, 1), (key2892, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

theorem rawRowCheck5358 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form2 = rawRow5358 := by decide +kernel

def row5358 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5358 : row5358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5358 := by decide +kernel

theorem rowEval5358 (x : Key → ℝ) : Integer.Sparse.eval row5358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5358, Integer.Sparse.eval_collectBalanced, rawRowCheck5358]

def rawRow5359 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2645, 2), (key2636, -1), (key2627, -1), (key2636, 2), (key2611, 2), (key2627, -1), (key2611, -1), (key2624, 2), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2722, -2), (key2734, 1), (key2701, 1), (key2734, -2), (key2666, -2), (key2701, 1), (key2666, 1), (key2698, -2), (key2698, 1), (key2663, 1), (key2902, -1), (key2825, -1), (key2866, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2856, -1), (key2790, -1), (key2892, -1), (key2804, -1), (key2892, 1), (key2781, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

theorem rawRowCheck5359 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form2 = rawRow5359 := by decide +kernel

def row5359 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

theorem rowCheck5359 : row5359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5359 := by decide +kernel

theorem rowEval5359 (x : Key → ℝ) : Integer.Sparse.eval row5359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5359, Integer.Sparse.eval_collectBalanced, rawRowCheck5359]

def rawRow5360 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2666, 2), (key2698, -1), (key2701, -1), (key2698, 2), (key2734, 2), (key2701, -1), (key2734, -1), (key2722, 2), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2611, -2), (key2801, 1), (key2804, 1), (key2801, -2), (key2825, -2), (key2804, 1), (key2825, 1), (key2947, -2), (key2947, 1), (key2958, 1), (key2624, -1), (key2636, -1), (key2627, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2701, -1), (key2722, -1), (key2851, -1), (key2856, -1), (key2851, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, -1), (key2981, -1)]

theorem rawRowCheck5360 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5360 := by decide +kernel

def row5360 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5360 : row5360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5360 := by decide +kernel

theorem rowEval5360 (x : Key → ℝ) : Integer.Sparse.eval row5360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5360, Integer.Sparse.eval_collectBalanced, rawRowCheck5360]

def rawRow5361 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2666, 2), (key2701, -1), (key2698, -1), (key2734, 2), (key2698, 2), (key2734, -1), (key2701, -1), (key2722, 2), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2611, -2), (key2804, 1), (key2801, 1), (key2825, -2), (key2801, -2), (key2825, 1), (key2804, 1), (key2947, -2), (key2958, 1), (key2947, 1), (key2636, -1), (key2624, -1), (key2636, 1), (key2627, 1), (key2722, 1), (key2698, 1), (key2722, -1), (key2701, -1), (key2856, -1), (key2851, -1), (key2866, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2981, -1), (key2971, -1)]

theorem rawRowCheck5361 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5361 := by decide +kernel

def row5361 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5361 : row5361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5361 := by decide +kernel

theorem rowEval5361 (x : Key → ℝ) : Integer.Sparse.eval row5361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5361, Integer.Sparse.eval_collectBalanced, rawRowCheck5361]

def rawRow5362 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2663, 2), (key2734, -1), (key2734, -1), (key2701, 2), (key2701, 2), (key2698, -1), (key2698, -1), (key2745, 2), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2608, -2), (key2825, 1), (key2825, 1), (key2804, -2), (key2804, -2), (key2801, 1), (key2801, 1), (key2958, -2), (key2947, 1), (key2947, 1), (key2627, -1), (key2627, -1), (key2624, 1), (key2624, 1), (key2701, 1), (key2701, 1), (key2698, -1), (key2698, -1), (key2866, -1), (key2866, -1), (key2856, 1), (key2856, 1), (key2981, 1), (key2981, 1), (key2974, -1), (key2974, -1)]

theorem rawRowCheck5362 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5362 := by decide +kernel

def row5362 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 2), (key2856, 2), (key2866, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck5362 : row5362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5362 := by decide +kernel

theorem rowEval5362 (x : Key → ℝ) : Integer.Sparse.eval row5362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5362, Integer.Sparse.eval_collectBalanced, rawRowCheck5362]

def rawRow5363 : Integer.Sparse Key := [(key2698, -1), (key2701, -1), (key2722, 2), (key2663, -1), (key2666, -1), (key2698, 2), (key2734, 2), (key2722, -1), (key2745, -1), (key2666, 2), (key2701, -1), (key2734, -1), (key2801, 1), (key2804, 1), (key2825, -2), (key2608, 1), (key2611, 1), (key2801, -2), (key2825, -2), (key2947, 1), (key2958, 1), (key2611, -2), (key2804, 1), (key2825, 1), (key2851, -1), (key2856, -1), (key2971, 1), (key2974, 1), (key2851, 1), (key2866, 1), (key2971, -1), (key2981, -1), (key2624, -1), (key2636, -1), (key2698, 1), (key2722, 1), (key2627, 1), (key2636, 1), (key2701, -1), (key2722, -1)]

theorem rawRowCheck5363 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form2 = rawRow5363 := by decide +kernel

def row5363 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5363 : row5363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5363 := by decide +kernel

theorem rowEval5363 (x : Key → ℝ) : Integer.Sparse.eval row5363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5363, Integer.Sparse.eval_collectBalanced, rawRowCheck5363]

def rawRow5364 : Integer.Sparse Key := [(key2701, -1), (key2698, -1), (key2722, 2), (key2666, -1), (key2663, -1), (key2734, 2), (key2698, 2), (key2745, -1), (key2722, -1), (key2666, 2), (key2734, -1), (key2701, -1), (key2804, 1), (key2801, 1), (key2825, -2), (key2611, 1), (key2608, 1), (key2825, -2), (key2801, -2), (key2958, 1), (key2947, 1), (key2611, -2), (key2825, 1), (key2804, 1), (key2856, -1), (key2851, -1), (key2974, 1), (key2971, 1), (key2866, 1), (key2851, 1), (key2981, -1), (key2971, -1), (key2636, -1), (key2624, -1), (key2722, 1), (key2698, 1), (key2636, 1), (key2627, 1), (key2722, -1), (key2701, -1)]

theorem rawRowCheck5364 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form2 = rawRow5364 := by decide +kernel

def row5364 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5364 : row5364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5364 := by decide +kernel

theorem rowEval5364 (x : Key → ℝ) : Integer.Sparse.eval row5364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5364, Integer.Sparse.eval_collectBalanced, rawRowCheck5364]

def rawRow5365 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2701, 2), (key2698, -1), (key2722, -1), (key2663, 2), (key2745, 2), (key2666, -1), (key2734, -1), (key2701, 2), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2804, -2), (key2801, 1), (key2825, 1), (key2608, -2), (key2958, -2), (key2611, 1), (key2825, 1), (key2804, -2), (key2611, 1), (key2825, 1), (key2698, -1), (key2974, -1), (key2701, 1), (key2856, 1), (key2624, 1), (key2981, 1), (key2627, -1), (key2866, -1), (key2698, -1), (key2974, -1), (key2624, 1), (key2981, 1), (key2701, 1), (key2856, 1), (key2627, -1), (key2866, -1)]

theorem rawRowCheck5365 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form2 = rawRow5365 := by decide +kernel

def row5365 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 4), (key2856, 2), (key2866, -2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck5365 : row5365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5365 := by decide +kernel

theorem rowEval5365 (x : Key → ℝ) : Integer.Sparse.eval row5365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5365, Integer.Sparse.eval_collectBalanced, rawRowCheck5365]

def rawRow5366 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2698, -1), (key2745, 2), (key2663, 2), (key2734, -1), (key2666, -1), (key2701, 2), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2804, -2), (key2825, 1), (key2801, 1), (key2958, -2), (key2608, -2), (key2825, 1), (key2611, 1), (key2804, -2), (key2825, 1), (key2611, 1), (key2974, -1), (key2698, -1), (key2856, 1), (key2701, 1), (key2981, 1), (key2624, 1), (key2866, -1), (key2627, -1), (key2974, -1), (key2698, -1), (key2981, 1), (key2624, 1), (key2856, 1), (key2701, 1), (key2866, -1), (key2627, -1)]

theorem rawRowCheck5366 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form2 = rawRow5366 := by decide +kernel

def row5366 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 4), (key2856, 2), (key2866, -2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck5366 : row5366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5366 := by decide +kernel

theorem rowEval5366 (x : Key → ℝ) : Integer.Sparse.eval row5366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5366, Integer.Sparse.eval_collectBalanced, rawRowCheck5366]

def rawRow5367 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2698, 2), (key2734, -1), (key2745, -1), (key2666, 2), (key2722, 2), (key2663, -1), (key2698, -1), (key2734, 2), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2801, -2), (key2947, 1), (key2958, 1), (key2611, -2), (key2825, -2), (key2608, 1), (key2801, 1), (key2825, -2), (key2611, 1), (key2804, 1), (key2701, -1), (key2971, -1), (key2698, 1), (key2851, 1), (key2627, 1), (key2971, 1), (key2624, -1), (key2851, -1), (key2722, -1), (key2981, -1), (key2636, 1), (key2974, 1), (key2722, 1), (key2866, 1), (key2636, -1), (key2856, -1)]

theorem rawRowCheck5367 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form2 = rawRow5367 := by decide +kernel

def row5367 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5367 : row5367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5367 := by decide +kernel

theorem rowEval5367 (x : Key → ℝ) : Integer.Sparse.eval row5367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5367, Integer.Sparse.eval_collectBalanced, rawRowCheck5367]

def rawRow5368 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2698, 2), (key2745, -1), (key2734, -1), (key2722, 2), (key2666, 2), (key2698, -1), (key2663, -1), (key2734, 2), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2801, -2), (key2958, 1), (key2947, 1), (key2825, -2), (key2611, -2), (key2801, 1), (key2608, 1), (key2825, -2), (key2804, 1), (key2611, 1), (key2971, -1), (key2701, -1), (key2851, 1), (key2698, 1), (key2971, 1), (key2627, 1), (key2851, -1), (key2624, -1), (key2981, -1), (key2722, -1), (key2974, 1), (key2636, 1), (key2866, 1), (key2722, 1), (key2856, -1), (key2636, -1)]

theorem rawRowCheck5368 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form2 = rawRow5368 := by decide +kernel

def row5368 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5368 : row5368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5368 := by decide +kernel

theorem rowEval5368 (x : Key → ℝ) : Integer.Sparse.eval row5368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5368, Integer.Sparse.eval_collectBalanced, rawRowCheck5368]

def rawRow5369 : Integer.Sparse Key := [(key2734, -1), (key2734, -1), (key2745, 2), (key2666, -1), (key2666, -1), (key2701, 2), (key2701, 2), (key2722, -1), (key2722, -1), (key2663, 2), (key2698, -1), (key2698, -1), (key2947, 1), (key2947, 1), (key2958, -2), (key2611, 1), (key2611, 1), (key2804, -2), (key2804, -2), (key2825, 1), (key2825, 1), (key2608, -2), (key2801, 1), (key2801, 1), (key2866, -1), (key2866, -1), (key2981, 1), (key2981, 1), (key2856, 1), (key2856, 1), (key2974, -1), (key2974, -1), (key2627, -1), (key2627, -1), (key2701, 1), (key2701, 1), (key2624, 1), (key2624, 1), (key2698, -1), (key2698, -1)]

theorem rawRowCheck5369 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form2 = rawRow5369 := by decide +kernel

def row5369 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 2), (key2856, 2), (key2866, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck5369 : row5369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5369 := by decide +kernel

theorem rowEval5369 (x : Key → ℝ) : Integer.Sparse.eval row5369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5369, Integer.Sparse.eval_collectBalanced, rawRowCheck5369]

def rawRow5370 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2734, 2), (key2701, -1), (key2722, -1), (key2666, 2), (key2722, 2), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2947, -2), (key2804, 1), (key2825, 1), (key2611, -2), (key2825, -2), (key2611, 1), (key2804, 1), (key2801, -2), (key2608, 1), (key2801, 1), (key2722, -1), (key2981, -1), (key2722, 1), (key2866, 1), (key2636, 1), (key2974, 1), (key2636, -1), (key2856, -1), (key2701, -1), (key2971, -1), (key2627, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2624, -1), (key2851, -1)]

theorem rawRowCheck5370 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form2 = rawRow5370 := by decide +kernel

def row5370 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5370 : row5370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5370 := by decide +kernel

theorem rowEval5370 (x : Key → ℝ) : Integer.Sparse.eval row5370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5370, Integer.Sparse.eval_collectBalanced, rawRowCheck5370]

def rawRow5371 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2734, 2), (key2722, -1), (key2701, -1), (key2722, 2), (key2666, 2), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2947, -2), (key2825, 1), (key2804, 1), (key2825, -2), (key2611, -2), (key2804, 1), (key2611, 1), (key2801, -2), (key2801, 1), (key2608, 1), (key2981, -1), (key2722, -1), (key2866, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2856, -1), (key2636, -1), (key2971, -1), (key2701, -1), (key2971, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, -1), (key2624, -1)]

theorem rawRowCheck5371 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form2 = rawRow5371 := by decide +kernel

def row5371 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck5371 : row5371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5371 := by decide +kernel

theorem rowEval5371 (x : Key → ℝ) : Integer.Sparse.eval row5371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5371, Integer.Sparse.eval_collectBalanced, rawRowCheck5371]

def rawRow5372 : Integer.Sparse Key := [(key2778, -1), (key2790, -1), (key2781, 2), (key2851, -1), (key2856, -1), (key2801, 2), (key2895, 2), (key2804, -1), (key2892, -1), (key2866, 2), (key2825, -1), (key2902, -1), (key2624, 1), (key2636, 1), (key2627, -2), (key2851, 1), (key2856, 1), (key2698, -2), (key2974, -2), (key2701, 1), (key2971, 1), (key2866, -2), (key2722, 1), (key2981, 1), (key2608, -1), (key2651, -1), (key2611, 1), (key2636, 1), (key2663, 1), (key2745, 1), (key2666, -1), (key2722, -1), (key2801, -1), (key2895, -1), (key2778, 1), (key2902, 1), (key2947, 1), (key2974, 1), (key2935, -1), (key2981, -1)]

theorem rawRowCheck5372 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form2 = rawRow5372 := by decide +kernel

def row5372 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -2), (key2701, 1), (key2745, 1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2947, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5372 : row5372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5372 := by decide +kernel

theorem rowEval5372 (x : Key → ℝ) : Integer.Sparse.eval row5372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5372, Integer.Sparse.eval_collectBalanced, rawRowCheck5372]

def rawRow5373 : Integer.Sparse Key := [(key2790, -1), (key2778, -1), (key2781, 2), (key2856, -1), (key2851, -1), (key2895, 2), (key2801, 2), (key2892, -1), (key2804, -1), (key2866, 2), (key2902, -1), (key2825, -1), (key2636, 1), (key2624, 1), (key2627, -2), (key2856, 1), (key2851, 1), (key2974, -2), (key2698, -2), (key2971, 1), (key2701, 1), (key2866, -2), (key2981, 1), (key2722, 1), (key2651, -1), (key2608, -1), (key2636, 1), (key2611, 1), (key2745, 1), (key2663, 1), (key2722, -1), (key2666, -1), (key2895, -1), (key2801, -1), (key2902, 1), (key2778, 1), (key2974, 1), (key2947, 1), (key2981, -1), (key2935, -1)]

theorem rawRowCheck5373 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form2 = rawRow5373 := by decide +kernel

def row5373 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -2), (key2701, 1), (key2745, 1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2947, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5373 : row5373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5373 := by decide +kernel

theorem rowEval5373 (x : Key → ℝ) : Integer.Sparse.eval row5373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5373, Integer.Sparse.eval_collectBalanced, rawRowCheck5373]

def rawRow5374 : Integer.Sparse Key := [(key2781, -1), (key2790, -1), (key2778, 2), (key2892, -1), (key2895, -1), (key2804, 2), (key2856, 2), (key2801, -1), (key2851, -1), (key2902, 2), (key2825, -1), (key2866, -1), (key2627, 1), (key2636, 1), (key2624, -2), (key2971, 1), (key2974, 1), (key2701, -2), (key2856, -2), (key2698, 1), (key2851, 1), (key2981, -2), (key2722, 1), (key2866, 1), (key2611, -1), (key2636, -1), (key2608, 1), (key2624, 1), (key2666, 1), (key2734, 1), (key2663, -1), (key2698, -1), (key2825, -1), (key2902, -1), (key2790, 1), (key2895, 1), (key2958, 1), (key2981, 1), (key2941, -1), (key2974, -1)]

theorem rawRowCheck5374 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form2 = rawRow5374 := by decide +kernel

def row5374 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2941, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5374 : row5374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5374 := by decide +kernel

theorem rowEval5374 (x : Key → ℝ) : Integer.Sparse.eval row5374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5374, Integer.Sparse.eval_collectBalanced, rawRowCheck5374]

def rawRow5375 : Integer.Sparse Key := [(key2790, -1), (key2781, -1), (key2778, 2), (key2895, -1), (key2892, -1), (key2856, 2), (key2804, 2), (key2851, -1), (key2801, -1), (key2902, 2), (key2866, -1), (key2825, -1), (key2636, 1), (key2627, 1), (key2624, -2), (key2974, 1), (key2971, 1), (key2856, -2), (key2701, -2), (key2851, 1), (key2698, 1), (key2981, -2), (key2866, 1), (key2722, 1), (key2636, -1), (key2611, -1), (key2624, 1), (key2608, 1), (key2734, 1), (key2666, 1), (key2698, -1), (key2663, -1), (key2902, -1), (key2825, -1), (key2895, 1), (key2790, 1), (key2981, 1), (key2958, 1), (key2974, -1), (key2941, -1)]

theorem rawRowCheck5375 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form2 = rawRow5375 := by decide +kernel

def row5375 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2941, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5375 : row5375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5375 := by decide +kernel

theorem rowEval5375 (x : Key → ℝ) : Integer.Sparse.eval row5375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5375, Integer.Sparse.eval_collectBalanced, rawRowCheck5375]

end MUB6.Certificate.GramRows

end OAI
