import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1056 : Integer.Sparse Key := [(key406, -1), (key421, -1), (key236, -1), (key658, -1), (key241, -1), (key421, -1), (key411, 2), (key241, 2), (key421, 2), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1), (key321, -1), (key445, -1), (key253, -1), (key453, -1), (key263, -1), (key331, -1), (key487, -2), (key277, -2), (key489, -2), (key346, 1), (key488, 1), (key277, 1), (key489, 1), (key278, 1), (key347, 1)]

theorem rawRowCheck1056 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form5 = rawRow1056 := by decide +kernel

def row1056 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key658, -1), (key660, 1), (key662, 1)]

theorem rowCheck1056 : row1056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1056 := by decide +kernel

theorem rowEval1056 (x : Key → ℝ) : Integer.Sparse.eval row1056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1056, Integer.Sparse.eval_collectBalanced, rawRowCheck1056]

def rawRow1057 : Integer.Sparse Key := [(key421, -1), (key406, -1), (key658, -1), (key236, -1), (key421, -1), (key241, -1), (key411, 2), (key421, 2), (key241, 2), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1), (key445, -1), (key321, -1), (key453, -1), (key253, -1), (key331, -1), (key263, -1), (key487, -2), (key489, -2), (key277, -2), (key488, 1), (key346, 1), (key489, 1), (key277, 1), (key347, 1), (key278, 1)]

theorem rawRowCheck1057 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form5 = rawRow1057 := by decide +kernel

def row1057 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key658, -1), (key660, 1), (key662, 1)]

theorem rowCheck1057 : row1057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1057 := by decide +kernel

theorem rowEval1057 (x : Key → ℝ) : Integer.Sparse.eval row1057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1057, Integer.Sparse.eval_collectBalanced, rawRowCheck1057]

def rawRow1058 : Integer.Sparse Key := [(key657, -1), (key658, -1), (key241, -1), (key421, -1), (key236, -1), (key406, -1), (key421, 2), (key241, 2), (key411, 2), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1), (key331, -1), (key453, -1), (key263, -1), (key445, -1), (key253, -1), (key321, -1), (key489, -2), (key277, -2), (key487, -2), (key347, 1), (key489, 1), (key278, 1), (key488, 1), (key277, 1), (key346, 1)]

theorem rawRowCheck1058 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form5 = rawRow1058 := by decide +kernel

def row1058 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

theorem rowCheck1058 : row1058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1058 := by decide +kernel

theorem rowEval1058 (x : Key → ℝ) : Integer.Sparse.eval row1058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1058, Integer.Sparse.eval_collectBalanced, rawRowCheck1058]

def rawRow1059 : Integer.Sparse Key := [(key658, -1), (key657, -1), (key421, -1), (key241, -1), (key406, -1), (key236, -1), (key421, 2), (key411, 2), (key241, 2), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1), (key453, -1), (key331, -1), (key445, -1), (key263, -1), (key321, -1), (key253, -1), (key489, -2), (key487, -2), (key277, -2), (key489, 1), (key347, 1), (key488, 1), (key278, 1), (key346, 1), (key277, 1)]

theorem rawRowCheck1059 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form5 = rawRow1059 := by decide +kernel

def row1059 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

theorem rowCheck1059 : row1059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1059 := by decide +kernel

theorem rowEval1059 (x : Key → ℝ) : Integer.Sparse.eval row1059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1059, Integer.Sparse.eval_collectBalanced, rawRowCheck1059]

def rawRow1060 : Integer.Sparse Key := [(key241, -1), (key241, -1), (key411, -1), (key411, -1), (key421, -1), (key421, -1), (key236, 2), (key406, 2), (key406, 2), (key263, 1), (key263, 1), (key445, 1), (key445, 1), (key661, 1), (key661, 1), (key248, -1), (key248, -1), (key316, -1), (key316, -1), (key435, -1), (key435, -1), (key278, -2), (key488, -2), (key488, -2), (key277, 1), (key277, 1), (key346, 1), (key346, 1), (key487, 1), (key487, 1)]

theorem rawRowCheck1060 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form5 = rawRow1060 := by decide +kernel

def row1060 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

theorem rowCheck1060 : row1060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1060 := by decide +kernel

theorem rowEval1060 (x : Key → ℝ) : Integer.Sparse.eval row1060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1060, Integer.Sparse.eval_collectBalanced, rawRowCheck1060]

def rawRow1061 : Integer.Sparse Key := [(key411, -1), (key421, -1), (key241, -1), (key421, -1), (key241, -1), (key411, -1), (key406, 2), (key236, 2), (key406, 2), (key445, 1), (key661, 1), (key263, 1), (key661, 1), (key263, 1), (key445, 1), (key316, -1), (key435, -1), (key248, -1), (key435, -1), (key248, -1), (key316, -1), (key488, -2), (key278, -2), (key488, -2), (key346, 1), (key487, 1), (key277, 1), (key487, 1), (key277, 1), (key346, 1)]

theorem rawRowCheck1061 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form5 = rawRow1061 := by decide +kernel

def row1061 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

theorem rowCheck1061 : row1061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1061 := by decide +kernel

theorem rowEval1061 (x : Key → ℝ) : Integer.Sparse.eval row1061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1061, Integer.Sparse.eval_collectBalanced, rawRowCheck1061]

def rawRow1062 : Integer.Sparse Key := [(key421, -1), (key411, -1), (key421, -1), (key241, -1), (key411, -1), (key241, -1), (key406, 2), (key406, 2), (key236, 2), (key661, 1), (key445, 1), (key661, 1), (key263, 1), (key445, 1), (key263, 1), (key435, -1), (key316, -1), (key435, -1), (key248, -1), (key316, -1), (key248, -1), (key488, -2), (key488, -2), (key278, -2), (key487, 1), (key346, 1), (key487, 1), (key277, 1), (key346, 1), (key277, 1)]

theorem rawRowCheck1062 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form5 = rawRow1062 := by decide +kernel

def row1062 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

theorem rowCheck1062 : row1062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1062 := by decide +kernel

theorem rowEval1062 (x : Key → ℝ) : Integer.Sparse.eval row1062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1062, Integer.Sparse.eval_collectBalanced, rawRowCheck1062]

def rawRow1063 : Integer.Sparse Key := [(key248, -1), (key253, -1), (key435, -1), (key660, -1), (key453, -1), (key662, -1), (key263, 2), (key445, 2), (key661, 2), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1), (key277, -1), (key278, -1), (key346, -1), (key347, -1), (key488, -1), (key489, -1), (key241, -2), (key411, -2), (key421, -2), (key253, 1), (key263, 1), (key321, 1), (key331, 1), (key445, 1), (key453, 1)]

theorem rawRowCheck1063 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form5 = rawRow1063 := by decide +kernel

def row1063 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

theorem rowCheck1063 : row1063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1063 := by decide +kernel

theorem rowEval1063 (x : Key → ℝ) : Integer.Sparse.eval row1063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1063, Integer.Sparse.eval_collectBalanced, rawRowCheck1063]

def rawRow1064 : Integer.Sparse Key := [(key253, -1), (key248, -1), (key660, -1), (key435, -1), (key662, -1), (key453, -1), (key263, 2), (key661, 2), (key445, 2), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1), (key278, -1), (key277, -1), (key347, -1), (key346, -1), (key489, -1), (key488, -1), (key241, -2), (key421, -2), (key411, -2), (key263, 1), (key253, 1), (key331, 1), (key321, 1), (key453, 1), (key445, 1)]

theorem rawRowCheck1064 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form5 = rawRow1064 := by decide +kernel

def row1064 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

theorem rowCheck1064 : row1064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1064 := by decide +kernel

theorem rowEval1064 (x : Key → ℝ) : Integer.Sparse.eval row1064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1064, Integer.Sparse.eval_collectBalanced, rawRowCheck1064]

def rawRow1065 : Integer.Sparse Key := [(key435, -1), (key453, -1), (key248, -1), (key662, -1), (key253, -1), (key660, -1), (key445, 2), (key263, 2), (key661, 2), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1), (key346, -1), (key488, -1), (key277, -1), (key489, -1), (key278, -1), (key347, -1), (key411, -2), (key241, -2), (key421, -2), (key321, 1), (key445, 1), (key253, 1), (key453, 1), (key263, 1), (key331, 1)]

theorem rawRowCheck1065 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form5 = rawRow1065 := by decide +kernel

def row1065 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

theorem rowCheck1065 : row1065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1065 := by decide +kernel

theorem rowEval1065 (x : Key → ℝ) : Integer.Sparse.eval row1065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1065, Integer.Sparse.eval_collectBalanced, rawRowCheck1065]

def rawRow1066 : Integer.Sparse Key := [(key453, -1), (key435, -1), (key662, -1), (key248, -1), (key660, -1), (key253, -1), (key445, 2), (key661, 2), (key263, 2), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1), (key488, -1), (key346, -1), (key489, -1), (key277, -1), (key347, -1), (key278, -1), (key411, -2), (key421, -2), (key241, -2), (key445, 1), (key321, 1), (key453, 1), (key253, 1), (key331, 1), (key263, 1)]

theorem rawRowCheck1066 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form5 = rawRow1066 := by decide +kernel

def row1066 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

theorem rowCheck1066 : row1066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1066 := by decide +kernel

theorem rowEval1066 (x : Key → ℝ) : Integer.Sparse.eval row1066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1066, Integer.Sparse.eval_collectBalanced, rawRowCheck1066]

def rawRow1067 : Integer.Sparse Key := [(key660, -1), (key662, -1), (key253, -1), (key453, -1), (key248, -1), (key435, -1), (key661, 2), (key263, 2), (key445, 2), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1), (key347, -1), (key489, -1), (key278, -1), (key488, -1), (key277, -1), (key346, -1), (key421, -2), (key241, -2), (key411, -2), (key331, 1), (key453, 1), (key263, 1), (key445, 1), (key253, 1), (key321, 1)]

theorem rawRowCheck1067 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form5 = rawRow1067 := by decide +kernel

def row1067 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

theorem rowCheck1067 : row1067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1067 := by decide +kernel

theorem rowEval1067 (x : Key → ℝ) : Integer.Sparse.eval row1067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1067, Integer.Sparse.eval_collectBalanced, rawRowCheck1067]

def rawRow1068 : Integer.Sparse Key := [(key662, -1), (key660, -1), (key453, -1), (key253, -1), (key435, -1), (key248, -1), (key661, 2), (key445, 2), (key263, 2), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1), (key489, -1), (key347, -1), (key488, -1), (key278, -1), (key346, -1), (key277, -1), (key421, -2), (key411, -2), (key241, -2), (key453, 1), (key331, 1), (key445, 1), (key263, 1), (key321, 1), (key253, 1)]

theorem rawRowCheck1068 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form5 = rawRow1068 := by decide +kernel

def row1068 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

theorem rowCheck1068 : row1068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1068 := by decide +kernel

theorem rowEval1068 (x : Key → ℝ) : Integer.Sparse.eval row1068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1068, Integer.Sparse.eval_collectBalanced, rawRowCheck1068]

def rawRow1069 : Integer.Sparse Key := [(key253, -1), (key263, -1), (key321, -1), (key445, -1), (key331, -1), (key453, -1), (key248, 2), (key316, 2), (key435, 2), (key277, 1), (key278, 1), (key346, 1), (key488, 1), (key347, 1), (key489, 1), (key236, -1), (key248, -1), (key302, -1), (key316, -1), (key385, -1), (key406, -1), (key263, -2), (key400, -2), (key445, -2), (key241, 1), (key253, 1), (key307, 1), (key321, 1), (key390, 1), (key411, 1)]

theorem rawRowCheck1069 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form5 = rawRow1069 := by decide +kernel

def row1069 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

theorem rowCheck1069 : row1069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1069 := by decide +kernel

theorem rowEval1069 (x : Key → ℝ) : Integer.Sparse.eval row1069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1069, Integer.Sparse.eval_collectBalanced, rawRowCheck1069]

def rawRow1070 : Integer.Sparse Key := [(key263, -1), (key253, -1), (key445, -1), (key321, -1), (key453, -1), (key331, -1), (key248, 2), (key435, 2), (key316, 2), (key278, 1), (key277, 1), (key488, 1), (key346, 1), (key489, 1), (key347, 1), (key248, -1), (key236, -1), (key316, -1), (key302, -1), (key406, -1), (key385, -1), (key263, -2), (key445, -2), (key400, -2), (key253, 1), (key241, 1), (key321, 1), (key307, 1), (key411, 1), (key390, 1)]

theorem rawRowCheck1070 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form5 = rawRow1070 := by decide +kernel

def row1070 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

theorem rowCheck1070 : row1070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1070 := by decide +kernel

theorem rowEval1070 (x : Key → ℝ) : Integer.Sparse.eval row1070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1070, Integer.Sparse.eval_collectBalanced, rawRowCheck1070]

def rawRow1071 : Integer.Sparse Key := [(key321, -1), (key331, -1), (key253, -1), (key453, -1), (key263, -1), (key445, -1), (key316, 2), (key248, 2), (key435, 2), (key346, 1), (key347, 1), (key277, 1), (key489, 1), (key278, 1), (key488, 1), (key302, -1), (key316, -1), (key236, -1), (key406, -1), (key248, -1), (key316, -1), (key400, -2), (key263, -2), (key445, -2), (key307, 1), (key390, 1), (key241, 1), (key411, 1), (key253, 1), (key321, 1)]

theorem rawRowCheck1071 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form5 = rawRow1071 := by decide +kernel

def row1071 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key331, -1), (key346, 1), (key347, 1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

theorem rowCheck1071 : row1071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1071 := by decide +kernel

theorem rowEval1071 (x : Key → ℝ) : Integer.Sparse.eval row1071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1071, Integer.Sparse.eval_collectBalanced, rawRowCheck1071]

def rawRow1072 : Integer.Sparse Key := [(key331, -1), (key321, -1), (key453, -1), (key253, -1), (key445, -1), (key263, -1), (key316, 2), (key435, 2), (key248, 2), (key347, 1), (key346, 1), (key489, 1), (key277, 1), (key488, 1), (key278, 1), (key316, -1), (key302, -1), (key406, -1), (key236, -1), (key316, -1), (key248, -1), (key400, -2), (key445, -2), (key263, -2), (key390, 1), (key307, 1), (key411, 1), (key241, 1), (key321, 1), (key253, 1)]

theorem rawRowCheck1072 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form5 = rawRow1072 := by decide +kernel

def row1072 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key331, -1), (key346, 1), (key347, 1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

theorem rowCheck1072 : row1072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1072 := by decide +kernel

theorem rowEval1072 (x : Key → ℝ) : Integer.Sparse.eval row1072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1072, Integer.Sparse.eval_collectBalanced, rawRowCheck1072]

def rawRow1073 : Integer.Sparse Key := [(key445, -1), (key453, -1), (key263, -1), (key331, -1), (key253, -1), (key321, -1), (key435, 2), (key248, 2), (key316, 2), (key488, 1), (key489, 1), (key278, 1), (key347, 1), (key277, 1), (key346, 1), (key385, -1), (key406, -1), (key248, -1), (key316, -1), (key236, -1), (key302, -1), (key445, -2), (key263, -2), (key400, -2), (key321, 1), (key411, 1), (key253, 1), (key390, 1), (key241, 1), (key307, 1)]

theorem rawRowCheck1073 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form5 = rawRow1073 := by decide +kernel

def row1073 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

theorem rowCheck1073 : row1073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1073 := by decide +kernel

theorem rowEval1073 (x : Key → ℝ) : Integer.Sparse.eval row1073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1073, Integer.Sparse.eval_collectBalanced, rawRowCheck1073]

def rawRow1074 : Integer.Sparse Key := [(key453, -1), (key445, -1), (key331, -1), (key263, -1), (key321, -1), (key253, -1), (key435, 2), (key316, 2), (key248, 2), (key489, 1), (key488, 1), (key347, 1), (key278, 1), (key346, 1), (key277, 1), (key406, -1), (key385, -1), (key316, -1), (key248, -1), (key302, -1), (key236, -1), (key445, -2), (key400, -2), (key263, -2), (key411, 1), (key321, 1), (key390, 1), (key253, 1), (key307, 1), (key241, 1)]

theorem rawRowCheck1074 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form5 = rawRow1074 := by decide +kernel

def row1074 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

theorem rowCheck1074 : row1074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1074 := by decide +kernel

theorem rowEval1074 (x : Key → ℝ) : Integer.Sparse.eval row1074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1074, Integer.Sparse.eval_collectBalanced, rawRowCheck1074]

def rawRow1075 : Integer.Sparse Key := [(key277, -1), (key277, -1), (key487, -1), (key487, -1), (key489, -1), (key489, -1), (key278, 2), (key488, 2), (key488, 2), (key241, 1), (key241, 1), (key411, 1), (key411, 1), (key421, 1), (key421, 1), (key263, -1), (key263, -1), (key400, -1), (key400, -1), (key445, -1), (key445, -1), (key236, -2), (key406, -2), (key406, -2), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

theorem rawRowCheck1075 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form5 = rawRow1075 := by decide +kernel

def row1075 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

theorem rowCheck1075 : row1075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1075 := by decide +kernel

theorem rowEval1075 (x : Key → ℝ) : Integer.Sparse.eval row1075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1075, Integer.Sparse.eval_collectBalanced, rawRowCheck1075]

def rawRow1076 : Integer.Sparse Key := [(key487, -1), (key489, -1), (key277, -1), (key489, -1), (key277, -1), (key487, -1), (key488, 2), (key278, 2), (key488, 2), (key411, 1), (key421, 1), (key241, 1), (key421, 1), (key241, 1), (key411, 1), (key400, -1), (key445, -1), (key263, -1), (key445, -1), (key263, -1), (key400, -1), (key406, -2), (key236, -2), (key406, -2), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

theorem rawRowCheck1076 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form5 = rawRow1076 := by decide +kernel

def row1076 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

theorem rowCheck1076 : row1076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1076 := by decide +kernel

theorem rowEval1076 (x : Key → ℝ) : Integer.Sparse.eval row1076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1076, Integer.Sparse.eval_collectBalanced, rawRowCheck1076]

def rawRow1077 : Integer.Sparse Key := [(key489, -1), (key487, -1), (key489, -1), (key277, -1), (key487, -1), (key277, -1), (key488, 2), (key488, 2), (key278, 2), (key421, 1), (key411, 1), (key421, 1), (key241, 1), (key411, 1), (key241, 1), (key445, -1), (key400, -1), (key445, -1), (key263, -1), (key400, -1), (key263, -1), (key406, -2), (key406, -2), (key236, -2), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

theorem rawRowCheck1077 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form5 = rawRow1077 := by decide +kernel

def row1077 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

theorem rowCheck1077 : row1077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1077 := by decide +kernel

theorem rowEval1077 (x : Key → ℝ) : Integer.Sparse.eval row1077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1077, Integer.Sparse.eval_collectBalanced, rawRowCheck1077]

def rawRow1078 : Integer.Sparse Key := [(key277, -1), (key278, -1), (key346, -1), (key488, -1), (key347, -1), (key489, -1), (key277, 2), (key346, 2), (key487, 2), (key253, 1), (key263, 1), (key321, 1), (key445, 1), (key331, 1), (key453, 1), (key241, -1), (key253, -1), (key307, -1), (key390, -1), (key321, -1), (key411, -1), (key248, -2), (key316, -2), (key435, -2), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

theorem rawRowCheck1078 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form5 = rawRow1078 := by decide +kernel

def row1078 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

theorem rowCheck1078 : row1078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1078 := by decide +kernel

theorem rowEval1078 (x : Key → ℝ) : Integer.Sparse.eval row1078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1078, Integer.Sparse.eval_collectBalanced, rawRowCheck1078]

def rawRow1079 : Integer.Sparse Key := [(key278, -1), (key277, -1), (key488, -1), (key346, -1), (key489, -1), (key347, -1), (key277, 2), (key487, 2), (key346, 2), (key263, 1), (key253, 1), (key445, 1), (key321, 1), (key453, 1), (key331, 1), (key253, -1), (key241, -1), (key390, -1), (key307, -1), (key411, -1), (key321, -1), (key248, -2), (key435, -2), (key316, -2), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

theorem rawRowCheck1079 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form5 = rawRow1079 := by decide +kernel

def row1079 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

theorem rowCheck1079 : row1079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1079 := by decide +kernel

theorem rowEval1079 (x : Key → ℝ) : Integer.Sparse.eval row1079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1079, Integer.Sparse.eval_collectBalanced, rawRowCheck1079]

def rawRow1080 : Integer.Sparse Key := [(key346, -1), (key347, -1), (key277, -1), (key489, -1), (key278, -1), (key488, -1), (key346, 2), (key277, 2), (key487, 2), (key321, 1), (key331, 1), (key253, 1), (key453, 1), (key263, 1), (key445, 1), (key307, -1), (key321, -1), (key241, -1), (key411, -1), (key253, -1), (key390, -1), (key316, -2), (key248, -2), (key435, -2), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

theorem rawRowCheck1080 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form5 = rawRow1080 := by decide +kernel

def row1080 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key331, 1), (key346, 1), (key347, -1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

theorem rowCheck1080 : row1080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1080 := by decide +kernel

theorem rowEval1080 (x : Key → ℝ) : Integer.Sparse.eval row1080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1080, Integer.Sparse.eval_collectBalanced, rawRowCheck1080]

def rawRow1081 : Integer.Sparse Key := [(key347, -1), (key346, -1), (key489, -1), (key277, -1), (key488, -1), (key278, -1), (key346, 2), (key487, 2), (key277, 2), (key331, 1), (key321, 1), (key453, 1), (key253, 1), (key445, 1), (key263, 1), (key321, -1), (key307, -1), (key411, -1), (key241, -1), (key390, -1), (key253, -1), (key316, -2), (key435, -2), (key248, -2), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

theorem rawRowCheck1081 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form5 = rawRow1081 := by decide +kernel

def row1081 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key331, 1), (key346, 1), (key347, -1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

theorem rowCheck1081 : row1081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1081 := by decide +kernel

theorem rowEval1081 (x : Key → ℝ) : Integer.Sparse.eval row1081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1081, Integer.Sparse.eval_collectBalanced, rawRowCheck1081]

def rawRow1082 : Integer.Sparse Key := [(key488, -1), (key489, -1), (key278, -1), (key347, -1), (key277, -1), (key346, -1), (key487, 2), (key277, 2), (key346, 2), (key445, 1), (key453, 1), (key263, 1), (key331, 1), (key253, 1), (key321, 1), (key390, -1), (key411, -1), (key253, -1), (key321, -1), (key241, -1), (key307, -1), (key435, -2), (key248, -2), (key316, -2), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

theorem rawRowCheck1082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form5 = rawRow1082 := by decide +kernel

def row1082 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

theorem rowCheck1082 : row1082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1082 := by decide +kernel

theorem rowEval1082 (x : Key → ℝ) : Integer.Sparse.eval row1082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1082, Integer.Sparse.eval_collectBalanced, rawRowCheck1082]

def rawRow1083 : Integer.Sparse Key := [(key489, -1), (key488, -1), (key347, -1), (key278, -1), (key346, -1), (key277, -1), (key487, 2), (key346, 2), (key277, 2), (key453, 1), (key445, 1), (key331, 1), (key263, 1), (key321, 1), (key253, 1), (key411, -1), (key390, -1), (key321, -1), (key253, -1), (key307, -1), (key241, -1), (key435, -2), (key316, -2), (key248, -2), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

theorem rawRowCheck1083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form5 = rawRow1083 := by decide +kernel

def row1083 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

theorem rowCheck1083 : row1083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1083 := by decide +kernel

theorem rowEval1083 (x : Key → ℝ) : Integer.Sparse.eval row1083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1083, Integer.Sparse.eval_collectBalanced, rawRowCheck1083]

def rawRow1084 : Integer.Sparse Key := [(key2693, -2), (key3055, -2), (key3117, -2), (key3051, 1), (key3057, 1), (key3051, 1), (key3112, 1), (key3057, 1), (key3112, 1), (key3070, 2), (key3070, 2), (key3147, 2), (key3051, -1), (key3074, -1), (key3051, -1), (key3112, -1), (key3074, -1), (key3112, -1), (key3070, -1), (key3077, -1), (key3070, -1), (key3147, -1), (key3077, -1), (key3147, -1), (key3055, 1), (key3078, 1), (key3055, 1), (key3117, 1), (key3078, 1), (key3117, 1)]

theorem rawRowCheck1084 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form0 = rawRow1084 := by decide +kernel

def row1084 : Integer.Sparse Key := [(key2693, -2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2)]

theorem rowCheck1084 : row1084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1084 := by decide +kernel

theorem rowEval1084 (x : Key → ℝ) : Integer.Sparse.eval row1084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, -1, 2] GramFunctions.Block1.form0) x := by
  rw [rowCheck1084, Integer.Sparse.eval_collectBalanced, rawRowCheck1084]

def rawRow1085 : Integer.Sparse Key := [(key2693, -2), (key3117, -2), (key3055, -2), (key3057, 1), (key3051, 1), (key3112, 1), (key3051, 1), (key3112, 1), (key3057, 1), (key3070, 2), (key3147, 2), (key3070, 2), (key3074, -1), (key3051, -1), (key3112, -1), (key3051, -1), (key3112, -1), (key3074, -1), (key3077, -1), (key3070, -1), (key3147, -1), (key3070, -1), (key3147, -1), (key3077, -1), (key3078, 1), (key3055, 1), (key3117, 1), (key3055, 1), (key3117, 1), (key3078, 1)]

theorem rawRowCheck1085 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form0 = rawRow1085 := by decide +kernel

def row1085 : Integer.Sparse Key := [(key2693, -2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2)]

theorem rowCheck1085 : row1085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1085 := by decide +kernel

theorem rowEval1085 (x : Key → ℝ) : Integer.Sparse.eval row1085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -1, 2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1085, Integer.Sparse.eval_collectBalanced, rawRowCheck1085]

def rawRow1086 : Integer.Sparse Key := [(key3018, -2), (key2693, -2), (key2693, -2), (key3112, 1), (key3112, 1), (key3057, 1), (key3057, 1), (key3051, 1), (key3051, 1), (key3147, 2), (key3070, 2), (key3070, 2), (key3112, -1), (key3112, -1), (key3074, -1), (key3074, -1), (key3051, -1), (key3051, -1), (key3147, -1), (key3147, -1), (key3077, -1), (key3077, -1), (key3070, -1), (key3070, -1), (key3117, 1), (key3117, 1), (key3078, 1), (key3078, 1), (key3055, 1), (key3055, 1)]

theorem rawRowCheck1086 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form0 = rawRow1086 := by decide +kernel

def row1086 : Integer.Sparse Key := [(key2693, -4), (key3018, -2), (key3055, 2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2), (key3117, 2)]

theorem rowCheck1086 : row1086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1086 := by decide +kernel

theorem rowEval1086 (x : Key → ℝ) : Integer.Sparse.eval row1086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1086, Integer.Sparse.eval_collectBalanced, rawRowCheck1086]

def rawRow1087 : Integer.Sparse Key := [(key2695, -2), (key2695, -2), (key2836, -2), (key2686, 1), (key2693, 1), (key2686, 1), (key2822, 1), (key2693, 1), (key2822, 1), (key3074, 2), (key3074, 2), (key3146, 2), (key3051, -1), (key3070, -1), (key3051, -1), (key3107, -1), (key3070, -1), (key3107, -1), (key3074, -1), (key3078, -1), (key3074, -1), (key3146, -1), (key3078, -1), (key3146, -1), (key3057, 1), (key3077, 1), (key3057, 1), (key3116, 1), (key3077, 1), (key3116, 1)]

theorem rawRowCheck1087 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form0 = rawRow1087 := by decide +kernel

def row1087 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

theorem rowCheck1087 : row1087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1087 := by decide +kernel

theorem rowEval1087 (x : Key → ℝ) : Integer.Sparse.eval row1087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1087, Integer.Sparse.eval_collectBalanced, rawRowCheck1087]

end MUB6.Certificate.GramRows

end OAI
