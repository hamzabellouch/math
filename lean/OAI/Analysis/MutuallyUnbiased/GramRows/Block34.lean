import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
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

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1280 : Integer.Sparse Key := [(key347, -1), (key331, -1), (key346, -1), (key307, -1), (key316, -1), (key302, -1), (key331, 2), (key321, 2), (key307, 2), (key489, 1), (key453, 1), (key487, 1), (key390, 1), (key435, 1), (key385, 1), (key453, -1), (key421, -1), (key445, -1), (key400, -1), (key411, -1), (key390, -1), (key662, -2), (key660, -2), (key655, -2), (key662, 1), (key658, 1), (key661, 1), (key656, 1), (key657, 1), (key655, 1)]

theorem rawRowCheck1280 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form5 = rawRow1280 := by decide +kernel

def row1280 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

theorem rowCheck1280 : row1280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1280 := by decide +kernel

theorem rowEval1280 (x : Key → ℝ) : Integer.Sparse.eval row1280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1280, Integer.Sparse.eval_collectBalanced, rawRowCheck1280]

def rawRow1281 : Integer.Sparse Key := [(key406, -1), (key411, -1), (key406, -1), (key421, -1), (key411, -1), (key421, -1), (key657, 2), (key657, 2), (key658, 2), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1), (key660, -1), (key661, -1), (key660, -1), (key662, -1), (key661, -1), (key662, -1), (key346, -2), (key346, -2), (key347, -2), (key487, 1), (key488, 1), (key487, 1), (key489, 1), (key488, 1), (key489, 1)]

theorem rawRowCheck1281 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form5 = rawRow1281 := by decide +kernel

def row1281 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

theorem rowCheck1281 : row1281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1281 := by decide +kernel

theorem rowEval1281 (x : Key → ℝ) : Integer.Sparse.eval row1281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1281, Integer.Sparse.eval_collectBalanced, rawRowCheck1281]

def rawRow1282 : Integer.Sparse Key := [(key411, -1), (key406, -1), (key421, -1), (key406, -1), (key421, -1), (key411, -1), (key657, 2), (key658, 2), (key657, 2), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1), (key661, -1), (key660, -1), (key662, -1), (key660, -1), (key662, -1), (key661, -1), (key346, -2), (key347, -2), (key346, -2), (key488, 1), (key487, 1), (key489, 1), (key487, 1), (key489, 1), (key488, 1)]

theorem rawRowCheck1282 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form5 = rawRow1282 := by decide +kernel

def row1282 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

theorem rowCheck1282 : row1282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1282 := by decide +kernel

theorem rowEval1282 (x : Key → ℝ) : Integer.Sparse.eval row1282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1282, Integer.Sparse.eval_collectBalanced, rawRowCheck1282]

def rawRow1283 : Integer.Sparse Key := [(key421, -1), (key421, -1), (key411, -1), (key411, -1), (key406, -1), (key406, -1), (key658, 2), (key657, 2), (key657, 2), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key662, -1), (key662, -1), (key661, -1), (key661, -1), (key660, -1), (key660, -1), (key347, -2), (key346, -2), (key346, -2), (key489, 1), (key489, 1), (key488, 1), (key488, 1), (key487, 1), (key487, 1)]

theorem rawRowCheck1283 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form5 = rawRow1283 := by decide +kernel

def row1283 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

theorem rowCheck1283 : row1283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1283 := by decide +kernel

theorem rowEval1283 (x : Key → ℝ) : Integer.Sparse.eval row1283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1283, Integer.Sparse.eval_collectBalanced, rawRowCheck1283]

def rawRow1284 : Integer.Sparse Key := [(key316, -1), (key321, -1), (key435, -1), (key660, -1), (key445, -1), (key661, -1), (key331, 2), (key453, 2), (key662, 2), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key661, -1), (key662, -1), (key307, -2), (key321, -2), (key331, -2), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key445, 1), (key453, 1)]

theorem rawRowCheck1284 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form5 = rawRow1284 := by decide +kernel

def row1284 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

theorem rowCheck1284 : row1284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1284 := by decide +kernel

theorem rowEval1284 (x : Key → ℝ) : Integer.Sparse.eval row1284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1284, Integer.Sparse.eval_collectBalanced, rawRowCheck1284]

def rawRow1285 : Integer.Sparse Key := [(key321, -1), (key316, -1), (key660, -1), (key435, -1), (key661, -1), (key445, -1), (key331, 2), (key662, 2), (key453, 2), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1), (key656, -1), (key655, -1), (key658, -1), (key657, -1), (key662, -1), (key661, -1), (key307, -2), (key331, -2), (key321, -2), (key400, 1), (key390, 1), (key421, 1), (key411, 1), (key453, 1), (key445, 1)]

theorem rawRowCheck1285 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form5 = rawRow1285 := by decide +kernel

def row1285 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

theorem rowCheck1285 : row1285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1285 := by decide +kernel

theorem rowEval1285 (x : Key → ℝ) : Integer.Sparse.eval row1285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1285, Integer.Sparse.eval_collectBalanced, rawRowCheck1285]

def rawRow1286 : Integer.Sparse Key := [(key435, -1), (key445, -1), (key316, -1), (key661, -1), (key321, -1), (key660, -1), (key453, 2), (key331, 2), (key662, 2), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1), (key657, -1), (key661, -1), (key655, -1), (key662, -1), (key656, -1), (key658, -1), (key321, -2), (key307, -2), (key331, -2), (key411, 1), (key445, 1), (key390, 1), (key453, 1), (key400, 1), (key421, 1)]

theorem rawRowCheck1286 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form5 = rawRow1286 := by decide +kernel

def row1286 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

theorem rowCheck1286 : row1286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1286 := by decide +kernel

theorem rowEval1286 (x : Key → ℝ) : Integer.Sparse.eval row1286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck1286, Integer.Sparse.eval_collectBalanced, rawRowCheck1286]

def rawRow1287 : Integer.Sparse Key := [(key445, -1), (key435, -1), (key661, -1), (key316, -1), (key660, -1), (key321, -1), (key453, 2), (key662, 2), (key331, 2), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1), (key661, -1), (key657, -1), (key662, -1), (key655, -1), (key658, -1), (key656, -1), (key321, -2), (key331, -2), (key307, -2), (key445, 1), (key411, 1), (key453, 1), (key390, 1), (key421, 1), (key400, 1)]

theorem rawRowCheck1287 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form5 = rawRow1287 := by decide +kernel

def row1287 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

theorem rowCheck1287 : row1287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1287 := by decide +kernel

theorem rowEval1287 (x : Key → ℝ) : Integer.Sparse.eval row1287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1287, Integer.Sparse.eval_collectBalanced, rawRowCheck1287]

def rawRow1288 : Integer.Sparse Key := [(key660, -1), (key661, -1), (key321, -1), (key445, -1), (key316, -1), (key435, -1), (key662, 2), (key331, 2), (key453, 2), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1), (key658, -1), (key662, -1), (key656, -1), (key661, -1), (key655, -1), (key657, -1), (key331, -2), (key307, -2), (key321, -2), (key421, 1), (key453, 1), (key400, 1), (key445, 1), (key390, 1), (key411, 1)]

theorem rawRowCheck1288 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form5 = rawRow1288 := by decide +kernel

def row1288 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

theorem rowCheck1288 : row1288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1288 := by decide +kernel

theorem rowEval1288 (x : Key → ℝ) : Integer.Sparse.eval row1288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form5) x := by
  rw [rowCheck1288, Integer.Sparse.eval_collectBalanced, rawRowCheck1288]

def rawRow1289 : Integer.Sparse Key := [(key661, -1), (key660, -1), (key445, -1), (key321, -1), (key435, -1), (key316, -1), (key662, 2), (key453, 2), (key331, 2), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1), (key662, -1), (key658, -1), (key661, -1), (key656, -1), (key657, -1), (key655, -1), (key331, -2), (key321, -2), (key307, -2), (key453, 1), (key421, 1), (key445, 1), (key400, 1), (key411, 1), (key390, 1)]

theorem rawRowCheck1289 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form5 = rawRow1289 := by decide +kernel

def row1289 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

theorem rowCheck1289 : row1289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1289 := by decide +kernel

theorem rowEval1289 (x : Key → ℝ) : Integer.Sparse.eval row1289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form5) x := by
  rw [rowCheck1289, Integer.Sparse.eval_collectBalanced, rawRowCheck1289]

def rawRow1290 : Integer.Sparse Key := [(key1433, -2), (key1439, -2), (key1439, -2), (key1477, 2), (key1479, 2), (key1479, 2), (key1582, 2), (key1588, 2), (key1588, 2), (key1688, -6), (key1908, -2), (key1910, -2), (key1910, -2), (key1925, 6)]

theorem rawRowCheck1290 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1290 := by decide +kernel

def row1290 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

theorem rowCheck1290 : row1290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1290 := by decide +kernel

theorem rowEval1290 (x : Key → ℝ) : Integer.Sparse.eval row1290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1290, Integer.Sparse.eval_collectBalanced, rawRowCheck1290]

def rawRow1291 : Integer.Sparse Key := [(key1439, -2), (key1433, -2), (key1439, -2), (key1479, 2), (key1477, 2), (key1479, 2), (key1588, 2), (key1582, 2), (key1588, 2), (key1688, -6), (key1910, -2), (key1908, -2), (key1910, -2), (key1925, 6)]

theorem rawRowCheck1291 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1291 := by decide +kernel

def row1291 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

theorem rowCheck1291 : row1291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1291 := by decide +kernel

theorem rowEval1291 (x : Key → ℝ) : Integer.Sparse.eval row1291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1291, Integer.Sparse.eval_collectBalanced, rawRowCheck1291]

def rawRow1292 : Integer.Sparse Key := [(key1439, -2), (key1439, -2), (key1433, -2), (key1479, 2), (key1479, 2), (key1477, 2), (key1588, 2), (key1588, 2), (key1582, 2), (key1688, -6), (key1910, -2), (key1910, -2), (key1908, -2), (key1925, 6)]

theorem rawRowCheck1292 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1292 := by decide +kernel

def row1292 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

theorem rowCheck1292 : row1292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1292 := by decide +kernel

theorem rowEval1292 (x : Key → ℝ) : Integer.Sparse.eval row1292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1292, Integer.Sparse.eval_collectBalanced, rawRowCheck1292]

def rawRow1293 : Integer.Sparse Key := [(key1405, -2), (key1414, -2), (key1479, -2), (key1410, 2), (key1414, 2), (key1439, 2), (key1582, 2), (key1588, 2), (key1688, 2), (key1588, -6), (key1908, -2), (key1910, -2), (key1925, -2), (key1910, 6)]

theorem rawRowCheck1293 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form6 = rawRow1293 := by decide +kernel

def row1293 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

theorem rowCheck1293 : row1293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1293 := by decide +kernel

theorem rowEval1293 (x : Key → ℝ) : Integer.Sparse.eval row1293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1293, Integer.Sparse.eval_collectBalanced, rawRowCheck1293]

def rawRow1294 : Integer.Sparse Key := [(key1414, -2), (key1405, -2), (key1479, -2), (key1414, 2), (key1410, 2), (key1439, 2), (key1588, 2), (key1582, 2), (key1688, 2), (key1588, -6), (key1910, -2), (key1908, -2), (key1925, -2), (key1910, 6)]

theorem rawRowCheck1294 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form6 = rawRow1294 := by decide +kernel

def row1294 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

theorem rowCheck1294 : row1294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1294 := by decide +kernel

theorem rowEval1294 (x : Key → ℝ) : Integer.Sparse.eval row1294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1294, Integer.Sparse.eval_collectBalanced, rawRowCheck1294]

def rawRow1295 : Integer.Sparse Key := [(key1405, -2), (key1479, -2), (key1414, -2), (key1410, 2), (key1439, 2), (key1414, 2), (key1582, 2), (key1688, 2), (key1588, 2), (key1588, -6), (key1908, -2), (key1925, -2), (key1910, -2), (key1910, 6)]

theorem rawRowCheck1295 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form6 = rawRow1295 := by decide +kernel

def row1295 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

theorem rowCheck1295 : row1295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1295 := by decide +kernel

theorem rowEval1295 (x : Key → ℝ) : Integer.Sparse.eval row1295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1295, Integer.Sparse.eval_collectBalanced, rawRowCheck1295]

def rawRow1296 : Integer.Sparse Key := [(key1479, -2), (key1405, -2), (key1414, -2), (key1439, 2), (key1410, 2), (key1414, 2), (key1688, 2), (key1582, 2), (key1588, 2), (key1588, -6), (key1925, -2), (key1908, -2), (key1910, -2), (key1910, 6)]

theorem rawRowCheck1296 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form6 = rawRow1296 := by decide +kernel

def row1296 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

theorem rowCheck1296 : row1296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1296 := by decide +kernel

theorem rowEval1296 (x : Key → ℝ) : Integer.Sparse.eval row1296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1296, Integer.Sparse.eval_collectBalanced, rawRowCheck1296]

def rawRow1297 : Integer.Sparse Key := [(key1414, -2), (key1479, -2), (key1405, -2), (key1414, 2), (key1439, 2), (key1410, 2), (key1588, 2), (key1688, 2), (key1582, 2), (key1588, -6), (key1910, -2), (key1925, -2), (key1908, -2), (key1910, 6)]

theorem rawRowCheck1297 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form6 = rawRow1297 := by decide +kernel

def row1297 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

theorem rowCheck1297 : row1297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1297 := by decide +kernel

theorem rowEval1297 (x : Key → ℝ) : Integer.Sparse.eval row1297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1297, Integer.Sparse.eval_collectBalanced, rawRowCheck1297]

def rawRow1298 : Integer.Sparse Key := [(key1479, -2), (key1414, -2), (key1405, -2), (key1439, 2), (key1414, 2), (key1410, 2), (key1688, 2), (key1588, 2), (key1582, 2), (key1588, -6), (key1925, -2), (key1910, -2), (key1908, -2), (key1910, 6)]

theorem rawRowCheck1298 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form6 = rawRow1298 := by decide +kernel

def row1298 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1439, 2), (key1479, -2), (key1582, 2), (key1588, -4), (key1688, 2), (key1908, -2), (key1910, 4), (key1925, -2)]

theorem rowCheck1298 : row1298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1298 := by decide +kernel

theorem rowEval1298 (x : Key → ℝ) : Integer.Sparse.eval row1298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1298, Integer.Sparse.eval_collectBalanced, rawRowCheck1298]

def rawRow1299 : Integer.Sparse Key := [(key1582, -2), (key1588, -2), (key1588, -2), (key1908, 2), (key1910, 2), (key1910, 2), (key1433, 2), (key1439, 2), (key1439, 2), (key1925, -6), (key1477, -2), (key1479, -2), (key1479, -2), (key1688, 6)]

theorem rawRowCheck1299 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form6 = rawRow1299 := by decide +kernel

def row1299 : Integer.Sparse Key := [(key1433, 2), (key1439, 4), (key1477, -2), (key1479, -4), (key1582, -2), (key1588, -4), (key1688, 6), (key1908, 2), (key1910, 4), (key1925, -6)]

theorem rowCheck1299 : row1299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1299 := by decide +kernel

theorem rowEval1299 (x : Key → ℝ) : Integer.Sparse.eval row1299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1299, Integer.Sparse.eval_collectBalanced, rawRowCheck1299]

def rawRow1300 : Integer.Sparse Key := [(key1588, -2), (key1582, -2), (key1588, -2), (key1910, 2), (key1908, 2), (key1910, 2), (key1439, 2), (key1433, 2), (key1439, 2), (key1925, -6), (key1479, -2), (key1477, -2), (key1479, -2), (key1688, 6)]

theorem rawRowCheck1300 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form6 = rawRow1300 := by decide +kernel

def row1300 : Integer.Sparse Key := [(key1433, 2), (key1439, 4), (key1477, -2), (key1479, -4), (key1582, -2), (key1588, -4), (key1688, 6), (key1908, 2), (key1910, 4), (key1925, -6)]

theorem rowCheck1300 : row1300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1300 := by decide +kernel

theorem rowEval1300 (x : Key → ℝ) : Integer.Sparse.eval row1300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1300, Integer.Sparse.eval_collectBalanced, rawRowCheck1300]

def rawRow1301 : Integer.Sparse Key := [(key1588, -2), (key1588, -2), (key1582, -2), (key1910, 2), (key1910, 2), (key1908, 2), (key1439, 2), (key1439, 2), (key1433, 2), (key1925, -6), (key1479, -2), (key1479, -2), (key1477, -2), (key1688, 6)]

theorem rawRowCheck1301 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form6 = rawRow1301 := by decide +kernel

def row1301 : Integer.Sparse Key := [(key1433, 2), (key1439, 4), (key1477, -2), (key1479, -4), (key1582, -2), (key1588, -4), (key1688, 6), (key1908, 2), (key1910, 4), (key1925, -6)]

theorem rowCheck1301 : row1301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1301 := by decide +kernel

theorem rowEval1301 (x : Key → ℝ) : Integer.Sparse.eval row1301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1301, Integer.Sparse.eval_collectBalanced, rawRowCheck1301]

def rawRow1302 : Integer.Sparse Key := [(key1405, -2), (key1414, -2), (key1910, -2), (key1410, 2), (key1414, 2), (key1588, 2), (key1433, 2), (key1439, 2), (key1925, 2), (key1439, -6), (key1477, -2), (key1479, -2), (key1688, -2), (key1479, 6)]

theorem rawRowCheck1302 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form6 = rawRow1302 := by decide +kernel

def row1302 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

theorem rowCheck1302 : row1302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1302 := by decide +kernel

theorem rowEval1302 (x : Key → ℝ) : Integer.Sparse.eval row1302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1302, Integer.Sparse.eval_collectBalanced, rawRowCheck1302]

def rawRow1303 : Integer.Sparse Key := [(key1414, -2), (key1405, -2), (key1910, -2), (key1414, 2), (key1410, 2), (key1588, 2), (key1439, 2), (key1433, 2), (key1925, 2), (key1439, -6), (key1479, -2), (key1477, -2), (key1688, -2), (key1479, 6)]

theorem rawRowCheck1303 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form6 = rawRow1303 := by decide +kernel

def row1303 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

theorem rowCheck1303 : row1303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1303 := by decide +kernel

theorem rowEval1303 (x : Key → ℝ) : Integer.Sparse.eval row1303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1303, Integer.Sparse.eval_collectBalanced, rawRowCheck1303]

def rawRow1304 : Integer.Sparse Key := [(key1405, -2), (key1910, -2), (key1414, -2), (key1410, 2), (key1588, 2), (key1414, 2), (key1433, 2), (key1925, 2), (key1439, 2), (key1439, -6), (key1477, -2), (key1688, -2), (key1479, -2), (key1479, 6)]

theorem rawRowCheck1304 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form6 = rawRow1304 := by decide +kernel

def row1304 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

theorem rowCheck1304 : row1304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1304 := by decide +kernel

theorem rowEval1304 (x : Key → ℝ) : Integer.Sparse.eval row1304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1304, Integer.Sparse.eval_collectBalanced, rawRowCheck1304]

def rawRow1305 : Integer.Sparse Key := [(key1910, -2), (key1405, -2), (key1414, -2), (key1588, 2), (key1410, 2), (key1414, 2), (key1925, 2), (key1433, 2), (key1439, 2), (key1439, -6), (key1688, -2), (key1477, -2), (key1479, -2), (key1479, 6)]

theorem rawRowCheck1305 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form6 = rawRow1305 := by decide +kernel

def row1305 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

theorem rowCheck1305 : row1305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1305 := by decide +kernel

theorem rowEval1305 (x : Key → ℝ) : Integer.Sparse.eval row1305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1305, Integer.Sparse.eval_collectBalanced, rawRowCheck1305]

def rawRow1306 : Integer.Sparse Key := [(key1414, -2), (key1910, -2), (key1405, -2), (key1414, 2), (key1588, 2), (key1410, 2), (key1439, 2), (key1925, 2), (key1433, 2), (key1439, -6), (key1479, -2), (key1688, -2), (key1477, -2), (key1479, 6)]

theorem rawRowCheck1306 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form6 = rawRow1306 := by decide +kernel

def row1306 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

theorem rowCheck1306 : row1306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1306 := by decide +kernel

theorem rowEval1306 (x : Key → ℝ) : Integer.Sparse.eval row1306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1306, Integer.Sparse.eval_collectBalanced, rawRowCheck1306]

def rawRow1307 : Integer.Sparse Key := [(key1910, -2), (key1414, -2), (key1405, -2), (key1588, 2), (key1414, 2), (key1410, 2), (key1925, 2), (key1439, 2), (key1433, 2), (key1439, -6), (key1688, -2), (key1479, -2), (key1477, -2), (key1479, 6)]

theorem rawRowCheck1307 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form6 = rawRow1307 := by decide +kernel

def row1307 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -4), (key1477, -2), (key1479, 4), (key1588, 2), (key1688, -2), (key1910, -2), (key1925, 2)]

theorem rowCheck1307 : row1307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1307 := by decide +kernel

theorem rowEval1307 (x : Key → ℝ) : Integer.Sparse.eval row1307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1307, Integer.Sparse.eval_collectBalanced, rawRowCheck1307]

def rawRow1308 : Integer.Sparse Key := [(key1582, -2), (key1588, -2), (key1688, -2), (key1908, 2), (key1910, 2), (key1925, 2), (key1405, 2), (key1414, 2), (key1479, 2), (key1910, -6), (key1410, -2), (key1414, -2), (key1439, -2), (key1588, 6)]

theorem rawRowCheck1308 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form6 = rawRow1308 := by decide +kernel

def row1308 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

theorem rowCheck1308 : row1308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1308 := by decide +kernel

theorem rowEval1308 (x : Key → ℝ) : Integer.Sparse.eval row1308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1308, Integer.Sparse.eval_collectBalanced, rawRowCheck1308]

def rawRow1309 : Integer.Sparse Key := [(key1588, -2), (key1582, -2), (key1688, -2), (key1910, 2), (key1908, 2), (key1925, 2), (key1414, 2), (key1405, 2), (key1479, 2), (key1910, -6), (key1414, -2), (key1410, -2), (key1439, -2), (key1588, 6)]

theorem rawRowCheck1309 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form6 = rawRow1309 := by decide +kernel

def row1309 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

theorem rowCheck1309 : row1309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1309 := by decide +kernel

theorem rowEval1309 (x : Key → ℝ) : Integer.Sparse.eval row1309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1309, Integer.Sparse.eval_collectBalanced, rawRowCheck1309]

def rawRow1310 : Integer.Sparse Key := [(key1582, -2), (key1688, -2), (key1588, -2), (key1908, 2), (key1925, 2), (key1910, 2), (key1405, 2), (key1479, 2), (key1414, 2), (key1910, -6), (key1410, -2), (key1439, -2), (key1414, -2), (key1588, 6)]

theorem rawRowCheck1310 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form6 = rawRow1310 := by decide +kernel

def row1310 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

theorem rowCheck1310 : row1310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1310 := by decide +kernel

theorem rowEval1310 (x : Key → ℝ) : Integer.Sparse.eval row1310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1310, Integer.Sparse.eval_collectBalanced, rawRowCheck1310]

def rawRow1311 : Integer.Sparse Key := [(key1688, -2), (key1582, -2), (key1588, -2), (key1925, 2), (key1908, 2), (key1910, 2), (key1479, 2), (key1405, 2), (key1414, 2), (key1910, -6), (key1439, -2), (key1410, -2), (key1414, -2), (key1588, 6)]

theorem rawRowCheck1311 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form6 = rawRow1311 := by decide +kernel

def row1311 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

theorem rowCheck1311 : row1311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1311 := by decide +kernel

theorem rowEval1311 (x : Key → ℝ) : Integer.Sparse.eval row1311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1311, Integer.Sparse.eval_collectBalanced, rawRowCheck1311]

def rawRow1312 : Integer.Sparse Key := [(key1588, -2), (key1688, -2), (key1582, -2), (key1910, 2), (key1925, 2), (key1908, 2), (key1414, 2), (key1479, 2), (key1405, 2), (key1910, -6), (key1414, -2), (key1439, -2), (key1410, -2), (key1588, 6)]

theorem rawRowCheck1312 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form6 = rawRow1312 := by decide +kernel

def row1312 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

theorem rowCheck1312 : row1312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1312 := by decide +kernel

theorem rowEval1312 (x : Key → ℝ) : Integer.Sparse.eval row1312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1312, Integer.Sparse.eval_collectBalanced, rawRowCheck1312]

def rawRow1313 : Integer.Sparse Key := [(key1688, -2), (key1588, -2), (key1582, -2), (key1925, 2), (key1910, 2), (key1908, 2), (key1479, 2), (key1414, 2), (key1405, 2), (key1910, -6), (key1439, -2), (key1414, -2), (key1410, -2), (key1588, 6)]

theorem rawRowCheck1313 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form6 = rawRow1313 := by decide +kernel

def row1313 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1439, -2), (key1479, 2), (key1582, -2), (key1588, 4), (key1688, -2), (key1908, 2), (key1910, -4), (key1925, 2)]

theorem rowCheck1313 : row1313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1313 := by decide +kernel

theorem rowEval1313 (x : Key → ℝ) : Integer.Sparse.eval row1313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form6) x := by
  rw [rowCheck1313, Integer.Sparse.eval_collectBalanced, rawRowCheck1313]

def rawRow1314 : Integer.Sparse Key := [(key1433, -2), (key1439, -2), (key1925, -2), (key1477, 2), (key1479, 2), (key1688, 2), (key1405, 2), (key1414, 2), (key1910, 2), (key1479, -6), (key1410, -2), (key1414, -2), (key1588, -2), (key1439, 6)]

theorem rawRowCheck1314 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form6 = rawRow1314 := by decide +kernel

def row1314 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

theorem rowCheck1314 : row1314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1314 := by decide +kernel

theorem rowEval1314 (x : Key → ℝ) : Integer.Sparse.eval row1314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1314, Integer.Sparse.eval_collectBalanced, rawRowCheck1314]

def rawRow1315 : Integer.Sparse Key := [(key1439, -2), (key1433, -2), (key1925, -2), (key1479, 2), (key1477, 2), (key1688, 2), (key1414, 2), (key1405, 2), (key1910, 2), (key1479, -6), (key1414, -2), (key1410, -2), (key1588, -2), (key1439, 6)]

theorem rawRowCheck1315 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form6 = rawRow1315 := by decide +kernel

def row1315 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

theorem rowCheck1315 : row1315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1315 := by decide +kernel

theorem rowEval1315 (x : Key → ℝ) : Integer.Sparse.eval row1315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1315, Integer.Sparse.eval_collectBalanced, rawRowCheck1315]

def rawRow1316 : Integer.Sparse Key := [(key1433, -2), (key1925, -2), (key1439, -2), (key1477, 2), (key1688, 2), (key1479, 2), (key1405, 2), (key1910, 2), (key1414, 2), (key1479, -6), (key1410, -2), (key1588, -2), (key1414, -2), (key1439, 6)]

theorem rawRowCheck1316 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form6 = rawRow1316 := by decide +kernel

def row1316 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

theorem rowCheck1316 : row1316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1316 := by decide +kernel

theorem rowEval1316 (x : Key → ℝ) : Integer.Sparse.eval row1316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1316, Integer.Sparse.eval_collectBalanced, rawRowCheck1316]

def rawRow1317 : Integer.Sparse Key := [(key1925, -2), (key1433, -2), (key1439, -2), (key1688, 2), (key1477, 2), (key1479, 2), (key1910, 2), (key1405, 2), (key1414, 2), (key1479, -6), (key1588, -2), (key1410, -2), (key1414, -2), (key1439, 6)]

theorem rawRowCheck1317 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form6 = rawRow1317 := by decide +kernel

def row1317 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

theorem rowCheck1317 : row1317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1317 := by decide +kernel

theorem rowEval1317 (x : Key → ℝ) : Integer.Sparse.eval row1317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1317, Integer.Sparse.eval_collectBalanced, rawRowCheck1317]

def rawRow1318 : Integer.Sparse Key := [(key1439, -2), (key1925, -2), (key1433, -2), (key1479, 2), (key1688, 2), (key1477, 2), (key1414, 2), (key1910, 2), (key1405, 2), (key1479, -6), (key1414, -2), (key1588, -2), (key1410, -2), (key1439, 6)]

theorem rawRowCheck1318 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form6 = rawRow1318 := by decide +kernel

def row1318 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

theorem rowCheck1318 : row1318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1318 := by decide +kernel

theorem rowEval1318 (x : Key → ℝ) : Integer.Sparse.eval row1318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1318, Integer.Sparse.eval_collectBalanced, rawRowCheck1318]

def rawRow1319 : Integer.Sparse Key := [(key1925, -2), (key1439, -2), (key1433, -2), (key1688, 2), (key1479, 2), (key1477, 2), (key1910, 2), (key1414, 2), (key1405, 2), (key1479, -6), (key1588, -2), (key1414, -2), (key1410, -2), (key1439, 6)]

theorem rawRowCheck1319 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form6 = rawRow1319 := by decide +kernel

def row1319 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 4), (key1477, 2), (key1479, -4), (key1588, -2), (key1688, 2), (key1910, 2), (key1925, -2)]

theorem rowCheck1319 : row1319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1319 := by decide +kernel

theorem rowEval1319 (x : Key → ℝ) : Integer.Sparse.eval row1319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form6) x := by
  rw [rowCheck1319, Integer.Sparse.eval_collectBalanced, rawRowCheck1319]

def rawRow1320 : Integer.Sparse Key := [(key236, -2), (key241, -2), (key241, -2), (key248, 1), (key253, 1), (key248, 1), (key263, 1), (key253, 1), (key263, 1), (key302, 2), (key307, 2), (key307, 2), (key316, -1), (key321, -1), (key316, -1), (key331, -1), (key321, -1), (key331, -1), (key385, -1), (key390, -1), (key385, -1), (key400, -1), (key390, -1), (key400, -1), (key406, 1), (key411, 1), (key406, 1), (key421, 1), (key411, 1), (key421, 1)]

theorem rawRowCheck1320 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1320 := by decide +kernel

def row1320 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key302, 2), (key307, 4), (key316, -2), (key321, -2), (key331, -2), (key385, -2), (key390, -2), (key400, -2), (key406, 2), (key411, 2), (key421, 2)]

theorem rowCheck1320 : row1320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1320 := by decide +kernel

theorem rowEval1320 (x : Key → ℝ) : Integer.Sparse.eval row1320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1320, Integer.Sparse.eval_collectBalanced, rawRowCheck1320]

def rawRow1321 : Integer.Sparse Key := [(key241, -2), (key236, -2), (key241, -2), (key253, 1), (key248, 1), (key263, 1), (key248, 1), (key263, 1), (key253, 1), (key307, 2), (key302, 2), (key307, 2), (key321, -1), (key316, -1), (key331, -1), (key316, -1), (key331, -1), (key321, -1), (key390, -1), (key385, -1), (key400, -1), (key385, -1), (key400, -1), (key390, -1), (key411, 1), (key406, 1), (key421, 1), (key406, 1), (key421, 1), (key411, 1)]

theorem rawRowCheck1321 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1321 := by decide +kernel

def row1321 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key302, 2), (key307, 4), (key316, -2), (key321, -2), (key331, -2), (key385, -2), (key390, -2), (key400, -2), (key406, 2), (key411, 2), (key421, 2)]

theorem rowCheck1321 : row1321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1321 := by decide +kernel

theorem rowEval1321 (x : Key → ℝ) : Integer.Sparse.eval row1321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1321, Integer.Sparse.eval_collectBalanced, rawRowCheck1321]

def rawRow1322 : Integer.Sparse Key := [(key241, -2), (key241, -2), (key236, -2), (key263, 1), (key263, 1), (key253, 1), (key253, 1), (key248, 1), (key248, 1), (key307, 2), (key307, 2), (key302, 2), (key331, -1), (key331, -1), (key321, -1), (key321, -1), (key316, -1), (key316, -1), (key400, -1), (key400, -1), (key390, -1), (key390, -1), (key385, -1), (key385, -1), (key421, 1), (key421, 1), (key411, 1), (key411, 1), (key406, 1), (key406, 1)]

theorem rawRowCheck1322 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1322 := by decide +kernel

def row1322 : Integer.Sparse Key := [(key236, -2), (key241, -4), (key248, 2), (key253, 2), (key263, 2), (key302, 2), (key307, 4), (key316, -2), (key321, -2), (key331, -2), (key385, -2), (key390, -2), (key400, -2), (key406, 2), (key411, 2), (key421, 2)]

theorem rowCheck1322 : row1322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1322 := by decide +kernel

theorem rowEval1322 (x : Key → ℝ) : Integer.Sparse.eval row1322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1322, Integer.Sparse.eval_collectBalanced, rawRowCheck1322]

def rawRow1323 : Integer.Sparse Key := [(key248, -2), (key253, -2), (key263, -2), (key236, 1), (key241, 1), (key248, 1), (key263, 1), (key277, 1), (key278, 1), (key316, 2), (key321, 2), (key346, 2), (key302, -1), (key307, -1), (key316, -1), (key331, -1), (key346, -1), (key347, -1), (key406, -1), (key411, -1), (key435, -1), (key445, -1), (key487, -1), (key488, -1), (key385, 1), (key390, 1), (key435, 1), (key453, 1), (key487, 1), (key489, 1)]

theorem rawRowCheck1323 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form7 = rawRow1323 := by decide +kernel

def row1323 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

theorem rowCheck1323 : row1323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1323 := by decide +kernel

theorem rowEval1323 (x : Key → ℝ) : Integer.Sparse.eval row1323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1323, Integer.Sparse.eval_collectBalanced, rawRowCheck1323]

def rawRow1324 : Integer.Sparse Key := [(key253, -2), (key248, -2), (key263, -2), (key241, 1), (key236, 1), (key263, 1), (key248, 1), (key278, 1), (key277, 1), (key321, 2), (key316, 2), (key346, 2), (key307, -1), (key302, -1), (key331, -1), (key316, -1), (key347, -1), (key346, -1), (key411, -1), (key406, -1), (key445, -1), (key435, -1), (key488, -1), (key487, -1), (key390, 1), (key385, 1), (key453, 1), (key435, 1), (key489, 1), (key487, 1)]

theorem rawRowCheck1324 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form7 = rawRow1324 := by decide +kernel

def row1324 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

theorem rowCheck1324 : row1324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1324 := by decide +kernel

theorem rowEval1324 (x : Key → ℝ) : Integer.Sparse.eval row1324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1324, Integer.Sparse.eval_collectBalanced, rawRowCheck1324]

def rawRow1325 : Integer.Sparse Key := [(key248, -2), (key263, -2), (key253, -2), (key248, 1), (key263, 1), (key236, 1), (key278, 1), (key241, 1), (key263, 1), (key316, 2), (key346, 2), (key321, 2), (key316, -1), (key346, -1), (key302, -1), (key347, -1), (key307, -1), (key331, -1), (key435, -1), (key487, -1), (key406, -1), (key488, -1), (key411, -1), (key445, -1), (key435, 1), (key487, 1), (key385, 1), (key489, 1), (key390, 1), (key453, 1)]

theorem rawRowCheck1325 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form7 = rawRow1325 := by decide +kernel

def row1325 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

theorem rowCheck1325 : row1325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1325 := by decide +kernel

theorem rowEval1325 (x : Key → ℝ) : Integer.Sparse.eval row1325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1325, Integer.Sparse.eval_collectBalanced, rawRowCheck1325]

def rawRow1326 : Integer.Sparse Key := [(key263, -2), (key248, -2), (key253, -2), (key263, 1), (key248, 1), (key278, 1), (key236, 1), (key263, 1), (key241, 1), (key346, 2), (key316, 2), (key321, 2), (key346, -1), (key316, -1), (key347, -1), (key302, -1), (key331, -1), (key307, -1), (key487, -1), (key435, -1), (key488, -1), (key406, -1), (key445, -1), (key411, -1), (key487, 1), (key435, 1), (key489, 1), (key385, 1), (key453, 1), (key390, 1)]

theorem rawRowCheck1326 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form7 = rawRow1326 := by decide +kernel

def row1326 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

theorem rowCheck1326 : row1326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1326 := by decide +kernel

theorem rowEval1326 (x : Key → ℝ) : Integer.Sparse.eval row1326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1326, Integer.Sparse.eval_collectBalanced, rawRowCheck1326]

def rawRow1327 : Integer.Sparse Key := [(key253, -2), (key263, -2), (key248, -2), (key277, 1), (key278, 1), (key241, 1), (key263, 1), (key236, 1), (key248, 1), (key321, 2), (key346, 2), (key316, 2), (key331, -1), (key347, -1), (key307, -1), (key346, -1), (key302, -1), (key316, -1), (key445, -1), (key488, -1), (key411, -1), (key487, -1), (key406, -1), (key435, -1), (key453, 1), (key489, 1), (key390, 1), (key487, 1), (key385, 1), (key435, 1)]

theorem rawRowCheck1327 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form7 = rawRow1327 := by decide +kernel

def row1327 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

theorem rowCheck1327 : row1327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1327 := by decide +kernel

theorem rowEval1327 (x : Key → ℝ) : Integer.Sparse.eval row1327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1327, Integer.Sparse.eval_collectBalanced, rawRowCheck1327]

def rawRow1328 : Integer.Sparse Key := [(key263, -2), (key253, -2), (key248, -2), (key278, 1), (key277, 1), (key263, 1), (key241, 1), (key248, 1), (key236, 1), (key346, 2), (key321, 2), (key316, 2), (key347, -1), (key331, -1), (key346, -1), (key307, -1), (key316, -1), (key302, -1), (key488, -1), (key445, -1), (key487, -1), (key411, -1), (key435, -1), (key406, -1), (key489, 1), (key453, 1), (key487, 1), (key390, 1), (key435, 1), (key385, 1)]

theorem rawRowCheck1328 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form7 = rawRow1328 := by decide +kernel

def row1328 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -2), (key263, -1), (key277, 1), (key278, 1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, -1), (key346, 1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -1), (key445, -1), (key453, 1), (key488, -1), (key489, 1)]

theorem rowCheck1328 : row1328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1328 := by decide +kernel

theorem rowEval1328 (x : Key → ℝ) : Integer.Sparse.eval row1328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1328, Integer.Sparse.eval_collectBalanced, rawRowCheck1328]

def rawRow1329 : Integer.Sparse Key := [(key302, -2), (key307, -2), (key307, -2), (key316, 1), (key321, 1), (key316, 1), (key346, 1), (key321, 1), (key346, 1), (key236, 2), (key241, 2), (key241, 2), (key406, -1), (key411, -1), (key406, -1), (key421, -1), (key411, -1), (key421, -1), (key248, -1), (key253, -1), (key248, -1), (key263, -1), (key253, -1), (key263, -1), (key316, 1), (key321, 1), (key316, 1), (key331, 1), (key321, 1), (key331, 1)]

theorem rawRowCheck1329 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form7 = rawRow1329 := by decide +kernel

def row1329 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, -2), (key253, -2), (key263, -2), (key302, -2), (key307, -4), (key316, 4), (key321, 4), (key331, 2), (key346, 2), (key406, -2), (key411, -2), (key421, -2)]

theorem rowCheck1329 : row1329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1329 := by decide +kernel

theorem rowEval1329 (x : Key → ℝ) : Integer.Sparse.eval row1329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1329, Integer.Sparse.eval_collectBalanced, rawRowCheck1329]

def rawRow1330 : Integer.Sparse Key := [(key307, -2), (key302, -2), (key307, -2), (key321, 1), (key316, 1), (key346, 1), (key316, 1), (key346, 1), (key321, 1), (key241, 2), (key236, 2), (key241, 2), (key411, -1), (key406, -1), (key421, -1), (key406, -1), (key421, -1), (key411, -1), (key253, -1), (key248, -1), (key263, -1), (key248, -1), (key263, -1), (key253, -1), (key321, 1), (key316, 1), (key331, 1), (key316, 1), (key331, 1), (key321, 1)]

theorem rawRowCheck1330 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form7 = rawRow1330 := by decide +kernel

def row1330 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, -2), (key253, -2), (key263, -2), (key302, -2), (key307, -4), (key316, 4), (key321, 4), (key331, 2), (key346, 2), (key406, -2), (key411, -2), (key421, -2)]

theorem rowCheck1330 : row1330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1330 := by decide +kernel

theorem rowEval1330 (x : Key → ℝ) : Integer.Sparse.eval row1330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1330, Integer.Sparse.eval_collectBalanced, rawRowCheck1330]

def rawRow1331 : Integer.Sparse Key := [(key307, -2), (key307, -2), (key302, -2), (key346, 1), (key346, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1), (key241, 2), (key241, 2), (key236, 2), (key421, -1), (key421, -1), (key411, -1), (key411, -1), (key406, -1), (key406, -1), (key263, -1), (key263, -1), (key253, -1), (key253, -1), (key248, -1), (key248, -1), (key331, 1), (key331, 1), (key321, 1), (key321, 1), (key316, 1), (key316, 1)]

theorem rawRowCheck1331 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form7 = rawRow1331 := by decide +kernel

def row1331 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, -2), (key253, -2), (key263, -2), (key302, -2), (key307, -4), (key316, 4), (key321, 4), (key331, 2), (key346, 2), (key406, -2), (key411, -2), (key421, -2)]

theorem rowCheck1331 : row1331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1331 := by decide +kernel

theorem rowEval1331 (x : Key → ℝ) : Integer.Sparse.eval row1331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1331, Integer.Sparse.eval_collectBalanced, rawRowCheck1331]

def rawRow1332 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key302, 1), (key307, 1), (key316, 1), (key346, 1), (key331, 1), (key347, 1), (key406, 2), (key411, 2), (key421, 2), (key236, -1), (key241, -1), (key406, -1), (key421, -1), (key657, -1), (key658, -1), (key316, -1), (key321, -1), (key435, -1), (key445, -1), (key660, -1), (key661, -1), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1)]

theorem rawRowCheck1332 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form7 = rawRow1332 := by decide +kernel

def row1332 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

theorem rowCheck1332 : row1332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1332 := by decide +kernel

theorem rowEval1332 (x : Key → ℝ) : Integer.Sparse.eval row1332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1332, Integer.Sparse.eval_collectBalanced, rawRowCheck1332]

def rawRow1333 : Integer.Sparse Key := [(key321, -2), (key316, -2), (key331, -2), (key307, 1), (key302, 1), (key346, 1), (key316, 1), (key347, 1), (key331, 1), (key411, 2), (key406, 2), (key421, 2), (key241, -1), (key236, -1), (key421, -1), (key406, -1), (key658, -1), (key657, -1), (key321, -1), (key316, -1), (key445, -1), (key435, -1), (key661, -1), (key660, -1), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1)]

theorem rawRowCheck1333 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form7 = rawRow1333 := by decide +kernel

def row1333 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

theorem rowCheck1333 : row1333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1333 := by decide +kernel

theorem rowEval1333 (x : Key → ℝ) : Integer.Sparse.eval row1333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1333, Integer.Sparse.eval_collectBalanced, rawRowCheck1333]

def rawRow1334 : Integer.Sparse Key := [(key316, -2), (key331, -2), (key321, -2), (key316, 1), (key331, 1), (key302, 1), (key347, 1), (key307, 1), (key346, 1), (key406, 2), (key421, 2), (key411, 2), (key406, -1), (key421, -1), (key236, -1), (key658, -1), (key241, -1), (key421, -1), (key435, -1), (key660, -1), (key316, -1), (key661, -1), (key321, -1), (key445, -1), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1)]

theorem rawRowCheck1334 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form7 = rawRow1334 := by decide +kernel

def row1334 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key445, -1), (key453, 1), (key658, -1), (key661, -1), (key662, 1)]

theorem rowCheck1334 : row1334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1334 := by decide +kernel

theorem rowEval1334 (x : Key → ℝ) : Integer.Sparse.eval row1334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1334, Integer.Sparse.eval_collectBalanced, rawRowCheck1334]

def rawRow1335 : Integer.Sparse Key := [(key331, -2), (key316, -2), (key321, -2), (key331, 1), (key316, 1), (key347, 1), (key302, 1), (key346, 1), (key307, 1), (key421, 2), (key406, 2), (key411, 2), (key421, -1), (key406, -1), (key658, -1), (key236, -1), (key421, -1), (key241, -1), (key660, -1), (key435, -1), (key661, -1), (key316, -1), (key445, -1), (key321, -1), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1)]

theorem rawRowCheck1335 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form7 = rawRow1335 := by decide +kernel

def row1335 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key445, -1), (key453, 1), (key658, -1), (key661, -1), (key662, 1)]

theorem rowCheck1335 : row1335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1335 := by decide +kernel

theorem rowEval1335 (x : Key → ℝ) : Integer.Sparse.eval row1335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1335, Integer.Sparse.eval_collectBalanced, rawRowCheck1335]

def rawRow1336 : Integer.Sparse Key := [(key321, -2), (key331, -2), (key316, -2), (key346, 1), (key347, 1), (key307, 1), (key331, 1), (key302, 1), (key316, 1), (key411, 2), (key421, 2), (key406, 2), (key657, -1), (key658, -1), (key241, -1), (key421, -1), (key236, -1), (key406, -1), (key445, -1), (key661, -1), (key321, -1), (key660, -1), (key316, -1), (key435, -1), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1)]

theorem rawRowCheck1336 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form7 = rawRow1336 := by decide +kernel

def row1336 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

theorem rowCheck1336 : row1336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1336 := by decide +kernel

theorem rowEval1336 (x : Key → ℝ) : Integer.Sparse.eval row1336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1336, Integer.Sparse.eval_collectBalanced, rawRowCheck1336]

def rawRow1337 : Integer.Sparse Key := [(key331, -2), (key321, -2), (key316, -2), (key347, 1), (key346, 1), (key331, 1), (key307, 1), (key316, 1), (key302, 1), (key421, 2), (key411, 2), (key406, 2), (key658, -1), (key657, -1), (key421, -1), (key241, -1), (key406, -1), (key236, -1), (key661, -1), (key445, -1), (key660, -1), (key321, -1), (key435, -1), (key316, -1), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1)]

theorem rawRowCheck1337 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form7 = rawRow1337 := by decide +kernel

def row1337 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 1), (key302, 1), (key307, 1), (key316, -2), (key321, -3), (key331, -1), (key346, 1), (key347, 1), (key406, 1), (key411, 2), (key421, 1), (key445, -1), (key453, 1), (key657, -1), (key658, -1), (key661, -1), (key662, 1)]

theorem rowCheck1337 : row1337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1337 := by decide +kernel

theorem rowEval1337 (x : Key → ℝ) : Integer.Sparse.eval row1337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1337, Integer.Sparse.eval_collectBalanced, rawRowCheck1337]

def rawRow1338 : Integer.Sparse Key := [(key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key435, 1), (key487, 1), (key445, 1), (key488, 1), (key248, 2), (key253, 2), (key263, 2), (key316, -1), (key321, -1), (key435, -1), (key660, -1), (key445, -1), (key661, -1), (key236, -1), (key241, -1), (key248, -1), (key263, -1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key316, 1), (key331, 1), (key346, 1), (key347, 1)]

theorem rawRowCheck1338 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form7 = rawRow1338 := by decide +kernel

def row1338 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

theorem rowCheck1338 : row1338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1338 := by decide +kernel

theorem rowEval1338 (x : Key → ℝ) : Integer.Sparse.eval row1338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1338, Integer.Sparse.eval_collectBalanced, rawRowCheck1338]

def rawRow1339 : Integer.Sparse Key := [(key390, -2), (key385, -2), (key400, -2), (key411, 1), (key406, 1), (key487, 1), (key435, 1), (key488, 1), (key445, 1), (key253, 2), (key248, 2), (key263, 2), (key321, -1), (key316, -1), (key660, -1), (key435, -1), (key661, -1), (key445, -1), (key241, -1), (key236, -1), (key263, -1), (key248, -1), (key278, -1), (key277, -1), (key307, 1), (key302, 1), (key331, 1), (key316, 1), (key347, 1), (key346, 1)]

theorem rawRowCheck1339 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form7 = rawRow1339 := by decide +kernel

def row1339 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

theorem rowCheck1339 : row1339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1339 := by decide +kernel

theorem rowEval1339 (x : Key → ℝ) : Integer.Sparse.eval row1339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1339, Integer.Sparse.eval_collectBalanced, rawRowCheck1339]

def rawRow1340 : Integer.Sparse Key := [(key385, -2), (key400, -2), (key390, -2), (key435, 1), (key445, 1), (key406, 1), (key488, 1), (key411, 1), (key487, 1), (key248, 2), (key263, 2), (key253, 2), (key435, -1), (key445, -1), (key316, -1), (key661, -1), (key321, -1), (key660, -1), (key248, -1), (key263, -1), (key236, -1), (key278, -1), (key241, -1), (key263, -1), (key316, 1), (key346, 1), (key302, 1), (key347, 1), (key307, 1), (key331, 1)]

theorem rawRowCheck1340 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form7 = rawRow1340 := by decide +kernel

def row1340 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

theorem rowCheck1340 : row1340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1340 := by decide +kernel

theorem rowEval1340 (x : Key → ℝ) : Integer.Sparse.eval row1340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1340, Integer.Sparse.eval_collectBalanced, rawRowCheck1340]

def rawRow1341 : Integer.Sparse Key := [(key400, -2), (key385, -2), (key390, -2), (key445, 1), (key435, 1), (key488, 1), (key406, 1), (key487, 1), (key411, 1), (key263, 2), (key248, 2), (key253, 2), (key445, -1), (key435, -1), (key661, -1), (key316, -1), (key660, -1), (key321, -1), (key263, -1), (key248, -1), (key278, -1), (key236, -1), (key263, -1), (key241, -1), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1)]

theorem rawRowCheck1341 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form7 = rawRow1341 := by decide +kernel

def row1341 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

theorem rowCheck1341 : row1341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1341 := by decide +kernel

theorem rowEval1341 (x : Key → ℝ) : Integer.Sparse.eval row1341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1341, Integer.Sparse.eval_collectBalanced, rawRowCheck1341]

def rawRow1342 : Integer.Sparse Key := [(key390, -2), (key400, -2), (key385, -2), (key487, 1), (key488, 1), (key411, 1), (key445, 1), (key406, 1), (key435, 1), (key253, 2), (key263, 2), (key248, 2), (key660, -1), (key661, -1), (key321, -1), (key445, -1), (key316, -1), (key435, -1), (key277, -1), (key278, -1), (key241, -1), (key263, -1), (key236, -1), (key248, -1), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1)]

theorem rawRowCheck1342 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form7 = rawRow1342 := by decide +kernel

def row1342 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

theorem rowCheck1342 : row1342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1342 := by decide +kernel

theorem rowEval1342 (x : Key → ℝ) : Integer.Sparse.eval row1342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1342, Integer.Sparse.eval_collectBalanced, rawRowCheck1342]

def rawRow1343 : Integer.Sparse Key := [(key400, -2), (key390, -2), (key385, -2), (key488, 1), (key487, 1), (key445, 1), (key411, 1), (key435, 1), (key406, 1), (key263, 2), (key253, 2), (key248, 2), (key661, -1), (key660, -1), (key445, -1), (key321, -1), (key435, -1), (key316, -1), (key278, -1), (key277, -1), (key263, -1), (key241, -1), (key248, -1), (key236, -1), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1)]

theorem rawRowCheck1343 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form7 = rawRow1343 := by decide +kernel

def row1343 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key248, 1), (key253, 2), (key263, 1), (key277, -1), (key278, -1), (key302, 1), (key307, 1), (key321, -1), (key331, 1), (key346, 1), (key347, 1), (key385, -2), (key390, -2), (key400, -2), (key406, 1), (key411, 1), (key487, 1), (key488, 1), (key660, -1), (key661, -1)]

theorem rowCheck1343 : row1343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1343 := by decide +kernel

theorem rowEval1343 (x : Key → ℝ) : Integer.Sparse.eval row1343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form7) x := by
  rw [rowCheck1343, Integer.Sparse.eval_collectBalanced, rawRowCheck1343]

def rawRow1344 : Integer.Sparse Key := [(key406, -2), (key411, -2), (key421, -2), (key385, 1), (key390, 1), (key435, 1), (key487, 1), (key453, 1), (key489, 1), (key316, 2), (key321, 2), (key331, 2), (key248, -1), (key253, -1), (key435, -1), (key660, -1), (key453, -1), (key662, -1), (key302, -1), (key307, -1), (key316, -1), (key346, -1), (key331, -1), (key347, -1), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1)]

theorem rawRowCheck1344 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form7 = rawRow1344 := by decide +kernel

def row1344 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

theorem rowCheck1344 : row1344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1344 := by decide +kernel

theorem rowEval1344 (x : Key → ℝ) : Integer.Sparse.eval row1344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1344, Integer.Sparse.eval_collectBalanced, rawRowCheck1344]

def rawRow1345 : Integer.Sparse Key := [(key411, -2), (key406, -2), (key421, -2), (key390, 1), (key385, 1), (key487, 1), (key435, 1), (key489, 1), (key453, 1), (key321, 2), (key316, 2), (key331, 2), (key253, -1), (key248, -1), (key660, -1), (key435, -1), (key662, -1), (key453, -1), (key307, -1), (key302, -1), (key346, -1), (key316, -1), (key347, -1), (key331, -1), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1)]

theorem rawRowCheck1345 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form7 = rawRow1345 := by decide +kernel

def row1345 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

theorem rowCheck1345 : row1345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1345 := by decide +kernel

theorem rowEval1345 (x : Key → ℝ) : Integer.Sparse.eval row1345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1345, Integer.Sparse.eval_collectBalanced, rawRowCheck1345]

def rawRow1346 : Integer.Sparse Key := [(key406, -2), (key421, -2), (key411, -2), (key435, 1), (key453, 1), (key385, 1), (key489, 1), (key390, 1), (key487, 1), (key316, 2), (key331, 2), (key321, 2), (key435, -1), (key453, -1), (key248, -1), (key662, -1), (key253, -1), (key660, -1), (key316, -1), (key331, -1), (key302, -1), (key347, -1), (key307, -1), (key346, -1), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1)]

theorem rawRowCheck1346 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form7 = rawRow1346 := by decide +kernel

def row1346 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key487, 1), (key489, 1), (key658, 1), (key660, -1), (key662, -1)]

theorem rowCheck1346 : row1346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1346 := by decide +kernel

theorem rowEval1346 (x : Key → ℝ) : Integer.Sparse.eval row1346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1346, Integer.Sparse.eval_collectBalanced, rawRowCheck1346]

def rawRow1347 : Integer.Sparse Key := [(key421, -2), (key406, -2), (key411, -2), (key453, 1), (key435, 1), (key489, 1), (key385, 1), (key487, 1), (key390, 1), (key331, 2), (key316, 2), (key321, 2), (key453, -1), (key435, -1), (key662, -1), (key248, -1), (key660, -1), (key253, -1), (key331, -1), (key316, -1), (key347, -1), (key302, -1), (key346, -1), (key307, -1), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1)]

theorem rawRowCheck1347 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form7 = rawRow1347 := by decide +kernel

def row1347 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key487, 1), (key489, 1), (key658, 1), (key660, -1), (key662, -1)]

theorem rowCheck1347 : row1347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1347 := by decide +kernel

theorem rowEval1347 (x : Key → ℝ) : Integer.Sparse.eval row1347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1347, Integer.Sparse.eval_collectBalanced, rawRowCheck1347]

def rawRow1348 : Integer.Sparse Key := [(key411, -2), (key421, -2), (key406, -2), (key487, 1), (key489, 1), (key390, 1), (key453, 1), (key385, 1), (key435, 1), (key321, 2), (key331, 2), (key316, 2), (key660, -1), (key662, -1), (key253, -1), (key453, -1), (key248, -1), (key435, -1), (key346, -1), (key347, -1), (key307, -1), (key331, -1), (key302, -1), (key316, -1), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1)]

theorem rawRowCheck1348 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form7 = rawRow1348 := by decide +kernel

def row1348 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

theorem rowCheck1348 : row1348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1348 := by decide +kernel

theorem rowEval1348 (x : Key → ℝ) : Integer.Sparse.eval row1348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck1348, Integer.Sparse.eval_collectBalanced, rawRowCheck1348]

def rawRow1349 : Integer.Sparse Key := [(key421, -2), (key411, -2), (key406, -2), (key489, 1), (key487, 1), (key453, 1), (key390, 1), (key435, 1), (key385, 1), (key331, 2), (key321, 2), (key316, 2), (key662, -1), (key660, -1), (key453, -1), (key253, -1), (key435, -1), (key248, -1), (key347, -1), (key346, -1), (key331, -1), (key307, -1), (key316, -1), (key302, -1), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1)]

theorem rawRowCheck1349 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form7 = rawRow1349 := by decide +kernel

def row1349 : Integer.Sparse Key := [(key236, 1), (key241, 1), (key248, -1), (key253, -1), (key302, -1), (key307, -1), (key316, 1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key390, 1), (key406, -1), (key411, -2), (key421, -1), (key487, 1), (key489, 1), (key657, 1), (key658, 1), (key660, -1), (key662, -1)]

theorem rowCheck1349 : row1349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1349 := by decide +kernel

theorem rowEval1349 (x : Key → ℝ) : Integer.Sparse.eval row1349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form7) x := by
  rw [rowCheck1349, Integer.Sparse.eval_collectBalanced, rawRowCheck1349]

def rawRow1350 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1075, -2), (key1033, 1), (key1040, 1), (key1033, 1), (key1075, 1), (key1040, 1), (key1075, 1), (key1111, 2), (key1111, 2), (key1154, 2), (key1111, -1), (key1126, -1), (key1111, -1), (key1154, -1), (key1126, -1), (key1154, -1), (key1190, -1), (key1192, -1), (key1190, -1), (key1211, -1), (key1192, -1), (key1211, -1), (key1190, 1), (key1198, 1), (key1190, 1), (key1211, 1), (key1198, 1), (key1211, 1)]

theorem rawRowCheck1350 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1350 := by decide +kernel

def row1350 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

theorem rowCheck1350 : row1350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1350 := by decide +kernel

theorem rowEval1350 (x : Key → ℝ) : Integer.Sparse.eval row1350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1350, Integer.Sparse.eval_collectBalanced, rawRowCheck1350]

def rawRow1351 : Integer.Sparse Key := [(key1033, -2), (key1075, -2), (key1033, -2), (key1040, 1), (key1033, 1), (key1075, 1), (key1033, 1), (key1075, 1), (key1040, 1), (key1111, 2), (key1154, 2), (key1111, 2), (key1126, -1), (key1111, -1), (key1154, -1), (key1111, -1), (key1154, -1), (key1126, -1), (key1192, -1), (key1190, -1), (key1211, -1), (key1190, -1), (key1211, -1), (key1192, -1), (key1198, 1), (key1190, 1), (key1211, 1), (key1190, 1), (key1211, 1), (key1198, 1)]

theorem rawRowCheck1351 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1351 := by decide +kernel

def row1351 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

theorem rowCheck1351 : row1351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1351 := by decide +kernel

theorem rowEval1351 (x : Key → ℝ) : Integer.Sparse.eval row1351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1351, Integer.Sparse.eval_collectBalanced, rawRowCheck1351]

def rawRow1352 : Integer.Sparse Key := [(key1075, -2), (key1033, -2), (key1033, -2), (key1075, 1), (key1075, 1), (key1040, 1), (key1040, 1), (key1033, 1), (key1033, 1), (key1154, 2), (key1111, 2), (key1111, 2), (key1154, -1), (key1154, -1), (key1126, -1), (key1126, -1), (key1111, -1), (key1111, -1), (key1211, -1), (key1211, -1), (key1192, -1), (key1192, -1), (key1190, -1), (key1190, -1), (key1211, 1), (key1211, 1), (key1198, 1), (key1198, 1), (key1190, 1), (key1190, 1)]

theorem rawRowCheck1352 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1352 := by decide +kernel

def row1352 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

theorem rowCheck1352 : row1352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1352 := by decide +kernel

theorem rowEval1352 (x : Key → ℝ) : Integer.Sparse.eval row1352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1352, Integer.Sparse.eval_collectBalanced, rawRowCheck1352]

def rawRow1353 : Integer.Sparse Key := [(key1040, -2), (key1040, -2), (key1040, -2), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1126, 2), (key1126, 2), (key1126, 2), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1198, -1), (key1192, 1), (key1192, 1), (key1192, 1), (key1192, 1), (key1192, 1), (key1192, 1)]

theorem rawRowCheck1353 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1353 := by decide +kernel

def row1353 : Integer.Sparse Key := [(key1033, 6), (key1040, -6), (key1111, -6), (key1126, 6), (key1192, 6), (key1198, -6)]

theorem rowCheck1353 : row1353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1353 := by decide +kernel

theorem rowEval1353 (x : Key → ℝ) : Integer.Sparse.eval row1353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1353, Integer.Sparse.eval_collectBalanced, rawRowCheck1353]

def rawRow1354 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1154, -2), (key1190, 1), (key1192, 1), (key1190, 1), (key1211, 1), (key1192, 1), (key1211, 1), (key1033, 2), (key1033, 2), (key1075, 2), (key1190, -1), (key1198, -1), (key1190, -1), (key1211, -1), (key1198, -1), (key1211, -1), (key1033, -1), (key1040, -1), (key1033, -1), (key1075, -1), (key1040, -1), (key1075, -1), (key1111, 1), (key1126, 1), (key1111, 1), (key1154, 1), (key1126, 1), (key1154, 1)]

theorem rawRowCheck1354 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0 = rawRow1354 := by decide +kernel

def row1354 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

theorem rowCheck1354 : row1354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1354 := by decide +kernel

theorem rowEval1354 (x : Key → ℝ) : Integer.Sparse.eval row1354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck1354, Integer.Sparse.eval_collectBalanced, rawRowCheck1354]

def rawRow1355 : Integer.Sparse Key := [(key1111, -2), (key1154, -2), (key1111, -2), (key1192, 1), (key1190, 1), (key1211, 1), (key1190, 1), (key1211, 1), (key1192, 1), (key1033, 2), (key1075, 2), (key1033, 2), (key1198, -1), (key1190, -1), (key1211, -1), (key1190, -1), (key1211, -1), (key1198, -1), (key1040, -1), (key1033, -1), (key1075, -1), (key1033, -1), (key1075, -1), (key1040, -1), (key1126, 1), (key1111, 1), (key1154, 1), (key1111, 1), (key1154, 1), (key1126, 1)]

theorem rawRowCheck1355 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0 = rawRow1355 := by decide +kernel

def row1355 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

theorem rowCheck1355 : row1355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1355 := by decide +kernel

theorem rowEval1355 (x : Key → ℝ) : Integer.Sparse.eval row1355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1355, Integer.Sparse.eval_collectBalanced, rawRowCheck1355]

def rawRow1356 : Integer.Sparse Key := [(key1154, -2), (key1111, -2), (key1111, -2), (key1211, 1), (key1211, 1), (key1192, 1), (key1192, 1), (key1190, 1), (key1190, 1), (key1075, 2), (key1033, 2), (key1033, 2), (key1211, -1), (key1211, -1), (key1198, -1), (key1198, -1), (key1190, -1), (key1190, -1), (key1075, -1), (key1075, -1), (key1040, -1), (key1040, -1), (key1033, -1), (key1033, -1), (key1154, 1), (key1154, 1), (key1126, 1), (key1126, 1), (key1111, 1), (key1111, 1)]

theorem rawRowCheck1356 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0 = rawRow1356 := by decide +kernel

def row1356 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

theorem rowCheck1356 : row1356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1356 := by decide +kernel

theorem rowEval1356 (x : Key → ℝ) : Integer.Sparse.eval row1356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1356, Integer.Sparse.eval_collectBalanced, rawRowCheck1356]

def rawRow1357 : Integer.Sparse Key := [(key1005, -2), (key1192, -2), (key1192, -2), (key998, 1), (key998, 1), (key1111, 1), (key1111, 1), (key1190, 1), (key1190, 1), (key1018, 2), (key1198, 2), (key1198, 2), (key998, -1), (key998, -1), (key1033, -1), (key1033, -1), (key1190, -1), (key1190, -1), (key1018, -1), (key1018, -1), (key1126, -1), (key1126, -1), (key1198, -1), (key1198, -1), (key1005, 1), (key1005, 1), (key1040, 1), (key1040, 1), (key1192, 1), (key1192, 1)]

theorem rawRowCheck1357 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1357 := by decide +kernel

def row1357 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

theorem rowCheck1357 : row1357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1357 := by decide +kernel

theorem rowEval1357 (x : Key → ℝ) : Integer.Sparse.eval row1357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1357, Integer.Sparse.eval_collectBalanced, rawRowCheck1357]

def rawRow1358 : Integer.Sparse Key := [(key1192, -2), (key1005, -2), (key1192, -2), (key1111, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1111, 1), (key1198, 2), (key1018, 2), (key1198, 2), (key1033, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1033, -1), (key1126, -1), (key1198, -1), (key1018, -1), (key1198, -1), (key1018, -1), (key1126, -1), (key1040, 1), (key1192, 1), (key1005, 1), (key1192, 1), (key1005, 1), (key1040, 1)]

theorem rawRowCheck1358 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1358 := by decide +kernel

def row1358 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

theorem rowCheck1358 : row1358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1358 := by decide +kernel

theorem rowEval1358 (x : Key → ℝ) : Integer.Sparse.eval row1358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1358, Integer.Sparse.eval_collectBalanced, rawRowCheck1358]

def rawRow1359 : Integer.Sparse Key := [(key1192, -2), (key1192, -2), (key1005, -2), (key1190, 1), (key1111, 1), (key1190, 1), (key998, 1), (key1111, 1), (key998, 1), (key1198, 2), (key1198, 2), (key1018, 2), (key1190, -1), (key1033, -1), (key1190, -1), (key998, -1), (key1033, -1), (key998, -1), (key1198, -1), (key1126, -1), (key1198, -1), (key1018, -1), (key1126, -1), (key1018, -1), (key1192, 1), (key1040, 1), (key1192, 1), (key1005, 1), (key1040, 1), (key1005, 1)]

theorem rawRowCheck1359 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1359 := by decide +kernel

def row1359 : Integer.Sparse Key := [(key1033, -2), (key1040, 2), (key1111, 2), (key1126, -2), (key1192, -2), (key1198, 2)]

theorem rowCheck1359 : row1359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1359 := by decide +kernel

theorem rowEval1359 (x : Key → ℝ) : Integer.Sparse.eval row1359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1359, Integer.Sparse.eval_collectBalanced, rawRowCheck1359]

def rawRow1360 : Integer.Sparse Key := [(key1126, -2), (key1126, -2), (key1126, -2), (key1198, 1), (key1198, 1), (key1198, 1), (key1198, 1), (key1198, 1), (key1198, 1), (key1040, 2), (key1040, 2), (key1040, 2), (key1192, -1), (key1192, -1), (key1192, -1), (key1192, -1), (key1192, -1), (key1192, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1)]

theorem rawRowCheck1360 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0 = rawRow1360 := by decide +kernel

def row1360 : Integer.Sparse Key := [(key1033, -6), (key1040, 6), (key1111, 6), (key1126, -6), (key1192, -6), (key1198, 6)]

theorem rowCheck1360 : row1360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1360 := by decide +kernel

theorem rowEval1360 (x : Key → ℝ) : Integer.Sparse.eval row1360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1360, Integer.Sparse.eval_collectBalanced, rawRowCheck1360]

def rawRow1361 : Integer.Sparse Key := [(key1018, -2), (key1198, -2), (key1198, -2), (key1018, 1), (key1018, 1), (key1126, 1), (key1126, 1), (key1198, 1), (key1198, 1), (key1005, 2), (key1192, 2), (key1192, 2), (key1005, -1), (key1005, -1), (key1040, -1), (key1040, -1), (key1192, -1), (key1192, -1), (key998, -1), (key998, -1), (key1111, -1), (key1111, -1), (key1190, -1), (key1190, -1), (key998, 1), (key998, 1), (key1033, 1), (key1033, 1), (key1190, 1), (key1190, 1)]

theorem rawRowCheck1361 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0 = rawRow1361 := by decide +kernel

def row1361 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

theorem rowCheck1361 : row1361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1361 := by decide +kernel

theorem rowEval1361 (x : Key → ℝ) : Integer.Sparse.eval row1361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1361, Integer.Sparse.eval_collectBalanced, rawRowCheck1361]

def rawRow1362 : Integer.Sparse Key := [(key1198, -2), (key1018, -2), (key1198, -2), (key1126, 1), (key1198, 1), (key1018, 1), (key1198, 1), (key1018, 1), (key1126, 1), (key1192, 2), (key1005, 2), (key1192, 2), (key1040, -1), (key1192, -1), (key1005, -1), (key1192, -1), (key1005, -1), (key1040, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1190, -1), (key998, -1), (key1111, -1), (key1033, 1), (key1190, 1), (key998, 1), (key1190, 1), (key998, 1), (key1033, 1)]

theorem rawRowCheck1362 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0 = rawRow1362 := by decide +kernel

def row1362 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

theorem rowCheck1362 : row1362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1362 := by decide +kernel

theorem rowEval1362 (x : Key → ℝ) : Integer.Sparse.eval row1362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck1362, Integer.Sparse.eval_collectBalanced, rawRowCheck1362]

def rawRow1363 : Integer.Sparse Key := [(key1198, -2), (key1198, -2), (key1018, -2), (key1198, 1), (key1126, 1), (key1198, 1), (key1018, 1), (key1126, 1), (key1018, 1), (key1192, 2), (key1192, 2), (key1005, 2), (key1192, -1), (key1040, -1), (key1192, -1), (key1005, -1), (key1040, -1), (key1005, -1), (key1190, -1), (key1111, -1), (key1190, -1), (key998, -1), (key1111, -1), (key998, -1), (key1190, 1), (key1033, 1), (key1190, 1), (key998, 1), (key1033, 1), (key998, 1)]

theorem rawRowCheck1363 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0 = rawRow1363 := by decide +kernel

def row1363 : Integer.Sparse Key := [(key1033, 2), (key1040, -2), (key1111, -2), (key1126, 2), (key1192, 2), (key1198, -2)]

theorem rowCheck1363 : row1363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1363 := by decide +kernel

theorem rowEval1363 (x : Key → ℝ) : Integer.Sparse.eval row1363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form0) x := by
  rw [rowCheck1363, Integer.Sparse.eval_collectBalanced, rawRowCheck1363]

def rawRow1364 : Integer.Sparse Key := [(key17, -6), (key17, 2), (key17, 2), (key28, 2), (key42, 6), (key42, -2), (key42, -2), (key69, -2), (key99, -2), (key99, -2), (key108, -2), (key99, 2), (key99, 2), (key132, 2)]

theorem rawRowCheck1364 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1364 := by decide +kernel

def row1364 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

theorem rowCheck1364 : row1364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1364 := by decide +kernel

theorem rowEval1364 (x : Key → ℝ) : Integer.Sparse.eval row1364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1364, Integer.Sparse.eval_collectBalanced, rawRowCheck1364]

def rawRow1365 : Integer.Sparse Key := [(key17, -6), (key17, 2), (key28, 2), (key17, 2), (key42, 6), (key42, -2), (key69, -2), (key42, -2), (key99, -2), (key108, -2), (key99, -2), (key99, 2), (key132, 2), (key99, 2)]

theorem rawRowCheck1365 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1365 := by decide +kernel

def row1365 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

theorem rowCheck1365 : row1365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1365 := by decide +kernel

theorem rowEval1365 (x : Key → ℝ) : Integer.Sparse.eval row1365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1365, Integer.Sparse.eval_collectBalanced, rawRowCheck1365]

def rawRow1366 : Integer.Sparse Key := [(key17, -6), (key28, 2), (key17, 2), (key17, 2), (key42, 6), (key69, -2), (key42, -2), (key42, -2), (key108, -2), (key99, -2), (key99, -2), (key132, 2), (key99, 2), (key99, 2)]

theorem rawRowCheck1366 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1366 := by decide +kernel

def row1366 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

theorem rowCheck1366 : row1366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1366 := by decide +kernel

theorem rowEval1366 (x : Key → ℝ) : Integer.Sparse.eval row1366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1366, Integer.Sparse.eval_collectBalanced, rawRowCheck1366]

def rawRow1367 : Integer.Sparse Key := [(key28, -6), (key17, 2), (key17, 2), (key17, 2), (key69, 6), (key42, -2), (key42, -2), (key42, -2), (key132, -2), (key132, -2), (key132, -2), (key108, 2), (key108, 2), (key108, 2)]

theorem rawRowCheck1367 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1367 := by decide +kernel

def row1367 : Integer.Sparse Key := [(key17, 6), (key28, -6), (key42, -6), (key69, 6), (key108, 6), (key132, -6)]

theorem rowCheck1367 : row1367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1367 := by decide +kernel

theorem rowEval1367 (x : Key → ℝ) : Integer.Sparse.eval row1367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1367, Integer.Sparse.eval_collectBalanced, rawRowCheck1367]

def rawRow1368 : Integer.Sparse Key := [(key42, -6), (key99, 2), (key99, 2), (key108, 2), (key17, 6), (key99, -2), (key99, -2), (key132, -2), (key17, -2), (key17, -2), (key28, -2), (key42, 2), (key42, 2), (key69, 2)]

theorem rawRowCheck1368 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1 = rawRow1368 := by decide +kernel

def row1368 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

theorem rowCheck1368 : row1368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1368 := by decide +kernel

theorem rowEval1368 (x : Key → ℝ) : Integer.Sparse.eval row1368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck1368, Integer.Sparse.eval_collectBalanced, rawRowCheck1368]

def rawRow1369 : Integer.Sparse Key := [(key42, -6), (key99, 2), (key108, 2), (key99, 2), (key17, 6), (key99, -2), (key132, -2), (key99, -2), (key17, -2), (key28, -2), (key17, -2), (key42, 2), (key69, 2), (key42, 2)]

theorem rawRowCheck1369 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1 = rawRow1369 := by decide +kernel

def row1369 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

theorem rowCheck1369 : row1369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1369 := by decide +kernel

theorem rowEval1369 (x : Key → ℝ) : Integer.Sparse.eval row1369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1369, Integer.Sparse.eval_collectBalanced, rawRowCheck1369]

def rawRow1370 : Integer.Sparse Key := [(key42, -6), (key108, 2), (key99, 2), (key99, 2), (key17, 6), (key132, -2), (key99, -2), (key99, -2), (key28, -2), (key17, -2), (key17, -2), (key69, 2), (key42, 2), (key42, 2)]

theorem rawRowCheck1370 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1 = rawRow1370 := by decide +kernel

def row1370 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

theorem rowCheck1370 : row1370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1370 := by decide +kernel

theorem rowEval1370 (x : Key → ℝ) : Integer.Sparse.eval row1370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1370, Integer.Sparse.eval_collectBalanced, rawRowCheck1370]

def rawRow1371 : Integer.Sparse Key := [(key108, -6), (key42, 2), (key99, 2), (key99, 2), (key132, 6), (key17, -2), (key99, -2), (key99, -2), (key69, -2), (key132, -2), (key132, -2), (key28, 2), (key108, 2), (key108, 2)]

theorem rawRowCheck1371 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1371 := by decide +kernel

def row1371 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

theorem rowCheck1371 : row1371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1371 := by decide +kernel

theorem rowEval1371 (x : Key → ℝ) : Integer.Sparse.eval row1371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1371, Integer.Sparse.eval_collectBalanced, rawRowCheck1371]

def rawRow1372 : Integer.Sparse Key := [(key108, -6), (key99, 2), (key42, 2), (key99, 2), (key132, 6), (key99, -2), (key17, -2), (key99, -2), (key132, -2), (key69, -2), (key132, -2), (key108, 2), (key28, 2), (key108, 2)]

theorem rawRowCheck1372 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1372 := by decide +kernel

def row1372 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

theorem rowCheck1372 : row1372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1372 := by decide +kernel

theorem rowEval1372 (x : Key → ℝ) : Integer.Sparse.eval row1372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1372, Integer.Sparse.eval_collectBalanced, rawRowCheck1372]

def rawRow1373 : Integer.Sparse Key := [(key108, -6), (key99, 2), (key99, 2), (key42, 2), (key132, 6), (key99, -2), (key99, -2), (key17, -2), (key132, -2), (key132, -2), (key69, -2), (key108, 2), (key108, 2), (key28, 2)]

theorem rawRowCheck1373 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1373 := by decide +kernel

def row1373 : Integer.Sparse Key := [(key17, -2), (key28, 2), (key42, 2), (key69, -2), (key108, -2), (key132, 2)]

theorem rowCheck1373 : row1373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1373 := by decide +kernel

theorem rowEval1373 (x : Key → ℝ) : Integer.Sparse.eval row1373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1373, Integer.Sparse.eval_collectBalanced, rawRowCheck1373]

def rawRow1374 : Integer.Sparse Key := [(key69, -6), (key132, 2), (key132, 2), (key132, 2), (key28, 6), (key108, -2), (key108, -2), (key108, -2), (key17, -2), (key17, -2), (key17, -2), (key42, 2), (key42, 2), (key42, 2)]

theorem rawRowCheck1374 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1 = rawRow1374 := by decide +kernel

def row1374 : Integer.Sparse Key := [(key17, -6), (key28, 6), (key42, 6), (key69, -6), (key108, -6), (key132, 6)]

theorem rowCheck1374 : row1374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1374 := by decide +kernel

theorem rowEval1374 (x : Key → ℝ) : Integer.Sparse.eval row1374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1374, Integer.Sparse.eval_collectBalanced, rawRowCheck1374]

def rawRow1375 : Integer.Sparse Key := [(key132, -6), (key69, 2), (key132, 2), (key132, 2), (key108, 6), (key28, -2), (key108, -2), (key108, -2), (key42, -2), (key99, -2), (key99, -2), (key17, 2), (key99, 2), (key99, 2)]

theorem rawRowCheck1375 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1 = rawRow1375 := by decide +kernel

def row1375 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

theorem rowCheck1375 : row1375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1375 := by decide +kernel

theorem rowEval1375 (x : Key → ℝ) : Integer.Sparse.eval row1375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1375, Integer.Sparse.eval_collectBalanced, rawRowCheck1375]

def rawRow1376 : Integer.Sparse Key := [(key132, -6), (key132, 2), (key69, 2), (key132, 2), (key108, 6), (key108, -2), (key28, -2), (key108, -2), (key99, -2), (key42, -2), (key99, -2), (key99, 2), (key17, 2), (key99, 2)]

theorem rawRowCheck1376 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1 = rawRow1376 := by decide +kernel

def row1376 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

theorem rowCheck1376 : row1376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1376 := by decide +kernel

theorem rowEval1376 (x : Key → ℝ) : Integer.Sparse.eval row1376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck1376, Integer.Sparse.eval_collectBalanced, rawRowCheck1376]

def rawRow1377 : Integer.Sparse Key := [(key132, -6), (key132, 2), (key132, 2), (key69, 2), (key108, 6), (key108, -2), (key108, -2), (key28, -2), (key99, -2), (key99, -2), (key42, -2), (key99, 2), (key99, 2), (key17, 2)]

theorem rawRowCheck1377 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1 = rawRow1377 := by decide +kernel

def row1377 : Integer.Sparse Key := [(key17, 2), (key28, -2), (key42, -2), (key69, 2), (key108, 2), (key132, -2)]

theorem rowCheck1377 : row1377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1377 := by decide +kernel

theorem rowEval1377 (x : Key → ℝ) : Integer.Sparse.eval row1377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form1) x := by
  rw [rowCheck1377, Integer.Sparse.eval_collectBalanced, rawRowCheck1377]

def rawRow1378 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1000, -2), (key994, 1), (key1000, 1), (key994, 1), (key1014, 1), (key1000, 1), (key1014, 1), (key1029, 2), (key1035, 2), (key1035, 2), (key1029, -1), (key1035, -1), (key1029, -1), (key1070, -1), (key1035, -1), (key1070, -1), (key1107, -1), (key1113, -1), (key1107, -1), (key1122, -1), (key1113, -1), (key1122, -1), (key1107, 1), (key1113, 1), (key1107, 1), (key1149, 1), (key1113, 1), (key1149, 1)]

theorem rawRowCheck1378 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1378 := by decide +kernel

def row1378 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

theorem rowCheck1378 : row1378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1378 := by decide +kernel

theorem rowEval1378 (x : Key → ℝ) : Integer.Sparse.eval row1378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1378, Integer.Sparse.eval_collectBalanced, rawRowCheck1378]

def rawRow1379 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1000, -2), (key1000, 1), (key994, 1), (key1014, 1), (key994, 1), (key1014, 1), (key1000, 1), (key1035, 2), (key1029, 2), (key1035, 2), (key1035, -1), (key1029, -1), (key1070, -1), (key1029, -1), (key1070, -1), (key1035, -1), (key1113, -1), (key1107, -1), (key1122, -1), (key1107, -1), (key1122, -1), (key1113, -1), (key1113, 1), (key1107, 1), (key1149, 1), (key1107, 1), (key1149, 1), (key1113, 1)]

theorem rawRowCheck1379 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1379 := by decide +kernel

def row1379 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

theorem rowCheck1379 : row1379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1379 := by decide +kernel

theorem rowEval1379 (x : Key → ℝ) : Integer.Sparse.eval row1379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1379, Integer.Sparse.eval_collectBalanced, rawRowCheck1379]

def rawRow1380 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key994, -2), (key1014, 1), (key1014, 1), (key1000, 1), (key1000, 1), (key994, 1), (key994, 1), (key1035, 2), (key1035, 2), (key1029, 2), (key1070, -1), (key1070, -1), (key1035, -1), (key1035, -1), (key1029, -1), (key1029, -1), (key1122, -1), (key1122, -1), (key1113, -1), (key1113, -1), (key1107, -1), (key1107, -1), (key1149, 1), (key1149, 1), (key1113, 1), (key1113, 1), (key1107, 1), (key1107, 1)]

theorem rawRowCheck1380 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1380 := by decide +kernel

def row1380 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

theorem rowCheck1380 : row1380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1380 := by decide +kernel

theorem rowEval1380 (x : Key → ℝ) : Integer.Sparse.eval row1380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1380, Integer.Sparse.eval_collectBalanced, rawRowCheck1380]

def rawRow1381 : Integer.Sparse Key := [(key1014, -2), (key1014, -2), (key1014, -2), (key1000, 1), (key1000, 1), (key1000, 1), (key1000, 1), (key1000, 1), (key1000, 1), (key1070, 2), (key1070, 2), (key1070, 2), (key1035, -1), (key1035, -1), (key1035, -1), (key1035, -1), (key1035, -1), (key1035, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1149, -1), (key1122, 1), (key1122, 1), (key1122, 1), (key1122, 1), (key1122, 1), (key1122, 1)]

theorem rawRowCheck1381 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1381 := by decide +kernel

def row1381 : Integer.Sparse Key := [(key1000, 6), (key1014, -6), (key1035, -6), (key1070, 6), (key1122, 6), (key1149, -6)]

theorem rowCheck1381 : row1381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1381 := by decide +kernel

theorem rowEval1381 (x : Key → ℝ) : Integer.Sparse.eval row1381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1381, Integer.Sparse.eval_collectBalanced, rawRowCheck1381]

def rawRow1382 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1035, -2), (key1107, 1), (key1113, 1), (key1107, 1), (key1122, 1), (key1113, 1), (key1122, 1), (key994, 2), (key1000, 2), (key1000, 2), (key1107, -1), (key1113, -1), (key1107, -1), (key1149, -1), (key1113, -1), (key1149, -1), (key994, -1), (key1000, -1), (key994, -1), (key1014, -1), (key1000, -1), (key1014, -1), (key1029, 1), (key1035, 1), (key1029, 1), (key1070, 1), (key1035, 1), (key1070, 1)]

theorem rawRowCheck1382 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2 = rawRow1382 := by decide +kernel

def row1382 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

theorem rowCheck1382 : row1382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1382 := by decide +kernel

theorem rowEval1382 (x : Key → ℝ) : Integer.Sparse.eval row1382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck1382, Integer.Sparse.eval_collectBalanced, rawRowCheck1382]

def rawRow1383 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1035, -2), (key1113, 1), (key1107, 1), (key1122, 1), (key1107, 1), (key1122, 1), (key1113, 1), (key1000, 2), (key994, 2), (key1000, 2), (key1113, -1), (key1107, -1), (key1149, -1), (key1107, -1), (key1149, -1), (key1113, -1), (key1000, -1), (key994, -1), (key1014, -1), (key994, -1), (key1014, -1), (key1000, -1), (key1035, 1), (key1029, 1), (key1070, 1), (key1029, 1), (key1070, 1), (key1035, 1)]

theorem rawRowCheck1383 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2 = rawRow1383 := by decide +kernel

def row1383 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

theorem rowCheck1383 : row1383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1383 := by decide +kernel

theorem rowEval1383 (x : Key → ℝ) : Integer.Sparse.eval row1383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1383, Integer.Sparse.eval_collectBalanced, rawRowCheck1383]

def rawRow1384 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1029, -2), (key1122, 1), (key1122, 1), (key1113, 1), (key1113, 1), (key1107, 1), (key1107, 1), (key1000, 2), (key1000, 2), (key994, 2), (key1149, -1), (key1149, -1), (key1113, -1), (key1113, -1), (key1107, -1), (key1107, -1), (key1014, -1), (key1014, -1), (key1000, -1), (key1000, -1), (key994, -1), (key994, -1), (key1070, 1), (key1070, 1), (key1035, 1), (key1035, 1), (key1029, 1), (key1029, 1)]

theorem rawRowCheck1384 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2 = rawRow1384 := by decide +kernel

def row1384 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

theorem rowCheck1384 : row1384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1384 := by decide +kernel

theorem rowEval1384 (x : Key → ℝ) : Integer.Sparse.eval row1384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1384, Integer.Sparse.eval_collectBalanced, rawRowCheck1384]

def rawRow1385 : Integer.Sparse Key := [(key1122, -2), (key1122, -2), (key1234, -2), (key1035, 1), (key1035, 1), (key1113, 1), (key1113, 1), (key1231, 1), (key1231, 1), (key1149, 2), (key1149, 2), (key1241, 2), (key1000, -1), (key1000, -1), (key1113, -1), (key1113, -1), (key1231, -1), (key1231, -1), (key1070, -1), (key1070, -1), (key1149, -1), (key1149, -1), (key1241, -1), (key1241, -1), (key1014, 1), (key1014, 1), (key1122, 1), (key1122, 1), (key1234, 1), (key1234, 1)]

theorem rawRowCheck1385 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1385 := by decide +kernel

def row1385 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

theorem rowCheck1385 : row1385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1385 := by decide +kernel

theorem rowEval1385 (x : Key → ℝ) : Integer.Sparse.eval row1385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1385, Integer.Sparse.eval_collectBalanced, rawRowCheck1385]

def rawRow1386 : Integer.Sparse Key := [(key1122, -2), (key1234, -2), (key1122, -2), (key1113, 1), (key1231, 1), (key1035, 1), (key1231, 1), (key1035, 1), (key1113, 1), (key1149, 2), (key1241, 2), (key1149, 2), (key1113, -1), (key1231, -1), (key1000, -1), (key1231, -1), (key1000, -1), (key1113, -1), (key1149, -1), (key1241, -1), (key1070, -1), (key1241, -1), (key1070, -1), (key1149, -1), (key1122, 1), (key1234, 1), (key1014, 1), (key1234, 1), (key1014, 1), (key1122, 1)]

theorem rawRowCheck1386 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1386 := by decide +kernel

def row1386 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

theorem rowCheck1386 : row1386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1386 := by decide +kernel

theorem rowEval1386 (x : Key → ℝ) : Integer.Sparse.eval row1386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1386, Integer.Sparse.eval_collectBalanced, rawRowCheck1386]

def rawRow1387 : Integer.Sparse Key := [(key1234, -2), (key1122, -2), (key1122, -2), (key1231, 1), (key1113, 1), (key1231, 1), (key1035, 1), (key1113, 1), (key1035, 1), (key1241, 2), (key1149, 2), (key1149, 2), (key1231, -1), (key1113, -1), (key1231, -1), (key1000, -1), (key1113, -1), (key1000, -1), (key1241, -1), (key1149, -1), (key1241, -1), (key1070, -1), (key1149, -1), (key1070, -1), (key1234, 1), (key1122, 1), (key1234, 1), (key1014, 1), (key1122, 1), (key1014, 1)]

theorem rawRowCheck1387 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1387 := by decide +kernel

def row1387 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1035, 2), (key1070, -2), (key1122, -2), (key1149, 2)]

theorem rowCheck1387 : row1387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1387 := by decide +kernel

theorem rowEval1387 (x : Key → ℝ) : Integer.Sparse.eval row1387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1387, Integer.Sparse.eval_collectBalanced, rawRowCheck1387]

def rawRow1388 : Integer.Sparse Key := [(key1070, -2), (key1070, -2), (key1070, -2), (key1149, 1), (key1149, 1), (key1149, 1), (key1149, 1), (key1149, 1), (key1149, 1), (key1014, 2), (key1014, 2), (key1014, 2), (key1122, -1), (key1122, -1), (key1122, -1), (key1122, -1), (key1122, -1), (key1122, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1000, -1), (key1035, 1), (key1035, 1), (key1035, 1), (key1035, 1), (key1035, 1), (key1035, 1)]

theorem rawRowCheck1388 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2 = rawRow1388 := by decide +kernel

def row1388 : Integer.Sparse Key := [(key1000, -6), (key1014, 6), (key1035, 6), (key1070, -6), (key1122, -6), (key1149, 6)]

theorem rowCheck1388 : row1388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1388 := by decide +kernel

theorem rowEval1388 (x : Key → ℝ) : Integer.Sparse.eval row1388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1388, Integer.Sparse.eval_collectBalanced, rawRowCheck1388]

def rawRow1389 : Integer.Sparse Key := [(key1149, -2), (key1149, -2), (key1241, -2), (key1070, 1), (key1070, 1), (key1149, 1), (key1149, 1), (key1241, 1), (key1241, 1), (key1122, 2), (key1122, 2), (key1234, 2), (key1014, -1), (key1014, -1), (key1122, -1), (key1122, -1), (key1234, -1), (key1234, -1), (key1035, -1), (key1035, -1), (key1113, -1), (key1113, -1), (key1231, -1), (key1231, -1), (key1000, 1), (key1000, 1), (key1113, 1), (key1113, 1), (key1231, 1), (key1231, 1)]

theorem rawRowCheck1389 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2 = rawRow1389 := by decide +kernel

def row1389 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

theorem rowCheck1389 : row1389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1389 := by decide +kernel

theorem rowEval1389 (x : Key → ℝ) : Integer.Sparse.eval row1389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1389, Integer.Sparse.eval_collectBalanced, rawRowCheck1389]

def rawRow1390 : Integer.Sparse Key := [(key1149, -2), (key1241, -2), (key1149, -2), (key1149, 1), (key1241, 1), (key1070, 1), (key1241, 1), (key1070, 1), (key1149, 1), (key1122, 2), (key1234, 2), (key1122, 2), (key1122, -1), (key1234, -1), (key1014, -1), (key1234, -1), (key1014, -1), (key1122, -1), (key1113, -1), (key1231, -1), (key1035, -1), (key1231, -1), (key1035, -1), (key1113, -1), (key1113, 1), (key1231, 1), (key1000, 1), (key1231, 1), (key1000, 1), (key1113, 1)]

theorem rawRowCheck1390 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2 = rawRow1390 := by decide +kernel

def row1390 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

theorem rowCheck1390 : row1390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1390 := by decide +kernel

theorem rowEval1390 (x : Key → ℝ) : Integer.Sparse.eval row1390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck1390, Integer.Sparse.eval_collectBalanced, rawRowCheck1390]

def rawRow1391 : Integer.Sparse Key := [(key1241, -2), (key1149, -2), (key1149, -2), (key1241, 1), (key1149, 1), (key1241, 1), (key1070, 1), (key1149, 1), (key1070, 1), (key1234, 2), (key1122, 2), (key1122, 2), (key1234, -1), (key1122, -1), (key1234, -1), (key1014, -1), (key1122, -1), (key1014, -1), (key1231, -1), (key1113, -1), (key1231, -1), (key1035, -1), (key1113, -1), (key1035, -1), (key1231, 1), (key1113, 1), (key1231, 1), (key1000, 1), (key1113, 1), (key1000, 1)]

theorem rawRowCheck1391 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2 = rawRow1391 := by decide +kernel

def row1391 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1035, -2), (key1070, 2), (key1122, 2), (key1149, -2)]

theorem rowCheck1391 : row1391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1391 := by decide +kernel

theorem rowEval1391 (x : Key → ℝ) : Integer.Sparse.eval row1391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form2) x := by
  rw [rowCheck1391, Integer.Sparse.eval_collectBalanced, rawRowCheck1391]

def rawRow1392 : Integer.Sparse Key := [(key2, -2), (key6, -2), (key6, -2), (key6, 6), (key85, 2), (key89, 2), (key89, 2), (key89, -2), (key89, -2), (key166, -2), (key150, -6), (key150, 2), (key150, 2), (key186, 2)]

theorem rawRowCheck1392 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1392 := by decide +kernel

def row1392 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck1392 : row1392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1392 := by decide +kernel

theorem rowEval1392 (x : Key → ℝ) : Integer.Sparse.eval row1392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1392, Integer.Sparse.eval_collectBalanced, rawRowCheck1392]

def rawRow1393 : Integer.Sparse Key := [(key6, -2), (key2, -2), (key6, -2), (key6, 6), (key89, 2), (key85, 2), (key89, 2), (key89, -2), (key166, -2), (key89, -2), (key150, -6), (key150, 2), (key186, 2), (key150, 2)]

theorem rawRowCheck1393 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1393 := by decide +kernel

def row1393 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck1393 : row1393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1393 := by decide +kernel

theorem rowEval1393 (x : Key → ℝ) : Integer.Sparse.eval row1393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1393, Integer.Sparse.eval_collectBalanced, rawRowCheck1393]

def rawRow1394 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key2, -2), (key6, 6), (key89, 2), (key89, 2), (key85, 2), (key166, -2), (key89, -2), (key89, -2), (key150, -6), (key186, 2), (key150, 2), (key150, 2)]

theorem rawRowCheck1394 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1394 := by decide +kernel

def row1394 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck1394 : row1394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1394 := by decide +kernel

theorem rowEval1394 (x : Key → ℝ) : Integer.Sparse.eval row1394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1394, Integer.Sparse.eval_collectBalanced, rawRowCheck1394]

def rawRow1395 : Integer.Sparse Key := [(key6, -2), (key6, -2), (key6, -2), (key2, 6), (key166, 2), (key166, 2), (key166, 2), (key85, -2), (key85, -2), (key85, -2), (key186, -6), (key150, 2), (key150, 2), (key150, 2)]

theorem rawRowCheck1395 : GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1395 := by decide +kernel

def row1395 : Integer.Sparse Key := [(key2, 6), (key6, -6), (key85, -6), (key150, 6), (key166, 6), (key186, -6)]

theorem rowCheck1395 : row1395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1395 := by decide +kernel

theorem rowEval1395 (x : Key → ℝ) : Integer.Sparse.eval row1395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1395, Integer.Sparse.eval_collectBalanced, rawRowCheck1395]

def rawRow1396 : Integer.Sparse Key := [(key85, -2), (key89, -2), (key89, -2), (key150, 6), (key2, 2), (key6, 2), (key6, 2), (key150, -2), (key150, -2), (key186, -2), (key6, -6), (key89, 2), (key89, 2), (key166, 2)]

theorem rawRowCheck1396 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3 = rawRow1396 := by decide +kernel

def row1396 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck1396 : row1396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1396 := by decide +kernel

theorem rowEval1396 (x : Key → ℝ) : Integer.Sparse.eval row1396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck1396, Integer.Sparse.eval_collectBalanced, rawRowCheck1396]

def rawRow1397 : Integer.Sparse Key := [(key89, -2), (key85, -2), (key89, -2), (key150, 6), (key6, 2), (key2, 2), (key6, 2), (key150, -2), (key186, -2), (key150, -2), (key6, -6), (key89, 2), (key166, 2), (key89, 2)]

theorem rawRowCheck1397 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3 = rawRow1397 := by decide +kernel

def row1397 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck1397 : row1397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1397 := by decide +kernel

theorem rowEval1397 (x : Key → ℝ) : Integer.Sparse.eval row1397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1397, Integer.Sparse.eval_collectBalanced, rawRowCheck1397]

def rawRow1398 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key85, -2), (key150, 6), (key6, 2), (key6, 2), (key2, 2), (key186, -2), (key150, -2), (key150, -2), (key6, -6), (key166, 2), (key89, 2), (key89, 2)]

theorem rawRowCheck1398 : GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3 = rawRow1398 := by decide +kernel

def row1398 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck1398 : row1398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1398 := by decide +kernel

theorem rowEval1398 (x : Key → ℝ) : Integer.Sparse.eval row1398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1398, Integer.Sparse.eval_collectBalanced, rawRowCheck1398]

def rawRow1399 : Integer.Sparse Key := [(key89, -2), (key89, -2), (key150, -2), (key85, 6), (key166, 2), (key166, 2), (key186, 2), (key2, -2), (key85, -2), (key85, -2), (key166, -6), (key6, 2), (key89, 2), (key89, 2)]

theorem rawRowCheck1399 : GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1399 := by decide +kernel

def row1399 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck1399 : row1399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1399 := by decide +kernel

theorem rowEval1399 (x : Key → ℝ) : Integer.Sparse.eval row1399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1399, Integer.Sparse.eval_collectBalanced, rawRowCheck1399]

def rawRow1400 : Integer.Sparse Key := [(key89, -2), (key150, -2), (key89, -2), (key85, 6), (key166, 2), (key186, 2), (key166, 2), (key85, -2), (key2, -2), (key85, -2), (key166, -6), (key89, 2), (key6, 2), (key89, 2)]

theorem rawRowCheck1400 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1400 := by decide +kernel

def row1400 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck1400 : row1400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1400 := by decide +kernel

theorem rowEval1400 (x : Key → ℝ) : Integer.Sparse.eval row1400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1400, Integer.Sparse.eval_collectBalanced, rawRowCheck1400]

def rawRow1401 : Integer.Sparse Key := [(key150, -2), (key89, -2), (key89, -2), (key85, 6), (key186, 2), (key166, 2), (key166, 2), (key85, -2), (key85, -2), (key2, -2), (key166, -6), (key89, 2), (key89, 2), (key6, 2)]

theorem rawRowCheck1401 : GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1401 := by decide +kernel

def row1401 : Integer.Sparse Key := [(key2, -2), (key6, 2), (key85, 2), (key150, -2), (key166, -2), (key186, 2)]

theorem rowCheck1401 : row1401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1401 := by decide +kernel

theorem rowEval1401 (x : Key → ℝ) : Integer.Sparse.eval row1401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1401, Integer.Sparse.eval_collectBalanced, rawRowCheck1401]

def rawRow1402 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key166, -2), (key186, 6), (key6, 2), (key6, 2), (key6, 2), (key150, -2), (key150, -2), (key150, -2), (key2, -6), (key85, 2), (key85, 2), (key85, 2)]

theorem rawRowCheck1402 : GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3 = rawRow1402 := by decide +kernel

def row1402 : Integer.Sparse Key := [(key2, -6), (key6, 6), (key85, 6), (key150, -6), (key166, -6), (key186, 6)]

theorem rowCheck1402 : row1402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1402 := by decide +kernel

theorem rowEval1402 (x : Key → ℝ) : Integer.Sparse.eval row1402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1402, Integer.Sparse.eval_collectBalanced, rawRowCheck1402]

def rawRow1403 : Integer.Sparse Key := [(key166, -2), (key166, -2), (key186, -2), (key166, 6), (key89, 2), (key89, 2), (key150, 2), (key6, -2), (key89, -2), (key89, -2), (key85, -6), (key2, 2), (key85, 2), (key85, 2)]

theorem rawRowCheck1403 : GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3 = rawRow1403 := by decide +kernel

def row1403 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck1403 : row1403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1403 := by decide +kernel

theorem rowEval1403 (x : Key → ℝ) : Integer.Sparse.eval row1403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1403, Integer.Sparse.eval_collectBalanced, rawRowCheck1403]

def rawRow1404 : Integer.Sparse Key := [(key166, -2), (key186, -2), (key166, -2), (key166, 6), (key89, 2), (key150, 2), (key89, 2), (key89, -2), (key6, -2), (key89, -2), (key85, -6), (key85, 2), (key2, 2), (key85, 2)]

theorem rawRowCheck1404 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3 = rawRow1404 := by decide +kernel

def row1404 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck1404 : row1404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1404 := by decide +kernel

theorem rowEval1404 (x : Key → ℝ) : Integer.Sparse.eval row1404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck1404, Integer.Sparse.eval_collectBalanced, rawRowCheck1404]

def rawRow1405 : Integer.Sparse Key := [(key186, -2), (key166, -2), (key166, -2), (key166, 6), (key150, 2), (key89, 2), (key89, 2), (key89, -2), (key89, -2), (key6, -2), (key85, -6), (key85, 2), (key85, 2), (key2, 2)]

theorem rawRowCheck1405 : GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3 = rawRow1405 := by decide +kernel

def row1405 : Integer.Sparse Key := [(key2, 2), (key6, -2), (key85, -2), (key150, 2), (key166, 2), (key186, -2)]

theorem rowCheck1405 : row1405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1405 := by decide +kernel

theorem rowEval1405 (x : Key → ℝ) : Integer.Sparse.eval row1405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form3) x := by
  rw [rowCheck1405, Integer.Sparse.eval_collectBalanced, rawRowCheck1405]

def rawRow1406 : Integer.Sparse Key := [(key992, -6), (key992, 2), (key992, 2), (key1010, 2), (key1027, 6), (key1027, -2), (key1027, -2), (key1066, -2), (key1105, -2), (key1105, -2), (key1118, -2), (key1105, 2), (key1105, 2), (key1145, 2)]

theorem rawRowCheck1406 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4 = rawRow1406 := by decide +kernel

def row1406 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

theorem rowCheck1406 : row1406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1406 := by decide +kernel

theorem rowEval1406 (x : Key → ℝ) : Integer.Sparse.eval row1406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1406, Integer.Sparse.eval_collectBalanced, rawRowCheck1406]

def rawRow1407 : Integer.Sparse Key := [(key992, -6), (key992, 2), (key1010, 2), (key992, 2), (key1027, 6), (key1027, -2), (key1066, -2), (key1027, -2), (key1105, -2), (key1118, -2), (key1105, -2), (key1105, 2), (key1145, 2), (key1105, 2)]

theorem rawRowCheck1407 : GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4 = rawRow1407 := by decide +kernel

def row1407 : Integer.Sparse Key := [(key992, -2), (key1010, 2), (key1027, 2), (key1066, -2), (key1118, -2), (key1145, 2)]

theorem rowCheck1407 : row1407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow1407 := by decide +kernel

theorem rowEval1407 (x : Key → ℝ) : Integer.Sparse.eval row1407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1407, Integer.Sparse.eval_collectBalanced, rawRowCheck1407]

end MUB6.Certificate.GramRows

end OAI
