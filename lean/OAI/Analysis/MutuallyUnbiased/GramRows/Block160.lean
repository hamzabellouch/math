import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17408 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key793, -2), (key768, -2), (key793, -2), (key769, -2), (key793, 2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key793, 2), (key766, 2), (key759, 2), (key766, 2), (key766, -6), (key761, 2), (key757, 2), (key761, 2), (key761, -6)]

theorem rawRowCheck17408 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form18 = rawRow17408 := by decide +kernel

def row17408 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

theorem rowCheck17408 : row17408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17408 := by decide +kernel

theorem rowEval17408 (x : Key → ℝ) : Integer.Sparse.eval row17408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17408, Integer.Sparse.eval_collectBalanced, rawRowCheck17408]

def rawRow17409 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key769, -2), (key769, -2), (key768, -2), (key768, -2), (key793, 2), (key793, 2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key766, 2), (key766, 2), (key759, 2), (key766, -6), (key761, 2), (key761, 2), (key757, 2), (key761, -6)]

theorem rawRowCheck17409 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form18 = rawRow17409 := by decide +kernel

def row17409 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

theorem rowCheck17409 : row17409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17409 := by decide +kernel

theorem rowEval17409 (x : Key → ℝ) : Integer.Sparse.eval row17409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17409, Integer.Sparse.eval_collectBalanced, rawRowCheck17409]

def rawRow17410 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key769, 2), (key769, 2), (key769, 2), (key768, 2), (key768, 2), (key768, 2), (key766, 2), (key766, 2), (key766, 2), (key759, -6), (key761, 2), (key761, 2), (key761, 2), (key757, -6)]

theorem rawRowCheck17410 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form18 = rawRow17410 := by decide +kernel

def row17410 : Integer.Sparse Key := [(key757, -6), (key759, -6), (key761, 6), (key766, 6), (key768, 6), (key769, 6), (key793, -12)]

theorem rowCheck17410 : row17410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17410 := by decide +kernel

theorem rowEval17410 (x : Key → ℝ) : Integer.Sparse.eval row17410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17410, Integer.Sparse.eval_collectBalanced, rawRowCheck17410]

def rawRow17411 : Integer.Sparse Key := [(key1854, 4), (key1887, 4), (key1887, 4), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1890, -2), (key1858, 4), (key1890, 4), (key1890, 4)]

theorem rawRowCheck17411 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form0 = rawRow17411 := by decide +kernel

def row17411 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

theorem rowCheck17411 : row17411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17411 := by decide +kernel

theorem rowEval17411 (x : Key → ℝ) : Integer.Sparse.eval row17411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17411, Integer.Sparse.eval_collectBalanced, rawRowCheck17411]

def rawRow17412 : Integer.Sparse Key := [(key1887, 4), (key1854, 4), (key1887, 4), (key1887, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1890, 4), (key1858, 4), (key1890, 4)]

theorem rawRowCheck17412 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form0 = rawRow17412 := by decide +kernel

def row17412 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

theorem rowCheck17412 : row17412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17412 := by decide +kernel

theorem rowEval17412 (x : Key → ℝ) : Integer.Sparse.eval row17412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17412, Integer.Sparse.eval_collectBalanced, rawRowCheck17412]

def rawRow17413 : Integer.Sparse Key := [(key1887, 4), (key1887, 4), (key1854, 4), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1890, -2), (key1887, -2), (key1890, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1890, 4), (key1890, 4), (key1858, 4)]

theorem rawRowCheck17413 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form0 = rawRow17413 := by decide +kernel

def row17413 : Integer.Sparse Key := [(key1854, 4), (key1856, -8), (key1858, 4)]

theorem rowCheck17413 : row17413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17413 := by decide +kernel

theorem rowEval17413 (x : Key → ℝ) : Integer.Sparse.eval row17413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17413, Integer.Sparse.eval_collectBalanced, rawRowCheck17413]

def rawRow17414 : Integer.Sparse Key := [(key1856, 4), (key1856, 4), (key1890, 4), (key1854, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1887, -2), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1890, -2), (key1856, 4), (key1856, 4), (key1887, 4)]

theorem rawRowCheck17414 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17414 := by decide +kernel

def row17414 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

theorem rowCheck17414 : row17414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17414 := by decide +kernel

theorem rowEval17414 (x : Key → ℝ) : Integer.Sparse.eval row17414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17414, Integer.Sparse.eval_collectBalanced, rawRowCheck17414]

def rawRow17415 : Integer.Sparse Key := [(key1856, 4), (key1890, 4), (key1856, 4), (key1856, -2), (key1854, -2), (key1887, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1856, 4), (key1887, 4), (key1856, 4)]

theorem rawRowCheck17415 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17415 := by decide +kernel

def row17415 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

theorem rowCheck17415 : row17415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17415 := by decide +kernel

theorem rowEval17415 (x : Key → ℝ) : Integer.Sparse.eval row17415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17415, Integer.Sparse.eval_collectBalanced, rawRowCheck17415]

def rawRow17416 : Integer.Sparse Key := [(key1890, 4), (key1856, 4), (key1856, 4), (key1887, -2), (key1887, -2), (key1856, -2), (key1856, -2), (key1854, -2), (key1854, -2), (key1890, -2), (key1890, -2), (key1858, -2), (key1858, -2), (key1856, -2), (key1856, -2), (key1887, 4), (key1856, 4), (key1856, 4)]

theorem rawRowCheck17416 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17416 := by decide +kernel

def row17416 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

theorem rowCheck17416 : row17416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17416 := by decide +kernel

theorem rowEval17416 (x : Key → ℝ) : Integer.Sparse.eval row17416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17416, Integer.Sparse.eval_collectBalanced, rawRowCheck17416]

def rawRow17417 : Integer.Sparse Key := [(key1856, 4), (key1856, 4), (key1890, 4), (key1856, -2), (key1858, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1890, -2), (key1854, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1887, -2), (key1856, 4), (key1856, 4), (key1887, 4)]

theorem rawRowCheck17417 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form0 = rawRow17417 := by decide +kernel

def row17417 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

theorem rowCheck17417 : row17417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17417 := by decide +kernel

theorem rowEval17417 (x : Key → ℝ) : Integer.Sparse.eval row17417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck17417, Integer.Sparse.eval_collectBalanced, rawRowCheck17417]

def rawRow17418 : Integer.Sparse Key := [(key1856, 4), (key1890, 4), (key1856, 4), (key1858, -2), (key1856, -2), (key1890, -2), (key1856, -2), (key1890, -2), (key1858, -2), (key1856, -2), (key1854, -2), (key1887, -2), (key1854, -2), (key1887, -2), (key1856, -2), (key1856, 4), (key1887, 4), (key1856, 4)]

theorem rawRowCheck17418 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form0 = rawRow17418 := by decide +kernel

def row17418 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

theorem rowCheck17418 : row17418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17418 := by decide +kernel

theorem rowEval17418 (x : Key → ℝ) : Integer.Sparse.eval row17418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17418, Integer.Sparse.eval_collectBalanced, rawRowCheck17418]

def rawRow17419 : Integer.Sparse Key := [(key1890, 4), (key1856, 4), (key1856, 4), (key1890, -2), (key1890, -2), (key1858, -2), (key1858, -2), (key1856, -2), (key1856, -2), (key1887, -2), (key1887, -2), (key1856, -2), (key1856, -2), (key1854, -2), (key1854, -2), (key1887, 4), (key1856, 4), (key1856, 4)]

theorem rawRowCheck17419 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form0 = rawRow17419 := by decide +kernel

def row17419 : Integer.Sparse Key := [(key1854, -4), (key1856, 8), (key1858, -4)]

theorem rowCheck17419 : row17419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17419 := by decide +kernel

theorem rowEval17419 (x : Key → ℝ) : Integer.Sparse.eval row17419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17419, Integer.Sparse.eval_collectBalanced, rawRowCheck17419]

def rawRow17420 : Integer.Sparse Key := [(key1858, 4), (key1858, 4), (key1858, 4), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1856, -2), (key1854, 4), (key1854, 4), (key1854, 4)]

theorem rawRowCheck17420 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow17420 := by decide +kernel

def row17420 : Integer.Sparse Key := [(key1854, 12), (key1856, -24), (key1858, 12)]

theorem rowCheck17420 : row17420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17420 := by decide +kernel

theorem rowEval17420 (x : Key → ℝ) : Integer.Sparse.eval row17420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck17420, Integer.Sparse.eval_collectBalanced, rawRowCheck17420]

def rawRow17421 : Integer.Sparse Key := [(key620, -2), (key620, -2), (key624, -2), (key624, 6), (key620, -2), (key620, -2), (key624, -2), (key620, 2), (key620, 2), (key646, 2), (key646, 2), (key652, 2), (key652, 2), (key624, -2), (key652, -2), (key652, -2), (key624, 6), (key624, -2), (key652, -2), (key652, -2)]

theorem rawRowCheck17421 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form1 = rawRow17421 := by decide +kernel

def row17421 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

theorem rowCheck17421 : row17421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17421 := by decide +kernel

theorem rowEval17421 (x : Key → ℝ) : Integer.Sparse.eval row17421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17421, Integer.Sparse.eval_collectBalanced, rawRowCheck17421]

def rawRow17422 : Integer.Sparse Key := [(key620, -2), (key624, -2), (key620, -2), (key624, 6), (key620, -2), (key624, -2), (key620, -2), (key646, 2), (key652, 2), (key620, 2), (key652, 2), (key620, 2), (key646, 2), (key652, -2), (key624, -2), (key652, -2), (key624, 6), (key652, -2), (key624, -2), (key652, -2)]

theorem rawRowCheck17422 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form1 = rawRow17422 := by decide +kernel

def row17422 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

theorem rowCheck17422 : row17422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17422 := by decide +kernel

theorem rowEval17422 (x : Key → ℝ) : Integer.Sparse.eval row17422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17422, Integer.Sparse.eval_collectBalanced, rawRowCheck17422]

def rawRow17423 : Integer.Sparse Key := [(key624, -2), (key620, -2), (key620, -2), (key624, 6), (key624, -2), (key620, -2), (key620, -2), (key652, 2), (key646, 2), (key652, 2), (key620, 2), (key646, 2), (key620, 2), (key652, -2), (key652, -2), (key624, -2), (key624, 6), (key652, -2), (key652, -2), (key624, -2)]

theorem rawRowCheck17423 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form1 = rawRow17423 := by decide +kernel

def row17423 : Integer.Sparse Key := [(key620, -4), (key624, 4), (key646, 4), (key652, -4)]

theorem rowCheck17423 : row17423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17423 := by decide +kernel

theorem rowEval17423 (x : Key → ℝ) : Integer.Sparse.eval row17423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17423, Integer.Sparse.eval_collectBalanced, rawRowCheck17423]

def rawRow17424 : Integer.Sparse Key := [(key620, -2), (key624, -2), (key624, -2), (key620, 6), (key646, -2), (key652, -2), (key652, -2), (key620, 2), (key624, 2), (key620, 2), (key652, 2), (key624, 2), (key652, 2), (key620, -2), (key620, -2), (key646, -2), (key652, 6), (key624, -2), (key624, -2), (key652, -2)]

theorem rawRowCheck17424 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17424 := by decide +kernel

def row17424 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

theorem rowCheck17424 : row17424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17424 := by decide +kernel

theorem rowEval17424 (x : Key → ℝ) : Integer.Sparse.eval row17424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17424, Integer.Sparse.eval_collectBalanced, rawRowCheck17424]

def rawRow17425 : Integer.Sparse Key := [(key624, -2), (key620, -2), (key624, -2), (key620, 6), (key652, -2), (key646, -2), (key652, -2), (key624, 2), (key620, 2), (key652, 2), (key620, 2), (key652, 2), (key624, 2), (key620, -2), (key646, -2), (key620, -2), (key652, 6), (key624, -2), (key652, -2), (key624, -2)]

theorem rawRowCheck17425 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17425 := by decide +kernel

def row17425 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

theorem rowCheck17425 : row17425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17425 := by decide +kernel

theorem rowEval17425 (x : Key → ℝ) : Integer.Sparse.eval row17425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17425, Integer.Sparse.eval_collectBalanced, rawRowCheck17425]

def rawRow17426 : Integer.Sparse Key := [(key624, -2), (key624, -2), (key620, -2), (key620, 6), (key652, -2), (key652, -2), (key646, -2), (key652, 2), (key652, 2), (key624, 2), (key624, 2), (key620, 2), (key620, 2), (key646, -2), (key620, -2), (key620, -2), (key652, 6), (key652, -2), (key624, -2), (key624, -2)]

theorem rawRowCheck17426 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17426 := by decide +kernel

def row17426 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

theorem rowCheck17426 : row17426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17426 := by decide +kernel

theorem rowEval17426 (x : Key → ℝ) : Integer.Sparse.eval row17426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17426, Integer.Sparse.eval_collectBalanced, rawRowCheck17426]

def rawRow17427 : Integer.Sparse Key := [(key646, -2), (key652, -2), (key652, -2), (key652, 6), (key620, -2), (key624, -2), (key624, -2), (key620, 2), (key624, 2), (key620, 2), (key652, 2), (key624, 2), (key652, 2), (key624, -2), (key624, -2), (key652, -2), (key620, 6), (key620, -2), (key620, -2), (key646, -2)]

theorem rawRowCheck17427 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form1 = rawRow17427 := by decide +kernel

def row17427 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

theorem rowCheck17427 : row17427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17427 := by decide +kernel

theorem rowEval17427 (x : Key → ℝ) : Integer.Sparse.eval row17427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck17427, Integer.Sparse.eval_collectBalanced, rawRowCheck17427]

def rawRow17428 : Integer.Sparse Key := [(key652, -2), (key646, -2), (key652, -2), (key652, 6), (key624, -2), (key620, -2), (key624, -2), (key624, 2), (key620, 2), (key652, 2), (key620, 2), (key652, 2), (key624, 2), (key624, -2), (key652, -2), (key624, -2), (key620, 6), (key620, -2), (key646, -2), (key620, -2)]

theorem rawRowCheck17428 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form1 = rawRow17428 := by decide +kernel

def row17428 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

theorem rowCheck17428 : row17428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17428 := by decide +kernel

theorem rowEval17428 (x : Key → ℝ) : Integer.Sparse.eval row17428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17428, Integer.Sparse.eval_collectBalanced, rawRowCheck17428]

def rawRow17429 : Integer.Sparse Key := [(key652, -2), (key652, -2), (key646, -2), (key652, 6), (key624, -2), (key624, -2), (key620, -2), (key652, 2), (key652, 2), (key624, 2), (key624, 2), (key620, 2), (key620, 2), (key652, -2), (key624, -2), (key624, -2), (key620, 6), (key646, -2), (key620, -2), (key620, -2)]

theorem rawRowCheck17429 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form1 = rawRow17429 := by decide +kernel

def row17429 : Integer.Sparse Key := [(key620, 4), (key624, -4), (key646, -4), (key652, 4)]

theorem rowCheck17429 : row17429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17429 := by decide +kernel

theorem rowEval17429 (x : Key → ℝ) : Integer.Sparse.eval row17429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17429, Integer.Sparse.eval_collectBalanced, rawRowCheck17429]

def rawRow17430 : Integer.Sparse Key := [(key652, -2), (key652, -2), (key652, -2), (key646, 6), (key652, -2), (key652, -2), (key652, -2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key624, 2), (key620, -2), (key620, -2), (key620, -2), (key646, 6), (key620, -2), (key620, -2), (key620, -2)]

theorem rawRowCheck17430 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form1 = rawRow17430 := by decide +kernel

def row17430 : Integer.Sparse Key := [(key620, -12), (key624, 12), (key646, 12), (key652, -12)]

theorem rowCheck17430 : row17430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17430 := by decide +kernel

theorem rowEval17430 (x : Key → ℝ) : Integer.Sparse.eval row17430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck17430, Integer.Sparse.eval_collectBalanced, rawRowCheck17430]

def rawRow17431 : Integer.Sparse Key := [(key1853, -2), (key1853, -2), (key1857, -2), (key1857, 6), (key1853, -2), (key1853, -2), (key1857, -2), (key1853, 2), (key1853, 2), (key1885, 2), (key1885, 2), (key1888, 2), (key1888, 2), (key1857, -2), (key1888, -2), (key1888, -2), (key1857, 6), (key1857, -2), (key1888, -2), (key1888, -2)]

theorem rawRowCheck17431 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form2 = rawRow17431 := by decide +kernel

def row17431 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

theorem rowCheck17431 : row17431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17431 := by decide +kernel

theorem rowEval17431 (x : Key → ℝ) : Integer.Sparse.eval row17431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17431, Integer.Sparse.eval_collectBalanced, rawRowCheck17431]

def rawRow17432 : Integer.Sparse Key := [(key1853, -2), (key1857, -2), (key1853, -2), (key1857, 6), (key1853, -2), (key1857, -2), (key1853, -2), (key1885, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1885, 2), (key1888, -2), (key1857, -2), (key1888, -2), (key1857, 6), (key1888, -2), (key1857, -2), (key1888, -2)]

theorem rawRowCheck17432 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form2 = rawRow17432 := by decide +kernel

def row17432 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

theorem rowCheck17432 : row17432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17432 := by decide +kernel

theorem rowEval17432 (x : Key → ℝ) : Integer.Sparse.eval row17432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17432, Integer.Sparse.eval_collectBalanced, rawRowCheck17432]

def rawRow17433 : Integer.Sparse Key := [(key1857, -2), (key1853, -2), (key1853, -2), (key1857, 6), (key1857, -2), (key1853, -2), (key1853, -2), (key1888, 2), (key1885, 2), (key1888, 2), (key1853, 2), (key1885, 2), (key1853, 2), (key1888, -2), (key1888, -2), (key1857, -2), (key1857, 6), (key1888, -2), (key1888, -2), (key1857, -2)]

theorem rawRowCheck17433 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form2 = rawRow17433 := by decide +kernel

def row17433 : Integer.Sparse Key := [(key1853, -4), (key1857, 4), (key1885, 4), (key1888, -4)]

theorem rowCheck17433 : row17433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17433 := by decide +kernel

theorem rowEval17433 (x : Key → ℝ) : Integer.Sparse.eval row17433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17433, Integer.Sparse.eval_collectBalanced, rawRowCheck17433]

def rawRow17434 : Integer.Sparse Key := [(key1853, -2), (key1857, -2), (key1857, -2), (key1853, 6), (key1885, -2), (key1888, -2), (key1888, -2), (key1853, 2), (key1857, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1888, 2), (key1853, -2), (key1853, -2), (key1885, -2), (key1888, 6), (key1857, -2), (key1857, -2), (key1888, -2)]

theorem rawRowCheck17434 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17434 := by decide +kernel

def row17434 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

theorem rowCheck17434 : row17434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17434 := by decide +kernel

theorem rowEval17434 (x : Key → ℝ) : Integer.Sparse.eval row17434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17434, Integer.Sparse.eval_collectBalanced, rawRowCheck17434]

def rawRow17435 : Integer.Sparse Key := [(key1857, -2), (key1853, -2), (key1857, -2), (key1853, 6), (key1888, -2), (key1885, -2), (key1888, -2), (key1857, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1853, -2), (key1885, -2), (key1853, -2), (key1888, 6), (key1857, -2), (key1888, -2), (key1857, -2)]

theorem rawRowCheck17435 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17435 := by decide +kernel

def row17435 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

theorem rowCheck17435 : row17435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17435 := by decide +kernel

theorem rowEval17435 (x : Key → ℝ) : Integer.Sparse.eval row17435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17435, Integer.Sparse.eval_collectBalanced, rawRowCheck17435]

def rawRow17436 : Integer.Sparse Key := [(key1857, -2), (key1857, -2), (key1853, -2), (key1853, 6), (key1888, -2), (key1888, -2), (key1885, -2), (key1888, 2), (key1888, 2), (key1857, 2), (key1857, 2), (key1853, 2), (key1853, 2), (key1885, -2), (key1853, -2), (key1853, -2), (key1888, 6), (key1888, -2), (key1857, -2), (key1857, -2)]

theorem rawRowCheck17436 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17436 := by decide +kernel

def row17436 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

theorem rowCheck17436 : row17436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17436 := by decide +kernel

theorem rowEval17436 (x : Key → ℝ) : Integer.Sparse.eval row17436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17436, Integer.Sparse.eval_collectBalanced, rawRowCheck17436]

def rawRow17437 : Integer.Sparse Key := [(key1885, -2), (key1888, -2), (key1888, -2), (key1888, 6), (key1853, -2), (key1857, -2), (key1857, -2), (key1853, 2), (key1857, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1888, 2), (key1857, -2), (key1857, -2), (key1888, -2), (key1853, 6), (key1853, -2), (key1853, -2), (key1885, -2)]

theorem rawRowCheck17437 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form2 = rawRow17437 := by decide +kernel

def row17437 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

theorem rowCheck17437 : row17437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17437 := by decide +kernel

theorem rowEval17437 (x : Key → ℝ) : Integer.Sparse.eval row17437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form2) x := by
  rw [rowCheck17437, Integer.Sparse.eval_collectBalanced, rawRowCheck17437]

def rawRow17438 : Integer.Sparse Key := [(key1888, -2), (key1885, -2), (key1888, -2), (key1888, 6), (key1857, -2), (key1853, -2), (key1857, -2), (key1857, 2), (key1853, 2), (key1888, 2), (key1853, 2), (key1888, 2), (key1857, 2), (key1857, -2), (key1888, -2), (key1857, -2), (key1853, 6), (key1853, -2), (key1885, -2), (key1853, -2)]

theorem rawRowCheck17438 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form2 = rawRow17438 := by decide +kernel

def row17438 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

theorem rowCheck17438 : row17438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17438 := by decide +kernel

theorem rowEval17438 (x : Key → ℝ) : Integer.Sparse.eval row17438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17438, Integer.Sparse.eval_collectBalanced, rawRowCheck17438]

def rawRow17439 : Integer.Sparse Key := [(key1888, -2), (key1888, -2), (key1885, -2), (key1888, 6), (key1857, -2), (key1857, -2), (key1853, -2), (key1888, 2), (key1888, 2), (key1857, 2), (key1857, 2), (key1853, 2), (key1853, 2), (key1888, -2), (key1857, -2), (key1857, -2), (key1853, 6), (key1885, -2), (key1853, -2), (key1853, -2)]

theorem rawRowCheck17439 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form2 = rawRow17439 := by decide +kernel

def row17439 : Integer.Sparse Key := [(key1853, 4), (key1857, -4), (key1885, -4), (key1888, 4)]

theorem rowCheck17439 : row17439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17439 := by decide +kernel

theorem rowEval17439 (x : Key → ℝ) : Integer.Sparse.eval row17439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17439, Integer.Sparse.eval_collectBalanced, rawRowCheck17439]

def rawRow17440 : Integer.Sparse Key := [(key1888, -2), (key1888, -2), (key1888, -2), (key1885, 6), (key1888, -2), (key1888, -2), (key1888, -2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1857, 2), (key1853, -2), (key1853, -2), (key1853, -2), (key1885, 6), (key1853, -2), (key1853, -2), (key1853, -2)]

theorem rawRowCheck17440 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form2 = rawRow17440 := by decide +kernel

def row17440 : Integer.Sparse Key := [(key1853, -12), (key1857, 12), (key1885, 12), (key1888, -12)]

theorem rowCheck17440 : row17440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17440 := by decide +kernel

theorem rowEval17440 (x : Key → ℝ) : Integer.Sparse.eval row17440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck17440, Integer.Sparse.eval_collectBalanced, rawRowCheck17440]

def rawRow17441 : Integer.Sparse Key := [(key1959, 6), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, 6), (key1959, -2), (key1967, -2), (key1967, -2), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1961, 2), (key1961, 2), (key1967, 2), (key1967, 2), (key1970, 2), (key1970, 2)]

theorem rawRowCheck17441 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form3 = rawRow17441 := by decide +kernel

def row17441 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

theorem rowCheck17441 : row17441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17441 := by decide +kernel

theorem rowEval17441 (x : Key → ℝ) : Integer.Sparse.eval row17441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17441, Integer.Sparse.eval_collectBalanced, rawRowCheck17441]

def rawRow17442 : Integer.Sparse Key := [(key1959, 6), (key1961, -2), (key1959, -2), (key1961, -2), (key1959, 6), (key1967, -2), (key1959, -2), (key1967, -2), (key1961, -2), (key1959, -2), (key1961, -2), (key1967, -2), (key1959, -2), (key1967, -2), (key1967, 2), (key1970, 2), (key1961, 2), (key1970, 2), (key1961, 2), (key1967, 2)]

theorem rawRowCheck17442 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form3 = rawRow17442 := by decide +kernel

def row17442 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

theorem rowCheck17442 : row17442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17442 := by decide +kernel

theorem rowEval17442 (x : Key → ℝ) : Integer.Sparse.eval row17442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17442, Integer.Sparse.eval_collectBalanced, rawRowCheck17442]

def rawRow17443 : Integer.Sparse Key := [(key1959, 6), (key1961, -2), (key1961, -2), (key1959, -2), (key1959, 6), (key1967, -2), (key1967, -2), (key1959, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1959, -2), (key1970, 2), (key1967, 2), (key1970, 2), (key1961, 2), (key1967, 2), (key1961, 2)]

theorem rawRowCheck17443 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form3 = rawRow17443 := by decide +kernel

def row17443 : Integer.Sparse Key := [(key1959, 4), (key1961, -4), (key1967, -4), (key1970, 4)]

theorem rowCheck17443 : row17443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17443 := by decide +kernel

theorem rowEval17443 (x : Key → ℝ) : Integer.Sparse.eval row17443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17443, Integer.Sparse.eval_collectBalanced, rawRowCheck17443]

def rawRow17444 : Integer.Sparse Key := [(key1961, 6), (key1959, -2), (key1959, -2), (key1961, -2), (key1967, 6), (key1959, -2), (key1959, -2), (key1967, -2), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, -2), (key1961, -2), (key1970, -2), (key1959, 2), (key1961, 2), (key1959, 2), (key1967, 2), (key1961, 2), (key1967, 2)]

theorem rawRowCheck17444 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17444 := by decide +kernel

def row17444 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

theorem rowCheck17444 : row17444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17444 := by decide +kernel

theorem rowEval17444 (x : Key → ℝ) : Integer.Sparse.eval row17444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17444, Integer.Sparse.eval_collectBalanced, rawRowCheck17444]

def rawRow17445 : Integer.Sparse Key := [(key1961, 6), (key1959, -2), (key1961, -2), (key1959, -2), (key1967, 6), (key1959, -2), (key1967, -2), (key1959, -2), (key1967, -2), (key1970, -2), (key1967, -2), (key1961, -2), (key1970, -2), (key1961, -2), (key1961, 2), (key1959, 2), (key1967, 2), (key1959, 2), (key1967, 2), (key1961, 2)]

theorem rawRowCheck17445 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17445 := by decide +kernel

def row17445 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

theorem rowCheck17445 : row17445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17445 := by decide +kernel

theorem rowEval17445 (x : Key → ℝ) : Integer.Sparse.eval row17445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17445, Integer.Sparse.eval_collectBalanced, rawRowCheck17445]

def rawRow17446 : Integer.Sparse Key := [(key1961, 6), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, 6), (key1967, -2), (key1959, -2), (key1959, -2), (key1970, -2), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, -2), (key1961, -2), (key1967, 2), (key1967, 2), (key1961, 2), (key1961, 2), (key1959, 2), (key1959, 2)]

theorem rawRowCheck17446 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17446 := by decide +kernel

def row17446 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

theorem rowCheck17446 : row17446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17446 := by decide +kernel

theorem rowEval17446 (x : Key → ℝ) : Integer.Sparse.eval row17446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17446, Integer.Sparse.eval_collectBalanced, rawRowCheck17446]

def rawRow17447 : Integer.Sparse Key := [(key1967, 6), (key1967, -2), (key1967, -2), (key1970, -2), (key1961, 6), (key1961, -2), (key1961, -2), (key1970, -2), (key1959, -2), (key1959, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, 2), (key1961, 2), (key1959, 2), (key1967, 2), (key1961, 2), (key1967, 2)]

theorem rawRowCheck17447 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form3 = rawRow17447 := by decide +kernel

def row17447 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

theorem rowCheck17447 : row17447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17447 := by decide +kernel

theorem rowEval17447 (x : Key → ℝ) : Integer.Sparse.eval row17447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form3) x := by
  rw [rowCheck17447, Integer.Sparse.eval_collectBalanced, rawRowCheck17447]

def rawRow17448 : Integer.Sparse Key := [(key1967, 6), (key1967, -2), (key1970, -2), (key1967, -2), (key1961, 6), (key1961, -2), (key1970, -2), (key1961, -2), (key1959, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, -2), (key1961, 2), (key1959, 2), (key1967, 2), (key1959, 2), (key1967, 2), (key1961, 2)]

theorem rawRowCheck17448 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form3 = rawRow17448 := by decide +kernel

def row17448 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

theorem rowCheck17448 : row17448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17448 := by decide +kernel

theorem rowEval17448 (x : Key → ℝ) : Integer.Sparse.eval row17448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17448, Integer.Sparse.eval_collectBalanced, rawRowCheck17448]

def rawRow17449 : Integer.Sparse Key := [(key1967, 6), (key1970, -2), (key1967, -2), (key1967, -2), (key1961, 6), (key1970, -2), (key1961, -2), (key1961, -2), (key1961, -2), (key1959, -2), (key1959, -2), (key1967, -2), (key1959, -2), (key1959, -2), (key1967, 2), (key1967, 2), (key1961, 2), (key1961, 2), (key1959, 2), (key1959, 2)]

theorem rawRowCheck17449 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form3 = rawRow17449 := by decide +kernel

def row17449 : Integer.Sparse Key := [(key1959, -4), (key1961, 4), (key1967, 4), (key1970, -4)]

theorem rowCheck17449 : row17449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17449 := by decide +kernel

theorem rowEval17449 (x : Key → ℝ) : Integer.Sparse.eval row17449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17449, Integer.Sparse.eval_collectBalanced, rawRowCheck17449]

def rawRow17450 : Integer.Sparse Key := [(key1970, 6), (key1967, -2), (key1967, -2), (key1967, -2), (key1970, 6), (key1961, -2), (key1961, -2), (key1961, -2), (key1967, -2), (key1967, -2), (key1967, -2), (key1961, -2), (key1961, -2), (key1961, -2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2), (key1959, 2)]

theorem rawRowCheck17450 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form3 = rawRow17450 := by decide +kernel

def row17450 : Integer.Sparse Key := [(key1959, 12), (key1961, -12), (key1967, -12), (key1970, 12)]

theorem rowCheck17450 : row17450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17450 := by decide +kernel

theorem rowEval17450 (x : Key → ℝ) : Integer.Sparse.eval row17450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck17450, Integer.Sparse.eval_collectBalanced, rawRowCheck17450]

def rawRow17451 : Integer.Sparse Key := [(key665, -2), (key665, -2), (key666, -2), (key666, 6), (key665, -2), (key665, -2), (key666, -2), (key665, 2), (key665, 2), (key682, 2), (key682, 2), (key683, 2), (key683, 2), (key666, -2), (key683, -2), (key683, -2), (key666, 6), (key666, -2), (key683, -2), (key683, -2)]

theorem rawRowCheck17451 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form4 = rawRow17451 := by decide +kernel

def row17451 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

theorem rowCheck17451 : row17451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17451 := by decide +kernel

theorem rowEval17451 (x : Key → ℝ) : Integer.Sparse.eval row17451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17451, Integer.Sparse.eval_collectBalanced, rawRowCheck17451]

def rawRow17452 : Integer.Sparse Key := [(key665, -2), (key666, -2), (key665, -2), (key666, 6), (key665, -2), (key666, -2), (key665, -2), (key682, 2), (key683, 2), (key665, 2), (key683, 2), (key665, 2), (key682, 2), (key683, -2), (key666, -2), (key683, -2), (key666, 6), (key683, -2), (key666, -2), (key683, -2)]

theorem rawRowCheck17452 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form4 = rawRow17452 := by decide +kernel

def row17452 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

theorem rowCheck17452 : row17452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17452 := by decide +kernel

theorem rowEval17452 (x : Key → ℝ) : Integer.Sparse.eval row17452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17452, Integer.Sparse.eval_collectBalanced, rawRowCheck17452]

def rawRow17453 : Integer.Sparse Key := [(key666, -2), (key665, -2), (key665, -2), (key666, 6), (key666, -2), (key665, -2), (key665, -2), (key683, 2), (key682, 2), (key683, 2), (key665, 2), (key682, 2), (key665, 2), (key683, -2), (key683, -2), (key666, -2), (key666, 6), (key683, -2), (key683, -2), (key666, -2)]

theorem rawRowCheck17453 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form4 = rawRow17453 := by decide +kernel

def row17453 : Integer.Sparse Key := [(key665, -4), (key666, 4), (key682, 4), (key683, -4)]

theorem rowCheck17453 : row17453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17453 := by decide +kernel

theorem rowEval17453 (x : Key → ℝ) : Integer.Sparse.eval row17453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17453, Integer.Sparse.eval_collectBalanced, rawRowCheck17453]

def rawRow17454 : Integer.Sparse Key := [(key665, -2), (key666, -2), (key666, -2), (key665, 6), (key682, -2), (key683, -2), (key683, -2), (key665, 2), (key666, 2), (key665, 2), (key683, 2), (key666, 2), (key683, 2), (key665, -2), (key665, -2), (key682, -2), (key683, 6), (key666, -2), (key666, -2), (key683, -2)]

theorem rawRowCheck17454 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17454 := by decide +kernel

def row17454 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

theorem rowCheck17454 : row17454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17454 := by decide +kernel

theorem rowEval17454 (x : Key → ℝ) : Integer.Sparse.eval row17454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17454, Integer.Sparse.eval_collectBalanced, rawRowCheck17454]

def rawRow17455 : Integer.Sparse Key := [(key666, -2), (key665, -2), (key666, -2), (key665, 6), (key683, -2), (key682, -2), (key683, -2), (key666, 2), (key665, 2), (key683, 2), (key665, 2), (key683, 2), (key666, 2), (key665, -2), (key682, -2), (key665, -2), (key683, 6), (key666, -2), (key683, -2), (key666, -2)]

theorem rawRowCheck17455 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17455 := by decide +kernel

def row17455 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

theorem rowCheck17455 : row17455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17455 := by decide +kernel

theorem rowEval17455 (x : Key → ℝ) : Integer.Sparse.eval row17455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17455, Integer.Sparse.eval_collectBalanced, rawRowCheck17455]

def rawRow17456 : Integer.Sparse Key := [(key666, -2), (key666, -2), (key665, -2), (key665, 6), (key683, -2), (key683, -2), (key682, -2), (key683, 2), (key683, 2), (key666, 2), (key666, 2), (key665, 2), (key665, 2), (key682, -2), (key665, -2), (key665, -2), (key683, 6), (key683, -2), (key666, -2), (key666, -2)]

theorem rawRowCheck17456 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17456 := by decide +kernel

def row17456 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

theorem rowCheck17456 : row17456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17456 := by decide +kernel

theorem rowEval17456 (x : Key → ℝ) : Integer.Sparse.eval row17456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17456, Integer.Sparse.eval_collectBalanced, rawRowCheck17456]

def rawRow17457 : Integer.Sparse Key := [(key682, -2), (key683, -2), (key683, -2), (key683, 6), (key665, -2), (key666, -2), (key666, -2), (key665, 2), (key666, 2), (key665, 2), (key683, 2), (key666, 2), (key683, 2), (key666, -2), (key666, -2), (key683, -2), (key665, 6), (key665, -2), (key665, -2), (key682, -2)]

theorem rawRowCheck17457 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form4 = rawRow17457 := by decide +kernel

def row17457 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

theorem rowCheck17457 : row17457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17457 := by decide +kernel

theorem rowEval17457 (x : Key → ℝ) : Integer.Sparse.eval row17457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form4) x := by
  rw [rowCheck17457, Integer.Sparse.eval_collectBalanced, rawRowCheck17457]

def rawRow17458 : Integer.Sparse Key := [(key683, -2), (key682, -2), (key683, -2), (key683, 6), (key666, -2), (key665, -2), (key666, -2), (key666, 2), (key665, 2), (key683, 2), (key665, 2), (key683, 2), (key666, 2), (key666, -2), (key683, -2), (key666, -2), (key665, 6), (key665, -2), (key682, -2), (key665, -2)]

theorem rawRowCheck17458 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form4 = rawRow17458 := by decide +kernel

def row17458 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

theorem rowCheck17458 : row17458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17458 := by decide +kernel

theorem rowEval17458 (x : Key → ℝ) : Integer.Sparse.eval row17458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17458, Integer.Sparse.eval_collectBalanced, rawRowCheck17458]

def rawRow17459 : Integer.Sparse Key := [(key683, -2), (key683, -2), (key682, -2), (key683, 6), (key666, -2), (key666, -2), (key665, -2), (key683, 2), (key683, 2), (key666, 2), (key666, 2), (key665, 2), (key665, 2), (key683, -2), (key666, -2), (key666, -2), (key665, 6), (key682, -2), (key665, -2), (key665, -2)]

theorem rawRowCheck17459 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form4 = rawRow17459 := by decide +kernel

def row17459 : Integer.Sparse Key := [(key665, 4), (key666, -4), (key682, -4), (key683, 4)]

theorem rowCheck17459 : row17459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17459 := by decide +kernel

theorem rowEval17459 (x : Key → ℝ) : Integer.Sparse.eval row17459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17459, Integer.Sparse.eval_collectBalanced, rawRowCheck17459]

def rawRow17460 : Integer.Sparse Key := [(key683, -2), (key683, -2), (key683, -2), (key682, 6), (key683, -2), (key683, -2), (key683, -2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key666, 2), (key665, -2), (key665, -2), (key665, -2), (key682, 6), (key665, -2), (key665, -2), (key665, -2)]

theorem rawRowCheck17460 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form4 = rawRow17460 := by decide +kernel

def row17460 : Integer.Sparse Key := [(key665, -12), (key666, 12), (key682, 12), (key683, -12)]

theorem rowCheck17460 : row17460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17460 := by decide +kernel

theorem rowEval17460 (x : Key → ℝ) : Integer.Sparse.eval row17460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck17460, Integer.Sparse.eval_collectBalanced, rawRowCheck17460]

def rawRow17461 : Integer.Sparse Key := [(key621, 4), (key649, 4), (key649, 4), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key653, -2), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key653, -2), (key625, 4), (key653, 4), (key653, 4)]

theorem rawRowCheck17461 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form5 = rawRow17461 := by decide +kernel

def row17461 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

theorem rowCheck17461 : row17461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17461 := by decide +kernel

theorem rowEval17461 (x : Key → ℝ) : Integer.Sparse.eval row17461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17461, Integer.Sparse.eval_collectBalanced, rawRowCheck17461]

def rawRow17462 : Integer.Sparse Key := [(key649, 4), (key621, 4), (key649, 4), (key649, -2), (key653, -2), (key623, -2), (key653, -2), (key623, -2), (key649, -2), (key649, -2), (key653, -2), (key623, -2), (key653, -2), (key623, -2), (key649, -2), (key653, 4), (key625, 4), (key653, 4)]

theorem rawRowCheck17462 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form5 = rawRow17462 := by decide +kernel

def row17462 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

theorem rowCheck17462 : row17462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17462 := by decide +kernel

theorem rowEval17462 (x : Key → ℝ) : Integer.Sparse.eval row17462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17462, Integer.Sparse.eval_collectBalanced, rawRowCheck17462]

def rawRow17463 : Integer.Sparse Key := [(key649, 4), (key649, 4), (key621, 4), (key653, -2), (key649, -2), (key653, -2), (key623, -2), (key649, -2), (key623, -2), (key653, -2), (key649, -2), (key653, -2), (key623, -2), (key649, -2), (key623, -2), (key653, 4), (key653, 4), (key625, 4)]

theorem rawRowCheck17463 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form5 = rawRow17463 := by decide +kernel

def row17463 : Integer.Sparse Key := [(key621, 4), (key623, -8), (key625, 4)]

theorem rowCheck17463 : row17463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17463 := by decide +kernel

theorem rowEval17463 (x : Key → ℝ) : Integer.Sparse.eval row17463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17463, Integer.Sparse.eval_collectBalanced, rawRowCheck17463]

def rawRow17464 : Integer.Sparse Key := [(key623, 4), (key623, 4), (key653, 4), (key621, -2), (key623, -2), (key621, -2), (key649, -2), (key623, -2), (key649, -2), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key625, -2), (key653, -2), (key623, 4), (key623, 4), (key649, 4)]

theorem rawRowCheck17464 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17464 := by decide +kernel

def row17464 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

theorem rowCheck17464 : row17464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17464 := by decide +kernel

theorem rowEval17464 (x : Key → ℝ) : Integer.Sparse.eval row17464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17464, Integer.Sparse.eval_collectBalanced, rawRowCheck17464]

def rawRow17465 : Integer.Sparse Key := [(key623, 4), (key653, 4), (key623, 4), (key623, -2), (key621, -2), (key649, -2), (key621, -2), (key649, -2), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key623, -2), (key653, -2), (key625, -2), (key623, 4), (key649, 4), (key623, 4)]

theorem rawRowCheck17465 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17465 := by decide +kernel

def row17465 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

theorem rowCheck17465 : row17465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17465 := by decide +kernel

theorem rowEval17465 (x : Key → ℝ) : Integer.Sparse.eval row17465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17465, Integer.Sparse.eval_collectBalanced, rawRowCheck17465]

def rawRow17466 : Integer.Sparse Key := [(key653, 4), (key623, 4), (key623, 4), (key649, -2), (key649, -2), (key623, -2), (key623, -2), (key621, -2), (key621, -2), (key653, -2), (key653, -2), (key625, -2), (key625, -2), (key623, -2), (key623, -2), (key649, 4), (key623, 4), (key623, 4)]

theorem rawRowCheck17466 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17466 := by decide +kernel

def row17466 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

theorem rowCheck17466 : row17466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17466 := by decide +kernel

theorem rowEval17466 (x : Key → ℝ) : Integer.Sparse.eval row17466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17466, Integer.Sparse.eval_collectBalanced, rawRowCheck17466]

def rawRow17467 : Integer.Sparse Key := [(key623, 4), (key623, 4), (key653, 4), (key623, -2), (key625, -2), (key623, -2), (key653, -2), (key625, -2), (key653, -2), (key621, -2), (key623, -2), (key621, -2), (key649, -2), (key623, -2), (key649, -2), (key623, 4), (key623, 4), (key649, 4)]

theorem rawRowCheck17467 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form5 = rawRow17467 := by decide +kernel

def row17467 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

theorem rowCheck17467 : row17467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17467 := by decide +kernel

theorem rowEval17467 (x : Key → ℝ) : Integer.Sparse.eval row17467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck17467, Integer.Sparse.eval_collectBalanced, rawRowCheck17467]

def rawRow17468 : Integer.Sparse Key := [(key623, 4), (key653, 4), (key623, 4), (key625, -2), (key623, -2), (key653, -2), (key623, -2), (key653, -2), (key625, -2), (key623, -2), (key621, -2), (key649, -2), (key621, -2), (key649, -2), (key623, -2), (key623, 4), (key649, 4), (key623, 4)]

theorem rawRowCheck17468 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form5 = rawRow17468 := by decide +kernel

def row17468 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

theorem rowCheck17468 : row17468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17468 := by decide +kernel

theorem rowEval17468 (x : Key → ℝ) : Integer.Sparse.eval row17468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17468, Integer.Sparse.eval_collectBalanced, rawRowCheck17468]

def rawRow17469 : Integer.Sparse Key := [(key653, 4), (key623, 4), (key623, 4), (key653, -2), (key653, -2), (key625, -2), (key625, -2), (key623, -2), (key623, -2), (key649, -2), (key649, -2), (key623, -2), (key623, -2), (key621, -2), (key621, -2), (key649, 4), (key623, 4), (key623, 4)]

theorem rawRowCheck17469 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form5 = rawRow17469 := by decide +kernel

def row17469 : Integer.Sparse Key := [(key621, -4), (key623, 8), (key625, -4)]

theorem rowCheck17469 : row17469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17469 := by decide +kernel

theorem rowEval17469 (x : Key → ℝ) : Integer.Sparse.eval row17469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17469, Integer.Sparse.eval_collectBalanced, rawRowCheck17469]

def rawRow17470 : Integer.Sparse Key := [(key625, 4), (key625, 4), (key625, 4), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key623, -2), (key621, 4), (key621, 4), (key621, 4)]

theorem rawRowCheck17470 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form5 = rawRow17470 := by decide +kernel

def row17470 : Integer.Sparse Key := [(key621, 12), (key623, -24), (key625, 12)]

theorem rowCheck17470 : row17470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17470 := by decide +kernel

theorem rowEval17470 (x : Key → ℝ) : Integer.Sparse.eval row17470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck17470, Integer.Sparse.eval_collectBalanced, rawRowCheck17470]

def rawRow17471 : Integer.Sparse Key := [(key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1866, 2), (key1881, 2), (key1881, 2), (key1862, -1), (key1862, -1), (key1878, -1), (key1878, -1), (key1881, -1), (key1881, -1), (key1868, 2), (key1868, 2), (key1878, 2), (key1878, 2), (key1889, 2), (key1889, 2), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1889, -1), (key1889, -1), (key1866, 2), (key1881, 2), (key1881, 2), (key1871, -1), (key1871, -1), (key1881, -1), (key1881, -1), (key1889, -1), (key1889, -1)]

theorem rawRowCheck17471 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form6 = rawRow17471 := by decide +kernel

def row17471 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

theorem rowCheck17471 : row17471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17471 := by decide +kernel

theorem rowEval17471 (x : Key → ℝ) : Integer.Sparse.eval row17471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17471, Integer.Sparse.eval_collectBalanced, rawRowCheck17471]

def rawRow17472 : Integer.Sparse Key := [(key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1881, 2), (key1866, 2), (key1881, 2), (key1878, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1878, 2), (key1889, 2), (key1868, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1881, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1881, 2), (key1866, 2), (key1881, 2), (key1881, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, -1), (key1881, -1)]

theorem rawRowCheck17472 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form6 = rawRow17472 := by decide +kernel

def row17472 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

theorem rowCheck17472 : row17472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17472 := by decide +kernel

theorem rowEval17472 (x : Key → ℝ) : Integer.Sparse.eval row17472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17472, Integer.Sparse.eval_collectBalanced, rawRowCheck17472]

def rawRow17473 : Integer.Sparse Key := [(key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1866, 2), (key1881, -1), (key1878, -1), (key1881, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1889, 2), (key1878, 2), (key1889, 2), (key1868, 2), (key1878, 2), (key1868, 2), (key1889, -1), (key1881, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1871, -1), (key1881, 2), (key1881, 2), (key1866, 2), (key1889, -1), (key1881, -1), (key1889, -1), (key1871, -1), (key1881, -1), (key1871, -1)]

theorem rawRowCheck17473 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form6 = rawRow17473 := by decide +kernel

def row17473 : Integer.Sparse Key := [(key1862, -4), (key1866, 4), (key1868, 4), (key1871, -4)]

theorem rowCheck17473 : row17473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17473 := by decide +kernel

theorem rowEval17473 (x : Key → ℝ) : Integer.Sparse.eval row17473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17473, Integer.Sparse.eval_collectBalanced, rawRowCheck17473]

def rawRow17474 : Integer.Sparse Key := [(key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1), (key1871, 2), (key1871, 2), (key1889, 2), (key1866, -1), (key1871, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1881, -1)]

theorem rawRowCheck17474 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form6 = rawRow17474 := by decide +kernel

def row17474 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

theorem rowCheck17474 : row17474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17474 := by decide +kernel

theorem rowEval17474 (x : Key → ℝ) : Integer.Sparse.eval row17474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17474, Integer.Sparse.eval_collectBalanced, rawRowCheck17474]

def rawRow17475 : Integer.Sparse Key := [(key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1871, 2), (key1889, 2), (key1871, 2), (key1871, -1), (key1866, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1871, -1)]

theorem rawRowCheck17475 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form6 = rawRow17475 := by decide +kernel

def row17475 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

theorem rowCheck17475 : row17475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17475 := by decide +kernel

theorem rowEval17475 (x : Key → ℝ) : Integer.Sparse.eval row17475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17475, Integer.Sparse.eval_collectBalanced, rawRowCheck17475]

def rawRow17476 : Integer.Sparse Key := [(key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1), (key1889, 2), (key1871, 2), (key1871, 2), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1)]

theorem rawRowCheck17476 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form6 = rawRow17476 := by decide +kernel

def row17476 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

theorem rowCheck17476 : row17476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17476 := by decide +kernel

theorem rowEval17476 (x : Key → ℝ) : Integer.Sparse.eval row17476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17476, Integer.Sparse.eval_collectBalanced, rawRowCheck17476]

def rawRow17477 : Integer.Sparse Key := [(key1868, -1), (key1871, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1889, -1), (key1871, 2), (key1871, 2), (key1889, 2), (key1862, -1), (key1866, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1862, 2), (key1871, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1881, 2), (key1866, -1), (key1871, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1881, -1), (key1862, 2), (key1862, 2), (key1878, 2), (key1862, -1), (key1868, -1), (key1862, -1), (key1878, -1), (key1868, -1), (key1878, -1)]

theorem rawRowCheck17477 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form6 = rawRow17477 := by decide +kernel

def row17477 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

theorem rowCheck17477 : row17477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17477 := by decide +kernel

theorem rowEval17477 (x : Key → ℝ) : Integer.Sparse.eval row17477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17477, Integer.Sparse.eval_collectBalanced, rawRowCheck17477]

def rawRow17478 : Integer.Sparse Key := [(key1871, -1), (key1868, -1), (key1889, -1), (key1868, -1), (key1889, -1), (key1871, -1), (key1871, 2), (key1889, 2), (key1871, 2), (key1866, -1), (key1862, -1), (key1881, -1), (key1862, -1), (key1881, -1), (key1866, -1), (key1871, 2), (key1862, 2), (key1881, 2), (key1862, 2), (key1881, 2), (key1871, 2), (key1871, -1), (key1866, -1), (key1881, -1), (key1866, -1), (key1881, -1), (key1871, -1), (key1862, 2), (key1878, 2), (key1862, 2), (key1868, -1), (key1862, -1), (key1878, -1), (key1862, -1), (key1878, -1), (key1868, -1)]

theorem rawRowCheck17478 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form6 = rawRow17478 := by decide +kernel

def row17478 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

theorem rowCheck17478 : row17478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17478 := by decide +kernel

theorem rowEval17478 (x : Key → ℝ) : Integer.Sparse.eval row17478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17478, Integer.Sparse.eval_collectBalanced, rawRowCheck17478]

def rawRow17479 : Integer.Sparse Key := [(key1889, -1), (key1889, -1), (key1871, -1), (key1871, -1), (key1868, -1), (key1868, -1), (key1889, 2), (key1871, 2), (key1871, 2), (key1881, -1), (key1881, -1), (key1866, -1), (key1866, -1), (key1862, -1), (key1862, -1), (key1881, 2), (key1881, 2), (key1871, 2), (key1871, 2), (key1862, 2), (key1862, 2), (key1881, -1), (key1881, -1), (key1871, -1), (key1871, -1), (key1866, -1), (key1866, -1), (key1878, 2), (key1862, 2), (key1862, 2), (key1878, -1), (key1878, -1), (key1868, -1), (key1868, -1), (key1862, -1), (key1862, -1)]

theorem rawRowCheck17479 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form6 = rawRow17479 := by decide +kernel

def row17479 : Integer.Sparse Key := [(key1862, 4), (key1866, -4), (key1868, -4), (key1871, 4)]

theorem rowCheck17479 : row17479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17479 := by decide +kernel

theorem rowEval17479 (x : Key → ℝ) : Integer.Sparse.eval row17479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17479, Integer.Sparse.eval_collectBalanced, rawRowCheck17479]

def rawRow17480 : Integer.Sparse Key := [(key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1871, -1), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1866, 2), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1)]

theorem rawRowCheck17480 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form6 = rawRow17480 := by decide +kernel

def row17480 : Integer.Sparse Key := [(key1862, -12), (key1866, 12), (key1868, 12), (key1871, -12)]

theorem rowCheck17480 : row17480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17480 := by decide +kernel

theorem rowEval17480 (x : Key → ℝ) : Integer.Sparse.eval row17480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17480, Integer.Sparse.eval_collectBalanced, rawRowCheck17480]

def rawRow17481 : Integer.Sparse Key := [(key1963, 4), (key1965, 4), (key1965, 4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1968, 12)]

theorem rawRowCheck17481 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form7 = rawRow17481 := by decide +kernel

def row17481 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

theorem rowCheck17481 : row17481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17481 := by decide +kernel

theorem rowEval17481 (x : Key → ℝ) : Integer.Sparse.eval row17481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17481, Integer.Sparse.eval_collectBalanced, rawRowCheck17481]

def rawRow17482 : Integer.Sparse Key := [(key1965, 4), (key1963, 4), (key1965, 4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1968, 12)]

theorem rawRowCheck17482 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form7 = rawRow17482 := by decide +kernel

def row17482 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

theorem rowCheck17482 : row17482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17482 := by decide +kernel

theorem rowEval17482 (x : Key → ℝ) : Integer.Sparse.eval row17482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17482, Integer.Sparse.eval_collectBalanced, rawRowCheck17482]

def rawRow17483 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1963, 4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1968, 12)]

theorem rawRowCheck17483 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form7 = rawRow17483 := by decide +kernel

def row17483 : Integer.Sparse Key := [(key1963, 4), (key1965, -8), (key1968, 4)]

theorem rowCheck17483 : row17483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17483 := by decide +kernel

theorem rowEval17483 (x : Key → ℝ) : Integer.Sparse.eval row17483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17483, Integer.Sparse.eval_collectBalanced, rawRowCheck17483]

def rawRow17484 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1968, 4), (key1963, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1968, -4), (key1968, -4), (key1965, 12)]

theorem rawRowCheck17484 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17484 := by decide +kernel

def row17484 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

theorem rowCheck17484 : row17484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17484 := by decide +kernel

theorem rowEval17484 (x : Key → ℝ) : Integer.Sparse.eval row17484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17484, Integer.Sparse.eval_collectBalanced, rawRowCheck17484]

def rawRow17485 : Integer.Sparse Key := [(key1965, 4), (key1968, 4), (key1965, 4), (key1965, -4), (key1963, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1968, -4), (key1965, 12)]

theorem rawRowCheck17485 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17485 := by decide +kernel

def row17485 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

theorem rowCheck17485 : row17485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17485 := by decide +kernel

theorem rowEval17485 (x : Key → ℝ) : Integer.Sparse.eval row17485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17485, Integer.Sparse.eval_collectBalanced, rawRowCheck17485]

def rawRow17486 : Integer.Sparse Key := [(key1968, 4), (key1965, 4), (key1965, 4), (key1965, -4), (key1965, -4), (key1963, -4), (key1968, -4), (key1968, -4), (key1965, -4), (key1965, 12)]

theorem rawRowCheck17486 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17486 := by decide +kernel

def row17486 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

theorem rowCheck17486 : row17486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17486 := by decide +kernel

theorem rowEval17486 (x : Key → ℝ) : Integer.Sparse.eval row17486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17486, Integer.Sparse.eval_collectBalanced, rawRowCheck17486]

def rawRow17487 : Integer.Sparse Key := [(key1965, 4), (key1965, 4), (key1968, 4), (key1965, -4), (key1968, -4), (key1968, -4), (key1963, -4), (key1965, -4), (key1965, -4), (key1965, 12)]

theorem rawRowCheck17487 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form7 = rawRow17487 := by decide +kernel

def row17487 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

theorem rowCheck17487 : row17487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17487 := by decide +kernel

theorem rowEval17487 (x : Key → ℝ) : Integer.Sparse.eval row17487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17487, Integer.Sparse.eval_collectBalanced, rawRowCheck17487]

def rawRow17488 : Integer.Sparse Key := [(key1965, 4), (key1968, 4), (key1965, 4), (key1968, -4), (key1965, -4), (key1968, -4), (key1965, -4), (key1963, -4), (key1965, -4), (key1965, 12)]

theorem rawRowCheck17488 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form7 = rawRow17488 := by decide +kernel

def row17488 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

theorem rowCheck17488 : row17488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17488 := by decide +kernel

theorem rowEval17488 (x : Key → ℝ) : Integer.Sparse.eval row17488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17488, Integer.Sparse.eval_collectBalanced, rawRowCheck17488]

def rawRow17489 : Integer.Sparse Key := [(key1968, 4), (key1965, 4), (key1965, 4), (key1968, -4), (key1968, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1963, -4), (key1965, 12)]

theorem rawRowCheck17489 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form7 = rawRow17489 := by decide +kernel

def row17489 : Integer.Sparse Key := [(key1963, -4), (key1965, 8), (key1968, -4)]

theorem rowCheck17489 : row17489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17489 := by decide +kernel

theorem rowEval17489 (x : Key → ℝ) : Integer.Sparse.eval row17489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17489, Integer.Sparse.eval_collectBalanced, rawRowCheck17489]

def rawRow17490 : Integer.Sparse Key := [(key1968, 4), (key1968, 4), (key1968, 4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1965, -4), (key1963, 12)]

theorem rawRowCheck17490 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form7 = rawRow17490 := by decide +kernel

def row17490 : Integer.Sparse Key := [(key1963, 12), (key1965, -24), (key1968, 12)]

theorem rowCheck17490 : row17490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17490 := by decide +kernel

theorem rowEval17490 (x : Key → ℝ) : Integer.Sparse.eval row17490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17490, Integer.Sparse.eval_collectBalanced, rawRowCheck17490]

def rawRow17491 : Integer.Sparse Key := [(key1934, -2), (key1934, -2), (key1935, -2), (key1935, 6), (key1934, -2), (key1934, -2), (key1935, -2), (key1934, 2), (key1934, 2), (key1954, 2), (key1954, 2), (key1955, 2), (key1955, 2), (key1935, -2), (key1955, -2), (key1955, -2), (key1935, 6), (key1935, -2), (key1955, -2), (key1955, -2)]

theorem rawRowCheck17491 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form8 = rawRow17491 := by decide +kernel

def row17491 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

theorem rowCheck17491 : row17491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17491 := by decide +kernel

theorem rowEval17491 (x : Key → ℝ) : Integer.Sparse.eval row17491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17491, Integer.Sparse.eval_collectBalanced, rawRowCheck17491]

def rawRow17492 : Integer.Sparse Key := [(key1934, -2), (key1935, -2), (key1934, -2), (key1935, 6), (key1934, -2), (key1935, -2), (key1934, -2), (key1954, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1954, 2), (key1955, -2), (key1935, -2), (key1955, -2), (key1935, 6), (key1955, -2), (key1935, -2), (key1955, -2)]

theorem rawRowCheck17492 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form8 = rawRow17492 := by decide +kernel

def row17492 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

theorem rowCheck17492 : row17492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17492 := by decide +kernel

theorem rowEval17492 (x : Key → ℝ) : Integer.Sparse.eval row17492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17492, Integer.Sparse.eval_collectBalanced, rawRowCheck17492]

def rawRow17493 : Integer.Sparse Key := [(key1935, -2), (key1934, -2), (key1934, -2), (key1935, 6), (key1935, -2), (key1934, -2), (key1934, -2), (key1955, 2), (key1954, 2), (key1955, 2), (key1934, 2), (key1954, 2), (key1934, 2), (key1955, -2), (key1955, -2), (key1935, -2), (key1935, 6), (key1955, -2), (key1955, -2), (key1935, -2)]

theorem rawRowCheck17493 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form8 = rawRow17493 := by decide +kernel

def row17493 : Integer.Sparse Key := [(key1934, -4), (key1935, 4), (key1954, 4), (key1955, -4)]

theorem rowCheck17493 : row17493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17493 := by decide +kernel

theorem rowEval17493 (x : Key → ℝ) : Integer.Sparse.eval row17493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17493, Integer.Sparse.eval_collectBalanced, rawRowCheck17493]

def rawRow17494 : Integer.Sparse Key := [(key1934, -2), (key1935, -2), (key1935, -2), (key1934, 6), (key1954, -2), (key1955, -2), (key1955, -2), (key1934, 2), (key1935, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1955, 2), (key1934, -2), (key1934, -2), (key1954, -2), (key1955, 6), (key1935, -2), (key1935, -2), (key1955, -2)]

theorem rawRowCheck17494 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17494 := by decide +kernel

def row17494 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

theorem rowCheck17494 : row17494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17494 := by decide +kernel

theorem rowEval17494 (x : Key → ℝ) : Integer.Sparse.eval row17494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17494, Integer.Sparse.eval_collectBalanced, rawRowCheck17494]

def rawRow17495 : Integer.Sparse Key := [(key1935, -2), (key1934, -2), (key1935, -2), (key1934, 6), (key1955, -2), (key1954, -2), (key1955, -2), (key1935, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1934, -2), (key1954, -2), (key1934, -2), (key1955, 6), (key1935, -2), (key1955, -2), (key1935, -2)]

theorem rawRowCheck17495 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17495 := by decide +kernel

def row17495 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

theorem rowCheck17495 : row17495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17495 := by decide +kernel

theorem rowEval17495 (x : Key → ℝ) : Integer.Sparse.eval row17495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17495, Integer.Sparse.eval_collectBalanced, rawRowCheck17495]

def rawRow17496 : Integer.Sparse Key := [(key1935, -2), (key1935, -2), (key1934, -2), (key1934, 6), (key1955, -2), (key1955, -2), (key1954, -2), (key1955, 2), (key1955, 2), (key1935, 2), (key1935, 2), (key1934, 2), (key1934, 2), (key1954, -2), (key1934, -2), (key1934, -2), (key1955, 6), (key1955, -2), (key1935, -2), (key1935, -2)]

theorem rawRowCheck17496 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17496 := by decide +kernel

def row17496 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

theorem rowCheck17496 : row17496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17496 := by decide +kernel

theorem rowEval17496 (x : Key → ℝ) : Integer.Sparse.eval row17496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17496, Integer.Sparse.eval_collectBalanced, rawRowCheck17496]

def rawRow17497 : Integer.Sparse Key := [(key1954, -2), (key1955, -2), (key1955, -2), (key1955, 6), (key1934, -2), (key1935, -2), (key1935, -2), (key1934, 2), (key1935, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1955, 2), (key1935, -2), (key1935, -2), (key1955, -2), (key1934, 6), (key1934, -2), (key1934, -2), (key1954, -2)]

theorem rawRowCheck17497 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form8 = rawRow17497 := by decide +kernel

def row17497 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

theorem rowCheck17497 : row17497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17497 := by decide +kernel

theorem rowEval17497 (x : Key → ℝ) : Integer.Sparse.eval row17497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17497, Integer.Sparse.eval_collectBalanced, rawRowCheck17497]

def rawRow17498 : Integer.Sparse Key := [(key1955, -2), (key1954, -2), (key1955, -2), (key1955, 6), (key1935, -2), (key1934, -2), (key1935, -2), (key1935, 2), (key1934, 2), (key1955, 2), (key1934, 2), (key1955, 2), (key1935, 2), (key1935, -2), (key1955, -2), (key1935, -2), (key1934, 6), (key1934, -2), (key1954, -2), (key1934, -2)]

theorem rawRowCheck17498 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form8 = rawRow17498 := by decide +kernel

def row17498 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

theorem rowCheck17498 : row17498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17498 := by decide +kernel

theorem rowEval17498 (x : Key → ℝ) : Integer.Sparse.eval row17498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17498, Integer.Sparse.eval_collectBalanced, rawRowCheck17498]

def rawRow17499 : Integer.Sparse Key := [(key1955, -2), (key1955, -2), (key1954, -2), (key1955, 6), (key1935, -2), (key1935, -2), (key1934, -2), (key1955, 2), (key1955, 2), (key1935, 2), (key1935, 2), (key1934, 2), (key1934, 2), (key1955, -2), (key1935, -2), (key1935, -2), (key1934, 6), (key1954, -2), (key1934, -2), (key1934, -2)]

theorem rawRowCheck17499 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form8 = rawRow17499 := by decide +kernel

def row17499 : Integer.Sparse Key := [(key1934, 4), (key1935, -4), (key1954, -4), (key1955, 4)]

theorem rowCheck17499 : row17499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17499 := by decide +kernel

theorem rowEval17499 (x : Key → ℝ) : Integer.Sparse.eval row17499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17499, Integer.Sparse.eval_collectBalanced, rawRowCheck17499]

def rawRow17500 : Integer.Sparse Key := [(key1955, -2), (key1955, -2), (key1955, -2), (key1954, 6), (key1955, -2), (key1955, -2), (key1955, -2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1935, 2), (key1934, -2), (key1934, -2), (key1934, -2), (key1954, 6), (key1934, -2), (key1934, -2), (key1934, -2)]

theorem rawRowCheck17500 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form8 = rawRow17500 := by decide +kernel

def row17500 : Integer.Sparse Key := [(key1934, -12), (key1935, 12), (key1954, 12), (key1955, -12)]

theorem rowCheck17500 : row17500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17500 := by decide +kernel

theorem rowEval17500 (x : Key → ℝ) : Integer.Sparse.eval row17500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17500, Integer.Sparse.eval_collectBalanced, rawRowCheck17500]

def rawRow17501 : Integer.Sparse Key := [(key688, 4), (key689, 4), (key689, 4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key691, 12)]

theorem rawRowCheck17501 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form9 = rawRow17501 := by decide +kernel

def row17501 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

theorem rowCheck17501 : row17501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17501 := by decide +kernel

theorem rowEval17501 (x : Key → ℝ) : Integer.Sparse.eval row17501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17501, Integer.Sparse.eval_collectBalanced, rawRowCheck17501]

def rawRow17502 : Integer.Sparse Key := [(key689, 4), (key688, 4), (key689, 4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key691, 12)]

theorem rawRowCheck17502 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form9 = rawRow17502 := by decide +kernel

def row17502 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

theorem rowCheck17502 : row17502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17502 := by decide +kernel

theorem rowEval17502 (x : Key → ℝ) : Integer.Sparse.eval row17502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17502, Integer.Sparse.eval_collectBalanced, rawRowCheck17502]

def rawRow17503 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key688, 4), (key691, -4), (key689, -4), (key689, -4), (key691, -4), (key689, -4), (key689, -4), (key691, 12)]

theorem rawRowCheck17503 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form9 = rawRow17503 := by decide +kernel

def row17503 : Integer.Sparse Key := [(key688, 4), (key689, -8), (key691, 4)]

theorem rowCheck17503 : row17503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17503 := by decide +kernel

theorem rowEval17503 (x : Key → ℝ) : Integer.Sparse.eval row17503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17503, Integer.Sparse.eval_collectBalanced, rawRowCheck17503]

def rawRow17504 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key691, 4), (key688, -4), (key689, -4), (key689, -4), (key689, -4), (key691, -4), (key691, -4), (key689, 12)]

theorem rawRowCheck17504 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17504 := by decide +kernel

def row17504 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

theorem rowCheck17504 : row17504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17504 := by decide +kernel

theorem rowEval17504 (x : Key → ℝ) : Integer.Sparse.eval row17504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17504, Integer.Sparse.eval_collectBalanced, rawRowCheck17504]

def rawRow17505 : Integer.Sparse Key := [(key689, 4), (key691, 4), (key689, 4), (key689, -4), (key688, -4), (key689, -4), (key691, -4), (key689, -4), (key691, -4), (key689, 12)]

theorem rawRowCheck17505 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17505 := by decide +kernel

def row17505 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

theorem rowCheck17505 : row17505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17505 := by decide +kernel

theorem rowEval17505 (x : Key → ℝ) : Integer.Sparse.eval row17505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17505, Integer.Sparse.eval_collectBalanced, rawRowCheck17505]

def rawRow17506 : Integer.Sparse Key := [(key691, 4), (key689, 4), (key689, 4), (key689, -4), (key689, -4), (key688, -4), (key691, -4), (key691, -4), (key689, -4), (key689, 12)]

theorem rawRowCheck17506 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17506 := by decide +kernel

def row17506 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

theorem rowCheck17506 : row17506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17506 := by decide +kernel

theorem rowEval17506 (x : Key → ℝ) : Integer.Sparse.eval row17506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17506, Integer.Sparse.eval_collectBalanced, rawRowCheck17506]

def rawRow17507 : Integer.Sparse Key := [(key689, 4), (key689, 4), (key691, 4), (key689, -4), (key691, -4), (key691, -4), (key688, -4), (key689, -4), (key689, -4), (key689, 12)]

theorem rawRowCheck17507 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form9 = rawRow17507 := by decide +kernel

def row17507 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

theorem rowCheck17507 : row17507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17507 := by decide +kernel

theorem rowEval17507 (x : Key → ℝ) : Integer.Sparse.eval row17507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17507, Integer.Sparse.eval_collectBalanced, rawRowCheck17507]

def rawRow17508 : Integer.Sparse Key := [(key689, 4), (key691, 4), (key689, 4), (key691, -4), (key689, -4), (key691, -4), (key689, -4), (key688, -4), (key689, -4), (key689, 12)]

theorem rawRowCheck17508 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form9 = rawRow17508 := by decide +kernel

def row17508 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

theorem rowCheck17508 : row17508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17508 := by decide +kernel

theorem rowEval17508 (x : Key → ℝ) : Integer.Sparse.eval row17508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17508, Integer.Sparse.eval_collectBalanced, rawRowCheck17508]

def rawRow17509 : Integer.Sparse Key := [(key691, 4), (key689, 4), (key689, 4), (key691, -4), (key691, -4), (key689, -4), (key689, -4), (key689, -4), (key688, -4), (key689, 12)]

theorem rawRowCheck17509 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form9 = rawRow17509 := by decide +kernel

def row17509 : Integer.Sparse Key := [(key688, -4), (key689, 8), (key691, -4)]

theorem rowCheck17509 : row17509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17509 := by decide +kernel

theorem rowEval17509 (x : Key → ℝ) : Integer.Sparse.eval row17509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17509, Integer.Sparse.eval_collectBalanced, rawRowCheck17509]

def rawRow17510 : Integer.Sparse Key := [(key691, 4), (key691, 4), (key691, 4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key689, -4), (key688, 12)]

theorem rawRowCheck17510 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form9 = rawRow17510 := by decide +kernel

def row17510 : Integer.Sparse Key := [(key688, 12), (key689, -24), (key691, 12)]

theorem rowCheck17510 : row17510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17510 := by decide +kernel

theorem rowEval17510 (x : Key → ℝ) : Integer.Sparse.eval row17510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17510, Integer.Sparse.eval_collectBalanced, rawRowCheck17510]

def rawRow17511 : Integer.Sparse Key := [(key1938, -1), (key1938, -1), (key1950, -1), (key1950, -1), (key1951, -1), (key1951, -1), (key1939, 2), (key1951, 2), (key1951, 2), (key1938, -1), (key1938, -1), (key1950, -1), (key1950, -1), (key1951, -1), (key1951, -1), (key1941, 2), (key1941, 2), (key1950, 2), (key1950, 2), (key1956, 2), (key1956, 2), (key1942, -1), (key1942, -1), (key1951, -1), (key1951, -1), (key1956, -1), (key1956, -1), (key1939, 2), (key1951, 2), (key1951, 2), (key1942, -1), (key1942, -1), (key1951, -1), (key1951, -1), (key1956, -1), (key1956, -1)]

theorem rawRowCheck17511 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form10 = rawRow17511 := by decide +kernel

def row17511 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

theorem rowCheck17511 : row17511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17511 := by decide +kernel

theorem rowEval17511 (x : Key → ℝ) : Integer.Sparse.eval row17511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17511, Integer.Sparse.eval_collectBalanced, rawRowCheck17511]

def rawRow17512 : Integer.Sparse Key := [(key1950, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1951, 2), (key1939, 2), (key1951, 2), (key1950, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1950, 2), (key1956, 2), (key1941, 2), (key1956, 2), (key1941, 2), (key1950, 2), (key1951, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1951, 2), (key1939, 2), (key1951, 2), (key1951, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, -1), (key1951, -1)]

theorem rawRowCheck17512 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form10 = rawRow17512 := by decide +kernel

def row17512 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

theorem rowCheck17512 : row17512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17512 := by decide +kernel

theorem rowEval17512 (x : Key → ℝ) : Integer.Sparse.eval row17512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17512, Integer.Sparse.eval_collectBalanced, rawRowCheck17512]

def rawRow17513 : Integer.Sparse Key := [(key1951, -1), (key1950, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1951, 2), (key1951, 2), (key1939, 2), (key1951, -1), (key1950, -1), (key1951, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1956, 2), (key1950, 2), (key1956, 2), (key1941, 2), (key1950, 2), (key1941, 2), (key1956, -1), (key1951, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1942, -1), (key1951, 2), (key1951, 2), (key1939, 2), (key1956, -1), (key1951, -1), (key1956, -1), (key1942, -1), (key1951, -1), (key1942, -1)]

theorem rawRowCheck17513 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form10 = rawRow17513 := by decide +kernel

def row17513 : Integer.Sparse Key := [(key1938, -4), (key1939, 4), (key1941, 4), (key1942, -4)]

theorem rowCheck17513 : row17513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17513 := by decide +kernel

theorem rowEval17513 (x : Key → ℝ) : Integer.Sparse.eval row17513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17513, Integer.Sparse.eval_collectBalanced, rawRowCheck17513]

def rawRow17514 : Integer.Sparse Key := [(key1938, -1), (key1939, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1941, -1), (key1942, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1938, 2), (key1942, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1951, 2), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1), (key1942, 2), (key1942, 2), (key1956, 2), (key1939, -1), (key1942, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1951, -1)]

theorem rawRowCheck17514 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form10 = rawRow17514 := by decide +kernel

def row17514 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

theorem rowCheck17514 : row17514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17514 := by decide +kernel

theorem rowEval17514 (x : Key → ℝ) : Integer.Sparse.eval row17514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17514, Integer.Sparse.eval_collectBalanced, rawRowCheck17514]

def rawRow17515 : Integer.Sparse Key := [(key1939, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1942, -1), (key1941, -1), (key1956, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1942, 2), (key1938, 2), (key1951, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1942, 2), (key1956, 2), (key1942, 2), (key1942, -1), (key1939, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1942, -1)]

theorem rawRowCheck17515 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form10 = rawRow17515 := by decide +kernel

def row17515 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

theorem rowCheck17515 : row17515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17515 := by decide +kernel

theorem rowEval17515 (x : Key → ℝ) : Integer.Sparse.eval row17515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17515, Integer.Sparse.eval_collectBalanced, rawRowCheck17515]

def rawRow17516 : Integer.Sparse Key := [(key1951, -1), (key1951, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1956, -1), (key1956, -1), (key1942, -1), (key1942, -1), (key1941, -1), (key1941, -1), (key1951, 2), (key1951, 2), (key1942, 2), (key1942, 2), (key1938, 2), (key1938, 2), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1), (key1956, 2), (key1942, 2), (key1942, 2), (key1951, -1), (key1951, -1), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1)]

theorem rawRowCheck17516 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form10 = rawRow17516 := by decide +kernel

def row17516 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

theorem rowCheck17516 : row17516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17516 := by decide +kernel

theorem rowEval17516 (x : Key → ℝ) : Integer.Sparse.eval row17516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17516, Integer.Sparse.eval_collectBalanced, rawRowCheck17516]

def rawRow17517 : Integer.Sparse Key := [(key1941, -1), (key1942, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1956, -1), (key1942, 2), (key1942, 2), (key1956, 2), (key1938, -1), (key1939, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1938, 2), (key1942, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1951, 2), (key1939, -1), (key1942, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1951, -1), (key1938, 2), (key1938, 2), (key1950, 2), (key1938, -1), (key1941, -1), (key1938, -1), (key1950, -1), (key1941, -1), (key1950, -1)]

theorem rawRowCheck17517 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form10 = rawRow17517 := by decide +kernel

def row17517 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

theorem rowCheck17517 : row17517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17517 := by decide +kernel

theorem rowEval17517 (x : Key → ℝ) : Integer.Sparse.eval row17517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17517, Integer.Sparse.eval_collectBalanced, rawRowCheck17517]

def rawRow17518 : Integer.Sparse Key := [(key1942, -1), (key1941, -1), (key1956, -1), (key1941, -1), (key1956, -1), (key1942, -1), (key1942, 2), (key1956, 2), (key1942, 2), (key1939, -1), (key1938, -1), (key1951, -1), (key1938, -1), (key1951, -1), (key1939, -1), (key1942, 2), (key1938, 2), (key1951, 2), (key1938, 2), (key1951, 2), (key1942, 2), (key1942, -1), (key1939, -1), (key1951, -1), (key1939, -1), (key1951, -1), (key1942, -1), (key1938, 2), (key1950, 2), (key1938, 2), (key1941, -1), (key1938, -1), (key1950, -1), (key1938, -1), (key1950, -1), (key1941, -1)]

theorem rawRowCheck17518 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form10 = rawRow17518 := by decide +kernel

def row17518 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

theorem rowCheck17518 : row17518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17518 := by decide +kernel

theorem rowEval17518 (x : Key → ℝ) : Integer.Sparse.eval row17518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17518, Integer.Sparse.eval_collectBalanced, rawRowCheck17518]

def rawRow17519 : Integer.Sparse Key := [(key1956, -1), (key1956, -1), (key1942, -1), (key1942, -1), (key1941, -1), (key1941, -1), (key1956, 2), (key1942, 2), (key1942, 2), (key1951, -1), (key1951, -1), (key1939, -1), (key1939, -1), (key1938, -1), (key1938, -1), (key1951, 2), (key1951, 2), (key1942, 2), (key1942, 2), (key1938, 2), (key1938, 2), (key1951, -1), (key1951, -1), (key1942, -1), (key1942, -1), (key1939, -1), (key1939, -1), (key1950, 2), (key1938, 2), (key1938, 2), (key1950, -1), (key1950, -1), (key1941, -1), (key1941, -1), (key1938, -1), (key1938, -1)]

theorem rawRowCheck17519 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form10 = rawRow17519 := by decide +kernel

def row17519 : Integer.Sparse Key := [(key1938, 4), (key1939, -4), (key1941, -4), (key1942, 4)]

theorem rowCheck17519 : row17519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17519 := by decide +kernel

theorem rowEval17519 (x : Key → ℝ) : Integer.Sparse.eval row17519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17519, Integer.Sparse.eval_collectBalanced, rawRowCheck17519]

def rawRow17520 : Integer.Sparse Key := [(key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1942, -1), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1939, 2), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1)]

theorem rawRowCheck17520 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form10 = rawRow17520 := by decide +kernel

def row17520 : Integer.Sparse Key := [(key1938, -12), (key1939, 12), (key1941, 12), (key1942, -12)]

theorem rowCheck17520 : row17520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17520 := by decide +kernel

theorem rowEval17520 (x : Key → ℝ) : Integer.Sparse.eval row17520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17520, Integer.Sparse.eval_collectBalanced, rawRowCheck17520]

def rawRow17521 : Integer.Sparse Key := [(key517, -2), (key517, -2), (key524, -2), (key524, 6), (key517, -2), (key517, -2), (key524, -2), (key517, 2), (key517, 2), (key549, 2), (key549, 2), (key555, 2), (key555, 2), (key524, -2), (key555, -2), (key555, -2), (key524, 6), (key524, -2), (key555, -2), (key555, -2)]

theorem rawRowCheck17521 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form11 = rawRow17521 := by decide +kernel

def row17521 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

theorem rowCheck17521 : row17521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17521 := by decide +kernel

theorem rowEval17521 (x : Key → ℝ) : Integer.Sparse.eval row17521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17521, Integer.Sparse.eval_collectBalanced, rawRowCheck17521]

def rawRow17522 : Integer.Sparse Key := [(key517, -2), (key524, -2), (key517, -2), (key524, 6), (key517, -2), (key524, -2), (key517, -2), (key549, 2), (key555, 2), (key517, 2), (key555, 2), (key517, 2), (key549, 2), (key555, -2), (key524, -2), (key555, -2), (key524, 6), (key555, -2), (key524, -2), (key555, -2)]

theorem rawRowCheck17522 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form11 = rawRow17522 := by decide +kernel

def row17522 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

theorem rowCheck17522 : row17522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17522 := by decide +kernel

theorem rowEval17522 (x : Key → ℝ) : Integer.Sparse.eval row17522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17522, Integer.Sparse.eval_collectBalanced, rawRowCheck17522]

def rawRow17523 : Integer.Sparse Key := [(key524, -2), (key517, -2), (key517, -2), (key524, 6), (key524, -2), (key517, -2), (key517, -2), (key555, 2), (key549, 2), (key555, 2), (key517, 2), (key549, 2), (key517, 2), (key555, -2), (key555, -2), (key524, -2), (key524, 6), (key555, -2), (key555, -2), (key524, -2)]

theorem rawRowCheck17523 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form11 = rawRow17523 := by decide +kernel

def row17523 : Integer.Sparse Key := [(key517, -4), (key524, 4), (key549, 4), (key555, -4)]

theorem rowCheck17523 : row17523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17523 := by decide +kernel

theorem rowEval17523 (x : Key → ℝ) : Integer.Sparse.eval row17523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17523, Integer.Sparse.eval_collectBalanced, rawRowCheck17523]

def rawRow17524 : Integer.Sparse Key := [(key517, -2), (key524, -2), (key524, -2), (key517, 6), (key549, -2), (key555, -2), (key555, -2), (key517, 2), (key524, 2), (key517, 2), (key555, 2), (key524, 2), (key555, 2), (key517, -2), (key517, -2), (key549, -2), (key555, 6), (key524, -2), (key524, -2), (key555, -2)]

theorem rawRowCheck17524 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17524 := by decide +kernel

def row17524 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

theorem rowCheck17524 : row17524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17524 := by decide +kernel

theorem rowEval17524 (x : Key → ℝ) : Integer.Sparse.eval row17524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17524, Integer.Sparse.eval_collectBalanced, rawRowCheck17524]

def rawRow17525 : Integer.Sparse Key := [(key524, -2), (key517, -2), (key524, -2), (key517, 6), (key555, -2), (key549, -2), (key555, -2), (key524, 2), (key517, 2), (key555, 2), (key517, 2), (key555, 2), (key524, 2), (key517, -2), (key549, -2), (key517, -2), (key555, 6), (key524, -2), (key555, -2), (key524, -2)]

theorem rawRowCheck17525 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17525 := by decide +kernel

def row17525 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

theorem rowCheck17525 : row17525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17525 := by decide +kernel

theorem rowEval17525 (x : Key → ℝ) : Integer.Sparse.eval row17525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17525, Integer.Sparse.eval_collectBalanced, rawRowCheck17525]

def rawRow17526 : Integer.Sparse Key := [(key524, -2), (key524, -2), (key517, -2), (key517, 6), (key555, -2), (key555, -2), (key549, -2), (key555, 2), (key555, 2), (key524, 2), (key524, 2), (key517, 2), (key517, 2), (key549, -2), (key517, -2), (key517, -2), (key555, 6), (key555, -2), (key524, -2), (key524, -2)]

theorem rawRowCheck17526 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17526 := by decide +kernel

def row17526 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

theorem rowCheck17526 : row17526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17526 := by decide +kernel

theorem rowEval17526 (x : Key → ℝ) : Integer.Sparse.eval row17526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17526, Integer.Sparse.eval_collectBalanced, rawRowCheck17526]

def rawRow17527 : Integer.Sparse Key := [(key549, -2), (key555, -2), (key555, -2), (key555, 6), (key517, -2), (key524, -2), (key524, -2), (key517, 2), (key524, 2), (key517, 2), (key555, 2), (key524, 2), (key555, 2), (key524, -2), (key524, -2), (key555, -2), (key517, 6), (key517, -2), (key517, -2), (key549, -2)]

theorem rawRowCheck17527 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form11 = rawRow17527 := by decide +kernel

def row17527 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

theorem rowCheck17527 : row17527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17527 := by decide +kernel

theorem rowEval17527 (x : Key → ℝ) : Integer.Sparse.eval row17527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17527, Integer.Sparse.eval_collectBalanced, rawRowCheck17527]

def rawRow17528 : Integer.Sparse Key := [(key555, -2), (key549, -2), (key555, -2), (key555, 6), (key524, -2), (key517, -2), (key524, -2), (key524, 2), (key517, 2), (key555, 2), (key517, 2), (key555, 2), (key524, 2), (key524, -2), (key555, -2), (key524, -2), (key517, 6), (key517, -2), (key549, -2), (key517, -2)]

theorem rawRowCheck17528 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form11 = rawRow17528 := by decide +kernel

def row17528 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

theorem rowCheck17528 : row17528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17528 := by decide +kernel

theorem rowEval17528 (x : Key → ℝ) : Integer.Sparse.eval row17528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 0, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17528, Integer.Sparse.eval_collectBalanced, rawRowCheck17528]

def rawRow17529 : Integer.Sparse Key := [(key555, -2), (key555, -2), (key549, -2), (key555, 6), (key524, -2), (key524, -2), (key517, -2), (key555, 2), (key555, 2), (key524, 2), (key524, 2), (key517, 2), (key517, 2), (key555, -2), (key524, -2), (key524, -2), (key517, 6), (key549, -2), (key517, -2), (key517, -2)]

theorem rawRowCheck17529 : GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form11 = rawRow17529 := by decide +kernel

def row17529 : Integer.Sparse Key := [(key517, 4), (key524, -4), (key549, -4), (key555, 4)]

theorem rowCheck17529 : row17529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17529 := by decide +kernel

theorem rowEval17529 (x : Key → ℝ) : Integer.Sparse.eval row17529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 0, 1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17529, Integer.Sparse.eval_collectBalanced, rawRowCheck17529]

def rawRow17530 : Integer.Sparse Key := [(key555, -2), (key555, -2), (key555, -2), (key549, 6), (key555, -2), (key555, -2), (key555, -2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key524, 2), (key517, -2), (key517, -2), (key517, -2), (key549, 6), (key517, -2), (key517, -2), (key517, -2)]

theorem rawRowCheck17530 : GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form11 = rawRow17530 := by decide +kernel

def row17530 : Integer.Sparse Key := [(key517, -12), (key524, 12), (key549, 12), (key555, -12)]

theorem rowCheck17530 : row17530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17530 := by decide +kernel

theorem rowEval17530 (x : Key → ℝ) : Integer.Sparse.eval row17530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 1, 1, 0, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17530, Integer.Sparse.eval_collectBalanced, rawRowCheck17530]

def rawRow17531 : Integer.Sparse Key := [(key1854, 2), (key1856, 2), (key1856, 2), (key1856, -2), (key1856, -2), (key1858, -2), (key1854, 2), (key1856, 2), (key1856, 2), (key1856, -1), (key1856, -1), (key1887, -1), (key1887, -1), (key1890, -1), (key1890, -1), (key1856, -2), (key1856, -2), (key1858, -2), (key1856, -1), (key1856, -1), (key1887, -1), (key1887, -1), (key1890, -1), (key1890, -1), (key1858, 4), (key1890, 4), (key1890, 4)]

theorem rawRowCheck17531 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form12 = rawRow17531 := by decide +kernel

def row17531 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

theorem rowCheck17531 : row17531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17531 := by decide +kernel

theorem rowEval17531 (x : Key → ℝ) : Integer.Sparse.eval row17531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 1, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17531, Integer.Sparse.eval_collectBalanced, rawRowCheck17531]

def rawRow17532 : Integer.Sparse Key := [(key1856, 2), (key1854, 2), (key1856, 2), (key1856, -2), (key1858, -2), (key1856, -2), (key1856, 2), (key1854, 2), (key1856, 2), (key1887, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -2), (key1858, -2), (key1856, -2), (key1887, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1890, 4), (key1858, 4), (key1890, 4)]

theorem rawRowCheck17532 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form12 = rawRow17532 := by decide +kernel

def row17532 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

theorem rowCheck17532 : row17532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17532 := by decide +kernel

theorem rowEval17532 (x : Key → ℝ) : Integer.Sparse.eval row17532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17532, Integer.Sparse.eval_collectBalanced, rawRowCheck17532]

def rawRow17533 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1854, 2), (key1858, -2), (key1856, -2), (key1856, -2), (key1856, 2), (key1856, 2), (key1854, 2), (key1890, -1), (key1887, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -1), (key1858, -2), (key1856, -2), (key1856, -2), (key1890, -1), (key1887, -1), (key1890, -1), (key1856, -1), (key1887, -1), (key1856, -1), (key1890, 4), (key1890, 4), (key1858, 4)]

theorem rawRowCheck17533 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form12 = rawRow17533 := by decide +kernel

def row17533 : Integer.Sparse Key := [(key1854, 4), (key1856, -4), (key1887, -4), (key1890, 4)]

theorem rowCheck17533 : row17533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17533 := by decide +kernel

theorem rowEval17533 (x : Key → ℝ) : Integer.Sparse.eval row17533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 1, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17533, Integer.Sparse.eval_collectBalanced, rawRowCheck17533]

def rawRow17534 : Integer.Sparse Key := [(key1856, 2), (key1856, 2), (key1858, 2), (key1854, -2), (key1856, -2), (key1856, -2), (key1887, 2), (key1887, 2), (key1890, 2), (key1854, -1), (key1856, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1887, -1), (key1887, -2), (key1890, -2), (key1890, -2), (key1856, -1), (key1858, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1890, -1), (key1856, 4), (key1856, 4), (key1887, 4)]

theorem rawRowCheck17534 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form12 = rawRow17534 := by decide +kernel

def row17534 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

theorem rowCheck17534 : row17534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17534 := by decide +kernel

theorem rowEval17534 (x : Key → ℝ) : Integer.Sparse.eval row17534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 0, 1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17534, Integer.Sparse.eval_collectBalanced, rawRowCheck17534]

def rawRow17535 : Integer.Sparse Key := [(key1856, 2), (key1858, 2), (key1856, 2), (key1856, -2), (key1854, -2), (key1856, -2), (key1887, 2), (key1890, 2), (key1887, 2), (key1856, -1), (key1854, -1), (key1887, -1), (key1854, -1), (key1887, -1), (key1856, -1), (key1890, -2), (key1887, -2), (key1890, -2), (key1858, -1), (key1856, -1), (key1890, -1), (key1856, -1), (key1890, -1), (key1858, -1), (key1856, 4), (key1887, 4), (key1856, 4)]

theorem rawRowCheck17535 : GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form12 = rawRow17535 := by decide +kernel

def row17535 : Integer.Sparse Key := [(key1854, -4), (key1856, 4), (key1887, 4), (key1890, -4)]

theorem rowCheck17535 : row17535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17535 := by decide +kernel

theorem rowEval17535 (x : Key → ℝ) : Integer.Sparse.eval row17535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 1, 0, 1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17535, Integer.Sparse.eval_collectBalanced, rawRowCheck17535]

end MUB6.Certificate.GramRows

end OAI
