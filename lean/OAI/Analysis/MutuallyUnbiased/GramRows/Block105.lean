import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
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

def rawRow10368 : Integer.Sparse Key := [(key93, 2), (key158, 2), (key158, 2), (key10, 2), (key189, 2), (key189, 2), (key13, 2), (key13, 2), (key158, 2), (key158, 2), (key192, 2), (key192, 2), (key96, -2), (key96, -2), (key170, -2), (key13, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key192, -2), (key15, -2), (key163, -2), (key163, -2)]

theorem rawRowCheck10368 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18 = rawRow10368 := by decide +kernel

def row10368 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

theorem rowCheck10368 : row10368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10368 := by decide +kernel

theorem rowEval10368 (x : Key → ℝ) : Integer.Sparse.eval row10368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10368, Integer.Sparse.eval_collectBalanced, rawRowCheck10368]

def rawRow10369 : Integer.Sparse Key := [(key158, 2), (key93, 2), (key158, 2), (key189, 2), (key10, 2), (key189, 2), (key158, 2), (key192, 2), (key13, 2), (key192, 2), (key13, 2), (key158, 2), (key96, -2), (key170, -2), (key96, -2), (key158, -2), (key192, -2), (key13, -2), (key192, -2), (key13, -2), (key158, -2), (key163, -2), (key15, -2), (key163, -2)]

theorem rawRowCheck10369 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18 = rawRow10369 := by decide +kernel

def row10369 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

theorem rowCheck10369 : row10369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10369 := by decide +kernel

theorem rowEval10369 (x : Key → ℝ) : Integer.Sparse.eval row10369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10369, Integer.Sparse.eval_collectBalanced, rawRowCheck10369]

def rawRow10370 : Integer.Sparse Key := [(key158, 2), (key158, 2), (key93, 2), (key189, 2), (key189, 2), (key10, 2), (key192, 2), (key158, 2), (key192, 2), (key13, 2), (key158, 2), (key13, 2), (key170, -2), (key96, -2), (key96, -2), (key192, -2), (key158, -2), (key192, -2), (key13, -2), (key158, -2), (key13, -2), (key163, -2), (key163, -2), (key15, -2)]

theorem rawRowCheck10370 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18 = rawRow10370 := by decide +kernel

def row10370 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 4), (key163, -4), (key170, -2), (key189, 4)]

theorem rowCheck10370 : row10370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10370 := by decide +kernel

theorem rowEval10370 (x : Key → ℝ) : Integer.Sparse.eval row10370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck10370, Integer.Sparse.eval_collectBalanced, rawRowCheck10370]

def rawRow10371 : Integer.Sparse Key := [(key169, 2), (key189, 2), (key192, 2), (key13, 2), (key158, 2), (key192, 2), (key10, 2), (key13, 2), (key93, 2), (key158, 2), (key169, 2), (key189, 2), (key158, -2), (key163, -2), (key192, -2), (key13, -2), (key15, -2), (key96, -2), (key163, -2), (key170, -2), (key192, -2), (key13, -2), (key96, -2), (key158, -2)]

theorem rawRowCheck10371 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18 = rawRow10371 := by decide +kernel

def row10371 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10371 : row10371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10371 := by decide +kernel

theorem rowEval10371 (x : Key → ℝ) : Integer.Sparse.eval row10371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10371, Integer.Sparse.eval_collectBalanced, rawRowCheck10371]

def rawRow10372 : Integer.Sparse Key := [(key169, 2), (key192, 2), (key189, 2), (key13, 2), (key192, 2), (key158, 2), (key13, 2), (key10, 2), (key158, 2), (key93, 2), (key189, 2), (key169, 2), (key163, -2), (key158, -2), (key192, -2), (key15, -2), (key13, -2), (key163, -2), (key96, -2), (key192, -2), (key170, -2), (key13, -2), (key158, -2), (key96, -2)]

theorem rawRowCheck10372 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18 = rawRow10372 := by decide +kernel

def row10372 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10372 : row10372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10372 := by decide +kernel

theorem rowEval10372 (x : Key → ℝ) : Integer.Sparse.eval row10372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10372, Integer.Sparse.eval_collectBalanced, rawRowCheck10372]

def rawRow10373 : Integer.Sparse Key := [(key189, 2), (key169, 2), (key192, 2), (key158, 2), (key13, 2), (key192, 2), (key93, 2), (key158, 2), (key10, 2), (key189, 2), (key13, 2), (key158, 2), (key158, -2), (key192, -2), (key163, -2), (key96, -2), (key170, -2), (key13, -2), (key192, -2), (key15, -2), (key163, -2), (key96, -2), (key13, -2), (key158, -2)]

theorem rawRowCheck10373 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18 = rawRow10373 := by decide +kernel

def row10373 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 2), (key163, -4), (key169, 2), (key170, -2), (key189, 4)]

theorem rowCheck10373 : row10373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10373 := by decide +kernel

theorem rowEval10373 (x : Key → ℝ) : Integer.Sparse.eval row10373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10373, Integer.Sparse.eval_collectBalanced, rawRowCheck10373]

def rawRow10374 : Integer.Sparse Key := [(key189, 2), (key192, 2), (key169, 2), (key158, 2), (key192, 2), (key13, 2), (key158, 2), (key93, 2), (key189, 2), (key10, 2), (key158, 2), (key13, 2), (key192, -2), (key158, -2), (key163, -2), (key170, -2), (key96, -2), (key192, -2), (key13, -2), (key163, -2), (key15, -2), (key96, -2), (key158, -2), (key13, -2)]

theorem rawRowCheck10374 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18 = rawRow10374 := by decide +kernel

def row10374 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key158, 2), (key163, -4), (key169, 2), (key170, -2), (key189, 4)]

theorem rowCheck10374 : row10374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10374 := by decide +kernel

theorem rowEval10374 (x : Key → ℝ) : Integer.Sparse.eval row10374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck10374, Integer.Sparse.eval_collectBalanced, rawRowCheck10374]

def rawRow10375 : Integer.Sparse Key := [(key192, 2), (key169, 2), (key189, 2), (key192, 2), (key13, 2), (key158, 2), (key169, 2), (key189, 2), (key13, 2), (key158, 2), (key10, 2), (key93, 2), (key163, -2), (key192, -2), (key158, -2), (key163, -2), (key192, -2), (key15, -2), (key170, -2), (key13, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2)]

theorem rawRowCheck10375 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18 = rawRow10375 := by decide +kernel

def row10375 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10375 : row10375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10375 := by decide +kernel

theorem rowEval10375 (x : Key → ℝ) : Integer.Sparse.eval row10375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10375, Integer.Sparse.eval_collectBalanced, rawRowCheck10375]

def rawRow10376 : Integer.Sparse Key := [(key192, 2), (key189, 2), (key169, 2), (key192, 2), (key158, 2), (key13, 2), (key189, 2), (key169, 2), (key158, 2), (key13, 2), (key93, 2), (key10, 2), (key192, -2), (key163, -2), (key158, -2), (key192, -2), (key163, -2), (key170, -2), (key15, -2), (key96, -2), (key13, -2), (key158, -2), (key96, -2), (key13, -2)]

theorem rawRowCheck10376 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18 = rawRow10376 := by decide +kernel

def row10376 : Integer.Sparse Key := [(key10, 2), (key15, -2), (key93, 2), (key96, -4), (key163, -4), (key169, 4), (key170, -2), (key189, 4)]

theorem rowCheck10376 : row10376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10376 := by decide +kernel

theorem rowEval10376 (x : Key → ℝ) : Integer.Sparse.eval row10376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck10376, Integer.Sparse.eval_collectBalanced, rawRowCheck10376]

def rawRow10377 : Integer.Sparse Key := [(key13, 2), (key13, 2), (key15, 2), (key96, 2), (key96, 2), (key170, 2), (key158, 2), (key163, 2), (key158, 2), (key192, 2), (key163, 2), (key192, 2), (key10, -2), (key13, -2), (key13, -2), (key93, -2), (key96, -2), (key93, -2), (key158, -2), (key96, -2), (key158, -2), (key169, -2), (key169, -2), (key189, -2)]

theorem rawRowCheck10377 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form18 = rawRow10377 := by decide +kernel

def row10377 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10377 : row10377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10377 := by decide +kernel

theorem rowEval10377 (x : Key → ℝ) : Integer.Sparse.eval row10377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10377, Integer.Sparse.eval_collectBalanced, rawRowCheck10377]

def rawRow10378 : Integer.Sparse Key := [(key13, 2), (key15, 2), (key13, 2), (key96, 2), (key170, 2), (key96, 2), (key163, 2), (key158, 2), (key192, 2), (key158, 2), (key192, 2), (key163, 2), (key13, -2), (key10, -2), (key13, -2), (key96, -2), (key93, -2), (key158, -2), (key93, -2), (key158, -2), (key96, -2), (key169, -2), (key189, -2), (key169, -2)]

theorem rawRowCheck10378 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form18 = rawRow10378 := by decide +kernel

def row10378 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10378 : row10378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10378 := by decide +kernel

theorem rowEval10378 (x : Key → ℝ) : Integer.Sparse.eval row10378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10378, Integer.Sparse.eval_collectBalanced, rawRowCheck10378]

def rawRow10379 : Integer.Sparse Key := [(key15, 2), (key13, 2), (key13, 2), (key170, 2), (key96, 2), (key96, 2), (key192, 2), (key192, 2), (key163, 2), (key163, 2), (key158, 2), (key158, 2), (key13, -2), (key13, -2), (key10, -2), (key158, -2), (key158, -2), (key96, -2), (key96, -2), (key93, -2), (key93, -2), (key189, -2), (key169, -2), (key169, -2)]

theorem rawRowCheck10379 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form18 = rawRow10379 := by decide +kernel

def row10379 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10379 : row10379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10379 := by decide +kernel

theorem rowEval10379 (x : Key → ℝ) : Integer.Sparse.eval row10379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10379, Integer.Sparse.eval_collectBalanced, rawRowCheck10379]

def rawRow10380 : Integer.Sparse Key := [(key96, 2), (key158, 2), (key163, 2), (key13, 2), (key158, 2), (key192, 2), (key13, 2), (key15, 2), (key96, 2), (key170, 2), (key163, 2), (key192, 2), (key93, -2), (key96, -2), (key158, -2), (key10, -2), (key13, -2), (key93, -2), (key158, -2), (key169, -2), (key189, -2), (key13, -2), (key96, -2), (key158, -2)]

theorem rawRowCheck10380 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form18 = rawRow10380 := by decide +kernel

def row10380 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10380 : row10380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10380 := by decide +kernel

theorem rowEval10380 (x : Key → ℝ) : Integer.Sparse.eval row10380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10380, Integer.Sparse.eval_collectBalanced, rawRowCheck10380]

def rawRow10381 : Integer.Sparse Key := [(key96, 2), (key163, 2), (key158, 2), (key13, 2), (key192, 2), (key158, 2), (key15, 2), (key13, 2), (key170, 2), (key96, 2), (key192, 2), (key163, 2), (key96, -2), (key93, -2), (key158, -2), (key13, -2), (key10, -2), (key158, -2), (key93, -2), (key189, -2), (key169, -2), (key13, -2), (key158, -2), (key96, -2)]

theorem rawRowCheck10381 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form18 = rawRow10381 := by decide +kernel

def row10381 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10381 : row10381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10381 := by decide +kernel

theorem rowEval10381 (x : Key → ℝ) : Integer.Sparse.eval row10381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10381, Integer.Sparse.eval_collectBalanced, rawRowCheck10381]

def rawRow10382 : Integer.Sparse Key := [(key158, 2), (key96, 2), (key163, 2), (key158, 2), (key13, 2), (key192, 2), (key96, 2), (key163, 2), (key13, 2), (key192, 2), (key15, 2), (key170, 2), (key93, -2), (key158, -2), (key96, -2), (key93, -2), (key158, -2), (key10, -2), (key189, -2), (key13, -2), (key158, -2), (key96, -2), (key13, -2), (key158, -2)]

theorem rawRowCheck10382 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form18 = rawRow10382 := by decide +kernel

def row10382 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -4), (key163, 4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10382 : row10382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10382 := by decide +kernel

theorem rowEval10382 (x : Key → ℝ) : Integer.Sparse.eval row10382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck10382, Integer.Sparse.eval_collectBalanced, rawRowCheck10382]

def rawRow10383 : Integer.Sparse Key := [(key158, 2), (key163, 2), (key96, 2), (key158, 2), (key192, 2), (key13, 2), (key163, 2), (key96, 2), (key192, 2), (key13, 2), (key170, 2), (key15, 2), (key158, -2), (key93, -2), (key96, -2), (key158, -2), (key93, -2), (key189, -2), (key10, -2), (key158, -2), (key13, -2), (key96, -2), (key158, -2), (key13, -2)]

theorem rawRowCheck10383 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form18 = rawRow10383 := by decide +kernel

def row10383 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -4), (key163, 4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10383 : row10383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10383 := by decide +kernel

theorem rowEval10383 (x : Key → ℝ) : Integer.Sparse.eval row10383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck10383, Integer.Sparse.eval_collectBalanced, rawRowCheck10383]

def rawRow10384 : Integer.Sparse Key := [(key163, 2), (key96, 2), (key158, 2), (key192, 2), (key13, 2), (key158, 2), (key170, 2), (key192, 2), (key15, 2), (key163, 2), (key13, 2), (key96, 2), (key96, -2), (key158, -2), (key93, -2), (key169, -2), (key189, -2), (key13, -2), (key158, -2), (key10, -2), (key93, -2), (key158, -2), (key13, -2), (key96, -2)]

theorem rawRowCheck10384 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form18 = rawRow10384 := by decide +kernel

def row10384 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10384 : row10384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10384 := by decide +kernel

theorem rowEval10384 (x : Key → ℝ) : Integer.Sparse.eval row10384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10384, Integer.Sparse.eval_collectBalanced, rawRowCheck10384]

def rawRow10385 : Integer.Sparse Key := [(key163, 2), (key158, 2), (key96, 2), (key192, 2), (key158, 2), (key13, 2), (key192, 2), (key170, 2), (key163, 2), (key15, 2), (key96, 2), (key13, 2), (key158, -2), (key96, -2), (key93, -2), (key189, -2), (key169, -2), (key158, -2), (key13, -2), (key93, -2), (key10, -2), (key158, -2), (key96, -2), (key13, -2)]

theorem rawRowCheck10385 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form18 = rawRow10385 := by decide +kernel

def row10385 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key158, -2), (key163, 4), (key169, -2), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10385 : row10385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10385 := by decide +kernel

theorem rowEval10385 (x : Key → ℝ) : Integer.Sparse.eval row10385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck10385, Integer.Sparse.eval_collectBalanced, rawRowCheck10385]

def rawRow10386 : Integer.Sparse Key := [(key170, 2), (key192, 2), (key192, 2), (key15, 2), (key163, 2), (key163, 2), (key13, 2), (key13, 2), (key96, 2), (key96, 2), (key158, 2), (key158, 2), (key169, -2), (key169, -2), (key189, -2), (key13, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key10, -2), (key93, -2), (key93, -2)]

theorem rawRowCheck10386 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form18 = rawRow10386 := by decide +kernel

def row10386 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10386 : row10386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10386 := by decide +kernel

theorem rowEval10386 (x : Key → ℝ) : Integer.Sparse.eval row10386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10386, Integer.Sparse.eval_collectBalanced, rawRowCheck10386]

def rawRow10387 : Integer.Sparse Key := [(key192, 2), (key170, 2), (key192, 2), (key163, 2), (key15, 2), (key163, 2), (key96, 2), (key158, 2), (key13, 2), (key158, 2), (key13, 2), (key96, 2), (key169, -2), (key189, -2), (key169, -2), (key96, -2), (key158, -2), (key13, -2), (key158, -2), (key13, -2), (key96, -2), (key93, -2), (key10, -2), (key93, -2)]

theorem rawRowCheck10387 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form18 = rawRow10387 := by decide +kernel

def row10387 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10387 : row10387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10387 := by decide +kernel

theorem rowEval10387 (x : Key → ℝ) : Integer.Sparse.eval row10387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck10387, Integer.Sparse.eval_collectBalanced, rawRowCheck10387]

def rawRow10388 : Integer.Sparse Key := [(key192, 2), (key192, 2), (key170, 2), (key163, 2), (key163, 2), (key15, 2), (key158, 2), (key96, 2), (key158, 2), (key13, 2), (key96, 2), (key13, 2), (key189, -2), (key169, -2), (key169, -2), (key158, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2), (key13, -2), (key93, -2), (key93, -2), (key10, -2)]

theorem rawRowCheck10388 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form18 = rawRow10388 := by decide +kernel

def row10388 : Integer.Sparse Key := [(key10, -2), (key15, 2), (key93, -4), (key163, 4), (key169, -4), (key170, 2), (key189, -2), (key192, 4)]

theorem rowCheck10388 : row10388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10388 := by decide +kernel

theorem rowEval10388 (x : Key → ℝ) : Integer.Sparse.eval row10388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block3.form18) x := by
  rw [rowCheck10388, Integer.Sparse.eval_collectBalanced, rawRowCheck10388]

def rawRow10389 : Integer.Sparse Key := [(key2420, 2), (key2427, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2495, 2), (key2427, 2), (key2427, 2), (key2495, 2), (key2495, 2), (key2504, 2), (key2504, 2), (key2427, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2504, -2)]

theorem rawRowCheck10389 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form0 = rawRow10389 := by decide +kernel

def row10389 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

theorem rowCheck10389 : row10389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10389 := by decide +kernel

theorem rowEval10389 (x : Key → ℝ) : Integer.Sparse.eval row10389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10389, Integer.Sparse.eval_collectBalanced, rawRowCheck10389]

def rawRow10390 : Integer.Sparse Key := [(key2427, 2), (key2420, 2), (key2427, 2), (key2495, 2), (key2420, 2), (key2495, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2495, 2), (key2427, -2), (key2438, -2), (key2427, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2504, -2), (key2438, -2), (key2504, -2)]

theorem rawRowCheck10390 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form0 = rawRow10390 := by decide +kernel

def row10390 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

theorem rowCheck10390 : row10390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10390 := by decide +kernel

theorem rowEval10390 (x : Key → ℝ) : Integer.Sparse.eval row10390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10390, Integer.Sparse.eval_collectBalanced, rawRowCheck10390]

def rawRow10391 : Integer.Sparse Key := [(key2427, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2495, 2), (key2420, 2), (key2504, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2495, 2), (key2427, 2), (key2438, -2), (key2427, -2), (key2427, -2), (key2504, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2504, -2), (key2504, -2), (key2438, -2)]

theorem rawRowCheck10391 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form0 = rawRow10391 := by decide +kernel

def row10391 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

theorem rowCheck10391 : row10391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10391 := by decide +kernel

theorem rowEval10391 (x : Key → ℝ) : Integer.Sparse.eval row10391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10391, Integer.Sparse.eval_collectBalanced, rawRowCheck10391]

def rawRow10392 : Integer.Sparse Key := [(key2495, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2420, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2427, 2), (key2495, 2), (key2495, -2), (key2504, -2), (key2504, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2427, -2), (key2427, -2), (key2495, -2)]

theorem rawRowCheck10392 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form0 = rawRow10392 := by decide +kernel

def row10392 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

theorem rowCheck10392 : row10392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10392 := by decide +kernel

theorem rowEval10392 (x : Key → ℝ) : Integer.Sparse.eval row10392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10392, Integer.Sparse.eval_collectBalanced, rawRowCheck10392]

def rawRow10393 : Integer.Sparse Key := [(key2495, 2), (key2504, 2), (key2495, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2420, 2), (key2495, 2), (key2427, 2), (key2504, -2), (key2495, -2), (key2504, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2427, -2), (key2495, -2), (key2427, -2)]

theorem rawRowCheck10393 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form0 = rawRow10393 := by decide +kernel

def row10393 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

theorem rowCheck10393 : row10393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10393 := by decide +kernel

theorem rowEval10393 (x : Key → ℝ) : Integer.Sparse.eval row10393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10393, Integer.Sparse.eval_collectBalanced, rawRowCheck10393]

def rawRow10394 : Integer.Sparse Key := [(key2504, 2), (key2495, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2495, 2), (key2495, 2), (key2427, 2), (key2427, 2), (key2420, 2), (key2420, 2), (key2504, -2), (key2504, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2438, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2427, -2)]

theorem rawRowCheck10394 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form0 = rawRow10394 := by decide +kernel

def row10394 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, 4), (key2504, -4)]

theorem rowCheck10394 : row10394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10394 := by decide +kernel

theorem rowEval10394 (x : Key → ℝ) : Integer.Sparse.eval row10394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10394, Integer.Sparse.eval_collectBalanced, rawRowCheck10394]

def rawRow10395 : Integer.Sparse Key := [(key2427, 2), (key2427, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2438, 2), (key2427, 2), (key2504, 2), (key2438, 2), (key2504, 2), (key2420, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2495, -2)]

theorem rawRowCheck10395 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form0 = rawRow10395 := by decide +kernel

def row10395 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

theorem rowCheck10395 : row10395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10395 := by decide +kernel

theorem rowEval10395 (x : Key → ℝ) : Integer.Sparse.eval row10395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck10395, Integer.Sparse.eval_collectBalanced, rawRowCheck10395]

def rawRow10396 : Integer.Sparse Key := [(key2427, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2438, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2504, 2), (key2438, 2), (key2427, -2), (key2420, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2427, -2)]

theorem rawRowCheck10396 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form0 = rawRow10396 := by decide +kernel

def row10396 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

theorem rowCheck10396 : row10396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10396 := by decide +kernel

theorem rowEval10396 (x : Key → ℝ) : Integer.Sparse.eval row10396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10396, Integer.Sparse.eval_collectBalanced, rawRowCheck10396]

def rawRow10397 : Integer.Sparse Key := [(key2438, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2504, 2), (key2438, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2427, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2427, -2)]

theorem rawRowCheck10397 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form0 = rawRow10397 := by decide +kernel

def row10397 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

theorem rowCheck10397 : row10397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10397 := by decide +kernel

theorem rowEval10397 (x : Key → ℝ) : Integer.Sparse.eval row10397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10397, Integer.Sparse.eval_collectBalanced, rawRowCheck10397]

def rawRow10398 : Integer.Sparse Key := [(key2504, 2), (key2504, 2), (key2504, 2), (key2438, 2), (key2438, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2495, -2), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2420, -2)]

theorem rawRowCheck10398 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form0 = rawRow10398 := by decide +kernel

def row10398 : Integer.Sparse Key := [(key2420, -6), (key2438, 6), (key2495, -6), (key2504, 6)]

theorem rowCheck10398 : row10398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10398 := by decide +kernel

theorem rowEval10398 (x : Key → ℝ) : Integer.Sparse.eval row10398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck10398, Integer.Sparse.eval_collectBalanced, rawRowCheck10398]

def rawRow10399 : Integer.Sparse Key := [(key1045, -24), (key1045, 6), (key1045, 6), (key1131, 6), (key1131, 6)]

theorem rawRowCheck10399 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form1 = rawRow10399 := by decide +kernel

def row10399 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

theorem rowCheck10399 : row10399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10399 := by decide +kernel

theorem rowEval10399 (x : Key → ℝ) : Integer.Sparse.eval row10399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10399, Integer.Sparse.eval_collectBalanced, rawRowCheck10399]

def rawRow10400 : Integer.Sparse Key := [(key1045, -24), (key1045, 6), (key1131, 6), (key1045, 6), (key1131, 6)]

theorem rawRowCheck10400 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form1 = rawRow10400 := by decide +kernel

def row10400 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

theorem rowCheck10400 : row10400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10400 := by decide +kernel

theorem rowEval10400 (x : Key → ℝ) : Integer.Sparse.eval row10400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10400, Integer.Sparse.eval_collectBalanced, rawRowCheck10400]

def rawRow10401 : Integer.Sparse Key := [(key1045, -24), (key1045, 6), (key1131, 6), (key1131, 6), (key1045, 6)]

theorem rawRowCheck10401 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form1 = rawRow10401 := by decide +kernel

def row10401 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

theorem rowCheck10401 : row10401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10401 := by decide +kernel

theorem rowEval10401 (x : Key → ℝ) : Integer.Sparse.eval row10401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10401, Integer.Sparse.eval_collectBalanced, rawRowCheck10401]

def rawRow10402 : Integer.Sparse Key := [(key1045, -24), (key1131, 6), (key1045, 6), (key1045, 6), (key1131, 6)]

theorem rawRowCheck10402 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form1 = rawRow10402 := by decide +kernel

def row10402 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

theorem rowCheck10402 : row10402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10402 := by decide +kernel

theorem rowEval10402 (x : Key → ℝ) : Integer.Sparse.eval row10402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10402, Integer.Sparse.eval_collectBalanced, rawRowCheck10402]

def rawRow10403 : Integer.Sparse Key := [(key1045, -24), (key1131, 6), (key1045, 6), (key1131, 6), (key1045, 6)]

theorem rawRowCheck10403 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form1 = rawRow10403 := by decide +kernel

def row10403 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

theorem rowCheck10403 : row10403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10403 := by decide +kernel

theorem rowEval10403 (x : Key → ℝ) : Integer.Sparse.eval row10403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10403, Integer.Sparse.eval_collectBalanced, rawRowCheck10403]

def rawRow10404 : Integer.Sparse Key := [(key1045, -24), (key1131, 6), (key1131, 6), (key1045, 6), (key1045, 6)]

theorem rawRowCheck10404 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form1 = rawRow10404 := by decide +kernel

def row10404 : Integer.Sparse Key := [(key1045, -12), (key1131, 12)]

theorem rowCheck10404 : row10404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10404 := by decide +kernel

theorem rowEval10404 (x : Key → ℝ) : Integer.Sparse.eval row10404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10404, Integer.Sparse.eval_collectBalanced, rawRowCheck10404]

def rawRow10405 : Integer.Sparse Key := [(key1131, -24), (key1045, 6), (key1045, 6), (key1045, 6), (key1131, 6)]

theorem rawRowCheck10405 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form1 = rawRow10405 := by decide +kernel

def row10405 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

theorem rowCheck10405 : row10405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10405 := by decide +kernel

theorem rowEval10405 (x : Key → ℝ) : Integer.Sparse.eval row10405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck10405, Integer.Sparse.eval_collectBalanced, rawRowCheck10405]

def rawRow10406 : Integer.Sparse Key := [(key1131, -24), (key1045, 6), (key1045, 6), (key1131, 6), (key1045, 6)]

theorem rawRowCheck10406 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form1 = rawRow10406 := by decide +kernel

def row10406 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

theorem rowCheck10406 : row10406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10406 := by decide +kernel

theorem rowEval10406 (x : Key → ℝ) : Integer.Sparse.eval row10406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10406, Integer.Sparse.eval_collectBalanced, rawRowCheck10406]

def rawRow10407 : Integer.Sparse Key := [(key1131, -24), (key1045, 6), (key1131, 6), (key1045, 6), (key1045, 6)]

theorem rawRowCheck10407 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form1 = rawRow10407 := by decide +kernel

def row10407 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

theorem rowCheck10407 : row10407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10407 := by decide +kernel

theorem rowEval10407 (x : Key → ℝ) : Integer.Sparse.eval row10407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10407, Integer.Sparse.eval_collectBalanced, rawRowCheck10407]

def rawRow10408 : Integer.Sparse Key := [(key1131, -24), (key1131, 6), (key1045, 6), (key1045, 6), (key1045, 6)]

theorem rawRowCheck10408 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form1 = rawRow10408 := by decide +kernel

def row10408 : Integer.Sparse Key := [(key1045, 18), (key1131, -18)]

theorem rowCheck10408 : row10408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10408 := by decide +kernel

theorem rowEval10408 (x : Key → ℝ) : Integer.Sparse.eval row10408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck10408, Integer.Sparse.eval_collectBalanced, rawRowCheck10408]

def rawRow10409 : Integer.Sparse Key := [(key1050, -6), (key1050, -6), (key1058, -6), (key1058, -6), (key1050, 2), (key1050, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1136, 2), (key1136, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1138, 2)]

theorem rawRowCheck10409 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form2 = rawRow10409 := by decide +kernel

def row10409 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

theorem rowCheck10409 : row10409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10409 := by decide +kernel

theorem rowEval10409 (x : Key → ℝ) : Integer.Sparse.eval row10409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10409, Integer.Sparse.eval_collectBalanced, rawRowCheck10409]

def rawRow10410 : Integer.Sparse Key := [(key1050, -6), (key1058, -6), (key1050, -6), (key1058, -6), (key1050, 2), (key1058, 2), (key1050, 2), (key1136, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1138, 2), (key1058, 2), (key1138, 2)]

theorem rawRowCheck10410 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form2 = rawRow10410 := by decide +kernel

def row10410 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

theorem rowCheck10410 : row10410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10410 := by decide +kernel

theorem rowEval10410 (x : Key → ℝ) : Integer.Sparse.eval row10410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10410, Integer.Sparse.eval_collectBalanced, rawRowCheck10410]

def rawRow10411 : Integer.Sparse Key := [(key1058, -6), (key1050, -6), (key1050, -6), (key1058, -6), (key1058, 2), (key1050, 2), (key1050, 2), (key1138, 2), (key1136, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1050, 2), (key1138, 2), (key1138, 2), (key1058, 2)]

theorem rawRowCheck10411 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form2 = rawRow10411 := by decide +kernel

def row10411 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

theorem rowCheck10411 : row10411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10411 := by decide +kernel

theorem rowEval10411 (x : Key → ℝ) : Integer.Sparse.eval row10411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10411, Integer.Sparse.eval_collectBalanced, rawRowCheck10411]

def rawRow10412 : Integer.Sparse Key := [(key1050, -6), (key1058, -6), (key1058, -6), (key1050, -6), (key1136, 2), (key1138, 2), (key1138, 2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1050, 2), (key1050, 2), (key1136, 2)]

theorem rawRowCheck10412 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form2 = rawRow10412 := by decide +kernel

def row10412 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

theorem rowCheck10412 : row10412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10412 := by decide +kernel

theorem rowEval10412 (x : Key → ℝ) : Integer.Sparse.eval row10412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10412, Integer.Sparse.eval_collectBalanced, rawRowCheck10412]

def rawRow10413 : Integer.Sparse Key := [(key1058, -6), (key1050, -6), (key1058, -6), (key1050, -6), (key1138, 2), (key1136, 2), (key1138, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1050, 2), (key1136, 2), (key1050, 2)]

theorem rawRowCheck10413 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form2 = rawRow10413 := by decide +kernel

def row10413 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

theorem rowCheck10413 : row10413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10413 := by decide +kernel

theorem rowEval10413 (x : Key → ℝ) : Integer.Sparse.eval row10413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10413, Integer.Sparse.eval_collectBalanced, rawRowCheck10413]

def rawRow10414 : Integer.Sparse Key := [(key1058, -6), (key1058, -6), (key1050, -6), (key1050, -6), (key1138, 2), (key1138, 2), (key1136, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1136, 2), (key1050, 2), (key1050, 2)]

theorem rawRowCheck10414 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form2 = rawRow10414 := by decide +kernel

def row10414 : Integer.Sparse Key := [(key1050, -4), (key1058, -8), (key1136, 4), (key1138, 8)]

theorem rowCheck10414 : row10414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10414 := by decide +kernel

theorem rowEval10414 (x : Key → ℝ) : Integer.Sparse.eval row10414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10414, Integer.Sparse.eval_collectBalanced, rawRowCheck10414]

def rawRow10415 : Integer.Sparse Key := [(key1136, -6), (key1138, -6), (key1138, -6), (key1138, -6), (key1050, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1138, 2)]

theorem rawRowCheck10415 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form2 = rawRow10415 := by decide +kernel

def row10415 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

theorem rowCheck10415 : row10415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10415 := by decide +kernel

theorem rowEval10415 (x : Key → ℝ) : Integer.Sparse.eval row10415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck10415, Integer.Sparse.eval_collectBalanced, rawRowCheck10415]

def rawRow10416 : Integer.Sparse Key := [(key1138, -6), (key1136, -6), (key1138, -6), (key1138, -6), (key1058, 2), (key1050, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1138, 2), (key1058, 2)]

theorem rawRowCheck10416 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form2 = rawRow10416 := by decide +kernel

def row10416 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

theorem rowCheck10416 : row10416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10416 := by decide +kernel

theorem rowEval10416 (x : Key → ℝ) : Integer.Sparse.eval row10416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10416, Integer.Sparse.eval_collectBalanced, rawRowCheck10416]

def rawRow10417 : Integer.Sparse Key := [(key1138, -6), (key1138, -6), (key1136, -6), (key1138, -6), (key1058, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1058, 2)]

theorem rawRowCheck10417 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form2 = rawRow10417 := by decide +kernel

def row10417 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

theorem rowCheck10417 : row10417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10417 := by decide +kernel

theorem rowEval10417 (x : Key → ℝ) : Integer.Sparse.eval row10417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10417, Integer.Sparse.eval_collectBalanced, rawRowCheck10417]

def rawRow10418 : Integer.Sparse Key := [(key1138, -6), (key1138, -6), (key1138, -6), (key1136, -6), (key1138, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1050, 2)]

theorem rawRowCheck10418 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form2 = rawRow10418 := by decide +kernel

def row10418 : Integer.Sparse Key := [(key1050, 6), (key1058, 12), (key1136, -6), (key1138, -12)]

theorem rowCheck10418 : row10418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10418 := by decide +kernel

theorem rowEval10418 (x : Key → ℝ) : Integer.Sparse.eval row10418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck10418, Integer.Sparse.eval_collectBalanced, rawRowCheck10418]

def rawRow10419 : Integer.Sparse Key := [(key2677, -6), (key3045, -6), (key3094, -6), (key3094, -6), (key3045, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3122, 2)]

theorem rawRowCheck10419 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form3 = rawRow10419 := by decide +kernel

def row10419 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

theorem rowCheck10419 : row10419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10419 := by decide +kernel

theorem rowEval10419 (x : Key → ℝ) : Integer.Sparse.eval row10419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10419, Integer.Sparse.eval_collectBalanced, rawRowCheck10419]

def rawRow10420 : Integer.Sparse Key := [(key2677, -6), (key3094, -6), (key3045, -6), (key3094, -6), (key3059, 2), (key3045, 2), (key3059, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3122, 2), (key3059, 2), (key3094, 2)]

theorem rawRowCheck10420 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form3 = rawRow10420 := by decide +kernel

def row10420 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

theorem rowCheck10420 : row10420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10420 := by decide +kernel

theorem rowEval10420 (x : Key → ℝ) : Integer.Sparse.eval row10420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10420, Integer.Sparse.eval_collectBalanced, rawRowCheck10420]

def rawRow10421 : Integer.Sparse Key := [(key2677, -6), (key3094, -6), (key3094, -6), (key3045, -6), (key3059, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3045, 2), (key3122, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3094, 2), (key3059, 2)]

theorem rawRowCheck10421 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form3 = rawRow10421 := by decide +kernel

def row10421 : Integer.Sparse Key := [(key2677, -6), (key3045, -2), (key3059, 8), (key3094, -4), (key3122, 4)]

theorem rowCheck10421 : row10421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10421 := by decide +kernel

theorem rowEval10421 (x : Key → ℝ) : Integer.Sparse.eval row10421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10421, Integer.Sparse.eval_collectBalanced, rawRowCheck10421]

def rawRow10422 : Integer.Sparse Key := [(key2811, -6), (key2677, -6), (key3045, -6), (key3094, -6), (key3094, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3059, 2), (key3122, 2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

theorem rawRowCheck10422 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form3 = rawRow10422 := by decide +kernel

def row10422 : Integer.Sparse Key := [(key2677, -6), (key2811, -6), (key3045, -2), (key3059, 8), (key3094, 2), (key3122, 4)]

theorem rowCheck10422 : row10422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10422 := by decide +kernel

theorem rowEval10422 (x : Key → ℝ) : Integer.Sparse.eval row10422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10422, Integer.Sparse.eval_collectBalanced, rawRowCheck10422]

def rawRow10423 : Integer.Sparse Key := [(key2811, -6), (key2677, -6), (key3094, -6), (key3045, -6), (key3094, 2), (key3122, 2), (key3094, 2), (key3059, 2), (key3122, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

theorem rawRowCheck10423 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form3 = rawRow10423 := by decide +kernel

def row10423 : Integer.Sparse Key := [(key2677, -6), (key2811, -6), (key3045, -2), (key3059, 8), (key3094, 2), (key3122, 4)]

theorem rowCheck10423 : row10423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10423 := by decide +kernel

theorem rowEval10423 (x : Key → ℝ) : Integer.Sparse.eval row10423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10423, Integer.Sparse.eval_collectBalanced, rawRowCheck10423]

def rawRow10424 : Integer.Sparse Key := [(key2811, -6), (key2811, -6), (key2677, -6), (key3045, -6), (key3122, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3059, 2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

theorem rawRowCheck10424 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form3 = rawRow10424 := by decide +kernel

def row10424 : Integer.Sparse Key := [(key2677, -6), (key2811, -12), (key3045, -2), (key3059, 8), (key3094, 8), (key3122, 4)]

theorem rowCheck10424 : row10424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10424 := by decide +kernel

theorem rowEval10424 (x : Key → ℝ) : Integer.Sparse.eval row10424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10424, Integer.Sparse.eval_collectBalanced, rawRowCheck10424]

def rawRow10425 : Integer.Sparse Key := [(key2708, -6), (key2708, -6), (key2708, -6), (key2861, -6), (key2677, 2), (key2677, 2), (key2708, 2), (key2677, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

theorem rawRowCheck10425 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form3 = rawRow10425 := by decide +kernel

def row10425 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 6)]

theorem rowCheck10425 : row10425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10425 := by decide +kernel

theorem rowEval10425 (x : Key → ℝ) : Integer.Sparse.eval row10425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck10425, Integer.Sparse.eval_collectBalanced, rawRowCheck10425]

def rawRow10426 : Integer.Sparse Key := [(key2708, -6), (key2708, -6), (key2861, -6), (key2708, -6), (key2677, 2), (key2708, 2), (key2677, 2), (key2677, 2), (key3094, 2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

theorem rawRowCheck10426 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form3 = rawRow10426 := by decide +kernel

def row10426 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 6)]

theorem rowCheck10426 : row10426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10426 := by decide +kernel

theorem rowEval10426 (x : Key → ℝ) : Integer.Sparse.eval row10426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10426, Integer.Sparse.eval_collectBalanced, rawRowCheck10426]

def rawRow10427 : Integer.Sparse Key := [(key2708, -6), (key2861, -6), (key2708, -6), (key2708, -6), (key2708, 2), (key2677, 2), (key2677, 2), (key2811, 2), (key2677, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

theorem rawRowCheck10427 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form3 = rawRow10427 := by decide +kernel

def row10427 : Integer.Sparse Key := [(key2677, 6), (key2708, -16), (key2811, 2), (key2861, -6), (key3045, 6), (key3059, 4), (key3094, 4)]

theorem rowCheck10427 : row10427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10427 := by decide +kernel

theorem rowEval10427 (x : Key → ℝ) : Integer.Sparse.eval row10427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10427, Integer.Sparse.eval_collectBalanced, rawRowCheck10427]

def rawRow10428 : Integer.Sparse Key := [(key2861, -6), (key2708, -6), (key2708, -6), (key2708, -6), (key2811, 2), (key2811, 2), (key2811, 2), (key2708, 2), (key2708, 2), (key2708, 2), (key2677, 2), (key2677, 2), (key2677, 2), (key3045, 2), (key3045, 2), (key3045, 2)]

theorem rawRowCheck10428 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form3 = rawRow10428 := by decide +kernel

def row10428 : Integer.Sparse Key := [(key2677, 6), (key2708, -12), (key2811, 6), (key2861, -6), (key3045, 6)]

theorem rowCheck10428 : row10428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10428 := by decide +kernel

theorem rowEval10428 (x : Key → ℝ) : Integer.Sparse.eval row10428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck10428, Integer.Sparse.eval_collectBalanced, rawRowCheck10428]

def rawRow10429 : Integer.Sparse Key := [(key2416, -6), (key2416, -6), (key2423, -6), (key2423, -6), (key2416, 2), (key2416, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2489, 2), (key2489, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2491, 2)]

theorem rawRowCheck10429 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form4 = rawRow10429 := by decide +kernel

def row10429 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

theorem rowCheck10429 : row10429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10429 := by decide +kernel

theorem rowEval10429 (x : Key → ℝ) : Integer.Sparse.eval row10429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10429, Integer.Sparse.eval_collectBalanced, rawRowCheck10429]

def rawRow10430 : Integer.Sparse Key := [(key2416, -6), (key2423, -6), (key2416, -6), (key2423, -6), (key2416, 2), (key2423, 2), (key2416, 2), (key2489, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2491, 2), (key2423, 2), (key2491, 2)]

theorem rawRowCheck10430 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form4 = rawRow10430 := by decide +kernel

def row10430 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

theorem rowCheck10430 : row10430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10430 := by decide +kernel

theorem rowEval10430 (x : Key → ℝ) : Integer.Sparse.eval row10430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10430, Integer.Sparse.eval_collectBalanced, rawRowCheck10430]

def rawRow10431 : Integer.Sparse Key := [(key2423, -6), (key2416, -6), (key2416, -6), (key2423, -6), (key2423, 2), (key2416, 2), (key2416, 2), (key2491, 2), (key2489, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2416, 2), (key2491, 2), (key2491, 2), (key2423, 2)]

theorem rawRowCheck10431 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form4 = rawRow10431 := by decide +kernel

def row10431 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

theorem rowCheck10431 : row10431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10431 := by decide +kernel

theorem rowEval10431 (x : Key → ℝ) : Integer.Sparse.eval row10431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10431, Integer.Sparse.eval_collectBalanced, rawRowCheck10431]

def rawRow10432 : Integer.Sparse Key := [(key2416, -6), (key2423, -6), (key2423, -6), (key2416, -6), (key2489, 2), (key2491, 2), (key2491, 2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2416, 2), (key2416, 2), (key2489, 2)]

theorem rawRowCheck10432 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form4 = rawRow10432 := by decide +kernel

def row10432 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

theorem rowCheck10432 : row10432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10432 := by decide +kernel

theorem rowEval10432 (x : Key → ℝ) : Integer.Sparse.eval row10432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10432, Integer.Sparse.eval_collectBalanced, rawRowCheck10432]

def rawRow10433 : Integer.Sparse Key := [(key2423, -6), (key2416, -6), (key2423, -6), (key2416, -6), (key2491, 2), (key2489, 2), (key2491, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2416, 2), (key2489, 2), (key2416, 2)]

theorem rawRowCheck10433 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form4 = rawRow10433 := by decide +kernel

def row10433 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

theorem rowCheck10433 : row10433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10433 := by decide +kernel

theorem rowEval10433 (x : Key → ℝ) : Integer.Sparse.eval row10433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10433, Integer.Sparse.eval_collectBalanced, rawRowCheck10433]

def rawRow10434 : Integer.Sparse Key := [(key2423, -6), (key2423, -6), (key2416, -6), (key2416, -6), (key2491, 2), (key2491, 2), (key2489, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2489, 2), (key2416, 2), (key2416, 2)]

theorem rawRowCheck10434 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form4 = rawRow10434 := by decide +kernel

def row10434 : Integer.Sparse Key := [(key2416, -4), (key2423, -8), (key2489, 4), (key2491, 8)]

theorem rowCheck10434 : row10434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10434 := by decide +kernel

theorem rowEval10434 (x : Key → ℝ) : Integer.Sparse.eval row10434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10434, Integer.Sparse.eval_collectBalanced, rawRowCheck10434]

def rawRow10435 : Integer.Sparse Key := [(key2489, -6), (key2491, -6), (key2491, -6), (key2491, -6), (key2416, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2491, 2)]

theorem rawRowCheck10435 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form4 = rawRow10435 := by decide +kernel

def row10435 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

theorem rowCheck10435 : row10435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10435 := by decide +kernel

theorem rowEval10435 (x : Key → ℝ) : Integer.Sparse.eval row10435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck10435, Integer.Sparse.eval_collectBalanced, rawRowCheck10435]

def rawRow10436 : Integer.Sparse Key := [(key2491, -6), (key2489, -6), (key2491, -6), (key2491, -6), (key2423, 2), (key2416, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2491, 2), (key2423, 2)]

theorem rawRowCheck10436 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form4 = rawRow10436 := by decide +kernel

def row10436 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

theorem rowCheck10436 : row10436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10436 := by decide +kernel

theorem rowEval10436 (x : Key → ℝ) : Integer.Sparse.eval row10436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10436, Integer.Sparse.eval_collectBalanced, rawRowCheck10436]

def rawRow10437 : Integer.Sparse Key := [(key2491, -6), (key2491, -6), (key2489, -6), (key2491, -6), (key2423, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2423, 2)]

theorem rawRowCheck10437 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form4 = rawRow10437 := by decide +kernel

def row10437 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

theorem rowCheck10437 : row10437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10437 := by decide +kernel

theorem rowEval10437 (x : Key → ℝ) : Integer.Sparse.eval row10437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10437, Integer.Sparse.eval_collectBalanced, rawRowCheck10437]

def rawRow10438 : Integer.Sparse Key := [(key2491, -6), (key2491, -6), (key2491, -6), (key2489, -6), (key2491, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2416, 2)]

theorem rawRowCheck10438 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form4 = rawRow10438 := by decide +kernel

def row10438 : Integer.Sparse Key := [(key2416, 6), (key2423, 12), (key2489, -6), (key2491, -12)]

theorem rowCheck10438 : row10438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10438 := by decide +kernel

theorem rowEval10438 (x : Key → ℝ) : Integer.Sparse.eval row10438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form4) x := by
  rw [rowCheck10438, Integer.Sparse.eval_collectBalanced, rawRowCheck10438]

def rawRow10439 : Integer.Sparse Key := [(key2681, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2815, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2681, 1), (key2681, 1), (key2712, 1), (key2712, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2817, 1), (key2817, 1), (key2712, 1), (key2712, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2817, 1), (key2817, 1), (key2863, 1), (key2863, 1)]

theorem rawRowCheck10439 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form5 = rawRow10439 := by decide +kernel

def row10439 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

theorem rowCheck10439 : row10439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10439 := by decide +kernel

theorem rowEval10439 (x : Key → ℝ) : Integer.Sparse.eval row10439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10439, Integer.Sparse.eval_collectBalanced, rawRowCheck10439]

def rawRow10440 : Integer.Sparse Key := [(key2681, -2), (key2688, -2), (key2681, -2), (key2815, -2), (key2817, -2), (key2681, -2), (key2817, -2), (key2681, -2), (key2815, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2712, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2714, 1), (key2817, 1)]

theorem rawRowCheck10440 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form5 = rawRow10440 := by decide +kernel

def row10440 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

theorem rowCheck10440 : row10440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10440 := by decide +kernel

theorem rowEval10440 (x : Key → ℝ) : Integer.Sparse.eval row10440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10440, Integer.Sparse.eval_collectBalanced, rawRowCheck10440]

def rawRow10441 : Integer.Sparse Key := [(key2688, -2), (key2681, -2), (key2681, -2), (key2817, -2), (key2815, -2), (key2817, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2714, 1), (key2712, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2817, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2712, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2817, 1), (key2714, 1)]

theorem rawRowCheck10441 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form5 = rawRow10441 := by decide +kernel

def row10441 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

theorem rowCheck10441 : row10441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10441 := by decide +kernel

theorem rowEval10441 (x : Key → ℝ) : Integer.Sparse.eval row10441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10441, Integer.Sparse.eval_collectBalanced, rawRowCheck10441]

def rawRow10442 : Integer.Sparse Key := [(key2815, -2), (key2817, -2), (key2817, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2815, 1), (key2817, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2712, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2712, 1), (key2815, 1)]

theorem rawRowCheck10442 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form5 = rawRow10442 := by decide +kernel

def row10442 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

theorem rowCheck10442 : row10442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10442 := by decide +kernel

theorem rowEval10442 (x : Key → ℝ) : Integer.Sparse.eval row10442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10442, Integer.Sparse.eval_collectBalanced, rawRowCheck10442]

def rawRow10443 : Integer.Sparse Key := [(key2817, -2), (key2815, -2), (key2817, -2), (key2688, -2), (key2681, -2), (key2817, -2), (key2681, -2), (key2817, -2), (key2688, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2817, 1), (key2815, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2815, 1), (key2712, 1)]

theorem rawRowCheck10443 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form5 = rawRow10443 := by decide +kernel

def row10443 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

theorem rowCheck10443 : row10443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10443 := by decide +kernel

theorem rowEval10443 (x : Key → ℝ) : Integer.Sparse.eval row10443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10443, Integer.Sparse.eval_collectBalanced, rawRowCheck10443]

def rawRow10444 : Integer.Sparse Key := [(key2817, -2), (key2817, -2), (key2815, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2681, -2), (key2863, 1), (key2863, 1), (key2817, 1), (key2817, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2712, 1), (key2712, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2712, 1), (key2712, 1), (key2681, 1), (key2681, 1)]

theorem rawRowCheck10444 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form5 = rawRow10444 := by decide +kernel

def row10444 : Integer.Sparse Key := [(key2681, -4), (key2688, -4), (key2712, 4), (key2714, 4), (key2817, -4), (key2863, 4)]

theorem rowCheck10444 : row10444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10444 := by decide +kernel

theorem rowEval10444 (x : Key → ℝ) : Integer.Sparse.eval row10444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10444, Integer.Sparse.eval_collectBalanced, rawRowCheck10444]

def rawRow10445 : Integer.Sparse Key := [(key2712, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2714, -2), (key2712, -2), (key2863, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2863, -2), (key2681, 1), (key2688, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2714, 1), (key2817, 1)]

theorem rawRowCheck10445 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form5 = rawRow10445 := by decide +kernel

def row10445 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

theorem rowCheck10445 : row10445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10445 := by decide +kernel

theorem rowEval10445 (x : Key → ℝ) : Integer.Sparse.eval row10445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck10445, Integer.Sparse.eval_collectBalanced, rawRowCheck10445]

def rawRow10446 : Integer.Sparse Key := [(key2714, -2), (key2712, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2863, -2), (key2712, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2688, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2714, 1)]

theorem rawRowCheck10446 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form5 = rawRow10446 := by decide +kernel

def row10446 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

theorem rowCheck10446 : row10446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10446 := by decide +kernel

theorem rowEval10446 (x : Key → ℝ) : Integer.Sparse.eval row10446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10446, Integer.Sparse.eval_collectBalanced, rawRowCheck10446]

def rawRow10447 : Integer.Sparse Key := [(key2714, -2), (key2714, -2), (key2712, -2), (key2863, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2712, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1)]

theorem rawRowCheck10447 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form5 = rawRow10447 := by decide +kernel

def row10447 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

theorem rowCheck10447 : row10447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10447 := by decide +kernel

theorem rowEval10447 (x : Key → ℝ) : Integer.Sparse.eval row10447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10447, Integer.Sparse.eval_collectBalanced, rawRowCheck10447]

def rawRow10448 : Integer.Sparse Key := [(key2863, -2), (key2863, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2712, -2), (key2712, -2), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1)]

theorem rawRowCheck10448 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form5 = rawRow10448 := by decide +kernel

def row10448 : Integer.Sparse Key := [(key2681, 6), (key2688, 6), (key2712, -6), (key2714, -6), (key2817, 6), (key2863, -6)]

theorem rowCheck10448 : row10448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10448 := by decide +kernel

theorem rowEval10448 (x : Key → ℝ) : Integer.Sparse.eval row10448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form5) x := by
  rw [rowCheck10448, Integer.Sparse.eval_collectBalanced, rawRowCheck10448]

def rawRow10449 : Integer.Sparse Key := [(key2412, -24), (key3031, 6), (key3031, 6), (key3118, 6), (key3118, 6)]

theorem rawRowCheck10449 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form6 = rawRow10449 := by decide +kernel

def row10449 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

theorem rowCheck10449 : row10449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10449 := by decide +kernel

theorem rowEval10449 (x : Key → ℝ) : Integer.Sparse.eval row10449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10449, Integer.Sparse.eval_collectBalanced, rawRowCheck10449]

def rawRow10450 : Integer.Sparse Key := [(key2412, -24), (key3031, 6), (key3118, 6), (key3031, 6), (key3118, 6)]

theorem rawRowCheck10450 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form6 = rawRow10450 := by decide +kernel

def row10450 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

theorem rowCheck10450 : row10450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10450 := by decide +kernel

theorem rowEval10450 (x : Key → ℝ) : Integer.Sparse.eval row10450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10450, Integer.Sparse.eval_collectBalanced, rawRowCheck10450]

def rawRow10451 : Integer.Sparse Key := [(key2412, -24), (key3031, 6), (key3118, 6), (key3118, 6), (key3031, 6)]

theorem rawRowCheck10451 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form6 = rawRow10451 := by decide +kernel

def row10451 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

theorem rowCheck10451 : row10451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10451 := by decide +kernel

theorem rowEval10451 (x : Key → ℝ) : Integer.Sparse.eval row10451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10451, Integer.Sparse.eval_collectBalanced, rawRowCheck10451]

def rawRow10452 : Integer.Sparse Key := [(key2412, -24), (key3118, 6), (key3031, 6), (key3031, 6), (key3118, 6)]

theorem rawRowCheck10452 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form6 = rawRow10452 := by decide +kernel

def row10452 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

theorem rowCheck10452 : row10452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10452 := by decide +kernel

theorem rowEval10452 (x : Key → ℝ) : Integer.Sparse.eval row10452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10452, Integer.Sparse.eval_collectBalanced, rawRowCheck10452]

def rawRow10453 : Integer.Sparse Key := [(key2412, -24), (key3118, 6), (key3031, 6), (key3118, 6), (key3031, 6)]

theorem rawRowCheck10453 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form6 = rawRow10453 := by decide +kernel

def row10453 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

theorem rowCheck10453 : row10453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10453 := by decide +kernel

theorem rowEval10453 (x : Key → ℝ) : Integer.Sparse.eval row10453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10453, Integer.Sparse.eval_collectBalanced, rawRowCheck10453]

def rawRow10454 : Integer.Sparse Key := [(key2412, -24), (key3118, 6), (key3118, 6), (key3031, 6), (key3031, 6)]

theorem rawRowCheck10454 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form6 = rawRow10454 := by decide +kernel

def row10454 : Integer.Sparse Key := [(key2412, -24), (key3031, 12), (key3118, 12)]

theorem rowCheck10454 : row10454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10454 := by decide +kernel

theorem rowEval10454 (x : Key → ℝ) : Integer.Sparse.eval row10454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10454, Integer.Sparse.eval_collectBalanced, rawRowCheck10454]

def rawRow10455 : Integer.Sparse Key := [(key2485, -24), (key2412, 6), (key3031, 6), (key3031, 6), (key3118, 6)]

theorem rawRowCheck10455 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form6 = rawRow10455 := by decide +kernel

def row10455 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

theorem rowCheck10455 : row10455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10455 := by decide +kernel

theorem rowEval10455 (x : Key → ℝ) : Integer.Sparse.eval row10455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck10455, Integer.Sparse.eval_collectBalanced, rawRowCheck10455]

def rawRow10456 : Integer.Sparse Key := [(key2485, -24), (key2412, 6), (key3031, 6), (key3118, 6), (key3031, 6)]

theorem rawRowCheck10456 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form6 = rawRow10456 := by decide +kernel

def row10456 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

theorem rowCheck10456 : row10456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10456 := by decide +kernel

theorem rowEval10456 (x : Key → ℝ) : Integer.Sparse.eval row10456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10456, Integer.Sparse.eval_collectBalanced, rawRowCheck10456]

def rawRow10457 : Integer.Sparse Key := [(key2485, -24), (key2412, 6), (key3118, 6), (key3031, 6), (key3031, 6)]

theorem rawRowCheck10457 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form6 = rawRow10457 := by decide +kernel

def row10457 : Integer.Sparse Key := [(key2412, 6), (key2485, -24), (key3031, 12), (key3118, 6)]

theorem rowCheck10457 : row10457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10457 := by decide +kernel

theorem rowEval10457 (x : Key → ℝ) : Integer.Sparse.eval row10457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10457, Integer.Sparse.eval_collectBalanced, rawRowCheck10457]

def rawRow10458 : Integer.Sparse Key := [(key2485, -24), (key2485, 6), (key2412, 6), (key3031, 6), (key3031, 6)]

theorem rawRowCheck10458 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form6 = rawRow10458 := by decide +kernel

def row10458 : Integer.Sparse Key := [(key2412, 6), (key2485, -18), (key3031, 12)]

theorem rowCheck10458 : row10458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10458 := by decide +kernel

theorem rowEval10458 (x : Key → ℝ) : Integer.Sparse.eval row10458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form6) x := by
  rw [rowCheck10458, Integer.Sparse.eval_collectBalanced, rawRowCheck10458]

def rawRow10459 : Integer.Sparse Key := [(key2681, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2712, -2), (key2712, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2714, -2), (key2714, -2), (key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2)]

theorem rawRowCheck10459 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form7 = rawRow10459 := by decide +kernel

def row10459 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

theorem rowCheck10459 : row10459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10459 := by decide +kernel

theorem rowEval10459 (x : Key → ℝ) : Integer.Sparse.eval row10459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10459, Integer.Sparse.eval_collectBalanced, rawRowCheck10459]

def rawRow10460 : Integer.Sparse Key := [(key2681, -2), (key2688, -2), (key2681, -2), (key2712, -2), (key2714, -2), (key2681, -2), (key2714, -2), (key2681, -2), (key2712, -2), (key2714, -2), (key2688, -2), (key2714, -2), (key2681, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2817, 2)]

theorem rawRowCheck10460 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form7 = rawRow10460 := by decide +kernel

def row10460 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

theorem rowCheck10460 : row10460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10460 := by decide +kernel

theorem rowEval10460 (x : Key → ℝ) : Integer.Sparse.eval row10460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10460, Integer.Sparse.eval_collectBalanced, rawRowCheck10460]

def rawRow10461 : Integer.Sparse Key := [(key2688, -2), (key2681, -2), (key2681, -2), (key2714, -2), (key2712, -2), (key2714, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2)]

theorem rawRowCheck10461 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form7 = rawRow10461 := by decide +kernel

def row10461 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

theorem rowCheck10461 : row10461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10461 := by decide +kernel

theorem rowEval10461 (x : Key → ℝ) : Integer.Sparse.eval row10461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10461, Integer.Sparse.eval_collectBalanced, rawRowCheck10461]

def rawRow10462 : Integer.Sparse Key := [(key2712, -2), (key2714, -2), (key2714, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2714, -2), (key2688, -2), (key2714, -2), (key2681, -2), (key2681, -2), (key2712, -2), (key2815, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2815, 2)]

theorem rawRowCheck10462 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form7 = rawRow10462 := by decide +kernel

def row10462 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

theorem rowCheck10462 : row10462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10462 := by decide +kernel

theorem rowEval10462 (x : Key → ℝ) : Integer.Sparse.eval row10462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10462, Integer.Sparse.eval_collectBalanced, rawRowCheck10462]

def rawRow10463 : Integer.Sparse Key := [(key2714, -2), (key2712, -2), (key2714, -2), (key2688, -2), (key2681, -2), (key2714, -2), (key2681, -2), (key2714, -2), (key2688, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2817, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2681, 2)]

theorem rawRowCheck10463 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form7 = rawRow10463 := by decide +kernel

def row10463 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

theorem rowCheck10463 : row10463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10463 := by decide +kernel

theorem rowEval10463 (x : Key → ℝ) : Integer.Sparse.eval row10463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10463, Integer.Sparse.eval_collectBalanced, rawRowCheck10463]

def rawRow10464 : Integer.Sparse Key := [(key2714, -2), (key2714, -2), (key2712, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2)]

theorem rawRowCheck10464 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form7 = rawRow10464 := by decide +kernel

def row10464 : Integer.Sparse Key := [(key2712, -4), (key2714, -8), (key2815, 4), (key2817, 8)]

theorem rowCheck10464 : row10464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10464 := by decide +kernel

theorem rowEval10464 (x : Key → ℝ) : Integer.Sparse.eval row10464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10464, Integer.Sparse.eval_collectBalanced, rawRowCheck10464]

def rawRow10465 : Integer.Sparse Key := [(key2815, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2817, -2), (key2815, -2), (key2863, -2), (key2817, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2)]

theorem rawRowCheck10465 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form7 = rawRow10465 := by decide +kernel

def row10465 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

theorem rowCheck10465 : row10465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10465 := by decide +kernel

theorem rowEval10465 (x : Key → ℝ) : Integer.Sparse.eval row10465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck10465, Integer.Sparse.eval_collectBalanced, rawRowCheck10465]

def rawRow10466 : Integer.Sparse Key := [(key2817, -2), (key2815, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2863, -2), (key2815, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2817, -2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2714, 2)]

theorem rawRowCheck10466 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form7 = rawRow10466 := by decide +kernel

def row10466 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

theorem rowCheck10466 : row10466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10466 := by decide +kernel

theorem rowEval10466 (x : Key → ℝ) : Integer.Sparse.eval row10466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10466, Integer.Sparse.eval_collectBalanced, rawRowCheck10466]

def rawRow10467 : Integer.Sparse Key := [(key2817, -2), (key2817, -2), (key2815, -2), (key2863, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2815, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2)]

theorem rawRowCheck10467 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form7 = rawRow10467 := by decide +kernel

def row10467 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

theorem rowCheck10467 : row10467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10467 := by decide +kernel

theorem rowEval10467 (x : Key → ℝ) : Integer.Sparse.eval row10467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10467, Integer.Sparse.eval_collectBalanced, rawRowCheck10467]

def rawRow10468 : Integer.Sparse Key := [(key2863, -2), (key2863, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2815, -2), (key2815, -2), (key2863, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2712, 2)]

theorem rawRowCheck10468 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form7 = rawRow10468 := by decide +kernel

def row10468 : Integer.Sparse Key := [(key2712, 6), (key2714, 12), (key2815, -6), (key2817, -12)]

theorem rowCheck10468 : row10468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10468 := by decide +kernel

theorem rowEval10468 (x : Key → ℝ) : Integer.Sparse.eval row10468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form7) x := by
  rw [rowCheck10468, Integer.Sparse.eval_collectBalanced, rawRowCheck10468]

def rawRow10469 : Integer.Sparse Key := [(key1407, -2), (key1407, -2), (key1411, -2), (key1407, -2), (key1407, -2), (key1584, -2), (key1584, -2), (key1585, -2), (key1585, -2), (key1411, -2), (key1585, -2), (key1585, -2), (key1407, 1), (key1407, 1), (key1435, 1), (key1435, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1407, 1), (key1584, 1), (key1584, 1), (key1585, 1), (key1585, 1), (key1435, 1), (key1435, 1), (key1584, 1), (key1584, 1), (key1628, 1), (key1628, 1), (key1436, 1), (key1436, 1), (key1585, 1), (key1585, 1), (key1628, 1), (key1628, 1)]

theorem rawRowCheck10469 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form8 = rawRow10469 := by decide +kernel

def row10469 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

theorem rowCheck10469 : row10469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10469 := by decide +kernel

theorem rowEval10469 (x : Key → ℝ) : Integer.Sparse.eval row10469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10469, Integer.Sparse.eval_collectBalanced, rawRowCheck10469]

def rawRow10470 : Integer.Sparse Key := [(key1407, -2), (key1411, -2), (key1407, -2), (key1584, -2), (key1585, -2), (key1407, -2), (key1585, -2), (key1407, -2), (key1584, -2), (key1585, -2), (key1411, -2), (key1585, -2), (key1435, 1), (key1436, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1435, 1), (key1584, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1584, 1), (key1584, 1), (key1628, 1), (key1435, 1), (key1628, 1), (key1435, 1), (key1584, 1), (key1585, 1), (key1628, 1), (key1436, 1), (key1628, 1), (key1436, 1), (key1585, 1)]

theorem rawRowCheck10470 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form8 = rawRow10470 := by decide +kernel

def row10470 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

theorem rowCheck10470 : row10470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10470 := by decide +kernel

theorem rowEval10470 (x : Key → ℝ) : Integer.Sparse.eval row10470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10470, Integer.Sparse.eval_collectBalanced, rawRowCheck10470]

def rawRow10471 : Integer.Sparse Key := [(key1411, -2), (key1407, -2), (key1407, -2), (key1585, -2), (key1584, -2), (key1585, -2), (key1407, -2), (key1584, -2), (key1407, -2), (key1585, -2), (key1585, -2), (key1411, -2), (key1436, 1), (key1435, 1), (key1436, 1), (key1407, 1), (key1435, 1), (key1407, 1), (key1585, 1), (key1584, 1), (key1585, 1), (key1407, 1), (key1584, 1), (key1407, 1), (key1628, 1), (key1584, 1), (key1628, 1), (key1435, 1), (key1584, 1), (key1435, 1), (key1628, 1), (key1585, 1), (key1628, 1), (key1436, 1), (key1585, 1), (key1436, 1)]

theorem rawRowCheck10471 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form8 = rawRow10471 := by decide +kernel

def row10471 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

theorem rowCheck10471 : row10471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10471 := by decide +kernel

theorem rowEval10471 (x : Key → ℝ) : Integer.Sparse.eval row10471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10471, Integer.Sparse.eval_collectBalanced, rawRowCheck10471]

def rawRow10472 : Integer.Sparse Key := [(key1584, -2), (key1585, -2), (key1585, -2), (key1407, -2), (key1411, -2), (key1407, -2), (key1585, -2), (key1411, -2), (key1585, -2), (key1407, -2), (key1407, -2), (key1584, -2), (key1584, 1), (key1585, 1), (key1584, 1), (key1628, 1), (key1585, 1), (key1628, 1), (key1435, 1), (key1436, 1), (key1435, 1), (key1628, 1), (key1436, 1), (key1628, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1585, 1), (key1407, 1), (key1435, 1), (key1407, 1), (key1584, 1), (key1435, 1), (key1584, 1)]

theorem rawRowCheck10472 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form8 = rawRow10472 := by decide +kernel

def row10472 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

theorem rowCheck10472 : row10472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10472 := by decide +kernel

theorem rowEval10472 (x : Key → ℝ) : Integer.Sparse.eval row10472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10472, Integer.Sparse.eval_collectBalanced, rawRowCheck10472]

def rawRow10473 : Integer.Sparse Key := [(key1585, -2), (key1584, -2), (key1585, -2), (key1411, -2), (key1407, -2), (key1585, -2), (key1407, -2), (key1585, -2), (key1411, -2), (key1407, -2), (key1584, -2), (key1407, -2), (key1585, 1), (key1584, 1), (key1628, 1), (key1584, 1), (key1628, 1), (key1585, 1), (key1436, 1), (key1435, 1), (key1628, 1), (key1435, 1), (key1628, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1435, 1), (key1407, 1), (key1584, 1), (key1407, 1), (key1584, 1), (key1435, 1)]

theorem rawRowCheck10473 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form8 = rawRow10473 := by decide +kernel

def row10473 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

theorem rowCheck10473 : row10473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10473 := by decide +kernel

theorem rowEval10473 (x : Key → ℝ) : Integer.Sparse.eval row10473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10473, Integer.Sparse.eval_collectBalanced, rawRowCheck10473]

def rawRow10474 : Integer.Sparse Key := [(key1585, -2), (key1585, -2), (key1584, -2), (key1585, -2), (key1585, -2), (key1411, -2), (key1411, -2), (key1407, -2), (key1407, -2), (key1584, -2), (key1407, -2), (key1407, -2), (key1628, 1), (key1628, 1), (key1585, 1), (key1585, 1), (key1584, 1), (key1584, 1), (key1628, 1), (key1628, 1), (key1436, 1), (key1436, 1), (key1435, 1), (key1435, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1407, 1), (key1584, 1), (key1584, 1), (key1435, 1), (key1435, 1), (key1407, 1), (key1407, 1)]

theorem rawRowCheck10474 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form8 = rawRow10474 := by decide +kernel

def row10474 : Integer.Sparse Key := [(key1407, -4), (key1411, -4), (key1435, 4), (key1436, 4), (key1585, -4), (key1628, 4)]

theorem rowCheck10474 : row10474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10474 := by decide +kernel

theorem rowEval10474 (x : Key → ℝ) : Integer.Sparse.eval row10474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10474, Integer.Sparse.eval_collectBalanced, rawRowCheck10474]

def rawRow10475 : Integer.Sparse Key := [(key1435, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1436, -2), (key1435, -2), (key1628, -2), (key1436, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1628, -2), (key1407, 1), (key1411, 1), (key1407, 1), (key1436, 1), (key1411, 1), (key1436, 1), (key1407, 1), (key1411, 1), (key1407, 1), (key1585, 1), (key1411, 1), (key1585, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1585, 1), (key1411, 1), (key1436, 1), (key1411, 1), (key1585, 1), (key1436, 1), (key1585, 1)]

theorem rawRowCheck10475 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form8 = rawRow10475 := by decide +kernel

def row10475 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

theorem rowCheck10475 : row10475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10475 := by decide +kernel

theorem rowEval10475 (x : Key → ℝ) : Integer.Sparse.eval row10475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck10475, Integer.Sparse.eval_collectBalanced, rawRowCheck10475]

def rawRow10476 : Integer.Sparse Key := [(key1436, -2), (key1435, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1628, -2), (key1435, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1628, -2), (key1436, -2), (key1411, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1436, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1411, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1411, 1), (key1585, 1), (key1411, 1), (key1585, 1), (key1436, 1)]

theorem rawRowCheck10476 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form8 = rawRow10476 := by decide +kernel

def row10476 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

theorem rowCheck10476 : row10476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10476 := by decide +kernel

theorem rowEval10476 (x : Key → ℝ) : Integer.Sparse.eval row10476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10476, Integer.Sparse.eval_collectBalanced, rawRowCheck10476]

def rawRow10477 : Integer.Sparse Key := [(key1436, -2), (key1436, -2), (key1435, -2), (key1628, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1435, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1436, 1), (key1436, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1407, 1), (key1585, 1), (key1585, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1407, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1407, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1411, 1), (key1411, 1)]

theorem rawRowCheck10477 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form8 = rawRow10477 := by decide +kernel

def row10477 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

theorem rowCheck10477 : row10477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10477 := by decide +kernel

theorem rowEval10477 (x : Key → ℝ) : Integer.Sparse.eval row10477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10477, Integer.Sparse.eval_collectBalanced, rawRowCheck10477]

def rawRow10478 : Integer.Sparse Key := [(key1628, -2), (key1628, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1435, -2), (key1435, -2), (key1585, 1), (key1585, 1), (key1585, 1), (key1585, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1407, 1), (key1407, 1), (key1407, 1), (key1407, 1), (key1407, 1)]

theorem rawRowCheck10478 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form8 = rawRow10478 := by decide +kernel

def row10478 : Integer.Sparse Key := [(key1407, 6), (key1411, 6), (key1435, -6), (key1436, -6), (key1585, 6), (key1628, -6)]

theorem rowCheck10478 : row10478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10478 := by decide +kernel

theorem rowEval10478 (x : Key → ℝ) : Integer.Sparse.eval row10478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck10478, Integer.Sparse.eval_collectBalanced, rawRowCheck10478]

def rawRow10479 : Integer.Sparse Key := [(key2681, 1), (key2681, 1), (key2712, 1), (key2712, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2817, 1), (key2817, 1), (key2712, 1), (key2712, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2817, 1), (key2817, 1), (key2863, 1), (key2863, 1), (key2688, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2714, -2), (key2714, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2863, -2)]

theorem rawRowCheck10479 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form9 = rawRow10479 := by decide +kernel

def row10479 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

theorem rowCheck10479 : row10479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10479 := by decide +kernel

theorem rowEval10479 (x : Key → ℝ) : Integer.Sparse.eval row10479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10479, Integer.Sparse.eval_collectBalanced, rawRowCheck10479]

def rawRow10480 : Integer.Sparse Key := [(key2712, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2714, 1), (key2817, 1), (key2714, -2), (key2688, -2), (key2714, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2817, -2)]

theorem rawRowCheck10480 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form9 = rawRow10480 := by decide +kernel

def row10480 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

theorem rowCheck10480 : row10480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10480 := by decide +kernel

theorem rowEval10480 (x : Key → ℝ) : Integer.Sparse.eval row10480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10480, Integer.Sparse.eval_collectBalanced, rawRowCheck10480]

def rawRow10481 : Integer.Sparse Key := [(key2714, 1), (key2712, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2817, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2712, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2817, 1), (key2714, 1), (key2714, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2863, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2817, -2), (key2714, -2)]

theorem rawRowCheck10481 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form9 = rawRow10481 := by decide +kernel

def row10481 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

theorem rowCheck10481 : row10481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10481 := by decide +kernel

theorem rowEval10481 (x : Key → ℝ) : Integer.Sparse.eval row10481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10481, Integer.Sparse.eval_collectBalanced, rawRowCheck10481]

def rawRow10482 : Integer.Sparse Key := [(key2815, 1), (key2817, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2712, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2712, 1), (key2815, 1), (key2817, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2863, -2), (key2688, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2714, -2), (key2817, -2)]

theorem rawRowCheck10482 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form9 = rawRow10482 := by decide +kernel

def row10482 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

theorem rowCheck10482 : row10482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10482 := by decide +kernel

theorem rowEval10482 (x : Key → ℝ) : Integer.Sparse.eval row10482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10482, Integer.Sparse.eval_collectBalanced, rawRowCheck10482]

def rawRow10483 : Integer.Sparse Key := [(key2817, 1), (key2815, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2815, 1), (key2712, 1), (key2817, -2), (key2863, -2), (key2817, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2714, -2)]

theorem rawRowCheck10483 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form9 = rawRow10483 := by decide +kernel

def row10483 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

theorem rowCheck10483 : row10483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10483 := by decide +kernel

theorem rowEval10483 (x : Key → ℝ) : Integer.Sparse.eval row10483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10483, Integer.Sparse.eval_collectBalanced, rawRowCheck10483]

def rawRow10484 : Integer.Sparse Key := [(key2863, 1), (key2863, 1), (key2817, 1), (key2817, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2712, 1), (key2712, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2712, 1), (key2712, 1), (key2681, 1), (key2681, 1), (key2863, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2817, -2), (key2817, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2688, -2)]

theorem rawRowCheck10484 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form9 = rawRow10484 := by decide +kernel

def row10484 : Integer.Sparse Key := [(key2681, 4), (key2688, -4), (key2712, 4), (key2714, -4), (key2815, 4), (key2817, -4)]

theorem rowCheck10484 : row10484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10484 := by decide +kernel

theorem rowEval10484 (x : Key → ℝ) : Integer.Sparse.eval row10484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10484, Integer.Sparse.eval_collectBalanced, rawRowCheck10484]

def rawRow10485 : Integer.Sparse Key := [(key2681, 1), (key2688, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2681, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2815, -2), (key2712, -2), (key2815, -2)]

theorem rawRowCheck10485 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form9 = rawRow10485 := by decide +kernel

def row10485 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

theorem rowCheck10485 : row10485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10485 := by decide +kernel

theorem rowEval10485 (x : Key → ℝ) : Integer.Sparse.eval row10485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck10485, Integer.Sparse.eval_collectBalanced, rawRowCheck10485]

def rawRow10486 : Integer.Sparse Key := [(key2688, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2714, 1), (key2681, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2815, -2), (key2712, -2)]

theorem rawRowCheck10486 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form9 = rawRow10486 := by decide +kernel

def row10486 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

theorem rowCheck10486 : row10486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10486 := by decide +kernel

theorem rowEval10486 (x : Key → ℝ) : Integer.Sparse.eval row10486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10486, Integer.Sparse.eval_collectBalanced, rawRowCheck10486]

def rawRow10487 : Integer.Sparse Key := [(key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2712, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2815, -2), (key2712, -2), (key2712, -2), (key2681, -2), (key2681, -2)]

theorem rawRowCheck10487 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form9 = rawRow10487 := by decide +kernel

def row10487 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

theorem rowCheck10487 : row10487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10487 := by decide +kernel

theorem rowEval10487 (x : Key → ℝ) : Integer.Sparse.eval row10487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10487, Integer.Sparse.eval_collectBalanced, rawRowCheck10487]

def rawRow10488 : Integer.Sparse Key := [(key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2815, -2), (key2815, -2), (key2815, -2), (key2712, -2), (key2712, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2681, -2), (key2681, -2), (key2681, -2), (key2681, -2)]

theorem rawRowCheck10488 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form9 = rawRow10488 := by decide +kernel

def row10488 : Integer.Sparse Key := [(key2681, -6), (key2688, 6), (key2712, -6), (key2714, 6), (key2815, -6), (key2817, 6)]

theorem rowCheck10488 : row10488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10488 := by decide +kernel

theorem rowEval10488 (x : Key → ℝ) : Integer.Sparse.eval row10488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck10488, Integer.Sparse.eval_collectBalanced, rawRowCheck10488]

def rawRow10489 : Integer.Sparse Key := [(key1402, -6), (key1402, -6), (key1579, -6), (key1579, -6), (key1402, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1579, 2), (key1579, 2), (key1627, 2), (key1627, 2)]

theorem rawRowCheck10489 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form10 = rawRow10489 := by decide +kernel

def row10489 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

theorem rowCheck10489 : row10489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10489 := by decide +kernel

theorem rowEval10489 (x : Key → ℝ) : Integer.Sparse.eval row10489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10489, Integer.Sparse.eval_collectBalanced, rawRowCheck10489]

def rawRow10490 : Integer.Sparse Key := [(key1402, -6), (key1579, -6), (key1402, -6), (key1579, -6), (key1430, 2), (key1402, 2), (key1430, 2), (key1579, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1627, 2), (key1430, 2), (key1579, 2)]

theorem rawRowCheck10490 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form10 = rawRow10490 := by decide +kernel

def row10490 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

theorem rowCheck10490 : row10490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10490 := by decide +kernel

theorem rowEval10490 (x : Key → ℝ) : Integer.Sparse.eval row10490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10490, Integer.Sparse.eval_collectBalanced, rawRowCheck10490]

def rawRow10491 : Integer.Sparse Key := [(key1402, -6), (key1579, -6), (key1579, -6), (key1402, -6), (key1430, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1402, 2), (key1627, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1579, 2), (key1430, 2)]

theorem rawRowCheck10491 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form10 = rawRow10491 := by decide +kernel

def row10491 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

theorem rowCheck10491 : row10491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10491 := by decide +kernel

theorem rowEval10491 (x : Key → ℝ) : Integer.Sparse.eval row10491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10491, Integer.Sparse.eval_collectBalanced, rawRowCheck10491]

def rawRow10492 : Integer.Sparse Key := [(key1579, -6), (key1402, -6), (key1402, -6), (key1579, -6), (key1579, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1430, 2), (key1627, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1430, 2), (key1579, 2)]

theorem rawRowCheck10492 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form10 = rawRow10492 := by decide +kernel

def row10492 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

theorem rowCheck10492 : row10492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10492 := by decide +kernel

theorem rowEval10492 (x : Key → ℝ) : Integer.Sparse.eval row10492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10492, Integer.Sparse.eval_collectBalanced, rawRowCheck10492]

def rawRow10493 : Integer.Sparse Key := [(key1579, -6), (key1402, -6), (key1579, -6), (key1402, -6), (key1579, 2), (key1627, 2), (key1579, 2), (key1430, 2), (key1627, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1579, 2), (key1430, 2)]

theorem rawRowCheck10493 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form10 = rawRow10493 := by decide +kernel

def row10493 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

theorem rowCheck10493 : row10493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10493 := by decide +kernel

theorem rowEval10493 (x : Key → ℝ) : Integer.Sparse.eval row10493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10493, Integer.Sparse.eval_collectBalanced, rawRowCheck10493]

def rawRow10494 : Integer.Sparse Key := [(key1579, -6), (key1579, -6), (key1402, -6), (key1402, -6), (key1627, 2), (key1579, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1430, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1402, 2)]

theorem rawRowCheck10494 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form10 = rawRow10494 := by decide +kernel

def row10494 : Integer.Sparse Key := [(key1402, -8), (key1430, 8), (key1579, -4), (key1627, 4)]

theorem rowCheck10494 : row10494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10494 := by decide +kernel

theorem rowEval10494 (x : Key → ℝ) : Integer.Sparse.eval row10494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck10494, Integer.Sparse.eval_collectBalanced, rawRowCheck10494]

def rawRow10495 : Integer.Sparse Key := [(key1430, -6), (key1430, -6), (key1430, -6), (key1627, -6), (key1402, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1430, 2), (key1579, 2)]

theorem rawRowCheck10495 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form10 = rawRow10495 := by decide +kernel

def row10495 : Integer.Sparse Key := [(key1402, 12), (key1430, -12), (key1579, 6), (key1627, -6)]

theorem rowCheck10495 : row10495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow10495 := by decide +kernel

theorem rowEval10495 (x : Key → ℝ) : Integer.Sparse.eval row10495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck10495, Integer.Sparse.eval_collectBalanced, rawRowCheck10495]

end MUB6.Certificate.GramRows

end OAI
