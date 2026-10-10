import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19456 : Integer.Sparse Key := [(key1698, 24), (key1698, 24), (key1750, 24), (key1698, 24), (key1275, 24)]

theorem rawRowCheck19456 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form3 = rawRow19456 := by decide +kernel

def row19456 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19456 : row19456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19456 := by decide +kernel

theorem rowEval19456 (x : Key → ℝ) : Integer.Sparse.eval row19456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19456, Integer.Sparse.eval_collectBalanced, rawRowCheck19456]

def rawRow19457 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1275, 24), (key1698, 24), (key1698, 24)]

theorem rawRowCheck19457 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19457 := by decide +kernel

def row19457 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19457 : row19457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19457 := by decide +kernel

theorem rowEval19457 (x : Key → ℝ) : Integer.Sparse.eval row19457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19457, Integer.Sparse.eval_collectBalanced, rawRowCheck19457]

def rawRow19458 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1698, 24), (key1275, 24), (key1698, 24)]

theorem rawRowCheck19458 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19458 := by decide +kernel

def row19458 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19458 : row19458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19458 := by decide +kernel

theorem rowEval19458 (x : Key → ℝ) : Integer.Sparse.eval row19458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19458, Integer.Sparse.eval_collectBalanced, rawRowCheck19458]

def rawRow19459 : Integer.Sparse Key := [(key1698, 24), (key1750, 24), (key1698, 24), (key1698, 24), (key1275, 24)]

theorem rawRowCheck19459 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19459 := by decide +kernel

def row19459 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19459 : row19459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19459 := by decide +kernel

theorem rowEval19459 (x : Key → ℝ) : Integer.Sparse.eval row19459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19459, Integer.Sparse.eval_collectBalanced, rawRowCheck19459]

def rawRow19460 : Integer.Sparse Key := [(key1750, 24), (key1275, 24), (key1698, 24), (key1698, 24), (key1698, 24)]

theorem rawRowCheck19460 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19460 := by decide +kernel

def row19460 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19460 : row19460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19460 := by decide +kernel

theorem rowEval19460 (x : Key → ℝ) : Integer.Sparse.eval row19460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19460, Integer.Sparse.eval_collectBalanced, rawRowCheck19460]

def rawRow19461 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1275, 24), (key1698, 24), (key1698, 24)]

theorem rawRowCheck19461 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form3 = rawRow19461 := by decide +kernel

def row19461 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19461 : row19461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19461 := by decide +kernel

theorem rowEval19461 (x : Key → ℝ) : Integer.Sparse.eval row19461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19461, Integer.Sparse.eval_collectBalanced, rawRowCheck19461]

def rawRow19462 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1698, 24), (key1275, 24), (key1698, 24)]

theorem rawRowCheck19462 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form3 = rawRow19462 := by decide +kernel

def row19462 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19462 : row19462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19462 := by decide +kernel

theorem rowEval19462 (x : Key → ℝ) : Integer.Sparse.eval row19462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19462, Integer.Sparse.eval_collectBalanced, rawRowCheck19462]

def rawRow19463 : Integer.Sparse Key := [(key1750, 24), (key1698, 24), (key1698, 24), (key1698, 24), (key1275, 24)]

theorem rawRowCheck19463 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form3 = rawRow19463 := by decide +kernel

def row19463 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

theorem rowCheck19463 : row19463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19463 := by decide +kernel

theorem rowEval19463 (x : Key → ℝ) : Integer.Sparse.eval row19463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19463, Integer.Sparse.eval_collectBalanced, rawRowCheck19463]

def rawRow19464 : Integer.Sparse Key := [(key220, 6), (key225, 6), (key225, 6), (key225, 6), (key492, 6), (key497, 6), (key497, 6), (key492, 6), (key497, 6), (key492, 6), (key551, 6), (key497, 6), (key551, 6), (key497, 6), (key497, 6), (key551, 6), (key664, 6), (key664, 6), (key664, 6), (key681, 6)]

theorem rawRowCheck19464 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19464 := by decide +kernel

def row19464 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19464 : row19464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19464 := by decide +kernel

theorem rowEval19464 (x : Key → ℝ) : Integer.Sparse.eval row19464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19464, Integer.Sparse.eval_collectBalanced, rawRowCheck19464]

def rawRow19465 : Integer.Sparse Key := [(key225, 6), (key220, 6), (key225, 6), (key225, 6), (key497, 6), (key492, 6), (key497, 6), (key497, 6), (key492, 6), (key551, 6), (key492, 6), (key551, 6), (key497, 6), (key497, 6), (key551, 6), (key497, 6), (key664, 6), (key664, 6), (key681, 6), (key664, 6)]

theorem rawRowCheck19465 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19465 := by decide +kernel

def row19465 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19465 : row19465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19465 := by decide +kernel

theorem rowEval19465 (x : Key → ℝ) : Integer.Sparse.eval row19465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19465, Integer.Sparse.eval_collectBalanced, rawRowCheck19465]

def rawRow19466 : Integer.Sparse Key := [(key225, 6), (key225, 6), (key220, 6), (key225, 6), (key497, 6), (key497, 6), (key492, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key551, 6), (key497, 6), (key497, 6), (key664, 6), (key681, 6), (key664, 6), (key664, 6)]

theorem rawRowCheck19466 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19466 := by decide +kernel

def row19466 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19466 : row19466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19466 := by decide +kernel

theorem rowEval19466 (x : Key → ℝ) : Integer.Sparse.eval row19466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19466, Integer.Sparse.eval_collectBalanced, rawRowCheck19466]

def rawRow19467 : Integer.Sparse Key := [(key225, 6), (key225, 6), (key225, 6), (key220, 6), (key551, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key492, 6), (key681, 6), (key664, 6), (key664, 6), (key664, 6)]

theorem rawRowCheck19467 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19467 := by decide +kernel

def row19467 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19467 : row19467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19467 := by decide +kernel

theorem rowEval19467 (x : Key → ℝ) : Integer.Sparse.eval row19467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19467, Integer.Sparse.eval_collectBalanced, rawRowCheck19467]

def rawRow19468 : Integer.Sparse Key := [(key492, 6), (key497, 6), (key497, 6), (key664, 6), (key220, 6), (key225, 6), (key225, 6), (key492, 6), (key497, 6), (key492, 6), (key551, 6), (key497, 6), (key551, 6), (key664, 6), (key664, 6), (key681, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6)]

theorem rawRowCheck19468 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19468 := by decide +kernel

def row19468 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19468 : row19468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19468 := by decide +kernel

theorem rowEval19468 (x : Key → ℝ) : Integer.Sparse.eval row19468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19468, Integer.Sparse.eval_collectBalanced, rawRowCheck19468]

def rawRow19469 : Integer.Sparse Key := [(key497, 6), (key492, 6), (key497, 6), (key664, 6), (key225, 6), (key220, 6), (key225, 6), (key497, 6), (key492, 6), (key551, 6), (key492, 6), (key551, 6), (key497, 6), (key664, 6), (key681, 6), (key664, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6)]

theorem rawRowCheck19469 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19469 := by decide +kernel

def row19469 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19469 : row19469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19469 := by decide +kernel

theorem rowEval19469 (x : Key → ℝ) : Integer.Sparse.eval row19469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19469, Integer.Sparse.eval_collectBalanced, rawRowCheck19469]

def rawRow19470 : Integer.Sparse Key := [(key497, 6), (key497, 6), (key492, 6), (key664, 6), (key225, 6), (key225, 6), (key220, 6), (key551, 6), (key551, 6), (key497, 6), (key497, 6), (key492, 6), (key492, 6), (key681, 6), (key664, 6), (key664, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6)]

theorem rawRowCheck19470 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19470 := by decide +kernel

def row19470 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19470 : row19470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19470 := by decide +kernel

theorem rowEval19470 (x : Key → ℝ) : Integer.Sparse.eval row19470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19470, Integer.Sparse.eval_collectBalanced, rawRowCheck19470]

def rawRow19471 : Integer.Sparse Key := [(key492, 6), (key497, 6), (key664, 6), (key497, 6), (key492, 6), (key497, 6), (key664, 6), (key220, 6), (key225, 6), (key492, 6), (key551, 6), (key664, 6), (key681, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6), (key551, 6)]

theorem rawRowCheck19471 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form4 = rawRow19471 := by decide +kernel

def row19471 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19471 : row19471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19471 := by decide +kernel

theorem rowEval19471 (x : Key → ℝ) : Integer.Sparse.eval row19471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19471, Integer.Sparse.eval_collectBalanced, rawRowCheck19471]

def rawRow19472 : Integer.Sparse Key := [(key497, 6), (key492, 6), (key664, 6), (key497, 6), (key497, 6), (key492, 6), (key664, 6), (key225, 6), (key220, 6), (key551, 6), (key492, 6), (key681, 6), (key664, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6), (key551, 6), (key497, 6)]

theorem rawRowCheck19472 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form4 = rawRow19472 := by decide +kernel

def row19472 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19472 : row19472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19472 := by decide +kernel

theorem rowEval19472 (x : Key → ℝ) : Integer.Sparse.eval row19472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19472, Integer.Sparse.eval_collectBalanced, rawRowCheck19472]

def rawRow19473 : Integer.Sparse Key := [(key492, 6), (key664, 6), (key497, 6), (key497, 6), (key492, 6), (key664, 6), (key497, 6), (key492, 6), (key664, 6), (key220, 6), (key681, 6), (key225, 6), (key551, 6), (key497, 6), (key225, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6), (key551, 6)]

theorem rawRowCheck19473 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form4 = rawRow19473 := by decide +kernel

def row19473 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19473 : row19473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19473 := by decide +kernel

theorem rowEval19473 (x : Key → ℝ) : Integer.Sparse.eval row19473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19473, Integer.Sparse.eval_collectBalanced, rawRowCheck19473]

def rawRow19474 : Integer.Sparse Key := [(key664, 6), (key492, 6), (key497, 6), (key497, 6), (key664, 6), (key492, 6), (key497, 6), (key664, 6), (key492, 6), (key681, 6), (key220, 6), (key551, 6), (key225, 6), (key497, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6), (key225, 6)]

theorem rawRowCheck19474 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form4 = rawRow19474 := by decide +kernel

def row19474 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19474 : row19474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19474 := by decide +kernel

theorem rowEval19474 (x : Key → ℝ) : Integer.Sparse.eval row19474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19474, Integer.Sparse.eval_collectBalanced, rawRowCheck19474]

def rawRow19475 : Integer.Sparse Key := [(key497, 6), (key664, 6), (key492, 6), (key497, 6), (key497, 6), (key664, 6), (key492, 6), (key551, 6), (key681, 6), (key225, 6), (key664, 6), (key220, 6), (key492, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6), (key551, 6), (key225, 6), (key497, 6)]

theorem rawRowCheck19475 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form4 = rawRow19475 := by decide +kernel

def row19475 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19475 : row19475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19475 := by decide +kernel

theorem rowEval19475 (x : Key → ℝ) : Integer.Sparse.eval row19475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19475, Integer.Sparse.eval_collectBalanced, rawRowCheck19475]

def rawRow19476 : Integer.Sparse Key := [(key664, 6), (key497, 6), (key492, 6), (key497, 6), (key664, 6), (key497, 6), (key492, 6), (key681, 6), (key551, 6), (key664, 6), (key225, 6), (key492, 6), (key220, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6), (key551, 6), (key497, 6), (key225, 6)]

theorem rawRowCheck19476 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form4 = rawRow19476 := by decide +kernel

def row19476 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19476 : row19476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19476 := by decide +kernel

theorem rowEval19476 (x : Key → ℝ) : Integer.Sparse.eval row19476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19476, Integer.Sparse.eval_collectBalanced, rawRowCheck19476]

def rawRow19477 : Integer.Sparse Key := [(key497, 6), (key497, 6), (key664, 6), (key492, 6), (key551, 6), (key551, 6), (key681, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key220, 6), (key492, 6), (key492, 6), (key551, 6), (key225, 6), (key497, 6), (key497, 6)]

theorem rawRowCheck19477 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19477 := by decide +kernel

def row19477 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19477 : row19477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19477 := by decide +kernel

theorem rowEval19477 (x : Key → ℝ) : Integer.Sparse.eval row19477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19477, Integer.Sparse.eval_collectBalanced, rawRowCheck19477]

def rawRow19478 : Integer.Sparse Key := [(key497, 6), (key664, 6), (key497, 6), (key492, 6), (key551, 6), (key681, 6), (key551, 6), (key497, 6), (key664, 6), (key225, 6), (key664, 6), (key225, 6), (key497, 6), (key492, 6), (key220, 6), (key492, 6), (key551, 6), (key497, 6), (key225, 6), (key497, 6)]

theorem rawRowCheck19478 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19478 := by decide +kernel

def row19478 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19478 : row19478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19478 := by decide +kernel

theorem rowEval19478 (x : Key → ℝ) : Integer.Sparse.eval row19478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19478, Integer.Sparse.eval_collectBalanced, rawRowCheck19478]

def rawRow19479 : Integer.Sparse Key := [(key664, 6), (key497, 6), (key497, 6), (key492, 6), (key681, 6), (key551, 6), (key551, 6), (key664, 6), (key497, 6), (key664, 6), (key225, 6), (key497, 6), (key225, 6), (key492, 6), (key492, 6), (key220, 6), (key551, 6), (key497, 6), (key497, 6), (key225, 6)]

theorem rawRowCheck19479 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19479 := by decide +kernel

def row19479 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19479 : row19479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19479 := by decide +kernel

theorem rowEval19479 (x : Key → ℝ) : Integer.Sparse.eval row19479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19479, Integer.Sparse.eval_collectBalanced, rawRowCheck19479]

def rawRow19480 : Integer.Sparse Key := [(key551, 6), (key551, 6), (key551, 6), (key681, 6), (key225, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key664, 6), (key220, 6), (key492, 6), (key492, 6), (key492, 6)]

theorem rawRowCheck19480 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19480 := by decide +kernel

def row19480 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19480 : row19480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19480 := by decide +kernel

theorem rowEval19480 (x : Key → ℝ) : Integer.Sparse.eval row19480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19480, Integer.Sparse.eval_collectBalanced, rawRowCheck19480]

def rawRow19481 : Integer.Sparse Key := [(key551, 6), (key551, 6), (key681, 6), (key551, 6), (key497, 6), (key497, 6), (key664, 6), (key225, 6), (key225, 6), (key497, 6), (key497, 6), (key664, 6), (key664, 6), (key225, 6), (key497, 6), (key497, 6), (key492, 6), (key220, 6), (key492, 6), (key492, 6)]

theorem rawRowCheck19481 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form4 = rawRow19481 := by decide +kernel

def row19481 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19481 : row19481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19481 := by decide +kernel

theorem rowEval19481 (x : Key → ℝ) : Integer.Sparse.eval row19481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19481, Integer.Sparse.eval_collectBalanced, rawRowCheck19481]

def rawRow19482 : Integer.Sparse Key := [(key551, 6), (key681, 6), (key551, 6), (key551, 6), (key497, 6), (key664, 6), (key497, 6), (key497, 6), (key664, 6), (key225, 6), (key664, 6), (key225, 6), (key497, 6), (key497, 6), (key225, 6), (key497, 6), (key492, 6), (key492, 6), (key220, 6), (key492, 6)]

theorem rawRowCheck19482 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form4 = rawRow19482 := by decide +kernel

def row19482 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19482 : row19482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19482 := by decide +kernel

theorem rowEval19482 (x : Key → ℝ) : Integer.Sparse.eval row19482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19482, Integer.Sparse.eval_collectBalanced, rawRowCheck19482]

def rawRow19483 : Integer.Sparse Key := [(key681, 6), (key551, 6), (key551, 6), (key551, 6), (key664, 6), (key497, 6), (key497, 6), (key664, 6), (key497, 6), (key664, 6), (key225, 6), (key497, 6), (key225, 6), (key497, 6), (key497, 6), (key225, 6), (key492, 6), (key492, 6), (key492, 6), (key220, 6)]

theorem rawRowCheck19483 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form4 = rawRow19483 := by decide +kernel

def row19483 : Integer.Sparse Key := [(key220, 6), (key225, 18), (key492, 18), (key497, 36), (key551, 18), (key664, 18), (key681, 6)]

theorem rowCheck19483 : row19483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19483 := by decide +kernel

theorem rowEval19483 (x : Key → ℝ) : Integer.Sparse.eval row19483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19483, Integer.Sparse.eval_collectBalanced, rawRowCheck19483]

def rawRow19484 : Integer.Sparse Key := [(key1277, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1756, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

theorem rawRowCheck19484 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19484 := by decide +kernel

def row19484 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19484 : row19484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19484 := by decide +kernel

theorem rowEval19484 (x : Key → ℝ) : Integer.Sparse.eval row19484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19484, Integer.Sparse.eval_collectBalanced, rawRowCheck19484]

def rawRow19485 : Integer.Sparse Key := [(key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

theorem rawRowCheck19485 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19485 := by decide +kernel

def row19485 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19485 : row19485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19485 := by decide +kernel

theorem rowEval19485 (x : Key → ℝ) : Integer.Sparse.eval row19485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19485, Integer.Sparse.eval_collectBalanced, rawRowCheck19485]

def rawRow19486 : Integer.Sparse Key := [(key1283, 4), (key1277, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

theorem rawRowCheck19486 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19486 := by decide +kernel

def row19486 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19486 : row19486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19486 := by decide +kernel

theorem rowEval19486 (x : Key → ℝ) : Integer.Sparse.eval row19486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19486, Integer.Sparse.eval_collectBalanced, rawRowCheck19486]

def rawRow19487 : Integer.Sparse Key := [(key1283, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1277, 4), (key1277, 4), (key1756, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

theorem rawRowCheck19487 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19487 := by decide +kernel

def row19487 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19487 : row19487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19487 := by decide +kernel

theorem rowEval19487 (x : Key → ℝ) : Integer.Sparse.eval row19487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19487, Integer.Sparse.eval_collectBalanced, rawRowCheck19487]

def rawRow19488 : Integer.Sparse Key := [(key1700, 4), (key1700, 4), (key1706, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1756, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1277, 4), (key1283, 4), (key1283, 4), (key1700, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

theorem rawRowCheck19488 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19488 := by decide +kernel

def row19488 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19488 : row19488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19488 := by decide +kernel

theorem rowEval19488 (x : Key → ℝ) : Integer.Sparse.eval row19488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19488, Integer.Sparse.eval_collectBalanced, rawRowCheck19488]

def rawRow19489 : Integer.Sparse Key := [(key1700, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1277, 4), (key1283, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1277, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1756, 4), (key1700, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

theorem rawRowCheck19489 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19489 := by decide +kernel

def row19489 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19489 : row19489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19489 := by decide +kernel

theorem rowEval19489 (x : Key → ℝ) : Integer.Sparse.eval row19489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19489, Integer.Sparse.eval_collectBalanced, rawRowCheck19489]

def rawRow19490 : Integer.Sparse Key := [(key1706, 4), (key1700, 4), (key1700, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1283, 4), (key1277, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1283, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1756, 4), (key1706, 4), (key1706, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

theorem rawRowCheck19490 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19490 := by decide +kernel

def row19490 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19490 : row19490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19490 := by decide +kernel

theorem rowEval19490 (x : Key → ℝ) : Integer.Sparse.eval row19490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19490, Integer.Sparse.eval_collectBalanced, rawRowCheck19490]

def rawRow19491 : Integer.Sparse Key := [(key1700, 4), (key1851, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1855, 4), (key1277, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1756, 4), (key1855, 4), (key1886, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1277, 4), (key1283, 4), (key1700, 4), (key1756, 4), (key1855, 4), (key1886, 4), (key1283, 4), (key1706, 4), (key1756, 4)]

theorem rawRowCheck19491 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form5 = rawRow19491 := by decide +kernel

def row19491 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19491 : row19491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19491 := by decide +kernel

theorem rowEval19491 (x : Key → ℝ) : Integer.Sparse.eval row19491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19491, Integer.Sparse.eval_collectBalanced, rawRowCheck19491]

def rawRow19492 : Integer.Sparse Key := [(key1700, 4), (key1855, 4), (key1851, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1851, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1283, 4), (key1277, 4), (key1756, 4), (key1700, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1756, 4), (key1706, 4)]

theorem rawRowCheck19492 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form5 = rawRow19492 := by decide +kernel

def row19492 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19492 : row19492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19492 := by decide +kernel

theorem rowEval19492 (x : Key → ℝ) : Integer.Sparse.eval row19492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19492, Integer.Sparse.eval_collectBalanced, rawRowCheck19492]

def rawRow19493 : Integer.Sparse Key := [(key1851, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1851, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1700, 4), (key1855, 4), (key1277, 4), (key1886, 4), (key1283, 4), (key1756, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1277, 4), (key1886, 4), (key1283, 4), (key1756, 4), (key1706, 4), (key1283, 4), (key1756, 4)]

theorem rawRowCheck19493 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form5 = rawRow19493 := by decide +kernel

def row19493 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19493 : row19493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19493 := by decide +kernel

theorem rowEval19493 (x : Key → ℝ) : Integer.Sparse.eval row19493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19493, Integer.Sparse.eval_collectBalanced, rawRowCheck19493]

def rawRow19494 : Integer.Sparse Key := [(key1851, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1851, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1855, 4), (key1700, 4), (key1886, 4), (key1277, 4), (key1756, 4), (key1283, 4), (key1855, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1886, 4), (key1277, 4), (key1756, 4), (key1283, 4), (key1706, 4), (key1756, 4), (key1283, 4)]

theorem rawRowCheck19494 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form5 = rawRow19494 := by decide +kernel

def row19494 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19494 : row19494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19494 := by decide +kernel

theorem rowEval19494 (x : Key → ℝ) : Integer.Sparse.eval row19494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19494, Integer.Sparse.eval_collectBalanced, rawRowCheck19494]

def rawRow19495 : Integer.Sparse Key := [(key1855, 4), (key1700, 4), (key1851, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1886, 4), (key1277, 4), (key1851, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1283, 4), (key1706, 4)]

theorem rawRowCheck19495 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form5 = rawRow19495 := by decide +kernel

def row19495 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19495 : row19495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19495 := by decide +kernel

theorem rowEval19495 (x : Key → ℝ) : Integer.Sparse.eval row19495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19495, Integer.Sparse.eval_collectBalanced, rawRowCheck19495]

def rawRow19496 : Integer.Sparse Key := [(key1855, 4), (key1851, 4), (key1700, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1855, 4), (key1851, 4), (key1700, 4), (key1886, 4), (key1851, 4), (key1277, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1283, 4), (key1700, 4), (key1277, 4), (key1855, 4), (key1706, 4), (key1700, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1283, 4), (key1700, 4), (key1277, 4), (key1756, 4), (key1706, 4), (key1283, 4)]

theorem rawRowCheck19496 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form5 = rawRow19496 := by decide +kernel

def row19496 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19496 : row19496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19496 := by decide +kernel

theorem rowEval19496 (x : Key → ℝ) : Integer.Sparse.eval row19496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19496, Integer.Sparse.eval_collectBalanced, rawRowCheck19496]

def rawRow19497 : Integer.Sparse Key := [(key1706, 4), (key1855, 4), (key1855, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1756, 4), (key1886, 4), (key1886, 4), (key1283, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1700, 4), (key1700, 4)]

theorem rawRowCheck19497 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19497 := by decide +kernel

def row19497 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19497 : row19497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19497 := by decide +kernel

theorem rowEval19497 (x : Key → ℝ) : Integer.Sparse.eval row19497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19497, Integer.Sparse.eval_collectBalanced, rawRowCheck19497]

def rawRow19498 : Integer.Sparse Key := [(key1855, 4), (key1706, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1277, 4), (key1700, 4)]

theorem rawRowCheck19498 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19498 := by decide +kernel

def row19498 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19498 : row19498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19498 := by decide +kernel

theorem rowEval19498 (x : Key → ℝ) : Integer.Sparse.eval row19498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19498, Integer.Sparse.eval_collectBalanced, rawRowCheck19498]

def rawRow19499 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1706, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1886, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1851, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1277, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1283, 4), (key1700, 4), (key1700, 4), (key1277, 4)]

theorem rawRowCheck19499 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19499 := by decide +kernel

def row19499 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19499 : row19499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19499 := by decide +kernel

theorem rowEval19499 (x : Key → ℝ) : Integer.Sparse.eval row19499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19499, Integer.Sparse.eval_collectBalanced, rawRowCheck19499]

def rawRow19500 : Integer.Sparse Key := [(key1756, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1283, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1277, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

theorem rawRowCheck19500 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19500 := by decide +kernel

def row19500 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19500 : row19500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19500 := by decide +kernel

theorem rowEval19500 (x : Key → ℝ) : Integer.Sparse.eval row19500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19500, Integer.Sparse.eval_collectBalanced, rawRowCheck19500]

def rawRow19501 : Integer.Sparse Key := [(key1756, 4), (key1886, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1886, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1283, 4), (key1706, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1700, 4)]

theorem rawRowCheck19501 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form5 = rawRow19501 := by decide +kernel

def row19501 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19501 : row19501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19501 := by decide +kernel

theorem rowEval19501 (x : Key → ℝ) : Integer.Sparse.eval row19501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19501, Integer.Sparse.eval_collectBalanced, rawRowCheck19501]

def rawRow19502 : Integer.Sparse Key := [(key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1277, 4), (key1700, 4)]

theorem rawRowCheck19502 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form5 = rawRow19502 := by decide +kernel

def row19502 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19502 : row19502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19502 := by decide +kernel

theorem rowEval19502 (x : Key → ℝ) : Integer.Sparse.eval row19502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19502, Integer.Sparse.eval_collectBalanced, rawRowCheck19502]

def rawRow19503 : Integer.Sparse Key := [(key1886, 4), (key1886, 4), (key1756, 4), (key1886, 4), (key1756, 4), (key1756, 4), (key1855, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1855, 4), (key1283, 4), (key1855, 4), (key1706, 4), (key1855, 4), (key1283, 4), (key1706, 4), (key1283, 4), (key1851, 4), (key1700, 4), (key1700, 4), (key1851, 4), (key1700, 4), (key1851, 4), (key1277, 4), (key1700, 4), (key1277, 4), (key1700, 4), (key1700, 4), (key1277, 4)]

theorem rawRowCheck19503 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form5 = rawRow19503 := by decide +kernel

def row19503 : Integer.Sparse Key := [(key1277, 12), (key1283, 12), (key1700, 24), (key1706, 12), (key1756, 12), (key1851, 12), (key1855, 24), (key1886, 12)]

theorem rowCheck19503 : row19503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19503 := by decide +kernel

theorem rowEval19503 (x : Key → ℝ) : Integer.Sparse.eval row19503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19503, Integer.Sparse.eval_collectBalanced, rawRowCheck19503]

def rawRow19504 : Integer.Sparse Key := [(key1274, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6)]

theorem rawRowCheck19504 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19504 := by decide +kernel

def row19504 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19504 : row19504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19504 := by decide +kernel

theorem rowEval19504 (x : Key → ℝ) : Integer.Sparse.eval row19504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19504, Integer.Sparse.eval_collectBalanced, rawRowCheck19504]

def rawRow19505 : Integer.Sparse Key := [(key1278, 6), (key1274, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6)]

theorem rawRowCheck19505 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19505 := by decide +kernel

def row19505 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19505 : row19505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19505 := by decide +kernel

theorem rowEval19505 (x : Key → ℝ) : Integer.Sparse.eval row19505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19505, Integer.Sparse.eval_collectBalanced, rawRowCheck19505]

def rawRow19506 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1274, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6)]

theorem rawRowCheck19506 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19506 := by decide +kernel

def row19506 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19506 : row19506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19506 := by decide +kernel

theorem rowEval19506 (x : Key → ℝ) : Integer.Sparse.eval row19506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19506, Integer.Sparse.eval_collectBalanced, rawRowCheck19506]

def rawRow19507 : Integer.Sparse Key := [(key1278, 6), (key1278, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6)]

theorem rawRowCheck19507 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19507 := by decide +kernel

def row19507 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19507 : row19507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19507 := by decide +kernel

theorem rowEval19507 (x : Key → ℝ) : Integer.Sparse.eval row19507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19507, Integer.Sparse.eval_collectBalanced, rawRowCheck19507]

def rawRow19508 : Integer.Sparse Key := [(key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1274, 6), (key1278, 6), (key1278, 6), (key1697, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1751, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6)]

theorem rawRowCheck19508 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19508 := by decide +kernel

def row19508 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19508 : row19508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19508 := by decide +kernel

theorem rowEval19508 (x : Key → ℝ) : Integer.Sparse.eval row19508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19508, Integer.Sparse.eval_collectBalanced, rawRowCheck19508]

def rawRow19509 : Integer.Sparse Key := [(key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1274, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6)]

theorem rawRowCheck19509 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19509 := by decide +kernel

def row19509 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19509 : row19509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19509 := by decide +kernel

theorem rowEval19509 (x : Key → ℝ) : Integer.Sparse.eval row19509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19509, Integer.Sparse.eval_collectBalanced, rawRowCheck19509]

def rawRow19510 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1278, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6)]

theorem rawRowCheck19510 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19510 := by decide +kernel

def row19510 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19510 : row19510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19510 := by decide +kernel

theorem rowEval19510 (x : Key → ℝ) : Integer.Sparse.eval row19510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19510, Integer.Sparse.eval_collectBalanced, rawRowCheck19510]

def rawRow19511 : Integer.Sparse Key := [(key1697, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1274, 6), (key1278, 6), (key1697, 6), (key1751, 6), (key1852, 6), (key1884, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6)]

theorem rawRowCheck19511 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19511 := by decide +kernel

def row19511 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19511 : row19511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19511 := by decide +kernel

theorem rowEval19511 (x : Key → ℝ) : Integer.Sparse.eval row19511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19511, Integer.Sparse.eval_collectBalanced, rawRowCheck19511]

def rawRow19512 : Integer.Sparse Key := [(key1701, 6), (key1697, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1278, 6), (key1274, 6), (key1751, 6), (key1697, 6), (key1884, 6), (key1852, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6)]

theorem rawRowCheck19512 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19512 := by decide +kernel

def row19512 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19512 : row19512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19512 := by decide +kernel

theorem rowEval19512 (x : Key → ℝ) : Integer.Sparse.eval row19512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19512, Integer.Sparse.eval_collectBalanced, rawRowCheck19512]

def rawRow19513 : Integer.Sparse Key := [(key1697, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1852, 6), (key1274, 6), (key1884, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1751, 6)]

theorem rawRowCheck19513 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19513 := by decide +kernel

def row19513 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19513 : row19513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19513 := by decide +kernel

theorem rowEval19513 (x : Key → ℝ) : Integer.Sparse.eval row19513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19513, Integer.Sparse.eval_collectBalanced, rawRowCheck19513]

def rawRow19514 : Integer.Sparse Key := [(key1852, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1884, 6), (key1274, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6)]

theorem rawRowCheck19514 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19514 := by decide +kernel

def row19514 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19514 : row19514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19514 := by decide +kernel

theorem rowEval19514 (x : Key → ℝ) : Integer.Sparse.eval row19514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19514, Integer.Sparse.eval_collectBalanced, rawRowCheck19514]

def rawRow19515 : Integer.Sparse Key := [(key1701, 6), (key1852, 6), (key1697, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1751, 6), (key1278, 6), (key1701, 6)]

theorem rawRowCheck19515 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19515 := by decide +kernel

def row19515 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19515 : row19515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19515 := by decide +kernel

theorem rowEval19515 (x : Key → ℝ) : Integer.Sparse.eval row19515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19515, Integer.Sparse.eval_collectBalanced, rawRowCheck19515]

def rawRow19516 : Integer.Sparse Key := [(key1852, 6), (key1701, 6), (key1697, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1884, 6), (key1751, 6), (key1852, 6), (key1278, 6), (key1697, 6), (key1274, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1751, 6), (key1701, 6), (key1278, 6)]

theorem rawRowCheck19516 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19516 := by decide +kernel

def row19516 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19516 : row19516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19516 := by decide +kernel

theorem rowEval19516 (x : Key → ℝ) : Integer.Sparse.eval row19516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19516, Integer.Sparse.eval_collectBalanced, rawRowCheck19516]

def rawRow19517 : Integer.Sparse Key := [(key1701, 6), (key1701, 6), (key1852, 6), (key1697, 6), (key1751, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1697, 6), (key1751, 6), (key1278, 6), (key1701, 6), (key1701, 6)]

theorem rawRowCheck19517 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19517 := by decide +kernel

def row19517 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19517 : row19517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19517 := by decide +kernel

theorem rowEval19517 (x : Key → ℝ) : Integer.Sparse.eval row19517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19517, Integer.Sparse.eval_collectBalanced, rawRowCheck19517]

def rawRow19518 : Integer.Sparse Key := [(key1701, 6), (key1852, 6), (key1701, 6), (key1697, 6), (key1751, 6), (key1884, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1274, 6), (key1697, 6), (key1751, 6), (key1701, 6), (key1278, 6), (key1701, 6)]

theorem rawRowCheck19518 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19518 := by decide +kernel

def row19518 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19518 : row19518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19518 := by decide +kernel

theorem rowEval19518 (x : Key → ℝ) : Integer.Sparse.eval row19518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19518, Integer.Sparse.eval_collectBalanced, rawRowCheck19518]

def rawRow19519 : Integer.Sparse Key := [(key1852, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1884, 6), (key1751, 6), (key1751, 6), (key1852, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1697, 6), (key1697, 6), (key1274, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1278, 6)]

theorem rawRowCheck19519 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19519 := by decide +kernel

def row19519 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19519 : row19519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19519 := by decide +kernel

theorem rowEval19519 (x : Key → ℝ) : Integer.Sparse.eval row19519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19519, Integer.Sparse.eval_collectBalanced, rawRowCheck19519]

def rawRow19520 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1751, 6), (key1884, 6), (key1278, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1274, 6), (key1697, 6), (key1697, 6), (key1697, 6)]

theorem rawRowCheck19520 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19520 := by decide +kernel

def row19520 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19520 : row19520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19520 := by decide +kernel

theorem rowEval19520 (x : Key → ℝ) : Integer.Sparse.eval row19520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19520, Integer.Sparse.eval_collectBalanced, rawRowCheck19520]

def rawRow19521 : Integer.Sparse Key := [(key1751, 6), (key1751, 6), (key1884, 6), (key1751, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1697, 6), (key1274, 6), (key1697, 6), (key1697, 6)]

theorem rawRowCheck19521 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19521 := by decide +kernel

def row19521 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19521 : row19521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19521 := by decide +kernel

theorem rowEval19521 (x : Key → ℝ) : Integer.Sparse.eval row19521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19521, Integer.Sparse.eval_collectBalanced, rawRowCheck19521]

def rawRow19522 : Integer.Sparse Key := [(key1751, 6), (key1884, 6), (key1751, 6), (key1751, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1697, 6), (key1697, 6), (key1274, 6), (key1697, 6)]

theorem rawRowCheck19522 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19522 := by decide +kernel

def row19522 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19522 : row19522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19522 := by decide +kernel

theorem rowEval19522 (x : Key → ℝ) : Integer.Sparse.eval row19522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19522, Integer.Sparse.eval_collectBalanced, rawRowCheck19522]

def rawRow19523 : Integer.Sparse Key := [(key1884, 6), (key1751, 6), (key1751, 6), (key1751, 6), (key1852, 6), (key1701, 6), (key1701, 6), (key1852, 6), (key1701, 6), (key1852, 6), (key1278, 6), (key1701, 6), (key1278, 6), (key1701, 6), (key1701, 6), (key1278, 6), (key1697, 6), (key1697, 6), (key1697, 6), (key1274, 6)]

theorem rawRowCheck19523 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19523 := by decide +kernel

def row19523 : Integer.Sparse Key := [(key1274, 6), (key1278, 18), (key1697, 18), (key1701, 36), (key1751, 18), (key1852, 18), (key1884, 6)]

theorem rowCheck19523 : row19523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19523 := by decide +kernel

theorem rowEval19523 (x : Key → ℝ) : Integer.Sparse.eval row19523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19523, Integer.Sparse.eval_collectBalanced, rawRowCheck19523]

def rawRow19524 : Integer.Sparse Key := [(key1360, 6), (key1360, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1712, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1721, 6), (key1739, 6)]

theorem rawRowCheck19524 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19524 := by decide +kernel

def row19524 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19524 : row19524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19524 := by decide +kernel

theorem rowEval19524 (x : Key → ℝ) : Integer.Sparse.eval row19524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19524, Integer.Sparse.eval_collectBalanced, rawRowCheck19524]

def rawRow19525 : Integer.Sparse Key := [(key1360, 6), (key1360, 6), (key1372, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1739, 6), (key1721, 6)]

theorem rawRowCheck19525 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19525 := by decide +kernel

def row19525 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19525 : row19525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19525 := by decide +kernel

theorem rowEval19525 (x : Key → ℝ) : Integer.Sparse.eval row19525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19525, Integer.Sparse.eval_collectBalanced, rawRowCheck19525]

def rawRow19526 : Integer.Sparse Key := [(key1360, 6), (key1372, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6)]

theorem rawRowCheck19526 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19526 := by decide +kernel

def row19526 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19526 : row19526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19526 := by decide +kernel

theorem rowEval19526 (x : Key → ℝ) : Integer.Sparse.eval row19526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19526, Integer.Sparse.eval_collectBalanced, rawRowCheck19526]

def rawRow19527 : Integer.Sparse Key := [(key1372, 6), (key1360, 6), (key1360, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1739, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6)]

theorem rawRowCheck19527 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19527 := by decide +kernel

def row19527 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19527 : row19527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19527 := by decide +kernel

theorem rowEval19527 (x : Key → ℝ) : Integer.Sparse.eval row19527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19527, Integer.Sparse.eval_collectBalanced, rawRowCheck19527]

def rawRow19528 : Integer.Sparse Key := [(key1486, 6), (key1712, 6), (key1712, 6), (key1721, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1486, 6), (key1511, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1721, 6), (key1739, 6)]

theorem rawRowCheck19528 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19528 := by decide +kernel

def row19528 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19528 : row19528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19528 := by decide +kernel

theorem rowEval19528 (x : Key → ℝ) : Integer.Sparse.eval row19528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19528, Integer.Sparse.eval_collectBalanced, rawRowCheck19528]

def rawRow19529 : Integer.Sparse Key := [(key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1372, 6), (key1360, 6), (key1486, 6), (key1511, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1739, 6), (key1721, 6)]

theorem rawRowCheck19529 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19529 := by decide +kernel

def row19529 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19529 : row19529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19529 := by decide +kernel

theorem rowEval19529 (x : Key → ℝ) : Integer.Sparse.eval row19529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19529, Integer.Sparse.eval_collectBalanced, rawRowCheck19529]

def rawRow19530 : Integer.Sparse Key := [(key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1372, 6), (key1360, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1486, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1712, 6), (key1712, 6)]

theorem rawRowCheck19530 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19530 := by decide +kernel

def row19530 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19530 : row19530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19530 := by decide +kernel

theorem rowEval19530 (x : Key → ℝ) : Integer.Sparse.eval row19530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19530, Integer.Sparse.eval_collectBalanced, rawRowCheck19530]

def rawRow19531 : Integer.Sparse Key := [(key1712, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1486, 6), (key1712, 6), (key1721, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1372, 6), (key1486, 6), (key1511, 6), (key1721, 6), (key1739, 6)]

theorem rawRowCheck19531 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form7 = rawRow19531 := by decide +kernel

def row19531 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19531 : row19531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19531 := by decide +kernel

theorem rowEval19531 (x : Key → ℝ) : Integer.Sparse.eval row19531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19531, Integer.Sparse.eval_collectBalanced, rawRowCheck19531]

def rawRow19532 : Integer.Sparse Key := [(key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1372, 6), (key1360, 6), (key1511, 6), (key1486, 6), (key1739, 6), (key1721, 6)]

theorem rawRowCheck19532 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form7 = rawRow19532 := by decide +kernel

def row19532 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19532 : row19532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19532 := by decide +kernel

theorem rowEval19532 (x : Key → ℝ) : Integer.Sparse.eval row19532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19532, Integer.Sparse.eval_collectBalanced, rawRowCheck19532]

def rawRow19533 : Integer.Sparse Key := [(key1712, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1712, 6), (key1486, 6), (key1721, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1486, 6), (key1721, 6), (key1360, 6), (key1739, 6), (key1372, 6), (key1511, 6)]

theorem rawRowCheck19533 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form7 = rawRow19533 := by decide +kernel

def row19533 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19533 : row19533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19533 := by decide +kernel

theorem rowEval19533 (x : Key → ℝ) : Integer.Sparse.eval row19533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19533, Integer.Sparse.eval_collectBalanced, rawRowCheck19533]

def rawRow19534 : Integer.Sparse Key := [(key1712, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1721, 6), (key1486, 6), (key1739, 6), (key1360, 6), (key1511, 6), (key1372, 6)]

theorem rawRowCheck19534 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form7 = rawRow19534 := by decide +kernel

def row19534 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19534 : row19534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19534 := by decide +kernel

theorem rowEval19534 (x : Key → ℝ) : Integer.Sparse.eval row19534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19534, Integer.Sparse.eval_collectBalanced, rawRowCheck19534]

def rawRow19535 : Integer.Sparse Key := [(key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1511, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1360, 6), (key1486, 6)]

theorem rawRowCheck19535 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form7 = rawRow19535 := by decide +kernel

def row19535 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19535 : row19535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19535 := by decide +kernel

theorem rowEval19535 (x : Key → ℝ) : Integer.Sparse.eval row19535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19535, Integer.Sparse.eval_collectBalanced, rawRowCheck19535]

def rawRow19536 : Integer.Sparse Key := [(key1712, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1372, 6), (key1486, 6), (key1360, 6)]

theorem rawRowCheck19536 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form7 = rawRow19536 := by decide +kernel

def row19536 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19536 : row19536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19536 := by decide +kernel

theorem rowEval19536 (x : Key → ℝ) : Integer.Sparse.eval row19536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19536, Integer.Sparse.eval_collectBalanced, rawRowCheck19536]

def rawRow19537 : Integer.Sparse Key := [(key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1739, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1511, 6), (key1739, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6)]

theorem rawRowCheck19537 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19537 := by decide +kernel

def row19537 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19537 : row19537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19537 := by decide +kernel

theorem rowEval19537 (x : Key → ℝ) : Integer.Sparse.eval row19537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19537, Integer.Sparse.eval_collectBalanced, rawRowCheck19537]

def rawRow19538 : Integer.Sparse Key := [(key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1739, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1739, 6), (key1511, 6), (key1739, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1360, 6), (key1486, 6)]

theorem rawRowCheck19538 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19538 := by decide +kernel

def row19538 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19538 : row19538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19538 := by decide +kernel

theorem rowEval19538 (x : Key → ℝ) : Integer.Sparse.eval row19538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19538, Integer.Sparse.eval_collectBalanced, rawRowCheck19538]

def rawRow19539 : Integer.Sparse Key := [(key1721, 6), (key1712, 6), (key1712, 6), (key1486, 6), (key1739, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1739, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1486, 6), (key1360, 6)]

theorem rawRowCheck19539 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19539 := by decide +kernel

def row19539 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19539 : row19539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19539 := by decide +kernel

theorem rowEval19539 (x : Key → ℝ) : Integer.Sparse.eval row19539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19539, Integer.Sparse.eval_collectBalanced, rawRowCheck19539]

def rawRow19540 : Integer.Sparse Key := [(key1511, 6), (key1739, 6), (key1739, 6), (key1739, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1360, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6), (key1712, 6)]

theorem rawRowCheck19540 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19540 := by decide +kernel

def row19540 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19540 : row19540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19540 := by decide +kernel

theorem rowEval19540 (x : Key → ℝ) : Integer.Sparse.eval row19540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19540, Integer.Sparse.eval_collectBalanced, rawRowCheck19540]

def rawRow19541 : Integer.Sparse Key := [(key1739, 6), (key1511, 6), (key1739, 6), (key1739, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1721, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1360, 6), (key1486, 6), (key1486, 6), (key1712, 6), (key1712, 6)]

theorem rawRowCheck19541 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19541 := by decide +kernel

def row19541 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19541 : row19541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19541 := by decide +kernel

theorem rowEval19541 (x : Key → ℝ) : Integer.Sparse.eval row19541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19541, Integer.Sparse.eval_collectBalanced, rawRowCheck19541]

def rawRow19542 : Integer.Sparse Key := [(key1739, 6), (key1739, 6), (key1511, 6), (key1739, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1721, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1360, 6), (key1486, 6)]

theorem rawRowCheck19542 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19542 := by decide +kernel

def row19542 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19542 : row19542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19542 := by decide +kernel

theorem rowEval19542 (x : Key → ℝ) : Integer.Sparse.eval row19542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19542, Integer.Sparse.eval_collectBalanced, rawRowCheck19542]

def rawRow19543 : Integer.Sparse Key := [(key1739, 6), (key1739, 6), (key1739, 6), (key1511, 6), (key1721, 6), (key1721, 6), (key1721, 6), (key1372, 6), (key1712, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1712, 6), (key1360, 6), (key1712, 6), (key1486, 6), (key1712, 6), (key1360, 6), (key1486, 6), (key1360, 6)]

theorem rawRowCheck19543 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19543 := by decide +kernel

def row19543 : Integer.Sparse Key := [(key1360, 18), (key1372, 6), (key1486, 18), (key1511, 6), (key1712, 36), (key1721, 18), (key1739, 18)]

theorem rowCheck19543 : row19543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19543 := by decide +kernel

theorem rowEval19543 (x : Key → ℝ) : Integer.Sparse.eval row19543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19543, Integer.Sparse.eval_collectBalanced, rawRowCheck19543]

def rawRow19544 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key515, 24), (key515, 24), (key547, 24)]

theorem rawRowCheck19544 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19544 := by decide +kernel

def row19544 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19544 : row19544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19544 := by decide +kernel

theorem rowEval19544 (x : Key → ℝ) : Integer.Sparse.eval row19544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19544, Integer.Sparse.eval_collectBalanced, rawRowCheck19544]

def rawRow19545 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key515, 24), (key515, 24), (key547, 24)]

theorem rawRowCheck19545 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19545 := by decide +kernel

def row19545 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19545 : row19545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19545 := by decide +kernel

theorem rowEval19545 (x : Key → ℝ) : Integer.Sparse.eval row19545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19545, Integer.Sparse.eval_collectBalanced, rawRowCheck19545]

def rawRow19546 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key513, 24), (key515, 24), (key547, 24)]

theorem rawRowCheck19546 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19546 := by decide +kernel

def row19546 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19546 : row19546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19546 := by decide +kernel

theorem rowEval19546 (x : Key → ℝ) : Integer.Sparse.eval row19546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19546, Integer.Sparse.eval_collectBalanced, rawRowCheck19546]

def rawRow19547 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key515, 24), (key513, 24), (key547, 24)]

theorem rawRowCheck19547 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19547 := by decide +kernel

def row19547 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19547 : row19547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19547 := by decide +kernel

theorem rowEval19547 (x : Key → ℝ) : Integer.Sparse.eval row19547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19547, Integer.Sparse.eval_collectBalanced, rawRowCheck19547]

def rawRow19548 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key515, 24), (key547, 24), (key515, 24)]

theorem rawRowCheck19548 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19548 := by decide +kernel

def row19548 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19548 : row19548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19548 := by decide +kernel

theorem rowEval19548 (x : Key → ℝ) : Integer.Sparse.eval row19548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19548, Integer.Sparse.eval_collectBalanced, rawRowCheck19548]

def rawRow19549 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key515, 24), (key547, 24), (key515, 24)]

theorem rawRowCheck19549 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19549 := by decide +kernel

def row19549 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19549 : row19549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19549 := by decide +kernel

theorem rowEval19549 (x : Key → ℝ) : Integer.Sparse.eval row19549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19549, Integer.Sparse.eval_collectBalanced, rawRowCheck19549]

def rawRow19550 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key513, 24), (key547, 24), (key515, 24)]

theorem rawRowCheck19550 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19550 := by decide +kernel

def row19550 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19550 : row19550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19550 := by decide +kernel

theorem rowEval19550 (x : Key → ℝ) : Integer.Sparse.eval row19550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19550, Integer.Sparse.eval_collectBalanced, rawRowCheck19550]

def rawRow19551 : Integer.Sparse Key := [(key513, 24), (key515, 24), (key547, 24), (key515, 24), (key515, 24)]

theorem rawRowCheck19551 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form8 = rawRow19551 := by decide +kernel

def row19551 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19551 : row19551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19551 := by decide +kernel

theorem rowEval19551 (x : Key → ℝ) : Integer.Sparse.eval row19551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19551, Integer.Sparse.eval_collectBalanced, rawRowCheck19551]

def rawRow19552 : Integer.Sparse Key := [(key515, 24), (key513, 24), (key547, 24), (key515, 24), (key515, 24)]

theorem rawRowCheck19552 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form8 = rawRow19552 := by decide +kernel

def row19552 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19552 : row19552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19552 := by decide +kernel

theorem rowEval19552 (x : Key → ℝ) : Integer.Sparse.eval row19552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19552, Integer.Sparse.eval_collectBalanced, rawRowCheck19552]

def rawRow19553 : Integer.Sparse Key := [(key513, 24), (key547, 24), (key515, 24), (key515, 24), (key515, 24)]

theorem rawRowCheck19553 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form8 = rawRow19553 := by decide +kernel

def row19553 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19553 : row19553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19553 := by decide +kernel

theorem rowEval19553 (x : Key → ℝ) : Integer.Sparse.eval row19553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19553, Integer.Sparse.eval_collectBalanced, rawRowCheck19553]

def rawRow19554 : Integer.Sparse Key := [(key547, 24), (key513, 24), (key515, 24), (key515, 24), (key515, 24)]

theorem rawRowCheck19554 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form8 = rawRow19554 := by decide +kernel

def row19554 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19554 : row19554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19554 := by decide +kernel

theorem rowEval19554 (x : Key → ℝ) : Integer.Sparse.eval row19554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19554, Integer.Sparse.eval_collectBalanced, rawRowCheck19554]

def rawRow19555 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key513, 24), (key515, 24), (key515, 24)]

theorem rawRowCheck19555 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form8 = rawRow19555 := by decide +kernel

def row19555 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19555 : row19555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19555 := by decide +kernel

theorem rowEval19555 (x : Key → ℝ) : Integer.Sparse.eval row19555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19555, Integer.Sparse.eval_collectBalanced, rawRowCheck19555]

def rawRow19556 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key513, 24), (key515, 24), (key515, 24)]

theorem rawRowCheck19556 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form8 = rawRow19556 := by decide +kernel

def row19556 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19556 : row19556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19556 := by decide +kernel

theorem rowEval19556 (x : Key → ℝ) : Integer.Sparse.eval row19556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19556, Integer.Sparse.eval_collectBalanced, rawRowCheck19556]

def rawRow19557 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key547, 24), (key513, 24), (key515, 24)]

theorem rawRowCheck19557 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form8 = rawRow19557 := by decide +kernel

def row19557 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19557 : row19557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19557 := by decide +kernel

theorem rowEval19557 (x : Key → ℝ) : Integer.Sparse.eval row19557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19557, Integer.Sparse.eval_collectBalanced, rawRowCheck19557]

def rawRow19558 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key515, 24), (key513, 24), (key515, 24)]

theorem rawRowCheck19558 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form8 = rawRow19558 := by decide +kernel

def row19558 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19558 : row19558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19558 := by decide +kernel

theorem rowEval19558 (x : Key → ℝ) : Integer.Sparse.eval row19558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19558, Integer.Sparse.eval_collectBalanced, rawRowCheck19558]

def rawRow19559 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key515, 24), (key513, 24), (key515, 24)]

theorem rawRowCheck19559 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form8 = rawRow19559 := by decide +kernel

def row19559 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19559 : row19559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19559 := by decide +kernel

theorem rowEval19559 (x : Key → ℝ) : Integer.Sparse.eval row19559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19559, Integer.Sparse.eval_collectBalanced, rawRowCheck19559]

def rawRow19560 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key515, 24), (key547, 24), (key513, 24)]

theorem rawRowCheck19560 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19560 := by decide +kernel

def row19560 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19560 : row19560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19560 := by decide +kernel

theorem rowEval19560 (x : Key → ℝ) : Integer.Sparse.eval row19560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19560, Integer.Sparse.eval_collectBalanced, rawRowCheck19560]

def rawRow19561 : Integer.Sparse Key := [(key515, 24), (key515, 24), (key547, 24), (key515, 24), (key513, 24)]

theorem rawRowCheck19561 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form8 = rawRow19561 := by decide +kernel

def row19561 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19561 : row19561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19561 := by decide +kernel

theorem rowEval19561 (x : Key → ℝ) : Integer.Sparse.eval row19561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19561, Integer.Sparse.eval_collectBalanced, rawRowCheck19561]

def rawRow19562 : Integer.Sparse Key := [(key515, 24), (key547, 24), (key515, 24), (key515, 24), (key513, 24)]

theorem rawRowCheck19562 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form8 = rawRow19562 := by decide +kernel

def row19562 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19562 : row19562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19562 := by decide +kernel

theorem rowEval19562 (x : Key → ℝ) : Integer.Sparse.eval row19562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19562, Integer.Sparse.eval_collectBalanced, rawRowCheck19562]

def rawRow19563 : Integer.Sparse Key := [(key547, 24), (key515, 24), (key515, 24), (key515, 24), (key513, 24)]

theorem rawRowCheck19563 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form8 = rawRow19563 := by decide +kernel

def row19563 : Integer.Sparse Key := [(key513, 24), (key515, 72), (key547, 24)]

theorem rowCheck19563 : row19563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19563 := by decide +kernel

theorem rowEval19563 (x : Key → ℝ) : Integer.Sparse.eval row19563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19563, Integer.Sparse.eval_collectBalanced, rawRowCheck19563]

def rawRow19564 : Integer.Sparse Key := [(key1501, 12), (key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1733, 12), (key1735, 12), (key1735, 12), (key1735, 12)]

theorem rawRowCheck19564 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form9 = rawRow19564 := by decide +kernel

def row19564 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19564 : row19564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19564 := by decide +kernel

theorem rowEval19564 (x : Key → ℝ) : Integer.Sparse.eval row19564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19564, Integer.Sparse.eval_collectBalanced, rawRowCheck19564]

def rawRow19565 : Integer.Sparse Key := [(key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1733, 12), (key1735, 12), (key1735, 12)]

theorem rawRowCheck19565 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form9 = rawRow19565 := by decide +kernel

def row19565 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19565 : row19565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19565 := by decide +kernel

theorem rowEval19565 (x : Key → ℝ) : Integer.Sparse.eval row19565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19565, Integer.Sparse.eval_collectBalanced, rawRowCheck19565]

def rawRow19566 : Integer.Sparse Key := [(key1506, 12), (key1501, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1733, 12), (key1735, 12)]

theorem rawRowCheck19566 : GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form9 = rawRow19566 := by decide +kernel

def row19566 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19566 : row19566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19566 := by decide +kernel

theorem rowEval19566 (x : Key → ℝ) : Integer.Sparse.eval row19566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 0, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19566, Integer.Sparse.eval_collectBalanced, rawRowCheck19566]

def rawRow19567 : Integer.Sparse Key := [(key1506, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1735, 12), (key1733, 12)]

theorem rawRowCheck19567 : GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form9 = rawRow19567 := by decide +kernel

def row19567 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19567 : row19567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19567 := by decide +kernel

theorem rowEval19567 (x : Key → ℝ) : Integer.Sparse.eval row19567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -2, 2, 0, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19567, Integer.Sparse.eval_collectBalanced, rawRowCheck19567]

def rawRow19568 : Integer.Sparse Key := [(key1501, 12), (key1501, 12), (key1506, 12), (key1733, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1506, 12), (key1735, 12)]

theorem rawRowCheck19568 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form9 = rawRow19568 := by decide +kernel

def row19568 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19568 : row19568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19568 := by decide +kernel

theorem rowEval19568 (x : Key → ℝ) : Integer.Sparse.eval row19568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19568, Integer.Sparse.eval_collectBalanced, rawRowCheck19568]

def rawRow19569 : Integer.Sparse Key := [(key1501, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1733, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1506, 12), (key1735, 12)]

theorem rawRowCheck19569 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form9 = rawRow19569 := by decide +kernel

def row19569 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19569 : row19569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19569 := by decide +kernel

theorem rowEval19569 (x : Key → ℝ) : Integer.Sparse.eval row19569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19569, Integer.Sparse.eval_collectBalanced, rawRowCheck19569]

def rawRow19570 : Integer.Sparse Key := [(key1506, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1735, 12), (key1733, 12), (key1506, 12), (key1506, 12), (key1501, 12), (key1735, 12)]

theorem rawRowCheck19570 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form9 = rawRow19570 := by decide +kernel

def row19570 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19570 : row19570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19570 := by decide +kernel

theorem rowEval19570 (x : Key → ℝ) : Integer.Sparse.eval row19570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19570, Integer.Sparse.eval_collectBalanced, rawRowCheck19570]

def rawRow19571 : Integer.Sparse Key := [(key1501, 12), (key1733, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1506, 12)]

theorem rawRowCheck19571 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form9 = rawRow19571 := by decide +kernel

def row19571 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19571 : row19571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19571 := by decide +kernel

theorem rowEval19571 (x : Key → ℝ) : Integer.Sparse.eval row19571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19571, Integer.Sparse.eval_collectBalanced, rawRowCheck19571]

def rawRow19572 : Integer.Sparse Key := [(key1501, 12), (key1735, 12), (key1733, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12)]

theorem rawRowCheck19572 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form9 = rawRow19572 := by decide +kernel

def row19572 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19572 : row19572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19572 := by decide +kernel

theorem rowEval19572 (x : Key → ℝ) : Integer.Sparse.eval row19572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19572, Integer.Sparse.eval_collectBalanced, rawRowCheck19572]

def rawRow19573 : Integer.Sparse Key := [(key1733, 12), (key1501, 12), (key1735, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1506, 12)]

theorem rawRowCheck19573 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form9 = rawRow19573 := by decide +kernel

def row19573 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19573 : row19573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19573 := by decide +kernel

theorem rowEval19573 (x : Key → ℝ) : Integer.Sparse.eval row19573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19573, Integer.Sparse.eval_collectBalanced, rawRowCheck19573]

def rawRow19574 : Integer.Sparse Key := [(key1733, 12), (key1735, 12), (key1501, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1506, 12)]

theorem rawRowCheck19574 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form9 = rawRow19574 := by decide +kernel

def row19574 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19574 : row19574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19574 := by decide +kernel

theorem rowEval19574 (x : Key → ℝ) : Integer.Sparse.eval row19574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19574, Integer.Sparse.eval_collectBalanced, rawRowCheck19574]

def rawRow19575 : Integer.Sparse Key := [(key1735, 12), (key1501, 12), (key1733, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1506, 12)]

theorem rawRowCheck19575 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form9 = rawRow19575 := by decide +kernel

def row19575 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19575 : row19575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19575 := by decide +kernel

theorem rowEval19575 (x : Key → ℝ) : Integer.Sparse.eval row19575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19575, Integer.Sparse.eval_collectBalanced, rawRowCheck19575]

def rawRow19576 : Integer.Sparse Key := [(key1735, 12), (key1733, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1506, 12)]

theorem rawRowCheck19576 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form9 = rawRow19576 := by decide +kernel

def row19576 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19576 : row19576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19576 := by decide +kernel

theorem rowEval19576 (x : Key → ℝ) : Integer.Sparse.eval row19576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19576, Integer.Sparse.eval_collectBalanced, rawRowCheck19576]

def rawRow19577 : Integer.Sparse Key := [(key1506, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1733, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1501, 12)]

theorem rawRowCheck19577 : GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form9 = rawRow19577 := by decide +kernel

def row19577 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19577 : row19577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19577 := by decide +kernel

theorem rowEval19577 (x : Key → ℝ) : Integer.Sparse.eval row19577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19577, Integer.Sparse.eval_collectBalanced, rawRowCheck19577]

def rawRow19578 : Integer.Sparse Key := [(key1735, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1733, 12), (key1501, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1501, 12)]

theorem rawRowCheck19578 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form9 = rawRow19578 := by decide +kernel

def row19578 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19578 : row19578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19578 := by decide +kernel

theorem rowEval19578 (x : Key → ℝ) : Integer.Sparse.eval row19578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19578, Integer.Sparse.eval_collectBalanced, rawRowCheck19578]

def rawRow19579 : Integer.Sparse Key := [(key1735, 12), (key1735, 12), (key1506, 12), (key1733, 12), (key1501, 12), (key1501, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1501, 12)]

theorem rawRowCheck19579 : GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form9 = rawRow19579 := by decide +kernel

def row19579 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19579 : row19579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19579 := by decide +kernel

theorem rowEval19579 (x : Key → ℝ) : Integer.Sparse.eval row19579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 2, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19579, Integer.Sparse.eval_collectBalanced, rawRowCheck19579]

def rawRow19580 : Integer.Sparse Key := [(key1506, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1735, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1501, 12), (key1733, 12)]

theorem rawRowCheck19580 : GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form9 = rawRow19580 := by decide +kernel

def row19580 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19580 : row19580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19580 := by decide +kernel

theorem rowEval19580 (x : Key → ℝ) : Integer.Sparse.eval row19580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, -2, 0, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19580, Integer.Sparse.eval_collectBalanced, rawRowCheck19580]

def rawRow19581 : Integer.Sparse Key := [(key1506, 12), (key1735, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1735, 12), (key1501, 12), (key1501, 12), (key1733, 12), (key1501, 12)]

theorem rawRowCheck19581 : GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form9 = rawRow19581 := by decide +kernel

def row19581 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19581 : row19581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19581 := by decide +kernel

theorem rowEval19581 (x : Key → ℝ) : Integer.Sparse.eval row19581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19581, Integer.Sparse.eval_collectBalanced, rawRowCheck19581]

def rawRow19582 : Integer.Sparse Key := [(key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1501, 12), (key1733, 12), (key1501, 12), (key1501, 12)]

theorem rawRowCheck19582 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form9 = rawRow19582 := by decide +kernel

def row19582 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19582 : row19582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19582 := by decide +kernel

theorem rowEval19582 (x : Key → ℝ) : Integer.Sparse.eval row19582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck19582, Integer.Sparse.eval_collectBalanced, rawRowCheck19582]

def rawRow19583 : Integer.Sparse Key := [(key1735, 12), (key1735, 12), (key1506, 12), (key1735, 12), (key1506, 12), (key1506, 12), (key1733, 12), (key1501, 12), (key1501, 12), (key1501, 12)]

theorem rawRowCheck19583 : GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form9 = rawRow19583 := by decide +kernel

def row19583 : Integer.Sparse Key := [(key1501, 36), (key1506, 36), (key1733, 12), (key1735, 36)]

theorem rowCheck19583 : row19583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19583 := by decide +kernel

theorem rowEval19583 (x : Key → ℝ) : Integer.Sparse.eval row19583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 2, 0, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck19583, Integer.Sparse.eval_collectBalanced, rawRowCheck19583]

end MUB6.Certificate.GramRows

end OAI
