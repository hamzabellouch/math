import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14464 : Integer.Sparse Key := [(key2816, 4), (key2687, 4), (key2816, 4), (key2678, -4), (key2812, -4), (key2678, -4), (key2713, -4), (key2862, -4), (key2713, -4), (key2709, 12)]

theorem rawRowCheck14464 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form7 = rawRow14464 := by decide +kernel

def row14464 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck14464 : row14464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14464 := by decide +kernel

theorem rowEval14464 (x : Key → ℝ) : Integer.Sparse.eval row14464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14464, Integer.Sparse.eval_collectBalanced, rawRowCheck14464]

def rawRow14465 : Integer.Sparse Key := [(key2816, 4), (key2816, 4), (key2687, 4), (key2812, -4), (key2678, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2713, -4), (key2709, 12)]

theorem rawRowCheck14465 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form7 = rawRow14465 := by decide +kernel

def row14465 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck14465 : row14465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14465 := by decide +kernel

theorem rowEval14465 (x : Key → ℝ) : Integer.Sparse.eval row14465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14465, Integer.Sparse.eval_collectBalanced, rawRowCheck14465]

def rawRow14466 : Integer.Sparse Key := [(key2678, 4), (key2812, 4), (key2816, 4), (key2709, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2687, -4), (key2816, -4), (key2713, 12)]

theorem rawRowCheck14466 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form7 = rawRow14466 := by decide +kernel

def row14466 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14466 : row14466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14466 := by decide +kernel

theorem rowEval14466 (x : Key → ℝ) : Integer.Sparse.eval row14466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14466, Integer.Sparse.eval_collectBalanced, rawRowCheck14466]

def rawRow14467 : Integer.Sparse Key := [(key2678, 4), (key2816, 4), (key2812, 4), (key2713, -4), (key2709, -4), (key2862, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, 12)]

theorem rawRowCheck14467 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form7 = rawRow14467 := by decide +kernel

def row14467 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14467 : row14467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14467 := by decide +kernel

theorem rowEval14467 (x : Key → ℝ) : Integer.Sparse.eval row14467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14467, Integer.Sparse.eval_collectBalanced, rawRowCheck14467]

def rawRow14468 : Integer.Sparse Key := [(key2812, 4), (key2678, 4), (key2816, 4), (key2709, -4), (key2862, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2713, 12)]

theorem rawRowCheck14468 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form7 = rawRow14468 := by decide +kernel

def row14468 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14468 : row14468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14468 := by decide +kernel

theorem rowEval14468 (x : Key → ℝ) : Integer.Sparse.eval row14468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14468, Integer.Sparse.eval_collectBalanced, rawRowCheck14468]

def rawRow14469 : Integer.Sparse Key := [(key2812, 4), (key2816, 4), (key2678, 4), (key2862, -4), (key2709, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2713, 12)]

theorem rawRowCheck14469 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form7 = rawRow14469 := by decide +kernel

def row14469 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14469 : row14469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14469 := by decide +kernel

theorem rowEval14469 (x : Key → ℝ) : Integer.Sparse.eval row14469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14469, Integer.Sparse.eval_collectBalanced, rawRowCheck14469]

def rawRow14470 : Integer.Sparse Key := [(key2816, 4), (key2678, 4), (key2812, 4), (key2713, -4), (key2862, -4), (key2709, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, 12)]

theorem rawRowCheck14470 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form7 = rawRow14470 := by decide +kernel

def row14470 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14470 : row14470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14470 := by decide +kernel

theorem rowEval14470 (x : Key → ℝ) : Integer.Sparse.eval row14470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14470, Integer.Sparse.eval_collectBalanced, rawRowCheck14470]

def rawRow14471 : Integer.Sparse Key := [(key2816, 4), (key2812, 4), (key2678, 4), (key2862, -4), (key2713, -4), (key2709, -4), (key2816, -4), (key2687, -4), (key2678, -4), (key2713, 12)]

theorem rawRowCheck14471 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form7 = rawRow14471 := by decide +kernel

def row14471 : Integer.Sparse Key := [(key2687, -4), (key2709, -4), (key2713, 8), (key2812, 4), (key2862, -4)]

theorem rowCheck14471 : row14471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14471 := by decide +kernel

theorem rowEval14471 (x : Key → ℝ) : Integer.Sparse.eval row14471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14471, Integer.Sparse.eval_collectBalanced, rawRowCheck14471]

def rawRow14472 : Integer.Sparse Key := [(key2709, 4), (key2812, 4), (key2862, 4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2687, 12)]

theorem rawRowCheck14472 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form7 = rawRow14472 := by decide +kernel

def row14472 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

theorem rowCheck14472 : row14472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14472 := by decide +kernel

theorem rowEval14472 (x : Key → ℝ) : Integer.Sparse.eval row14472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14472, Integer.Sparse.eval_collectBalanced, rawRowCheck14472]

def rawRow14473 : Integer.Sparse Key := [(key2709, 4), (key2862, 4), (key2812, 4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2687, 12)]

theorem rawRowCheck14473 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form7 = rawRow14473 := by decide +kernel

def row14473 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

theorem rowCheck14473 : row14473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14473 := by decide +kernel

theorem rowEval14473 (x : Key → ℝ) : Integer.Sparse.eval row14473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14473, Integer.Sparse.eval_collectBalanced, rawRowCheck14473]

def rawRow14474 : Integer.Sparse Key := [(key2812, 4), (key2709, 4), (key2862, 4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2687, 12)]

theorem rawRowCheck14474 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form7 = rawRow14474 := by decide +kernel

def row14474 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

theorem rowCheck14474 : row14474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14474 := by decide +kernel

theorem rowEval14474 (x : Key → ℝ) : Integer.Sparse.eval row14474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14474, Integer.Sparse.eval_collectBalanced, rawRowCheck14474]

def rawRow14475 : Integer.Sparse Key := [(key2812, 4), (key2862, 4), (key2709, 4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2687, 12)]

theorem rawRowCheck14475 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form7 = rawRow14475 := by decide +kernel

def row14475 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

theorem rowCheck14475 : row14475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14475 := by decide +kernel

theorem rowEval14475 (x : Key → ℝ) : Integer.Sparse.eval row14475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14475, Integer.Sparse.eval_collectBalanced, rawRowCheck14475]

def rawRow14476 : Integer.Sparse Key := [(key2862, 4), (key2709, 4), (key2812, 4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2687, 12)]

theorem rawRowCheck14476 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form7 = rawRow14476 := by decide +kernel

def row14476 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

theorem rowCheck14476 : row14476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14476 := by decide +kernel

theorem rowEval14476 (x : Key → ℝ) : Integer.Sparse.eval row14476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14476, Integer.Sparse.eval_collectBalanced, rawRowCheck14476]

def rawRow14477 : Integer.Sparse Key := [(key2862, 4), (key2812, 4), (key2709, 4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2687, 12)]

theorem rawRowCheck14477 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form7 = rawRow14477 := by decide +kernel

def row14477 : Integer.Sparse Key := [(key2678, -8), (key2687, 12), (key2709, 4), (key2713, -8), (key2812, 4), (key2816, -8), (key2862, 4)]

theorem rowCheck14477 : row14477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14477 := by decide +kernel

theorem rowEval14477 (x : Key → ℝ) : Integer.Sparse.eval row14477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14477, Integer.Sparse.eval_collectBalanced, rawRowCheck14477]

def rawRow14478 : Integer.Sparse Key := [(key2713, 4), (key2816, 4), (key2862, 4), (key2678, -4), (key2709, -4), (key2812, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, 12)]

theorem rawRowCheck14478 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form7 = rawRow14478 := by decide +kernel

def row14478 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14478 : row14478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14478 := by decide +kernel

theorem rowEval14478 (x : Key → ℝ) : Integer.Sparse.eval row14478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14478, Integer.Sparse.eval_collectBalanced, rawRowCheck14478]

def rawRow14479 : Integer.Sparse Key := [(key2713, 4), (key2862, 4), (key2816, 4), (key2709, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2687, -4), (key2816, -4), (key2678, 12)]

theorem rawRowCheck14479 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form7 = rawRow14479 := by decide +kernel

def row14479 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14479 : row14479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14479 := by decide +kernel

theorem rowEval14479 (x : Key → ℝ) : Integer.Sparse.eval row14479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14479, Integer.Sparse.eval_collectBalanced, rawRowCheck14479]

def rawRow14480 : Integer.Sparse Key := [(key2816, 4), (key2713, 4), (key2862, 4), (key2678, -4), (key2812, -4), (key2709, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, 12)]

theorem rawRowCheck14480 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form7 = rawRow14480 := by decide +kernel

def row14480 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14480 : row14480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14480 := by decide +kernel

theorem rowEval14480 (x : Key → ℝ) : Integer.Sparse.eval row14480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14480, Integer.Sparse.eval_collectBalanced, rawRowCheck14480]

def rawRow14481 : Integer.Sparse Key := [(key2816, 4), (key2862, 4), (key2713, 4), (key2812, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2687, -4), (key2713, -4), (key2678, 12)]

theorem rawRowCheck14481 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form7 = rawRow14481 := by decide +kernel

def row14481 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14481 : row14481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14481 := by decide +kernel

theorem rowEval14481 (x : Key → ℝ) : Integer.Sparse.eval row14481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14481, Integer.Sparse.eval_collectBalanced, rawRowCheck14481]

def rawRow14482 : Integer.Sparse Key := [(key2862, 4), (key2713, 4), (key2816, 4), (key2709, -4), (key2812, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2678, 12)]

theorem rawRowCheck14482 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form7 = rawRow14482 := by decide +kernel

def row14482 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14482 : row14482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14482 := by decide +kernel

theorem rowEval14482 (x : Key → ℝ) : Integer.Sparse.eval row14482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14482, Integer.Sparse.eval_collectBalanced, rawRowCheck14482]

def rawRow14483 : Integer.Sparse Key := [(key2862, 4), (key2816, 4), (key2713, 4), (key2812, -4), (key2709, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2678, 12)]

theorem rawRowCheck14483 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form7 = rawRow14483 := by decide +kernel

def row14483 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14483 : row14483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14483 := by decide +kernel

theorem rowEval14483 (x : Key → ℝ) : Integer.Sparse.eval row14483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14483, Integer.Sparse.eval_collectBalanced, rawRowCheck14483]

def rawRow14484 : Integer.Sparse Key := [(key2687, 4), (key2816, 4), (key2816, 4), (key2713, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2678, -4), (key2812, -4), (key2709, 12)]

theorem rawRowCheck14484 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form7 = rawRow14484 := by decide +kernel

def row14484 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck14484 : row14484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14484 := by decide +kernel

theorem rowEval14484 (x : Key → ℝ) : Integer.Sparse.eval row14484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14484, Integer.Sparse.eval_collectBalanced, rawRowCheck14484]

def rawRow14485 : Integer.Sparse Key := [(key2816, 4), (key2687, 4), (key2816, 4), (key2713, -4), (key2862, -4), (key2713, -4), (key2678, -4), (key2812, -4), (key2678, -4), (key2709, 12)]

theorem rawRowCheck14485 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form7 = rawRow14485 := by decide +kernel

def row14485 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck14485 : row14485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14485 := by decide +kernel

theorem rowEval14485 (x : Key → ℝ) : Integer.Sparse.eval row14485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14485, Integer.Sparse.eval_collectBalanced, rawRowCheck14485]

def rawRow14486 : Integer.Sparse Key := [(key2816, 4), (key2816, 4), (key2687, 4), (key2862, -4), (key2713, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2678, -4), (key2709, 12)]

theorem rawRowCheck14486 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form7 = rawRow14486 := by decide +kernel

def row14486 : Integer.Sparse Key := [(key2678, -8), (key2687, 4), (key2709, 12), (key2713, -8), (key2812, -4), (key2816, 8), (key2862, -4)]

theorem rowCheck14486 : row14486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14486 := by decide +kernel

theorem rowEval14486 (x : Key → ℝ) : Integer.Sparse.eval row14486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14486, Integer.Sparse.eval_collectBalanced, rawRowCheck14486]

def rawRow14487 : Integer.Sparse Key := [(key2713, 4), (key2816, 4), (key2862, 4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2709, -4), (key2812, -4), (key2678, 12)]

theorem rawRowCheck14487 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form7 = rawRow14487 := by decide +kernel

def row14487 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14487 : row14487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14487 := by decide +kernel

theorem rowEval14487 (x : Key → ℝ) : Integer.Sparse.eval row14487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14487, Integer.Sparse.eval_collectBalanced, rawRowCheck14487]

def rawRow14488 : Integer.Sparse Key := [(key2713, 4), (key2862, 4), (key2816, 4), (key2713, -4), (key2687, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2812, -4), (key2678, 12)]

theorem rawRowCheck14488 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form7 = rawRow14488 := by decide +kernel

def row14488 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14488 : row14488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14488 := by decide +kernel

theorem rowEval14488 (x : Key → ℝ) : Integer.Sparse.eval row14488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14488, Integer.Sparse.eval_collectBalanced, rawRowCheck14488]

def rawRow14489 : Integer.Sparse Key := [(key2816, 4), (key2713, 4), (key2862, 4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2812, -4), (key2709, -4), (key2678, 12)]

theorem rawRowCheck14489 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form7 = rawRow14489 := by decide +kernel

def row14489 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14489 : row14489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14489 := by decide +kernel

theorem rowEval14489 (x : Key → ℝ) : Integer.Sparse.eval row14489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck14489, Integer.Sparse.eval_collectBalanced, rawRowCheck14489]

def rawRow14490 : Integer.Sparse Key := [(key2816, 4), (key2862, 4), (key2713, 4), (key2816, -4), (key2687, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2709, -4), (key2678, 12)]

theorem rawRowCheck14490 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form7 = rawRow14490 := by decide +kernel

def row14490 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14490 : row14490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14490 := by decide +kernel

theorem rowEval14490 (x : Key → ℝ) : Integer.Sparse.eval row14490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14490, Integer.Sparse.eval_collectBalanced, rawRowCheck14490]

def rawRow14491 : Integer.Sparse Key := [(key2862, 4), (key2713, 4), (key2816, 4), (key2713, -4), (key2816, -4), (key2687, -4), (key2709, -4), (key2812, -4), (key2678, -4), (key2678, 12)]

theorem rawRowCheck14491 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form7 = rawRow14491 := by decide +kernel

def row14491 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14491 : row14491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14491 := by decide +kernel

theorem rowEval14491 (x : Key → ℝ) : Integer.Sparse.eval row14491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck14491, Integer.Sparse.eval_collectBalanced, rawRowCheck14491]

def rawRow14492 : Integer.Sparse Key := [(key2862, 4), (key2816, 4), (key2713, 4), (key2816, -4), (key2713, -4), (key2687, -4), (key2812, -4), (key2709, -4), (key2678, -4), (key2678, 12)]

theorem rawRowCheck14492 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form7 = rawRow14492 := by decide +kernel

def row14492 : Integer.Sparse Key := [(key2678, 8), (key2687, -4), (key2709, -4), (key2812, -4), (key2862, 4)]

theorem rowCheck14492 : row14492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14492 := by decide +kernel

theorem rowEval14492 (x : Key → ℝ) : Integer.Sparse.eval row14492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck14492, Integer.Sparse.eval_collectBalanced, rawRowCheck14492]

def rawRow14493 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2401, 6), (key2839, -2), (key2842, -2), (key2965, -2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2586, -2), (key2842, -2), (key2874, -2), (key2886, 6), (key2597, -2), (key2886, -2), (key2908, -2)]

theorem rawRowCheck14493 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form8 = rawRow14493 := by decide +kernel

def row14493 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

theorem rowCheck14493 : row14493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14493 := by decide +kernel

theorem rowEval14493 (x : Key → ℝ) : Integer.Sparse.eval row14493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14493, Integer.Sparse.eval_collectBalanced, rawRowCheck14493]

def rawRow14494 : Integer.Sparse Key := [(key2401, -2), (key2398, -2), (key2433, -2), (key2401, 6), (key2842, -2), (key2839, -2), (key2965, -2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2586, -2), (key2874, -2), (key2842, -2), (key2886, 6), (key2597, -2), (key2908, -2), (key2886, -2)]

theorem rawRowCheck14494 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form8 = rawRow14494 := by decide +kernel

def row14494 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

theorem rowCheck14494 : row14494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14494 := by decide +kernel

theorem rowEval14494 (x : Key → ℝ) : Integer.Sparse.eval row14494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14494, Integer.Sparse.eval_collectBalanced, rawRowCheck14494]

def rawRow14495 : Integer.Sparse Key := [(key2398, -2), (key2433, -2), (key2401, -2), (key2401, 6), (key2839, -2), (key2965, -2), (key2842, -2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2842, -2), (key2586, -2), (key2874, -2), (key2886, 6), (key2886, -2), (key2597, -2), (key2908, -2)]

theorem rawRowCheck14495 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form8 = rawRow14495 := by decide +kernel

def row14495 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

theorem rowCheck14495 : row14495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14495 := by decide +kernel

theorem rowEval14495 (x : Key → ℝ) : Integer.Sparse.eval row14495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14495, Integer.Sparse.eval_collectBalanced, rawRowCheck14495]

def rawRow14496 : Integer.Sparse Key := [(key2433, -2), (key2398, -2), (key2401, -2), (key2401, 6), (key2965, -2), (key2839, -2), (key2842, -2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2842, -2), (key2874, -2), (key2586, -2), (key2886, 6), (key2886, -2), (key2908, -2), (key2597, -2)]

theorem rawRowCheck14496 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form8 = rawRow14496 := by decide +kernel

def row14496 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

theorem rowCheck14496 : row14496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14496 := by decide +kernel

theorem rowEval14496 (x : Key → ℝ) : Integer.Sparse.eval row14496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14496, Integer.Sparse.eval_collectBalanced, rawRowCheck14496]

def rawRow14497 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2398, -2), (key2401, 6), (key2842, -2), (key2965, -2), (key2839, -2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2874, -2), (key2586, -2), (key2842, -2), (key2886, 6), (key2908, -2), (key2597, -2), (key2886, -2)]

theorem rawRowCheck14497 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form8 = rawRow14497 := by decide +kernel

def row14497 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

theorem rowCheck14497 : row14497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14497 := by decide +kernel

theorem rowEval14497 (x : Key → ℝ) : Integer.Sparse.eval row14497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14497, Integer.Sparse.eval_collectBalanced, rawRowCheck14497]

def rawRow14498 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2398, -2), (key2401, 6), (key2965, -2), (key2842, -2), (key2839, -2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2874, -2), (key2842, -2), (key2586, -2), (key2886, 6), (key2908, -2), (key2886, -2), (key2597, -2)]

theorem rawRowCheck14498 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form8 = rawRow14498 := by decide +kernel

def row14498 : Integer.Sparse Key := [(key2398, -2), (key2401, 4), (key2433, -2), (key2583, 2), (key2597, -2), (key2842, -4), (key2886, 4), (key2908, -2), (key2987, 2)]

theorem rowCheck14498 : row14498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14498 := by decide +kernel

theorem rowEval14498 (x : Key → ℝ) : Integer.Sparse.eval row14498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14498, Integer.Sparse.eval_collectBalanced, rawRowCheck14498]

def rawRow14499 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2433, -2), (key2398, 6), (key2874, -2), (key2874, -2), (key2987, -2), (key2586, 2), (key2586, 2), (key2842, 2), (key2842, 2), (key2965, 2), (key2965, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2908, 6), (key2597, -2), (key2886, -2), (key2886, -2)]

theorem rawRowCheck14499 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14499 := by decide +kernel

def row14499 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

theorem rowCheck14499 : row14499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14499 := by decide +kernel

theorem rowEval14499 (x : Key → ℝ) : Integer.Sparse.eval row14499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14499, Integer.Sparse.eval_collectBalanced, rawRowCheck14499]

def rawRow14500 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2401, -2), (key2398, 6), (key2874, -2), (key2987, -2), (key2874, -2), (key2842, 2), (key2965, 2), (key2586, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2908, 6), (key2886, -2), (key2597, -2), (key2886, -2)]

theorem rawRowCheck14500 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14500 := by decide +kernel

def row14500 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

theorem rowCheck14500 : row14500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14500 := by decide +kernel

theorem rowEval14500 (x : Key → ℝ) : Integer.Sparse.eval row14500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14500, Integer.Sparse.eval_collectBalanced, rawRowCheck14500]

def rawRow14501 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2401, -2), (key2398, 6), (key2987, -2), (key2874, -2), (key2874, -2), (key2965, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2586, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2908, 6), (key2886, -2), (key2886, -2), (key2597, -2)]

theorem rawRowCheck14501 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14501 := by decide +kernel

def row14501 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2586, 4), (key2597, -2), (key2839, -4), (key2842, 4), (key2874, -4), (key2886, -4), (key2908, 6), (key2965, 4), (key2987, -2)]

theorem rowCheck14501 : row14501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14501 := by decide +kernel

theorem rowEval14501 (x : Key → ℝ) : Integer.Sparse.eval row14501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14501, Integer.Sparse.eval_collectBalanced, rawRowCheck14501]

def rawRow14502 : Integer.Sparse Key := [(key2464, -2), (key2467, -2), (key2499, -2), (key2476, 6), (key2398, -2), (key2401, -2), (key2433, -2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2597, -2), (key2886, -2), (key2908, -2), (key2765, 6), (key2586, -2), (key2842, -2), (key2874, -2)]

theorem rawRowCheck14502 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form8 = rawRow14502 := by decide +kernel

def row14502 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

theorem rowCheck14502 : row14502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14502 := by decide +kernel

theorem rowEval14502 (x : Key → ℝ) : Integer.Sparse.eval row14502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14502, Integer.Sparse.eval_collectBalanced, rawRowCheck14502]

def rawRow14503 : Integer.Sparse Key := [(key2467, -2), (key2464, -2), (key2499, -2), (key2476, 6), (key2401, -2), (key2398, -2), (key2433, -2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2597, -2), (key2908, -2), (key2886, -2), (key2765, 6), (key2586, -2), (key2874, -2), (key2842, -2)]

theorem rawRowCheck14503 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form8 = rawRow14503 := by decide +kernel

def row14503 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

theorem rowCheck14503 : row14503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14503 := by decide +kernel

theorem rowEval14503 (x : Key → ℝ) : Integer.Sparse.eval row14503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14503, Integer.Sparse.eval_collectBalanced, rawRowCheck14503]

def rawRow14504 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2467, -2), (key2476, 6), (key2398, -2), (key2433, -2), (key2401, -2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2886, -2), (key2597, -2), (key2908, -2), (key2765, 6), (key2842, -2), (key2586, -2), (key2874, -2)]

theorem rawRowCheck14504 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form8 = rawRow14504 := by decide +kernel

def row14504 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

theorem rowCheck14504 : row14504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14504 := by decide +kernel

theorem rowEval14504 (x : Key → ℝ) : Integer.Sparse.eval row14504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14504, Integer.Sparse.eval_collectBalanced, rawRowCheck14504]

def rawRow14505 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2433, -2), (key2398, -2), (key2401, -2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2886, -2), (key2908, -2), (key2597, -2), (key2765, 6), (key2842, -2), (key2874, -2), (key2586, -2)]

theorem rawRowCheck14505 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form8 = rawRow14505 := by decide +kernel

def row14505 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

theorem rowCheck14505 : row14505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14505 := by decide +kernel

theorem rowEval14505 (x : Key → ℝ) : Integer.Sparse.eval row14505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14505, Integer.Sparse.eval_collectBalanced, rawRowCheck14505]

def rawRow14506 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2464, -2), (key2476, 6), (key2401, -2), (key2433, -2), (key2398, -2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2908, -2), (key2597, -2), (key2886, -2), (key2765, 6), (key2874, -2), (key2586, -2), (key2842, -2)]

theorem rawRowCheck14506 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form8 = rawRow14506 := by decide +kernel

def row14506 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

theorem rowCheck14506 : row14506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14506 := by decide +kernel

theorem rowEval14506 (x : Key → ℝ) : Integer.Sparse.eval row14506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14506, Integer.Sparse.eval_collectBalanced, rawRowCheck14506]

def rawRow14507 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2464, -2), (key2476, 6), (key2433, -2), (key2401, -2), (key2398, -2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2908, -2), (key2886, -2), (key2597, -2), (key2765, 6), (key2874, -2), (key2842, -2), (key2586, -2)]

theorem rawRowCheck14507 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form8 = rawRow14507 := by decide +kernel

def row14507 : Integer.Sparse Key := [(key2398, -2), (key2401, -2), (key2433, -2), (key2464, -2), (key2467, -2), (key2476, 6), (key2499, -2), (key2583, 2), (key2597, -2), (key2765, 6), (key2839, 2), (key2842, -2), (key2886, -2), (key2908, -2), (key2965, 2), (key2987, 2)]

theorem rowCheck14507 : row14507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14507 := by decide +kernel

theorem rowEval14507 (x : Key → ℝ) : Integer.Sparse.eval row14507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14507, Integer.Sparse.eval_collectBalanced, rawRowCheck14507]

def rawRow14508 : Integer.Sparse Key := [(key2464, -2), (key2476, -2), (key2499, -2), (key2467, 6), (key2464, -2), (key2476, -2), (key2499, -2), (key2370, 2), (key2386, 2), (key2762, 2), (key2908, 2), (key2928, 2), (key2987, 2), (key2586, -2), (key2765, -2), (key2874, -2), (key2842, 6), (key2586, -2), (key2765, -2), (key2874, -2)]

theorem rawRowCheck14508 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form8 = rawRow14508 := by decide +kernel

def row14508 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2928, 2), (key2987, 2)]

theorem rowCheck14508 : row14508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14508 := by decide +kernel

theorem rowEval14508 (x : Key → ℝ) : Integer.Sparse.eval row14508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14508, Integer.Sparse.eval_collectBalanced, rawRowCheck14508]

def rawRow14509 : Integer.Sparse Key := [(key2476, -2), (key2464, -2), (key2499, -2), (key2467, 6), (key2476, -2), (key2464, -2), (key2499, -2), (key2386, 2), (key2370, 2), (key2908, 2), (key2762, 2), (key2987, 2), (key2928, 2), (key2586, -2), (key2874, -2), (key2765, -2), (key2842, 6), (key2586, -2), (key2874, -2), (key2765, -2)]

theorem rawRowCheck14509 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form8 = rawRow14509 := by decide +kernel

def row14509 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2928, 2), (key2987, 2)]

theorem rowCheck14509 : row14509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14509 := by decide +kernel

theorem rowEval14509 (x : Key → ℝ) : Integer.Sparse.eval row14509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14509, Integer.Sparse.eval_collectBalanced, rawRowCheck14509]

def rawRow14510 : Integer.Sparse Key := [(key2464, -2), (key2499, -2), (key2476, -2), (key2467, 6), (key2464, -2), (key2499, -2), (key2476, -2), (key2398, 2), (key2433, 2), (key2583, 2), (key2987, 2), (key2597, 2), (key2908, 2), (key2765, -2), (key2586, -2), (key2874, -2), (key2842, 6), (key2765, -2), (key2586, -2), (key2874, -2)]

theorem rawRowCheck14510 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form8 = rawRow14510 := by decide +kernel

def row14510 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, -4), (key2597, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2987, 2)]

theorem rowCheck14510 : row14510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14510 := by decide +kernel

theorem rowEval14510 (x : Key → ℝ) : Integer.Sparse.eval row14510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14510, Integer.Sparse.eval_collectBalanced, rawRowCheck14510]

def rawRow14511 : Integer.Sparse Key := [(key2499, -2), (key2464, -2), (key2476, -2), (key2467, 6), (key2499, -2), (key2464, -2), (key2476, -2), (key2433, 2), (key2398, 2), (key2987, 2), (key2583, 2), (key2908, 2), (key2597, 2), (key2765, -2), (key2874, -2), (key2586, -2), (key2842, 6), (key2765, -2), (key2874, -2), (key2586, -2)]

theorem rawRowCheck14511 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form8 = rawRow14511 := by decide +kernel

def row14511 : Integer.Sparse Key := [(key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2583, 2), (key2586, -4), (key2597, 2), (key2765, -4), (key2842, 6), (key2874, -4), (key2908, 2), (key2987, 2)]

theorem rowCheck14511 : row14511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14511 := by decide +kernel

theorem rowEval14511 (x : Key → ℝ) : Integer.Sparse.eval row14511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14511, Integer.Sparse.eval_collectBalanced, rawRowCheck14511]

def rawRow14512 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2464, -2), (key2467, 6), (key2476, -2), (key2499, -2), (key2464, -2), (key2540, 2), (key2551, 2), (key2386, 2), (key2433, 2), (key2370, 2), (key2762, 2), (key2874, -2), (key2586, -2), (key2765, -2), (key2842, 6), (key2874, -2), (key2586, -2), (key2765, -2)]

theorem rawRowCheck14512 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form8 = rawRow14512 := by decide +kernel

def row14512 : Integer.Sparse Key := [(key2370, 2), (key2386, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2586, -4), (key2762, 2), (key2765, -4), (key2842, 6), (key2874, -4)]

theorem rowCheck14512 : row14512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14512 := by decide +kernel

theorem rowEval14512 (x : Key → ℝ) : Integer.Sparse.eval row14512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14512, Integer.Sparse.eval_collectBalanced, rawRowCheck14512]

def rawRow14513 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2464, -2), (key2467, 6), (key2499, -2), (key2476, -2), (key2464, -2), (key2551, 2), (key2540, 2), (key2433, 2), (key2386, 2), (key2398, 2), (key2583, 2), (key2874, -2), (key2765, -2), (key2586, -2), (key2842, 6), (key2874, -2), (key2765, -2), (key2586, -2)]

theorem rawRowCheck14513 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form8 = rawRow14513 := by decide +kernel

def row14513 : Integer.Sparse Key := [(key2386, 2), (key2398, 2), (key2433, 2), (key2464, -4), (key2467, 6), (key2476, -4), (key2499, -4), (key2540, 2), (key2551, 2), (key2583, 2), (key2586, -4), (key2765, -4), (key2842, 6), (key2874, -4)]

theorem rowCheck14513 : row14513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14513 := by decide +kernel

theorem rowEval14513 (x : Key → ℝ) : Integer.Sparse.eval row14513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14513, Integer.Sparse.eval_collectBalanced, rawRowCheck14513]

def rawRow14514 : Integer.Sparse Key := [(key2467, -2), (key2476, -2), (key2499, -2), (key2464, 6), (key2534, -2), (key2540, -2), (key2551, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2874, 6), (key2586, -2), (key2765, -2), (key2842, -2)]

theorem rawRowCheck14514 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form8 = rawRow14514 := by decide +kernel

def row14514 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

theorem rowCheck14514 : row14514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14514 := by decide +kernel

theorem rowEval14514 (x : Key → ℝ) : Integer.Sparse.eval row14514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14514, Integer.Sparse.eval_collectBalanced, rawRowCheck14514]

def rawRow14515 : Integer.Sparse Key := [(key2476, -2), (key2467, -2), (key2499, -2), (key2464, 6), (key2540, -2), (key2534, -2), (key2551, -2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2874, 6), (key2586, -2), (key2842, -2), (key2765, -2)]

theorem rawRowCheck14515 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form8 = rawRow14515 := by decide +kernel

def row14515 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

theorem rowCheck14515 : row14515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14515 := by decide +kernel

theorem rowEval14515 (x : Key → ℝ) : Integer.Sparse.eval row14515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14515, Integer.Sparse.eval_collectBalanced, rawRowCheck14515]

def rawRow14516 : Integer.Sparse Key := [(key2467, -2), (key2499, -2), (key2476, -2), (key2464, 6), (key2534, -2), (key2551, -2), (key2540, -2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2874, 6), (key2765, -2), (key2586, -2), (key2842, -2)]

theorem rawRowCheck14516 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form8 = rawRow14516 := by decide +kernel

def row14516 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

theorem rowCheck14516 : row14516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14516 := by decide +kernel

theorem rowEval14516 (x : Key → ℝ) : Integer.Sparse.eval row14516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14516, Integer.Sparse.eval_collectBalanced, rawRowCheck14516]

def rawRow14517 : Integer.Sparse Key := [(key2499, -2), (key2467, -2), (key2476, -2), (key2464, 6), (key2551, -2), (key2534, -2), (key2540, -2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2874, 6), (key2765, -2), (key2842, -2), (key2586, -2)]

theorem rawRowCheck14517 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form8 = rawRow14517 := by decide +kernel

def row14517 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 6), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2839, -2), (key2842, -2), (key2874, 6)]

theorem rowCheck14517 : row14517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14517 := by decide +kernel

theorem rowEval14517 (x : Key → ℝ) : Integer.Sparse.eval row14517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14517, Integer.Sparse.eval_collectBalanced, rawRowCheck14517]

def rawRow14518 : Integer.Sparse Key := [(key2476, -2), (key2499, -2), (key2467, -2), (key2464, 6), (key2540, -2), (key2551, -2), (key2534, -2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2874, 6), (key2842, -2), (key2586, -2), (key2765, -2)]

theorem rawRowCheck14518 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form8 = rawRow14518 := by decide +kernel

def row14518 : Integer.Sparse Key := [(key2370, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2433, 2), (key2464, 4), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2586, -2), (key2762, -2), (key2765, -2), (key2842, -2), (key2874, 6)]

theorem rowCheck14518 : row14518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14518 := by decide +kernel

theorem rowEval14518 (x : Key → ℝ) : Integer.Sparse.eval row14518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14518, Integer.Sparse.eval_collectBalanced, rawRowCheck14518]

def rawRow14519 : Integer.Sparse Key := [(key2499, -2), (key2476, -2), (key2467, -2), (key2464, 6), (key2551, -2), (key2540, -2), (key2534, -2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2874, 6), (key2842, -2), (key2765, -2), (key2586, -2)]

theorem rawRowCheck14519 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form8 = rawRow14519 := by decide +kernel

def row14519 : Integer.Sparse Key := [(key2373, 2), (key2386, 2), (key2398, -2), (key2401, 2), (key2433, 2), (key2464, 4), (key2467, -2), (key2534, -2), (key2540, -2), (key2551, -2), (key2583, -2), (key2586, -2), (key2765, -2), (key2842, -2), (key2874, 6)]

theorem rowCheck14519 : row14519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14519 := by decide +kernel

theorem rowEval14519 (x : Key → ℝ) : Integer.Sparse.eval row14519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14519, Integer.Sparse.eval_collectBalanced, rawRowCheck14519]

def rawRow14520 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2551, -2), (key2540, 6), (key2401, -2), (key2401, -2), (key2433, -2), (key2373, 2), (key2373, 2), (key2467, 2), (key2467, 2), (key2499, 2), (key2499, 2), (key2386, -2), (key2476, -2), (key2476, -2), (key2398, 6), (key2583, -2), (key2839, -2), (key2839, -2)]

theorem rawRowCheck14520 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form8 = rawRow14520 := by decide +kernel

def row14520 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

theorem rowCheck14520 : row14520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14520 := by decide +kernel

theorem rowEval14520 (x : Key → ℝ) : Integer.Sparse.eval row14520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14520, Integer.Sparse.eval_collectBalanced, rawRowCheck14520]

def rawRow14521 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2534, -2), (key2540, 6), (key2401, -2), (key2433, -2), (key2401, -2), (key2467, 2), (key2499, 2), (key2373, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2476, -2), (key2386, -2), (key2476, -2), (key2398, 6), (key2839, -2), (key2583, -2), (key2839, -2)]

theorem rawRowCheck14521 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form8 = rawRow14521 := by decide +kernel

def row14521 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

theorem rowCheck14521 : row14521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14521 := by decide +kernel

theorem rowEval14521 (x : Key → ℝ) : Integer.Sparse.eval row14521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14521, Integer.Sparse.eval_collectBalanced, rawRowCheck14521]

def rawRow14522 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2534, -2), (key2540, 6), (key2433, -2), (key2401, -2), (key2401, -2), (key2499, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2373, 2), (key2476, -2), (key2476, -2), (key2386, -2), (key2398, 6), (key2839, -2), (key2839, -2), (key2583, -2)]

theorem rawRowCheck14522 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form8 = rawRow14522 := by decide +kernel

def row14522 : Integer.Sparse Key := [(key2373, 4), (key2386, -2), (key2398, 6), (key2401, -4), (key2433, -2), (key2467, 4), (key2476, -4), (key2499, 4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, -2), (key2839, -4)]

theorem rowCheck14522 : row14522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14522 := by decide +kernel

theorem rowEval14522 (x : Key → ℝ) : Integer.Sparse.eval row14522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14522, Integer.Sparse.eval_collectBalanced, rawRowCheck14522]

def rawRow14523 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2551, -2), (key2534, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2373, -2), (key2401, -2), (key2467, -2), (key2464, 6), (key2370, -2), (key2762, -2), (key2839, -2)]

theorem rawRowCheck14523 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form8 = rawRow14523 := by decide +kernel

def row14523 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2), (key2839, -2)]

theorem rowCheck14523 : row14523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14523 := by decide +kernel

theorem rowEval14523 (x : Key → ℝ) : Integer.Sparse.eval row14523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14523, Integer.Sparse.eval_collectBalanced, rawRowCheck14523]

def rawRow14524 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2551, -2), (key2534, 6), (key2476, -2), (key2467, -2), (key2499, -2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2373, -2), (key2467, -2), (key2401, -2), (key2464, 6), (key2370, -2), (key2839, -2), (key2762, -2)]

theorem rawRowCheck14524 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form8 = rawRow14524 := by decide +kernel

def row14524 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2), (key2839, -2)]

theorem rowCheck14524 : row14524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14524 := by decide +kernel

theorem rowEval14524 (x : Key → ℝ) : Integer.Sparse.eval row14524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14524, Integer.Sparse.eval_collectBalanced, rawRowCheck14524]

def rawRow14525 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2540, -2), (key2534, 6), (key2467, -2), (key2499, -2), (key2476, -2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2401, -2), (key2373, -2), (key2467, -2), (key2464, 6), (key2398, -2), (key2583, -2), (key2839, -2)]

theorem rawRowCheck14525 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form8 = rawRow14525 := by decide +kernel

def row14525 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2), (key2839, -2)]

theorem rowCheck14525 : row14525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14525 := by decide +kernel

theorem rowEval14525 (x : Key → ℝ) : Integer.Sparse.eval row14525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck14525, Integer.Sparse.eval_collectBalanced, rawRowCheck14525]

def rawRow14526 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2540, -2), (key2534, 6), (key2499, -2), (key2467, -2), (key2476, -2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2401, -2), (key2467, -2), (key2373, -2), (key2464, 6), (key2398, -2), (key2839, -2), (key2583, -2)]

theorem rawRowCheck14526 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form8 = rawRow14526 := by decide +kernel

def row14526 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 6), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2), (key2839, -2)]

theorem rowCheck14526 : row14526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14526 := by decide +kernel

theorem rowEval14526 (x : Key → ℝ) : Integer.Sparse.eval row14526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14526, Integer.Sparse.eval_collectBalanced, rawRowCheck14526]

def rawRow14527 : Integer.Sparse Key := [(key2540, -2), (key2551, -2), (key2534, -2), (key2534, 6), (key2476, -2), (key2499, -2), (key2467, -2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2467, -2), (key2373, -2), (key2401, -2), (key2464, 6), (key2464, -2), (key2370, -2), (key2762, -2)]

theorem rawRowCheck14527 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form8 = rawRow14527 := by decide +kernel

def row14527 : Integer.Sparse Key := [(key2370, -2), (key2386, 2), (key2433, 2), (key2464, 4), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, -2)]

theorem rowCheck14527 : row14527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14527 := by decide +kernel

theorem rowEval14527 (x : Key → ℝ) : Integer.Sparse.eval row14527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck14527, Integer.Sparse.eval_collectBalanced, rawRowCheck14527]

def rawRow14528 : Integer.Sparse Key := [(key2551, -2), (key2540, -2), (key2534, -2), (key2534, 6), (key2499, -2), (key2476, -2), (key2467, -2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2467, -2), (key2401, -2), (key2373, -2), (key2464, 6), (key2464, -2), (key2398, -2), (key2583, -2)]

theorem rawRowCheck14528 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form8 = rawRow14528 := by decide +kernel

def row14528 : Integer.Sparse Key := [(key2386, 2), (key2398, -2), (key2433, 2), (key2464, 4), (key2467, -4), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, -2)]

theorem rowCheck14528 : row14528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14528 := by decide +kernel

theorem rowEval14528 (x : Key → ℝ) : Integer.Sparse.eval row14528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck14528, Integer.Sparse.eval_collectBalanced, rawRowCheck14528]

def rawRow14529 : Integer.Sparse Key := [(key2011, 4), (key2125, 4), (key2135, 4), (key2011, -4), (key2020, -4), (key2135, -4), (key2040, -4), (key2048, -4), (key2220, -4), (key2048, 12)]

theorem rawRowCheck14529 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form9 = rawRow14529 := by decide +kernel

def row14529 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14529 : row14529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14529 := by decide +kernel

theorem rowEval14529 (x : Key → ℝ) : Integer.Sparse.eval row14529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14529, Integer.Sparse.eval_collectBalanced, rawRowCheck14529]

def rawRow14530 : Integer.Sparse Key := [(key2011, 4), (key2135, 4), (key2125, 4), (key2020, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2040, -4), (key2220, -4), (key2048, 12)]

theorem rawRowCheck14530 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form9 = rawRow14530 := by decide +kernel

def row14530 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14530 : row14530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14530 := by decide +kernel

theorem rowEval14530 (x : Key → ℝ) : Integer.Sparse.eval row14530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14530, Integer.Sparse.eval_collectBalanced, rawRowCheck14530]

def rawRow14531 : Integer.Sparse Key := [(key2125, 4), (key2011, 4), (key2135, 4), (key2011, -4), (key2135, -4), (key2020, -4), (key2040, -4), (key2220, -4), (key2048, -4), (key2048, 12)]

theorem rawRowCheck14531 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form9 = rawRow14531 := by decide +kernel

def row14531 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14531 : row14531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14531 := by decide +kernel

theorem rowEval14531 (x : Key → ℝ) : Integer.Sparse.eval row14531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14531, Integer.Sparse.eval_collectBalanced, rawRowCheck14531]

def rawRow14532 : Integer.Sparse Key := [(key2125, 4), (key2135, 4), (key2011, 4), (key2135, -4), (key2011, -4), (key2020, -4), (key2220, -4), (key2040, -4), (key2048, -4), (key2048, 12)]

theorem rawRowCheck14532 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form9 = rawRow14532 := by decide +kernel

def row14532 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14532 : row14532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14532 := by decide +kernel

theorem rowEval14532 (x : Key → ℝ) : Integer.Sparse.eval row14532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14532, Integer.Sparse.eval_collectBalanced, rawRowCheck14532]

def rawRow14533 : Integer.Sparse Key := [(key2135, 4), (key2011, 4), (key2125, 4), (key2020, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2220, -4), (key2040, -4), (key2048, 12)]

theorem rawRowCheck14533 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form9 = rawRow14533 := by decide +kernel

def row14533 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14533 : row14533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14533 := by decide +kernel

theorem rowEval14533 (x : Key → ℝ) : Integer.Sparse.eval row14533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14533, Integer.Sparse.eval_collectBalanced, rawRowCheck14533]

def rawRow14534 : Integer.Sparse Key := [(key2135, 4), (key2125, 4), (key2011, 4), (key2135, -4), (key2020, -4), (key2011, -4), (key2220, -4), (key2048, -4), (key2040, -4), (key2048, 12)]

theorem rawRowCheck14534 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form9 = rawRow14534 := by decide +kernel

def row14534 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14534 : row14534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14534 := by decide +kernel

theorem rowEval14534 (x : Key → ℝ) : Integer.Sparse.eval row14534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14534, Integer.Sparse.eval_collectBalanced, rawRowCheck14534]

def rawRow14535 : Integer.Sparse Key := [(key2020, 4), (key2135, 4), (key2135, 4), (key2011, -4), (key2011, -4), (key2125, -4), (key2048, -4), (key2048, -4), (key2220, -4), (key2040, 12)]

theorem rawRowCheck14535 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14535 := by decide +kernel

def row14535 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck14535 : row14535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14535 := by decide +kernel

theorem rowEval14535 (x : Key → ℝ) : Integer.Sparse.eval row14535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14535, Integer.Sparse.eval_collectBalanced, rawRowCheck14535]

def rawRow14536 : Integer.Sparse Key := [(key2135, 4), (key2020, 4), (key2135, 4), (key2011, -4), (key2125, -4), (key2011, -4), (key2048, -4), (key2220, -4), (key2048, -4), (key2040, 12)]

theorem rawRowCheck14536 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14536 := by decide +kernel

def row14536 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck14536 : row14536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14536 := by decide +kernel

theorem rowEval14536 (x : Key → ℝ) : Integer.Sparse.eval row14536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14536, Integer.Sparse.eval_collectBalanced, rawRowCheck14536]

def rawRow14537 : Integer.Sparse Key := [(key2135, 4), (key2135, 4), (key2020, 4), (key2125, -4), (key2011, -4), (key2011, -4), (key2220, -4), (key2048, -4), (key2048, -4), (key2040, 12)]

theorem rawRowCheck14537 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14537 := by decide +kernel

def row14537 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck14537 : row14537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14537 := by decide +kernel

theorem rowEval14537 (x : Key → ℝ) : Integer.Sparse.eval row14537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14537, Integer.Sparse.eval_collectBalanced, rawRowCheck14537]

def rawRow14538 : Integer.Sparse Key := [(key2011, 4), (key2125, 4), (key2135, 4), (key2040, -4), (key2048, -4), (key2220, -4), (key2011, -4), (key2020, -4), (key2135, -4), (key2048, 12)]

theorem rawRowCheck14538 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form9 = rawRow14538 := by decide +kernel

def row14538 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14538 : row14538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14538 := by decide +kernel

theorem rowEval14538 (x : Key → ℝ) : Integer.Sparse.eval row14538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14538, Integer.Sparse.eval_collectBalanced, rawRowCheck14538]

def rawRow14539 : Integer.Sparse Key := [(key2011, 4), (key2135, 4), (key2125, 4), (key2048, -4), (key2040, -4), (key2220, -4), (key2020, -4), (key2011, -4), (key2135, -4), (key2048, 12)]

theorem rawRowCheck14539 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form9 = rawRow14539 := by decide +kernel

def row14539 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14539 : row14539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14539 := by decide +kernel

theorem rowEval14539 (x : Key → ℝ) : Integer.Sparse.eval row14539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14539, Integer.Sparse.eval_collectBalanced, rawRowCheck14539]

def rawRow14540 : Integer.Sparse Key := [(key2125, 4), (key2011, 4), (key2135, 4), (key2040, -4), (key2220, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2020, -4), (key2048, 12)]

theorem rawRowCheck14540 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form9 = rawRow14540 := by decide +kernel

def row14540 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14540 : row14540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14540 := by decide +kernel

theorem rowEval14540 (x : Key → ℝ) : Integer.Sparse.eval row14540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14540, Integer.Sparse.eval_collectBalanced, rawRowCheck14540]

def rawRow14541 : Integer.Sparse Key := [(key2125, 4), (key2135, 4), (key2011, 4), (key2220, -4), (key2040, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2020, -4), (key2048, 12)]

theorem rawRowCheck14541 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form9 = rawRow14541 := by decide +kernel

def row14541 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14541 : row14541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14541 := by decide +kernel

theorem rowEval14541 (x : Key → ℝ) : Integer.Sparse.eval row14541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14541, Integer.Sparse.eval_collectBalanced, rawRowCheck14541]

def rawRow14542 : Integer.Sparse Key := [(key2135, 4), (key2011, 4), (key2125, 4), (key2048, -4), (key2220, -4), (key2040, -4), (key2020, -4), (key2135, -4), (key2011, -4), (key2048, 12)]

theorem rawRowCheck14542 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form9 = rawRow14542 := by decide +kernel

def row14542 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14542 : row14542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14542 := by decide +kernel

theorem rowEval14542 (x : Key → ℝ) : Integer.Sparse.eval row14542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14542, Integer.Sparse.eval_collectBalanced, rawRowCheck14542]

def rawRow14543 : Integer.Sparse Key := [(key2135, 4), (key2125, 4), (key2011, 4), (key2220, -4), (key2048, -4), (key2040, -4), (key2135, -4), (key2020, -4), (key2011, -4), (key2048, 12)]

theorem rawRowCheck14543 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form9 = rawRow14543 := by decide +kernel

def row14543 : Integer.Sparse Key := [(key2020, -4), (key2040, -4), (key2048, 8), (key2125, 4), (key2220, -4)]

theorem rowCheck14543 : row14543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14543 := by decide +kernel

theorem rowEval14543 (x : Key → ℝ) : Integer.Sparse.eval row14543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14543, Integer.Sparse.eval_collectBalanced, rawRowCheck14543]

def rawRow14544 : Integer.Sparse Key := [(key2040, 4), (key2125, 4), (key2220, 4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2020, 12)]

theorem rawRowCheck14544 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form9 = rawRow14544 := by decide +kernel

def row14544 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

theorem rowCheck14544 : row14544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14544 := by decide +kernel

theorem rowEval14544 (x : Key → ℝ) : Integer.Sparse.eval row14544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14544, Integer.Sparse.eval_collectBalanced, rawRowCheck14544]

def rawRow14545 : Integer.Sparse Key := [(key2040, 4), (key2220, 4), (key2125, 4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2020, 12)]

theorem rawRowCheck14545 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form9 = rawRow14545 := by decide +kernel

def row14545 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

theorem rowCheck14545 : row14545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14545 := by decide +kernel

theorem rowEval14545 (x : Key → ℝ) : Integer.Sparse.eval row14545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14545, Integer.Sparse.eval_collectBalanced, rawRowCheck14545]

def rawRow14546 : Integer.Sparse Key := [(key2125, 4), (key2040, 4), (key2220, 4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2020, 12)]

theorem rawRowCheck14546 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form9 = rawRow14546 := by decide +kernel

def row14546 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

theorem rowCheck14546 : row14546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14546 := by decide +kernel

theorem rowEval14546 (x : Key → ℝ) : Integer.Sparse.eval row14546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14546, Integer.Sparse.eval_collectBalanced, rawRowCheck14546]

def rawRow14547 : Integer.Sparse Key := [(key2125, 4), (key2220, 4), (key2040, 4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2020, 12)]

theorem rawRowCheck14547 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form9 = rawRow14547 := by decide +kernel

def row14547 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

theorem rowCheck14547 : row14547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14547 := by decide +kernel

theorem rowEval14547 (x : Key → ℝ) : Integer.Sparse.eval row14547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14547, Integer.Sparse.eval_collectBalanced, rawRowCheck14547]

def rawRow14548 : Integer.Sparse Key := [(key2220, 4), (key2040, 4), (key2125, 4), (key2048, -4), (key2135, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2020, 12)]

theorem rawRowCheck14548 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form9 = rawRow14548 := by decide +kernel

def row14548 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

theorem rowCheck14548 : row14548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14548 := by decide +kernel

theorem rowEval14548 (x : Key → ℝ) : Integer.Sparse.eval row14548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14548, Integer.Sparse.eval_collectBalanced, rawRowCheck14548]

def rawRow14549 : Integer.Sparse Key := [(key2220, 4), (key2125, 4), (key2040, 4), (key2135, -4), (key2048, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2020, 12)]

theorem rawRowCheck14549 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form9 = rawRow14549 := by decide +kernel

def row14549 : Integer.Sparse Key := [(key2011, -8), (key2020, 12), (key2040, 4), (key2048, -8), (key2125, 4), (key2135, -8), (key2220, 4)]

theorem rowCheck14549 : row14549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14549 := by decide +kernel

theorem rowEval14549 (x : Key → ℝ) : Integer.Sparse.eval row14549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14549, Integer.Sparse.eval_collectBalanced, rawRowCheck14549]

def rawRow14550 : Integer.Sparse Key := [(key2048, 4), (key2135, 4), (key2220, 4), (key2011, -4), (key2040, -4), (key2125, -4), (key2020, -4), (key2048, -4), (key2135, -4), (key2011, 12)]

theorem rawRowCheck14550 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form9 = rawRow14550 := by decide +kernel

def row14550 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14550 : row14550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14550 := by decide +kernel

theorem rowEval14550 (x : Key → ℝ) : Integer.Sparse.eval row14550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14550, Integer.Sparse.eval_collectBalanced, rawRowCheck14550]

def rawRow14551 : Integer.Sparse Key := [(key2048, 4), (key2220, 4), (key2135, 4), (key2040, -4), (key2011, -4), (key2125, -4), (key2048, -4), (key2020, -4), (key2135, -4), (key2011, 12)]

theorem rawRowCheck14551 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form9 = rawRow14551 := by decide +kernel

def row14551 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14551 : row14551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14551 := by decide +kernel

theorem rowEval14551 (x : Key → ℝ) : Integer.Sparse.eval row14551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14551, Integer.Sparse.eval_collectBalanced, rawRowCheck14551]

def rawRow14552 : Integer.Sparse Key := [(key2135, 4), (key2048, 4), (key2220, 4), (key2011, -4), (key2125, -4), (key2040, -4), (key2020, -4), (key2135, -4), (key2048, -4), (key2011, 12)]

theorem rawRowCheck14552 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form9 = rawRow14552 := by decide +kernel

def row14552 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14552 : row14552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14552 := by decide +kernel

theorem rowEval14552 (x : Key → ℝ) : Integer.Sparse.eval row14552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14552, Integer.Sparse.eval_collectBalanced, rawRowCheck14552]

def rawRow14553 : Integer.Sparse Key := [(key2135, 4), (key2220, 4), (key2048, 4), (key2125, -4), (key2011, -4), (key2040, -4), (key2135, -4), (key2020, -4), (key2048, -4), (key2011, 12)]

theorem rawRowCheck14553 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form9 = rawRow14553 := by decide +kernel

def row14553 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14553 : row14553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14553 := by decide +kernel

theorem rowEval14553 (x : Key → ℝ) : Integer.Sparse.eval row14553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14553, Integer.Sparse.eval_collectBalanced, rawRowCheck14553]

def rawRow14554 : Integer.Sparse Key := [(key2220, 4), (key2048, 4), (key2135, 4), (key2040, -4), (key2125, -4), (key2011, -4), (key2048, -4), (key2135, -4), (key2020, -4), (key2011, 12)]

theorem rawRowCheck14554 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form9 = rawRow14554 := by decide +kernel

def row14554 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14554 : row14554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14554 := by decide +kernel

theorem rowEval14554 (x : Key → ℝ) : Integer.Sparse.eval row14554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14554, Integer.Sparse.eval_collectBalanced, rawRowCheck14554]

def rawRow14555 : Integer.Sparse Key := [(key2220, 4), (key2135, 4), (key2048, 4), (key2125, -4), (key2040, -4), (key2011, -4), (key2135, -4), (key2048, -4), (key2020, -4), (key2011, 12)]

theorem rawRowCheck14555 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form9 = rawRow14555 := by decide +kernel

def row14555 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14555 : row14555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14555 := by decide +kernel

theorem rowEval14555 (x : Key → ℝ) : Integer.Sparse.eval row14555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14555, Integer.Sparse.eval_collectBalanced, rawRowCheck14555]

def rawRow14556 : Integer.Sparse Key := [(key2020, 4), (key2135, 4), (key2135, 4), (key2048, -4), (key2048, -4), (key2220, -4), (key2011, -4), (key2011, -4), (key2125, -4), (key2040, 12)]

theorem rawRowCheck14556 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form9 = rawRow14556 := by decide +kernel

def row14556 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck14556 : row14556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14556 := by decide +kernel

theorem rowEval14556 (x : Key → ℝ) : Integer.Sparse.eval row14556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14556, Integer.Sparse.eval_collectBalanced, rawRowCheck14556]

def rawRow14557 : Integer.Sparse Key := [(key2135, 4), (key2020, 4), (key2135, 4), (key2048, -4), (key2220, -4), (key2048, -4), (key2011, -4), (key2125, -4), (key2011, -4), (key2040, 12)]

theorem rawRowCheck14557 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form9 = rawRow14557 := by decide +kernel

def row14557 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck14557 : row14557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14557 := by decide +kernel

theorem rowEval14557 (x : Key → ℝ) : Integer.Sparse.eval row14557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14557, Integer.Sparse.eval_collectBalanced, rawRowCheck14557]

def rawRow14558 : Integer.Sparse Key := [(key2135, 4), (key2135, 4), (key2020, 4), (key2220, -4), (key2048, -4), (key2048, -4), (key2125, -4), (key2011, -4), (key2011, -4), (key2040, 12)]

theorem rawRowCheck14558 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form9 = rawRow14558 := by decide +kernel

def row14558 : Integer.Sparse Key := [(key2011, -8), (key2020, 4), (key2040, 12), (key2048, -8), (key2125, -4), (key2135, 8), (key2220, -4)]

theorem rowCheck14558 : row14558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14558 := by decide +kernel

theorem rowEval14558 (x : Key → ℝ) : Integer.Sparse.eval row14558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14558, Integer.Sparse.eval_collectBalanced, rawRowCheck14558]

def rawRow14559 : Integer.Sparse Key := [(key2048, 4), (key2135, 4), (key2220, 4), (key2020, -4), (key2048, -4), (key2135, -4), (key2011, -4), (key2040, -4), (key2125, -4), (key2011, 12)]

theorem rawRowCheck14559 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form9 = rawRow14559 := by decide +kernel

def row14559 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14559 : row14559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14559 := by decide +kernel

theorem rowEval14559 (x : Key → ℝ) : Integer.Sparse.eval row14559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14559, Integer.Sparse.eval_collectBalanced, rawRowCheck14559]

def rawRow14560 : Integer.Sparse Key := [(key2048, 4), (key2220, 4), (key2135, 4), (key2048, -4), (key2020, -4), (key2135, -4), (key2040, -4), (key2011, -4), (key2125, -4), (key2011, 12)]

theorem rawRowCheck14560 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form9 = rawRow14560 := by decide +kernel

def row14560 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14560 : row14560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14560 := by decide +kernel

theorem rowEval14560 (x : Key → ℝ) : Integer.Sparse.eval row14560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14560, Integer.Sparse.eval_collectBalanced, rawRowCheck14560]

def rawRow14561 : Integer.Sparse Key := [(key2135, 4), (key2048, 4), (key2220, 4), (key2020, -4), (key2135, -4), (key2048, -4), (key2011, -4), (key2125, -4), (key2040, -4), (key2011, 12)]

theorem rawRowCheck14561 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form9 = rawRow14561 := by decide +kernel

def row14561 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14561 : row14561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14561 := by decide +kernel

theorem rowEval14561 (x : Key → ℝ) : Integer.Sparse.eval row14561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck14561, Integer.Sparse.eval_collectBalanced, rawRowCheck14561]

def rawRow14562 : Integer.Sparse Key := [(key2135, 4), (key2220, 4), (key2048, 4), (key2135, -4), (key2020, -4), (key2048, -4), (key2125, -4), (key2011, -4), (key2040, -4), (key2011, 12)]

theorem rawRowCheck14562 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form9 = rawRow14562 := by decide +kernel

def row14562 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14562 : row14562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14562 := by decide +kernel

theorem rowEval14562 (x : Key → ℝ) : Integer.Sparse.eval row14562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14562, Integer.Sparse.eval_collectBalanced, rawRowCheck14562]

def rawRow14563 : Integer.Sparse Key := [(key2220, 4), (key2048, 4), (key2135, 4), (key2048, -4), (key2135, -4), (key2020, -4), (key2040, -4), (key2125, -4), (key2011, -4), (key2011, 12)]

theorem rawRowCheck14563 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form9 = rawRow14563 := by decide +kernel

def row14563 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14563 : row14563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14563 := by decide +kernel

theorem rowEval14563 (x : Key → ℝ) : Integer.Sparse.eval row14563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck14563, Integer.Sparse.eval_collectBalanced, rawRowCheck14563]

def rawRow14564 : Integer.Sparse Key := [(key2220, 4), (key2135, 4), (key2048, 4), (key2135, -4), (key2048, -4), (key2020, -4), (key2125, -4), (key2040, -4), (key2011, -4), (key2011, 12)]

theorem rawRowCheck14564 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form9 = rawRow14564 := by decide +kernel

def row14564 : Integer.Sparse Key := [(key2011, 8), (key2020, -4), (key2040, -4), (key2125, -4), (key2220, 4)]

theorem rowCheck14564 : row14564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14564 := by decide +kernel

theorem rowEval14564 (x : Key → ℝ) : Integer.Sparse.eval row14564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck14564, Integer.Sparse.eval_collectBalanced, rawRowCheck14564]

def rawRow14565 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2624, -1), (key2627, -1), (key2851, -1), (key2866, -1), (key2971, -1), (key2981, -1), (key2624, 2), (key2636, 2), (key2698, 2), (key2722, 2), (key2974, 2), (key2981, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1), (key2645, 2), (key2892, 2), (key2902, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1)]

theorem rawRowCheck14565 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form10 = rawRow14565 := by decide +kernel

def row14565 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

theorem rowCheck14565 : row14565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14565 := by decide +kernel

theorem rowEval14565 (x : Key → ℝ) : Integer.Sparse.eval row14565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14565, Integer.Sparse.eval_collectBalanced, rawRowCheck14565]

def rawRow14566 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2627, -1), (key2624, -1), (key2866, -1), (key2851, -1), (key2981, -1), (key2971, -1), (key2636, 2), (key2624, 2), (key2722, 2), (key2698, 2), (key2981, 2), (key2974, 2), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1), (key2645, 2), (key2902, 2), (key2892, 2), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1)]

theorem rawRowCheck14566 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form10 = rawRow14566 := by decide +kernel

def row14566 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

theorem rowCheck14566 : row14566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14566 := by decide +kernel

theorem rowEval14566 (x : Key → ℝ) : Integer.Sparse.eval row14566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14566, Integer.Sparse.eval_collectBalanced, rawRowCheck14566]

def rawRow14567 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2851, -1), (key2971, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2698, 2), (key2974, 2), (key2624, 2), (key2981, 2), (key2636, 2), (key2722, 2), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2892, 2), (key2645, 2), (key2902, 2), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1)]

theorem rawRowCheck14567 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form10 = rawRow14567 := by decide +kernel

def row14567 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

theorem rowCheck14567 : row14567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14567 := by decide +kernel

theorem rowEval14567 (x : Key → ℝ) : Integer.Sparse.eval row14567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14567, Integer.Sparse.eval_collectBalanced, rawRowCheck14567]

def rawRow14568 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2971, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2866, -1), (key2627, -1), (key2974, 2), (key2698, 2), (key2981, 2), (key2624, 2), (key2722, 2), (key2636, 2), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1), (key2892, 2), (key2902, 2), (key2645, 2), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1)]

theorem rawRowCheck14568 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form10 = rawRow14568 := by decide +kernel

def row14568 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

theorem rowCheck14568 : row14568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14568 := by decide +kernel

theorem rowEval14568 (x : Key → ℝ) : Integer.Sparse.eval row14568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14568, Integer.Sparse.eval_collectBalanced, rawRowCheck14568]

def rawRow14569 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2866, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2624, -1), (key2851, -1), (key2722, 2), (key2981, 2), (key2636, 2), (key2974, 2), (key2624, 2), (key2698, 2), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1), (key2902, 2), (key2645, 2), (key2892, 2), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1)]

theorem rawRowCheck14569 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form10 = rawRow14569 := by decide +kernel

def row14569 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

theorem rowCheck14569 : row14569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14569 := by decide +kernel

theorem rowEval14569 (x : Key → ℝ) : Integer.Sparse.eval row14569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14569, Integer.Sparse.eval_collectBalanced, rawRowCheck14569]

def rawRow14570 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2981, -1), (key2866, -1), (key2971, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2981, 2), (key2722, 2), (key2974, 2), (key2636, 2), (key2698, 2), (key2624, 2), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2902, 2), (key2892, 2), (key2645, 2), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1)]

theorem rawRowCheck14570 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form10 = rawRow14570 := by decide +kernel

def row14570 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, 2), (key2895, -1), (key2902, 1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 2), (key2981, 1)]

theorem rowCheck14570 : row14570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14570 := by decide +kernel

theorem rowEval14570 (x : Key → ℝ) : Integer.Sparse.eval row14570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14570, Integer.Sparse.eval_collectBalanced, rawRowCheck14570]

def rawRow14571 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2636, -1), (key2636, -1), (key2856, -1), (key2856, -1), (key2974, -1), (key2974, -1), (key2627, 2), (key2627, 2), (key2701, 2), (key2701, 2), (key2971, 2), (key2971, 2), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2645, -1), (key2645, -1), (key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1)]

theorem rawRowCheck14571 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form10 = rawRow14571 := by decide +kernel

def row14571 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

theorem rowCheck14571 : row14571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14571 := by decide +kernel

theorem rowEval14571 (x : Key → ℝ) : Integer.Sparse.eval row14571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14571, Integer.Sparse.eval_collectBalanced, rawRowCheck14571]

def rawRow14572 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2856, -1), (key2974, -1), (key2636, -1), (key2974, -1), (key2636, -1), (key2856, -1), (key2701, 2), (key2971, 2), (key2627, 2), (key2971, 2), (key2627, 2), (key2701, 2), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2734, -1), (key2892, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2734, -1)]

theorem rawRowCheck14572 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form10 = rawRow14572 := by decide +kernel

def row14572 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

theorem rowCheck14572 : row14572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14572 := by decide +kernel

theorem rowEval14572 (x : Key → ℝ) : Integer.Sparse.eval row14572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14572, Integer.Sparse.eval_collectBalanced, rawRowCheck14572]

def rawRow14573 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2974, -1), (key2856, -1), (key2974, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2971, 2), (key2701, 2), (key2971, 2), (key2627, 2), (key2701, 2), (key2627, 2), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2892, -1), (key2734, -1), (key2892, -1), (key2645, -1), (key2734, -1), (key2645, -1)]

theorem rawRowCheck14573 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form10 = rawRow14573 := by decide +kernel

def row14573 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, -2), (key2701, 4), (key2734, -2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, -2), (key2892, -2), (key2895, 4), (key2971, 4), (key2974, -2)]

theorem rowCheck14573 : row14573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14573 := by decide +kernel

theorem rowEval14573 (x : Key → ℝ) : Integer.Sparse.eval row14573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14573, Integer.Sparse.eval_collectBalanced, rawRowCheck14573]

def rawRow14574 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2636, 2), (key2856, 2), (key2974, 2), (key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2624, 2), (key2636, 2), (key2698, 2), (key2722, 2), (key2974, 2), (key2981, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1)]

theorem rawRowCheck14574 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form10 = rawRow14574 := by decide +kernel

def row14574 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

theorem rowCheck14574 : row14574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14574 := by decide +kernel

theorem rowEval14574 (x : Key → ℝ) : Integer.Sparse.eval row14574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14574, Integer.Sparse.eval_collectBalanced, rawRowCheck14574]

def rawRow14575 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2636, 2), (key2974, 2), (key2856, 2), (key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2636, 2), (key2624, 2), (key2722, 2), (key2698, 2), (key2981, 2), (key2974, 2), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1)]

theorem rawRowCheck14575 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form10 = rawRow14575 := by decide +kernel

def row14575 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

theorem rowCheck14575 : row14575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14575 := by decide +kernel

theorem rowEval14575 (x : Key → ℝ) : Integer.Sparse.eval row14575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14575, Integer.Sparse.eval_collectBalanced, rawRowCheck14575]

def rawRow14576 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2856, 2), (key2636, 2), (key2974, 2), (key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2698, 2), (key2974, 2), (key2624, 2), (key2981, 2), (key2636, 2), (key2722, 2), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1)]

theorem rawRowCheck14576 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form10 = rawRow14576 := by decide +kernel

def row14576 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

theorem rowCheck14576 : row14576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14576 := by decide +kernel

theorem rowEval14576 (x : Key → ℝ) : Integer.Sparse.eval row14576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14576, Integer.Sparse.eval_collectBalanced, rawRowCheck14576]

def rawRow14577 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2856, 2), (key2974, 2), (key2636, 2), (key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2974, 2), (key2698, 2), (key2981, 2), (key2624, 2), (key2722, 2), (key2636, 2), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1)]

theorem rawRowCheck14577 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form10 = rawRow14577 := by decide +kernel

def row14577 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

theorem rowCheck14577 : row14577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14577 := by decide +kernel

theorem rowEval14577 (x : Key → ℝ) : Integer.Sparse.eval row14577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14577, Integer.Sparse.eval_collectBalanced, rawRowCheck14577]

def rawRow14578 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2974, 2), (key2636, 2), (key2856, 2), (key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2722, 2), (key2981, 2), (key2636, 2), (key2974, 2), (key2624, 2), (key2698, 2), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1)]

theorem rawRowCheck14578 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form10 = rawRow14578 := by decide +kernel

def row14578 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

theorem rowCheck14578 : row14578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14578 := by decide +kernel

theorem rowEval14578 (x : Key → ℝ) : Integer.Sparse.eval row14578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14578, Integer.Sparse.eval_collectBalanced, rawRowCheck14578]

def rawRow14579 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2974, 2), (key2856, 2), (key2636, 2), (key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2981, 2), (key2722, 2), (key2974, 2), (key2636, 2), (key2698, 2), (key2624, 2), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1)]

theorem rawRowCheck14579 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form10 = rawRow14579 := by decide +kernel

def row14579 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2698, 2), (key2701, -1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, -1), (key2856, 1), (key2866, -2), (key2895, -1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, 4), (key2981, 1)]

theorem rowCheck14579 : row14579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14579 := by decide +kernel

theorem rowEval14579 (x : Key → ℝ) : Integer.Sparse.eval row14579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14579, Integer.Sparse.eval_collectBalanced, rawRowCheck14579]

def rawRow14580 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2698, -1), (key2974, -1), (key2722, -1), (key2981, -1), (key2627, 2), (key2701, 2), (key2971, 2), (key2624, -1), (key2636, -1), (key2698, -1), (key2974, -1), (key2722, -1), (key2981, -1), (key2608, 2), (key2651, 2), (key2663, 2), (key2745, 2), (key2941, 2), (key2958, 2), (key2611, -1), (key2636, -1), (key2666, -1), (key2722, -1), (key2790, -1), (key2825, -1), (key2627, 2), (key2781, 2), (key2866, 2), (key2611, -1), (key2636, -1), (key2666, -1), (key2722, -1), (key2790, -1), (key2825, -1)]

theorem rawRowCheck14580 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form10 = rawRow14580 := by decide +kernel

def row14580 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck14580 : row14580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14580 := by decide +kernel

theorem rowEval14580 (x : Key → ℝ) : Integer.Sparse.eval row14580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14580, Integer.Sparse.eval_collectBalanced, rawRowCheck14580]

def rawRow14581 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2974, -1), (key2698, -1), (key2981, -1), (key2722, -1), (key2627, 2), (key2971, 2), (key2701, 2), (key2636, -1), (key2624, -1), (key2974, -1), (key2698, -1), (key2981, -1), (key2722, -1), (key2651, 2), (key2608, 2), (key2745, 2), (key2663, 2), (key2958, 2), (key2941, 2), (key2636, -1), (key2611, -1), (key2722, -1), (key2666, -1), (key2825, -1), (key2790, -1), (key2627, 2), (key2866, 2), (key2781, 2), (key2636, -1), (key2611, -1), (key2722, -1), (key2666, -1), (key2825, -1), (key2790, -1)]

theorem rawRowCheck14581 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form10 = rawRow14581 := by decide +kernel

def row14581 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck14581 : row14581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14581 := by decide +kernel

theorem rowEval14581 (x : Key → ℝ) : Integer.Sparse.eval row14581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14581, Integer.Sparse.eval_collectBalanced, rawRowCheck14581]

def rawRow14582 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2624, -1), (key2981, -1), (key2636, -1), (key2974, -1), (key2701, 2), (key2627, 2), (key2971, 2), (key2698, -1), (key2722, -1), (key2624, -1), (key2981, -1), (key2636, -1), (key2974, -1), (key2663, 2), (key2745, 2), (key2608, 2), (key2958, 2), (key2651, 2), (key2745, 2), (key2666, -1), (key2790, -1), (key2611, -1), (key2825, -1), (key2636, -1), (key2722, -1), (key2781, 2), (key2627, 2), (key2866, 2), (key2666, -1), (key2790, -1), (key2611, -1), (key2825, -1), (key2636, -1), (key2722, -1)]

theorem rawRowCheck14582 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form10 = rawRow14582 := by decide +kernel

def row14582 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 4), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck14582 : row14582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14582 := by decide +kernel

theorem rowEval14582 (x : Key → ℝ) : Integer.Sparse.eval row14582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14582, Integer.Sparse.eval_collectBalanced, rawRowCheck14582]

def rawRow14583 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2981, -1), (key2624, -1), (key2974, -1), (key2636, -1), (key2701, 2), (key2971, 2), (key2627, 2), (key2722, -1), (key2698, -1), (key2981, -1), (key2624, -1), (key2974, -1), (key2636, -1), (key2745, 2), (key2663, 2), (key2958, 2), (key2608, 2), (key2745, 2), (key2651, 2), (key2790, -1), (key2666, -1), (key2825, -1), (key2611, -1), (key2722, -1), (key2636, -1), (key2781, 2), (key2866, 2), (key2627, 2), (key2790, -1), (key2666, -1), (key2825, -1), (key2611, -1), (key2722, -1), (key2636, -1)]

theorem rawRowCheck14583 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form10 = rawRow14583 := by decide +kernel

def row14583 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 4), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck14583 : row14583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14583 := by decide +kernel

theorem rowEval14583 (x : Key → ℝ) : Integer.Sparse.eval row14583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14583, Integer.Sparse.eval_collectBalanced, rawRowCheck14583]

def rawRow14584 : Integer.Sparse Key := [(key2974, -1), (key2981, -1), (key2636, -1), (key2722, -1), (key2624, -1), (key2698, -1), (key2971, 2), (key2627, 2), (key2701, 2), (key2974, -1), (key2981, -1), (key2636, -1), (key2722, -1), (key2624, -1), (key2698, -1), (key2941, 2), (key2958, 2), (key2651, 2), (key2745, 2), (key2608, 2), (key2663, 2), (key2722, -1), (key2825, -1), (key2636, -1), (key2790, -1), (key2611, -1), (key2666, -1), (key2866, 2), (key2627, 2), (key2781, 2), (key2722, -1), (key2825, -1), (key2636, -1), (key2790, -1), (key2611, -1), (key2666, -1)]

theorem rawRowCheck14584 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form10 = rawRow14584 := by decide +kernel

def row14584 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck14584 : row14584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14584 := by decide +kernel

theorem rowEval14584 (x : Key → ℝ) : Integer.Sparse.eval row14584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14584, Integer.Sparse.eval_collectBalanced, rawRowCheck14584]

def rawRow14585 : Integer.Sparse Key := [(key2981, -1), (key2974, -1), (key2722, -1), (key2636, -1), (key2698, -1), (key2624, -1), (key2971, 2), (key2701, 2), (key2627, 2), (key2981, -1), (key2974, -1), (key2722, -1), (key2636, -1), (key2698, -1), (key2624, -1), (key2958, 2), (key2941, 2), (key2745, 2), (key2651, 2), (key2663, 2), (key2608, 2), (key2825, -1), (key2722, -1), (key2790, -1), (key2636, -1), (key2666, -1), (key2611, -1), (key2866, 2), (key2781, 2), (key2627, 2), (key2825, -1), (key2722, -1), (key2790, -1), (key2636, -1), (key2666, -1), (key2611, -1)]

theorem rawRowCheck14585 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form10 = rawRow14585 := by decide +kernel

def row14585 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -2), (key2701, 2), (key2722, -4), (key2745, 2), (key2781, 2), (key2790, -2), (key2825, -2), (key2866, 2), (key2941, 2), (key2958, 2), (key2971, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck14585 : row14585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14585 := by decide +kernel

theorem rowEval14585 (x : Key → ℝ) : Integer.Sparse.eval row14585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14585, Integer.Sparse.eval_collectBalanced, rawRowCheck14585]

def rawRow14586 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2611, 2), (key2636, 2), (key2666, 2), (key2790, 2), (key2722, 2), (key2825, 2), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2636, 2), (key2790, 2), (key2856, 2), (key2611, -1), (key2627, -1), (key2666, -1), (key2701, -1), (key2781, -1), (key2804, -1)]

theorem rawRowCheck14586 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form10 = rawRow14586 := by decide +kernel

def row14586 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

theorem rowCheck14586 : row14586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14586 := by decide +kernel

theorem rowEval14586 (x : Key → ℝ) : Integer.Sparse.eval row14586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14586, Integer.Sparse.eval_collectBalanced, rawRowCheck14586]

def rawRow14587 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2636, 2), (key2611, 2), (key2790, 2), (key2666, 2), (key2825, 2), (key2722, 2), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2636, 2), (key2856, 2), (key2790, 2), (key2627, -1), (key2611, -1), (key2701, -1), (key2666, -1), (key2804, -1), (key2781, -1)]

theorem rawRowCheck14587 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form10 = rawRow14587 := by decide +kernel

def row14587 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

theorem rowCheck14587 : row14587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14587 := by decide +kernel

theorem rowEval14587 (x : Key → ℝ) : Integer.Sparse.eval row14587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14587, Integer.Sparse.eval_collectBalanced, rawRowCheck14587]

def rawRow14588 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2666, 2), (key2722, 2), (key2611, 2), (key2825, 2), (key2636, 2), (key2790, 2), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2790, 2), (key2636, 2), (key2856, 2), (key2666, -1), (key2781, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2701, -1)]

theorem rawRowCheck14588 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form10 = rawRow14588 := by decide +kernel

def row14588 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

theorem rowCheck14588 : row14588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14588 := by decide +kernel

theorem rowEval14588 (x : Key → ℝ) : Integer.Sparse.eval row14588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck14588, Integer.Sparse.eval_collectBalanced, rawRowCheck14588]

def rawRow14589 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2722, 2), (key2666, 2), (key2825, 2), (key2611, 2), (key2790, 2), (key2636, 2), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2790, 2), (key2856, 2), (key2636, 2), (key2781, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2701, -1), (key2627, -1)]

theorem rawRowCheck14589 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form10 = rawRow14589 := by decide +kernel

def row14589 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

theorem rowCheck14589 : row14589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14589 := by decide +kernel

theorem rowEval14589 (x : Key → ℝ) : Integer.Sparse.eval row14589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14589, Integer.Sparse.eval_collectBalanced, rawRowCheck14589]

def rawRow14590 : Integer.Sparse Key := [(key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2790, 2), (key2825, 2), (key2636, 2), (key2722, 2), (key2611, 2), (key2666, 2), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2856, 2), (key2636, 2), (key2790, 2), (key2701, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2611, -1), (key2666, -1)]

theorem rawRowCheck14590 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form10 = rawRow14590 := by decide +kernel

def row14590 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

theorem rowCheck14590 : row14590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14590 := by decide +kernel

theorem rowEval14590 (x : Key → ℝ) : Integer.Sparse.eval row14590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck14590, Integer.Sparse.eval_collectBalanced, rawRowCheck14590]

def rawRow14591 : Integer.Sparse Key := [(key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, 2), (key2790, 2), (key2722, 2), (key2636, 2), (key2666, 2), (key2611, 2), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2856, 2), (key2790, 2), (key2636, 2), (key2804, -1), (key2701, -1), (key2781, -1), (key2627, -1), (key2666, -1), (key2611, -1)]

theorem rawRowCheck14591 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form10 = rawRow14591 := by decide +kernel

def row14591 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, -1), (key2790, 4), (key2801, -1), (key2804, -1), (key2825, 2), (key2851, 2), (key2856, 1), (key2866, -1), (key2895, -1), (key2902, -1)]

theorem rowCheck14591 : row14591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14591 := by decide +kernel

theorem rowEval14591 (x : Key → ℝ) : Integer.Sparse.eval row14591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck14591, Integer.Sparse.eval_collectBalanced, rawRowCheck14591]

end MUB6.Certificate.GramRows

end OAI
