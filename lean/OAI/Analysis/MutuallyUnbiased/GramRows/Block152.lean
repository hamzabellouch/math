import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16384 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 6), (key2847, -2), (key2969, -2), (key2847, -2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2881, -2), (key2594, -2), (key2881, -2), (key2890, 6), (key2911, -2), (key2601, -2), (key2911, -2)]

theorem rawRowCheck16384 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form8 = rawRow16384 := by decide +kernel

def row16384 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

theorem rowCheck16384 : row16384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16384 := by decide +kernel

theorem rowEval16384 (x : Key → ℝ) : Integer.Sparse.eval row16384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16384, Integer.Sparse.eval_collectBalanced, rawRowCheck16384]

def rawRow16385 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2773, 6), (key2969, -2), (key2847, -2), (key2847, -2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2881, -2), (key2881, -2), (key2594, -2), (key2890, 6), (key2911, -2), (key2911, -2), (key2601, -2)]

theorem rawRowCheck16385 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form8 = rawRow16385 := by decide +kernel

def row16385 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

theorem rowCheck16385 : row16385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16385 := by decide +kernel

theorem rowEval16385 (x : Key → ℝ) : Integer.Sparse.eval row16385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16385, Integer.Sparse.eval_collectBalanced, rawRowCheck16385]

def rawRow16386 : Integer.Sparse Key := [(key2770, -2), (key2773, -2), (key2932, -2), (key2770, 6), (key2878, -2), (key2881, -2), (key2990, -2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2591, -2), (key2847, -2), (key2878, -2), (key2911, 6), (key2601, -2), (key2890, -2), (key2911, -2)]

theorem rawRowCheck16386 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form8 = rawRow16386 := by decide +kernel

def row16386 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16386 : row16386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16386 := by decide +kernel

theorem rowEval16386 (x : Key → ℝ) : Integer.Sparse.eval row16386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16386, Integer.Sparse.eval_collectBalanced, rawRowCheck16386]

def rawRow16387 : Integer.Sparse Key := [(key2773, -2), (key2770, -2), (key2932, -2), (key2770, 6), (key2881, -2), (key2878, -2), (key2990, -2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2591, -2), (key2878, -2), (key2847, -2), (key2911, 6), (key2601, -2), (key2911, -2), (key2890, -2)]

theorem rawRowCheck16387 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form8 = rawRow16387 := by decide +kernel

def row16387 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16387 : row16387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16387 := by decide +kernel

theorem rowEval16387 (x : Key → ℝ) : Integer.Sparse.eval row16387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16387, Integer.Sparse.eval_collectBalanced, rawRowCheck16387]

def rawRow16388 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2773, -2), (key2770, 6), (key2878, -2), (key2990, -2), (key2881, -2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2847, -2), (key2591, -2), (key2878, -2), (key2911, 6), (key2890, -2), (key2601, -2), (key2911, -2)]

theorem rawRowCheck16388 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form8 = rawRow16388 := by decide +kernel

def row16388 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16388 : row16388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16388 := by decide +kernel

theorem rowEval16388 (x : Key → ℝ) : Integer.Sparse.eval row16388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16388, Integer.Sparse.eval_collectBalanced, rawRowCheck16388]

def rawRow16389 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2773, -2), (key2770, 6), (key2990, -2), (key2878, -2), (key2881, -2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2847, -2), (key2878, -2), (key2591, -2), (key2911, 6), (key2890, -2), (key2911, -2), (key2601, -2)]

theorem rawRowCheck16389 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form8 = rawRow16389 := by decide +kernel

def row16389 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16389 : row16389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16389 := by decide +kernel

theorem rowEval16389 (x : Key → ℝ) : Integer.Sparse.eval row16389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16389, Integer.Sparse.eval_collectBalanced, rawRowCheck16389]

def rawRow16390 : Integer.Sparse Key := [(key2773, -2), (key2932, -2), (key2770, -2), (key2770, 6), (key2881, -2), (key2990, -2), (key2878, -2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2878, -2), (key2591, -2), (key2847, -2), (key2911, 6), (key2911, -2), (key2601, -2), (key2890, -2)]

theorem rawRowCheck16390 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form8 = rawRow16390 := by decide +kernel

def row16390 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16390 : row16390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16390 := by decide +kernel

theorem rowEval16390 (x : Key → ℝ) : Integer.Sparse.eval row16390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16390, Integer.Sparse.eval_collectBalanced, rawRowCheck16390]

def rawRow16391 : Integer.Sparse Key := [(key2932, -2), (key2773, -2), (key2770, -2), (key2770, 6), (key2990, -2), (key2881, -2), (key2878, -2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2878, -2), (key2847, -2), (key2591, -2), (key2911, 6), (key2911, -2), (key2890, -2), (key2601, -2)]

theorem rawRowCheck16391 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form8 = rawRow16391 := by decide +kernel

def row16391 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16391 : row16391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16391 := by decide +kernel

theorem rowEval16391 (x : Key → ℝ) : Integer.Sparse.eval row16391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16391, Integer.Sparse.eval_collectBalanced, rawRowCheck16391]

def rawRow16392 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2890, 6), (key2770, -2), (key2770, -2), (key2932, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2601, -2), (key2911, -2), (key2911, -2), (key2773, 6), (key2594, -2), (key2881, -2), (key2881, -2)]

theorem rawRowCheck16392 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form8 = rawRow16392 := by decide +kernel

def row16392 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

theorem rowCheck16392 : row16392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16392 := by decide +kernel

theorem rowEval16392 (x : Key → ℝ) : Integer.Sparse.eval row16392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16392, Integer.Sparse.eval_collectBalanced, rawRowCheck16392]

def rawRow16393 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2890, 6), (key2770, -2), (key2932, -2), (key2770, -2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2911, -2), (key2601, -2), (key2911, -2), (key2773, 6), (key2881, -2), (key2594, -2), (key2881, -2)]

theorem rawRowCheck16393 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form8 = rawRow16393 := by decide +kernel

def row16393 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

theorem rowCheck16393 : row16393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16393 := by decide +kernel

theorem rowEval16393 (x : Key → ℝ) : Integer.Sparse.eval row16393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16393, Integer.Sparse.eval_collectBalanced, rawRowCheck16393]

def rawRow16394 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2890, 6), (key2932, -2), (key2770, -2), (key2770, -2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2911, -2), (key2911, -2), (key2601, -2), (key2773, 6), (key2881, -2), (key2881, -2), (key2594, -2)]

theorem rawRowCheck16394 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form8 = rawRow16394 := by decide +kernel

def row16394 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

theorem rowCheck16394 : row16394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16394 := by decide +kernel

theorem rowEval16394 (x : Key → ℝ) : Integer.Sparse.eval row16394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16394, Integer.Sparse.eval_collectBalanced, rawRowCheck16394]

def rawRow16395 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2969, -2), (key2847, 6), (key2878, -2), (key2911, -2), (key2990, -2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2591, -2), (key2770, -2), (key2878, -2), (key2881, 6), (key2594, -2), (key2773, -2), (key2881, -2)]

theorem rawRowCheck16395 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form8 = rawRow16395 := by decide +kernel

def row16395 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16395 : row16395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16395 := by decide +kernel

theorem rowEval16395 (x : Key → ℝ) : Integer.Sparse.eval row16395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16395, Integer.Sparse.eval_collectBalanced, rawRowCheck16395]

def rawRow16396 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2969, -2), (key2847, 6), (key2911, -2), (key2878, -2), (key2990, -2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2591, -2), (key2878, -2), (key2770, -2), (key2881, 6), (key2594, -2), (key2881, -2), (key2773, -2)]

theorem rawRowCheck16396 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form8 = rawRow16396 := by decide +kernel

def row16396 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16396 : row16396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16396 := by decide +kernel

theorem rowEval16396 (x : Key → ℝ) : Integer.Sparse.eval row16396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16396, Integer.Sparse.eval_collectBalanced, rawRowCheck16396]

def rawRow16397 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2890, -2), (key2847, 6), (key2878, -2), (key2990, -2), (key2911, -2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2770, -2), (key2591, -2), (key2878, -2), (key2881, 6), (key2773, -2), (key2594, -2), (key2881, -2)]

theorem rawRowCheck16397 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form8 = rawRow16397 := by decide +kernel

def row16397 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16397 : row16397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16397 := by decide +kernel

theorem rowEval16397 (x : Key → ℝ) : Integer.Sparse.eval row16397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16397, Integer.Sparse.eval_collectBalanced, rawRowCheck16397]

def rawRow16398 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2890, -2), (key2847, 6), (key2990, -2), (key2878, -2), (key2911, -2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2770, -2), (key2878, -2), (key2591, -2), (key2881, 6), (key2773, -2), (key2881, -2), (key2594, -2)]

theorem rawRowCheck16398 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form8 = rawRow16398 := by decide +kernel

def row16398 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16398 : row16398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16398 := by decide +kernel

theorem rowEval16398 (x : Key → ℝ) : Integer.Sparse.eval row16398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16398, Integer.Sparse.eval_collectBalanced, rawRowCheck16398]

def rawRow16399 : Integer.Sparse Key := [(key2890, -2), (key2969, -2), (key2847, -2), (key2847, 6), (key2911, -2), (key2990, -2), (key2878, -2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2878, -2), (key2591, -2), (key2770, -2), (key2881, 6), (key2881, -2), (key2594, -2), (key2773, -2)]

theorem rawRowCheck16399 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form8 = rawRow16399 := by decide +kernel

def row16399 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16399 : row16399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16399 := by decide +kernel

theorem rowEval16399 (x : Key → ℝ) : Integer.Sparse.eval row16399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16399, Integer.Sparse.eval_collectBalanced, rawRowCheck16399]

def rawRow16400 : Integer.Sparse Key := [(key2969, -2), (key2890, -2), (key2847, -2), (key2847, 6), (key2990, -2), (key2911, -2), (key2878, -2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2878, -2), (key2770, -2), (key2591, -2), (key2881, 6), (key2881, -2), (key2773, -2), (key2594, -2)]

theorem rawRowCheck16400 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form8 = rawRow16400 := by decide +kernel

def row16400 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16400 : row16400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16400 := by decide +kernel

theorem rowEval16400 (x : Key → ℝ) : Integer.Sparse.eval row16400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16400, Integer.Sparse.eval_collectBalanced, rawRowCheck16400]

def rawRow16401 : Integer.Sparse Key := [(key2878, -2), (key2881, -2), (key2990, -2), (key2911, 6), (key2770, -2), (key2773, -2), (key2932, -2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2601, -2), (key2890, -2), (key2911, -2), (key2770, 6), (key2591, -2), (key2847, -2), (key2878, -2)]

theorem rawRowCheck16401 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form8 = rawRow16401 := by decide +kernel

def row16401 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16401 : row16401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16401 := by decide +kernel

theorem rowEval16401 (x : Key → ℝ) : Integer.Sparse.eval row16401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16401, Integer.Sparse.eval_collectBalanced, rawRowCheck16401]

def rawRow16402 : Integer.Sparse Key := [(key2881, -2), (key2878, -2), (key2990, -2), (key2911, 6), (key2773, -2), (key2770, -2), (key2932, -2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2601, -2), (key2911, -2), (key2890, -2), (key2770, 6), (key2591, -2), (key2878, -2), (key2847, -2)]

theorem rawRowCheck16402 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form8 = rawRow16402 := by decide +kernel

def row16402 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16402 : row16402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16402 := by decide +kernel

theorem rowEval16402 (x : Key → ℝ) : Integer.Sparse.eval row16402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16402, Integer.Sparse.eval_collectBalanced, rawRowCheck16402]

def rawRow16403 : Integer.Sparse Key := [(key2878, -2), (key2990, -2), (key2881, -2), (key2911, 6), (key2770, -2), (key2932, -2), (key2773, -2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2890, -2), (key2601, -2), (key2911, -2), (key2770, 6), (key2847, -2), (key2591, -2), (key2878, -2)]

theorem rawRowCheck16403 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form8 = rawRow16403 := by decide +kernel

def row16403 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16403 : row16403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16403 := by decide +kernel

theorem rowEval16403 (x : Key → ℝ) : Integer.Sparse.eval row16403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16403, Integer.Sparse.eval_collectBalanced, rawRowCheck16403]

def rawRow16404 : Integer.Sparse Key := [(key2990, -2), (key2878, -2), (key2881, -2), (key2911, 6), (key2932, -2), (key2770, -2), (key2773, -2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2890, -2), (key2911, -2), (key2601, -2), (key2770, 6), (key2847, -2), (key2878, -2), (key2591, -2)]

theorem rawRowCheck16404 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form8 = rawRow16404 := by decide +kernel

def row16404 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16404 : row16404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16404 := by decide +kernel

theorem rowEval16404 (x : Key → ℝ) : Integer.Sparse.eval row16404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16404, Integer.Sparse.eval_collectBalanced, rawRowCheck16404]

def rawRow16405 : Integer.Sparse Key := [(key2881, -2), (key2990, -2), (key2878, -2), (key2911, 6), (key2773, -2), (key2932, -2), (key2770, -2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2911, -2), (key2601, -2), (key2890, -2), (key2770, 6), (key2878, -2), (key2591, -2), (key2847, -2)]

theorem rawRowCheck16405 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form8 = rawRow16405 := by decide +kernel

def row16405 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16405 : row16405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16405 := by decide +kernel

theorem rowEval16405 (x : Key → ℝ) : Integer.Sparse.eval row16405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16405, Integer.Sparse.eval_collectBalanced, rawRowCheck16405]

def rawRow16406 : Integer.Sparse Key := [(key2990, -2), (key2881, -2), (key2878, -2), (key2911, 6), (key2932, -2), (key2773, -2), (key2770, -2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2911, -2), (key2890, -2), (key2601, -2), (key2770, 6), (key2878, -2), (key2847, -2), (key2591, -2)]

theorem rawRowCheck16406 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form8 = rawRow16406 := by decide +kernel

def row16406 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

theorem rowCheck16406 : row16406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16406 := by decide +kernel

theorem rowEval16406 (x : Key → ℝ) : Integer.Sparse.eval row16406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16406, Integer.Sparse.eval_collectBalanced, rawRowCheck16406]

def rawRow16407 : Integer.Sparse Key := [(key2878, -2), (key2911, -2), (key2990, -2), (key2881, 6), (key2847, -2), (key2890, -2), (key2969, -2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2594, -2), (key2773, -2), (key2881, -2), (key2847, 6), (key2591, -2), (key2770, -2), (key2878, -2)]

theorem rawRowCheck16407 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form8 = rawRow16407 := by decide +kernel

def row16407 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16407 : row16407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16407 := by decide +kernel

theorem rowEval16407 (x : Key → ℝ) : Integer.Sparse.eval row16407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16407, Integer.Sparse.eval_collectBalanced, rawRowCheck16407]

def rawRow16408 : Integer.Sparse Key := [(key2911, -2), (key2878, -2), (key2990, -2), (key2881, 6), (key2890, -2), (key2847, -2), (key2969, -2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2594, -2), (key2881, -2), (key2773, -2), (key2847, 6), (key2591, -2), (key2878, -2), (key2770, -2)]

theorem rawRowCheck16408 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form8 = rawRow16408 := by decide +kernel

def row16408 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16408 : row16408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16408 := by decide +kernel

theorem rowEval16408 (x : Key → ℝ) : Integer.Sparse.eval row16408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16408, Integer.Sparse.eval_collectBalanced, rawRowCheck16408]

def rawRow16409 : Integer.Sparse Key := [(key2878, -2), (key2990, -2), (key2911, -2), (key2881, 6), (key2847, -2), (key2969, -2), (key2890, -2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2773, -2), (key2594, -2), (key2881, -2), (key2847, 6), (key2770, -2), (key2591, -2), (key2878, -2)]

theorem rawRowCheck16409 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form8 = rawRow16409 := by decide +kernel

def row16409 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16409 : row16409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16409 := by decide +kernel

theorem rowEval16409 (x : Key → ℝ) : Integer.Sparse.eval row16409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16409, Integer.Sparse.eval_collectBalanced, rawRowCheck16409]

def rawRow16410 : Integer.Sparse Key := [(key2990, -2), (key2878, -2), (key2911, -2), (key2881, 6), (key2969, -2), (key2847, -2), (key2890, -2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2773, -2), (key2881, -2), (key2594, -2), (key2847, 6), (key2770, -2), (key2878, -2), (key2591, -2)]

theorem rawRowCheck16410 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form8 = rawRow16410 := by decide +kernel

def row16410 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16410 : row16410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16410 := by decide +kernel

theorem rowEval16410 (x : Key → ℝ) : Integer.Sparse.eval row16410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16410, Integer.Sparse.eval_collectBalanced, rawRowCheck16410]

def rawRow16411 : Integer.Sparse Key := [(key2911, -2), (key2990, -2), (key2878, -2), (key2881, 6), (key2890, -2), (key2969, -2), (key2847, -2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2881, -2), (key2594, -2), (key2773, -2), (key2847, 6), (key2878, -2), (key2591, -2), (key2770, -2)]

theorem rawRowCheck16411 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form8 = rawRow16411 := by decide +kernel

def row16411 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16411 : row16411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16411 := by decide +kernel

theorem rowEval16411 (x : Key → ℝ) : Integer.Sparse.eval row16411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16411, Integer.Sparse.eval_collectBalanced, rawRowCheck16411]

def rawRow16412 : Integer.Sparse Key := [(key2990, -2), (key2911, -2), (key2878, -2), (key2881, 6), (key2969, -2), (key2890, -2), (key2847, -2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2881, -2), (key2773, -2), (key2594, -2), (key2847, 6), (key2878, -2), (key2770, -2), (key2591, -2)]

theorem rawRowCheck16412 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form8 = rawRow16412 := by decide +kernel

def row16412 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

theorem rowCheck16412 : row16412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16412 := by decide +kernel

theorem rowEval16412 (x : Key → ℝ) : Integer.Sparse.eval row16412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16412, Integer.Sparse.eval_collectBalanced, rawRowCheck16412]

def rawRow16413 : Integer.Sparse Key := [(key2881, -2), (key2911, -2), (key2990, -2), (key2878, 6), (key2881, -2), (key2911, -2), (key2990, -2), (key2594, 2), (key2601, 2), (key2773, 2), (key2890, 2), (key2932, 2), (key2969, 2), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6), (key2591, -2), (key2770, -2), (key2847, -2)]

theorem rawRowCheck16413 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form8 = rawRow16413 := by decide +kernel

def row16413 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

theorem rowCheck16413 : row16413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16413 := by decide +kernel

theorem rowEval16413 (x : Key → ℝ) : Integer.Sparse.eval row16413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16413, Integer.Sparse.eval_collectBalanced, rawRowCheck16413]

def rawRow16414 : Integer.Sparse Key := [(key2911, -2), (key2881, -2), (key2990, -2), (key2878, 6), (key2911, -2), (key2881, -2), (key2990, -2), (key2601, 2), (key2594, 2), (key2890, 2), (key2773, 2), (key2969, 2), (key2932, 2), (key2591, -2), (key2847, -2), (key2770, -2), (key2878, 6), (key2591, -2), (key2847, -2), (key2770, -2)]

theorem rawRowCheck16414 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form8 = rawRow16414 := by decide +kernel

def row16414 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

theorem rowCheck16414 : row16414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16414 := by decide +kernel

theorem rowEval16414 (x : Key → ℝ) : Integer.Sparse.eval row16414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16414, Integer.Sparse.eval_collectBalanced, rawRowCheck16414]

def rawRow16415 : Integer.Sparse Key := [(key2881, -2), (key2990, -2), (key2911, -2), (key2878, 6), (key2881, -2), (key2990, -2), (key2911, -2), (key2773, 2), (key2932, 2), (key2594, 2), (key2969, 2), (key2601, 2), (key2890, 2), (key2770, -2), (key2591, -2), (key2847, -2), (key2878, 6), (key2770, -2), (key2591, -2), (key2847, -2)]

theorem rawRowCheck16415 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form8 = rawRow16415 := by decide +kernel

def row16415 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

theorem rowCheck16415 : row16415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16415 := by decide +kernel

theorem rowEval16415 (x : Key → ℝ) : Integer.Sparse.eval row16415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck16415, Integer.Sparse.eval_collectBalanced, rawRowCheck16415]

def rawRow16416 : Integer.Sparse Key := [(key2990, -2), (key2881, -2), (key2911, -2), (key2878, 6), (key2990, -2), (key2881, -2), (key2911, -2), (key2932, 2), (key2773, 2), (key2969, 2), (key2594, 2), (key2890, 2), (key2601, 2), (key2770, -2), (key2847, -2), (key2591, -2), (key2878, 6), (key2770, -2), (key2847, -2), (key2591, -2)]

theorem rawRowCheck16416 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form8 = rawRow16416 := by decide +kernel

def row16416 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

theorem rowCheck16416 : row16416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16416 := by decide +kernel

theorem rowEval16416 (x : Key → ℝ) : Integer.Sparse.eval row16416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16416, Integer.Sparse.eval_collectBalanced, rawRowCheck16416]

def rawRow16417 : Integer.Sparse Key := [(key2911, -2), (key2990, -2), (key2881, -2), (key2878, 6), (key2911, -2), (key2990, -2), (key2881, -2), (key2890, 2), (key2969, 2), (key2601, 2), (key2932, 2), (key2594, 2), (key2773, 2), (key2847, -2), (key2591, -2), (key2770, -2), (key2878, 6), (key2847, -2), (key2591, -2), (key2770, -2)]

theorem rawRowCheck16417 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form8 = rawRow16417 := by decide +kernel

def row16417 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

theorem rowCheck16417 : row16417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16417 := by decide +kernel

theorem rowEval16417 (x : Key → ℝ) : Integer.Sparse.eval row16417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck16417, Integer.Sparse.eval_collectBalanced, rawRowCheck16417]

def rawRow16418 : Integer.Sparse Key := [(key2990, -2), (key2911, -2), (key2881, -2), (key2878, 6), (key2990, -2), (key2911, -2), (key2881, -2), (key2969, 2), (key2890, 2), (key2932, 2), (key2601, 2), (key2773, 2), (key2594, 2), (key2847, -2), (key2770, -2), (key2591, -2), (key2878, 6), (key2847, -2), (key2770, -2), (key2591, -2)]

theorem rawRowCheck16418 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form8 = rawRow16418 := by decide +kernel

def row16418 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

theorem rowCheck16418 : row16418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16418 := by decide +kernel

theorem rowEval16418 (x : Key → ℝ) : Integer.Sparse.eval row16418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck16418, Integer.Sparse.eval_collectBalanced, rawRowCheck16418]

def rawRow16419 : Integer.Sparse Key := [(key2016, 4), (key2136, 4), (key2136, 4), (key2021, -4), (key2021, -4), (key2171, -4), (key2049, -4), (key2049, -4), (key2263, -4), (key2074, 12)]

theorem rawRowCheck16419 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form9 = rawRow16419 := by decide +kernel

def row16419 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

theorem rowCheck16419 : row16419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16419 := by decide +kernel

theorem rowEval16419 (x : Key → ℝ) : Integer.Sparse.eval row16419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16419, Integer.Sparse.eval_collectBalanced, rawRowCheck16419]

def rawRow16420 : Integer.Sparse Key := [(key2136, 4), (key2016, 4), (key2136, 4), (key2021, -4), (key2171, -4), (key2021, -4), (key2049, -4), (key2263, -4), (key2049, -4), (key2074, 12)]

theorem rawRowCheck16420 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form9 = rawRow16420 := by decide +kernel

def row16420 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

theorem rowCheck16420 : row16420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16420 := by decide +kernel

theorem rowEval16420 (x : Key → ℝ) : Integer.Sparse.eval row16420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16420, Integer.Sparse.eval_collectBalanced, rawRowCheck16420]

def rawRow16421 : Integer.Sparse Key := [(key2136, 4), (key2136, 4), (key2016, 4), (key2171, -4), (key2021, -4), (key2021, -4), (key2263, -4), (key2049, -4), (key2049, -4), (key2074, 12)]

theorem rawRowCheck16421 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form9 = rawRow16421 := by decide +kernel

def row16421 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

theorem rowCheck16421 : row16421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16421 := by decide +kernel

theorem rowEval16421 (x : Key → ℝ) : Integer.Sparse.eval row16421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16421, Integer.Sparse.eval_collectBalanced, rawRowCheck16421]

def rawRow16422 : Integer.Sparse Key := [(key2021, 4), (key2136, 4), (key2171, 4), (key2016, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2074, -4), (key2263, -4), (key2049, 12)]

theorem rawRowCheck16422 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form9 = rawRow16422 := by decide +kernel

def row16422 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16422 : row16422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16422 := by decide +kernel

theorem rowEval16422 (x : Key → ℝ) : Integer.Sparse.eval row16422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16422, Integer.Sparse.eval_collectBalanced, rawRowCheck16422]

def rawRow16423 : Integer.Sparse Key := [(key2021, 4), (key2171, 4), (key2136, 4), (key2021, -4), (key2016, -4), (key2136, -4), (key2074, -4), (key2049, -4), (key2263, -4), (key2049, 12)]

theorem rawRowCheck16423 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form9 = rawRow16423 := by decide +kernel

def row16423 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16423 : row16423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16423 := by decide +kernel

theorem rowEval16423 (x : Key → ℝ) : Integer.Sparse.eval row16423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16423, Integer.Sparse.eval_collectBalanced, rawRowCheck16423]

def rawRow16424 : Integer.Sparse Key := [(key2136, 4), (key2021, 4), (key2171, 4), (key2016, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2263, -4), (key2074, -4), (key2049, 12)]

theorem rawRowCheck16424 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form9 = rawRow16424 := by decide +kernel

def row16424 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16424 : row16424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16424 := by decide +kernel

theorem rowEval16424 (x : Key → ℝ) : Integer.Sparse.eval row16424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16424, Integer.Sparse.eval_collectBalanced, rawRowCheck16424]

def rawRow16425 : Integer.Sparse Key := [(key2136, 4), (key2171, 4), (key2021, 4), (key2136, -4), (key2016, -4), (key2021, -4), (key2263, -4), (key2049, -4), (key2074, -4), (key2049, 12)]

theorem rawRowCheck16425 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form9 = rawRow16425 := by decide +kernel

def row16425 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16425 : row16425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16425 := by decide +kernel

theorem rowEval16425 (x : Key → ℝ) : Integer.Sparse.eval row16425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16425, Integer.Sparse.eval_collectBalanced, rawRowCheck16425]

def rawRow16426 : Integer.Sparse Key := [(key2171, 4), (key2021, 4), (key2136, 4), (key2021, -4), (key2136, -4), (key2016, -4), (key2074, -4), (key2263, -4), (key2049, -4), (key2049, 12)]

theorem rawRowCheck16426 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form9 = rawRow16426 := by decide +kernel

def row16426 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16426 : row16426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16426 := by decide +kernel

theorem rowEval16426 (x : Key → ℝ) : Integer.Sparse.eval row16426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16426, Integer.Sparse.eval_collectBalanced, rawRowCheck16426]

def rawRow16427 : Integer.Sparse Key := [(key2171, 4), (key2136, 4), (key2021, 4), (key2136, -4), (key2021, -4), (key2016, -4), (key2263, -4), (key2074, -4), (key2049, -4), (key2049, 12)]

theorem rawRowCheck16427 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form9 = rawRow16427 := by decide +kernel

def row16427 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16427 : row16427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16427 := by decide +kernel

theorem rowEval16427 (x : Key → ℝ) : Integer.Sparse.eval row16427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16427, Integer.Sparse.eval_collectBalanced, rawRowCheck16427]

def rawRow16428 : Integer.Sparse Key := [(key2016, 4), (key2136, 4), (key2136, 4), (key2049, -4), (key2049, -4), (key2263, -4), (key2021, -4), (key2021, -4), (key2171, -4), (key2074, 12)]

theorem rawRowCheck16428 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form9 = rawRow16428 := by decide +kernel

def row16428 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

theorem rowCheck16428 : row16428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16428 := by decide +kernel

theorem rowEval16428 (x : Key → ℝ) : Integer.Sparse.eval row16428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16428, Integer.Sparse.eval_collectBalanced, rawRowCheck16428]

def rawRow16429 : Integer.Sparse Key := [(key2136, 4), (key2016, 4), (key2136, 4), (key2049, -4), (key2263, -4), (key2049, -4), (key2021, -4), (key2171, -4), (key2021, -4), (key2074, 12)]

theorem rawRowCheck16429 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form9 = rawRow16429 := by decide +kernel

def row16429 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

theorem rowCheck16429 : row16429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16429 := by decide +kernel

theorem rowEval16429 (x : Key → ℝ) : Integer.Sparse.eval row16429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16429, Integer.Sparse.eval_collectBalanced, rawRowCheck16429]

def rawRow16430 : Integer.Sparse Key := [(key2136, 4), (key2136, 4), (key2016, 4), (key2263, -4), (key2049, -4), (key2049, -4), (key2171, -4), (key2021, -4), (key2021, -4), (key2074, 12)]

theorem rawRowCheck16430 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form9 = rawRow16430 := by decide +kernel

def row16430 : Integer.Sparse Key := [(key2016, 4), (key2021, -8), (key2049, -8), (key2074, 12), (key2136, 8), (key2171, -4), (key2263, -4)]

theorem rowCheck16430 : row16430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16430 := by decide +kernel

theorem rowEval16430 (x : Key → ℝ) : Integer.Sparse.eval row16430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16430, Integer.Sparse.eval_collectBalanced, rawRowCheck16430]

def rawRow16431 : Integer.Sparse Key := [(key2049, 4), (key2136, 4), (key2263, 4), (key2016, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2074, -4), (key2171, -4), (key2021, 12)]

theorem rawRowCheck16431 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form9 = rawRow16431 := by decide +kernel

def row16431 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16431 : row16431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16431 := by decide +kernel

theorem rowEval16431 (x : Key → ℝ) : Integer.Sparse.eval row16431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16431, Integer.Sparse.eval_collectBalanced, rawRowCheck16431]

def rawRow16432 : Integer.Sparse Key := [(key2049, 4), (key2263, 4), (key2136, 4), (key2049, -4), (key2016, -4), (key2136, -4), (key2074, -4), (key2021, -4), (key2171, -4), (key2021, 12)]

theorem rawRowCheck16432 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form9 = rawRow16432 := by decide +kernel

def row16432 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16432 : row16432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16432 := by decide +kernel

theorem rowEval16432 (x : Key → ℝ) : Integer.Sparse.eval row16432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16432, Integer.Sparse.eval_collectBalanced, rawRowCheck16432]

def rawRow16433 : Integer.Sparse Key := [(key2136, 4), (key2049, 4), (key2263, 4), (key2016, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2171, -4), (key2074, -4), (key2021, 12)]

theorem rawRowCheck16433 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form9 = rawRow16433 := by decide +kernel

def row16433 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16433 : row16433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16433 := by decide +kernel

theorem rowEval16433 (x : Key → ℝ) : Integer.Sparse.eval row16433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16433, Integer.Sparse.eval_collectBalanced, rawRowCheck16433]

def rawRow16434 : Integer.Sparse Key := [(key2136, 4), (key2263, 4), (key2049, 4), (key2136, -4), (key2016, -4), (key2049, -4), (key2171, -4), (key2021, -4), (key2074, -4), (key2021, 12)]

theorem rawRowCheck16434 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form9 = rawRow16434 := by decide +kernel

def row16434 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16434 : row16434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16434 := by decide +kernel

theorem rowEval16434 (x : Key → ℝ) : Integer.Sparse.eval row16434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16434, Integer.Sparse.eval_collectBalanced, rawRowCheck16434]

def rawRow16435 : Integer.Sparse Key := [(key2263, 4), (key2049, 4), (key2136, 4), (key2049, -4), (key2136, -4), (key2016, -4), (key2074, -4), (key2171, -4), (key2021, -4), (key2021, 12)]

theorem rawRowCheck16435 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form9 = rawRow16435 := by decide +kernel

def row16435 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16435 : row16435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16435 := by decide +kernel

theorem rowEval16435 (x : Key → ℝ) : Integer.Sparse.eval row16435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16435, Integer.Sparse.eval_collectBalanced, rawRowCheck16435]

def rawRow16436 : Integer.Sparse Key := [(key2263, 4), (key2136, 4), (key2049, 4), (key2136, -4), (key2049, -4), (key2016, -4), (key2171, -4), (key2074, -4), (key2021, -4), (key2021, 12)]

theorem rawRowCheck16436 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form9 = rawRow16436 := by decide +kernel

def row16436 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16436 : row16436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16436 := by decide +kernel

theorem rowEval16436 (x : Key → ℝ) : Integer.Sparse.eval row16436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16436, Integer.Sparse.eval_collectBalanced, rawRowCheck16436]

def rawRow16437 : Integer.Sparse Key := [(key2021, 4), (key2136, 4), (key2171, 4), (key2049, -4), (key2074, -4), (key2263, -4), (key2016, -4), (key2021, -4), (key2136, -4), (key2049, 12)]

theorem rawRowCheck16437 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form9 = rawRow16437 := by decide +kernel

def row16437 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16437 : row16437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16437 := by decide +kernel

theorem rowEval16437 (x : Key → ℝ) : Integer.Sparse.eval row16437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16437, Integer.Sparse.eval_collectBalanced, rawRowCheck16437]

def rawRow16438 : Integer.Sparse Key := [(key2021, 4), (key2171, 4), (key2136, 4), (key2074, -4), (key2049, -4), (key2263, -4), (key2021, -4), (key2016, -4), (key2136, -4), (key2049, 12)]

theorem rawRowCheck16438 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form9 = rawRow16438 := by decide +kernel

def row16438 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16438 : row16438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16438 := by decide +kernel

theorem rowEval16438 (x : Key → ℝ) : Integer.Sparse.eval row16438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16438, Integer.Sparse.eval_collectBalanced, rawRowCheck16438]

def rawRow16439 : Integer.Sparse Key := [(key2136, 4), (key2021, 4), (key2171, 4), (key2049, -4), (key2263, -4), (key2074, -4), (key2016, -4), (key2136, -4), (key2021, -4), (key2049, 12)]

theorem rawRowCheck16439 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form9 = rawRow16439 := by decide +kernel

def row16439 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16439 : row16439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16439 := by decide +kernel

theorem rowEval16439 (x : Key → ℝ) : Integer.Sparse.eval row16439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16439, Integer.Sparse.eval_collectBalanced, rawRowCheck16439]

def rawRow16440 : Integer.Sparse Key := [(key2136, 4), (key2171, 4), (key2021, 4), (key2263, -4), (key2049, -4), (key2074, -4), (key2136, -4), (key2016, -4), (key2021, -4), (key2049, 12)]

theorem rawRowCheck16440 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form9 = rawRow16440 := by decide +kernel

def row16440 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16440 : row16440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16440 := by decide +kernel

theorem rowEval16440 (x : Key → ℝ) : Integer.Sparse.eval row16440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16440, Integer.Sparse.eval_collectBalanced, rawRowCheck16440]

def rawRow16441 : Integer.Sparse Key := [(key2171, 4), (key2021, 4), (key2136, 4), (key2074, -4), (key2263, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2016, -4), (key2049, 12)]

theorem rawRowCheck16441 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form9 = rawRow16441 := by decide +kernel

def row16441 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16441 : row16441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16441 := by decide +kernel

theorem rowEval16441 (x : Key → ℝ) : Integer.Sparse.eval row16441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16441, Integer.Sparse.eval_collectBalanced, rawRowCheck16441]

def rawRow16442 : Integer.Sparse Key := [(key2171, 4), (key2136, 4), (key2021, 4), (key2263, -4), (key2074, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2016, -4), (key2049, 12)]

theorem rawRowCheck16442 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form9 = rawRow16442 := by decide +kernel

def row16442 : Integer.Sparse Key := [(key2016, -4), (key2049, 8), (key2074, -4), (key2171, 4), (key2263, -4)]

theorem rowCheck16442 : row16442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16442 := by decide +kernel

theorem rowEval16442 (x : Key → ℝ) : Integer.Sparse.eval row16442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16442, Integer.Sparse.eval_collectBalanced, rawRowCheck16442]

def rawRow16443 : Integer.Sparse Key := [(key2049, 4), (key2136, 4), (key2263, 4), (key2021, -4), (key2074, -4), (key2171, -4), (key2016, -4), (key2049, -4), (key2136, -4), (key2021, 12)]

theorem rawRowCheck16443 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form9 = rawRow16443 := by decide +kernel

def row16443 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16443 : row16443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16443 := by decide +kernel

theorem rowEval16443 (x : Key → ℝ) : Integer.Sparse.eval row16443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16443, Integer.Sparse.eval_collectBalanced, rawRowCheck16443]

def rawRow16444 : Integer.Sparse Key := [(key2049, 4), (key2263, 4), (key2136, 4), (key2074, -4), (key2021, -4), (key2171, -4), (key2049, -4), (key2016, -4), (key2136, -4), (key2021, 12)]

theorem rawRowCheck16444 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form9 = rawRow16444 := by decide +kernel

def row16444 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16444 : row16444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16444 := by decide +kernel

theorem rowEval16444 (x : Key → ℝ) : Integer.Sparse.eval row16444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16444, Integer.Sparse.eval_collectBalanced, rawRowCheck16444]

def rawRow16445 : Integer.Sparse Key := [(key2136, 4), (key2049, 4), (key2263, 4), (key2021, -4), (key2171, -4), (key2074, -4), (key2016, -4), (key2136, -4), (key2049, -4), (key2021, 12)]

theorem rawRowCheck16445 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form9 = rawRow16445 := by decide +kernel

def row16445 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16445 : row16445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16445 := by decide +kernel

theorem rowEval16445 (x : Key → ℝ) : Integer.Sparse.eval row16445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16445, Integer.Sparse.eval_collectBalanced, rawRowCheck16445]

def rawRow16446 : Integer.Sparse Key := [(key2136, 4), (key2263, 4), (key2049, 4), (key2171, -4), (key2021, -4), (key2074, -4), (key2136, -4), (key2016, -4), (key2049, -4), (key2021, 12)]

theorem rawRowCheck16446 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form9 = rawRow16446 := by decide +kernel

def row16446 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16446 : row16446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16446 := by decide +kernel

theorem rowEval16446 (x : Key → ℝ) : Integer.Sparse.eval row16446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16446, Integer.Sparse.eval_collectBalanced, rawRowCheck16446]

def rawRow16447 : Integer.Sparse Key := [(key2263, 4), (key2049, 4), (key2136, 4), (key2074, -4), (key2171, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2016, -4), (key2021, 12)]

theorem rawRowCheck16447 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form9 = rawRow16447 := by decide +kernel

def row16447 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16447 : row16447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16447 := by decide +kernel

theorem rowEval16447 (x : Key → ℝ) : Integer.Sparse.eval row16447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16447, Integer.Sparse.eval_collectBalanced, rawRowCheck16447]

def rawRow16448 : Integer.Sparse Key := [(key2263, 4), (key2136, 4), (key2049, 4), (key2171, -4), (key2074, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2016, -4), (key2021, 12)]

theorem rawRowCheck16448 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form9 = rawRow16448 := by decide +kernel

def row16448 : Integer.Sparse Key := [(key2016, -4), (key2021, 8), (key2074, -4), (key2171, -4), (key2263, 4)]

theorem rowCheck16448 : row16448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16448 := by decide +kernel

theorem rowEval16448 (x : Key → ℝ) : Integer.Sparse.eval row16448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16448, Integer.Sparse.eval_collectBalanced, rawRowCheck16448]

def rawRow16449 : Integer.Sparse Key := [(key2074, 4), (key2171, 4), (key2263, 4), (key2021, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2016, 12)]

theorem rawRowCheck16449 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form9 = rawRow16449 := by decide +kernel

def row16449 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

theorem rowCheck16449 : row16449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16449 := by decide +kernel

theorem rowEval16449 (x : Key → ℝ) : Integer.Sparse.eval row16449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16449, Integer.Sparse.eval_collectBalanced, rawRowCheck16449]

def rawRow16450 : Integer.Sparse Key := [(key2074, 4), (key2263, 4), (key2171, 4), (key2049, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2016, 12)]

theorem rawRowCheck16450 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form9 = rawRow16450 := by decide +kernel

def row16450 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

theorem rowCheck16450 : row16450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16450 := by decide +kernel

theorem rowEval16450 (x : Key → ℝ) : Integer.Sparse.eval row16450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16450, Integer.Sparse.eval_collectBalanced, rawRowCheck16450]

def rawRow16451 : Integer.Sparse Key := [(key2171, 4), (key2074, 4), (key2263, 4), (key2021, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2016, 12)]

theorem rawRowCheck16451 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form9 = rawRow16451 := by decide +kernel

def row16451 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

theorem rowCheck16451 : row16451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16451 := by decide +kernel

theorem rowEval16451 (x : Key → ℝ) : Integer.Sparse.eval row16451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck16451, Integer.Sparse.eval_collectBalanced, rawRowCheck16451]

def rawRow16452 : Integer.Sparse Key := [(key2171, 4), (key2263, 4), (key2074, 4), (key2136, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2016, 12)]

theorem rawRowCheck16452 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form9 = rawRow16452 := by decide +kernel

def row16452 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

theorem rowCheck16452 : row16452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16452 := by decide +kernel

theorem rowEval16452 (x : Key → ℝ) : Integer.Sparse.eval row16452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16452, Integer.Sparse.eval_collectBalanced, rawRowCheck16452]

def rawRow16453 : Integer.Sparse Key := [(key2263, 4), (key2074, 4), (key2171, 4), (key2049, -4), (key2136, -4), (key2021, -4), (key2049, -4), (key2136, -4), (key2021, -4), (key2016, 12)]

theorem rawRowCheck16453 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form9 = rawRow16453 := by decide +kernel

def row16453 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

theorem rowCheck16453 : row16453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16453 := by decide +kernel

theorem rowEval16453 (x : Key → ℝ) : Integer.Sparse.eval row16453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck16453, Integer.Sparse.eval_collectBalanced, rawRowCheck16453]

def rawRow16454 : Integer.Sparse Key := [(key2263, 4), (key2171, 4), (key2074, 4), (key2136, -4), (key2049, -4), (key2021, -4), (key2136, -4), (key2049, -4), (key2021, -4), (key2016, 12)]

theorem rawRowCheck16454 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form9 = rawRow16454 := by decide +kernel

def row16454 : Integer.Sparse Key := [(key2016, 12), (key2021, -8), (key2049, -8), (key2074, 4), (key2136, -8), (key2171, 4), (key2263, 4)]

theorem rowCheck16454 : row16454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16454 := by decide +kernel

theorem rowEval16454 (x : Key → ℝ) : Integer.Sparse.eval row16454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck16454, Integer.Sparse.eval_collectBalanced, rawRowCheck16454]

def rawRow16455 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key2992, 2), (key2992, 2), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1)]

theorem rawRowCheck16455 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form10 = rawRow16455 := by decide +kernel

def row16455 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

theorem rowCheck16455 : row16455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16455 := by decide +kernel

theorem rowEval16455 (x : Key → ℝ) : Integer.Sparse.eval row16455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16455, Integer.Sparse.eval_collectBalanced, rawRowCheck16455]

def rawRow16456 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key2992, 2), (key2640, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1)]

theorem rawRowCheck16456 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form10 = rawRow16456 := by decide +kernel

def row16456 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

theorem rowCheck16456 : row16456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16456 := by decide +kernel

theorem rowEval16456 (x : Key → ℝ) : Integer.Sparse.eval row16456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16456, Integer.Sparse.eval_collectBalanced, rawRowCheck16456]

def rawRow16457 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2992, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1)]

theorem rawRowCheck16457 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form10 = rawRow16457 := by decide +kernel

def row16457 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

theorem rowCheck16457 : row16457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16457 := by decide +kernel

theorem rowEval16457 (x : Key → ℝ) : Integer.Sparse.eval row16457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16457, Integer.Sparse.eval_collectBalanced, rawRowCheck16457]

def rawRow16458 : Integer.Sparse Key := [(key2616, -1), (key2619, -1), (key2809, -1), (key2832, -1), (key2951, -1), (key2961, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2640, -1), (key2642, -1), (key2860, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2632, 2), (key2642, 2), (key2706, 2), (key2729, 2), (key2977, 2), (key2984, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1), (key2654, 2), (key2898, 2), (key2913, 2), (key2649, -1), (key2654, -1), (key2738, -1), (key2748, -1), (key2898, -1), (key2905, -1)]

theorem rawRowCheck16458 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form10 = rawRow16458 := by decide +kernel

def row16458 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16458 : row16458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16458 := by decide +kernel

theorem rowEval16458 (x : Key → ℝ) : Integer.Sparse.eval row16458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16458, Integer.Sparse.eval_collectBalanced, rawRowCheck16458]

def rawRow16459 : Integer.Sparse Key := [(key2619, -1), (key2616, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2951, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2642, -1), (key2640, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2977, -1), (key2642, 2), (key2632, 2), (key2729, 2), (key2706, 2), (key2984, 2), (key2977, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1), (key2654, 2), (key2913, 2), (key2898, 2), (key2654, -1), (key2649, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2898, -1)]

theorem rawRowCheck16459 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form10 = rawRow16459 := by decide +kernel

def row16459 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16459 : row16459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16459 := by decide +kernel

theorem rowEval16459 (x : Key → ℝ) : Integer.Sparse.eval row16459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16459, Integer.Sparse.eval_collectBalanced, rawRowCheck16459]

def rawRow16460 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2860, -1), (key2977, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2706, 2), (key2977, 2), (key2632, 2), (key2984, 2), (key2642, 2), (key2729, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2898, 2), (key2654, 2), (key2913, 2), (key2738, -1), (key2898, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2748, -1)]

theorem rawRowCheck16460 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form10 = rawRow16460 := by decide +kernel

def row16460 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16460 : row16460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16460 := by decide +kernel

theorem rowEval16460 (x : Key → ℝ) : Integer.Sparse.eval row16460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16460, Integer.Sparse.eval_collectBalanced, rawRowCheck16460]

def rawRow16461 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2832, -1), (key2619, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2977, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2883, -1), (key2642, -1), (key2977, 2), (key2706, 2), (key2984, 2), (key2632, 2), (key2729, 2), (key2642, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1), (key2898, 2), (key2913, 2), (key2654, 2), (key2898, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2748, -1), (key2654, -1)]

theorem rawRowCheck16461 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form10 = rawRow16461 := by decide +kernel

def row16461 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16461 : row16461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16461 := by decide +kernel

theorem rowEval16461 (x : Key → ℝ) : Integer.Sparse.eval row16461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16461, Integer.Sparse.eval_collectBalanced, rawRowCheck16461]

def rawRow16462 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2616, -1), (key2809, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2883, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2640, -1), (key2860, -1), (key2729, 2), (key2984, 2), (key2642, 2), (key2977, 2), (key2632, 2), (key2706, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1), (key2913, 2), (key2654, 2), (key2898, 2), (key2748, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2649, -1), (key2738, -1)]

theorem rawRowCheck16462 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form10 = rawRow16462 := by decide +kernel

def row16462 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16462 : row16462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16462 := by decide +kernel

theorem rowEval16462 (x : Key → ℝ) : Integer.Sparse.eval row16462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16462, Integer.Sparse.eval_collectBalanced, rawRowCheck16462]

def rawRow16463 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2951, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2992, -1), (key2883, -1), (key2977, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2984, 2), (key2729, 2), (key2977, 2), (key2642, 2), (key2706, 2), (key2632, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2913, 2), (key2898, 2), (key2654, 2), (key2905, -1), (key2748, -1), (key2898, -1), (key2654, -1), (key2738, -1), (key2649, -1)]

theorem rawRowCheck16463 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form10 = rawRow16463 := by decide +kernel

def row16463 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16463 : row16463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16463 := by decide +kernel

theorem rowEval16463 (x : Key → ℝ) : Integer.Sparse.eval row16463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16463, Integer.Sparse.eval_collectBalanced, rawRowCheck16463]

def rawRow16464 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key2992, 2), (key2992, 2), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1)]

theorem rawRowCheck16464 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form10 = rawRow16464 := by decide +kernel

def row16464 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

theorem rowCheck16464 : row16464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16464 := by decide +kernel

theorem rowEval16464 (x : Key → ℝ) : Integer.Sparse.eval row16464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16464, Integer.Sparse.eval_collectBalanced, rawRowCheck16464]

def rawRow16465 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key2992, 2), (key2640, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1)]

theorem rawRowCheck16465 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form10 = rawRow16465 := by decide +kernel

def row16465 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

theorem rowCheck16465 : row16465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16465 := by decide +kernel

theorem rowEval16465 (x : Key → ℝ) : Integer.Sparse.eval row16465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16465, Integer.Sparse.eval_collectBalanced, rawRowCheck16465]

def rawRow16466 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2992, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1)]

theorem rawRowCheck16466 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form10 = rawRow16466 := by decide +kernel

def row16466 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

theorem rowCheck16466 : row16466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16466 := by decide +kernel

theorem rowEval16466 (x : Key → ℝ) : Integer.Sparse.eval row16466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16466, Integer.Sparse.eval_collectBalanced, rawRowCheck16466]

def rawRow16467 : Integer.Sparse Key := [(key2632, -1), (key2649, -1), (key2786, -1), (key2905, -1), (key2939, -1), (key2984, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2913, -1), (key2944, -1), (key2992, -1), (key2616, 2), (key2654, 2), (key2671, 2), (key2748, 2), (key2944, 2), (key2961, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1), (key2642, 2), (key2796, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2729, -1), (key2796, -1), (key2832, -1)]

theorem rawRowCheck16467 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form10 = rawRow16467 := by decide +kernel

def row16467 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16467 : row16467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16467 := by decide +kernel

theorem rowEval16467 (x : Key → ℝ) : Integer.Sparse.eval row16467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16467, Integer.Sparse.eval_collectBalanced, rawRowCheck16467]

def rawRow16468 : Integer.Sparse Key := [(key2649, -1), (key2632, -1), (key2905, -1), (key2786, -1), (key2984, -1), (key2939, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2654, -1), (key2640, -1), (key2913, -1), (key2794, -1), (key2992, -1), (key2944, -1), (key2654, 2), (key2616, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2944, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1), (key2642, 2), (key2883, 2), (key2796, 2), (key2642, -1), (key2619, -1), (key2729, -1), (key2674, -1), (key2832, -1), (key2796, -1)]

theorem rawRowCheck16468 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form10 = rawRow16468 := by decide +kernel

def row16468 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16468 : row16468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16468 := by decide +kernel

theorem rowEval16468 (x : Key → ℝ) : Integer.Sparse.eval row16468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16468, Integer.Sparse.eval_collectBalanced, rawRowCheck16468]

def rawRow16469 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2794, -1), (key2944, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2671, 2), (key2944, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2796, 2), (key2642, 2), (key2883, 2), (key2674, -1), (key2796, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2729, -1)]

theorem rawRowCheck16469 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form10 = rawRow16469 := by decide +kernel

def row16469 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16469 : row16469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16469 := by decide +kernel

theorem rowEval16469 (x : Key → ℝ) : Integer.Sparse.eval row16469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16469, Integer.Sparse.eval_collectBalanced, rawRowCheck16469]

def rawRow16470 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2905, -1), (key2649, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2944, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2913, -1), (key2654, -1), (key2944, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2748, 2), (key2654, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1), (key2796, 2), (key2883, 2), (key2642, 2), (key2796, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2729, -1), (key2642, -1)]

theorem rawRowCheck16470 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form10 = rawRow16470 := by decide +kernel

def row16470 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16470 : row16470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16470 := by decide +kernel

theorem rowEval16470 (x : Key → ℝ) : Integer.Sparse.eval row16470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16470, Integer.Sparse.eval_collectBalanced, rawRowCheck16470]

def rawRow16471 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2632, -1), (key2786, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2913, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2640, -1), (key2794, -1), (key2748, 2), (key2961, 2), (key2654, 2), (key2944, 2), (key2616, 2), (key2671, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1), (key2883, 2), (key2642, 2), (key2796, 2), (key2729, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2619, -1), (key2674, -1)]

theorem rawRowCheck16471 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form10 = rawRow16471 := by decide +kernel

def row16471 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16471 : row16471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16471 := by decide +kernel

theorem rowEval16471 (x : Key → ℝ) : Integer.Sparse.eval row16471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16471, Integer.Sparse.eval_collectBalanced, rawRowCheck16471]

def rawRow16472 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2939, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2992, -1), (key2913, -1), (key2944, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2961, 2), (key2748, 2), (key2944, 2), (key2654, 2), (key2671, 2), (key2616, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2883, 2), (key2796, 2), (key2642, 2), (key2832, -1), (key2729, -1), (key2796, -1), (key2642, -1), (key2674, -1), (key2619, -1)]

theorem rawRowCheck16472 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form10 = rawRow16472 := by decide +kernel

def row16472 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16472 : row16472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16472 := by decide +kernel

theorem rowEval16472 (x : Key → ℝ) : Integer.Sparse.eval row16472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16472, Integer.Sparse.eval_collectBalanced, rawRowCheck16472]

def rawRow16473 : Integer.Sparse Key := [(key2640, -1), (key2642, -1), (key2860, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2654, 2), (key2898, 2), (key2913, 2), (key2616, -1), (key2619, -1), (key2809, -1), (key2832, -1), (key2951, -1), (key2961, -1), (key2632, 2), (key2642, 2), (key2706, 2), (key2729, 2), (key2977, 2), (key2984, 2), (key2649, -1), (key2654, -1), (key2738, -1), (key2748, -1), (key2898, -1), (key2905, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1)]

theorem rawRowCheck16473 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form10 = rawRow16473 := by decide +kernel

def row16473 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16473 : row16473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16473 := by decide +kernel

theorem rowEval16473 (x : Key → ℝ) : Integer.Sparse.eval row16473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16473, Integer.Sparse.eval_collectBalanced, rawRowCheck16473]

def rawRow16474 : Integer.Sparse Key := [(key2642, -1), (key2640, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2977, -1), (key2654, 2), (key2913, 2), (key2898, 2), (key2619, -1), (key2616, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2951, -1), (key2642, 2), (key2632, 2), (key2729, 2), (key2706, 2), (key2984, 2), (key2977, 2), (key2654, -1), (key2649, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2898, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1)]

theorem rawRowCheck16474 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form10 = rawRow16474 := by decide +kernel

def row16474 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16474 : row16474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16474 := by decide +kernel

theorem rowEval16474 (x : Key → ℝ) : Integer.Sparse.eval row16474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16474, Integer.Sparse.eval_collectBalanced, rawRowCheck16474]

def rawRow16475 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2898, 2), (key2654, 2), (key2913, 2), (key2809, -1), (key2951, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2706, 2), (key2977, 2), (key2632, 2), (key2984, 2), (key2642, 2), (key2729, 2), (key2738, -1), (key2898, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2748, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1)]

theorem rawRowCheck16475 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form10 = rawRow16475 := by decide +kernel

def row16475 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16475 : row16475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16475 := by decide +kernel

theorem rowEval16475 (x : Key → ℝ) : Integer.Sparse.eval row16475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16475, Integer.Sparse.eval_collectBalanced, rawRowCheck16475]

def rawRow16476 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2883, -1), (key2642, -1), (key2898, 2), (key2913, 2), (key2654, 2), (key2951, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2832, -1), (key2619, -1), (key2977, 2), (key2706, 2), (key2984, 2), (key2632, 2), (key2729, 2), (key2642, 2), (key2898, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2748, -1), (key2654, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1)]

theorem rawRowCheck16476 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form10 = rawRow16476 := by decide +kernel

def row16476 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16476 : row16476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16476 := by decide +kernel

theorem rowEval16476 (x : Key → ℝ) : Integer.Sparse.eval row16476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16476, Integer.Sparse.eval_collectBalanced, rawRowCheck16476]

def rawRow16477 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2640, -1), (key2860, -1), (key2913, 2), (key2654, 2), (key2898, 2), (key2832, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2616, -1), (key2809, -1), (key2729, 2), (key2984, 2), (key2642, 2), (key2977, 2), (key2632, 2), (key2706, 2), (key2748, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2649, -1), (key2738, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1)]

theorem rawRowCheck16477 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form10 = rawRow16477 := by decide +kernel

def row16477 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16477 : row16477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16477 := by decide +kernel

theorem rowEval16477 (x : Key → ℝ) : Integer.Sparse.eval row16477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16477, Integer.Sparse.eval_collectBalanced, rawRowCheck16477]

def rawRow16478 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2977, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2913, 2), (key2898, 2), (key2654, 2), (key2961, -1), (key2832, -1), (key2951, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2984, 2), (key2729, 2), (key2977, 2), (key2642, 2), (key2706, 2), (key2632, 2), (key2905, -1), (key2748, -1), (key2898, -1), (key2654, -1), (key2738, -1), (key2649, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1)]

theorem rawRowCheck16478 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form10 = rawRow16478 := by decide +kernel

def row16478 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

theorem rowCheck16478 : row16478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16478 := by decide +kernel

theorem rowEval16478 (x : Key → ℝ) : Integer.Sparse.eval row16478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16478, Integer.Sparse.eval_collectBalanced, rawRowCheck16478]

def rawRow16479 : Integer.Sparse Key := [(key2640, -1), (key2654, -1), (key2794, -1), (key2913, -1), (key2944, -1), (key2992, -1), (key2642, 2), (key2796, 2), (key2883, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2905, -1), (key2939, -1), (key2984, -1), (key2616, 2), (key2654, 2), (key2671, 2), (key2748, 2), (key2944, 2), (key2961, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2729, -1), (key2796, -1), (key2832, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1)]

theorem rawRowCheck16479 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form10 = rawRow16479 := by decide +kernel

def row16479 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16479 : row16479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16479 := by decide +kernel

theorem rowEval16479 (x : Key → ℝ) : Integer.Sparse.eval row16479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16479, Integer.Sparse.eval_collectBalanced, rawRowCheck16479]

def rawRow16480 : Integer.Sparse Key := [(key2654, -1), (key2640, -1), (key2913, -1), (key2794, -1), (key2992, -1), (key2944, -1), (key2642, 2), (key2883, 2), (key2796, 2), (key2649, -1), (key2632, -1), (key2905, -1), (key2786, -1), (key2984, -1), (key2939, -1), (key2654, 2), (key2616, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2944, 2), (key2642, -1), (key2619, -1), (key2729, -1), (key2674, -1), (key2832, -1), (key2796, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1)]

theorem rawRowCheck16480 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form10 = rawRow16480 := by decide +kernel

def row16480 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16480 : row16480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16480 := by decide +kernel

theorem rowEval16480 (x : Key → ℝ) : Integer.Sparse.eval row16480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16480, Integer.Sparse.eval_collectBalanced, rawRowCheck16480]

def rawRow16481 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2796, 2), (key2642, 2), (key2883, 2), (key2786, -1), (key2939, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2671, 2), (key2944, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2674, -1), (key2796, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1)]

theorem rawRowCheck16481 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form10 = rawRow16481 := by decide +kernel

def row16481 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16481 : row16481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16481 := by decide +kernel

theorem rowEval16481 (x : Key → ℝ) : Integer.Sparse.eval row16481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16481, Integer.Sparse.eval_collectBalanced, rawRowCheck16481]

def rawRow16482 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2913, -1), (key2654, -1), (key2796, 2), (key2883, 2), (key2642, 2), (key2939, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2905, -1), (key2649, -1), (key2944, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2748, 2), (key2654, 2), (key2796, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2729, -1), (key2642, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1)]

theorem rawRowCheck16482 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form10 = rawRow16482 := by decide +kernel

def row16482 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16482 : row16482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16482 := by decide +kernel

theorem rowEval16482 (x : Key → ℝ) : Integer.Sparse.eval row16482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16482, Integer.Sparse.eval_collectBalanced, rawRowCheck16482]

def rawRow16483 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2640, -1), (key2794, -1), (key2883, 2), (key2642, 2), (key2796, 2), (key2905, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2632, -1), (key2786, -1), (key2748, 2), (key2961, 2), (key2654, 2), (key2944, 2), (key2616, 2), (key2671, 2), (key2729, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2619, -1), (key2674, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1)]

theorem rawRowCheck16483 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form10 = rawRow16483 := by decide +kernel

def row16483 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16483 : row16483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16483 := by decide +kernel

theorem rowEval16483 (x : Key → ℝ) : Integer.Sparse.eval row16483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16483, Integer.Sparse.eval_collectBalanced, rawRowCheck16483]

def rawRow16484 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2944, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2883, 2), (key2796, 2), (key2642, 2), (key2984, -1), (key2905, -1), (key2939, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2961, 2), (key2748, 2), (key2944, 2), (key2654, 2), (key2671, 2), (key2616, 2), (key2832, -1), (key2729, -1), (key2796, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1)]

theorem rawRowCheck16484 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form10 = rawRow16484 := by decide +kernel

def row16484 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

theorem rowCheck16484 : row16484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16484 := by decide +kernel

theorem rowEval16484 (x : Key → ℝ) : Integer.Sparse.eval row16484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16484, Integer.Sparse.eval_collectBalanced, rawRowCheck16484]

def rawRow16485 : Integer.Sparse Key := [(key2642, -1), (key2654, -1), (key2796, -1), (key2898, -1), (key2944, -1), (key2977, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2642, -1), (key2654, -1), (key2796, -1), (key2898, -1), (key2944, -1), (key2977, -1), (key2619, 2), (key2649, 2), (key2674, 2), (key2738, 2), (key2939, 2), (key2951, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1)]

theorem rawRowCheck16485 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form10 = rawRow16485 := by decide +kernel

def row16485 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

theorem rowCheck16485 : row16485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16485 := by decide +kernel

theorem rowEval16485 (x : Key → ℝ) : Integer.Sparse.eval row16485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16485, Integer.Sparse.eval_collectBalanced, rawRowCheck16485]

def rawRow16486 : Integer.Sparse Key := [(key2654, -1), (key2642, -1), (key2898, -1), (key2796, -1), (key2977, -1), (key2944, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2654, -1), (key2642, -1), (key2898, -1), (key2796, -1), (key2977, -1), (key2944, -1), (key2649, 2), (key2619, 2), (key2738, 2), (key2674, 2), (key2951, 2), (key2939, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1)]

theorem rawRowCheck16486 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form10 = rawRow16486 := by decide +kernel

def row16486 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

theorem rowCheck16486 : row16486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16486 := by decide +kernel

theorem rowEval16486 (x : Key → ℝ) : Integer.Sparse.eval row16486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16486, Integer.Sparse.eval_collectBalanced, rawRowCheck16486]

def rawRow16487 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2642, -1), (key2977, -1), (key2654, -1), (key2898, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2796, -1), (key2944, -1), (key2642, -1), (key2977, -1), (key2654, -1), (key2898, -1), (key2674, 2), (key2939, 2), (key2619, 2), (key2951, 2), (key2649, 2), (key2738, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1)]

theorem rawRowCheck16487 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form10 = rawRow16487 := by decide +kernel

def row16487 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

theorem rowCheck16487 : row16487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16487 := by decide +kernel

theorem rowEval16487 (x : Key → ℝ) : Integer.Sparse.eval row16487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck16487, Integer.Sparse.eval_collectBalanced, rawRowCheck16487]

def rawRow16488 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2977, -1), (key2642, -1), (key2898, -1), (key2654, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2944, -1), (key2796, -1), (key2977, -1), (key2642, -1), (key2898, -1), (key2654, -1), (key2939, 2), (key2674, 2), (key2951, 2), (key2619, 2), (key2738, 2), (key2649, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1)]

theorem rawRowCheck16488 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form10 = rawRow16488 := by decide +kernel

def row16488 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

theorem rowCheck16488 : row16488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16488 := by decide +kernel

theorem rowEval16488 (x : Key → ℝ) : Integer.Sparse.eval row16488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16488, Integer.Sparse.eval_collectBalanced, rawRowCheck16488]

def rawRow16489 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2654, -1), (key2944, -1), (key2642, -1), (key2796, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2898, -1), (key2977, -1), (key2654, -1), (key2944, -1), (key2642, -1), (key2796, -1), (key2738, 2), (key2951, 2), (key2649, 2), (key2939, 2), (key2619, 2), (key2674, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1)]

theorem rawRowCheck16489 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form10 = rawRow16489 := by decide +kernel

def row16489 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

theorem rowCheck16489 : row16489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16489 := by decide +kernel

theorem rowEval16489 (x : Key → ℝ) : Integer.Sparse.eval row16489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16489, Integer.Sparse.eval_collectBalanced, rawRowCheck16489]

def rawRow16490 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2944, -1), (key2654, -1), (key2796, -1), (key2642, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2977, -1), (key2898, -1), (key2944, -1), (key2654, -1), (key2796, -1), (key2642, -1), (key2951, 2), (key2738, 2), (key2939, 2), (key2649, 2), (key2674, 2), (key2619, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1)]

theorem rawRowCheck16490 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form10 = rawRow16490 := by decide +kernel

def row16490 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

theorem rowCheck16490 : row16490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16490 := by decide +kernel

theorem rowEval16490 (x : Key → ℝ) : Integer.Sparse.eval row16490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -1, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck16490, Integer.Sparse.eval_collectBalanced, rawRowCheck16490]

def rawRow16491 : Integer.Sparse Key := [(key1489, -2), (key1489, -2), (key1518, -2), (key1495, 6), (key1715, -2), (key1715, -2), (key1746, -2), (key1363, 2), (key1363, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1879, 2), (key1369, -2), (key1864, -2), (key1864, -2), (key1727, 6), (key1378, -2), (key1869, -2), (key1869, -2)]

theorem rawRowCheck16491 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form11 = rawRow16491 := by decide +kernel

def row16491 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

theorem rowCheck16491 : row16491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16491 := by decide +kernel

theorem rowEval16491 (x : Key → ℝ) : Integer.Sparse.eval row16491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16491, Integer.Sparse.eval_collectBalanced, rawRowCheck16491]

def rawRow16492 : Integer.Sparse Key := [(key1489, -2), (key1518, -2), (key1489, -2), (key1495, 6), (key1715, -2), (key1746, -2), (key1715, -2), (key1860, 2), (key1879, 2), (key1363, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1864, -2), (key1369, -2), (key1864, -2), (key1727, 6), (key1869, -2), (key1378, -2), (key1869, -2)]

theorem rawRowCheck16492 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form11 = rawRow16492 := by decide +kernel

def row16492 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

theorem rowCheck16492 : row16492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16492 := by decide +kernel

theorem rowEval16492 (x : Key → ℝ) : Integer.Sparse.eval row16492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16492, Integer.Sparse.eval_collectBalanced, rawRowCheck16492]

def rawRow16493 : Integer.Sparse Key := [(key1518, -2), (key1489, -2), (key1489, -2), (key1495, 6), (key1746, -2), (key1715, -2), (key1715, -2), (key1879, 2), (key1860, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1363, 2), (key1864, -2), (key1864, -2), (key1369, -2), (key1727, 6), (key1869, -2), (key1869, -2), (key1378, -2)]

theorem rawRowCheck16493 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form11 = rawRow16493 := by decide +kernel

def row16493 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

theorem rowCheck16493 : row16493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16493 := by decide +kernel

theorem rowEval16493 (x : Key → ℝ) : Integer.Sparse.eval row16493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16493, Integer.Sparse.eval_collectBalanced, rawRowCheck16493]

def rawRow16494 : Integer.Sparse Key := [(key1489, -2), (key1495, -2), (key1518, -2), (key1489, 6), (key1860, -2), (key1864, -2), (key1879, -2), (key1363, 2), (key1369, 2), (key1715, 2), (key1864, 2), (key1746, 2), (key1879, 2), (key1363, -2), (key1715, -2), (key1860, -2), (key1869, 6), (key1378, -2), (key1727, -2), (key1869, -2)]

theorem rawRowCheck16494 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form11 = rawRow16494 := by decide +kernel

def row16494 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16494 : row16494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16494 := by decide +kernel

theorem rowEval16494 (x : Key → ℝ) : Integer.Sparse.eval row16494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16494, Integer.Sparse.eval_collectBalanced, rawRowCheck16494]

def rawRow16495 : Integer.Sparse Key := [(key1495, -2), (key1489, -2), (key1518, -2), (key1489, 6), (key1864, -2), (key1860, -2), (key1879, -2), (key1369, 2), (key1363, 2), (key1864, 2), (key1715, 2), (key1879, 2), (key1746, 2), (key1363, -2), (key1860, -2), (key1715, -2), (key1869, 6), (key1378, -2), (key1869, -2), (key1727, -2)]

theorem rawRowCheck16495 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form11 = rawRow16495 := by decide +kernel

def row16495 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16495 : row16495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16495 := by decide +kernel

theorem rowEval16495 (x : Key → ℝ) : Integer.Sparse.eval row16495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16495, Integer.Sparse.eval_collectBalanced, rawRowCheck16495]

def rawRow16496 : Integer.Sparse Key := [(key1489, -2), (key1518, -2), (key1495, -2), (key1489, 6), (key1860, -2), (key1879, -2), (key1864, -2), (key1715, 2), (key1746, 2), (key1363, 2), (key1879, 2), (key1369, 2), (key1864, 2), (key1715, -2), (key1363, -2), (key1860, -2), (key1869, 6), (key1727, -2), (key1378, -2), (key1869, -2)]

theorem rawRowCheck16496 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form11 = rawRow16496 := by decide +kernel

def row16496 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16496 : row16496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16496 := by decide +kernel

theorem rowEval16496 (x : Key → ℝ) : Integer.Sparse.eval row16496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16496, Integer.Sparse.eval_collectBalanced, rawRowCheck16496]

def rawRow16497 : Integer.Sparse Key := [(key1518, -2), (key1489, -2), (key1495, -2), (key1489, 6), (key1879, -2), (key1860, -2), (key1864, -2), (key1746, 2), (key1715, 2), (key1879, 2), (key1363, 2), (key1864, 2), (key1369, 2), (key1715, -2), (key1860, -2), (key1363, -2), (key1869, 6), (key1727, -2), (key1869, -2), (key1378, -2)]

theorem rawRowCheck16497 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form11 = rawRow16497 := by decide +kernel

def row16497 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16497 : row16497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16497 := by decide +kernel

theorem rowEval16497 (x : Key → ℝ) : Integer.Sparse.eval row16497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16497, Integer.Sparse.eval_collectBalanced, rawRowCheck16497]

def rawRow16498 : Integer.Sparse Key := [(key1495, -2), (key1518, -2), (key1489, -2), (key1489, 6), (key1864, -2), (key1879, -2), (key1860, -2), (key1864, 2), (key1879, 2), (key1369, 2), (key1746, 2), (key1363, 2), (key1715, 2), (key1860, -2), (key1363, -2), (key1715, -2), (key1869, 6), (key1869, -2), (key1378, -2), (key1727, -2)]

theorem rawRowCheck16498 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form11 = rawRow16498 := by decide +kernel

def row16498 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16498 : row16498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16498 := by decide +kernel

theorem rowEval16498 (x : Key → ℝ) : Integer.Sparse.eval row16498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16498, Integer.Sparse.eval_collectBalanced, rawRowCheck16498]

def rawRow16499 : Integer.Sparse Key := [(key1518, -2), (key1495, -2), (key1489, -2), (key1489, 6), (key1879, -2), (key1864, -2), (key1860, -2), (key1879, 2), (key1864, 2), (key1746, 2), (key1369, 2), (key1715, 2), (key1363, 2), (key1860, -2), (key1715, -2), (key1363, -2), (key1869, 6), (key1869, -2), (key1727, -2), (key1378, -2)]

theorem rawRowCheck16499 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form11 = rawRow16499 := by decide +kernel

def row16499 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16499 : row16499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16499 := by decide +kernel

theorem rowEval16499 (x : Key → ℝ) : Integer.Sparse.eval row16499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16499, Integer.Sparse.eval_collectBalanced, rawRowCheck16499]

def rawRow16500 : Integer.Sparse Key := [(key1715, -2), (key1715, -2), (key1746, -2), (key1727, 6), (key1489, -2), (key1489, -2), (key1518, -2), (key1363, 2), (key1363, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1879, 2), (key1378, -2), (key1869, -2), (key1869, -2), (key1495, 6), (key1369, -2), (key1864, -2), (key1864, -2)]

theorem rawRowCheck16500 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form11 = rawRow16500 := by decide +kernel

def row16500 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

theorem rowCheck16500 : row16500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16500 := by decide +kernel

theorem rowEval16500 (x : Key → ℝ) : Integer.Sparse.eval row16500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16500, Integer.Sparse.eval_collectBalanced, rawRowCheck16500]

def rawRow16501 : Integer.Sparse Key := [(key1715, -2), (key1746, -2), (key1715, -2), (key1727, 6), (key1489, -2), (key1518, -2), (key1489, -2), (key1860, 2), (key1879, 2), (key1363, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1869, -2), (key1378, -2), (key1869, -2), (key1495, 6), (key1864, -2), (key1369, -2), (key1864, -2)]

theorem rawRowCheck16501 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form11 = rawRow16501 := by decide +kernel

def row16501 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

theorem rowCheck16501 : row16501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16501 := by decide +kernel

theorem rowEval16501 (x : Key → ℝ) : Integer.Sparse.eval row16501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16501, Integer.Sparse.eval_collectBalanced, rawRowCheck16501]

def rawRow16502 : Integer.Sparse Key := [(key1746, -2), (key1715, -2), (key1715, -2), (key1727, 6), (key1518, -2), (key1489, -2), (key1489, -2), (key1879, 2), (key1860, 2), (key1879, 2), (key1363, 2), (key1860, 2), (key1363, 2), (key1869, -2), (key1869, -2), (key1378, -2), (key1495, 6), (key1864, -2), (key1864, -2), (key1369, -2)]

theorem rawRowCheck16502 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form11 = rawRow16502 := by decide +kernel

def row16502 : Integer.Sparse Key := [(key1363, 4), (key1369, -2), (key1378, -2), (key1489, -4), (key1495, 6), (key1518, -2), (key1715, -4), (key1727, 6), (key1746, -2), (key1860, 4), (key1864, -4), (key1869, -4), (key1879, 4)]

theorem rowCheck16502 : row16502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16502 := by decide +kernel

theorem rowEval16502 (x : Key → ℝ) : Integer.Sparse.eval row16502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16502, Integer.Sparse.eval_collectBalanced, rawRowCheck16502]

def rawRow16503 : Integer.Sparse Key := [(key1715, -2), (key1727, -2), (key1746, -2), (key1715, 6), (key1860, -2), (key1869, -2), (key1879, -2), (key1363, 2), (key1378, 2), (key1489, 2), (key1869, 2), (key1518, 2), (key1879, 2), (key1363, -2), (key1489, -2), (key1860, -2), (key1864, 6), (key1369, -2), (key1495, -2), (key1864, -2)]

theorem rawRowCheck16503 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form11 = rawRow16503 := by decide +kernel

def row16503 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16503 : row16503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16503 := by decide +kernel

theorem rowEval16503 (x : Key → ℝ) : Integer.Sparse.eval row16503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16503, Integer.Sparse.eval_collectBalanced, rawRowCheck16503]

def rawRow16504 : Integer.Sparse Key := [(key1727, -2), (key1715, -2), (key1746, -2), (key1715, 6), (key1869, -2), (key1860, -2), (key1879, -2), (key1378, 2), (key1363, 2), (key1869, 2), (key1489, 2), (key1879, 2), (key1518, 2), (key1363, -2), (key1860, -2), (key1489, -2), (key1864, 6), (key1369, -2), (key1864, -2), (key1495, -2)]

theorem rawRowCheck16504 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form11 = rawRow16504 := by decide +kernel

def row16504 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16504 : row16504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16504 := by decide +kernel

theorem rowEval16504 (x : Key → ℝ) : Integer.Sparse.eval row16504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16504, Integer.Sparse.eval_collectBalanced, rawRowCheck16504]

def rawRow16505 : Integer.Sparse Key := [(key1715, -2), (key1746, -2), (key1727, -2), (key1715, 6), (key1860, -2), (key1879, -2), (key1869, -2), (key1489, 2), (key1518, 2), (key1363, 2), (key1879, 2), (key1378, 2), (key1869, 2), (key1489, -2), (key1363, -2), (key1860, -2), (key1864, 6), (key1495, -2), (key1369, -2), (key1864, -2)]

theorem rawRowCheck16505 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form11 = rawRow16505 := by decide +kernel

def row16505 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16505 : row16505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16505 := by decide +kernel

theorem rowEval16505 (x : Key → ℝ) : Integer.Sparse.eval row16505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16505, Integer.Sparse.eval_collectBalanced, rawRowCheck16505]

def rawRow16506 : Integer.Sparse Key := [(key1746, -2), (key1715, -2), (key1727, -2), (key1715, 6), (key1879, -2), (key1860, -2), (key1869, -2), (key1518, 2), (key1489, 2), (key1879, 2), (key1363, 2), (key1869, 2), (key1378, 2), (key1489, -2), (key1860, -2), (key1363, -2), (key1864, 6), (key1495, -2), (key1864, -2), (key1369, -2)]

theorem rawRowCheck16506 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form11 = rawRow16506 := by decide +kernel

def row16506 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16506 : row16506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16506 := by decide +kernel

theorem rowEval16506 (x : Key → ℝ) : Integer.Sparse.eval row16506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16506, Integer.Sparse.eval_collectBalanced, rawRowCheck16506]

def rawRow16507 : Integer.Sparse Key := [(key1727, -2), (key1746, -2), (key1715, -2), (key1715, 6), (key1869, -2), (key1879, -2), (key1860, -2), (key1869, 2), (key1879, 2), (key1378, 2), (key1518, 2), (key1363, 2), (key1489, 2), (key1860, -2), (key1363, -2), (key1489, -2), (key1864, 6), (key1864, -2), (key1369, -2), (key1495, -2)]

theorem rawRowCheck16507 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form11 = rawRow16507 := by decide +kernel

def row16507 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16507 : row16507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16507 := by decide +kernel

theorem rowEval16507 (x : Key → ℝ) : Integer.Sparse.eval row16507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16507, Integer.Sparse.eval_collectBalanced, rawRowCheck16507]

def rawRow16508 : Integer.Sparse Key := [(key1746, -2), (key1727, -2), (key1715, -2), (key1715, 6), (key1879, -2), (key1869, -2), (key1860, -2), (key1879, 2), (key1869, 2), (key1518, 2), (key1378, 2), (key1489, 2), (key1363, 2), (key1860, -2), (key1489, -2), (key1363, -2), (key1864, 6), (key1864, -2), (key1495, -2), (key1369, -2)]

theorem rawRowCheck16508 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form11 = rawRow16508 := by decide +kernel

def row16508 : Integer.Sparse Key := [(key1369, -2), (key1378, 2), (key1495, -2), (key1518, 2), (key1715, 4), (key1727, -2), (key1746, -2), (key1860, -4), (key1864, 4)]

theorem rowCheck16508 : row16508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16508 := by decide +kernel

theorem rowEval16508 (x : Key → ℝ) : Integer.Sparse.eval row16508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16508, Integer.Sparse.eval_collectBalanced, rawRowCheck16508]

def rawRow16509 : Integer.Sparse Key := [(key1860, -2), (key1864, -2), (key1879, -2), (key1869, 6), (key1489, -2), (key1495, -2), (key1518, -2), (key1363, 2), (key1369, 2), (key1715, 2), (key1864, 2), (key1746, 2), (key1879, 2), (key1378, -2), (key1727, -2), (key1869, -2), (key1489, 6), (key1363, -2), (key1715, -2), (key1860, -2)]

theorem rawRowCheck16509 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form11 = rawRow16509 := by decide +kernel

def row16509 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16509 : row16509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16509 := by decide +kernel

theorem rowEval16509 (x : Key → ℝ) : Integer.Sparse.eval row16509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16509, Integer.Sparse.eval_collectBalanced, rawRowCheck16509]

def rawRow16510 : Integer.Sparse Key := [(key1864, -2), (key1860, -2), (key1879, -2), (key1869, 6), (key1495, -2), (key1489, -2), (key1518, -2), (key1369, 2), (key1363, 2), (key1864, 2), (key1715, 2), (key1879, 2), (key1746, 2), (key1378, -2), (key1869, -2), (key1727, -2), (key1489, 6), (key1363, -2), (key1860, -2), (key1715, -2)]

theorem rawRowCheck16510 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form11 = rawRow16510 := by decide +kernel

def row16510 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16510 : row16510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16510 := by decide +kernel

theorem rowEval16510 (x : Key → ℝ) : Integer.Sparse.eval row16510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck16510, Integer.Sparse.eval_collectBalanced, rawRowCheck16510]

def rawRow16511 : Integer.Sparse Key := [(key1860, -2), (key1879, -2), (key1864, -2), (key1869, 6), (key1489, -2), (key1518, -2), (key1495, -2), (key1715, 2), (key1746, 2), (key1363, 2), (key1879, 2), (key1369, 2), (key1864, 2), (key1727, -2), (key1378, -2), (key1869, -2), (key1489, 6), (key1715, -2), (key1363, -2), (key1860, -2)]

theorem rawRowCheck16511 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form11 = rawRow16511 := by decide +kernel

def row16511 : Integer.Sparse Key := [(key1369, 2), (key1378, -2), (key1489, 4), (key1495, -2), (key1518, -2), (key1727, -2), (key1746, 2), (key1860, -4), (key1869, 4)]

theorem rowCheck16511 : row16511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16511 := by decide +kernel

theorem rowEval16511 (x : Key → ℝ) : Integer.Sparse.eval row16511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16511, Integer.Sparse.eval_collectBalanced, rawRowCheck16511]

end MUB6.Certificate.GramRows

end OAI
