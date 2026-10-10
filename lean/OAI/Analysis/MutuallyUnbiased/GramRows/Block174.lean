import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
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

def rawRow19200 : Integer.Sparse Key := [(key2369, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2431, 6), (key2497, 6), (key2497, 6)]

theorem rawRowCheck19200 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19200 := by decide +kernel

def row19200 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19200 : row19200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19200 := by decide +kernel

theorem rowEval19200 (x : Key → ℝ) : Integer.Sparse.eval row19200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19200, Integer.Sparse.eval_collectBalanced, rawRowCheck19200]

def rawRow19201 : Integer.Sparse Key := [(key2369, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2431, 6), (key2497, 6)]

theorem rawRowCheck19201 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19201 := by decide +kernel

def row19201 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19201 : row19201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19201 := by decide +kernel

theorem rowEval19201 (x : Key → ℝ) : Integer.Sparse.eval row19201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19201, Integer.Sparse.eval_collectBalanced, rawRowCheck19201]

def rawRow19202 : Integer.Sparse Key := [(key2384, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2497, 6), (key2497, 6), (key2497, 6), (key2431, 6)]

theorem rawRowCheck19202 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19202 := by decide +kernel

def row19202 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19202 : row19202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19202 := by decide +kernel

theorem rowEval19202 (x : Key → ℝ) : Integer.Sparse.eval row19202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19202, Integer.Sparse.eval_collectBalanced, rawRowCheck19202]

def rawRow19203 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2474, 6), (key2474, 6)]

theorem rawRowCheck19203 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19203 := by decide +kernel

def row19203 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19203 : row19203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19203 := by decide +kernel

theorem rowEval19203 (x : Key → ℝ) : Integer.Sparse.eval row19203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19203, Integer.Sparse.eval_collectBalanced, rawRowCheck19203]

def rawRow19204 : Integer.Sparse Key := [(key2397, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2384, 6), (key2474, 6), (key2474, 6)]

theorem rawRowCheck19204 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19204 := by decide +kernel

def row19204 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19204 : row19204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19204 := by decide +kernel

theorem rowEval19204 (x : Key → ℝ) : Integer.Sparse.eval row19204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19204, Integer.Sparse.eval_collectBalanced, rawRowCheck19204]

def rawRow19205 : Integer.Sparse Key := [(key2397, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2384, 6), (key2474, 6)]

theorem rawRowCheck19205 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19205 := by decide +kernel

def row19205 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19205 : row19205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19205 := by decide +kernel

theorem rowEval19205 (x : Key → ℝ) : Integer.Sparse.eval row19205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19205, Integer.Sparse.eval_collectBalanced, rawRowCheck19205]

def rawRow19206 : Integer.Sparse Key := [(key2431, 6), (key2397, 6), (key2397, 6), (key2397, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2474, 6), (key2474, 6), (key2474, 6), (key2384, 6)]

theorem rawRowCheck19206 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19206 := by decide +kernel

def row19206 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19206 : row19206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19206 := by decide +kernel

theorem rowEval19206 (x : Key → ℝ) : Integer.Sparse.eval row19206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19206, Integer.Sparse.eval_collectBalanced, rawRowCheck19206]

def rawRow19207 : Integer.Sparse Key := [(key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2369, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2497, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6)]

theorem rawRowCheck19207 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19207 := by decide +kernel

def row19207 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19207 : row19207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19207 := by decide +kernel

theorem rowEval19207 (x : Key → ℝ) : Integer.Sparse.eval row19207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19207, Integer.Sparse.eval_collectBalanced, rawRowCheck19207]

def rawRow19208 : Integer.Sparse Key := [(key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2384, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2431, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6)]

theorem rawRowCheck19208 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19208 := by decide +kernel

def row19208 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19208 : row19208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19208 := by decide +kernel

theorem rowEval19208 (x : Key → ℝ) : Integer.Sparse.eval row19208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19208, Integer.Sparse.eval_collectBalanced, rawRowCheck19208]

def rawRow19209 : Integer.Sparse Key := [(key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2384, 6), (key2369, 6), (key2369, 6), (key2474, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2397, 6), (key2497, 6), (key2497, 6), (key2431, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6)]

theorem rawRowCheck19209 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19209 := by decide +kernel

def row19209 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19209 : row19209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19209 := by decide +kernel

theorem rowEval19209 (x : Key → ℝ) : Integer.Sparse.eval row19209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19209, Integer.Sparse.eval_collectBalanced, rawRowCheck19209]

def rawRow19210 : Integer.Sparse Key := [(key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2397, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2474, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6)]

theorem rawRowCheck19210 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19210 := by decide +kernel

def row19210 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19210 : row19210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19210 := by decide +kernel

theorem rowEval19210 (x : Key → ℝ) : Integer.Sparse.eval row19210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19210, Integer.Sparse.eval_collectBalanced, rawRowCheck19210]

def rawRow19211 : Integer.Sparse Key := [(key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2397, 6), (key2431, 6), (key2397, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2474, 6), (key2384, 6), (key2474, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6)]

theorem rawRowCheck19211 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19211 := by decide +kernel

def row19211 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19211 : row19211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19211 := by decide +kernel

theorem rowEval19211 (x : Key → ℝ) : Integer.Sparse.eval row19211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19211, Integer.Sparse.eval_collectBalanced, rawRowCheck19211]

def rawRow19212 : Integer.Sparse Key := [(key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2431, 6), (key2397, 6), (key2397, 6), (key2497, 6), (key2463, 6), (key2497, 6), (key2369, 6), (key2463, 6), (key2369, 6), (key2474, 6), (key2474, 6), (key2384, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6)]

theorem rawRowCheck19212 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19212 := by decide +kernel

def row19212 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19212 : row19212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19212 := by decide +kernel

theorem rowEval19212 (x : Key → ℝ) : Integer.Sparse.eval row19212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19212, Integer.Sparse.eval_collectBalanced, rawRowCheck19212]

def rawRow19213 : Integer.Sparse Key := [(key2463, 6), (key2474, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2369, 6), (key2384, 6), (key2397, 6), (key2474, 6), (key2431, 6), (key2497, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2397, 6), (key2463, 6)]

theorem rawRowCheck19213 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form6 = rawRow19213 := by decide +kernel

def row19213 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19213 : row19213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19213 := by decide +kernel

theorem rowEval19213 (x : Key → ℝ) : Integer.Sparse.eval row19213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19213, Integer.Sparse.eval_collectBalanced, rawRowCheck19213]

def rawRow19214 : Integer.Sparse Key := [(key2474, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2384, 6), (key2369, 6), (key2474, 6), (key2397, 6), (key2497, 6), (key2431, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2397, 6)]

theorem rawRowCheck19214 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form6 = rawRow19214 := by decide +kernel

def row19214 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19214 : row19214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19214 := by decide +kernel

theorem rowEval19214 (x : Key → ℝ) : Integer.Sparse.eval row19214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19214, Integer.Sparse.eval_collectBalanced, rawRowCheck19214]

def rawRow19215 : Integer.Sparse Key := [(key2463, 6), (key2497, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2397, 6), (key2431, 6), (key2369, 6), (key2497, 6), (key2384, 6), (key2474, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2369, 6), (key2463, 6)]

theorem rawRowCheck19215 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form6 = rawRow19215 := by decide +kernel

def row19215 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19215 : row19215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19215 := by decide +kernel

theorem rowEval19215 (x : Key → ℝ) : Integer.Sparse.eval row19215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19215, Integer.Sparse.eval_collectBalanced, rawRowCheck19215]

def rawRow19216 : Integer.Sparse Key := [(key2497, 6), (key2463, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2431, 6), (key2397, 6), (key2497, 6), (key2369, 6), (key2474, 6), (key2384, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2463, 6), (key2369, 6)]

theorem rawRowCheck19216 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form6 = rawRow19216 := by decide +kernel

def row19216 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19216 : row19216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19216 := by decide +kernel

theorem rowEval19216 (x : Key → ℝ) : Integer.Sparse.eval row19216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19216, Integer.Sparse.eval_collectBalanced, rawRowCheck19216]

def rawRow19217 : Integer.Sparse Key := [(key2474, 6), (key2497, 6), (key2463, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2463, 6), (key2474, 6), (key2497, 6), (key2384, 6), (key2431, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2369, 6), (key2397, 6), (key2463, 6), (key2463, 6), (key2369, 6), (key2397, 6)]

theorem rawRowCheck19217 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form6 = rawRow19217 := by decide +kernel

def row19217 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19217 : row19217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19217 := by decide +kernel

theorem rowEval19217 (x : Key → ℝ) : Integer.Sparse.eval row19217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19217, Integer.Sparse.eval_collectBalanced, rawRowCheck19217]

def rawRow19218 : Integer.Sparse Key := [(key2497, 6), (key2474, 6), (key2463, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2463, 6), (key2497, 6), (key2474, 6), (key2431, 6), (key2384, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2397, 6), (key2369, 6), (key2463, 6), (key2463, 6), (key2397, 6), (key2369, 6)]

theorem rawRowCheck19218 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form6 = rawRow19218 := by decide +kernel

def row19218 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

theorem rowCheck19218 : row19218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19218 := by decide +kernel

theorem rowEval19218 (x : Key → ℝ) : Integer.Sparse.eval row19218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19218, Integer.Sparse.eval_collectBalanced, rawRowCheck19218]

def rawRow19219 : Integer.Sparse Key := [(key2606, 6), (key2622, 6), (key2622, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2776, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6)]

theorem rawRowCheck19219 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19219 := by decide +kernel

def row19219 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19219 : row19219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19219 := by decide +kernel

theorem rowEval19219 (x : Key → ℝ) : Integer.Sparse.eval row19219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19219, Integer.Sparse.eval_collectBalanced, rawRowCheck19219]

def rawRow19220 : Integer.Sparse Key := [(key2622, 6), (key2606, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6)]

theorem rawRowCheck19220 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form7 = rawRow19220 := by decide +kernel

def row19220 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19220 : row19220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19220 := by decide +kernel

theorem rowEval19220 (x : Key → ℝ) : Integer.Sparse.eval row19220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19220, Integer.Sparse.eval_collectBalanced, rawRowCheck19220]

def rawRow19221 : Integer.Sparse Key := [(key2622, 6), (key2622, 6), (key2606, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2776, 6), (key2799, 6)]

theorem rawRowCheck19221 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form7 = rawRow19221 := by decide +kernel

def row19221 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19221 : row19221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19221 := by decide +kernel

theorem rowEval19221 (x : Key → ℝ) : Integer.Sparse.eval row19221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19221, Integer.Sparse.eval_collectBalanced, rawRowCheck19221]

def rawRow19222 : Integer.Sparse Key := [(key2622, 6), (key2622, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2849, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2776, 6)]

theorem rawRowCheck19222 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form7 = rawRow19222 := by decide +kernel

def row19222 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19222 : row19222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19222 := by decide +kernel

theorem rowEval19222 (x : Key → ℝ) : Integer.Sparse.eval row19222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19222, Integer.Sparse.eval_collectBalanced, rawRowCheck19222]

def rawRow19223 : Integer.Sparse Key := [(key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2622, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6), (key2849, 6)]

theorem rawRowCheck19223 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19223 := by decide +kernel

def row19223 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

theorem rowCheck19223 : row19223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19223 := by decide +kernel

theorem rowEval19223 (x : Key → ℝ) : Integer.Sparse.eval row19223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19223, Integer.Sparse.eval_collectBalanced, rawRowCheck19223]

def rawRow19224 : Integer.Sparse Key := [(key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6)]

theorem rawRowCheck19224 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19224 := by decide +kernel

def row19224 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

theorem rowCheck19224 : row19224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19224 := by decide +kernel

theorem rowEval19224 (x : Key → ℝ) : Integer.Sparse.eval row19224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19224, Integer.Sparse.eval_collectBalanced, rawRowCheck19224]

def rawRow19225 : Integer.Sparse Key := [(key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2622, 6), (key2696, 6)]

theorem rawRowCheck19225 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19225 := by decide +kernel

def row19225 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

theorem rowCheck19225 : row19225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19225 := by decide +kernel

theorem rowEval19225 (x : Key → ℝ) : Integer.Sparse.eval row19225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19225, Integer.Sparse.eval_collectBalanced, rawRowCheck19225]

def rawRow19226 : Integer.Sparse Key := [(key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2622, 6)]

theorem rawRowCheck19226 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19226 := by decide +kernel

def row19226 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

theorem rowCheck19226 : row19226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19226 := by decide +kernel

theorem rowEval19226 (x : Key → ℝ) : Integer.Sparse.eval row19226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19226, Integer.Sparse.eval_collectBalanced, rawRowCheck19226]

def rawRow19227 : Integer.Sparse Key := [(key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2606, 6), (key2622, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2776, 6), (key2776, 6), (key2799, 6), (key2799, 6), (key2849, 6), (key2849, 6)]

theorem rawRowCheck19227 : GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow19227 := by decide +kernel

def row19227 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19227 : row19227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19227 := by decide +kernel

theorem rowEval19227 (x : Key → ℝ) : Integer.Sparse.eval row19227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19227, Integer.Sparse.eval_collectBalanced, rawRowCheck19227]

def rawRow19228 : Integer.Sparse Key := [(key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2606, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2776, 6), (key2799, 6)]

theorem rawRowCheck19228 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow19228 := by decide +kernel

def row19228 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19228 : row19228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19228 := by decide +kernel

theorem rowEval19228 (x : Key → ℝ) : Integer.Sparse.eval row19228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19228, Integer.Sparse.eval_collectBalanced, rawRowCheck19228]

def rawRow19229 : Integer.Sparse Key := [(key2776, 6), (key2849, 6), (key2849, 6), (key2799, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2776, 6)]

theorem rawRowCheck19229 : GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow19229 := by decide +kernel

def row19229 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19229 : row19229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19229 := by decide +kernel

theorem rowEval19229 (x : Key → ℝ) : Integer.Sparse.eval row19229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19229, Integer.Sparse.eval_collectBalanced, rawRowCheck19229]

def rawRow19230 : Integer.Sparse Key := [(key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2849, 6), (key2661, 6), (key2696, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2799, 6), (key2622, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2849, 6), (key2849, 6)]

theorem rawRowCheck19230 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form7 = rawRow19230 := by decide +kernel

def row19230 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

theorem rowCheck19230 : row19230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19230 := by decide +kernel

theorem rowEval19230 (x : Key → ℝ) : Integer.Sparse.eval row19230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19230, Integer.Sparse.eval_collectBalanced, rawRowCheck19230]

def rawRow19231 : Integer.Sparse Key := [(key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2661, 6), (key2696, 6), (key2799, 6), (key2606, 6), (key2799, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2622, 6), (key2696, 6)]

theorem rawRowCheck19231 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form7 = rawRow19231 := by decide +kernel

def row19231 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

theorem rowCheck19231 : row19231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19231 := by decide +kernel

theorem rowEval19231 (x : Key → ℝ) : Integer.Sparse.eval row19231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19231, Integer.Sparse.eval_collectBalanced, rawRowCheck19231]

def rawRow19232 : Integer.Sparse Key := [(key2799, 6), (key2849, 6), (key2849, 6), (key2776, 6), (key2696, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2799, 6), (key2606, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2622, 6)]

theorem rawRowCheck19232 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form7 = rawRow19232 := by decide +kernel

def row19232 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

theorem rowCheck19232 : row19232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19232 := by decide +kernel

theorem rowEval19232 (x : Key → ℝ) : Integer.Sparse.eval row19232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19232, Integer.Sparse.eval_collectBalanced, rawRowCheck19232]

def rawRow19233 : Integer.Sparse Key := [(key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2606, 6), (key2622, 6), (key2661, 6), (key2696, 6), (key2776, 6), (key2799, 6)]

theorem rawRowCheck19233 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form7 = rawRow19233 := by decide +kernel

def row19233 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19233 : row19233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19233 := by decide +kernel

theorem rowEval19233 (x : Key → ℝ) : Integer.Sparse.eval row19233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19233, Integer.Sparse.eval_collectBalanced, rawRowCheck19233]

def rawRow19234 : Integer.Sparse Key := [(key2849, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2776, 6), (key2849, 6), (key2799, 6), (key2622, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2606, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2776, 6)]

theorem rawRowCheck19234 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form7 = rawRow19234 := by decide +kernel

def row19234 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19234 : row19234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19234 := by decide +kernel

theorem rowEval19234 (x : Key → ℝ) : Integer.Sparse.eval row19234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19234, Integer.Sparse.eval_collectBalanced, rawRowCheck19234]

def rawRow19235 : Integer.Sparse Key := [(key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2661, 6), (key2696, 6), (key2606, 6), (key2799, 6), (key2622, 6), (key2696, 6)]

theorem rawRowCheck19235 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form7 = rawRow19235 := by decide +kernel

def row19235 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 24), (key2776, 12), (key2799, 18), (key2849, 36)]

theorem rowCheck19235 : row19235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19235 := by decide +kernel

theorem rowEval19235 (x : Key → ℝ) : Integer.Sparse.eval row19235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19235, Integer.Sparse.eval_collectBalanced, rawRowCheck19235]

def rawRow19236 : Integer.Sparse Key := [(key2849, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2799, 6), (key2849, 6), (key2776, 6), (key2696, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2661, 6), (key2799, 6), (key2606, 6), (key2696, 6), (key2622, 6)]

theorem rawRowCheck19236 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form7 = rawRow19236 := by decide +kernel

def row19236 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 24), (key2776, 12), (key2799, 18), (key2849, 36)]

theorem rowCheck19236 : row19236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19236 := by decide +kernel

theorem rowEval19236 (x : Key → ℝ) : Integer.Sparse.eval row19236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19236, Integer.Sparse.eval_collectBalanced, rawRowCheck19236]

def rawRow19237 : Integer.Sparse Key := [(key2849, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2849, 6), (key2776, 6), (key2799, 6), (key2849, 6), (key2622, 6), (key2696, 6), (key2776, 6), (key2799, 6), (key2622, 6), (key2696, 6), (key2606, 6), (key2661, 6)]

theorem rawRowCheck19237 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form7 = rawRow19237 := by decide +kernel

def row19237 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19237 : row19237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19237 := by decide +kernel

theorem rowEval19237 (x : Key → ℝ) : Integer.Sparse.eval row19237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck19237, Integer.Sparse.eval_collectBalanced, rawRowCheck19237]

def rawRow19238 : Integer.Sparse Key := [(key2849, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2849, 6), (key2799, 6), (key2776, 6), (key2849, 6), (key2696, 6), (key2622, 6), (key2799, 6), (key2776, 6), (key2696, 6), (key2622, 6), (key2661, 6), (key2606, 6)]

theorem rawRowCheck19238 : GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form7 = rawRow19238 := by decide +kernel

def row19238 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

theorem rowCheck19238 : row19238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19238 := by decide +kernel

theorem rowEval19238 (x : Key → ℝ) : Integer.Sparse.eval row19238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19238, Integer.Sparse.eval_collectBalanced, rawRowCheck19238]

def rawRow19239 : Integer.Sparse Key := [(key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6)]

theorem rawRowCheck19239 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19239 := by decide +kernel

def row19239 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

theorem rowCheck19239 : row19239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19239 := by decide +kernel

theorem rowEval19239 (x : Key → ℝ) : Integer.Sparse.eval row19239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19239, Integer.Sparse.eval_collectBalanced, rawRowCheck19239]

def rawRow19240 : Integer.Sparse Key := [(key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6)]

theorem rawRowCheck19240 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19240 := by decide +kernel

def row19240 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

theorem rowCheck19240 : row19240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19240 := by decide +kernel

theorem rowEval19240 (x : Key → ℝ) : Integer.Sparse.eval row19240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19240, Integer.Sparse.eval_collectBalanced, rawRowCheck19240]

def rawRow19241 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1884, 6), (key1852, 6), (key1852, 6)]

theorem rawRowCheck19241 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19241 := by decide +kernel

def row19241 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

theorem rowCheck19241 : row19241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19241 := by decide +kernel

theorem rowEval19241 (x : Key → ℝ) : Integer.Sparse.eval row19241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19241, Integer.Sparse.eval_collectBalanced, rawRowCheck19241]

def rawRow19242 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1850, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6)]

theorem rawRowCheck19242 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19242 := by decide +kernel

def row19242 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

theorem rowCheck19242 : row19242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19242 := by decide +kernel

theorem rowEval19242 (x : Key → ℝ) : Integer.Sparse.eval row19242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19242, Integer.Sparse.eval_collectBalanced, rawRowCheck19242]

def rawRow19243 : Integer.Sparse Key := [(key1884, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1850, 6), (key1850, 6), (key1850, 6)]

theorem rawRowCheck19243 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form0 = rawRow19243 := by decide +kernel

def row19243 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

theorem rowCheck19243 : row19243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19243 := by decide +kernel

theorem rowEval19243 (x : Key → ℝ) : Integer.Sparse.eval row19243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19243, Integer.Sparse.eval_collectBalanced, rawRowCheck19243]

def rawRow19244 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key685, 24), (key685, 24), (key692, 24)]

theorem rawRowCheck19244 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19244 := by decide +kernel

def row19244 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

theorem rowCheck19244 : row19244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19244 := by decide +kernel

theorem rowEval19244 (x : Key → ℝ) : Integer.Sparse.eval row19244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19244, Integer.Sparse.eval_collectBalanced, rawRowCheck19244]

def rawRow19245 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key685, 24), (key692, 24), (key685, 24)]

theorem rawRowCheck19245 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19245 := by decide +kernel

def row19245 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

theorem rowCheck19245 : row19245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19245 := by decide +kernel

theorem rowEval19245 (x : Key → ℝ) : Integer.Sparse.eval row19245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19245, Integer.Sparse.eval_collectBalanced, rawRowCheck19245]

def rawRow19246 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key692, 24), (key685, 24), (key685, 24)]

theorem rawRowCheck19246 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19246 := by decide +kernel

def row19246 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

theorem rowCheck19246 : row19246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19246 := by decide +kernel

theorem rowEval19246 (x : Key → ℝ) : Integer.Sparse.eval row19246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19246, Integer.Sparse.eval_collectBalanced, rawRowCheck19246]

def rawRow19247 : Integer.Sparse Key := [(key685, 24), (key692, 24), (key685, 24), (key685, 24), (key685, 24)]

theorem rawRowCheck19247 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19247 := by decide +kernel

def row19247 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

theorem rowCheck19247 : row19247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19247 := by decide +kernel

theorem rowEval19247 (x : Key → ℝ) : Integer.Sparse.eval row19247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19247, Integer.Sparse.eval_collectBalanced, rawRowCheck19247]

def rawRow19248 : Integer.Sparse Key := [(key692, 24), (key685, 24), (key685, 24), (key685, 24), (key685, 24)]

theorem rawRowCheck19248 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form1 = rawRow19248 := by decide +kernel

def row19248 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

theorem rowCheck19248 : row19248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19248 := by decide +kernel

theorem rowEval19248 (x : Key → ℝ) : Integer.Sparse.eval row19248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19248, Integer.Sparse.eval_collectBalanced, rawRowCheck19248]

def rawRow19249 : Integer.Sparse Key := [(key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1877, 2), (key1867, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1877, 2)]

theorem rawRowCheck19249 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form2 = rawRow19249 := by decide +kernel

def row19249 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

theorem rowCheck19249 : row19249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19249 := by decide +kernel

theorem rowEval19249 (x : Key → ℝ) : Integer.Sparse.eval row19249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form2) x := by
  rw [rowCheck19249, Integer.Sparse.eval_collectBalanced, rawRowCheck19249]

def rawRow19250 : Integer.Sparse Key := [(key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1867, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1867, 2)]

theorem rawRowCheck19250 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form2 = rawRow19250 := by decide +kernel

def row19250 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

theorem rowCheck19250 : row19250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19250 := by decide +kernel

theorem rowEval19250 (x : Key → ℝ) : Integer.Sparse.eval row19250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19250, Integer.Sparse.eval_collectBalanced, rawRowCheck19250]

def rawRow19251 : Integer.Sparse Key := [(key1861, 2), (key1861, 2), (key1859, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2)]

theorem rawRowCheck19251 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form2 = rawRow19251 := by decide +kernel

def row19251 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

theorem rowCheck19251 : row19251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19251 := by decide +kernel

theorem rowEval19251 (x : Key → ℝ) : Integer.Sparse.eval row19251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19251, Integer.Sparse.eval_collectBalanced, rawRowCheck19251]

def rawRow19252 : Integer.Sparse Key := [(key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2)]

theorem rawRowCheck19252 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19252 := by decide +kernel

def row19252 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

theorem rowCheck19252 : row19252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19252 := by decide +kernel

theorem rowEval19252 (x : Key → ℝ) : Integer.Sparse.eval row19252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19252, Integer.Sparse.eval_collectBalanced, rawRowCheck19252]

def rawRow19253 : Integer.Sparse Key := [(key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1877, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2), (key1859, 2)]

theorem rawRowCheck19253 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form2 = rawRow19253 := by decide +kernel

def row19253 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

theorem rowCheck19253 : row19253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19253 := by decide +kernel

theorem rowEval19253 (x : Key → ℝ) : Integer.Sparse.eval row19253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19253, Integer.Sparse.eval_collectBalanced, rawRowCheck19253]

def rawRow19254 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1957, 24), (key1957, 24), (key1969, 24)]

theorem rawRowCheck19254 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form3 = rawRow19254 := by decide +kernel

def row19254 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

theorem rowCheck19254 : row19254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19254 := by decide +kernel

theorem rowEval19254 (x : Key → ℝ) : Integer.Sparse.eval row19254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form3) x := by
  rw [rowCheck19254, Integer.Sparse.eval_collectBalanced, rawRowCheck19254]

def rawRow19255 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1957, 24), (key1969, 24), (key1957, 24)]

theorem rawRowCheck19255 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form3 = rawRow19255 := by decide +kernel

def row19255 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

theorem rowCheck19255 : row19255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19255 := by decide +kernel

theorem rowEval19255 (x : Key → ℝ) : Integer.Sparse.eval row19255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19255, Integer.Sparse.eval_collectBalanced, rawRowCheck19255]

def rawRow19256 : Integer.Sparse Key := [(key1957, 24), (key1957, 24), (key1969, 24), (key1957, 24), (key1957, 24)]

theorem rawRowCheck19256 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form3 = rawRow19256 := by decide +kernel

def row19256 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

theorem rowCheck19256 : row19256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19256 := by decide +kernel

theorem rowEval19256 (x : Key → ℝ) : Integer.Sparse.eval row19256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19256, Integer.Sparse.eval_collectBalanced, rawRowCheck19256]

def rawRow19257 : Integer.Sparse Key := [(key1957, 24), (key1969, 24), (key1957, 24), (key1957, 24), (key1957, 24)]

theorem rawRowCheck19257 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19257 := by decide +kernel

def row19257 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

theorem rowCheck19257 : row19257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19257 := by decide +kernel

theorem rowEval19257 (x : Key → ℝ) : Integer.Sparse.eval row19257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19257, Integer.Sparse.eval_collectBalanced, rawRowCheck19257]

def rawRow19258 : Integer.Sparse Key := [(key1969, 24), (key1957, 24), (key1957, 24), (key1957, 24), (key1957, 24)]

theorem rawRowCheck19258 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form3 = rawRow19258 := by decide +kernel

def row19258 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

theorem rowCheck19258 : row19258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19258 := by decide +kernel

theorem rowEval19258 (x : Key → ℝ) : Integer.Sparse.eval row19258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19258, Integer.Sparse.eval_collectBalanced, rawRowCheck19258]

def rawRow19259 : Integer.Sparse Key := [(key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key617, 6), (key645, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6)]

theorem rawRowCheck19259 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form4 = rawRow19259 := by decide +kernel

def row19259 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

theorem rowCheck19259 : row19259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19259 := by decide +kernel

theorem rowEval19259 (x : Key → ℝ) : Integer.Sparse.eval row19259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form4) x := by
  rw [rowCheck19259, Integer.Sparse.eval_collectBalanced, rawRowCheck19259]

def rawRow19260 : Integer.Sparse Key := [(key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6)]

theorem rawRowCheck19260 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form4 = rawRow19260 := by decide +kernel

def row19260 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

theorem rowCheck19260 : row19260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19260 := by decide +kernel

theorem rowEval19260 (x : Key → ℝ) : Integer.Sparse.eval row19260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19260, Integer.Sparse.eval_collectBalanced, rawRowCheck19260]

def rawRow19261 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key645, 6), (key619, 6), (key619, 6)]

theorem rawRowCheck19261 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form4 = rawRow19261 := by decide +kernel

def row19261 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

theorem rowCheck19261 : row19261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19261 := by decide +kernel

theorem rowEval19261 (x : Key → ℝ) : Integer.Sparse.eval row19261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19261, Integer.Sparse.eval_collectBalanced, rawRowCheck19261]

def rawRow19262 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key617, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6)]

theorem rawRowCheck19262 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19262 := by decide +kernel

def row19262 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

theorem rowCheck19262 : row19262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19262 := by decide +kernel

theorem rowEval19262 (x : Key → ℝ) : Integer.Sparse.eval row19262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19262, Integer.Sparse.eval_collectBalanced, rawRowCheck19262]

def rawRow19263 : Integer.Sparse Key := [(key645, 6), (key645, 6), (key645, 6), (key645, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key619, 6), (key617, 6), (key617, 6), (key617, 6), (key617, 6)]

theorem rawRowCheck19263 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form4 = rawRow19263 := by decide +kernel

def row19263 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

theorem rowCheck19263 : row19263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19263 := by decide +kernel

theorem rowEval19263 (x : Key → ℝ) : Integer.Sparse.eval row19263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19263, Integer.Sparse.eval_collectBalanced, rawRowCheck19263]

def rawRow19264 : Integer.Sparse Key := [(key1851, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4)]

theorem rawRowCheck19264 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form5 = rawRow19264 := by decide +kernel

def row19264 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

theorem rowCheck19264 : row19264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19264 := by decide +kernel

theorem rowEval19264 (x : Key → ℝ) : Integer.Sparse.eval row19264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form5) x := by
  rw [rowCheck19264, Integer.Sparse.eval_collectBalanced, rawRowCheck19264]

def rawRow19265 : Integer.Sparse Key := [(key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1886, 4), (key1855, 4)]

theorem rawRowCheck19265 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form5 = rawRow19265 := by decide +kernel

def row19265 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

theorem rowCheck19265 : row19265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19265 := by decide +kernel

theorem rowEval19265 (x : Key → ℝ) : Integer.Sparse.eval row19265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19265, Integer.Sparse.eval_collectBalanced, rawRowCheck19265]

def rawRow19266 : Integer.Sparse Key := [(key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1855, 4), (key1855, 4)]

theorem rawRowCheck19266 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form5 = rawRow19266 := by decide +kernel

def row19266 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

theorem rowCheck19266 : row19266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19266 := by decide +kernel

theorem rowEval19266 (x : Key → ℝ) : Integer.Sparse.eval row19266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19266, Integer.Sparse.eval_collectBalanced, rawRowCheck19266]

def rawRow19267 : Integer.Sparse Key := [(key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

theorem rawRowCheck19267 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19267 := by decide +kernel

def row19267 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

theorem rowCheck19267 : row19267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19267 := by decide +kernel

theorem rowEval19267 (x : Key → ℝ) : Integer.Sparse.eval row19267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19267, Integer.Sparse.eval_collectBalanced, rawRowCheck19267]

def rawRow19268 : Integer.Sparse Key := [(key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1886, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1855, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4), (key1851, 4)]

theorem rawRowCheck19268 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form5 = rawRow19268 := by decide +kernel

def row19268 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

theorem rowCheck19268 : row19268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19268 := by decide +kernel

theorem rowEval19268 (x : Key → ℝ) : Integer.Sparse.eval row19268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form5) x := by
  rw [rowCheck19268, Integer.Sparse.eval_collectBalanced, rawRowCheck19268]

def rawRow19269 : Integer.Sparse Key := [(key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6)]

theorem rawRowCheck19269 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19269 := by decide +kernel

def row19269 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

theorem rowCheck19269 : row19269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19269 := by decide +kernel

theorem rowEval19269 (x : Key → ℝ) : Integer.Sparse.eval row19269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19269, Integer.Sparse.eval_collectBalanced, rawRowCheck19269]

def rawRow19270 : Integer.Sparse Key := [(key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6)]

theorem rawRowCheck19270 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19270 := by decide +kernel

def row19270 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

theorem rowCheck19270 : row19270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19270 := by decide +kernel

theorem rowEval19270 (x : Key → ℝ) : Integer.Sparse.eval row19270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19270, Integer.Sparse.eval_collectBalanced, rawRowCheck19270]

def rawRow19271 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1953, 6), (key1933, 6), (key1933, 6)]

theorem rawRowCheck19271 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19271 := by decide +kernel

def row19271 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

theorem rowCheck19271 : row19271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19271 := by decide +kernel

theorem rowEval19271 (x : Key → ℝ) : Integer.Sparse.eval row19271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19271, Integer.Sparse.eval_collectBalanced, rawRowCheck19271]

def rawRow19272 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1932, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6)]

theorem rawRowCheck19272 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19272 := by decide +kernel

def row19272 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

theorem rowCheck19272 : row19272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19272 := by decide +kernel

theorem rowEval19272 (x : Key → ℝ) : Integer.Sparse.eval row19272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19272, Integer.Sparse.eval_collectBalanced, rawRowCheck19272]

def rawRow19273 : Integer.Sparse Key := [(key1953, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1932, 6), (key1932, 6), (key1932, 6)]

theorem rawRowCheck19273 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form6 = rawRow19273 := by decide +kernel

def row19273 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

theorem rowCheck19273 : row19273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19273 := by decide +kernel

theorem rowEval19273 (x : Key → ℝ) : Integer.Sparse.eval row19273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19273, Integer.Sparse.eval_collectBalanced, rawRowCheck19273]

def rawRow19274 : Integer.Sparse Key := [(key1958, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1966, 6), (key1960, 6), (key1966, 6)]

theorem rawRowCheck19274 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form7 = rawRow19274 := by decide +kernel

def row19274 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

theorem rowCheck19274 : row19274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19274 := by decide +kernel

theorem rowEval19274 (x : Key → ℝ) : Integer.Sparse.eval row19274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck19274, Integer.Sparse.eval_collectBalanced, rawRowCheck19274]

def rawRow19275 : Integer.Sparse Key := [(key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1966, 6), (key1960, 6)]

theorem rawRowCheck19275 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form7 = rawRow19275 := by decide +kernel

def row19275 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

theorem rowCheck19275 : row19275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19275 := by decide +kernel

theorem rowEval19275 (x : Key → ℝ) : Integer.Sparse.eval row19275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19275, Integer.Sparse.eval_collectBalanced, rawRowCheck19275]

def rawRow19276 : Integer.Sparse Key := [(key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6)]

theorem rawRowCheck19276 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form7 = rawRow19276 := by decide +kernel

def row19276 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

theorem rowCheck19276 : row19276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19276 := by decide +kernel

theorem rowEval19276 (x : Key → ℝ) : Integer.Sparse.eval row19276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19276, Integer.Sparse.eval_collectBalanced, rawRowCheck19276]

def rawRow19277 : Integer.Sparse Key := [(key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

theorem rawRowCheck19277 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19277 := by decide +kernel

def row19277 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

theorem rowCheck19277 : row19277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19277 := by decide +kernel

theorem rowEval19277 (x : Key → ℝ) : Integer.Sparse.eval row19277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19277, Integer.Sparse.eval_collectBalanced, rawRowCheck19277]

def rawRow19278 : Integer.Sparse Key := [(key1966, 6), (key1966, 6), (key1966, 6), (key1966, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1960, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

theorem rawRowCheck19278 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form7 = rawRow19278 := by decide +kernel

def row19278 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

theorem rowCheck19278 : row19278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19278 := by decide +kernel

theorem rowEval19278 (x : Key → ℝ) : Integer.Sparse.eval row19278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck19278, Integer.Sparse.eval_collectBalanced, rawRowCheck19278]

def rawRow19279 : Integer.Sparse Key := [(key288, 24), (key289, 24), (key289, 24), (key289, 24), (key289, 24)]

theorem rawRowCheck19279 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form8 = rawRow19279 := by decide +kernel

def row19279 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

theorem rowCheck19279 : row19279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19279 := by decide +kernel

theorem rowEval19279 (x : Key → ℝ) : Integer.Sparse.eval row19279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck19279, Integer.Sparse.eval_collectBalanced, rawRowCheck19279]

def rawRow19280 : Integer.Sparse Key := [(key289, 24), (key288, 24), (key289, 24), (key289, 24), (key289, 24)]

theorem rawRowCheck19280 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form8 = rawRow19280 := by decide +kernel

def row19280 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

theorem rowCheck19280 : row19280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19280 := by decide +kernel

theorem rowEval19280 (x : Key → ℝ) : Integer.Sparse.eval row19280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19280, Integer.Sparse.eval_collectBalanced, rawRowCheck19280]

def rawRow19281 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key288, 24), (key289, 24), (key289, 24)]

theorem rawRowCheck19281 : GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form8 = rawRow19281 := by decide +kernel

def row19281 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

theorem rowCheck19281 : row19281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19281 := by decide +kernel

theorem rowEval19281 (x : Key → ℝ) : Integer.Sparse.eval row19281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 0, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19281, Integer.Sparse.eval_collectBalanced, rawRowCheck19281]

def rawRow19282 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key289, 24), (key288, 24), (key289, 24)]

theorem rawRowCheck19282 : GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19282 := by decide +kernel

def row19282 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

theorem rowCheck19282 : row19282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19282 := by decide +kernel

theorem rowEval19282 (x : Key → ℝ) : Integer.Sparse.eval row19282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 0, 2, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19282, Integer.Sparse.eval_collectBalanced, rawRowCheck19282]

def rawRow19283 : Integer.Sparse Key := [(key289, 24), (key289, 24), (key289, 24), (key289, 24), (key288, 24)]

theorem rawRowCheck19283 : GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form8 = rawRow19283 := by decide +kernel

def row19283 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

theorem rowCheck19283 : row19283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19283 := by decide +kernel

theorem rowEval19283 (x : Key → ℝ) : Integer.Sparse.eval row19283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-2, 2, 0, 0, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck19283, Integer.Sparse.eval_collectBalanced, rawRowCheck19283]

def rawRow19284 : Integer.Sparse Key := [(key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2491, 6)]

theorem rawRowCheck19284 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19284 := by decide +kernel

def row19284 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19284 : row19284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19284 := by decide +kernel

theorem rowEval19284 (x : Key → ℝ) : Integer.Sparse.eval row19284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19284, Integer.Sparse.eval_collectBalanced, rawRowCheck19284]

def rawRow19285 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2491, 6)]

theorem rawRowCheck19285 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19285 := by decide +kernel

def row19285 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19285 : row19285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19285 := by decide +kernel

theorem rowEval19285 (x : Key → ℝ) : Integer.Sparse.eval row19285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19285, Integer.Sparse.eval_collectBalanced, rawRowCheck19285]

def rawRow19286 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2491, 6), (key2423, 6)]

theorem rawRowCheck19286 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19286 := by decide +kernel

def row19286 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19286 : row19286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19286 := by decide +kernel

theorem rowEval19286 (x : Key → ℝ) : Integer.Sparse.eval row19286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19286, Integer.Sparse.eval_collectBalanced, rawRowCheck19286]

def rawRow19287 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6)]

theorem rawRowCheck19287 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form0 = rawRow19287 := by decide +kernel

def row19287 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19287 : row19287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19287 := by decide +kernel

theorem rowEval19287 (x : Key → ℝ) : Integer.Sparse.eval row19287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19287, Integer.Sparse.eval_collectBalanced, rawRowCheck19287]

def rawRow19288 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6)]

theorem rawRowCheck19288 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form0 = rawRow19288 := by decide +kernel

def row19288 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19288 : row19288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19288 := by decide +kernel

theorem rowEval19288 (x : Key → ℝ) : Integer.Sparse.eval row19288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19288, Integer.Sparse.eval_collectBalanced, rawRowCheck19288]

def rawRow19289 : Integer.Sparse Key := [(key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6)]

theorem rawRowCheck19289 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form0 = rawRow19289 := by decide +kernel

def row19289 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19289 : row19289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19289 := by decide +kernel

theorem rowEval19289 (x : Key → ℝ) : Integer.Sparse.eval row19289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19289, Integer.Sparse.eval_collectBalanced, rawRowCheck19289]

def rawRow19290 : Integer.Sparse Key := [(key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2416, 6), (key2416, 6), (key2416, 6), (key2489, 6)]

theorem rawRowCheck19290 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form0 = rawRow19290 := by decide +kernel

def row19290 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19290 : row19290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19290 := by decide +kernel

theorem rowEval19290 (x : Key → ℝ) : Integer.Sparse.eval row19290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19290, Integer.Sparse.eval_collectBalanced, rawRowCheck19290]

def rawRow19291 : Integer.Sparse Key := [(key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2491, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6)]

theorem rawRowCheck19291 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form0 = rawRow19291 := by decide +kernel

def row19291 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19291 : row19291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19291 := by decide +kernel

theorem rowEval19291 (x : Key → ℝ) : Integer.Sparse.eval row19291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19291, Integer.Sparse.eval_collectBalanced, rawRowCheck19291]

def rawRow19292 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6)]

theorem rawRowCheck19292 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form0 = rawRow19292 := by decide +kernel

def row19292 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19292 : row19292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19292 := by decide +kernel

theorem rowEval19292 (x : Key → ℝ) : Integer.Sparse.eval row19292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19292, Integer.Sparse.eval_collectBalanced, rawRowCheck19292]

def rawRow19293 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2416, 6), (key2489, 6), (key2416, 6), (key2416, 6), (key2416, 6)]

theorem rawRowCheck19293 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form0 = rawRow19293 := by decide +kernel

def row19293 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

theorem rowCheck19293 : row19293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19293 := by decide +kernel

theorem rowEval19293 (x : Key → ℝ) : Integer.Sparse.eval row19293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19293, Integer.Sparse.eval_collectBalanced, rawRowCheck19293]

def rawRow19294 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1045, 24), (key1131, 24), (key1131, 24)]

theorem rawRowCheck19294 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19294 := by decide +kernel

def row19294 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19294 : row19294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19294 := by decide +kernel

theorem rowEval19294 (x : Key → ℝ) : Integer.Sparse.eval row19294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19294, Integer.Sparse.eval_collectBalanced, rawRowCheck19294]

def rawRow19295 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1131, 24), (key1045, 24), (key1131, 24)]

theorem rawRowCheck19295 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19295 := by decide +kernel

def row19295 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19295 : row19295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19295 := by decide +kernel

theorem rowEval19295 (x : Key → ℝ) : Integer.Sparse.eval row19295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19295, Integer.Sparse.eval_collectBalanced, rawRowCheck19295]

def rawRow19296 : Integer.Sparse Key := [(key1045, 24), (key1045, 24), (key1131, 24), (key1131, 24), (key1045, 24)]

theorem rawRowCheck19296 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19296 := by decide +kernel

def row19296 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19296 : row19296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19296 := by decide +kernel

theorem rowEval19296 (x : Key → ℝ) : Integer.Sparse.eval row19296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19296, Integer.Sparse.eval_collectBalanced, rawRowCheck19296]

def rawRow19297 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1045, 24), (key1045, 24), (key1131, 24)]

theorem rawRowCheck19297 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form1 = rawRow19297 := by decide +kernel

def row19297 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19297 : row19297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19297 := by decide +kernel

theorem rowEval19297 (x : Key → ℝ) : Integer.Sparse.eval row19297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19297, Integer.Sparse.eval_collectBalanced, rawRowCheck19297]

def rawRow19298 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1045, 24), (key1131, 24), (key1045, 24)]

theorem rawRowCheck19298 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form1 = rawRow19298 := by decide +kernel

def row19298 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19298 : row19298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19298 := by decide +kernel

theorem rowEval19298 (x : Key → ℝ) : Integer.Sparse.eval row19298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19298, Integer.Sparse.eval_collectBalanced, rawRowCheck19298]

def rawRow19299 : Integer.Sparse Key := [(key1045, 24), (key1131, 24), (key1131, 24), (key1045, 24), (key1045, 24)]

theorem rawRowCheck19299 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form1 = rawRow19299 := by decide +kernel

def row19299 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19299 : row19299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19299 := by decide +kernel

theorem rowEval19299 (x : Key → ℝ) : Integer.Sparse.eval row19299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19299, Integer.Sparse.eval_collectBalanced, rawRowCheck19299]

def rawRow19300 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1045, 24), (key1045, 24), (key1131, 24)]

theorem rawRowCheck19300 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form1 = rawRow19300 := by decide +kernel

def row19300 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19300 : row19300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19300 := by decide +kernel

theorem rowEval19300 (x : Key → ℝ) : Integer.Sparse.eval row19300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19300, Integer.Sparse.eval_collectBalanced, rawRowCheck19300]

def rawRow19301 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1045, 24), (key1131, 24), (key1045, 24)]

theorem rawRowCheck19301 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form1 = rawRow19301 := by decide +kernel

def row19301 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19301 : row19301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19301 := by decide +kernel

theorem rowEval19301 (x : Key → ℝ) : Integer.Sparse.eval row19301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19301, Integer.Sparse.eval_collectBalanced, rawRowCheck19301]

def rawRow19302 : Integer.Sparse Key := [(key1131, 24), (key1045, 24), (key1131, 24), (key1045, 24), (key1045, 24)]

theorem rawRowCheck19302 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form1 = rawRow19302 := by decide +kernel

def row19302 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19302 : row19302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19302 := by decide +kernel

theorem rowEval19302 (x : Key → ℝ) : Integer.Sparse.eval row19302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19302, Integer.Sparse.eval_collectBalanced, rawRowCheck19302]

def rawRow19303 : Integer.Sparse Key := [(key1131, 24), (key1131, 24), (key1045, 24), (key1045, 24), (key1045, 24)]

theorem rawRowCheck19303 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form1 = rawRow19303 := by decide +kernel

def row19303 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

theorem rowCheck19303 : row19303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19303 := by decide +kernel

theorem rowEval19303 (x : Key → ℝ) : Integer.Sparse.eval row19303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19303, Integer.Sparse.eval_collectBalanced, rawRowCheck19303]

def rawRow19304 : Integer.Sparse Key := [(key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2712, 2), (key2712, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2863, 2), (key2688, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2863, 2)]

theorem rawRowCheck19304 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form2 = rawRow19304 := by decide +kernel

def row19304 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19304 : row19304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19304 := by decide +kernel

theorem rowEval19304 (x : Key → ℝ) : Integer.Sparse.eval row19304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19304, Integer.Sparse.eval_collectBalanced, rawRowCheck19304]

def rawRow19305 : Integer.Sparse Key := [(key2681, 2), (key2688, 2), (key2681, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2817, 2)]

theorem rawRowCheck19305 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form2 = rawRow19305 := by decide +kernel

def row19305 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19305 : row19305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19305 := by decide +kernel

theorem rowEval19305 (x : Key → ℝ) : Integer.Sparse.eval row19305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19305, Integer.Sparse.eval_collectBalanced, rawRowCheck19305]

def rawRow19306 : Integer.Sparse Key := [(key2688, 2), (key2681, 2), (key2681, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2712, 2), (key2815, 2), (key2712, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2817, 2), (key2714, 2)]

theorem rawRowCheck19306 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form2 = rawRow19306 := by decide +kernel

def row19306 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19306 : row19306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19306 := by decide +kernel

theorem rowEval19306 (x : Key → ℝ) : Integer.Sparse.eval row19306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19306, Integer.Sparse.eval_collectBalanced, rawRowCheck19306]

def rawRow19307 : Integer.Sparse Key := [(key2712, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2688, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2817, 2)]

theorem rawRowCheck19307 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form2 = rawRow19307 := by decide +kernel

def row19307 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19307 : row19307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19307 := by decide +kernel

theorem rowEval19307 (x : Key → ℝ) : Integer.Sparse.eval row19307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19307, Integer.Sparse.eval_collectBalanced, rawRowCheck19307]

def rawRow19308 : Integer.Sparse Key := [(key2714, 2), (key2712, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2714, 2)]

theorem rawRowCheck19308 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form2 = rawRow19308 := by decide +kernel

def row19308 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19308 : row19308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19308 := by decide +kernel

theorem rowEval19308 (x : Key → ℝ) : Integer.Sparse.eval row19308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19308, Integer.Sparse.eval_collectBalanced, rawRowCheck19308]

def rawRow19309 : Integer.Sparse Key := [(key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2)]

theorem rawRowCheck19309 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form2 = rawRow19309 := by decide +kernel

def row19309 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19309 : row19309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19309 := by decide +kernel

theorem rowEval19309 (x : Key → ℝ) : Integer.Sparse.eval row19309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19309, Integer.Sparse.eval_collectBalanced, rawRowCheck19309]

def rawRow19310 : Integer.Sparse Key := [(key2815, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2712, 2), (key2815, 2)]

theorem rawRowCheck19310 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form2 = rawRow19310 := by decide +kernel

def row19310 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19310 : row19310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19310 := by decide +kernel

theorem rowEval19310 (x : Key → ℝ) : Integer.Sparse.eval row19310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form2) x := by
  rw [rowCheck19310, Integer.Sparse.eval_collectBalanced, rawRowCheck19310]

def rawRow19311 : Integer.Sparse Key := [(key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2863, 2), (key2817, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2688, 2), (key2681, 2), (key2714, 2), (key2681, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2714, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2714, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2712, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2815, 2), (key2712, 2)]

theorem rawRowCheck19311 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form2 = rawRow19311 := by decide +kernel

def row19311 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19311 : row19311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19311 := by decide +kernel

theorem rowEval19311 (x : Key → ℝ) : Integer.Sparse.eval row19311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19311, Integer.Sparse.eval_collectBalanced, rawRowCheck19311]

def rawRow19312 : Integer.Sparse Key := [(key2817, 2), (key2817, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2)]

theorem rawRowCheck19312 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form2 = rawRow19312 := by decide +kernel

def row19312 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19312 : row19312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19312 := by decide +kernel

theorem rowEval19312 (x : Key → ℝ) : Integer.Sparse.eval row19312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19312, Integer.Sparse.eval_collectBalanced, rawRowCheck19312]

def rawRow19313 : Integer.Sparse Key := [(key2863, 2), (key2863, 2), (key2863, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2815, 2), (key2815, 2), (key2815, 2), (key2863, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2712, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2817, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2815, 2), (key2712, 2), (key2712, 2), (key2712, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2), (key2681, 2)]

theorem rawRowCheck19313 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form2 = rawRow19313 := by decide +kernel

def row19313 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

theorem rowCheck19313 : row19313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19313 := by decide +kernel

theorem rowEval19313 (x : Key → ℝ) : Integer.Sparse.eval row19313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form2) x := by
  rw [rowCheck19313, Integer.Sparse.eval_collectBalanced, rawRowCheck19313]

def rawRow19314 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3031, 24), (key3118, 24), (key3118, 24)]

theorem rawRowCheck19314 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form3 = rawRow19314 := by decide +kernel

def row19314 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

theorem rowCheck19314 : row19314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19314 := by decide +kernel

theorem rowEval19314 (x : Key → ℝ) : Integer.Sparse.eval row19314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19314, Integer.Sparse.eval_collectBalanced, rawRowCheck19314]

def rawRow19315 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3118, 24), (key3031, 24), (key3118, 24)]

theorem rawRowCheck19315 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form3 = rawRow19315 := by decide +kernel

def row19315 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

theorem rowCheck19315 : row19315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19315 := by decide +kernel

theorem rowEval19315 (x : Key → ℝ) : Integer.Sparse.eval row19315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19315, Integer.Sparse.eval_collectBalanced, rawRowCheck19315]

def rawRow19316 : Integer.Sparse Key := [(key2412, 24), (key3031, 24), (key3118, 24), (key3118, 24), (key3031, 24)]

theorem rawRowCheck19316 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form3 = rawRow19316 := by decide +kernel

def row19316 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

theorem rowCheck19316 : row19316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19316 := by decide +kernel

theorem rowEval19316 (x : Key → ℝ) : Integer.Sparse.eval row19316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19316, Integer.Sparse.eval_collectBalanced, rawRowCheck19316]

def rawRow19317 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3031, 24), (key3031, 24), (key3118, 24)]

theorem rawRowCheck19317 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form3 = rawRow19317 := by decide +kernel

def row19317 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

theorem rowCheck19317 : row19317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19317 := by decide +kernel

theorem rowEval19317 (x : Key → ℝ) : Integer.Sparse.eval row19317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19317, Integer.Sparse.eval_collectBalanced, rawRowCheck19317]

def rawRow19318 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3031, 24), (key3118, 24), (key3031, 24)]

theorem rawRowCheck19318 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form3 = rawRow19318 := by decide +kernel

def row19318 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

theorem rowCheck19318 : row19318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19318 := by decide +kernel

theorem rowEval19318 (x : Key → ℝ) : Integer.Sparse.eval row19318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19318, Integer.Sparse.eval_collectBalanced, rawRowCheck19318]

def rawRow19319 : Integer.Sparse Key := [(key2412, 24), (key3118, 24), (key3118, 24), (key3031, 24), (key3031, 24)]

theorem rawRowCheck19319 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form3 = rawRow19319 := by decide +kernel

def row19319 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

theorem rowCheck19319 : row19319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19319 := by decide +kernel

theorem rowEval19319 (x : Key → ℝ) : Integer.Sparse.eval row19319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19319, Integer.Sparse.eval_collectBalanced, rawRowCheck19319]

def rawRow19320 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3031, 24), (key3031, 24), (key3118, 24)]

theorem rawRowCheck19320 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form3 = rawRow19320 := by decide +kernel

def row19320 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

theorem rowCheck19320 : row19320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19320 := by decide +kernel

theorem rowEval19320 (x : Key → ℝ) : Integer.Sparse.eval row19320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, -1, 0] GramFunctions.Block5.form3) x := by
  rw [rowCheck19320, Integer.Sparse.eval_collectBalanced, rawRowCheck19320]

def rawRow19321 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3031, 24), (key3118, 24), (key3031, 24)]

theorem rawRowCheck19321 : GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form3 = rawRow19321 := by decide +kernel

def row19321 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

theorem rowCheck19321 : row19321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19321 := by decide +kernel

theorem rowEval19321 (x : Key → ℝ) : Integer.Sparse.eval row19321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19321, Integer.Sparse.eval_collectBalanced, rawRowCheck19321]

def rawRow19322 : Integer.Sparse Key := [(key2485, 24), (key2412, 24), (key3118, 24), (key3031, 24), (key3031, 24)]

theorem rawRowCheck19322 : GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form3 = rawRow19322 := by decide +kernel

def row19322 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

theorem rowCheck19322 : row19322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19322 := by decide +kernel

theorem rowEval19322 (x : Key → ℝ) : Integer.Sparse.eval row19322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, 0, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19322, Integer.Sparse.eval_collectBalanced, rawRowCheck19322]

def rawRow19323 : Integer.Sparse Key := [(key2485, 24), (key2485, 24), (key2412, 24), (key3031, 24), (key3031, 24)]

theorem rawRowCheck19323 : GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form3 = rawRow19323 := by decide +kernel

def row19323 : Integer.Sparse Key := [(key2412, 24), (key2485, 48), (key3031, 48)]

theorem rowCheck19323 : row19323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19323 := by decide +kernel

theorem rowEval19323 (x : Key → ℝ) : Integer.Sparse.eval row19323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, 0, -1, -1, -1] GramFunctions.Block5.form3) x := by
  rw [rowCheck19323, Integer.Sparse.eval_collectBalanced, rawRowCheck19323]

def rawRow19324 : Integer.Sparse Key := [(key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1138, 6)]

theorem rawRowCheck19324 : GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form4 = rawRow19324 := by decide +kernel

def row19324 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19324 : row19324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19324 := by decide +kernel

theorem rowEval19324 (x : Key → ℝ) : Integer.Sparse.eval row19324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, -1, 0, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19324, Integer.Sparse.eval_collectBalanced, rawRowCheck19324]

def rawRow19325 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1050, 6), (key1138, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1058, 6), (key1138, 6)]

theorem rawRowCheck19325 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form4 = rawRow19325 := by decide +kernel

def row19325 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19325 : row19325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19325 := by decide +kernel

theorem rowEval19325 (x : Key → ℝ) : Integer.Sparse.eval row19325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19325, Integer.Sparse.eval_collectBalanced, rawRowCheck19325]

def rawRow19326 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1050, 6), (key1136, 6), (key1050, 6), (key1138, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6), (key1138, 6), (key1058, 6)]

theorem rawRowCheck19326 : GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form4 = rawRow19326 := by decide +kernel

def row19326 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19326 : row19326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19326 := by decide +kernel

theorem rowEval19326 (x : Key → ℝ) : Integer.Sparse.eval row19326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -1, 0, 0, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19326, Integer.Sparse.eval_collectBalanced, rawRowCheck19326]

def rawRow19327 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, 6), (key1058, 6), (key1138, 6), (key1050, 6), (key1050, 6), (key1136, 6), (key1138, 6), (key1058, 6), (key1058, 6), (key1138, 6)]

theorem rawRowCheck19327 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form4 = rawRow19327 := by decide +kernel

def row19327 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

theorem rowCheck19327 : row19327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19327 := by decide +kernel

theorem rowEval19327 (x : Key → ℝ) : Integer.Sparse.eval row19327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -1, -1, 0] GramFunctions.Block5.form4) x := by
  rw [rowCheck19327, Integer.Sparse.eval_collectBalanced, rawRowCheck19327]

end MUB6.Certificate.GramRows

end OAI
