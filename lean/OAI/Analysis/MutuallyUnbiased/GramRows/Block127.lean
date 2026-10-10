import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow13184 : Integer.Sparse Key := [(key632, 2), (key650, 2), (key650, 2), (key298, 2), (key561, 2), (key561, 2), (key294, 2), (key294, 2), (key522, 2), (key522, 2), (key553, 2), (key553, 2), (key631, -2), (key631, -2), (key647, -2), (key294, -2), (key294, -2), (key522, -2), (key522, -2), (key553, -2), (key553, -2), (key291, -2), (key518, -2), (key518, -2)]

theorem rawRowCheck13184 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form26 = rawRow13184 := by decide +kernel

def row13184 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13184 : row13184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13184 := by decide +kernel

theorem rowEval13184 (x : Key → ℝ) : Integer.Sparse.eval row13184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13184, Integer.Sparse.eval_collectBalanced, rawRowCheck13184]

def rawRow13185 : Integer.Sparse Key := [(key650, 2), (key632, 2), (key650, 2), (key561, 2), (key298, 2), (key561, 2), (key522, 2), (key553, 2), (key294, 2), (key553, 2), (key294, 2), (key522, 2), (key631, -2), (key647, -2), (key631, -2), (key522, -2), (key553, -2), (key294, -2), (key553, -2), (key294, -2), (key522, -2), (key518, -2), (key291, -2), (key518, -2)]

theorem rawRowCheck13185 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form26 = rawRow13185 := by decide +kernel

def row13185 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13185 : row13185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13185 := by decide +kernel

theorem rowEval13185 (x : Key → ℝ) : Integer.Sparse.eval row13185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form26) x := by
  rw [rowCheck13185, Integer.Sparse.eval_collectBalanced, rawRowCheck13185]

def rawRow13186 : Integer.Sparse Key := [(key650, 2), (key650, 2), (key632, 2), (key561, 2), (key561, 2), (key298, 2), (key553, 2), (key522, 2), (key553, 2), (key294, 2), (key522, 2), (key294, 2), (key647, -2), (key631, -2), (key631, -2), (key553, -2), (key522, -2), (key553, -2), (key294, -2), (key522, -2), (key294, -2), (key518, -2), (key518, -2), (key291, -2)]

theorem rawRowCheck13186 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form26 = rawRow13186 := by decide +kernel

def row13186 : Integer.Sparse Key := [(key291, -2), (key298, 2), (key518, -4), (key561, 4), (key631, -4), (key632, 2), (key647, -2), (key650, 4)]

theorem rowCheck13186 : row13186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13186 := by decide +kernel

theorem rowEval13186 (x : Key → ℝ) : Integer.Sparse.eval row13186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form26) x := by
  rw [rowCheck13186, Integer.Sparse.eval_collectBalanced, rawRowCheck13186]

def rawRow13187 : Integer.Sparse Key := [(key2362, 4), (key2562, 4), (key2562, 4), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2365, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2564, -2), (key2367, 4), (key2525, 4), (key2525, 4)]

theorem rawRowCheck13187 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0 = rawRow13187 := by decide +kernel

def row13187 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

theorem rowCheck13187 : row13187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13187 := by decide +kernel

theorem rowEval13187 (x : Key → ℝ) : Integer.Sparse.eval row13187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13187, Integer.Sparse.eval_collectBalanced, rawRowCheck13187]

def rawRow13188 : Integer.Sparse Key := [(key2562, 4), (key2362, 4), (key2562, 4), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2525, 4), (key2367, 4), (key2525, 4)]

theorem rawRowCheck13188 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0 = rawRow13188 := by decide +kernel

def row13188 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

theorem rowCheck13188 : row13188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13188 := by decide +kernel

theorem rowEval13188 (x : Key → ℝ) : Integer.Sparse.eval row13188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13188, Integer.Sparse.eval_collectBalanced, rawRowCheck13188]

def rawRow13189 : Integer.Sparse Key := [(key2562, 4), (key2562, 4), (key2362, 4), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2564, -2), (key2521, -2), (key2564, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2525, 4), (key2525, 4), (key2367, 4)]

theorem rawRowCheck13189 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0 = rawRow13189 := by decide +kernel

def row13189 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2521, -8), (key2525, 8), (key2562, 8), (key2564, -8)]

theorem rowCheck13189 : row13189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13189 := by decide +kernel

theorem rowEval13189 (x : Key → ℝ) : Integer.Sparse.eval row13189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 1, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13189, Integer.Sparse.eval_collectBalanced, rawRowCheck13189]

def rawRow13190 : Integer.Sparse Key := [(key2365, 4), (key2521, 4), (key2564, 4), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2367, -2), (key2460, -2), (key2525, -2), (key2533, -2), (key2564, -2), (key2365, 4), (key2460, 4), (key2521, 4)]

theorem rawRowCheck13190 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13190 := by decide +kernel

def row13190 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13190 : row13190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13190 := by decide +kernel

theorem rowEval13190 (x : Key → ℝ) : Integer.Sparse.eval row13190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13190, Integer.Sparse.eval_collectBalanced, rawRowCheck13190]

def rawRow13191 : Integer.Sparse Key := [(key2365, 4), (key2564, 4), (key2521, 4), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2367, -2), (key2365, -2), (key2525, -2), (key2460, -2), (key2564, -2), (key2533, -2), (key2365, 4), (key2521, 4), (key2460, 4)]

theorem rawRowCheck13191 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13191 := by decide +kernel

def row13191 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13191 : row13191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13191 := by decide +kernel

theorem rowEval13191 (x : Key → ℝ) : Integer.Sparse.eval row13191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13191, Integer.Sparse.eval_collectBalanced, rawRowCheck13191]

def rawRow13192 : Integer.Sparse Key := [(key2521, 4), (key2365, 4), (key2564, 4), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2533, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2460, 4), (key2365, 4), (key2521, 4)]

theorem rawRowCheck13192 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13192 := by decide +kernel

def row13192 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13192 : row13192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13192 := by decide +kernel

theorem rowEval13192 (x : Key → ℝ) : Integer.Sparse.eval row13192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13192, Integer.Sparse.eval_collectBalanced, rawRowCheck13192]

def rawRow13193 : Integer.Sparse Key := [(key2521, 4), (key2564, 4), (key2365, 4), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2525, -2), (key2367, -2), (key2460, 4), (key2521, 4), (key2365, 4)]

theorem rawRowCheck13193 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13193 := by decide +kernel

def row13193 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13193 : row13193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13193 := by decide +kernel

theorem rowEval13193 (x : Key → ℝ) : Integer.Sparse.eval row13193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13193, Integer.Sparse.eval_collectBalanced, rawRowCheck13193]

def rawRow13194 : Integer.Sparse Key := [(key2564, 4), (key2365, 4), (key2521, 4), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2525, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2365, -2), (key2460, -2), (key2521, 4), (key2365, 4), (key2460, 4)]

theorem rawRowCheck13194 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13194 := by decide +kernel

def row13194 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13194 : row13194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13194 := by decide +kernel

theorem rowEval13194 (x : Key → ℝ) : Integer.Sparse.eval row13194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13194, Integer.Sparse.eval_collectBalanced, rawRowCheck13194]

def rawRow13195 : Integer.Sparse Key := [(key2564, 4), (key2521, 4), (key2365, 4), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2564, -2), (key2525, -2), (key2533, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2521, 4), (key2460, 4), (key2365, 4)]

theorem rawRowCheck13195 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13195 := by decide +kernel

def row13195 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13195 : row13195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13195 := by decide +kernel

theorem rowEval13195 (x : Key → ℝ) : Integer.Sparse.eval row13195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13195, Integer.Sparse.eval_collectBalanced, rawRowCheck13195]

def rawRow13196 : Integer.Sparse Key := [(key2365, 4), (key2521, 4), (key2564, 4), (key2365, -2), (key2367, -2), (key2460, -2), (key2533, -2), (key2525, -2), (key2564, -2), (key2362, -2), (key2365, -2), (key2457, -2), (key2521, -2), (key2532, -2), (key2562, -2), (key2365, 4), (key2460, 4), (key2521, 4)]

theorem rawRowCheck13196 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0 = rawRow13196 := by decide +kernel

def row13196 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13196 : row13196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13196 := by decide +kernel

theorem rowEval13196 (x : Key → ℝ) : Integer.Sparse.eval row13196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13196, Integer.Sparse.eval_collectBalanced, rawRowCheck13196]

def rawRow13197 : Integer.Sparse Key := [(key2365, 4), (key2564, 4), (key2521, 4), (key2367, -2), (key2365, -2), (key2533, -2), (key2460, -2), (key2564, -2), (key2525, -2), (key2365, -2), (key2362, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2532, -2), (key2365, 4), (key2521, 4), (key2460, 4)]

theorem rawRowCheck13197 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0 = rawRow13197 := by decide +kernel

def row13197 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13197 : row13197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13197 := by decide +kernel

theorem rowEval13197 (x : Key → ℝ) : Integer.Sparse.eval row13197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13197, Integer.Sparse.eval_collectBalanced, rawRowCheck13197]

def rawRow13198 : Integer.Sparse Key := [(key2521, 4), (key2365, 4), (key2564, 4), (key2460, -2), (key2525, -2), (key2365, -2), (key2564, -2), (key2367, -2), (key2533, -2), (key2457, -2), (key2521, -2), (key2362, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2460, 4), (key2365, 4), (key2521, 4)]

theorem rawRowCheck13198 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0 = rawRow13198 := by decide +kernel

def row13198 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13198 : row13198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13198 := by decide +kernel

theorem rowEval13198 (x : Key → ℝ) : Integer.Sparse.eval row13198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13198, Integer.Sparse.eval_collectBalanced, rawRowCheck13198]

def rawRow13199 : Integer.Sparse Key := [(key2521, 4), (key2564, 4), (key2365, 4), (key2525, -2), (key2460, -2), (key2564, -2), (key2365, -2), (key2533, -2), (key2367, -2), (key2521, -2), (key2457, -2), (key2562, -2), (key2362, -2), (key2521, -2), (key2365, -2), (key2460, 4), (key2521, 4), (key2365, 4)]

theorem rawRowCheck13199 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0 = rawRow13199 := by decide +kernel

def row13199 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 4), (key2525, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13199 : row13199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13199 := by decide +kernel

theorem rowEval13199 (x : Key → ℝ) : Integer.Sparse.eval row13199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13199, Integer.Sparse.eval_collectBalanced, rawRowCheck13199]

def rawRow13200 : Integer.Sparse Key := [(key2564, 4), (key2365, 4), (key2521, 4), (key2533, -2), (key2564, -2), (key2367, -2), (key2525, -2), (key2365, -2), (key2460, -2), (key2532, -2), (key2562, -2), (key2365, -2), (key2521, -2), (key2362, -2), (key2457, -2), (key2521, 4), (key2365, 4), (key2460, 4)]

theorem rawRowCheck13200 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0 = rawRow13200 := by decide +kernel

def row13200 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13200 : row13200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13200 := by decide +kernel

theorem rowEval13200 (x : Key → ℝ) : Integer.Sparse.eval row13200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13200, Integer.Sparse.eval_collectBalanced, rawRowCheck13200]

def rawRow13201 : Integer.Sparse Key := [(key2564, 4), (key2521, 4), (key2365, 4), (key2564, -2), (key2533, -2), (key2525, -2), (key2367, -2), (key2460, -2), (key2365, -2), (key2562, -2), (key2532, -2), (key2521, -2), (key2365, -2), (key2457, -2), (key2362, -2), (key2521, 4), (key2460, 4), (key2365, 4)]

theorem rawRowCheck13201 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0 = rawRow13201 := by decide +kernel

def row13201 : Integer.Sparse Key := [(key2362, -2), (key2365, 4), (key2367, -2), (key2457, -2), (key2460, 2), (key2521, 6), (key2525, -2), (key2532, -2), (key2533, -2), (key2562, -2), (key2564, 2)]

theorem rowCheck13201 : row13201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13201 := by decide +kernel

theorem rowEval13201 (x : Key → ℝ) : Integer.Sparse.eval row13201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13201, Integer.Sparse.eval_collectBalanced, rawRowCheck13201]

def rawRow13202 : Integer.Sparse Key := [(key2367, 4), (key2525, 4), (key2525, 4), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2365, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2521, -2), (key2362, 4), (key2457, 4), (key2457, 4)]

theorem rawRowCheck13202 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13202 := by decide +kernel

def row13202 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

theorem rowCheck13202 : row13202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13202 := by decide +kernel

theorem rowEval13202 (x : Key → ℝ) : Integer.Sparse.eval row13202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13202, Integer.Sparse.eval_collectBalanced, rawRowCheck13202]

def rawRow13203 : Integer.Sparse Key := [(key2525, 4), (key2367, 4), (key2525, 4), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2457, 4), (key2362, 4), (key2457, 4)]

theorem rawRowCheck13203 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13203 := by decide +kernel

def row13203 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

theorem rowCheck13203 : row13203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13203 := by decide +kernel

theorem rowEval13203 (x : Key → ℝ) : Integer.Sparse.eval row13203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13203, Integer.Sparse.eval_collectBalanced, rawRowCheck13203]

def rawRow13204 : Integer.Sparse Key := [(key2525, 4), (key2525, 4), (key2367, 4), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2521, -2), (key2460, -2), (key2521, -2), (key2365, -2), (key2460, -2), (key2365, -2), (key2457, 4), (key2457, 4), (key2362, 4)]

theorem rawRowCheck13204 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13204 := by decide +kernel

def row13204 : Integer.Sparse Key := [(key2362, 4), (key2365, -8), (key2367, 4), (key2457, 8), (key2460, -8), (key2521, -8), (key2525, 8)]

theorem rowCheck13204 : row13204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13204 := by decide +kernel

theorem rowEval13204 (x : Key → ℝ) : Integer.Sparse.eval row13204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13204, Integer.Sparse.eval_collectBalanced, rawRowCheck13204]

def rawRow13205 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1169, 4), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1183, 4), (key1183, 4), (key1220, 4)]

theorem rawRowCheck13205 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13205 := by decide +kernel

def row13205 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13205 : row13205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13205 := by decide +kernel

theorem rowEval13205 (x : Key → ℝ) : Integer.Sparse.eval row13205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13205, Integer.Sparse.eval_collectBalanced, rawRowCheck13205]

def rawRow13206 : Integer.Sparse Key := [(key1090, 4), (key1169, 4), (key1090, 4), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1183, 4), (key1220, 4), (key1183, 4)]

theorem rawRowCheck13206 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13206 := by decide +kernel

def row13206 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13206 : row13206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13206 := by decide +kernel

theorem rowEval13206 (x : Key → ℝ) : Integer.Sparse.eval row13206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13206, Integer.Sparse.eval_collectBalanced, rawRowCheck13206]

def rawRow13207 : Integer.Sparse Key := [(key1169, 4), (key1090, 4), (key1090, 4), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1220, 4), (key1183, 4), (key1183, 4)]

theorem rawRowCheck13207 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13207 := by decide +kernel

def row13207 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13207 : row13207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13207 := by decide +kernel

theorem rowEval13207 (x : Key → ℝ) : Integer.Sparse.eval row13207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13207, Integer.Sparse.eval_collectBalanced, rawRowCheck13207]

def rawRow13208 : Integer.Sparse Key := [(key1098, 4), (key1098, 4), (key1098, 4), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

theorem rawRowCheck13208 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13208 := by decide +kernel

def row13208 : Integer.Sparse Key := [(key1090, -12), (key1098, 12), (key1180, 12), (key1183, -12)]

theorem rowCheck13208 : row13208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13208 := by decide +kernel

theorem rowEval13208 (x : Key → ℝ) : Integer.Sparse.eval row13208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13208, Integer.Sparse.eval_collectBalanced, rawRowCheck13208]

def rawRow13209 : Integer.Sparse Key := [(key1090, 4), (key1090, 4), (key1169, 4), (key1180, -2), (key1183, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1220, -2), (key1090, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1169, -2), (key1183, 4), (key1183, 4), (key1220, 4)]

theorem rawRowCheck13209 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13209 := by decide +kernel

def row13209 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13209 : row13209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13209 := by decide +kernel

theorem rowEval13209 (x : Key → ℝ) : Integer.Sparse.eval row13209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13209, Integer.Sparse.eval_collectBalanced, rawRowCheck13209]

def rawRow13210 : Integer.Sparse Key := [(key1090, 4), (key1169, 4), (key1090, 4), (key1183, -2), (key1180, -2), (key1220, -2), (key1180, -2), (key1220, -2), (key1183, -2), (key1098, -2), (key1090, -2), (key1169, -2), (key1090, -2), (key1169, -2), (key1098, -2), (key1183, 4), (key1220, 4), (key1183, 4)]

theorem rawRowCheck13210 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13210 := by decide +kernel

def row13210 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13210 : row13210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13210 := by decide +kernel

theorem rowEval13210 (x : Key → ℝ) : Integer.Sparse.eval row13210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13210, Integer.Sparse.eval_collectBalanced, rawRowCheck13210]

def rawRow13211 : Integer.Sparse Key := [(key1169, 4), (key1090, 4), (key1090, 4), (key1220, -2), (key1220, -2), (key1183, -2), (key1183, -2), (key1180, -2), (key1180, -2), (key1169, -2), (key1169, -2), (key1098, -2), (key1098, -2), (key1090, -2), (key1090, -2), (key1220, 4), (key1183, 4), (key1183, 4)]

theorem rawRowCheck13211 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13211 := by decide +kernel

def row13211 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13211 : row13211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13211 := by decide +kernel

theorem rowEval13211 (x : Key → ℝ) : Integer.Sparse.eval row13211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13211, Integer.Sparse.eval_collectBalanced, rawRowCheck13211]

def rawRow13212 : Integer.Sparse Key := [(key976, 4), (key1180, 4), (key1220, 4), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key976, -2), (key984, -2), (key1090, -2), (key1169, -2), (key1183, -2), (key1220, -2), (key984, 4), (key1098, 4), (key1169, 4)]

theorem rawRowCheck13212 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0 = rawRow13212 := by decide +kernel

def row13212 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

theorem rowCheck13212 : row13212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13212 := by decide +kernel

theorem rowEval13212 (x : Key → ℝ) : Integer.Sparse.eval row13212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13212, Integer.Sparse.eval_collectBalanced, rawRowCheck13212]

def rawRow13213 : Integer.Sparse Key := [(key976, 4), (key1220, 4), (key1180, 4), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, -2), (key976, -2), (key1169, -2), (key1090, -2), (key1220, -2), (key1183, -2), (key984, 4), (key1169, 4), (key1098, 4)]

theorem rawRowCheck13213 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0 = rawRow13213 := by decide +kernel

def row13213 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

theorem rowCheck13213 : row13213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13213 := by decide +kernel

theorem rowEval13213 (x : Key → ℝ) : Integer.Sparse.eval row13213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13213, Integer.Sparse.eval_collectBalanced, rawRowCheck13213]

def rawRow13214 : Integer.Sparse Key := [(key1180, 4), (key976, 4), (key1220, 4), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1090, -2), (key1183, -2), (key976, -2), (key1220, -2), (key984, -2), (key1169, -2), (key1098, 4), (key984, 4), (key1169, 4)]

theorem rawRowCheck13214 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0 = rawRow13214 := by decide +kernel

def row13214 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

theorem rowCheck13214 : row13214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13214 := by decide +kernel

theorem rowEval13214 (x : Key → ℝ) : Integer.Sparse.eval row13214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13214, Integer.Sparse.eval_collectBalanced, rawRowCheck13214]

def rawRow13215 : Integer.Sparse Key := [(key1180, 4), (key1220, 4), (key976, 4), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1183, -2), (key1090, -2), (key1220, -2), (key976, -2), (key1169, -2), (key984, -2), (key1098, 4), (key1169, 4), (key984, 4)]

theorem rawRowCheck13215 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0 = rawRow13215 := by decide +kernel

def row13215 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

theorem rowCheck13215 : row13215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13215 := by decide +kernel

theorem rowEval13215 (x : Key → ℝ) : Integer.Sparse.eval row13215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13215, Integer.Sparse.eval_collectBalanced, rawRowCheck13215]

def rawRow13216 : Integer.Sparse Key := [(key1220, 4), (key976, 4), (key1180, 4), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, -2), (key1220, -2), (key984, -2), (key1183, -2), (key976, -2), (key1090, -2), (key1169, 4), (key984, 4), (key1098, 4)]

theorem rawRowCheck13216 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0 = rawRow13216 := by decide +kernel

def row13216 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

theorem rowCheck13216 : row13216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13216 := by decide +kernel

theorem rowEval13216 (x : Key → ℝ) : Integer.Sparse.eval row13216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13216, Integer.Sparse.eval_collectBalanced, rawRowCheck13216]

def rawRow13217 : Integer.Sparse Key := [(key1220, 4), (key1180, 4), (key976, 4), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1220, -2), (key1169, -2), (key1183, -2), (key984, -2), (key1090, -2), (key976, -2), (key1169, 4), (key1098, 4), (key984, 4)]

theorem rawRowCheck13217 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0 = rawRow13217 := by decide +kernel

def row13217 : Integer.Sparse Key := [(key1090, -4), (key1098, 4), (key1180, 4), (key1183, -4)]

theorem rowCheck13217 : row13217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13217 := by decide +kernel

theorem rowEval13217 (x : Key → ℝ) : Integer.Sparse.eval row13217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13217, Integer.Sparse.eval_collectBalanced, rawRowCheck13217]

def rawRow13218 : Integer.Sparse Key := [(key984, 4), (key1183, 4), (key1183, 4), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, 4), (key1090, 4), (key1090, 4)]

theorem rawRowCheck13218 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13218 := by decide +kernel

def row13218 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13218 : row13218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13218 := by decide +kernel

theorem rowEval13218 (x : Key → ℝ) : Integer.Sparse.eval row13218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13218, Integer.Sparse.eval_collectBalanced, rawRowCheck13218]

def rawRow13219 : Integer.Sparse Key := [(key1183, 4), (key984, 4), (key1183, 4), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, 4), (key976, 4), (key1090, 4)]

theorem rawRowCheck13219 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13219 := by decide +kernel

def row13219 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13219 : row13219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13219 := by decide +kernel

theorem rowEval13219 (x : Key → ℝ) : Integer.Sparse.eval row13219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13219, Integer.Sparse.eval_collectBalanced, rawRowCheck13219]

def rawRow13220 : Integer.Sparse Key := [(key1183, 4), (key1183, 4), (key984, 4), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1090, 4), (key1090, 4), (key976, 4)]

theorem rawRowCheck13220 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13220 := by decide +kernel

def row13220 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13220 : row13220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13220 := by decide +kernel

theorem rowEval13220 (x : Key → ℝ) : Integer.Sparse.eval row13220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13220, Integer.Sparse.eval_collectBalanced, rawRowCheck13220]

def rawRow13221 : Integer.Sparse Key := [(key1098, 4), (key1098, 4), (key1098, 4), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1183, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1090, -2), (key1180, 4), (key1180, 4), (key1180, 4)]

theorem rawRowCheck13221 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13221 := by decide +kernel

def row13221 : Integer.Sparse Key := [(key1090, -12), (key1098, 12), (key1180, 12), (key1183, -12)]

theorem rowCheck13221 : row13221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13221 := by decide +kernel

theorem rowEval13221 (x : Key → ℝ) : Integer.Sparse.eval row13221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13221, Integer.Sparse.eval_collectBalanced, rawRowCheck13221]

def rawRow13222 : Integer.Sparse Key := [(key984, 4), (key1183, 4), (key1183, 4), (key984, -2), (key984, -2), (key1098, -2), (key1098, -2), (key1183, -2), (key1183, -2), (key976, -2), (key976, -2), (key1090, -2), (key1090, -2), (key1180, -2), (key1180, -2), (key976, 4), (key1090, 4), (key1090, 4)]

theorem rawRowCheck13222 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13222 := by decide +kernel

def row13222 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13222 : row13222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13222 := by decide +kernel

theorem rowEval13222 (x : Key → ℝ) : Integer.Sparse.eval row13222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13222, Integer.Sparse.eval_collectBalanced, rawRowCheck13222]

def rawRow13223 : Integer.Sparse Key := [(key1183, 4), (key984, 4), (key1183, 4), (key1098, -2), (key1183, -2), (key984, -2), (key1183, -2), (key984, -2), (key1098, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1180, -2), (key976, -2), (key1090, -2), (key1090, 4), (key976, 4), (key1090, 4)]

theorem rawRowCheck13223 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13223 := by decide +kernel

def row13223 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13223 : row13223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13223 := by decide +kernel

theorem rowEval13223 (x : Key → ℝ) : Integer.Sparse.eval row13223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13223, Integer.Sparse.eval_collectBalanced, rawRowCheck13223]

def rawRow13224 : Integer.Sparse Key := [(key1183, 4), (key1183, 4), (key984, 4), (key1183, -2), (key1098, -2), (key1183, -2), (key984, -2), (key1098, -2), (key984, -2), (key1180, -2), (key1090, -2), (key1180, -2), (key976, -2), (key1090, -2), (key976, -2), (key1090, 4), (key1090, 4), (key976, 4)]

theorem rawRowCheck13224 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13224 := by decide +kernel

def row13224 : Integer.Sparse Key := [(key1090, 4), (key1098, -4), (key1180, -4), (key1183, 4)]

theorem rowCheck13224 : row13224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13224 := by decide +kernel

theorem rowEval13224 (x : Key → ℝ) : Integer.Sparse.eval row13224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13224, Integer.Sparse.eval_collectBalanced, rawRowCheck13224]

def rawRow13225 : Integer.Sparse Key := [(key1, -2), (key7, -2), (key7, -2), (key7, 6), (key84, -2), (key90, -2), (key90, -2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key90, -2), (key90, -2), (key151, -2), (key193, 6), (key193, -2), (key193, -2), (key202, -2)]

theorem rawRowCheck13225 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13225 := by decide +kernel

def row13225 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck13225 : row13225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13225 := by decide +kernel

theorem rowEval13225 (x : Key → ℝ) : Integer.Sparse.eval row13225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13225, Integer.Sparse.eval_collectBalanced, rawRowCheck13225]

def rawRow13226 : Integer.Sparse Key := [(key7, -2), (key1, -2), (key7, -2), (key7, 6), (key90, -2), (key84, -2), (key90, -2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key90, -2), (key151, -2), (key90, -2), (key193, 6), (key193, -2), (key202, -2), (key193, -2)]

theorem rawRowCheck13226 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13226 := by decide +kernel

def row13226 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck13226 : row13226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13226 := by decide +kernel

theorem rowEval13226 (x : Key → ℝ) : Integer.Sparse.eval row13226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13226, Integer.Sparse.eval_collectBalanced, rawRowCheck13226]

def rawRow13227 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key1, -2), (key7, 6), (key90, -2), (key90, -2), (key84, -2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key151, -2), (key90, -2), (key90, -2), (key193, 6), (key202, -2), (key193, -2), (key193, -2)]

theorem rawRowCheck13227 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13227 := by decide +kernel

def row13227 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck13227 : row13227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13227 := by decide +kernel

theorem rowEval13227 (x : Key → ℝ) : Integer.Sparse.eval row13227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13227, Integer.Sparse.eval_collectBalanced, rawRowCheck13227]

def rawRow13228 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key7, -2), (key1, 6), (key151, -2), (key151, -2), (key151, -2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key84, -2), (key84, -2), (key84, -2), (key202, 6), (key193, -2), (key193, -2), (key193, -2)]

theorem rawRowCheck13228 : GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13228 := by decide +kernel

def row13228 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key90, 12), (key151, -6), (key193, -6), (key202, 6)]

theorem rowCheck13228 : row13228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13228 := by decide +kernel

theorem rowEval13228 (x : Key → ℝ) : Integer.Sparse.eval row13228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13228, Integer.Sparse.eval_collectBalanced, rawRowCheck13228]

def rawRow13229 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key90, -2), (key151, 6), (key1, -2), (key7, -2), (key7, -2), (key84, 2), (key90, 2), (key84, 2), (key151, 2), (key90, 2), (key151, 2), (key193, -2), (key193, -2), (key202, -2), (key7, 6), (key90, -2), (key90, -2), (key151, -2)]

theorem rawRowCheck13229 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13229 := by decide +kernel

def row13229 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck13229 : row13229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13229 := by decide +kernel

theorem rowEval13229 (x : Key → ℝ) : Integer.Sparse.eval row13229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13229, Integer.Sparse.eval_collectBalanced, rawRowCheck13229]

def rawRow13230 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key90, -2), (key151, 6), (key7, -2), (key1, -2), (key7, -2), (key90, 2), (key84, 2), (key151, 2), (key84, 2), (key151, 2), (key90, 2), (key193, -2), (key202, -2), (key193, -2), (key7, 6), (key90, -2), (key151, -2), (key90, -2)]

theorem rawRowCheck13230 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13230 := by decide +kernel

def row13230 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck13230 : row13230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13230 := by decide +kernel

theorem rowEval13230 (x : Key → ℝ) : Integer.Sparse.eval row13230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13230, Integer.Sparse.eval_collectBalanced, rawRowCheck13230]

def rawRow13231 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key84, -2), (key151, 6), (key7, -2), (key7, -2), (key1, -2), (key151, 2), (key151, 2), (key90, 2), (key90, 2), (key84, 2), (key84, 2), (key202, -2), (key193, -2), (key193, -2), (key7, 6), (key151, -2), (key90, -2), (key90, -2)]

theorem rawRowCheck13231 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13231 := by decide +kernel

def row13231 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck13231 : row13231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13231 := by decide +kernel

theorem rowEval13231 (x : Key → ℝ) : Integer.Sparse.eval row13231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13231, Integer.Sparse.eval_collectBalanced, rawRowCheck13231]

def rawRow13232 : Integer.Sparse Key := [(key84, -2), (key90, -2), (key151, -2), (key90, 6), (key84, -2), (key90, -2), (key151, -2), (key1, 2), (key7, 2), (key84, 2), (key151, 2), (key193, 2), (key202, 2), (key7, -2), (key90, -2), (key151, -2), (key90, 6), (key7, -2), (key90, -2), (key151, -2)]

theorem rawRowCheck13232 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1 = rawRow13232 := by decide +kernel

def row13232 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

theorem rowCheck13232 : row13232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13232 := by decide +kernel

theorem rowEval13232 (x : Key → ℝ) : Integer.Sparse.eval row13232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13232, Integer.Sparse.eval_collectBalanced, rawRowCheck13232]

def rawRow13233 : Integer.Sparse Key := [(key90, -2), (key84, -2), (key151, -2), (key90, 6), (key90, -2), (key84, -2), (key151, -2), (key7, 2), (key1, 2), (key151, 2), (key84, 2), (key202, 2), (key193, 2), (key7, -2), (key151, -2), (key90, -2), (key90, 6), (key7, -2), (key151, -2), (key90, -2)]

theorem rawRowCheck13233 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1 = rawRow13233 := by decide +kernel

def row13233 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

theorem rowCheck13233 : row13233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13233 := by decide +kernel

theorem rowEval13233 (x : Key → ℝ) : Integer.Sparse.eval row13233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13233, Integer.Sparse.eval_collectBalanced, rawRowCheck13233]

def rawRow13234 : Integer.Sparse Key := [(key84, -2), (key151, -2), (key90, -2), (key90, 6), (key84, -2), (key151, -2), (key90, -2), (key84, 2), (key151, 2), (key1, 2), (key202, 2), (key7, 2), (key151, 2), (key90, -2), (key7, -2), (key151, -2), (key90, 6), (key90, -2), (key7, -2), (key151, -2)]

theorem rawRowCheck13234 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1 = rawRow13234 := by decide +kernel

def row13234 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -4), (key202, 2)]

theorem rowCheck13234 : row13234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13234 := by decide +kernel

theorem rowEval13234 (x : Key → ℝ) : Integer.Sparse.eval row13234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13234, Integer.Sparse.eval_collectBalanced, rawRowCheck13234]

def rawRow13235 : Integer.Sparse Key := [(key151, -2), (key84, -2), (key90, -2), (key90, 6), (key151, -2), (key84, -2), (key90, -2), (key151, 2), (key84, 2), (key202, 2), (key1, 2), (key151, 2), (key7, 2), (key90, -2), (key151, -2), (key7, -2), (key90, 6), (key90, -2), (key151, -2), (key7, -2)]

theorem rawRowCheck13235 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1 = rawRow13235 := by decide +kernel

def row13235 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -4), (key202, 2)]

theorem rowCheck13235 : row13235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13235 := by decide +kernel

theorem rowEval13235 (x : Key → ℝ) : Integer.Sparse.eval row13235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13235, Integer.Sparse.eval_collectBalanced, rawRowCheck13235]

def rawRow13236 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key84, -2), (key90, 6), (key90, -2), (key151, -2), (key84, -2), (key193, 2), (key202, 2), (key7, 2), (key151, 2), (key1, 2), (key84, 2), (key151, -2), (key7, -2), (key90, -2), (key90, 6), (key151, -2), (key7, -2), (key90, -2)]

theorem rawRowCheck13236 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1 = rawRow13236 := by decide +kernel

def row13236 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

theorem rowCheck13236 : row13236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13236 := by decide +kernel

theorem rowEval13236 (x : Key → ℝ) : Integer.Sparse.eval row13236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13236, Integer.Sparse.eval_collectBalanced, rawRowCheck13236]

def rawRow13237 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key84, -2), (key90, 6), (key151, -2), (key90, -2), (key84, -2), (key202, 2), (key193, 2), (key151, 2), (key7, 2), (key84, 2), (key1, 2), (key151, -2), (key90, -2), (key7, -2), (key90, 6), (key151, -2), (key90, -2), (key7, -2)]

theorem rawRowCheck13237 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1 = rawRow13237 := by decide +kernel

def row13237 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key90, 4), (key151, -6), (key193, 2), (key202, 2)]

theorem rowCheck13237 : row13237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13237 := by decide +kernel

theorem rowEval13237 (x : Key → ℝ) : Integer.Sparse.eval row13237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13237, Integer.Sparse.eval_collectBalanced, rawRowCheck13237]

def rawRow13238 : Integer.Sparse Key := [(key90, -2), (key90, -2), (key151, -2), (key84, 6), (key193, -2), (key193, -2), (key202, -2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key1, -2), (key84, -2), (key84, -2), (key151, 6), (key7, -2), (key90, -2), (key90, -2)]

theorem rawRowCheck13238 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13238 := by decide +kernel

def row13238 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck13238 : row13238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13238 := by decide +kernel

theorem rowEval13238 (x : Key → ℝ) : Integer.Sparse.eval row13238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13238, Integer.Sparse.eval_collectBalanced, rawRowCheck13238]

def rawRow13239 : Integer.Sparse Key := [(key90, -2), (key151, -2), (key90, -2), (key84, 6), (key193, -2), (key202, -2), (key193, -2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key84, -2), (key1, -2), (key84, -2), (key151, 6), (key90, -2), (key7, -2), (key90, -2)]

theorem rawRowCheck13239 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13239 := by decide +kernel

def row13239 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck13239 : row13239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13239 := by decide +kernel

theorem rowEval13239 (x : Key → ℝ) : Integer.Sparse.eval row13239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13239, Integer.Sparse.eval_collectBalanced, rawRowCheck13239]

def rawRow13240 : Integer.Sparse Key := [(key151, -2), (key90, -2), (key90, -2), (key84, 6), (key202, -2), (key193, -2), (key193, -2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key84, -2), (key84, -2), (key1, -2), (key151, 6), (key90, -2), (key90, -2), (key7, -2)]

theorem rawRowCheck13240 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13240 := by decide +kernel

def row13240 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 8), (key193, -4), (key202, -2)]

theorem rowCheck13240 : row13240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13240 := by decide +kernel

theorem rowEval13240 (x : Key → ℝ) : Integer.Sparse.eval row13240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13240, Integer.Sparse.eval_collectBalanced, rawRowCheck13240]

def rawRow13241 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key193, -2), (key202, 6), (key7, -2), (key7, -2), (key7, -2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key90, 2), (key151, -2), (key151, -2), (key151, -2), (key1, 6), (key84, -2), (key84, -2), (key84, -2)]

theorem rawRowCheck13241 : GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13241 := by decide +kernel

def row13241 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key90, 12), (key151, -6), (key193, -6), (key202, 6)]

theorem rowCheck13241 : row13241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13241 := by decide +kernel

theorem rowEval13241 (x : Key → ℝ) : Integer.Sparse.eval row13241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13241, Integer.Sparse.eval_collectBalanced, rawRowCheck13241]

def rawRow13242 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key202, -2), (key193, 6), (key90, -2), (key90, -2), (key151, -2), (key7, 2), (key7, 2), (key90, 2), (key90, 2), (key151, 2), (key151, 2), (key7, -2), (key90, -2), (key90, -2), (key84, 6), (key1, -2), (key84, -2), (key84, -2)]

theorem rawRowCheck13242 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13242 := by decide +kernel

def row13242 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck13242 : row13242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13242 := by decide +kernel

theorem rowEval13242 (x : Key → ℝ) : Integer.Sparse.eval row13242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13242, Integer.Sparse.eval_collectBalanced, rawRowCheck13242]

def rawRow13243 : Integer.Sparse Key := [(key193, -2), (key202, -2), (key193, -2), (key193, 6), (key90, -2), (key151, -2), (key90, -2), (key90, 2), (key151, 2), (key7, 2), (key151, 2), (key7, 2), (key90, 2), (key90, -2), (key7, -2), (key90, -2), (key84, 6), (key84, -2), (key1, -2), (key84, -2)]

theorem rawRowCheck13243 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13243 := by decide +kernel

def row13243 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck13243 : row13243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13243 := by decide +kernel

theorem rowEval13243 (x : Key → ℝ) : Integer.Sparse.eval row13243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13243, Integer.Sparse.eval_collectBalanced, rawRowCheck13243]

def rawRow13244 : Integer.Sparse Key := [(key202, -2), (key193, -2), (key193, -2), (key193, 6), (key151, -2), (key90, -2), (key90, -2), (key151, 2), (key90, 2), (key151, 2), (key7, 2), (key90, 2), (key7, 2), (key90, -2), (key90, -2), (key7, -2), (key84, 6), (key84, -2), (key84, -2), (key1, -2)]

theorem rawRowCheck13244 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13244 := by decide +kernel

def row13244 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key90, -4), (key151, 2), (key193, 2), (key202, -2)]

theorem rowCheck13244 : row13244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13244 := by decide +kernel

theorem rowEval13244 (x : Key → ℝ) : Integer.Sparse.eval row13244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13244, Integer.Sparse.eval_collectBalanced, rawRowCheck13244]

def rawRow13245 : Integer.Sparse Key := [(key2452, 4), (key2452, 4), (key2519, 4), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2530, 4), (key2530, 4), (key2560, 4)]

theorem rawRowCheck13245 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13245 := by decide +kernel

def row13245 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

theorem rowCheck13245 : row13245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13245 := by decide +kernel

theorem rowEval13245 (x : Key → ℝ) : Integer.Sparse.eval row13245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13245, Integer.Sparse.eval_collectBalanced, rawRowCheck13245]

def rawRow13246 : Integer.Sparse Key := [(key2452, 4), (key2519, 4), (key2452, 4), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2530, 4), (key2560, 4), (key2530, 4)]

theorem rawRowCheck13246 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13246 := by decide +kernel

def row13246 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

theorem rowCheck13246 : row13246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13246 := by decide +kernel

theorem rowEval13246 (x : Key → ℝ) : Integer.Sparse.eval row13246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13246, Integer.Sparse.eval_collectBalanced, rawRowCheck13246]

def rawRow13247 : Integer.Sparse Key := [(key2519, 4), (key2452, 4), (key2452, 4), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2560, 4), (key2530, 4), (key2530, 4)]

theorem rawRowCheck13247 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13247 := by decide +kernel

def row13247 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

theorem rowCheck13247 : row13247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13247 := by decide +kernel

theorem rowEval13247 (x : Key → ℝ) : Integer.Sparse.eval row13247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13247, Integer.Sparse.eval_collectBalanced, rawRowCheck13247]

def rawRow13248 : Integer.Sparse Key := [(key2458, 4), (key2458, 4), (key2458, 4), (key2452, -2), (key2452, -2), (key2452, -2), (key2452, -2), (key2452, -2), (key2452, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2530, -2), (key2528, 4), (key2528, 4), (key2528, 4)]

theorem rawRowCheck13248 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13248 := by decide +kernel

def row13248 : Integer.Sparse Key := [(key2452, -12), (key2458, 12), (key2528, 12), (key2530, -12)]

theorem rowCheck13248 : row13248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13248 := by decide +kernel

theorem rowEval13248 (x : Key → ℝ) : Integer.Sparse.eval row13248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13248, Integer.Sparse.eval_collectBalanced, rawRowCheck13248]

def rawRow13249 : Integer.Sparse Key := [(key2452, 4), (key2452, 4), (key2519, 4), (key2528, -2), (key2530, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2560, -2), (key2452, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2519, -2), (key2530, 4), (key2530, 4), (key2560, 4)]

theorem rawRowCheck13249 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0 = rawRow13249 := by decide +kernel

def row13249 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

theorem rowCheck13249 : row13249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13249 := by decide +kernel

theorem rowEval13249 (x : Key → ℝ) : Integer.Sparse.eval row13249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13249, Integer.Sparse.eval_collectBalanced, rawRowCheck13249]

def rawRow13250 : Integer.Sparse Key := [(key2452, 4), (key2519, 4), (key2452, 4), (key2530, -2), (key2528, -2), (key2560, -2), (key2528, -2), (key2560, -2), (key2530, -2), (key2458, -2), (key2452, -2), (key2519, -2), (key2452, -2), (key2519, -2), (key2458, -2), (key2530, 4), (key2560, 4), (key2530, 4)]

theorem rawRowCheck13250 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0 = rawRow13250 := by decide +kernel

def row13250 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

theorem rowCheck13250 : row13250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13250 := by decide +kernel

theorem rowEval13250 (x : Key → ℝ) : Integer.Sparse.eval row13250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13250, Integer.Sparse.eval_collectBalanced, rawRowCheck13250]

def rawRow13251 : Integer.Sparse Key := [(key2519, 4), (key2452, 4), (key2452, 4), (key2560, -2), (key2560, -2), (key2530, -2), (key2530, -2), (key2528, -2), (key2528, -2), (key2519, -2), (key2519, -2), (key2458, -2), (key2458, -2), (key2452, -2), (key2452, -2), (key2560, 4), (key2530, 4), (key2530, 4)]

theorem rawRowCheck13251 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0 = rawRow13251 := by decide +kernel

def row13251 : Integer.Sparse Key := [(key2452, 4), (key2458, -4), (key2528, -4), (key2530, 4)]

theorem rowCheck13251 : row13251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13251 := by decide +kernel

theorem rowEval13251 (x : Key → ℝ) : Integer.Sparse.eval row13251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13251, Integer.Sparse.eval_collectBalanced, rawRowCheck13251]

def rawRow13252 : Integer.Sparse Key := [(key2357, 4), (key2528, 4), (key2560, 4), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2357, -2), (key2363, -2), (key2452, -2), (key2519, -2), (key2530, -2), (key2560, -2), (key2363, 4), (key2458, 4), (key2519, 4)]

theorem rawRowCheck13252 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0 = rawRow13252 := by decide +kernel

def row13252 : Integer.Sparse Key := [(key2452, -4), (key2458, 4), (key2528, 4), (key2530, -4)]

theorem rowCheck13252 : row13252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13252 := by decide +kernel

theorem rowEval13252 (x : Key → ℝ) : Integer.Sparse.eval row13252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13252, Integer.Sparse.eval_collectBalanced, rawRowCheck13252]

def rawRow13253 : Integer.Sparse Key := [(key2361, 4), (key2560, 4), (key2528, 4), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, -2), (key2357, -2), (key2519, -2), (key2452, -2), (key2560, -2), (key2530, -2), (key2363, 4), (key2519, 4), (key2458, 4)]

theorem rawRowCheck13253 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0 = rawRow13253 := by decide +kernel

def row13253 : Integer.Sparse Key := [(key2357, -4), (key2361, 4), (key2452, -4), (key2458, 4), (key2528, 4), (key2530, -4)]

theorem rowCheck13253 : row13253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13253 := by decide +kernel

theorem rowEval13253 (x : Key → ℝ) : Integer.Sparse.eval row13253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13253, Integer.Sparse.eval_collectBalanced, rawRowCheck13253]

def rawRow13254 : Integer.Sparse Key := [(key2517, 4), (key2357, 4), (key2560, 4), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2452, -2), (key2530, -2), (key2357, -2), (key2560, -2), (key2363, -2), (key2519, -2), (key2458, 4), (key2363, 4), (key2519, 4)]

theorem rawRowCheck13254 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0 = rawRow13254 := by decide +kernel

def row13254 : Integer.Sparse Key := [(key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4)]

theorem rowCheck13254 : row13254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13254 := by decide +kernel

theorem rowEval13254 (x : Key → ℝ) : Integer.Sparse.eval row13254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck13254, Integer.Sparse.eval_collectBalanced, rawRowCheck13254]

def rawRow13255 : Integer.Sparse Key := [(key2517, 4), (key2560, 4), (key2357, 4), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2530, -2), (key2452, -2), (key2560, -2), (key2357, -2), (key2519, -2), (key2363, -2), (key2458, 4), (key2519, 4), (key2363, 4)]

theorem rawRowCheck13255 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0 = rawRow13255 := by decide +kernel

def row13255 : Integer.Sparse Key := [(key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4)]

theorem rowCheck13255 : row13255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13255 := by decide +kernel

theorem rowEval13255 (x : Key → ℝ) : Integer.Sparse.eval row13255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13255, Integer.Sparse.eval_collectBalanced, rawRowCheck13255]

def rawRow13256 : Integer.Sparse Key := [(key2579, 4), (key2361, 4), (key2517, 4), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, -2), (key2560, -2), (key2363, -2), (key2530, -2), (key2357, -2), (key2452, -2), (key2519, 4), (key2363, 4), (key2458, 4)]

theorem rawRowCheck13256 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0 = rawRow13256 := by decide +kernel

def row13256 : Integer.Sparse Key := [(key2357, -4), (key2361, 4), (key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4), (key2560, -4), (key2579, 4)]

theorem rowCheck13256 : row13256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13256 := by decide +kernel

theorem rowEval13256 (x : Key → ℝ) : Integer.Sparse.eval row13256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13256, Integer.Sparse.eval_collectBalanced, rawRowCheck13256]

def rawRow13257 : Integer.Sparse Key := [(key2579, 4), (key2517, 4), (key2361, 4), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2560, -2), (key2519, -2), (key2530, -2), (key2363, -2), (key2452, -2), (key2357, -2), (key2519, 4), (key2458, 4), (key2363, 4)]

theorem rawRowCheck13257 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0 = rawRow13257 := by decide +kernel

def row13257 : Integer.Sparse Key := [(key2357, -4), (key2361, 4), (key2452, -4), (key2458, 4), (key2517, 4), (key2530, -4), (key2560, -4), (key2579, 4)]

theorem rowCheck13257 : row13257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13257 := by decide +kernel

theorem rowEval13257 (x : Key → ℝ) : Integer.Sparse.eval row13257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13257, Integer.Sparse.eval_collectBalanced, rawRowCheck13257]

def rawRow13258 : Integer.Sparse Key := [(key2366, 4), (key2523, 4), (key2523, 4), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2363, -2), (key2363, -2), (key2458, -2), (key2458, -2), (key2530, -2), (key2530, -2), (key2357, 4), (key2452, 4), (key2452, 4)]

theorem rawRowCheck13258 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13258 := by decide +kernel

def row13258 : Integer.Sparse Key := [(key2357, 4), (key2361, -4), (key2363, -4), (key2366, 4), (key2452, 8), (key2456, -4), (key2458, -4), (key2517, -4), (key2523, 8), (key2530, -4)]

theorem rowCheck13258 : row13258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13258 := by decide +kernel

theorem rowEval13258 (x : Key → ℝ) : Integer.Sparse.eval row13258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13258, Integer.Sparse.eval_collectBalanced, rawRowCheck13258]

def rawRow13259 : Integer.Sparse Key := [(key2523, 4), (key2366, 4), (key2523, 4), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2452, 4), (key2357, 4), (key2452, 4)]

theorem rawRowCheck13259 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13259 := by decide +kernel

def row13259 : Integer.Sparse Key := [(key2357, 4), (key2361, -4), (key2363, -4), (key2366, 4), (key2452, 8), (key2456, -4), (key2458, -4), (key2517, -4), (key2523, 8), (key2530, -4)]

theorem rowCheck13259 : row13259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13259 := by decide +kernel

theorem rowEval13259 (x : Key → ℝ) : Integer.Sparse.eval row13259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13259, Integer.Sparse.eval_collectBalanced, rawRowCheck13259]

def rawRow13260 : Integer.Sparse Key := [(key2523, 4), (key2523, 4), (key2366, 4), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2530, -2), (key2458, -2), (key2530, -2), (key2363, -2), (key2458, -2), (key2363, -2), (key2452, 4), (key2452, 4), (key2357, 4)]

theorem rawRowCheck13260 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13260 := by decide +kernel

def row13260 : Integer.Sparse Key := [(key2357, 4), (key2361, -4), (key2363, -4), (key2366, 4), (key2452, 8), (key2456, -4), (key2458, -4), (key2517, -4), (key2523, 8), (key2530, -4)]

theorem rowCheck13260 : row13260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13260 := by decide +kernel

theorem rowEval13260 (x : Key → ℝ) : Integer.Sparse.eval row13260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13260, Integer.Sparse.eval_collectBalanced, rawRowCheck13260]

def rawRow13261 : Integer.Sparse Key := [(key2461, 4), (key2461, 4), (key2461, 4), (key2523, -2), (key2523, -2), (key2523, -2), (key2523, -2), (key2523, -2), (key2523, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, 4), (key2517, 4), (key2517, 4)]

theorem rawRowCheck13261 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13261 := by decide +kernel

def row13261 : Integer.Sparse Key := [(key2456, -12), (key2461, 12), (key2517, 12), (key2523, -12)]

theorem rowCheck13261 : row13261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13261 := by decide +kernel

theorem rowEval13261 (x : Key → ℝ) : Integer.Sparse.eval row13261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13261, Integer.Sparse.eval_collectBalanced, rawRowCheck13261]

def rawRow13262 : Integer.Sparse Key := [(key2366, 4), (key2523, 4), (key2523, 4), (key2366, -2), (key2366, -2), (key2461, -2), (key2461, -2), (key2523, -2), (key2523, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, 4), (key2456, 4), (key2456, 4)]

theorem rawRowCheck13262 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0 = rawRow13262 := by decide +kernel

def row13262 : Integer.Sparse Key := [(key2456, 4), (key2461, -4), (key2517, -4), (key2523, 4)]

theorem rowCheck13262 : row13262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13262 := by decide +kernel

theorem rowEval13262 (x : Key → ℝ) : Integer.Sparse.eval row13262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13262, Integer.Sparse.eval_collectBalanced, rawRowCheck13262]

def rawRow13263 : Integer.Sparse Key := [(key2523, 4), (key2366, 4), (key2523, 4), (key2461, -2), (key2523, -2), (key2366, -2), (key2523, -2), (key2366, -2), (key2461, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, 4), (key2361, 4), (key2456, 4)]

theorem rawRowCheck13263 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0 = rawRow13263 := by decide +kernel

def row13263 : Integer.Sparse Key := [(key2456, 4), (key2461, -4), (key2517, -4), (key2523, 4)]

theorem rowCheck13263 : row13263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13263 := by decide +kernel

theorem rowEval13263 (x : Key → ℝ) : Integer.Sparse.eval row13263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13263, Integer.Sparse.eval_collectBalanced, rawRowCheck13263]

def rawRow13264 : Integer.Sparse Key := [(key2523, 4), (key2523, 4), (key2366, 4), (key2523, -2), (key2461, -2), (key2523, -2), (key2366, -2), (key2461, -2), (key2366, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, 4), (key2456, 4), (key2361, 4)]

theorem rawRowCheck13264 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0 = rawRow13264 := by decide +kernel

def row13264 : Integer.Sparse Key := [(key2456, 4), (key2461, -4), (key2517, -4), (key2523, 4)]

theorem rowCheck13264 : row13264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13264 := by decide +kernel

theorem rowEval13264 (x : Key → ℝ) : Integer.Sparse.eval row13264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form0) x := by
  rw [rowCheck13264, Integer.Sparse.eval_collectBalanced, rawRowCheck13264]

def rawRow13265 : Integer.Sparse Key := [(key971, -2), (key979, -2), (key979, -2), (key979, 6), (key1085, -2), (key1093, -2), (key1093, -2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1093, -2), (key1093, -2), (key1228, -2), (key1164, 6), (key1164, -2), (key1164, -2), (key1245, -2)]

theorem rawRowCheck13265 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13265 := by decide +kernel

def row13265 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13265 : row13265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13265 := by decide +kernel

theorem rowEval13265 (x : Key → ℝ) : Integer.Sparse.eval row13265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13265, Integer.Sparse.eval_collectBalanced, rawRowCheck13265]

def rawRow13266 : Integer.Sparse Key := [(key979, -2), (key971, -2), (key979, -2), (key979, 6), (key1093, -2), (key1085, -2), (key1093, -2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1093, -2), (key1228, -2), (key1093, -2), (key1164, 6), (key1164, -2), (key1245, -2), (key1164, -2)]

theorem rawRowCheck13266 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13266 := by decide +kernel

def row13266 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13266 : row13266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13266 := by decide +kernel

theorem rowEval13266 (x : Key → ℝ) : Integer.Sparse.eval row13266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13266, Integer.Sparse.eval_collectBalanced, rawRowCheck13266]

def rawRow13267 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key971, -2), (key979, 6), (key1093, -2), (key1093, -2), (key1085, -2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1228, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key1245, -2), (key1164, -2), (key1164, -2)]

theorem rawRowCheck13267 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13267 := by decide +kernel

def row13267 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13267 : row13267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13267 := by decide +kernel

theorem rowEval13267 (x : Key → ℝ) : Integer.Sparse.eval row13267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13267, Integer.Sparse.eval_collectBalanced, rawRowCheck13267]

def rawRow13268 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key979, -2), (key971, 6), (key1228, -2), (key1228, -2), (key1228, -2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1245, 6), (key1164, -2), (key1164, -2), (key1164, -2)]

theorem rawRowCheck13268 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13268 := by decide +kernel

def row13268 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1093, 12), (key1164, -6), (key1228, -6), (key1245, 6)]

theorem rowCheck13268 : row13268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13268 := by decide +kernel

theorem rowEval13268 (x : Key → ℝ) : Integer.Sparse.eval row13268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13268, Integer.Sparse.eval_collectBalanced, rawRowCheck13268]

def rawRow13269 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1093, -2), (key1164, 6), (key971, -2), (key979, -2), (key979, -2), (key1085, 2), (key1093, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1228, 2), (key1164, -2), (key1164, -2), (key1245, -2), (key979, 6), (key1093, -2), (key1093, -2), (key1228, -2)]

theorem rawRowCheck13269 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1 = rawRow13269 := by decide +kernel

def row13269 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13269 : row13269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13269 := by decide +kernel

theorem rowEval13269 (x : Key → ℝ) : Integer.Sparse.eval row13269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13269, Integer.Sparse.eval_collectBalanced, rawRowCheck13269]

def rawRow13270 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1093, -2), (key1164, 6), (key979, -2), (key971, -2), (key979, -2), (key1093, 2), (key1085, 2), (key1228, 2), (key1085, 2), (key1228, 2), (key1093, 2), (key1164, -2), (key1245, -2), (key1164, -2), (key979, 6), (key1093, -2), (key1228, -2), (key1093, -2)]

theorem rawRowCheck13270 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1 = rawRow13270 := by decide +kernel

def row13270 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13270 : row13270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13270 := by decide +kernel

theorem rowEval13270 (x : Key → ℝ) : Integer.Sparse.eval row13270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13270, Integer.Sparse.eval_collectBalanced, rawRowCheck13270]

def rawRow13271 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1085, -2), (key1164, 6), (key979, -2), (key979, -2), (key971, -2), (key1228, 2), (key1228, 2), (key1093, 2), (key1093, 2), (key1085, 2), (key1085, 2), (key1245, -2), (key1164, -2), (key1164, -2), (key979, 6), (key1228, -2), (key1093, -2), (key1093, -2)]

theorem rawRowCheck13271 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1 = rawRow13271 := by decide +kernel

def row13271 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13271 : row13271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13271 := by decide +kernel

theorem rowEval13271 (x : Key → ℝ) : Integer.Sparse.eval row13271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13271, Integer.Sparse.eval_collectBalanced, rawRowCheck13271]

def rawRow13272 : Integer.Sparse Key := [(key1085, -2), (key1093, -2), (key1164, -2), (key1093, 6), (key1085, -2), (key1093, -2), (key1164, -2), (key971, 2), (key979, 2), (key1085, 2), (key1228, 2), (key1164, 2), (key1245, 2), (key979, -2), (key1093, -2), (key1228, -2), (key1093, 6), (key979, -2), (key1093, -2), (key1228, -2)]

theorem rawRowCheck13272 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1 = rawRow13272 := by decide +kernel

def row13272 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck13272 : row13272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13272 := by decide +kernel

theorem rowEval13272 (x : Key → ℝ) : Integer.Sparse.eval row13272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13272, Integer.Sparse.eval_collectBalanced, rawRowCheck13272]

def rawRow13273 : Integer.Sparse Key := [(key1093, -2), (key1085, -2), (key1164, -2), (key1093, 6), (key1093, -2), (key1085, -2), (key1164, -2), (key979, 2), (key971, 2), (key1228, 2), (key1085, 2), (key1245, 2), (key1164, 2), (key979, -2), (key1228, -2), (key1093, -2), (key1093, 6), (key979, -2), (key1228, -2), (key1093, -2)]

theorem rawRowCheck13273 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1 = rawRow13273 := by decide +kernel

def row13273 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck13273 : row13273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13273 := by decide +kernel

theorem rowEval13273 (x : Key → ℝ) : Integer.Sparse.eval row13273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13273, Integer.Sparse.eval_collectBalanced, rawRowCheck13273]

def rawRow13274 : Integer.Sparse Key := [(key1085, -2), (key1164, -2), (key1093, -2), (key1093, 6), (key1085, -2), (key1164, -2), (key1093, -2), (key1085, 2), (key1164, 2), (key971, 2), (key1245, 2), (key979, 2), (key1228, 2), (key1093, -2), (key979, -2), (key1228, -2), (key1093, 6), (key1093, -2), (key979, -2), (key1228, -2)]

theorem rawRowCheck13274 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1 = rawRow13274 := by decide +kernel

def row13274 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck13274 : row13274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13274 := by decide +kernel

theorem rowEval13274 (x : Key → ℝ) : Integer.Sparse.eval row13274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form1) x := by
  rw [rowCheck13274, Integer.Sparse.eval_collectBalanced, rawRowCheck13274]

def rawRow13275 : Integer.Sparse Key := [(key1164, -2), (key1085, -2), (key1093, -2), (key1093, 6), (key1164, -2), (key1085, -2), (key1093, -2), (key1164, 2), (key1085, 2), (key1245, 2), (key971, 2), (key1228, 2), (key979, 2), (key1093, -2), (key1228, -2), (key979, -2), (key1093, 6), (key1093, -2), (key1228, -2), (key979, -2)]

theorem rawRowCheck13275 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1 = rawRow13275 := by decide +kernel

def row13275 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck13275 : row13275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13275 := by decide +kernel

theorem rowEval13275 (x : Key → ℝ) : Integer.Sparse.eval row13275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13275, Integer.Sparse.eval_collectBalanced, rawRowCheck13275]

def rawRow13276 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1085, -2), (key1093, 6), (key1093, -2), (key1164, -2), (key1085, -2), (key1228, 2), (key1245, 2), (key979, 2), (key1164, 2), (key971, 2), (key1085, 2), (key1228, -2), (key979, -2), (key1093, -2), (key1093, 6), (key1228, -2), (key979, -2), (key1093, -2)]

theorem rawRowCheck13276 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1 = rawRow13276 := by decide +kernel

def row13276 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck13276 : row13276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13276 := by decide +kernel

theorem rowEval13276 (x : Key → ℝ) : Integer.Sparse.eval row13276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13276, Integer.Sparse.eval_collectBalanced, rawRowCheck13276]

def rawRow13277 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1085, -2), (key1093, 6), (key1164, -2), (key1093, -2), (key1085, -2), (key1245, 2), (key1228, 2), (key1164, 2), (key979, 2), (key1085, 2), (key971, 2), (key1228, -2), (key1093, -2), (key979, -2), (key1093, 6), (key1228, -2), (key1093, -2), (key979, -2)]

theorem rawRowCheck13277 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1 = rawRow13277 := by decide +kernel

def row13277 : Integer.Sparse Key := [(key971, 2), (key979, -2), (key1085, -2), (key1093, 4), (key1164, -2), (key1228, -2), (key1245, 2)]

theorem rowCheck13277 : row13277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13277 := by decide +kernel

theorem rowEval13277 (x : Key → ℝ) : Integer.Sparse.eval row13277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13277, Integer.Sparse.eval_collectBalanced, rawRowCheck13277]

def rawRow13278 : Integer.Sparse Key := [(key1093, -2), (key1093, -2), (key1164, -2), (key1085, 6), (key1228, -2), (key1228, -2), (key1245, -2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key971, -2), (key1085, -2), (key1085, -2), (key1228, 6), (key979, -2), (key1093, -2), (key1093, -2)]

theorem rawRowCheck13278 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13278 := by decide +kernel

def row13278 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13278 : row13278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13278 := by decide +kernel

theorem rowEval13278 (x : Key → ℝ) : Integer.Sparse.eval row13278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13278, Integer.Sparse.eval_collectBalanced, rawRowCheck13278]

def rawRow13279 : Integer.Sparse Key := [(key1093, -2), (key1164, -2), (key1093, -2), (key1085, 6), (key1228, -2), (key1245, -2), (key1228, -2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1085, -2), (key971, -2), (key1085, -2), (key1228, 6), (key1093, -2), (key979, -2), (key1093, -2)]

theorem rawRowCheck13279 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13279 := by decide +kernel

def row13279 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13279 : row13279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13279 := by decide +kernel

theorem rowEval13279 (x : Key → ℝ) : Integer.Sparse.eval row13279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13279, Integer.Sparse.eval_collectBalanced, rawRowCheck13279]

def rawRow13280 : Integer.Sparse Key := [(key1164, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key1245, -2), (key1228, -2), (key1228, -2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1085, -2), (key1085, -2), (key971, -2), (key1228, 6), (key1093, -2), (key1093, -2), (key979, -2)]

theorem rawRowCheck13280 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13280 := by decide +kernel

def row13280 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13280 : row13280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13280 := by decide +kernel

theorem rowEval13280 (x : Key → ℝ) : Integer.Sparse.eval row13280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13280, Integer.Sparse.eval_collectBalanced, rawRowCheck13280]

def rawRow13281 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1228, -2), (key1245, 6), (key979, -2), (key979, -2), (key979, -2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1164, -2), (key1164, -2), (key1164, -2), (key971, 6), (key1085, -2), (key1085, -2), (key1085, -2)]

theorem rawRowCheck13281 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1 = rawRow13281 := by decide +kernel

def row13281 : Integer.Sparse Key := [(key971, 6), (key979, -6), (key1085, -6), (key1093, 12), (key1164, -6), (key1228, -6), (key1245, 6)]

theorem rowCheck13281 : row13281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13281 := by decide +kernel

theorem rowEval13281 (x : Key → ℝ) : Integer.Sparse.eval row13281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13281, Integer.Sparse.eval_collectBalanced, rawRowCheck13281]

def rawRow13282 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1245, -2), (key1228, 6), (key1093, -2), (key1093, -2), (key1164, -2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key979, -2), (key1093, -2), (key1093, -2), (key1085, 6), (key971, -2), (key1085, -2), (key1085, -2)]

theorem rawRowCheck13282 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1 = rawRow13282 := by decide +kernel

def row13282 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13282 : row13282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13282 := by decide +kernel

theorem rowEval13282 (x : Key → ℝ) : Integer.Sparse.eval row13282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13282, Integer.Sparse.eval_collectBalanced, rawRowCheck13282]

def rawRow13283 : Integer.Sparse Key := [(key1228, -2), (key1245, -2), (key1228, -2), (key1228, 6), (key1093, -2), (key1164, -2), (key1093, -2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, -2), (key979, -2), (key1093, -2), (key1085, 6), (key1085, -2), (key971, -2), (key1085, -2)]

theorem rawRowCheck13283 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1 = rawRow13283 := by decide +kernel

def row13283 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13283 : row13283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13283 := by decide +kernel

theorem rowEval13283 (x : Key → ℝ) : Integer.Sparse.eval row13283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck13283, Integer.Sparse.eval_collectBalanced, rawRowCheck13283]

def rawRow13284 : Integer.Sparse Key := [(key1245, -2), (key1228, -2), (key1228, -2), (key1228, 6), (key1164, -2), (key1093, -2), (key1093, -2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, -2), (key1093, -2), (key979, -2), (key1085, 6), (key1085, -2), (key1085, -2), (key971, -2)]

theorem rawRowCheck13284 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1 = rawRow13284 := by decide +kernel

def row13284 : Integer.Sparse Key := [(key971, -2), (key979, 2), (key1085, 2), (key1093, -4), (key1164, 2), (key1228, 2), (key1245, -2)]

theorem rowCheck13284 : row13284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13284 := by decide +kernel

theorem rowEval13284 (x : Key → ℝ) : Integer.Sparse.eval row13284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form1) x := by
  rw [rowCheck13284, Integer.Sparse.eval_collectBalanced, rawRowCheck13284]

def rawRow13285 : Integer.Sparse Key := [(key2353, -2), (key2359, -2), (key2359, -2), (key2359, 6), (key2448, -2), (key2454, -2), (key2454, -2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2454, -2), (key2454, -2), (key2515, -2), (key2566, 6), (key2566, -2), (key2566, -2), (key2578, -2)]

theorem rawRowCheck13285 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form2 = rawRow13285 := by decide +kernel

def row13285 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck13285 : row13285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13285 := by decide +kernel

theorem rowEval13285 (x : Key → ℝ) : Integer.Sparse.eval row13285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13285, Integer.Sparse.eval_collectBalanced, rawRowCheck13285]

def rawRow13286 : Integer.Sparse Key := [(key2359, -2), (key2353, -2), (key2359, -2), (key2359, 6), (key2454, -2), (key2448, -2), (key2454, -2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2454, -2), (key2515, -2), (key2454, -2), (key2566, 6), (key2566, -2), (key2578, -2), (key2566, -2)]

theorem rawRowCheck13286 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form2 = rawRow13286 := by decide +kernel

def row13286 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck13286 : row13286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13286 := by decide +kernel

theorem rowEval13286 (x : Key → ℝ) : Integer.Sparse.eval row13286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13286, Integer.Sparse.eval_collectBalanced, rawRowCheck13286]

def rawRow13287 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2353, -2), (key2359, 6), (key2454, -2), (key2454, -2), (key2448, -2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2515, -2), (key2454, -2), (key2454, -2), (key2566, 6), (key2578, -2), (key2566, -2), (key2566, -2)]

theorem rawRowCheck13287 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form2 = rawRow13287 := by decide +kernel

def row13287 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck13287 : row13287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13287 := by decide +kernel

theorem rowEval13287 (x : Key → ℝ) : Integer.Sparse.eval row13287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13287, Integer.Sparse.eval_collectBalanced, rawRowCheck13287]

def rawRow13288 : Integer.Sparse Key := [(key2359, -2), (key2359, -2), (key2359, -2), (key2353, 6), (key2515, -2), (key2515, -2), (key2515, -2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2578, 6), (key2566, -2), (key2566, -2), (key2566, -2)]

theorem rawRowCheck13288 : GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13288 := by decide +kernel

def row13288 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2454, 12), (key2515, -6), (key2566, -6), (key2578, 6)]

theorem rowCheck13288 : row13288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13288 := by decide +kernel

theorem rowEval13288 (x : Key → ℝ) : Integer.Sparse.eval row13288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 2, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13288, Integer.Sparse.eval_collectBalanced, rawRowCheck13288]

def rawRow13289 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2454, -2), (key2515, 6), (key2353, -2), (key2359, -2), (key2359, -2), (key2448, 2), (key2454, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, 6), (key2454, -2), (key2454, -2), (key2515, -2)]

theorem rawRowCheck13289 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form2 = rawRow13289 := by decide +kernel

def row13289 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck13289 : row13289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13289 := by decide +kernel

theorem rowEval13289 (x : Key → ℝ) : Integer.Sparse.eval row13289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13289, Integer.Sparse.eval_collectBalanced, rawRowCheck13289]

def rawRow13290 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2454, -2), (key2515, 6), (key2359, -2), (key2353, -2), (key2359, -2), (key2454, 2), (key2448, 2), (key2515, 2), (key2448, 2), (key2515, 2), (key2454, 2), (key2566, -2), (key2578, -2), (key2566, -2), (key2359, 6), (key2454, -2), (key2515, -2), (key2454, -2)]

theorem rawRowCheck13290 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form2 = rawRow13290 := by decide +kernel

def row13290 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck13290 : row13290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13290 := by decide +kernel

theorem rowEval13290 (x : Key → ℝ) : Integer.Sparse.eval row13290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13290, Integer.Sparse.eval_collectBalanced, rawRowCheck13290]

def rawRow13291 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2448, -2), (key2515, 6), (key2359, -2), (key2359, -2), (key2353, -2), (key2515, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2448, 2), (key2448, 2), (key2578, -2), (key2566, -2), (key2566, -2), (key2359, 6), (key2515, -2), (key2454, -2), (key2454, -2)]

theorem rawRowCheck13291 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form2 = rawRow13291 := by decide +kernel

def row13291 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck13291 : row13291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13291 := by decide +kernel

theorem rowEval13291 (x : Key → ℝ) : Integer.Sparse.eval row13291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 2, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13291, Integer.Sparse.eval_collectBalanced, rawRowCheck13291]

def rawRow13292 : Integer.Sparse Key := [(key2448, -2), (key2454, -2), (key2515, -2), (key2454, 6), (key2448, -2), (key2454, -2), (key2515, -2), (key2353, 2), (key2359, 2), (key2448, 2), (key2515, 2), (key2566, 2), (key2578, 2), (key2359, -2), (key2454, -2), (key2515, -2), (key2454, 6), (key2359, -2), (key2454, -2), (key2515, -2)]

theorem rawRowCheck13292 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form2 = rawRow13292 := by decide +kernel

def row13292 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

theorem rowCheck13292 : row13292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13292 := by decide +kernel

theorem rowEval13292 (x : Key → ℝ) : Integer.Sparse.eval row13292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 0, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13292, Integer.Sparse.eval_collectBalanced, rawRowCheck13292]

def rawRow13293 : Integer.Sparse Key := [(key2454, -2), (key2448, -2), (key2515, -2), (key2454, 6), (key2454, -2), (key2448, -2), (key2515, -2), (key2359, 2), (key2353, 2), (key2515, 2), (key2448, 2), (key2578, 2), (key2566, 2), (key2359, -2), (key2515, -2), (key2454, -2), (key2454, 6), (key2359, -2), (key2515, -2), (key2454, -2)]

theorem rawRowCheck13293 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form2 = rawRow13293 := by decide +kernel

def row13293 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

theorem rowCheck13293 : row13293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13293 := by decide +kernel

theorem rowEval13293 (x : Key → ℝ) : Integer.Sparse.eval row13293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -3, 2, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13293, Integer.Sparse.eval_collectBalanced, rawRowCheck13293]

def rawRow13294 : Integer.Sparse Key := [(key2448, -2), (key2515, -2), (key2454, -2), (key2454, 6), (key2448, -2), (key2515, -2), (key2454, -2), (key2448, 2), (key2515, 2), (key2353, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2454, -2), (key2359, -2), (key2515, -2), (key2454, 6), (key2454, -2), (key2359, -2), (key2515, -2)]

theorem rawRowCheck13294 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form2 = rawRow13294 := by decide +kernel

def row13294 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -4), (key2578, 2)]

theorem rowCheck13294 : row13294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13294 := by decide +kernel

theorem rowEval13294 (x : Key → ℝ) : Integer.Sparse.eval row13294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, -3, 2] GramFunctions.Block4.form2) x := by
  rw [rowCheck13294, Integer.Sparse.eval_collectBalanced, rawRowCheck13294]

def rawRow13295 : Integer.Sparse Key := [(key2515, -2), (key2448, -2), (key2454, -2), (key2454, 6), (key2515, -2), (key2448, -2), (key2454, -2), (key2515, 2), (key2448, 2), (key2578, 2), (key2353, 2), (key2515, 2), (key2359, 2), (key2454, -2), (key2515, -2), (key2359, -2), (key2454, 6), (key2454, -2), (key2515, -2), (key2359, -2)]

theorem rawRowCheck13295 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form2 = rawRow13295 := by decide +kernel

def row13295 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -4), (key2578, 2)]

theorem rowCheck13295 : row13295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13295 := by decide +kernel

theorem rowEval13295 (x : Key → ℝ) : Integer.Sparse.eval row13295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 0, 2, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13295, Integer.Sparse.eval_collectBalanced, rawRowCheck13295]

def rawRow13296 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2448, -2), (key2454, 6), (key2454, -2), (key2515, -2), (key2448, -2), (key2566, 2), (key2578, 2), (key2359, 2), (key2515, 2), (key2353, 2), (key2448, 2), (key2515, -2), (key2359, -2), (key2454, -2), (key2454, 6), (key2515, -2), (key2359, -2), (key2454, -2)]

theorem rawRowCheck13296 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form2 = rawRow13296 := by decide +kernel

def row13296 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

theorem rowCheck13296 : row13296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13296 := by decide +kernel

theorem rowEval13296 (x : Key → ℝ) : Integer.Sparse.eval row13296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13296, Integer.Sparse.eval_collectBalanced, rawRowCheck13296]

def rawRow13297 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2448, -2), (key2454, 6), (key2515, -2), (key2454, -2), (key2448, -2), (key2578, 2), (key2566, 2), (key2515, 2), (key2359, 2), (key2448, 2), (key2353, 2), (key2515, -2), (key2454, -2), (key2359, -2), (key2454, 6), (key2515, -2), (key2454, -2), (key2359, -2)]

theorem rawRowCheck13297 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form2 = rawRow13297 := by decide +kernel

def row13297 : Integer.Sparse Key := [(key2353, 2), (key2359, -2), (key2448, -2), (key2454, 4), (key2515, -6), (key2566, 2), (key2578, 2)]

theorem rowCheck13297 : row13297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13297 := by decide +kernel

theorem rowEval13297 (x : Key → ℝ) : Integer.Sparse.eval row13297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13297, Integer.Sparse.eval_collectBalanced, rawRowCheck13297]

def rawRow13298 : Integer.Sparse Key := [(key2454, -2), (key2454, -2), (key2515, -2), (key2448, 6), (key2566, -2), (key2566, -2), (key2578, -2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2515, 6), (key2359, -2), (key2454, -2), (key2454, -2)]

theorem rawRowCheck13298 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13298 := by decide +kernel

def row13298 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck13298 : row13298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13298 := by decide +kernel

theorem rowEval13298 (x : Key → ℝ) : Integer.Sparse.eval row13298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13298, Integer.Sparse.eval_collectBalanced, rawRowCheck13298]

def rawRow13299 : Integer.Sparse Key := [(key2454, -2), (key2515, -2), (key2454, -2), (key2448, 6), (key2566, -2), (key2578, -2), (key2566, -2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2515, 6), (key2454, -2), (key2359, -2), (key2454, -2)]

theorem rawRowCheck13299 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13299 := by decide +kernel

def row13299 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck13299 : row13299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13299 := by decide +kernel

theorem rowEval13299 (x : Key → ℝ) : Integer.Sparse.eval row13299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13299, Integer.Sparse.eval_collectBalanced, rawRowCheck13299]

def rawRow13300 : Integer.Sparse Key := [(key2515, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2578, -2), (key2566, -2), (key2566, -2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2515, 6), (key2454, -2), (key2454, -2), (key2359, -2)]

theorem rawRowCheck13300 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13300 := by decide +kernel

def row13300 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 8), (key2566, -4), (key2578, -2)]

theorem rowCheck13300 : row13300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13300 := by decide +kernel

theorem rowEval13300 (x : Key → ℝ) : Integer.Sparse.eval row13300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13300, Integer.Sparse.eval_collectBalanced, rawRowCheck13300]

def rawRow13301 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2566, -2), (key2578, 6), (key2359, -2), (key2359, -2), (key2359, -2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2515, -2), (key2515, -2), (key2515, -2), (key2353, 6), (key2448, -2), (key2448, -2), (key2448, -2)]

theorem rawRowCheck13301 : GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form2 = rawRow13301 := by decide +kernel

def row13301 : Integer.Sparse Key := [(key2353, 6), (key2359, -6), (key2448, -6), (key2454, 12), (key2515, -6), (key2566, -6), (key2578, 6)]

theorem rowCheck13301 : row13301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13301 := by decide +kernel

theorem rowEval13301 (x : Key → ℝ) : Integer.Sparse.eval row13301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -3, 0, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13301, Integer.Sparse.eval_collectBalanced, rawRowCheck13301]

def rawRow13302 : Integer.Sparse Key := [(key2566, -2), (key2566, -2), (key2578, -2), (key2566, 6), (key2454, -2), (key2454, -2), (key2515, -2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2359, -2), (key2454, -2), (key2454, -2), (key2448, 6), (key2353, -2), (key2448, -2), (key2448, -2)]

theorem rawRowCheck13302 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form2 = rawRow13302 := by decide +kernel

def row13302 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck13302 : row13302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13302 := by decide +kernel

theorem rowEval13302 (x : Key → ℝ) : Integer.Sparse.eval row13302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -3, 0, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13302, Integer.Sparse.eval_collectBalanced, rawRowCheck13302]

def rawRow13303 : Integer.Sparse Key := [(key2566, -2), (key2578, -2), (key2566, -2), (key2566, 6), (key2454, -2), (key2515, -2), (key2454, -2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, -2), (key2359, -2), (key2454, -2), (key2448, 6), (key2448, -2), (key2353, -2), (key2448, -2)]

theorem rawRowCheck13303 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form2 = rawRow13303 := by decide +kernel

def row13303 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck13303 : row13303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13303 := by decide +kernel

theorem rowEval13303 (x : Key → ℝ) : Integer.Sparse.eval row13303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -3, 0] GramFunctions.Block4.form2) x := by
  rw [rowCheck13303, Integer.Sparse.eval_collectBalanced, rawRowCheck13303]

def rawRow13304 : Integer.Sparse Key := [(key2578, -2), (key2566, -2), (key2566, -2), (key2566, 6), (key2515, -2), (key2454, -2), (key2454, -2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2454, -2), (key2454, -2), (key2359, -2), (key2448, 6), (key2448, -2), (key2448, -2), (key2353, -2)]

theorem rawRowCheck13304 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form2 = rawRow13304 := by decide +kernel

def row13304 : Integer.Sparse Key := [(key2353, -2), (key2359, 2), (key2448, 2), (key2454, -4), (key2515, 2), (key2566, 2), (key2578, -2)]

theorem rowCheck13304 : row13304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13304 := by decide +kernel

theorem rowEval13304 (x : Key → ℝ) : Integer.Sparse.eval row13304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block4.form2) x := by
  rw [rowCheck13304, Integer.Sparse.eval_collectBalanced, rawRowCheck13304]

def rawRow13305 : Integer.Sparse Key := [(key2471, 4), (key2471, 4), (key2471, 4), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2518, 4), (key2518, 4), (key2518, 4)]

theorem rawRowCheck13305 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13305 := by decide +kernel

def row13305 : Integer.Sparse Key := [(key2471, 12), (key2479, -12), (key2502, -12), (key2518, 12)]

theorem rowCheck13305 : row13305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13305 := by decide +kernel

theorem rowEval13305 (x : Key → ℝ) : Integer.Sparse.eval row13305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13305, Integer.Sparse.eval_collectBalanced, rawRowCheck13305]

def rawRow13306 : Integer.Sparse Key := [(key2405, 4), (key2479, 4), (key2479, 4), (key2405, -2), (key2405, -2), (key2471, -2), (key2471, -2), (key2479, -2), (key2479, -2), (key2436, -2), (key2436, -2), (key2502, -2), (key2502, -2), (key2518, -2), (key2518, -2), (key2436, 4), (key2502, 4), (key2502, 4)]

theorem rawRowCheck13306 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form0 = rawRow13306 := by decide +kernel

def row13306 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13306 : row13306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13306 := by decide +kernel

theorem rowEval13306 (x : Key → ℝ) : Integer.Sparse.eval row13306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13306, Integer.Sparse.eval_collectBalanced, rawRowCheck13306]

def rawRow13307 : Integer.Sparse Key := [(key2479, 4), (key2405, 4), (key2479, 4), (key2471, -2), (key2479, -2), (key2405, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2502, 4), (key2436, 4), (key2502, 4)]

theorem rawRowCheck13307 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form0 = rawRow13307 := by decide +kernel

def row13307 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13307 : row13307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13307 := by decide +kernel

theorem rowEval13307 (x : Key → ℝ) : Integer.Sparse.eval row13307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13307, Integer.Sparse.eval_collectBalanced, rawRowCheck13307]

def rawRow13308 : Integer.Sparse Key := [(key2479, 4), (key2479, 4), (key2405, 4), (key2479, -2), (key2471, -2), (key2479, -2), (key2405, -2), (key2471, -2), (key2405, -2), (key2518, -2), (key2502, -2), (key2518, -2), (key2436, -2), (key2502, -2), (key2436, -2), (key2502, 4), (key2502, 4), (key2436, 4)]

theorem rawRowCheck13308 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form0 = rawRow13308 := by decide +kernel

def row13308 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13308 : row13308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13308 := by decide +kernel

theorem rowEval13308 (x : Key → ℝ) : Integer.Sparse.eval row13308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck13308, Integer.Sparse.eval_collectBalanced, rawRowCheck13308]

def rawRow13309 : Integer.Sparse Key := [(key2471, 4), (key2471, 4), (key2471, 4), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2502, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2479, -2), (key2518, 4), (key2518, 4), (key2518, 4)]

theorem rawRowCheck13309 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form0 = rawRow13309 := by decide +kernel

def row13309 : Integer.Sparse Key := [(key2471, 12), (key2479, -12), (key2502, -12), (key2518, 12)]

theorem rowCheck13309 : row13309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13309 := by decide +kernel

theorem rowEval13309 (x : Key → ℝ) : Integer.Sparse.eval row13309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13309, Integer.Sparse.eval_collectBalanced, rawRowCheck13309]

def rawRow13310 : Integer.Sparse Key := [(key2377, 4), (key2502, 4), (key2502, 4), (key2377, -2), (key2377, -2), (key2471, -2), (key2471, -2), (key2502, -2), (key2502, -2), (key2389, -2), (key2389, -2), (key2479, -2), (key2479, -2), (key2518, -2), (key2518, -2), (key2389, 4), (key2479, 4), (key2479, 4)]

theorem rawRowCheck13310 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form0 = rawRow13310 := by decide +kernel

def row13310 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13310 : row13310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13310 := by decide +kernel

theorem rowEval13310 (x : Key → ℝ) : Integer.Sparse.eval row13310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13310, Integer.Sparse.eval_collectBalanced, rawRowCheck13310]

def rawRow13311 : Integer.Sparse Key := [(key2502, 4), (key2377, 4), (key2502, 4), (key2471, -2), (key2502, -2), (key2377, -2), (key2502, -2), (key2377, -2), (key2471, -2), (key2479, -2), (key2518, -2), (key2389, -2), (key2518, -2), (key2389, -2), (key2479, -2), (key2479, 4), (key2389, 4), (key2479, 4)]

theorem rawRowCheck13311 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form0 = rawRow13311 := by decide +kernel

def row13311 : Integer.Sparse Key := [(key2471, -4), (key2479, 4), (key2502, 4), (key2518, -4)]

theorem rowCheck13311 : row13311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13311 := by decide +kernel

theorem rowEval13311 (x : Key → ℝ) : Integer.Sparse.eval row13311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck13311, Integer.Sparse.eval_collectBalanced, rawRowCheck13311]

end MUB6.Certificate.GramRows

end OAI
