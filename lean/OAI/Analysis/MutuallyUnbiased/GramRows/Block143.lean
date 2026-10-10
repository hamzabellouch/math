import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15232 : Integer.Sparse Key := [(key2610, 6), (key2626, -2), (key2635, -2), (key2626, -2), (key2665, 6), (key2700, -2), (key2721, -2), (key2700, -2), (key2780, -2), (key2789, -2), (key2780, -2), (key2803, -2), (key2824, -2), (key2803, -2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck15232 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form3 = rawRow15232 := by decide +kernel

def row15232 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck15232 : row15232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15232 := by decide +kernel

theorem rowEval15232 (x : Key → ℝ) : Integer.Sparse.eval row15232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15232, Integer.Sparse.eval_collectBalanced, rawRowCheck15232]

def rawRow15233 : Integer.Sparse Key := [(key2610, 6), (key2635, -2), (key2626, -2), (key2626, -2), (key2665, 6), (key2721, -2), (key2700, -2), (key2700, -2), (key2789, -2), (key2780, -2), (key2780, -2), (key2824, -2), (key2803, -2), (key2803, -2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck15233 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form3 = rawRow15233 := by decide +kernel

def row15233 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck15233 : row15233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15233 := by decide +kernel

theorem rowEval15233 (x : Key → ℝ) : Integer.Sparse.eval row15233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15233, Integer.Sparse.eval_collectBalanced, rawRowCheck15233]

def rawRow15234 : Integer.Sparse Key := [(key2626, 6), (key2610, -2), (key2626, -2), (key2635, -2), (key2700, 6), (key2665, -2), (key2700, -2), (key2721, -2), (key2803, -2), (key2853, -2), (key2855, -2), (key2780, -2), (key2853, -2), (key2865, -2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck15234 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form3 = rawRow15234 := by decide +kernel

def row15234 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15234 : row15234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15234 := by decide +kernel

theorem rowEval15234 (x : Key → ℝ) : Integer.Sparse.eval row15234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck15234, Integer.Sparse.eval_collectBalanced, rawRowCheck15234]

def rawRow15235 : Integer.Sparse Key := [(key2626, 6), (key2610, -2), (key2635, -2), (key2626, -2), (key2700, 6), (key2665, -2), (key2721, -2), (key2700, -2), (key2803, -2), (key2855, -2), (key2853, -2), (key2780, -2), (key2865, -2), (key2853, -2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck15235 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form3 = rawRow15235 := by decide +kernel

def row15235 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15235 : row15235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15235 := by decide +kernel

theorem rowEval15235 (x : Key → ℝ) : Integer.Sparse.eval row15235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15235, Integer.Sparse.eval_collectBalanced, rawRowCheck15235]

def rawRow15236 : Integer.Sparse Key := [(key2626, 6), (key2626, -2), (key2610, -2), (key2635, -2), (key2700, 6), (key2700, -2), (key2665, -2), (key2721, -2), (key2853, -2), (key2803, -2), (key2855, -2), (key2853, -2), (key2780, -2), (key2865, -2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

theorem rawRowCheck15236 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form3 = rawRow15236 := by decide +kernel

def row15236 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15236 : row15236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15236 := by decide +kernel

theorem rowEval15236 (x : Key → ℝ) : Integer.Sparse.eval row15236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck15236, Integer.Sparse.eval_collectBalanced, rawRowCheck15236]

def rawRow15237 : Integer.Sparse Key := [(key2626, 6), (key2626, -2), (key2635, -2), (key2610, -2), (key2700, 6), (key2700, -2), (key2721, -2), (key2665, -2), (key2853, -2), (key2855, -2), (key2803, -2), (key2853, -2), (key2865, -2), (key2780, -2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

theorem rawRowCheck15237 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form3 = rawRow15237 := by decide +kernel

def row15237 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15237 : row15237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15237 := by decide +kernel

theorem rowEval15237 (x : Key → ℝ) : Integer.Sparse.eval row15237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15237, Integer.Sparse.eval_collectBalanced, rawRowCheck15237]

def rawRow15238 : Integer.Sparse Key := [(key2626, 6), (key2635, -2), (key2610, -2), (key2626, -2), (key2700, 6), (key2721, -2), (key2665, -2), (key2700, -2), (key2855, -2), (key2803, -2), (key2853, -2), (key2865, -2), (key2780, -2), (key2853, -2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck15238 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form3 = rawRow15238 := by decide +kernel

def row15238 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15238 : row15238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15238 := by decide +kernel

theorem rowEval15238 (x : Key → ℝ) : Integer.Sparse.eval row15238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15238, Integer.Sparse.eval_collectBalanced, rawRowCheck15238]

def rawRow15239 : Integer.Sparse Key := [(key2626, 6), (key2635, -2), (key2626, -2), (key2610, -2), (key2700, 6), (key2721, -2), (key2700, -2), (key2665, -2), (key2855, -2), (key2853, -2), (key2803, -2), (key2865, -2), (key2853, -2), (key2780, -2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck15239 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form3 = rawRow15239 := by decide +kernel

def row15239 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15239 : row15239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15239 := by decide +kernel

theorem rowEval15239 (x : Key → ℝ) : Integer.Sparse.eval row15239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15239, Integer.Sparse.eval_collectBalanced, rawRowCheck15239]

def rawRow15240 : Integer.Sparse Key := [(key2665, 6), (key2780, -2), (key2780, -2), (key2789, -2), (key2610, 6), (key2803, -2), (key2803, -2), (key2824, -2), (key2626, -2), (key2626, -2), (key2635, -2), (key2700, -2), (key2700, -2), (key2721, -2), (key2853, 2), (key2855, 2), (key2853, 2), (key2865, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck15240 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form3 = rawRow15240 := by decide +kernel

def row15240 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck15240 : row15240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15240 := by decide +kernel

theorem rowEval15240 (x : Key → ℝ) : Integer.Sparse.eval row15240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck15240, Integer.Sparse.eval_collectBalanced, rawRowCheck15240]

def rawRow15241 : Integer.Sparse Key := [(key2665, 6), (key2780, -2), (key2789, -2), (key2780, -2), (key2610, 6), (key2803, -2), (key2824, -2), (key2803, -2), (key2626, -2), (key2635, -2), (key2626, -2), (key2700, -2), (key2721, -2), (key2700, -2), (key2855, 2), (key2853, 2), (key2865, 2), (key2853, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck15241 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form3 = rawRow15241 := by decide +kernel

def row15241 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck15241 : row15241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15241 := by decide +kernel

theorem rowEval15241 (x : Key → ℝ) : Integer.Sparse.eval row15241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15241, Integer.Sparse.eval_collectBalanced, rawRowCheck15241]

def rawRow15242 : Integer.Sparse Key := [(key2665, 6), (key2789, -2), (key2780, -2), (key2780, -2), (key2610, 6), (key2824, -2), (key2803, -2), (key2803, -2), (key2635, -2), (key2626, -2), (key2626, -2), (key2721, -2), (key2700, -2), (key2700, -2), (key2865, 2), (key2865, 2), (key2855, 2), (key2855, 2), (key2853, 2), (key2853, 2)]

theorem rawRowCheck15242 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form3 = rawRow15242 := by decide +kernel

def row15242 : Integer.Sparse Key := [(key2610, 6), (key2626, -4), (key2635, -2), (key2665, 6), (key2700, -4), (key2721, -2), (key2780, -4), (key2789, -2), (key2803, -4), (key2824, -2), (key2853, 4), (key2855, 4), (key2865, 4)]

theorem rowCheck15242 : row15242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15242 := by decide +kernel

theorem rowEval15242 (x : Key → ℝ) : Integer.Sparse.eval row15242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15242, Integer.Sparse.eval_collectBalanced, rawRowCheck15242]

def rawRow15243 : Integer.Sparse Key := [(key2700, 6), (key2803, -2), (key2853, -2), (key2855, -2), (key2626, 6), (key2780, -2), (key2853, -2), (key2865, -2), (key2610, -2), (key2626, -2), (key2635, -2), (key2665, -2), (key2700, -2), (key2721, -2), (key2780, 2), (key2789, 2), (key2803, 2), (key2824, 2), (key2855, 2), (key2865, 2)]

theorem rawRowCheck15243 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form3 = rawRow15243 := by decide +kernel

def row15243 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15243 : row15243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15243 := by decide +kernel

theorem rowEval15243 (x : Key → ℝ) : Integer.Sparse.eval row15243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck15243, Integer.Sparse.eval_collectBalanced, rawRowCheck15243]

def rawRow15244 : Integer.Sparse Key := [(key2700, 6), (key2803, -2), (key2855, -2), (key2853, -2), (key2626, 6), (key2780, -2), (key2865, -2), (key2853, -2), (key2610, -2), (key2635, -2), (key2626, -2), (key2665, -2), (key2721, -2), (key2700, -2), (key2789, 2), (key2780, 2), (key2824, 2), (key2803, 2), (key2865, 2), (key2855, 2)]

theorem rawRowCheck15244 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form3 = rawRow15244 := by decide +kernel

def row15244 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15244 : row15244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15244 := by decide +kernel

theorem rowEval15244 (x : Key → ℝ) : Integer.Sparse.eval row15244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15244, Integer.Sparse.eval_collectBalanced, rawRowCheck15244]

def rawRow15245 : Integer.Sparse Key := [(key2700, 6), (key2853, -2), (key2803, -2), (key2855, -2), (key2626, 6), (key2853, -2), (key2780, -2), (key2865, -2), (key2626, -2), (key2610, -2), (key2635, -2), (key2700, -2), (key2665, -2), (key2721, -2), (key2803, 2), (key2855, 2), (key2780, 2), (key2865, 2), (key2789, 2), (key2824, 2)]

theorem rawRowCheck15245 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form3 = rawRow15245 := by decide +kernel

def row15245 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15245 : row15245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15245 := by decide +kernel

theorem rowEval15245 (x : Key → ℝ) : Integer.Sparse.eval row15245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form3) x := by
  rw [rowCheck15245, Integer.Sparse.eval_collectBalanced, rawRowCheck15245]

def rawRow15246 : Integer.Sparse Key := [(key2700, 6), (key2853, -2), (key2855, -2), (key2803, -2), (key2626, 6), (key2853, -2), (key2865, -2), (key2780, -2), (key2626, -2), (key2635, -2), (key2610, -2), (key2700, -2), (key2721, -2), (key2665, -2), (key2855, 2), (key2803, 2), (key2865, 2), (key2780, 2), (key2824, 2), (key2789, 2)]

theorem rawRowCheck15246 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form3 = rawRow15246 := by decide +kernel

def row15246 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15246 : row15246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15246 := by decide +kernel

theorem rowEval15246 (x : Key → ℝ) : Integer.Sparse.eval row15246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15246, Integer.Sparse.eval_collectBalanced, rawRowCheck15246]

def rawRow15247 : Integer.Sparse Key := [(key2700, 6), (key2855, -2), (key2803, -2), (key2853, -2), (key2626, 6), (key2865, -2), (key2780, -2), (key2853, -2), (key2635, -2), (key2610, -2), (key2626, -2), (key2721, -2), (key2665, -2), (key2700, -2), (key2824, 2), (key2865, 2), (key2789, 2), (key2855, 2), (key2780, 2), (key2803, 2)]

theorem rawRowCheck15247 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form3 = rawRow15247 := by decide +kernel

def row15247 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15247 : row15247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15247 := by decide +kernel

theorem rowEval15247 (x : Key → ℝ) : Integer.Sparse.eval row15247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck15247, Integer.Sparse.eval_collectBalanced, rawRowCheck15247]

def rawRow15248 : Integer.Sparse Key := [(key2700, 6), (key2855, -2), (key2853, -2), (key2803, -2), (key2626, 6), (key2865, -2), (key2853, -2), (key2780, -2), (key2635, -2), (key2626, -2), (key2610, -2), (key2721, -2), (key2700, -2), (key2665, -2), (key2865, 2), (key2824, 2), (key2855, 2), (key2789, 2), (key2803, 2), (key2780, 2)]

theorem rawRowCheck15248 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form3 = rawRow15248 := by decide +kernel

def row15248 : Integer.Sparse Key := [(key2610, -2), (key2626, 4), (key2635, -2), (key2665, -2), (key2700, 4), (key2721, -2), (key2789, 2), (key2824, 2), (key2853, -4)]

theorem rowCheck15248 : row15248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15248 := by decide +kernel

theorem rowEval15248 (x : Key → ℝ) : Integer.Sparse.eval row15248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck15248, Integer.Sparse.eval_collectBalanced, rawRowCheck15248]

def rawRow15249 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1000, -2), (key1014, 6), (key1029, -2), (key1035, -2), (key1035, -2), (key1107, 2), (key1113, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1231, 2), (key1122, -2), (key1122, -2), (key1234, -2), (key1070, 6), (key1149, -2), (key1149, -2), (key1241, -2)]

theorem rawRowCheck15249 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form4 = rawRow15249 := by decide +kernel

def row15249 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck15249 : row15249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15249 := by decide +kernel

theorem rowEval15249 (x : Key → ℝ) : Integer.Sparse.eval row15249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck15249, Integer.Sparse.eval_collectBalanced, rawRowCheck15249]

def rawRow15250 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1000, -2), (key1014, 6), (key1035, -2), (key1029, -2), (key1035, -2), (key1113, 2), (key1107, 2), (key1231, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1122, -2), (key1234, -2), (key1122, -2), (key1070, 6), (key1149, -2), (key1241, -2), (key1149, -2)]

theorem rawRowCheck15250 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form4 = rawRow15250 := by decide +kernel

def row15250 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck15250 : row15250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15250 := by decide +kernel

theorem rowEval15250 (x : Key → ℝ) : Integer.Sparse.eval row15250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15250, Integer.Sparse.eval_collectBalanced, rawRowCheck15250]

def rawRow15251 : Integer.Sparse Key := [(key1000, -2), (key1000, -2), (key994, -2), (key1014, 6), (key1035, -2), (key1035, -2), (key1029, -2), (key1231, 2), (key1231, 2), (key1113, 2), (key1113, 2), (key1107, 2), (key1107, 2), (key1234, -2), (key1122, -2), (key1122, -2), (key1070, 6), (key1241, -2), (key1149, -2), (key1149, -2)]

theorem rawRowCheck15251 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form4 = rawRow15251 := by decide +kernel

def row15251 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck15251 : row15251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15251 := by decide +kernel

theorem rowEval15251 (x : Key → ℝ) : Integer.Sparse.eval row15251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15251, Integer.Sparse.eval_collectBalanced, rawRowCheck15251]

def rawRow15252 : Integer.Sparse Key := [(key994, -2), (key1000, -2), (key1014, -2), (key1000, 6), (key1107, -2), (key1113, -2), (key1122, -2), (key1029, 2), (key1035, 2), (key1107, 2), (key1231, 2), (key1122, 2), (key1234, 2), (key1035, -2), (key1113, -2), (key1231, -2), (key1149, 6), (key1070, -2), (key1149, -2), (key1241, -2)]

theorem rawRowCheck15252 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form4 = rawRow15252 := by decide +kernel

def row15252 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15252 : row15252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15252 := by decide +kernel

theorem rowEval15252 (x : Key → ℝ) : Integer.Sparse.eval row15252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck15252, Integer.Sparse.eval_collectBalanced, rawRowCheck15252]

def rawRow15253 : Integer.Sparse Key := [(key1000, -2), (key994, -2), (key1014, -2), (key1000, 6), (key1113, -2), (key1107, -2), (key1122, -2), (key1035, 2), (key1029, 2), (key1231, 2), (key1107, 2), (key1234, 2), (key1122, 2), (key1035, -2), (key1231, -2), (key1113, -2), (key1149, 6), (key1070, -2), (key1241, -2), (key1149, -2)]

theorem rawRowCheck15253 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form4 = rawRow15253 := by decide +kernel

def row15253 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15253 : row15253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15253 := by decide +kernel

theorem rowEval15253 (x : Key → ℝ) : Integer.Sparse.eval row15253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15253, Integer.Sparse.eval_collectBalanced, rawRowCheck15253]

def rawRow15254 : Integer.Sparse Key := [(key994, -2), (key1014, -2), (key1000, -2), (key1000, 6), (key1107, -2), (key1122, -2), (key1113, -2), (key1107, 2), (key1122, 2), (key1029, 2), (key1234, 2), (key1035, 2), (key1231, 2), (key1113, -2), (key1035, -2), (key1231, -2), (key1149, 6), (key1149, -2), (key1070, -2), (key1241, -2)]

theorem rawRowCheck15254 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form4 = rawRow15254 := by decide +kernel

def row15254 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15254 : row15254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15254 := by decide +kernel

theorem rowEval15254 (x : Key → ℝ) : Integer.Sparse.eval row15254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck15254, Integer.Sparse.eval_collectBalanced, rawRowCheck15254]

def rawRow15255 : Integer.Sparse Key := [(key1014, -2), (key994, -2), (key1000, -2), (key1000, 6), (key1122, -2), (key1107, -2), (key1113, -2), (key1122, 2), (key1107, 2), (key1234, 2), (key1029, 2), (key1231, 2), (key1035, 2), (key1113, -2), (key1231, -2), (key1035, -2), (key1149, 6), (key1149, -2), (key1241, -2), (key1070, -2)]

theorem rawRowCheck15255 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form4 = rawRow15255 := by decide +kernel

def row15255 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15255 : row15255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15255 := by decide +kernel

theorem rowEval15255 (x : Key → ℝ) : Integer.Sparse.eval row15255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15255, Integer.Sparse.eval_collectBalanced, rawRowCheck15255]

def rawRow15256 : Integer.Sparse Key := [(key1000, -2), (key1014, -2), (key994, -2), (key1000, 6), (key1113, -2), (key1122, -2), (key1107, -2), (key1231, 2), (key1234, 2), (key1035, 2), (key1122, 2), (key1029, 2), (key1107, 2), (key1231, -2), (key1035, -2), (key1113, -2), (key1149, 6), (key1241, -2), (key1070, -2), (key1149, -2)]

theorem rawRowCheck15256 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form4 = rawRow15256 := by decide +kernel

def row15256 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15256 : row15256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15256 := by decide +kernel

theorem rowEval15256 (x : Key → ℝ) : Integer.Sparse.eval row15256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15256, Integer.Sparse.eval_collectBalanced, rawRowCheck15256]

def rawRow15257 : Integer.Sparse Key := [(key1014, -2), (key1000, -2), (key994, -2), (key1000, 6), (key1122, -2), (key1113, -2), (key1107, -2), (key1234, 2), (key1231, 2), (key1122, 2), (key1035, 2), (key1107, 2), (key1029, 2), (key1231, -2), (key1113, -2), (key1035, -2), (key1149, 6), (key1241, -2), (key1149, -2), (key1070, -2)]

theorem rawRowCheck15257 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form4 = rawRow15257 := by decide +kernel

def row15257 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15257 : row15257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15257 := by decide +kernel

theorem rowEval15257 (x : Key → ℝ) : Integer.Sparse.eval row15257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15257, Integer.Sparse.eval_collectBalanced, rawRowCheck15257]

def rawRow15258 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1035, -2), (key1070, 6), (key994, -2), (key1000, -2), (key1000, -2), (key1107, 2), (key1113, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1231, 2), (key1149, -2), (key1149, -2), (key1241, -2), (key1014, 6), (key1122, -2), (key1122, -2), (key1234, -2)]

theorem rawRowCheck15258 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form4 = rawRow15258 := by decide +kernel

def row15258 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck15258 : row15258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15258 := by decide +kernel

theorem rowEval15258 (x : Key → ℝ) : Integer.Sparse.eval row15258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck15258, Integer.Sparse.eval_collectBalanced, rawRowCheck15258]

def rawRow15259 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1035, -2), (key1070, 6), (key1000, -2), (key994, -2), (key1000, -2), (key1113, 2), (key1107, 2), (key1231, 2), (key1107, 2), (key1231, 2), (key1113, 2), (key1149, -2), (key1241, -2), (key1149, -2), (key1014, 6), (key1122, -2), (key1234, -2), (key1122, -2)]

theorem rawRowCheck15259 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form4 = rawRow15259 := by decide +kernel

def row15259 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck15259 : row15259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15259 := by decide +kernel

theorem rowEval15259 (x : Key → ℝ) : Integer.Sparse.eval row15259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15259, Integer.Sparse.eval_collectBalanced, rawRowCheck15259]

def rawRow15260 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1029, -2), (key1070, 6), (key1000, -2), (key1000, -2), (key994, -2), (key1231, 2), (key1231, 2), (key1113, 2), (key1113, 2), (key1107, 2), (key1107, 2), (key1241, -2), (key1149, -2), (key1149, -2), (key1014, 6), (key1234, -2), (key1122, -2), (key1122, -2)]

theorem rawRowCheck15260 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form4 = rawRow15260 := by decide +kernel

def row15260 : Integer.Sparse Key := [(key994, -2), (key1000, -4), (key1014, 6), (key1029, -2), (key1035, -4), (key1070, 6), (key1107, 4), (key1113, 4), (key1122, -4), (key1149, -4), (key1231, 4), (key1234, -2), (key1241, -2)]

theorem rowCheck15260 : row15260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15260 := by decide +kernel

theorem rowEval15260 (x : Key → ℝ) : Integer.Sparse.eval row15260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15260, Integer.Sparse.eval_collectBalanced, rawRowCheck15260]

def rawRow15261 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1122, -2), (key1149, 6), (key994, -2), (key1000, -2), (key1014, -2), (key1029, 2), (key1035, 2), (key1107, 2), (key1231, 2), (key1122, 2), (key1234, 2), (key1070, -2), (key1149, -2), (key1241, -2), (key1000, 6), (key1035, -2), (key1113, -2), (key1231, -2)]

theorem rawRowCheck15261 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form4 = rawRow15261 := by decide +kernel

def row15261 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15261 : row15261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15261 := by decide +kernel

theorem rowEval15261 (x : Key → ℝ) : Integer.Sparse.eval row15261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck15261, Integer.Sparse.eval_collectBalanced, rawRowCheck15261]

def rawRow15262 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1122, -2), (key1149, 6), (key1000, -2), (key994, -2), (key1014, -2), (key1035, 2), (key1029, 2), (key1231, 2), (key1107, 2), (key1234, 2), (key1122, 2), (key1070, -2), (key1241, -2), (key1149, -2), (key1000, 6), (key1035, -2), (key1231, -2), (key1113, -2)]

theorem rawRowCheck15262 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form4 = rawRow15262 := by decide +kernel

def row15262 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15262 : row15262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15262 := by decide +kernel

theorem rowEval15262 (x : Key → ℝ) : Integer.Sparse.eval row15262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15262, Integer.Sparse.eval_collectBalanced, rawRowCheck15262]

def rawRow15263 : Integer.Sparse Key := [(key1107, -2), (key1122, -2), (key1113, -2), (key1149, 6), (key994, -2), (key1014, -2), (key1000, -2), (key1107, 2), (key1122, 2), (key1029, 2), (key1234, 2), (key1035, 2), (key1231, 2), (key1149, -2), (key1070, -2), (key1241, -2), (key1000, 6), (key1113, -2), (key1035, -2), (key1231, -2)]

theorem rawRowCheck15263 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form4 = rawRow15263 := by decide +kernel

def row15263 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15263 : row15263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15263 := by decide +kernel

theorem rowEval15263 (x : Key → ℝ) : Integer.Sparse.eval row15263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form4) x := by
  rw [rowCheck15263, Integer.Sparse.eval_collectBalanced, rawRowCheck15263]

def rawRow15264 : Integer.Sparse Key := [(key1122, -2), (key1107, -2), (key1113, -2), (key1149, 6), (key1014, -2), (key994, -2), (key1000, -2), (key1122, 2), (key1107, 2), (key1234, 2), (key1029, 2), (key1231, 2), (key1035, 2), (key1149, -2), (key1241, -2), (key1070, -2), (key1000, 6), (key1113, -2), (key1231, -2), (key1035, -2)]

theorem rawRowCheck15264 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form4 = rawRow15264 := by decide +kernel

def row15264 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15264 : row15264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15264 := by decide +kernel

theorem rowEval15264 (x : Key → ℝ) : Integer.Sparse.eval row15264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15264, Integer.Sparse.eval_collectBalanced, rawRowCheck15264]

def rawRow15265 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1107, -2), (key1149, 6), (key1000, -2), (key1014, -2), (key994, -2), (key1231, 2), (key1234, 2), (key1035, 2), (key1122, 2), (key1029, 2), (key1107, 2), (key1241, -2), (key1070, -2), (key1149, -2), (key1000, 6), (key1231, -2), (key1035, -2), (key1113, -2)]

theorem rawRowCheck15265 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form4 = rawRow15265 := by decide +kernel

def row15265 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15265 : row15265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15265 := by decide +kernel

theorem rowEval15265 (x : Key → ℝ) : Integer.Sparse.eval row15265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form4) x := by
  rw [rowCheck15265, Integer.Sparse.eval_collectBalanced, rawRowCheck15265]

def rawRow15266 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1107, -2), (key1149, 6), (key1014, -2), (key1000, -2), (key994, -2), (key1234, 2), (key1231, 2), (key1122, 2), (key1035, 2), (key1107, 2), (key1029, 2), (key1241, -2), (key1149, -2), (key1070, -2), (key1000, 6), (key1231, -2), (key1113, -2), (key1035, -2)]

theorem rawRowCheck15266 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form4 = rawRow15266 := by decide +kernel

def row15266 : Integer.Sparse Key := [(key994, -2), (key1000, 4), (key1014, -2), (key1029, 2), (key1070, -2), (key1113, -4), (key1149, 4), (key1234, 2), (key1241, -2)]

theorem rowCheck15266 : row15266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15266 := by decide +kernel

theorem rowEval15266 (x : Key → ℝ) : Integer.Sparse.eval row15266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form4) x := by
  rw [rowCheck15266, Integer.Sparse.eval_collectBalanced, rawRowCheck15266]

def rawRow15267 : Integer.Sparse Key := [(key1116, 4), (key1116, 4), (key1233, 4), (key1125, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1152, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1174, 4), (key1174, 4), (key1247, 4)]

theorem rawRowCheck15267 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form5 = rawRow15267 := by decide +kernel

def row15267 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck15267 : row15267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15267 := by decide +kernel

theorem rowEval15267 (x : Key → ℝ) : Integer.Sparse.eval row15267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck15267, Integer.Sparse.eval_collectBalanced, rawRowCheck15267]

def rawRow15268 : Integer.Sparse Key := [(key1116, 4), (key1233, 4), (key1116, 4), (key1130, -2), (key1125, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1174, 4), (key1247, 4), (key1174, 4)]

theorem rawRowCheck15268 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form5 = rawRow15268 := by decide +kernel

def row15268 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck15268 : row15268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15268 := by decide +kernel

theorem rowEval15268 (x : Key → ℝ) : Integer.Sparse.eval row15268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15268, Integer.Sparse.eval_collectBalanced, rawRowCheck15268]

def rawRow15269 : Integer.Sparse Key := [(key1233, 4), (key1116, 4), (key1116, 4), (key1236, -2), (key1236, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1243, -2), (key1243, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1247, 4), (key1174, 4), (key1174, 4)]

theorem rawRowCheck15269 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form5 = rawRow15269 := by decide +kernel

def row15269 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck15269 : row15269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15269 := by decide +kernel

theorem rowEval15269 (x : Key → ℝ) : Integer.Sparse.eval row15269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15269, Integer.Sparse.eval_collectBalanced, rawRowCheck15269]

def rawRow15270 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1236, 4), (key1038, -2), (key1044, -2), (key1116, -2), (key1233, -2), (key1130, -2), (key1236, -2), (key1073, -2), (key1080, -2), (key1152, -2), (key1243, -2), (key1174, -2), (key1247, -2), (key1080, 4), (key1159, 4), (key1243, 4)]

theorem rawRowCheck15270 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form5 = rawRow15270 := by decide +kernel

def row15270 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15270 : row15270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15270 := by decide +kernel

theorem rowEval15270 (x : Key → ℝ) : Integer.Sparse.eval row15270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck15270, Integer.Sparse.eval_collectBalanced, rawRowCheck15270]

def rawRow15271 : Integer.Sparse Key := [(key1038, 4), (key1236, 4), (key1125, 4), (key1044, -2), (key1038, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1130, -2), (key1080, -2), (key1073, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1080, 4), (key1243, 4), (key1159, 4)]

theorem rawRowCheck15271 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form5 = rawRow15271 := by decide +kernel

def row15271 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15271 : row15271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15271 := by decide +kernel

theorem rowEval15271 (x : Key → ℝ) : Integer.Sparse.eval row15271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15271, Integer.Sparse.eval_collectBalanced, rawRowCheck15271]

def rawRow15272 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1236, 4), (key1116, -2), (key1130, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1152, -2), (key1174, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1159, 4), (key1080, 4), (key1243, 4)]

theorem rawRowCheck15272 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form5 = rawRow15272 := by decide +kernel

def row15272 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15272 : row15272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15272 := by decide +kernel

theorem rowEval15272 (x : Key → ℝ) : Integer.Sparse.eval row15272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck15272, Integer.Sparse.eval_collectBalanced, rawRowCheck15272]

def rawRow15273 : Integer.Sparse Key := [(key1125, 4), (key1236, 4), (key1038, 4), (key1130, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1233, -2), (key1044, -2), (key1174, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1243, -2), (key1080, -2), (key1159, 4), (key1243, 4), (key1080, 4)]

theorem rawRowCheck15273 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form5 = rawRow15273 := by decide +kernel

def row15273 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15273 : row15273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15273 := by decide +kernel

theorem rowEval15273 (x : Key → ℝ) : Integer.Sparse.eval row15273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15273, Integer.Sparse.eval_collectBalanced, rawRowCheck15273]

def rawRow15274 : Integer.Sparse Key := [(key1236, 4), (key1038, 4), (key1125, 4), (key1233, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1038, -2), (key1116, -2), (key1243, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1073, -2), (key1152, -2), (key1243, 4), (key1080, 4), (key1159, 4)]

theorem rawRowCheck15274 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form5 = rawRow15274 := by decide +kernel

def row15274 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15274 : row15274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15274 := by decide +kernel

theorem rowEval15274 (x : Key → ℝ) : Integer.Sparse.eval row15274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15274, Integer.Sparse.eval_collectBalanced, rawRowCheck15274]

def rawRow15275 : Integer.Sparse Key := [(key1236, 4), (key1125, 4), (key1038, 4), (key1236, -2), (key1233, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1247, -2), (key1243, -2), (key1174, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1243, 4), (key1159, 4), (key1080, 4)]

theorem rawRowCheck15275 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form5 = rawRow15275 := by decide +kernel

def row15275 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15275 : row15275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15275 := by decide +kernel

theorem rowEval15275 (x : Key → ℝ) : Integer.Sparse.eval row15275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15275, Integer.Sparse.eval_collectBalanced, rawRowCheck15275]

def rawRow15276 : Integer.Sparse Key := [(key1116, 4), (key1116, 4), (key1233, 4), (key1152, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1125, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1174, 4), (key1174, 4), (key1247, 4)]

theorem rawRowCheck15276 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form5 = rawRow15276 := by decide +kernel

def row15276 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck15276 : row15276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15276 := by decide +kernel

theorem rowEval15276 (x : Key → ℝ) : Integer.Sparse.eval row15276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck15276, Integer.Sparse.eval_collectBalanced, rawRowCheck15276]

def rawRow15277 : Integer.Sparse Key := [(key1116, 4), (key1233, 4), (key1116, 4), (key1159, -2), (key1152, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1174, 4), (key1247, 4), (key1174, 4)]

theorem rawRowCheck15277 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form5 = rawRow15277 := by decide +kernel

def row15277 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck15277 : row15277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15277 := by decide +kernel

theorem rowEval15277 (x : Key → ℝ) : Integer.Sparse.eval row15277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15277, Integer.Sparse.eval_collectBalanced, rawRowCheck15277]

def rawRow15278 : Integer.Sparse Key := [(key1233, 4), (key1116, 4), (key1116, 4), (key1243, -2), (key1243, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1236, -2), (key1236, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1247, 4), (key1174, 4), (key1174, 4)]

theorem rawRowCheck15278 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form5 = rawRow15278 := by decide +kernel

def row15278 : Integer.Sparse Key := [(key1116, 8), (key1125, -4), (key1130, -4), (key1152, -4), (key1159, -4), (key1174, 8), (key1233, 4), (key1236, -4), (key1243, -4), (key1247, 4)]

theorem rowCheck15278 : row15278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15278 := by decide +kernel

theorem rowEval15278 (x : Key → ℝ) : Integer.Sparse.eval row15278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15278, Integer.Sparse.eval_collectBalanced, rawRowCheck15278]

def rawRow15279 : Integer.Sparse Key := [(key1038, 4), (key1125, 4), (key1236, 4), (key1073, -2), (key1080, -2), (key1152, -2), (key1243, -2), (key1174, -2), (key1247, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1233, -2), (key1130, -2), (key1236, -2), (key1080, 4), (key1159, 4), (key1243, 4)]

theorem rawRowCheck15279 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form5 = rawRow15279 := by decide +kernel

def row15279 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15279 : row15279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15279 := by decide +kernel

theorem rowEval15279 (x : Key → ℝ) : Integer.Sparse.eval row15279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck15279, Integer.Sparse.eval_collectBalanced, rawRowCheck15279]

def rawRow15280 : Integer.Sparse Key := [(key1038, 4), (key1236, 4), (key1125, 4), (key1080, -2), (key1073, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1044, -2), (key1038, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1130, -2), (key1080, 4), (key1243, 4), (key1159, 4)]

theorem rawRowCheck15280 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form5 = rawRow15280 := by decide +kernel

def row15280 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15280 : row15280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15280 := by decide +kernel

theorem rowEval15280 (x : Key → ℝ) : Integer.Sparse.eval row15280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15280, Integer.Sparse.eval_collectBalanced, rawRowCheck15280]

def rawRow15281 : Integer.Sparse Key := [(key1125, 4), (key1038, 4), (key1236, 4), (key1152, -2), (key1174, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1116, -2), (key1130, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1159, 4), (key1080, 4), (key1243, 4)]

theorem rawRowCheck15281 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form5 = rawRow15281 := by decide +kernel

def row15281 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15281 : row15281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15281 := by decide +kernel

theorem rowEval15281 (x : Key → ℝ) : Integer.Sparse.eval row15281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form5) x := by
  rw [rowCheck15281, Integer.Sparse.eval_collectBalanced, rawRowCheck15281]

def rawRow15282 : Integer.Sparse Key := [(key1125, 4), (key1236, 4), (key1038, 4), (key1174, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1243, -2), (key1080, -2), (key1130, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1233, -2), (key1044, -2), (key1159, 4), (key1243, 4), (key1080, 4)]

theorem rawRowCheck15282 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form5 = rawRow15282 := by decide +kernel

def row15282 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15282 : row15282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15282 := by decide +kernel

theorem rowEval15282 (x : Key → ℝ) : Integer.Sparse.eval row15282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15282, Integer.Sparse.eval_collectBalanced, rawRowCheck15282]

def rawRow15283 : Integer.Sparse Key := [(key1236, 4), (key1038, 4), (key1125, 4), (key1243, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1073, -2), (key1152, -2), (key1233, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1038, -2), (key1116, -2), (key1243, 4), (key1080, 4), (key1159, 4)]

theorem rawRowCheck15283 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form5 = rawRow15283 := by decide +kernel

def row15283 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15283 : row15283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15283 := by decide +kernel

theorem rowEval15283 (x : Key → ℝ) : Integer.Sparse.eval row15283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck15283, Integer.Sparse.eval_collectBalanced, rawRowCheck15283]

def rawRow15284 : Integer.Sparse Key := [(key1236, 4), (key1125, 4), (key1038, 4), (key1247, -2), (key1243, -2), (key1174, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1236, -2), (key1233, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1243, 4), (key1159, 4), (key1080, 4)]

theorem rawRowCheck15284 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form5 = rawRow15284 := by decide +kernel

def row15284 : Integer.Sparse Key := [(key1038, 2), (key1044, -2), (key1073, -2), (key1080, 2), (key1116, -2), (key1125, 4), (key1130, -2), (key1152, -2), (key1159, 4), (key1174, -2), (key1233, -2), (key1236, 2), (key1243, 2), (key1247, -2)]

theorem rowCheck15284 : row15284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15284 := by decide +kernel

theorem rowEval15284 (x : Key → ℝ) : Integer.Sparse.eval row15284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form5) x := by
  rw [rowCheck15284, Integer.Sparse.eval_collectBalanced, rawRowCheck15284]

def rawRow15285 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key2922, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key3021, -1), (key3022, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key3025, -1)]

theorem rawRowCheck15285 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form6 = rawRow15285 := by decide +kernel

def row15285 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

theorem rowCheck15285 : row15285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15285 := by decide +kernel

theorem rowEval15285 (x : Key → ℝ) : Integer.Sparse.eval row15285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck15285, Integer.Sparse.eval_collectBalanced, rawRowCheck15285]

def rawRow15286 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key3022, -1), (key3021, -1), (key3025, -1), (key3021, -1), (key3025, -1), (key3022, -1)]

theorem rawRowCheck15286 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form6 = rawRow15286 := by decide +kernel

def row15286 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

theorem rowCheck15286 : row15286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15286 := by decide +kernel

theorem rowEval15286 (x : Key → ℝ) : Integer.Sparse.eval row15286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15286, Integer.Sparse.eval_collectBalanced, rawRowCheck15286]

def rawRow15287 : Integer.Sparse Key := [(key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, -1), (key2918, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key3025, -1), (key3025, -1), (key3022, -1), (key3022, -1), (key3021, -1), (key3021, -1)]

theorem rawRowCheck15287 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form6 = rawRow15287 := by decide +kernel

def row15287 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

theorem rowCheck15287 : row15287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15287 := by decide +kernel

theorem rowEval15287 (x : Key → ℝ) : Integer.Sparse.eval row15287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15287, Integer.Sparse.eval_collectBalanced, rawRowCheck15287]

def rawRow15288 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2669, 2), (key2704, 2), (key2724, 2), (key2778, -1), (key2784, -1), (key2851, -1), (key2868, -1), (key2918, -1), (key2922, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, -1), (key2868, -1), (key3007, 2), (key3021, 2), (key3025, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, -1)]

theorem rawRowCheck15288 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form6 = rawRow15288 := by decide +kernel

def row15288 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

theorem rowCheck15288 : row15288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15288 := by decide +kernel

theorem rowEval15288 (x : Key → ℝ) : Integer.Sparse.eval row15288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck15288, Integer.Sparse.eval_collectBalanced, rawRowCheck15288]

def rawRow15289 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2669, 2), (key2724, 2), (key2704, 2), (key2784, -1), (key2778, -1), (key2868, -1), (key2851, -1), (key2922, -1), (key2918, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2858, -1), (key3007, 2), (key3025, 2), (key3021, 2), (key3009, -1), (key3007, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3022, -1)]

theorem rawRowCheck15289 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form6 = rawRow15289 := by decide +kernel

def row15289 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

theorem rowCheck15289 : row15289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15289 := by decide +kernel

theorem rowEval15289 (x : Key → ℝ) : Integer.Sparse.eval row15289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15289, Integer.Sparse.eval_collectBalanced, rawRowCheck15289]

def rawRow15290 : Integer.Sparse Key := [(key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2704, 2), (key2669, 2), (key2724, 2), (key2851, -1), (key2918, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2807, -1), (key2858, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2827, -1), (key3021, 2), (key3007, 2), (key3025, 2), (key3011, -1), (key3022, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3016, -1)]

theorem rawRowCheck15290 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form6 = rawRow15290 := by decide +kernel

def row15290 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

theorem rowCheck15290 : row15290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15290 := by decide +kernel

theorem rowEval15290 (x : Key → ℝ) : Integer.Sparse.eval row15290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck15290, Integer.Sparse.eval_collectBalanced, rawRowCheck15290]

def rawRow15291 : Integer.Sparse Key := [(key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2704, 2), (key2724, 2), (key2669, 2), (key2918, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2868, -1), (key2784, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key2858, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2827, -1), (key2792, -1), (key3021, 2), (key3025, 2), (key3007, 2), (key3022, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3016, -1), (key3009, -1)]

theorem rawRowCheck15291 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form6 = rawRow15291 := by decide +kernel

def row15291 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

theorem rowCheck15291 : row15291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15291 := by decide +kernel

theorem rowEval15291 (x : Key → ℝ) : Integer.Sparse.eval row15291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15291, Integer.Sparse.eval_collectBalanced, rawRowCheck15291]

def rawRow15292 : Integer.Sparse Key := [(key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2724, 2), (key2669, 2), (key2704, 2), (key2868, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2778, -1), (key2851, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, -1), (key2807, -1), (key3025, 2), (key3007, 2), (key3021, 2), (key3016, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key3007, -1), (key3011, -1)]

theorem rawRowCheck15292 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form6 = rawRow15292 := by decide +kernel

def row15292 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

theorem rowCheck15292 : row15292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15292 := by decide +kernel

theorem rowEval15292 (x : Key → ℝ) : Integer.Sparse.eval row15292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15292, Integer.Sparse.eval_collectBalanced, rawRowCheck15292]

def rawRow15293 : Integer.Sparse Key := [(key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2724, 2), (key2704, 2), (key2669, 2), (key2922, -1), (key2868, -1), (key2918, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, -1), (key2784, -1), (key3025, 2), (key3021, 2), (key3007, 2), (key3025, -1), (key3016, -1), (key3022, -1), (key3009, -1), (key3011, -1), (key3007, -1)]

theorem rawRowCheck15293 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form6 = rawRow15293 := by decide +kernel

def row15293 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

theorem rowCheck15293 : row15293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15293 := by decide +kernel

theorem rowEval15293 (x : Key → ℝ) : Integer.Sparse.eval row15293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15293, Integer.Sparse.eval_collectBalanced, rawRowCheck15293]

def rawRow15294 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key2698, -1), (key2704, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key3021, -1), (key3022, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key3025, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2918, -1), (key2919, -1), (key2918, -1), (key2922, -1), (key2919, -1), (key2922, -1)]

theorem rawRowCheck15294 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form6 = rawRow15294 := by decide +kernel

def row15294 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

theorem rowCheck15294 : row15294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15294 := by decide +kernel

theorem rowEval15294 (x : Key → ℝ) : Integer.Sparse.eval row15294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck15294, Integer.Sparse.eval_collectBalanced, rawRowCheck15294]

def rawRow15295 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2827, -1), (key2801, -1), (key2827, -1), (key2807, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key2704, -1), (key2698, -1), (key2724, -1), (key2698, -1), (key2724, -1), (key2704, -1), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key3022, -1), (key3021, -1), (key3025, -1), (key3021, -1), (key3025, -1), (key3022, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2919, -1), (key2918, -1), (key2922, -1), (key2918, -1), (key2922, -1), (key2919, -1)]

theorem rawRowCheck15295 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form6 = rawRow15295 := by decide +kernel

def row15295 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

theorem rowCheck15295 : row15295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15295 := by decide +kernel

theorem rowEval15295 (x : Key → ℝ) : Integer.Sparse.eval row15295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15295, Integer.Sparse.eval_collectBalanced, rawRowCheck15295]

def rawRow15296 : Integer.Sparse Key := [(key2827, -1), (key2827, -1), (key2807, -1), (key2807, -1), (key2801, -1), (key2801, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key2724, -1), (key2724, -1), (key2704, -1), (key2704, -1), (key2698, -1), (key2698, -1), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key3025, -1), (key3025, -1), (key3022, -1), (key3022, -1), (key3021, -1), (key3021, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2922, -1), (key2919, -1), (key2919, -1), (key2918, -1), (key2918, -1)]

theorem rawRowCheck15296 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form6 = rawRow15296 := by decide +kernel

def row15296 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

theorem rowCheck15296 : row15296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15296 := by decide +kernel

theorem rowEval15296 (x : Key → ℝ) : Integer.Sparse.eval row15296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15296, Integer.Sparse.eval_collectBalanced, rawRowCheck15296]

def rawRow15297 : Integer.Sparse Key := [(key2698, -1), (key2704, -1), (key2851, -1), (key3021, -1), (key2858, -1), (key3022, -1), (key2724, 2), (key2868, 2), (key3025, 2), (key2663, -1), (key2669, -1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, -1), (key2669, 2), (key2704, 2), (key2724, 2), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, -1), (key2868, -1)]

theorem rawRowCheck15297 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form6 = rawRow15297 := by decide +kernel

def row15297 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

theorem rowCheck15297 : row15297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15297 := by decide +kernel

theorem rowEval15297 (x : Key → ℝ) : Integer.Sparse.eval row15297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck15297, Integer.Sparse.eval_collectBalanced, rawRowCheck15297]

def rawRow15298 : Integer.Sparse Key := [(key2704, -1), (key2698, -1), (key3021, -1), (key2851, -1), (key3022, -1), (key2858, -1), (key2724, 2), (key3025, 2), (key2868, 2), (key2669, -1), (key2663, -1), (key2724, -1), (key2698, -1), (key2757, -1), (key2752, -1), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key3009, -1), (key3007, -1), (key3016, -1), (key3011, -1), (key3025, -1), (key3022, -1), (key2669, 2), (key2724, 2), (key2704, 2), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, -1), (key2858, -1)]

theorem rawRowCheck15298 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form6 = rawRow15298 := by decide +kernel

def row15298 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

theorem rowCheck15298 : row15298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15298 := by decide +kernel

theorem rowEval15298 (x : Key → ℝ) : Integer.Sparse.eval row15298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15298, Integer.Sparse.eval_collectBalanced, rawRowCheck15298]

def rawRow15299 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2868, 2), (key2724, 2), (key3025, 2), (key2698, -1), (key2752, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key3011, -1), (key3022, -1), (key3007, -1), (key3025, -1), (key3009, -1), (key3016, -1), (key2704, 2), (key2669, 2), (key2724, 2), (key2807, -1), (key2858, -1), (key2784, -1), (key2868, -1), (key2792, -1), (key2827, -1)]

theorem rawRowCheck15299 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form6 = rawRow15299 := by decide +kernel

def row15299 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

theorem rowCheck15299 : row15299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15299 := by decide +kernel

theorem rowEval15299 (x : Key → ℝ) : Integer.Sparse.eval row15299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck15299, Integer.Sparse.eval_collectBalanced, rawRowCheck15299]

def rawRow15300 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key3021, -1), (key2704, -1), (key2868, 2), (key3025, 2), (key2724, 2), (key2752, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2724, -1), (key2669, -1), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key3022, -1), (key3011, -1), (key3025, -1), (key3007, -1), (key3016, -1), (key3009, -1), (key2704, 2), (key2724, 2), (key2669, 2), (key2858, -1), (key2807, -1), (key2868, -1), (key2784, -1), (key2827, -1), (key2792, -1)]

theorem rawRowCheck15300 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form6 = rawRow15300 := by decide +kernel

def row15300 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

theorem rowCheck15300 : row15300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15300 := by decide +kernel

theorem rowEval15300 (x : Key → ℝ) : Integer.Sparse.eval row15300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15300, Integer.Sparse.eval_collectBalanced, rawRowCheck15300]

def rawRow15301 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2698, -1), (key2851, -1), (key3025, 2), (key2724, 2), (key2868, 2), (key2724, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2663, -1), (key2698, -1), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key3016, -1), (key3025, -1), (key3009, -1), (key3022, -1), (key3007, -1), (key3011, -1), (key2724, 2), (key2669, 2), (key2704, 2), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, -1), (key2807, -1)]

theorem rawRowCheck15301 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form6 = rawRow15301 := by decide +kernel

def row15301 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

theorem rowCheck15301 : row15301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15301 := by decide +kernel

theorem rowEval15301 (x : Key → ℝ) : Integer.Sparse.eval row15301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15301, Integer.Sparse.eval_collectBalanced, rawRowCheck15301]

def rawRow15302 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key2858, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 2), (key2868, 2), (key2724, 2), (key2757, -1), (key2724, -1), (key2752, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key3025, -1), (key3016, -1), (key3022, -1), (key3009, -1), (key3011, -1), (key3007, -1), (key2724, 2), (key2704, 2), (key2669, 2), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, -1), (key2784, -1)]

theorem rawRowCheck15302 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form6 = rawRow15302 := by decide +kernel

def row15302 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

theorem rowCheck15302 : row15302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15302 := by decide +kernel

theorem rowEval15302 (x : Key → ℝ) : Integer.Sparse.eval row15302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15302, Integer.Sparse.eval_collectBalanced, rawRowCheck15302]

def rawRow15303 : Integer.Sparse Key := [(key2681, 4), (key2681, 4), (key2688, 4), (key2712, -4), (key2714, -4), (key2714, -4), (key2815, -4), (key2817, -4), (key2817, -4), (key2863, 12)]

theorem rawRowCheck15303 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form7 = rawRow15303 := by decide +kernel

def row15303 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

theorem rowCheck15303 : row15303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15303 := by decide +kernel

theorem rowEval15303 (x : Key → ℝ) : Integer.Sparse.eval row15303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15303, Integer.Sparse.eval_collectBalanced, rawRowCheck15303]

def rawRow15304 : Integer.Sparse Key := [(key2681, 4), (key2688, 4), (key2681, 4), (key2714, -4), (key2712, -4), (key2714, -4), (key2817, -4), (key2815, -4), (key2817, -4), (key2863, 12)]

theorem rawRowCheck15304 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form7 = rawRow15304 := by decide +kernel

def row15304 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

theorem rowCheck15304 : row15304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15304 := by decide +kernel

theorem rowEval15304 (x : Key → ℝ) : Integer.Sparse.eval row15304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15304, Integer.Sparse.eval_collectBalanced, rawRowCheck15304]

def rawRow15305 : Integer.Sparse Key := [(key2688, 4), (key2681, 4), (key2681, 4), (key2714, -4), (key2714, -4), (key2712, -4), (key2817, -4), (key2817, -4), (key2815, -4), (key2863, 12)]

theorem rawRowCheck15305 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form7 = rawRow15305 := by decide +kernel

def row15305 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

theorem rowCheck15305 : row15305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15305 := by decide +kernel

theorem rowEval15305 (x : Key → ℝ) : Integer.Sparse.eval row15305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15305, Integer.Sparse.eval_collectBalanced, rawRowCheck15305]

def rawRow15306 : Integer.Sparse Key := [(key2681, 4), (key2712, 4), (key2714, 4), (key2681, -4), (key2688, -4), (key2714, -4), (key2815, -4), (key2817, -4), (key2863, -4), (key2817, 12)]

theorem rawRowCheck15306 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form7 = rawRow15306 := by decide +kernel

def row15306 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15306 : row15306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15306 := by decide +kernel

theorem rowEval15306 (x : Key → ℝ) : Integer.Sparse.eval row15306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15306, Integer.Sparse.eval_collectBalanced, rawRowCheck15306]

def rawRow15307 : Integer.Sparse Key := [(key2681, 4), (key2714, 4), (key2712, 4), (key2688, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2815, -4), (key2863, -4), (key2817, 12)]

theorem rawRowCheck15307 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form7 = rawRow15307 := by decide +kernel

def row15307 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15307 : row15307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15307 := by decide +kernel

theorem rowEval15307 (x : Key → ℝ) : Integer.Sparse.eval row15307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15307, Integer.Sparse.eval_collectBalanced, rawRowCheck15307]

def rawRow15308 : Integer.Sparse Key := [(key2712, 4), (key2681, 4), (key2714, 4), (key2681, -4), (key2714, -4), (key2688, -4), (key2815, -4), (key2863, -4), (key2817, -4), (key2817, 12)]

theorem rawRowCheck15308 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form7 = rawRow15308 := by decide +kernel

def row15308 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15308 : row15308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15308 := by decide +kernel

theorem rowEval15308 (x : Key → ℝ) : Integer.Sparse.eval row15308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15308, Integer.Sparse.eval_collectBalanced, rawRowCheck15308]

def rawRow15309 : Integer.Sparse Key := [(key2712, 4), (key2714, 4), (key2681, 4), (key2714, -4), (key2681, -4), (key2688, -4), (key2863, -4), (key2815, -4), (key2817, -4), (key2817, 12)]

theorem rawRowCheck15309 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form7 = rawRow15309 := by decide +kernel

def row15309 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15309 : row15309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15309 := by decide +kernel

theorem rowEval15309 (x : Key → ℝ) : Integer.Sparse.eval row15309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15309, Integer.Sparse.eval_collectBalanced, rawRowCheck15309]

def rawRow15310 : Integer.Sparse Key := [(key2714, 4), (key2681, 4), (key2712, 4), (key2688, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2863, -4), (key2815, -4), (key2817, 12)]

theorem rawRowCheck15310 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form7 = rawRow15310 := by decide +kernel

def row15310 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15310 : row15310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15310 := by decide +kernel

theorem rowEval15310 (x : Key → ℝ) : Integer.Sparse.eval row15310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15310, Integer.Sparse.eval_collectBalanced, rawRowCheck15310]

def rawRow15311 : Integer.Sparse Key := [(key2714, 4), (key2712, 4), (key2681, 4), (key2714, -4), (key2688, -4), (key2681, -4), (key2863, -4), (key2817, -4), (key2815, -4), (key2817, 12)]

theorem rawRowCheck15311 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form7 = rawRow15311 := by decide +kernel

def row15311 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15311 : row15311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15311 := by decide +kernel

theorem rowEval15311 (x : Key → ℝ) : Integer.Sparse.eval row15311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15311, Integer.Sparse.eval_collectBalanced, rawRowCheck15311]

def rawRow15312 : Integer.Sparse Key := [(key2681, 4), (key2681, 4), (key2688, 4), (key2815, -4), (key2817, -4), (key2817, -4), (key2712, -4), (key2714, -4), (key2714, -4), (key2863, 12)]

theorem rawRowCheck15312 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form7 = rawRow15312 := by decide +kernel

def row15312 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

theorem rowCheck15312 : row15312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15312 := by decide +kernel

theorem rowEval15312 (x : Key → ℝ) : Integer.Sparse.eval row15312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15312, Integer.Sparse.eval_collectBalanced, rawRowCheck15312]

def rawRow15313 : Integer.Sparse Key := [(key2681, 4), (key2688, 4), (key2681, 4), (key2817, -4), (key2815, -4), (key2817, -4), (key2714, -4), (key2712, -4), (key2714, -4), (key2863, 12)]

theorem rawRowCheck15313 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form7 = rawRow15313 := by decide +kernel

def row15313 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

theorem rowCheck15313 : row15313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15313 := by decide +kernel

theorem rowEval15313 (x : Key → ℝ) : Integer.Sparse.eval row15313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15313, Integer.Sparse.eval_collectBalanced, rawRowCheck15313]

def rawRow15314 : Integer.Sparse Key := [(key2688, 4), (key2681, 4), (key2681, 4), (key2817, -4), (key2817, -4), (key2815, -4), (key2714, -4), (key2714, -4), (key2712, -4), (key2863, 12)]

theorem rawRowCheck15314 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form7 = rawRow15314 := by decide +kernel

def row15314 : Integer.Sparse Key := [(key2681, 8), (key2688, 4), (key2712, -4), (key2714, -8), (key2815, -4), (key2817, -8), (key2863, 12)]

theorem rowCheck15314 : row15314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15314 := by decide +kernel

theorem rowEval15314 (x : Key → ℝ) : Integer.Sparse.eval row15314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15314, Integer.Sparse.eval_collectBalanced, rawRowCheck15314]

def rawRow15315 : Integer.Sparse Key := [(key2681, 4), (key2815, 4), (key2817, 4), (key2681, -4), (key2688, -4), (key2817, -4), (key2712, -4), (key2714, -4), (key2863, -4), (key2714, 12)]

theorem rawRowCheck15315 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form7 = rawRow15315 := by decide +kernel

def row15315 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15315 : row15315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15315 := by decide +kernel

theorem rowEval15315 (x : Key → ℝ) : Integer.Sparse.eval row15315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15315, Integer.Sparse.eval_collectBalanced, rawRowCheck15315]

def rawRow15316 : Integer.Sparse Key := [(key2681, 4), (key2817, 4), (key2815, 4), (key2688, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2712, -4), (key2863, -4), (key2714, 12)]

theorem rawRowCheck15316 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form7 = rawRow15316 := by decide +kernel

def row15316 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15316 : row15316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15316 := by decide +kernel

theorem rowEval15316 (x : Key → ℝ) : Integer.Sparse.eval row15316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15316, Integer.Sparse.eval_collectBalanced, rawRowCheck15316]

def rawRow15317 : Integer.Sparse Key := [(key2815, 4), (key2681, 4), (key2817, 4), (key2681, -4), (key2817, -4), (key2688, -4), (key2712, -4), (key2863, -4), (key2714, -4), (key2714, 12)]

theorem rawRowCheck15317 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form7 = rawRow15317 := by decide +kernel

def row15317 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15317 : row15317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15317 := by decide +kernel

theorem rowEval15317 (x : Key → ℝ) : Integer.Sparse.eval row15317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15317, Integer.Sparse.eval_collectBalanced, rawRowCheck15317]

def rawRow15318 : Integer.Sparse Key := [(key2815, 4), (key2817, 4), (key2681, 4), (key2817, -4), (key2681, -4), (key2688, -4), (key2863, -4), (key2712, -4), (key2714, -4), (key2714, 12)]

theorem rawRowCheck15318 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form7 = rawRow15318 := by decide +kernel

def row15318 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15318 : row15318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15318 := by decide +kernel

theorem rowEval15318 (x : Key → ℝ) : Integer.Sparse.eval row15318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15318, Integer.Sparse.eval_collectBalanced, rawRowCheck15318]

def rawRow15319 : Integer.Sparse Key := [(key2817, 4), (key2681, 4), (key2815, 4), (key2688, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2863, -4), (key2712, -4), (key2714, 12)]

theorem rawRowCheck15319 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form7 = rawRow15319 := by decide +kernel

def row15319 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15319 : row15319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15319 := by decide +kernel

theorem rowEval15319 (x : Key → ℝ) : Integer.Sparse.eval row15319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15319, Integer.Sparse.eval_collectBalanced, rawRowCheck15319]

def rawRow15320 : Integer.Sparse Key := [(key2817, 4), (key2815, 4), (key2681, 4), (key2817, -4), (key2688, -4), (key2681, -4), (key2863, -4), (key2714, -4), (key2712, -4), (key2714, 12)]

theorem rawRowCheck15320 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form7 = rawRow15320 := by decide +kernel

def row15320 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15320 : row15320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15320 := by decide +kernel

theorem rowEval15320 (x : Key → ℝ) : Integer.Sparse.eval row15320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15320, Integer.Sparse.eval_collectBalanced, rawRowCheck15320]

def rawRow15321 : Integer.Sparse Key := [(key2681, 4), (key2712, 4), (key2714, 4), (key2815, -4), (key2817, -4), (key2863, -4), (key2681, -4), (key2688, -4), (key2714, -4), (key2817, 12)]

theorem rawRowCheck15321 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form7 = rawRow15321 := by decide +kernel

def row15321 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15321 : row15321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15321 := by decide +kernel

theorem rowEval15321 (x : Key → ℝ) : Integer.Sparse.eval row15321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15321, Integer.Sparse.eval_collectBalanced, rawRowCheck15321]

def rawRow15322 : Integer.Sparse Key := [(key2681, 4), (key2714, 4), (key2712, 4), (key2817, -4), (key2815, -4), (key2863, -4), (key2688, -4), (key2681, -4), (key2714, -4), (key2817, 12)]

theorem rawRowCheck15322 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form7 = rawRow15322 := by decide +kernel

def row15322 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15322 : row15322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15322 := by decide +kernel

theorem rowEval15322 (x : Key → ℝ) : Integer.Sparse.eval row15322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15322, Integer.Sparse.eval_collectBalanced, rawRowCheck15322]

def rawRow15323 : Integer.Sparse Key := [(key2712, 4), (key2681, 4), (key2714, 4), (key2815, -4), (key2863, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2688, -4), (key2817, 12)]

theorem rawRowCheck15323 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form7 = rawRow15323 := by decide +kernel

def row15323 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15323 : row15323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15323 := by decide +kernel

theorem rowEval15323 (x : Key → ℝ) : Integer.Sparse.eval row15323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15323, Integer.Sparse.eval_collectBalanced, rawRowCheck15323]

def rawRow15324 : Integer.Sparse Key := [(key2712, 4), (key2714, 4), (key2681, 4), (key2863, -4), (key2815, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2688, -4), (key2817, 12)]

theorem rawRowCheck15324 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form7 = rawRow15324 := by decide +kernel

def row15324 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15324 : row15324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15324 := by decide +kernel

theorem rowEval15324 (x : Key → ℝ) : Integer.Sparse.eval row15324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15324, Integer.Sparse.eval_collectBalanced, rawRowCheck15324]

def rawRow15325 : Integer.Sparse Key := [(key2714, 4), (key2681, 4), (key2712, 4), (key2817, -4), (key2863, -4), (key2815, -4), (key2688, -4), (key2714, -4), (key2681, -4), (key2817, 12)]

theorem rawRowCheck15325 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form7 = rawRow15325 := by decide +kernel

def row15325 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15325 : row15325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15325 := by decide +kernel

theorem rowEval15325 (x : Key → ℝ) : Integer.Sparse.eval row15325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15325, Integer.Sparse.eval_collectBalanced, rawRowCheck15325]

def rawRow15326 : Integer.Sparse Key := [(key2714, 4), (key2712, 4), (key2681, 4), (key2863, -4), (key2817, -4), (key2815, -4), (key2714, -4), (key2688, -4), (key2681, -4), (key2817, 12)]

theorem rawRowCheck15326 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form7 = rawRow15326 := by decide +kernel

def row15326 : Integer.Sparse Key := [(key2688, -4), (key2712, 4), (key2815, -4), (key2817, 8), (key2863, -4)]

theorem rowCheck15326 : row15326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15326 := by decide +kernel

theorem rowEval15326 (x : Key → ℝ) : Integer.Sparse.eval row15326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15326, Integer.Sparse.eval_collectBalanced, rawRowCheck15326]

def rawRow15327 : Integer.Sparse Key := [(key2681, 4), (key2815, 4), (key2817, 4), (key2712, -4), (key2714, -4), (key2863, -4), (key2681, -4), (key2688, -4), (key2817, -4), (key2714, 12)]

theorem rawRowCheck15327 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form7 = rawRow15327 := by decide +kernel

def row15327 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15327 : row15327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15327 := by decide +kernel

theorem rowEval15327 (x : Key → ℝ) : Integer.Sparse.eval row15327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15327, Integer.Sparse.eval_collectBalanced, rawRowCheck15327]

def rawRow15328 : Integer.Sparse Key := [(key2681, 4), (key2817, 4), (key2815, 4), (key2714, -4), (key2712, -4), (key2863, -4), (key2688, -4), (key2681, -4), (key2817, -4), (key2714, 12)]

theorem rawRowCheck15328 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form7 = rawRow15328 := by decide +kernel

def row15328 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15328 : row15328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15328 := by decide +kernel

theorem rowEval15328 (x : Key → ℝ) : Integer.Sparse.eval row15328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15328, Integer.Sparse.eval_collectBalanced, rawRowCheck15328]

def rawRow15329 : Integer.Sparse Key := [(key2815, 4), (key2681, 4), (key2817, 4), (key2712, -4), (key2863, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2688, -4), (key2714, 12)]

theorem rawRowCheck15329 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form7 = rawRow15329 := by decide +kernel

def row15329 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15329 : row15329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15329 := by decide +kernel

theorem rowEval15329 (x : Key → ℝ) : Integer.Sparse.eval row15329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15329, Integer.Sparse.eval_collectBalanced, rawRowCheck15329]

def rawRow15330 : Integer.Sparse Key := [(key2815, 4), (key2817, 4), (key2681, 4), (key2863, -4), (key2712, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2688, -4), (key2714, 12)]

theorem rawRowCheck15330 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form7 = rawRow15330 := by decide +kernel

def row15330 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15330 : row15330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15330 := by decide +kernel

theorem rowEval15330 (x : Key → ℝ) : Integer.Sparse.eval row15330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15330, Integer.Sparse.eval_collectBalanced, rawRowCheck15330]

def rawRow15331 : Integer.Sparse Key := [(key2817, 4), (key2681, 4), (key2815, 4), (key2714, -4), (key2863, -4), (key2712, -4), (key2688, -4), (key2817, -4), (key2681, -4), (key2714, 12)]

theorem rawRowCheck15331 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form7 = rawRow15331 := by decide +kernel

def row15331 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15331 : row15331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15331 := by decide +kernel

theorem rowEval15331 (x : Key → ℝ) : Integer.Sparse.eval row15331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15331, Integer.Sparse.eval_collectBalanced, rawRowCheck15331]

def rawRow15332 : Integer.Sparse Key := [(key2817, 4), (key2815, 4), (key2681, 4), (key2863, -4), (key2714, -4), (key2712, -4), (key2817, -4), (key2688, -4), (key2681, -4), (key2714, 12)]

theorem rawRowCheck15332 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form7 = rawRow15332 := by decide +kernel

def row15332 : Integer.Sparse Key := [(key2688, -4), (key2712, -4), (key2714, 8), (key2815, 4), (key2863, -4)]

theorem rowCheck15332 : row15332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15332 := by decide +kernel

theorem rowEval15332 (x : Key → ℝ) : Integer.Sparse.eval row15332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15332, Integer.Sparse.eval_collectBalanced, rawRowCheck15332]

def rawRow15333 : Integer.Sparse Key := [(key2712, 4), (key2815, 4), (key2863, 4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2688, 12)]

theorem rawRowCheck15333 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form7 = rawRow15333 := by decide +kernel

def row15333 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

theorem rowCheck15333 : row15333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15333 := by decide +kernel

theorem rowEval15333 (x : Key → ℝ) : Integer.Sparse.eval row15333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15333, Integer.Sparse.eval_collectBalanced, rawRowCheck15333]

def rawRow15334 : Integer.Sparse Key := [(key2712, 4), (key2863, 4), (key2815, 4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2688, 12)]

theorem rawRowCheck15334 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form7 = rawRow15334 := by decide +kernel

def row15334 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

theorem rowCheck15334 : row15334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15334 := by decide +kernel

theorem rowEval15334 (x : Key → ℝ) : Integer.Sparse.eval row15334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -2, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15334, Integer.Sparse.eval_collectBalanced, rawRowCheck15334]

def rawRow15335 : Integer.Sparse Key := [(key2815, 4), (key2712, 4), (key2863, 4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2688, 12)]

theorem rawRowCheck15335 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form7 = rawRow15335 := by decide +kernel

def row15335 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

theorem rowCheck15335 : row15335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15335 := by decide +kernel

theorem rowEval15335 (x : Key → ℝ) : Integer.Sparse.eval row15335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15335, Integer.Sparse.eval_collectBalanced, rawRowCheck15335]

def rawRow15336 : Integer.Sparse Key := [(key2815, 4), (key2863, 4), (key2712, 4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2688, 12)]

theorem rawRowCheck15336 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form7 = rawRow15336 := by decide +kernel

def row15336 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

theorem rowCheck15336 : row15336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15336 := by decide +kernel

theorem rowEval15336 (x : Key → ℝ) : Integer.Sparse.eval row15336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15336, Integer.Sparse.eval_collectBalanced, rawRowCheck15336]

def rawRow15337 : Integer.Sparse Key := [(key2863, 4), (key2712, 4), (key2815, 4), (key2714, -4), (key2817, -4), (key2681, -4), (key2714, -4), (key2817, -4), (key2681, -4), (key2688, 12)]

theorem rawRowCheck15337 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form7 = rawRow15337 := by decide +kernel

def row15337 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

theorem rowCheck15337 : row15337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15337 := by decide +kernel

theorem rowEval15337 (x : Key → ℝ) : Integer.Sparse.eval row15337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15337, Integer.Sparse.eval_collectBalanced, rawRowCheck15337]

def rawRow15338 : Integer.Sparse Key := [(key2863, 4), (key2815, 4), (key2712, 4), (key2817, -4), (key2714, -4), (key2681, -4), (key2817, -4), (key2714, -4), (key2681, -4), (key2688, 12)]

theorem rawRowCheck15338 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form7 = rawRow15338 := by decide +kernel

def row15338 : Integer.Sparse Key := [(key2681, -8), (key2688, 12), (key2712, 4), (key2714, -8), (key2815, 4), (key2817, -8), (key2863, 4)]

theorem rowCheck15338 : row15338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15338 := by decide +kernel

theorem rowEval15338 (x : Key → ℝ) : Integer.Sparse.eval row15338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block4.form7) x := by
  rw [rowCheck15338, Integer.Sparse.eval_collectBalanced, rawRowCheck15338]

def rawRow15339 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2599, 6), (key2763, -2), (key2767, -2), (key2767, -2), (key2840, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2888, -2), (key2888, -2), (key2909, -2), (key2930, 6), (key2967, -2), (key2967, -2), (key2988, -2)]

theorem rawRowCheck15339 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form8 = rawRow15339 := by decide +kernel

def row15339 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

theorem rowCheck15339 : row15339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15339 := by decide +kernel

theorem rowEval15339 (x : Key → ℝ) : Integer.Sparse.eval row15339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15339, Integer.Sparse.eval_collectBalanced, rawRowCheck15339]

def rawRow15340 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2599, 6), (key2767, -2), (key2763, -2), (key2767, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2888, -2), (key2909, -2), (key2888, -2), (key2930, 6), (key2967, -2), (key2988, -2), (key2967, -2)]

theorem rawRowCheck15340 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form8 = rawRow15340 := by decide +kernel

def row15340 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

theorem rowCheck15340 : row15340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15340 := by decide +kernel

theorem rowEval15340 (x : Key → ℝ) : Integer.Sparse.eval row15340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15340, Integer.Sparse.eval_collectBalanced, rawRowCheck15340]

def rawRow15341 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, 6), (key2767, -2), (key2767, -2), (key2763, -2), (key2875, 2), (key2875, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2909, -2), (key2888, -2), (key2888, -2), (key2930, 6), (key2988, -2), (key2967, -2), (key2967, -2)]

theorem rawRowCheck15341 : GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form8 = rawRow15341 := by decide +kernel

def row15341 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

theorem rowCheck15341 : row15341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15341 := by decide +kernel

theorem rowEval15341 (x : Key → ℝ) : Integer.Sparse.eval row15341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15341, Integer.Sparse.eval_collectBalanced, rawRowCheck15341]

def rawRow15342 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2599, -2), (key2588, 6), (key2840, -2), (key2844, -2), (key2888, -2), (key2763, 2), (key2767, 2), (key2840, 2), (key2875, 2), (key2888, 2), (key2909, 2), (key2767, -2), (key2844, -2), (key2875, -2), (key2967, 6), (key2930, -2), (key2967, -2), (key2988, -2)]

theorem rawRowCheck15342 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form8 = rawRow15342 := by decide +kernel

def row15342 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15342 : row15342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15342 := by decide +kernel

theorem rowEval15342 (x : Key → ℝ) : Integer.Sparse.eval row15342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15342, Integer.Sparse.eval_collectBalanced, rawRowCheck15342]

def rawRow15343 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2599, -2), (key2588, 6), (key2844, -2), (key2840, -2), (key2888, -2), (key2767, 2), (key2763, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2767, -2), (key2875, -2), (key2844, -2), (key2967, 6), (key2930, -2), (key2988, -2), (key2967, -2)]

theorem rawRowCheck15343 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form8 = rawRow15343 := by decide +kernel

def row15343 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15343 : row15343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15343 := by decide +kernel

theorem rowEval15343 (x : Key → ℝ) : Integer.Sparse.eval row15343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15343, Integer.Sparse.eval_collectBalanced, rawRowCheck15343]

def rawRow15344 : Integer.Sparse Key := [(key2584, -2), (key2599, -2), (key2588, -2), (key2588, 6), (key2840, -2), (key2888, -2), (key2844, -2), (key2840, 2), (key2888, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2844, -2), (key2767, -2), (key2875, -2), (key2967, 6), (key2967, -2), (key2930, -2), (key2988, -2)]

theorem rawRowCheck15344 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form8 = rawRow15344 := by decide +kernel

def row15344 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15344 : row15344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15344 := by decide +kernel

theorem rowEval15344 (x : Key → ℝ) : Integer.Sparse.eval row15344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15344, Integer.Sparse.eval_collectBalanced, rawRowCheck15344]

def rawRow15345 : Integer.Sparse Key := [(key2599, -2), (key2584, -2), (key2588, -2), (key2588, 6), (key2888, -2), (key2840, -2), (key2844, -2), (key2888, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2875, 2), (key2767, 2), (key2844, -2), (key2875, -2), (key2767, -2), (key2967, 6), (key2967, -2), (key2988, -2), (key2930, -2)]

theorem rawRowCheck15345 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form8 = rawRow15345 := by decide +kernel

def row15345 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15345 : row15345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15345 := by decide +kernel

theorem rowEval15345 (x : Key → ℝ) : Integer.Sparse.eval row15345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15345, Integer.Sparse.eval_collectBalanced, rawRowCheck15345]

def rawRow15346 : Integer.Sparse Key := [(key2588, -2), (key2599, -2), (key2584, -2), (key2588, 6), (key2844, -2), (key2888, -2), (key2840, -2), (key2875, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2763, 2), (key2840, 2), (key2875, -2), (key2767, -2), (key2844, -2), (key2967, 6), (key2988, -2), (key2930, -2), (key2967, -2)]

theorem rawRowCheck15346 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form8 = rawRow15346 := by decide +kernel

def row15346 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15346 : row15346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15346 := by decide +kernel

theorem rowEval15346 (x : Key → ℝ) : Integer.Sparse.eval row15346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15346, Integer.Sparse.eval_collectBalanced, rawRowCheck15346]

def rawRow15347 : Integer.Sparse Key := [(key2599, -2), (key2588, -2), (key2584, -2), (key2588, 6), (key2888, -2), (key2844, -2), (key2840, -2), (key2909, 2), (key2875, 2), (key2888, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2875, -2), (key2844, -2), (key2767, -2), (key2967, 6), (key2988, -2), (key2967, -2), (key2930, -2)]

theorem rawRowCheck15347 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form8 = rawRow15347 := by decide +kernel

def row15347 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15347 : row15347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15347 := by decide +kernel

theorem rowEval15347 (x : Key → ℝ) : Integer.Sparse.eval row15347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15347, Integer.Sparse.eval_collectBalanced, rawRowCheck15347]

def rawRow15348 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2930, 6), (key2584, -2), (key2588, -2), (key2588, -2), (key2840, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2967, -2), (key2967, -2), (key2988, -2), (key2599, 6), (key2888, -2), (key2888, -2), (key2909, -2)]

theorem rawRowCheck15348 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form8 = rawRow15348 := by decide +kernel

def row15348 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

theorem rowCheck15348 : row15348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15348 := by decide +kernel

theorem rowEval15348 (x : Key → ℝ) : Integer.Sparse.eval row15348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15348, Integer.Sparse.eval_collectBalanced, rawRowCheck15348]

def rawRow15349 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2930, 6), (key2588, -2), (key2584, -2), (key2588, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2967, -2), (key2988, -2), (key2967, -2), (key2599, 6), (key2888, -2), (key2909, -2), (key2888, -2)]

theorem rawRowCheck15349 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form8 = rawRow15349 := by decide +kernel

def row15349 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

theorem rowCheck15349 : row15349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15349 := by decide +kernel

theorem rowEval15349 (x : Key → ℝ) : Integer.Sparse.eval row15349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15349, Integer.Sparse.eval_collectBalanced, rawRowCheck15349]

def rawRow15350 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2930, 6), (key2588, -2), (key2588, -2), (key2584, -2), (key2875, 2), (key2875, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, -2), (key2967, -2), (key2967, -2), (key2599, 6), (key2909, -2), (key2888, -2), (key2888, -2)]

theorem rawRowCheck15350 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form8 = rawRow15350 := by decide +kernel

def row15350 : Integer.Sparse Key := [(key2584, -2), (key2588, -4), (key2599, 6), (key2763, -2), (key2767, -4), (key2840, 4), (key2844, 4), (key2875, 4), (key2888, -4), (key2909, -2), (key2930, 6), (key2967, -4), (key2988, -2)]

theorem rowCheck15350 : row15350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15350 := by decide +kernel

theorem rowEval15350 (x : Key → ℝ) : Integer.Sparse.eval row15350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15350, Integer.Sparse.eval_collectBalanced, rawRowCheck15350]

def rawRow15351 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2930, -2), (key2767, 6), (key2840, -2), (key2844, -2), (key2967, -2), (key2584, 2), (key2588, 2), (key2840, 2), (key2875, 2), (key2967, 2), (key2988, 2), (key2588, -2), (key2844, -2), (key2875, -2), (key2888, 6), (key2599, -2), (key2888, -2), (key2909, -2)]

theorem rawRowCheck15351 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form8 = rawRow15351 := by decide +kernel

def row15351 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15351 : row15351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15351 := by decide +kernel

theorem rowEval15351 (x : Key → ℝ) : Integer.Sparse.eval row15351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15351, Integer.Sparse.eval_collectBalanced, rawRowCheck15351]

def rawRow15352 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2930, -2), (key2767, 6), (key2844, -2), (key2840, -2), (key2967, -2), (key2588, 2), (key2584, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2588, -2), (key2875, -2), (key2844, -2), (key2888, 6), (key2599, -2), (key2909, -2), (key2888, -2)]

theorem rawRowCheck15352 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form8 = rawRow15352 := by decide +kernel

def row15352 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15352 : row15352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15352 := by decide +kernel

theorem rowEval15352 (x : Key → ℝ) : Integer.Sparse.eval row15352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15352, Integer.Sparse.eval_collectBalanced, rawRowCheck15352]

def rawRow15353 : Integer.Sparse Key := [(key2763, -2), (key2930, -2), (key2767, -2), (key2767, 6), (key2840, -2), (key2967, -2), (key2844, -2), (key2840, 2), (key2967, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2844, -2), (key2588, -2), (key2875, -2), (key2888, 6), (key2888, -2), (key2599, -2), (key2909, -2)]

theorem rawRowCheck15353 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form8 = rawRow15353 := by decide +kernel

def row15353 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15353 : row15353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15353 := by decide +kernel

theorem rowEval15353 (x : Key → ℝ) : Integer.Sparse.eval row15353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15353, Integer.Sparse.eval_collectBalanced, rawRowCheck15353]

def rawRow15354 : Integer.Sparse Key := [(key2930, -2), (key2763, -2), (key2767, -2), (key2767, 6), (key2967, -2), (key2840, -2), (key2844, -2), (key2967, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2875, 2), (key2588, 2), (key2844, -2), (key2875, -2), (key2588, -2), (key2888, 6), (key2888, -2), (key2909, -2), (key2599, -2)]

theorem rawRowCheck15354 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form8 = rawRow15354 := by decide +kernel

def row15354 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15354 : row15354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15354 := by decide +kernel

theorem rowEval15354 (x : Key → ℝ) : Integer.Sparse.eval row15354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15354, Integer.Sparse.eval_collectBalanced, rawRowCheck15354]

def rawRow15355 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2763, -2), (key2767, 6), (key2844, -2), (key2967, -2), (key2840, -2), (key2875, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2584, 2), (key2840, 2), (key2875, -2), (key2588, -2), (key2844, -2), (key2888, 6), (key2909, -2), (key2599, -2), (key2888, -2)]

theorem rawRowCheck15355 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form8 = rawRow15355 := by decide +kernel

def row15355 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15355 : row15355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15355 := by decide +kernel

theorem rowEval15355 (x : Key → ℝ) : Integer.Sparse.eval row15355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15355, Integer.Sparse.eval_collectBalanced, rawRowCheck15355]

def rawRow15356 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2763, -2), (key2767, 6), (key2967, -2), (key2844, -2), (key2840, -2), (key2988, 2), (key2875, 2), (key2967, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2875, -2), (key2844, -2), (key2588, -2), (key2888, 6), (key2909, -2), (key2888, -2), (key2599, -2)]

theorem rawRowCheck15356 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form8 = rawRow15356 := by decide +kernel

def row15356 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -2), (key2767, 4), (key2844, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2988, 2)]

theorem rowCheck15356 : row15356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15356 := by decide +kernel

theorem rowEval15356 (x : Key → ℝ) : Integer.Sparse.eval row15356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15356, Integer.Sparse.eval_collectBalanced, rawRowCheck15356]

def rawRow15357 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2888, -2), (key2967, 6), (key2584, -2), (key2588, -2), (key2599, -2), (key2763, 2), (key2767, 2), (key2840, 2), (key2875, 2), (key2888, 2), (key2909, 2), (key2930, -2), (key2967, -2), (key2988, -2), (key2588, 6), (key2767, -2), (key2844, -2), (key2875, -2)]

theorem rawRowCheck15357 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form8 = rawRow15357 := by decide +kernel

def row15357 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15357 : row15357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15357 := by decide +kernel

theorem rowEval15357 (x : Key → ℝ) : Integer.Sparse.eval row15357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15357, Integer.Sparse.eval_collectBalanced, rawRowCheck15357]

def rawRow15358 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2888, -2), (key2967, 6), (key2588, -2), (key2584, -2), (key2599, -2), (key2767, 2), (key2763, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2930, -2), (key2988, -2), (key2967, -2), (key2588, 6), (key2767, -2), (key2875, -2), (key2844, -2)]

theorem rawRowCheck15358 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form8 = rawRow15358 := by decide +kernel

def row15358 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15358 : row15358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15358 := by decide +kernel

theorem rowEval15358 (x : Key → ℝ) : Integer.Sparse.eval row15358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15358, Integer.Sparse.eval_collectBalanced, rawRowCheck15358]

def rawRow15359 : Integer.Sparse Key := [(key2840, -2), (key2888, -2), (key2844, -2), (key2967, 6), (key2584, -2), (key2599, -2), (key2588, -2), (key2840, 2), (key2888, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2967, -2), (key2930, -2), (key2988, -2), (key2588, 6), (key2844, -2), (key2767, -2), (key2875, -2)]

theorem rawRowCheck15359 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form8 = rawRow15359 := by decide +kernel

def row15359 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 2), (key2844, -4), (key2909, 2), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15359 : row15359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15359 := by decide +kernel

theorem rowEval15359 (x : Key → ℝ) : Integer.Sparse.eval row15359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15359, Integer.Sparse.eval_collectBalanced, rawRowCheck15359]

end MUB6.Certificate.GramRows

end OAI
