import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
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

def rawRow9216 : Integer.Sparse Key := [(key2463, -6), (key2497, -6), (key2369, -6), (key2463, -6), (key2474, 2), (key2397, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2431, 2), (key2497, 2), (key2384, 2), (key2474, 2), (key2369, 2), (key2397, 2)]

theorem rawRowCheck9216 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form3 = rawRow9216 := by decide +kernel

def row9216 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9216 : row9216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9216 := by decide +kernel

theorem rowEval9216 (x : Key → ℝ) : Integer.Sparse.eval row9216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9216, Integer.Sparse.eval_collectBalanced, rawRowCheck9216]

def rawRow9217 : Integer.Sparse Key := [(key2463, -6), (key2497, -6), (key2463, -6), (key2369, -6), (key2474, 2), (key2463, 2), (key2397, 2), (key2497, 2), (key2463, 2), (key2369, 2), (key2497, 2), (key2431, 2), (key2474, 2), (key2384, 2), (key2397, 2), (key2369, 2)]

theorem rawRowCheck9217 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form3 = rawRow9217 := by decide +kernel

def row9217 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9217 : row9217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9217 := by decide +kernel

theorem rowEval9217 (x : Key → ℝ) : Integer.Sparse.eval row9217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9217, Integer.Sparse.eval_collectBalanced, rawRowCheck9217]

def rawRow9218 : Integer.Sparse Key := [(key2497, -6), (key2369, -6), (key2463, -6), (key2463, -6), (key2431, 2), (key2497, 2), (key2497, 2), (key2384, 2), (key2474, 2), (key2474, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck9218 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form3 = rawRow9218 := by decide +kernel

def row9218 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9218 : row9218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9218 := by decide +kernel

theorem rowEval9218 (x : Key → ℝ) : Integer.Sparse.eval row9218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9218, Integer.Sparse.eval_collectBalanced, rawRowCheck9218]

def rawRow9219 : Integer.Sparse Key := [(key2497, -6), (key2463, -6), (key2369, -6), (key2463, -6), (key2497, 2), (key2431, 2), (key2497, 2), (key2474, 2), (key2384, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

theorem rawRowCheck9219 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form3 = rawRow9219 := by decide +kernel

def row9219 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9219 : row9219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9219 := by decide +kernel

theorem rowEval9219 (x : Key → ℝ) : Integer.Sparse.eval row9219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9219, Integer.Sparse.eval_collectBalanced, rawRowCheck9219]

def rawRow9220 : Integer.Sparse Key := [(key2497, -6), (key2463, -6), (key2463, -6), (key2369, -6), (key2497, 2), (key2497, 2), (key2431, 2), (key2474, 2), (key2474, 2), (key2384, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

theorem rawRowCheck9220 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form3 = rawRow9220 := by decide +kernel

def row9220 : Integer.Sparse Key := [(key2369, -2), (key2384, 2), (key2397, 4), (key2431, 2), (key2463, -8), (key2474, 4), (key2497, -2)]

theorem rowCheck9220 : row9220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9220 := by decide +kernel

theorem rowEval9220 (x : Key → ℝ) : Integer.Sparse.eval row9220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form3) x := by
  rw [rowCheck9220, Integer.Sparse.eval_collectBalanced, rawRowCheck9220]

def rawRow9221 : Integer.Sparse Key := [(key2449, -6), (key2453, -6), (key2453, -6), (key2514, -6), (key2354, 2), (key2358, 2), (key2358, 2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2514, 2), (key2514, 2), (key2559, 2)]

theorem rawRowCheck9221 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form4 = rawRow9221 := by decide +kernel

def row9221 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9221 : row9221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9221 := by decide +kernel

theorem rowEval9221 (x : Key → ℝ) : Integer.Sparse.eval row9221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9221, Integer.Sparse.eval_collectBalanced, rawRowCheck9221]

def rawRow9222 : Integer.Sparse Key := [(key2453, -6), (key2449, -6), (key2453, -6), (key2514, -6), (key2358, 2), (key2354, 2), (key2358, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2514, 2), (key2559, 2), (key2514, 2)]

theorem rawRowCheck9222 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form4 = rawRow9222 := by decide +kernel

def row9222 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9222 : row9222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9222 := by decide +kernel

theorem rowEval9222 (x : Key → ℝ) : Integer.Sparse.eval row9222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9222, Integer.Sparse.eval_collectBalanced, rawRowCheck9222]

def rawRow9223 : Integer.Sparse Key := [(key2453, -6), (key2453, -6), (key2449, -6), (key2514, -6), (key2358, 2), (key2358, 2), (key2354, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2559, 2), (key2514, 2), (key2514, 2)]

theorem rawRowCheck9223 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form4 = rawRow9223 := by decide +kernel

def row9223 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9223 : row9223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9223 := by decide +kernel

theorem rowEval9223 (x : Key → ℝ) : Integer.Sparse.eval row9223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9223, Integer.Sparse.eval_collectBalanced, rawRowCheck9223]

def rawRow9224 : Integer.Sparse Key := [(key2449, -6), (key2453, -6), (key2514, -6), (key2453, -6), (key2449, 2), (key2453, 2), (key2514, 2), (key2354, 2), (key2358, 2), (key2449, 2), (key2529, 2), (key2514, 2), (key2559, 2), (key2358, 2), (key2453, 2), (key2529, 2)]

theorem rawRowCheck9224 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form4 = rawRow9224 := by decide +kernel

def row9224 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9224 : row9224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9224 := by decide +kernel

theorem rowEval9224 (x : Key → ℝ) : Integer.Sparse.eval row9224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9224, Integer.Sparse.eval_collectBalanced, rawRowCheck9224]

def rawRow9225 : Integer.Sparse Key := [(key2453, -6), (key2449, -6), (key2514, -6), (key2453, -6), (key2453, 2), (key2449, 2), (key2514, 2), (key2358, 2), (key2354, 2), (key2529, 2), (key2449, 2), (key2559, 2), (key2514, 2), (key2358, 2), (key2529, 2), (key2453, 2)]

theorem rawRowCheck9225 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form4 = rawRow9225 := by decide +kernel

def row9225 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9225 : row9225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9225 := by decide +kernel

theorem rowEval9225 (x : Key → ℝ) : Integer.Sparse.eval row9225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9225, Integer.Sparse.eval_collectBalanced, rawRowCheck9225]

def rawRow9226 : Integer.Sparse Key := [(key2449, -6), (key2514, -6), (key2453, -6), (key2453, -6), (key2449, 2), (key2514, 2), (key2453, 2), (key2449, 2), (key2514, 2), (key2354, 2), (key2559, 2), (key2358, 2), (key2529, 2), (key2453, 2), (key2358, 2), (key2529, 2)]

theorem rawRowCheck9226 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form4 = rawRow9226 := by decide +kernel

def row9226 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9226 : row9226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9226 := by decide +kernel

theorem rowEval9226 (x : Key → ℝ) : Integer.Sparse.eval row9226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9226, Integer.Sparse.eval_collectBalanced, rawRowCheck9226]

def rawRow9227 : Integer.Sparse Key := [(key2514, -6), (key2449, -6), (key2453, -6), (key2453, -6), (key2514, 2), (key2449, 2), (key2453, 2), (key2514, 2), (key2449, 2), (key2559, 2), (key2354, 2), (key2529, 2), (key2358, 2), (key2453, 2), (key2529, 2), (key2358, 2)]

theorem rawRowCheck9227 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form4 = rawRow9227 := by decide +kernel

def row9227 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9227 : row9227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9227 := by decide +kernel

theorem rowEval9227 (x : Key → ℝ) : Integer.Sparse.eval row9227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9227, Integer.Sparse.eval_collectBalanced, rawRowCheck9227]

def rawRow9228 : Integer.Sparse Key := [(key2453, -6), (key2514, -6), (key2449, -6), (key2453, -6), (key2453, 2), (key2514, 2), (key2449, 2), (key2529, 2), (key2559, 2), (key2358, 2), (key2514, 2), (key2354, 2), (key2449, 2), (key2529, 2), (key2358, 2), (key2453, 2)]

theorem rawRowCheck9228 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form4 = rawRow9228 := by decide +kernel

def row9228 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9228 : row9228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9228 := by decide +kernel

theorem rowEval9228 (x : Key → ℝ) : Integer.Sparse.eval row9228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9228, Integer.Sparse.eval_collectBalanced, rawRowCheck9228]

def rawRow9229 : Integer.Sparse Key := [(key2514, -6), (key2453, -6), (key2449, -6), (key2453, -6), (key2514, 2), (key2453, 2), (key2449, 2), (key2559, 2), (key2529, 2), (key2514, 2), (key2358, 2), (key2449, 2), (key2354, 2), (key2529, 2), (key2453, 2), (key2358, 2)]

theorem rawRowCheck9229 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form4 = rawRow9229 := by decide +kernel

def row9229 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9229 : row9229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9229 := by decide +kernel

theorem rowEval9229 (x : Key → ℝ) : Integer.Sparse.eval row9229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9229, Integer.Sparse.eval_collectBalanced, rawRowCheck9229]

def rawRow9230 : Integer.Sparse Key := [(key2453, -6), (key2453, -6), (key2514, -6), (key2449, -6), (key2529, 2), (key2529, 2), (key2559, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2354, 2), (key2449, 2), (key2449, 2)]

theorem rawRowCheck9230 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form4 = rawRow9230 := by decide +kernel

def row9230 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9230 : row9230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9230 := by decide +kernel

theorem rowEval9230 (x : Key → ℝ) : Integer.Sparse.eval row9230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9230, Integer.Sparse.eval_collectBalanced, rawRowCheck9230]

def rawRow9231 : Integer.Sparse Key := [(key2453, -6), (key2514, -6), (key2453, -6), (key2449, -6), (key2529, 2), (key2559, 2), (key2529, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2449, 2), (key2354, 2), (key2449, 2)]

theorem rawRowCheck9231 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form4 = rawRow9231 := by decide +kernel

def row9231 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9231 : row9231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9231 := by decide +kernel

theorem rowEval9231 (x : Key → ℝ) : Integer.Sparse.eval row9231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9231, Integer.Sparse.eval_collectBalanced, rawRowCheck9231]

def rawRow9232 : Integer.Sparse Key := [(key2514, -6), (key2453, -6), (key2453, -6), (key2449, -6), (key2559, 2), (key2529, 2), (key2529, 2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2449, 2), (key2449, 2), (key2354, 2)]

theorem rawRowCheck9232 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form4 = rawRow9232 := by decide +kernel

def row9232 : Integer.Sparse Key := [(key2354, 2), (key2358, 4), (key2449, -2), (key2453, -8), (key2514, -2), (key2529, 4), (key2559, 2)]

theorem rowCheck9232 : row9232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9232 := by decide +kernel

theorem rowEval9232 (x : Key → ℝ) : Integer.Sparse.eval row9232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form4) x := by
  rw [rowCheck9232, Integer.Sparse.eval_collectBalanced, rawRowCheck9232]

def rawRow9233 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2840, -2), (key2844, -2), (key2840, -2), (key2967, -2), (key2844, -2), (key2967, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2909, 1), (key2988, 1)]

theorem rawRowCheck9233 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form5 = rawRow9233 := by decide +kernel

def row9233 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9233 : row9233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9233 := by decide +kernel

theorem rowEval9233 (x : Key → ℝ) : Integer.Sparse.eval row9233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9233, Integer.Sparse.eval_collectBalanced, rawRowCheck9233]

def rawRow9234 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2844, -2), (key2840, -2), (key2967, -2), (key2840, -2), (key2967, -2), (key2844, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2875, 1), (key2988, 1), (key2909, 1)]

theorem rawRowCheck9234 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form5 = rawRow9234 := by decide +kernel

def row9234 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9234 : row9234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9234 := by decide +kernel

theorem rowEval9234 (x : Key → ℝ) : Integer.Sparse.eval row9234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9234, Integer.Sparse.eval_collectBalanced, rawRowCheck9234]

def rawRow9235 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2967, -2), (key2967, -2), (key2844, -2), (key2844, -2), (key2840, -2), (key2840, -2), (key2988, -2), (key2875, -2), (key2875, -2), (key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2988, 1), (key2988, 1), (key2909, 1), (key2909, 1), (key2875, 1), (key2875, 1)]

theorem rawRowCheck9235 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form5 = rawRow9235 := by decide +kernel

def row9235 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9235 : row9235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9235 := by decide +kernel

theorem rowEval9235 (x : Key → ℝ) : Integer.Sparse.eval row9235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9235, Integer.Sparse.eval_collectBalanced, rawRowCheck9235]

def rawRow9236 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2875, -2), (key2584, -2), (key2588, -2), (key2840, -2), (key2967, -2), (key2875, -2), (key2988, -2), (key2588, -2), (key2844, -2), (key2967, -2), (key2763, 1), (key2767, 1), (key2840, 1), (key2888, 1), (key2875, 1), (key2909, 1), (key2584, 1), (key2588, 1), (key2840, 1), (key2967, 1), (key2875, 1), (key2988, 1), (key2584, 1), (key2599, 1), (key2763, 1), (key2930, 1), (key2909, 1), (key2988, 1), (key2588, 1), (key2599, 1), (key2767, 1), (key2930, 1), (key2888, 1), (key2967, 1)]

theorem rawRowCheck9236 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form5 = rawRow9236 := by decide +kernel

def row9236 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9236 : row9236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9236 := by decide +kernel

theorem rowEval9236 (x : Key → ℝ) : Integer.Sparse.eval row9236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9236, Integer.Sparse.eval_collectBalanced, rawRowCheck9236]

def rawRow9237 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2875, -2), (key2588, -2), (key2584, -2), (key2967, -2), (key2840, -2), (key2988, -2), (key2875, -2), (key2588, -2), (key2967, -2), (key2844, -2), (key2767, 1), (key2763, 1), (key2888, 1), (key2840, 1), (key2909, 1), (key2875, 1), (key2588, 1), (key2584, 1), (key2967, 1), (key2840, 1), (key2988, 1), (key2875, 1), (key2599, 1), (key2584, 1), (key2930, 1), (key2763, 1), (key2988, 1), (key2909, 1), (key2599, 1), (key2588, 1), (key2930, 1), (key2767, 1), (key2967, 1), (key2888, 1)]

theorem rawRowCheck9237 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form5 = rawRow9237 := by decide +kernel

def row9237 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9237 : row9237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9237 := by decide +kernel

theorem rowEval9237 (x : Key → ℝ) : Integer.Sparse.eval row9237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9237, Integer.Sparse.eval_collectBalanced, rawRowCheck9237]

def rawRow9238 : Integer.Sparse Key := [(key2840, -2), (key2875, -2), (key2844, -2), (key2840, -2), (key2875, -2), (key2584, -2), (key2988, -2), (key2588, -2), (key2967, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2840, 1), (key2875, 1), (key2763, 1), (key2909, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2875, 1), (key2584, 1), (key2988, 1), (key2588, 1), (key2967, 1), (key2763, 1), (key2909, 1), (key2584, 1), (key2988, 1), (key2599, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2588, 1), (key2967, 1), (key2599, 1), (key2930, 1)]

theorem rawRowCheck9238 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form5 = rawRow9238 := by decide +kernel

def row9238 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9238 : row9238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9238 := by decide +kernel

theorem rowEval9238 (x : Key → ℝ) : Integer.Sparse.eval row9238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form5) x := by
  rw [rowCheck9238, Integer.Sparse.eval_collectBalanced, rawRowCheck9238]

def rawRow9239 : Integer.Sparse Key := [(key2875, -2), (key2840, -2), (key2844, -2), (key2875, -2), (key2840, -2), (key2988, -2), (key2584, -2), (key2967, -2), (key2588, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2875, 1), (key2840, 1), (key2909, 1), (key2763, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2840, 1), (key2988, 1), (key2584, 1), (key2967, 1), (key2588, 1), (key2909, 1), (key2763, 1), (key2988, 1), (key2584, 1), (key2930, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2967, 1), (key2588, 1), (key2930, 1), (key2599, 1)]

theorem rawRowCheck9239 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form5 = rawRow9239 := by decide +kernel

def row9239 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9239 : row9239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9239 := by decide +kernel

theorem rowEval9239 (x : Key → ℝ) : Integer.Sparse.eval row9239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck9239, Integer.Sparse.eval_collectBalanced, rawRowCheck9239]

def rawRow9240 : Integer.Sparse Key := [(key2844, -2), (key2875, -2), (key2840, -2), (key2967, -2), (key2988, -2), (key2588, -2), (key2875, -2), (key2584, -2), (key2840, -2), (key2967, -2), (key2588, -2), (key2844, -2), (key2888, 1), (key2909, 1), (key2767, 1), (key2875, 1), (key2763, 1), (key2840, 1), (key2967, 1), (key2988, 1), (key2588, 1), (key2875, 1), (key2584, 1), (key2840, 1), (key2930, 1), (key2988, 1), (key2599, 1), (key2909, 1), (key2584, 1), (key2763, 1), (key2930, 1), (key2967, 1), (key2599, 1), (key2888, 1), (key2588, 1), (key2767, 1)]

theorem rawRowCheck9240 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form5 = rawRow9240 := by decide +kernel

def row9240 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9240 : row9240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9240 := by decide +kernel

theorem rowEval9240 (x : Key → ℝ) : Integer.Sparse.eval row9240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9240, Integer.Sparse.eval_collectBalanced, rawRowCheck9240]

def rawRow9241 : Integer.Sparse Key := [(key2875, -2), (key2844, -2), (key2840, -2), (key2988, -2), (key2967, -2), (key2875, -2), (key2588, -2), (key2840, -2), (key2584, -2), (key2967, -2), (key2844, -2), (key2588, -2), (key2909, 1), (key2888, 1), (key2875, 1), (key2767, 1), (key2840, 1), (key2763, 1), (key2988, 1), (key2967, 1), (key2875, 1), (key2588, 1), (key2840, 1), (key2584, 1), (key2988, 1), (key2930, 1), (key2909, 1), (key2599, 1), (key2763, 1), (key2584, 1), (key2967, 1), (key2930, 1), (key2888, 1), (key2599, 1), (key2767, 1), (key2588, 1)]

theorem rawRowCheck9241 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form5 = rawRow9241 := by decide +kernel

def row9241 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9241 : row9241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9241 := by decide +kernel

theorem rowEval9241 (x : Key → ℝ) : Integer.Sparse.eval row9241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck9241, Integer.Sparse.eval_collectBalanced, rawRowCheck9241]

def rawRow9242 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2588, -2), (key2588, -2), (key2844, -2), (key2844, -2), (key2875, -2), (key2875, -2), (key2584, -2), (key2840, -2), (key2840, -2), (key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2584, 1), (key2584, 1), (key2763, 1), (key2763, 1), (key2840, 1), (key2840, 1)]

theorem rawRowCheck9242 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form5 = rawRow9242 := by decide +kernel

def row9242 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9242 : row9242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9242 := by decide +kernel

theorem rowEval9242 (x : Key → ℝ) : Integer.Sparse.eval row9242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9242, Integer.Sparse.eval_collectBalanced, rawRowCheck9242]

def rawRow9243 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2844, -2), (key2875, -2), (key2588, -2), (key2875, -2), (key2588, -2), (key2844, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2840, 1), (key2584, 1), (key2763, 1)]

theorem rawRowCheck9243 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form5 = rawRow9243 := by decide +kernel

def row9243 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9243 : row9243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9243 := by decide +kernel

theorem rowEval9243 (x : Key → ℝ) : Integer.Sparse.eval row9243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck9243, Integer.Sparse.eval_collectBalanced, rawRowCheck9243]

def rawRow9244 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2875, -2), (key2844, -2), (key2875, -2), (key2588, -2), (key2844, -2), (key2588, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2763, 1), (key2584, 1)]

theorem rawRowCheck9244 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form5 = rawRow9244 := by decide +kernel

def row9244 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, 2), (key2767, 2), (key2840, -2), (key2844, -4), (key2875, -2), (key2888, 2), (key2909, 2), (key2930, 2), (key2967, -2)]

theorem rowCheck9244 : row9244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9244 := by decide +kernel

theorem rowEval9244 (x : Key → ℝ) : Integer.Sparse.eval row9244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form5) x := by
  rw [rowCheck9244, Integer.Sparse.eval_collectBalanced, rawRowCheck9244]

def rawRow9245 : Integer.Sparse Key := [(key2447, -24), (key2352, 6), (key2447, 6), (key2447, 6), (key2511, 6)]

theorem rawRowCheck9245 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form6 = rawRow9245 := by decide +kernel

def row9245 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9245 : row9245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9245 := by decide +kernel

theorem rowEval9245 (x : Key → ℝ) : Integer.Sparse.eval row9245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9245, Integer.Sparse.eval_collectBalanced, rawRowCheck9245]

def rawRow9246 : Integer.Sparse Key := [(key2447, -24), (key2352, 6), (key2447, 6), (key2511, 6), (key2447, 6)]

theorem rawRowCheck9246 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form6 = rawRow9246 := by decide +kernel

def row9246 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9246 : row9246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9246 := by decide +kernel

theorem rowEval9246 (x : Key → ℝ) : Integer.Sparse.eval row9246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9246, Integer.Sparse.eval_collectBalanced, rawRowCheck9246]

def rawRow9247 : Integer.Sparse Key := [(key2447, -24), (key2352, 6), (key2511, 6), (key2447, 6), (key2447, 6)]

theorem rawRowCheck9247 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form6 = rawRow9247 := by decide +kernel

def row9247 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9247 : row9247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9247 := by decide +kernel

theorem rowEval9247 (x : Key → ℝ) : Integer.Sparse.eval row9247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9247, Integer.Sparse.eval_collectBalanced, rawRowCheck9247]

def rawRow9248 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2352, 6), (key2447, 6), (key2511, 6)]

theorem rawRowCheck9248 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form6 = rawRow9248 := by decide +kernel

def row9248 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9248 : row9248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9248 := by decide +kernel

theorem rowEval9248 (x : Key → ℝ) : Integer.Sparse.eval row9248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9248, Integer.Sparse.eval_collectBalanced, rawRowCheck9248]

def rawRow9249 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2352, 6), (key2511, 6), (key2447, 6)]

theorem rawRowCheck9249 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form6 = rawRow9249 := by decide +kernel

def row9249 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9249 : row9249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9249 := by decide +kernel

theorem rowEval9249 (x : Key → ℝ) : Integer.Sparse.eval row9249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9249, Integer.Sparse.eval_collectBalanced, rawRowCheck9249]

def rawRow9250 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2447, 6), (key2352, 6), (key2511, 6)]

theorem rawRowCheck9250 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form6 = rawRow9250 := by decide +kernel

def row9250 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9250 : row9250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9250 := by decide +kernel

theorem rowEval9250 (x : Key → ℝ) : Integer.Sparse.eval row9250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form6) x := by
  rw [rowCheck9250, Integer.Sparse.eval_collectBalanced, rawRowCheck9250]

def rawRow9251 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2447, 6), (key2511, 6), (key2352, 6)]

theorem rawRowCheck9251 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form6 = rawRow9251 := by decide +kernel

def row9251 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9251 : row9251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9251 := by decide +kernel

theorem rowEval9251 (x : Key → ℝ) : Integer.Sparse.eval row9251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9251, Integer.Sparse.eval_collectBalanced, rawRowCheck9251]

def rawRow9252 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2511, 6), (key2352, 6), (key2447, 6)]

theorem rawRowCheck9252 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form6 = rawRow9252 := by decide +kernel

def row9252 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9252 : row9252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9252 := by decide +kernel

theorem rowEval9252 (x : Key → ℝ) : Integer.Sparse.eval row9252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9252, Integer.Sparse.eval_collectBalanced, rawRowCheck9252]

def rawRow9253 : Integer.Sparse Key := [(key2447, -24), (key2447, 6), (key2511, 6), (key2447, 6), (key2352, 6)]

theorem rawRowCheck9253 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form6 = rawRow9253 := by decide +kernel

def row9253 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9253 : row9253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9253 := by decide +kernel

theorem rowEval9253 (x : Key → ℝ) : Integer.Sparse.eval row9253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9253, Integer.Sparse.eval_collectBalanced, rawRowCheck9253]

def rawRow9254 : Integer.Sparse Key := [(key2447, -24), (key2511, 6), (key2352, 6), (key2447, 6), (key2447, 6)]

theorem rawRowCheck9254 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form6 = rawRow9254 := by decide +kernel

def row9254 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9254 : row9254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9254 := by decide +kernel

theorem rowEval9254 (x : Key → ℝ) : Integer.Sparse.eval row9254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9254, Integer.Sparse.eval_collectBalanced, rawRowCheck9254]

def rawRow9255 : Integer.Sparse Key := [(key2447, -24), (key2511, 6), (key2447, 6), (key2352, 6), (key2447, 6)]

theorem rawRowCheck9255 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form6 = rawRow9255 := by decide +kernel

def row9255 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9255 : row9255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9255 := by decide +kernel

theorem rowEval9255 (x : Key → ℝ) : Integer.Sparse.eval row9255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck9255, Integer.Sparse.eval_collectBalanced, rawRowCheck9255]

def rawRow9256 : Integer.Sparse Key := [(key2447, -24), (key2511, 6), (key2447, 6), (key2447, 6), (key2352, 6)]

theorem rawRowCheck9256 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form6 = rawRow9256 := by decide +kernel

def row9256 : Integer.Sparse Key := [(key2352, 6), (key2447, -12), (key2511, 6)]

theorem rowCheck9256 : row9256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9256 := by decide +kernel

theorem rowEval9256 (x : Key → ℝ) : Integer.Sparse.eval row9256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form6) x := by
  rw [rowCheck9256, Integer.Sparse.eval_collectBalanced, rawRowCheck9256]

def rawRow9257 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2840, -2), (key2844, -2), (key2840, -2), (key2888, -2), (key2844, -2), (key2888, -2), (key2875, -2), (key2875, -2), (key2909, -2), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2988, 2)]

theorem rawRowCheck9257 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form7 = rawRow9257 := by decide +kernel

def row9257 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9257 : row9257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9257 := by decide +kernel

theorem rowEval9257 (x : Key → ℝ) : Integer.Sparse.eval row9257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9257, Integer.Sparse.eval_collectBalanced, rawRowCheck9257]

def rawRow9258 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2844, -2), (key2840, -2), (key2888, -2), (key2840, -2), (key2888, -2), (key2844, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2988, 2), (key2875, 2)]

theorem rawRowCheck9258 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form7 = rawRow9258 := by decide +kernel

def row9258 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9258 : row9258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9258 := by decide +kernel

theorem rowEval9258 (x : Key → ℝ) : Integer.Sparse.eval row9258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9258, Integer.Sparse.eval_collectBalanced, rawRowCheck9258]

def rawRow9259 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2888, -2), (key2888, -2), (key2844, -2), (key2844, -2), (key2840, -2), (key2840, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2875, 2)]

theorem rawRowCheck9259 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form7 = rawRow9259 := by decide +kernel

def row9259 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9259 : row9259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9259 := by decide +kernel

theorem rowEval9259 (x : Key → ℝ) : Integer.Sparse.eval row9259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9259, Integer.Sparse.eval_collectBalanced, rawRowCheck9259]

def rawRow9260 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2875, -2), (key2763, -2), (key2767, -2), (key2840, -2), (key2888, -2), (key2875, -2), (key2909, -2), (key2767, -2), (key2844, -2), (key2888, -2), (key2840, 2), (key2844, 2), (key2875, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2588, 2), (key2844, 2), (key2967, 2)]

theorem rawRowCheck9260 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form7 = rawRow9260 := by decide +kernel

def row9260 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9260 : row9260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9260 := by decide +kernel

theorem rowEval9260 (x : Key → ℝ) : Integer.Sparse.eval row9260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9260, Integer.Sparse.eval_collectBalanced, rawRowCheck9260]

def rawRow9261 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2875, -2), (key2767, -2), (key2763, -2), (key2888, -2), (key2840, -2), (key2909, -2), (key2875, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2844, 2), (key2840, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2967, 2), (key2844, 2)]

theorem rawRowCheck9261 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form7 = rawRow9261 := by decide +kernel

def row9261 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9261 : row9261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9261 := by decide +kernel

theorem rowEval9261 (x : Key → ℝ) : Integer.Sparse.eval row9261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9261, Integer.Sparse.eval_collectBalanced, rawRowCheck9261]

def rawRow9262 : Integer.Sparse Key := [(key2840, -2), (key2875, -2), (key2844, -2), (key2840, -2), (key2875, -2), (key2763, -2), (key2909, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2767, -2), (key2888, -2), (key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2)]

theorem rawRowCheck9262 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form7 = rawRow9262 := by decide +kernel

def row9262 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9262 : row9262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9262 := by decide +kernel

theorem rowEval9262 (x : Key → ℝ) : Integer.Sparse.eval row9262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form7) x := by
  rw [rowCheck9262, Integer.Sparse.eval_collectBalanced, rawRowCheck9262]

def rawRow9263 : Integer.Sparse Key := [(key2875, -2), (key2840, -2), (key2844, -2), (key2875, -2), (key2840, -2), (key2909, -2), (key2763, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2888, -2), (key2767, -2), (key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2)]

theorem rawRowCheck9263 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form7 = rawRow9263 := by decide +kernel

def row9263 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9263 : row9263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9263 := by decide +kernel

theorem rowEval9263 (x : Key → ℝ) : Integer.Sparse.eval row9263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9263, Integer.Sparse.eval_collectBalanced, rawRowCheck9263]

def rawRow9264 : Integer.Sparse Key := [(key2844, -2), (key2875, -2), (key2840, -2), (key2888, -2), (key2909, -2), (key2767, -2), (key2875, -2), (key2763, -2), (key2840, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2844, 2), (key2875, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2588, 2), (key2844, 2)]

theorem rawRowCheck9264 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form7 = rawRow9264 := by decide +kernel

def row9264 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9264 : row9264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9264 := by decide +kernel

theorem rowEval9264 (x : Key → ℝ) : Integer.Sparse.eval row9264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9264, Integer.Sparse.eval_collectBalanced, rawRowCheck9264]

def rawRow9265 : Integer.Sparse Key := [(key2875, -2), (key2844, -2), (key2840, -2), (key2909, -2), (key2888, -2), (key2875, -2), (key2767, -2), (key2840, -2), (key2763, -2), (key2888, -2), (key2844, -2), (key2767, -2), (key2875, 2), (key2844, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2967, 2), (key2844, 2), (key2588, 2)]

theorem rawRowCheck9265 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form7 = rawRow9265 := by decide +kernel

def row9265 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9265 : row9265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9265 := by decide +kernel

theorem rowEval9265 (x : Key → ℝ) : Integer.Sparse.eval row9265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9265, Integer.Sparse.eval_collectBalanced, rawRowCheck9265]

def rawRow9266 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2767, -2), (key2767, -2), (key2844, -2), (key2844, -2), (key2875, -2), (key2875, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2840, 2)]

theorem rawRowCheck9266 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form7 = rawRow9266 := by decide +kernel

def row9266 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9266 : row9266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9266 := by decide +kernel

theorem rowEval9266 (x : Key → ℝ) : Integer.Sparse.eval row9266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9266, Integer.Sparse.eval_collectBalanced, rawRowCheck9266]

def rawRow9267 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2844, -2), (key2875, -2), (key2767, -2), (key2875, -2), (key2767, -2), (key2844, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2584, 2), (key2840, 2)]

theorem rawRowCheck9267 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form7 = rawRow9267 := by decide +kernel

def row9267 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9267 : row9267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9267 := by decide +kernel

theorem rowEval9267 (x : Key → ℝ) : Integer.Sparse.eval row9267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck9267, Integer.Sparse.eval_collectBalanced, rawRowCheck9267]

def rawRow9268 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2875, -2), (key2844, -2), (key2875, -2), (key2767, -2), (key2844, -2), (key2767, -2), (key2840, -2), (key2840, -2), (key2763, -2), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2584, 2)]

theorem rawRowCheck9268 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form7 = rawRow9268 := by decide +kernel

def row9268 : Integer.Sparse Key := [(key2584, 2), (key2588, 4), (key2763, -2), (key2767, -4), (key2888, -4), (key2909, -2), (key2967, 4), (key2988, 2)]

theorem rowCheck9268 : row9268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9268 := by decide +kernel

theorem rowEval9268 (x : Key → ℝ) : Integer.Sparse.eval row9268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form7) x := by
  rw [rowCheck9268, Integer.Sparse.eval_collectBalanced, rawRowCheck9268]

def rawRow9269 : Integer.Sparse Key := [(key1252, -2), (key1257, -2), (key1257, -2), (key1605, -2), (key1610, -2), (key1605, -2), (key1807, -2), (key1610, -2), (key1807, -2), (key1638, -2), (key1638, -2), (key1830, -2), (key1252, 1), (key1257, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1266, 1), (key1527, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1766, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1807, 1), (key1638, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1672, 1), (key1830, 1)]

theorem rawRowCheck9269 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form8 = rawRow9269 := by decide +kernel

def row9269 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9269 : row9269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9269 := by decide +kernel

theorem rowEval9269 (x : Key → ℝ) : Integer.Sparse.eval row9269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9269, Integer.Sparse.eval_collectBalanced, rawRowCheck9269]

def rawRow9270 : Integer.Sparse Key := [(key1257, -2), (key1252, -2), (key1257, -2), (key1610, -2), (key1605, -2), (key1807, -2), (key1605, -2), (key1807, -2), (key1610, -2), (key1638, -2), (key1830, -2), (key1638, -2), (key1257, 1), (key1252, 1), (key1266, 1), (key1252, 1), (key1266, 1), (key1257, 1), (key1532, 1), (key1527, 1), (key1766, 1), (key1527, 1), (key1766, 1), (key1532, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1672, 1), (key1638, 1), (key1830, 1), (key1638, 1), (key1830, 1), (key1672, 1)]

theorem rawRowCheck9270 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form8 = rawRow9270 := by decide +kernel

def row9270 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9270 : row9270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9270 := by decide +kernel

theorem rowEval9270 (x : Key → ℝ) : Integer.Sparse.eval row9270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9270, Integer.Sparse.eval_collectBalanced, rawRowCheck9270]

def rawRow9271 : Integer.Sparse Key := [(key1257, -2), (key1257, -2), (key1252, -2), (key1807, -2), (key1807, -2), (key1610, -2), (key1610, -2), (key1605, -2), (key1605, -2), (key1830, -2), (key1638, -2), (key1638, -2), (key1266, 1), (key1266, 1), (key1257, 1), (key1257, 1), (key1252, 1), (key1252, 1), (key1766, 1), (key1766, 1), (key1532, 1), (key1532, 1), (key1527, 1), (key1527, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1605, 1), (key1605, 1), (key1830, 1), (key1830, 1), (key1672, 1), (key1672, 1), (key1638, 1), (key1638, 1)]

theorem rawRowCheck9271 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form8 = rawRow9271 := by decide +kernel

def row9271 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9271 : row9271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9271 := by decide +kernel

theorem rowEval9271 (x : Key → ℝ) : Integer.Sparse.eval row9271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9271, Integer.Sparse.eval_collectBalanced, rawRowCheck9271]

def rawRow9272 : Integer.Sparse Key := [(key1605, -2), (key1610, -2), (key1638, -2), (key1252, -2), (key1257, -2), (key1605, -2), (key1807, -2), (key1638, -2), (key1830, -2), (key1257, -2), (key1610, -2), (key1807, -2), (key1527, 1), (key1532, 1), (key1605, 1), (key1649, 1), (key1638, 1), (key1672, 1), (key1252, 1), (key1257, 1), (key1605, 1), (key1807, 1), (key1638, 1), (key1830, 1), (key1252, 1), (key1266, 1), (key1527, 1), (key1766, 1), (key1672, 1), (key1830, 1), (key1257, 1), (key1266, 1), (key1532, 1), (key1766, 1), (key1649, 1), (key1807, 1)]

theorem rawRowCheck9272 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form8 = rawRow9272 := by decide +kernel

def row9272 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9272 : row9272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9272 := by decide +kernel

theorem rowEval9272 (x : Key → ℝ) : Integer.Sparse.eval row9272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9272, Integer.Sparse.eval_collectBalanced, rawRowCheck9272]

def rawRow9273 : Integer.Sparse Key := [(key1610, -2), (key1605, -2), (key1638, -2), (key1257, -2), (key1252, -2), (key1807, -2), (key1605, -2), (key1830, -2), (key1638, -2), (key1257, -2), (key1807, -2), (key1610, -2), (key1532, 1), (key1527, 1), (key1649, 1), (key1605, 1), (key1672, 1), (key1638, 1), (key1257, 1), (key1252, 1), (key1807, 1), (key1605, 1), (key1830, 1), (key1638, 1), (key1266, 1), (key1252, 1), (key1766, 1), (key1527, 1), (key1830, 1), (key1672, 1), (key1266, 1), (key1257, 1), (key1766, 1), (key1532, 1), (key1807, 1), (key1649, 1)]

theorem rawRowCheck9273 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form8 = rawRow9273 := by decide +kernel

def row9273 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9273 : row9273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9273 := by decide +kernel

theorem rowEval9273 (x : Key → ℝ) : Integer.Sparse.eval row9273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9273, Integer.Sparse.eval_collectBalanced, rawRowCheck9273]

def rawRow9274 : Integer.Sparse Key := [(key1605, -2), (key1638, -2), (key1610, -2), (key1605, -2), (key1638, -2), (key1252, -2), (key1830, -2), (key1257, -2), (key1807, -2), (key1610, -2), (key1257, -2), (key1807, -2), (key1605, 1), (key1638, 1), (key1527, 1), (key1672, 1), (key1532, 1), (key1649, 1), (key1605, 1), (key1638, 1), (key1252, 1), (key1830, 1), (key1257, 1), (key1807, 1), (key1527, 1), (key1672, 1), (key1252, 1), (key1830, 1), (key1266, 1), (key1766, 1), (key1532, 1), (key1649, 1), (key1257, 1), (key1807, 1), (key1266, 1), (key1766, 1)]

theorem rawRowCheck9274 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form8 = rawRow9274 := by decide +kernel

def row9274 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9274 : row9274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9274 := by decide +kernel

theorem rowEval9274 (x : Key → ℝ) : Integer.Sparse.eval row9274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form8) x := by
  rw [rowCheck9274, Integer.Sparse.eval_collectBalanced, rawRowCheck9274]

def rawRow9275 : Integer.Sparse Key := [(key1638, -2), (key1605, -2), (key1610, -2), (key1638, -2), (key1605, -2), (key1830, -2), (key1252, -2), (key1807, -2), (key1257, -2), (key1610, -2), (key1807, -2), (key1257, -2), (key1638, 1), (key1605, 1), (key1672, 1), (key1527, 1), (key1649, 1), (key1532, 1), (key1638, 1), (key1605, 1), (key1830, 1), (key1252, 1), (key1807, 1), (key1257, 1), (key1672, 1), (key1527, 1), (key1830, 1), (key1252, 1), (key1766, 1), (key1266, 1), (key1649, 1), (key1532, 1), (key1807, 1), (key1257, 1), (key1766, 1), (key1266, 1)]

theorem rawRowCheck9275 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form8 = rawRow9275 := by decide +kernel

def row9275 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9275 : row9275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9275 := by decide +kernel

theorem rowEval9275 (x : Key → ℝ) : Integer.Sparse.eval row9275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck9275, Integer.Sparse.eval_collectBalanced, rawRowCheck9275]

def rawRow9276 : Integer.Sparse Key := [(key1610, -2), (key1638, -2), (key1605, -2), (key1807, -2), (key1830, -2), (key1257, -2), (key1638, -2), (key1252, -2), (key1605, -2), (key1807, -2), (key1257, -2), (key1610, -2), (key1649, 1), (key1672, 1), (key1532, 1), (key1638, 1), (key1527, 1), (key1605, 1), (key1807, 1), (key1830, 1), (key1257, 1), (key1638, 1), (key1252, 1), (key1605, 1), (key1766, 1), (key1830, 1), (key1266, 1), (key1672, 1), (key1252, 1), (key1527, 1), (key1766, 1), (key1807, 1), (key1266, 1), (key1649, 1), (key1257, 1), (key1532, 1)]

theorem rawRowCheck9276 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form8 = rawRow9276 := by decide +kernel

def row9276 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9276 : row9276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9276 := by decide +kernel

theorem rowEval9276 (x : Key → ℝ) : Integer.Sparse.eval row9276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9276, Integer.Sparse.eval_collectBalanced, rawRowCheck9276]

def rawRow9277 : Integer.Sparse Key := [(key1638, -2), (key1610, -2), (key1605, -2), (key1830, -2), (key1807, -2), (key1638, -2), (key1257, -2), (key1605, -2), (key1252, -2), (key1807, -2), (key1610, -2), (key1257, -2), (key1672, 1), (key1649, 1), (key1638, 1), (key1532, 1), (key1605, 1), (key1527, 1), (key1830, 1), (key1807, 1), (key1638, 1), (key1257, 1), (key1605, 1), (key1252, 1), (key1830, 1), (key1766, 1), (key1672, 1), (key1266, 1), (key1527, 1), (key1252, 1), (key1807, 1), (key1766, 1), (key1649, 1), (key1266, 1), (key1532, 1), (key1257, 1)]

theorem rawRowCheck9277 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form8 = rawRow9277 := by decide +kernel

def row9277 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9277 : row9277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9277 := by decide +kernel

theorem rowEval9277 (x : Key → ℝ) : Integer.Sparse.eval row9277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck9277, Integer.Sparse.eval_collectBalanced, rawRowCheck9277]

def rawRow9278 : Integer.Sparse Key := [(key1807, -2), (key1807, -2), (key1830, -2), (key1257, -2), (key1257, -2), (key1610, -2), (key1610, -2), (key1638, -2), (key1638, -2), (key1252, -2), (key1605, -2), (key1605, -2), (key1766, 1), (key1766, 1), (key1807, 1), (key1807, 1), (key1830, 1), (key1830, 1), (key1266, 1), (key1266, 1), (key1649, 1), (key1649, 1), (key1672, 1), (key1672, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1638, 1), (key1638, 1), (key1252, 1), (key1252, 1), (key1527, 1), (key1527, 1), (key1605, 1), (key1605, 1)]

theorem rawRowCheck9278 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form8 = rawRow9278 := by decide +kernel

def row9278 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9278 : row9278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9278 := by decide +kernel

theorem rowEval9278 (x : Key → ℝ) : Integer.Sparse.eval row9278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9278, Integer.Sparse.eval_collectBalanced, rawRowCheck9278]

def rawRow9279 : Integer.Sparse Key := [(key1807, -2), (key1830, -2), (key1807, -2), (key1610, -2), (key1638, -2), (key1257, -2), (key1638, -2), (key1257, -2), (key1610, -2), (key1605, -2), (key1252, -2), (key1605, -2), (key1807, 1), (key1830, 1), (key1766, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1605, 1), (key1252, 1), (key1527, 1)]

theorem rawRowCheck9279 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form8 = rawRow9279 := by decide +kernel

def row9279 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9279 : row9279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9279 := by decide +kernel

theorem rowEval9279 (x : Key → ℝ) : Integer.Sparse.eval row9279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck9279, Integer.Sparse.eval_collectBalanced, rawRowCheck9279]

def rawRow9280 : Integer.Sparse Key := [(key1830, -2), (key1807, -2), (key1807, -2), (key1638, -2), (key1610, -2), (key1638, -2), (key1257, -2), (key1610, -2), (key1257, -2), (key1605, -2), (key1605, -2), (key1252, -2), (key1830, 1), (key1807, 1), (key1830, 1), (key1766, 1), (key1807, 1), (key1766, 1), (key1672, 1), (key1649, 1), (key1672, 1), (key1266, 1), (key1649, 1), (key1266, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1257, 1), (key1605, 1), (key1527, 1), (key1605, 1), (key1252, 1), (key1527, 1), (key1252, 1)]

theorem rawRowCheck9280 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form8 = rawRow9280 := by decide +kernel

def row9280 : Integer.Sparse Key := [(key1257, -2), (key1266, 2), (key1527, 2), (key1532, 2), (key1605, -2), (key1610, -4), (key1638, -2), (key1649, 2), (key1672, 2), (key1766, 2), (key1807, -2)]

theorem rowCheck9280 : row9280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9280 := by decide +kernel

theorem rowEval9280 (x : Key → ℝ) : Integer.Sparse.eval row9280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form8) x := by
  rw [rowCheck9280, Integer.Sparse.eval_collectBalanced, rawRowCheck9280]

def rawRow9281 : Integer.Sparse Key := [(key2584, 1), (key2588, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2599, 1), (key2763, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2930, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2909, 1), (key2988, 1), (key2588, -2), (key2588, -2), (key2599, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2844, -2), (key2888, -2), (key2844, -2), (key2967, -2), (key2888, -2), (key2967, -2)]

theorem rawRowCheck9281 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form9 = rawRow9281 := by decide +kernel

def row9281 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9281 : row9281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9281 := by decide +kernel

theorem rowEval9281 (x : Key → ℝ) : Integer.Sparse.eval row9281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9281, Integer.Sparse.eval_collectBalanced, rawRowCheck9281]

def rawRow9282 : Integer.Sparse Key := [(key2588, 1), (key2584, 1), (key2599, 1), (key2584, 1), (key2599, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2930, 1), (key2763, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2875, 1), (key2988, 1), (key2875, 1), (key2988, 1), (key2909, 1), (key2588, -2), (key2599, -2), (key2588, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2967, -2), (key2844, -2), (key2967, -2), (key2888, -2)]

theorem rawRowCheck9282 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form9 = rawRow9282 := by decide +kernel

def row9282 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9282 : row9282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9282 := by decide +kernel

theorem rowEval9282 (x : Key → ℝ) : Integer.Sparse.eval row9282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9282, Integer.Sparse.eval_collectBalanced, rawRowCheck9282]

def rawRow9283 : Integer.Sparse Key := [(key2599, 1), (key2599, 1), (key2588, 1), (key2588, 1), (key2584, 1), (key2584, 1), (key2930, 1), (key2930, 1), (key2767, 1), (key2767, 1), (key2763, 1), (key2763, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2988, 1), (key2988, 1), (key2909, 1), (key2909, 1), (key2875, 1), (key2875, 1), (key2599, -2), (key2588, -2), (key2588, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2967, -2), (key2967, -2), (key2888, -2), (key2888, -2), (key2844, -2), (key2844, -2)]

theorem rawRowCheck9283 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form9 = rawRow9283 := by decide +kernel

def row9283 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9283 : row9283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9283 := by decide +kernel

theorem rowEval9283 (x : Key → ℝ) : Integer.Sparse.eval row9283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9283, Integer.Sparse.eval_collectBalanced, rawRowCheck9283]

def rawRow9284 : Integer.Sparse Key := [(key2763, 1), (key2767, 1), (key2840, 1), (key2888, 1), (key2875, 1), (key2909, 1), (key2584, 1), (key2588, 1), (key2840, 1), (key2967, 1), (key2875, 1), (key2988, 1), (key2584, 1), (key2599, 1), (key2763, 1), (key2930, 1), (key2909, 1), (key2988, 1), (key2588, 1), (key2599, 1), (key2767, 1), (key2930, 1), (key2888, 1), (key2967, 1), (key2767, -2), (key2844, -2), (key2888, -2), (key2588, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2599, -2), (key2767, -2), (key2930, -2), (key2888, -2), (key2967, -2)]

theorem rawRowCheck9284 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form9 = rawRow9284 := by decide +kernel

def row9284 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9284 : row9284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9284 := by decide +kernel

theorem rowEval9284 (x : Key → ℝ) : Integer.Sparse.eval row9284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9284, Integer.Sparse.eval_collectBalanced, rawRowCheck9284]

def rawRow9285 : Integer.Sparse Key := [(key2767, 1), (key2763, 1), (key2888, 1), (key2840, 1), (key2909, 1), (key2875, 1), (key2588, 1), (key2584, 1), (key2967, 1), (key2840, 1), (key2988, 1), (key2875, 1), (key2599, 1), (key2584, 1), (key2930, 1), (key2763, 1), (key2988, 1), (key2909, 1), (key2599, 1), (key2588, 1), (key2930, 1), (key2767, 1), (key2967, 1), (key2888, 1), (key2767, -2), (key2888, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2844, -2), (key2599, -2), (key2588, -2), (key2930, -2), (key2767, -2), (key2967, -2), (key2888, -2)]

theorem rawRowCheck9285 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form9 = rawRow9285 := by decide +kernel

def row9285 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9285 : row9285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9285 := by decide +kernel

theorem rowEval9285 (x : Key → ℝ) : Integer.Sparse.eval row9285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9285, Integer.Sparse.eval_collectBalanced, rawRowCheck9285]

def rawRow9286 : Integer.Sparse Key := [(key2840, 1), (key2875, 1), (key2763, 1), (key2909, 1), (key2767, 1), (key2888, 1), (key2840, 1), (key2875, 1), (key2584, 1), (key2988, 1), (key2588, 1), (key2967, 1), (key2763, 1), (key2909, 1), (key2584, 1), (key2988, 1), (key2599, 1), (key2930, 1), (key2767, 1), (key2888, 1), (key2588, 1), (key2967, 1), (key2599, 1), (key2930, 1), (key2844, -2), (key2767, -2), (key2888, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2767, -2), (key2888, -2), (key2588, -2), (key2967, -2), (key2599, -2), (key2930, -2)]

theorem rawRowCheck9286 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form9 = rawRow9286 := by decide +kernel

def row9286 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9286 : row9286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9286 := by decide +kernel

theorem rowEval9286 (x : Key → ℝ) : Integer.Sparse.eval row9286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck9286, Integer.Sparse.eval_collectBalanced, rawRowCheck9286]

def rawRow9287 : Integer.Sparse Key := [(key2875, 1), (key2840, 1), (key2909, 1), (key2763, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2840, 1), (key2988, 1), (key2584, 1), (key2967, 1), (key2588, 1), (key2909, 1), (key2763, 1), (key2988, 1), (key2584, 1), (key2930, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2967, 1), (key2588, 1), (key2930, 1), (key2599, 1), (key2844, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2888, -2), (key2767, -2), (key2967, -2), (key2588, -2), (key2930, -2), (key2599, -2)]

theorem rawRowCheck9287 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form9 = rawRow9287 := by decide +kernel

def row9287 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9287 : row9287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9287 := by decide +kernel

theorem rowEval9287 (x : Key → ℝ) : Integer.Sparse.eval row9287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck9287, Integer.Sparse.eval_collectBalanced, rawRowCheck9287]

def rawRow9288 : Integer.Sparse Key := [(key2888, 1), (key2909, 1), (key2767, 1), (key2875, 1), (key2763, 1), (key2840, 1), (key2967, 1), (key2988, 1), (key2588, 1), (key2875, 1), (key2584, 1), (key2840, 1), (key2930, 1), (key2988, 1), (key2599, 1), (key2909, 1), (key2584, 1), (key2763, 1), (key2930, 1), (key2967, 1), (key2599, 1), (key2888, 1), (key2588, 1), (key2767, 1), (key2888, -2), (key2767, -2), (key2844, -2), (key2967, -2), (key2588, -2), (key2844, -2), (key2930, -2), (key2967, -2), (key2599, -2), (key2888, -2), (key2588, -2), (key2767, -2)]

theorem rawRowCheck9288 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form9 = rawRow9288 := by decide +kernel

def row9288 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9288 : row9288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9288 := by decide +kernel

theorem rowEval9288 (x : Key → ℝ) : Integer.Sparse.eval row9288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9288, Integer.Sparse.eval_collectBalanced, rawRowCheck9288]

def rawRow9289 : Integer.Sparse Key := [(key2909, 1), (key2888, 1), (key2875, 1), (key2767, 1), (key2840, 1), (key2763, 1), (key2988, 1), (key2967, 1), (key2875, 1), (key2588, 1), (key2840, 1), (key2584, 1), (key2988, 1), (key2930, 1), (key2909, 1), (key2599, 1), (key2763, 1), (key2584, 1), (key2967, 1), (key2930, 1), (key2888, 1), (key2599, 1), (key2767, 1), (key2588, 1), (key2888, -2), (key2844, -2), (key2767, -2), (key2967, -2), (key2844, -2), (key2588, -2), (key2967, -2), (key2930, -2), (key2888, -2), (key2599, -2), (key2767, -2), (key2588, -2)]

theorem rawRowCheck9289 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form9 = rawRow9289 := by decide +kernel

def row9289 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9289 : row9289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9289 := by decide +kernel

theorem rowEval9289 (x : Key → ℝ) : Integer.Sparse.eval row9289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck9289, Integer.Sparse.eval_collectBalanced, rawRowCheck9289]

def rawRow9290 : Integer.Sparse Key := [(key2930, 1), (key2930, 1), (key2967, 1), (key2967, 1), (key2988, 1), (key2988, 1), (key2599, 1), (key2599, 1), (key2888, 1), (key2888, 1), (key2909, 1), (key2909, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2584, 1), (key2584, 1), (key2763, 1), (key2763, 1), (key2840, 1), (key2840, 1), (key2930, -2), (key2967, -2), (key2967, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2588, -2), (key2588, -2), (key2767, -2), (key2767, -2), (key2844, -2), (key2844, -2)]

theorem rawRowCheck9290 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form9 = rawRow9290 := by decide +kernel

def row9290 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9290 : row9290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9290 := by decide +kernel

theorem rowEval9290 (x : Key → ℝ) : Integer.Sparse.eval row9290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9290, Integer.Sparse.eval_collectBalanced, rawRowCheck9290]

def rawRow9291 : Integer.Sparse Key := [(key2967, 1), (key2988, 1), (key2930, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2840, 1), (key2584, 1), (key2763, 1), (key2967, -2), (key2930, -2), (key2967, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2767, -2), (key2844, -2), (key2588, -2), (key2844, -2), (key2588, -2), (key2767, -2)]

theorem rawRowCheck9291 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form9 = rawRow9291 := by decide +kernel

def row9291 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9291 : row9291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9291 := by decide +kernel

theorem rowEval9291 (x : Key → ℝ) : Integer.Sparse.eval row9291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck9291, Integer.Sparse.eval_collectBalanced, rawRowCheck9291]

def rawRow9292 : Integer.Sparse Key := [(key2988, 1), (key2967, 1), (key2988, 1), (key2930, 1), (key2967, 1), (key2930, 1), (key2909, 1), (key2888, 1), (key2909, 1), (key2599, 1), (key2888, 1), (key2599, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, 1), (key2763, 1), (key2840, 1), (key2584, 1), (key2763, 1), (key2584, 1), (key2967, -2), (key2967, -2), (key2930, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2844, -2), (key2767, -2), (key2844, -2), (key2588, -2), (key2767, -2), (key2588, -2)]

theorem rawRowCheck9292 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form9 = rawRow9292 := by decide +kernel

def row9292 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, 2), (key2844, -4), (key2875, 2), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

theorem rowCheck9292 : row9292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9292 := by decide +kernel

theorem rowEval9292 (x : Key → ℝ) : Integer.Sparse.eval row9292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck9292, Integer.Sparse.eval_collectBalanced, rawRowCheck9292]

def rawRow9293 : Integer.Sparse Key := [(key1249, -6), (key1602, -6), (key1602, -6), (key1803, -6), (key1249, 2), (key1249, 2), (key1262, 2), (key1524, 2), (key1524, 2), (key1762, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1645, 2), (key1803, 2)]

theorem rawRowCheck9293 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form10 = rawRow9293 := by decide +kernel

def row9293 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9293 : row9293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9293 := by decide +kernel

theorem rowEval9293 (x : Key → ℝ) : Integer.Sparse.eval row9293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9293, Integer.Sparse.eval_collectBalanced, rawRowCheck9293]

def rawRow9294 : Integer.Sparse Key := [(key1249, -6), (key1602, -6), (key1803, -6), (key1602, -6), (key1249, 2), (key1262, 2), (key1249, 2), (key1524, 2), (key1762, 2), (key1524, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1803, 2), (key1645, 2)]

theorem rawRowCheck9294 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form10 = rawRow9294 := by decide +kernel

def row9294 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9294 : row9294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9294 := by decide +kernel

theorem rowEval9294 (x : Key → ℝ) : Integer.Sparse.eval row9294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9294, Integer.Sparse.eval_collectBalanced, rawRowCheck9294]

def rawRow9295 : Integer.Sparse Key := [(key1249, -6), (key1803, -6), (key1602, -6), (key1602, -6), (key1262, 2), (key1249, 2), (key1249, 2), (key1762, 2), (key1524, 2), (key1524, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck9295 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form10 = rawRow9295 := by decide +kernel

def row9295 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9295 : row9295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9295 := by decide +kernel

theorem rowEval9295 (x : Key → ℝ) : Integer.Sparse.eval row9295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9295, Integer.Sparse.eval_collectBalanced, rawRowCheck9295]

def rawRow9296 : Integer.Sparse Key := [(key1602, -6), (key1249, -6), (key1602, -6), (key1803, -6), (key1524, 2), (key1602, 2), (key1645, 2), (key1249, 2), (key1602, 2), (key1803, 2), (key1249, 2), (key1262, 2), (key1524, 2), (key1762, 2), (key1645, 2), (key1803, 2)]

theorem rawRowCheck9296 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form10 = rawRow9296 := by decide +kernel

def row9296 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9296 : row9296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9296 := by decide +kernel

theorem rowEval9296 (x : Key → ℝ) : Integer.Sparse.eval row9296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9296, Integer.Sparse.eval_collectBalanced, rawRowCheck9296]

def rawRow9297 : Integer.Sparse Key := [(key1602, -6), (key1249, -6), (key1803, -6), (key1602, -6), (key1524, 2), (key1645, 2), (key1602, 2), (key1249, 2), (key1803, 2), (key1602, 2), (key1262, 2), (key1249, 2), (key1762, 2), (key1524, 2), (key1803, 2), (key1645, 2)]

theorem rawRowCheck9297 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form10 = rawRow9297 := by decide +kernel

def row9297 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9297 : row9297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9297 := by decide +kernel

theorem rowEval9297 (x : Key → ℝ) : Integer.Sparse.eval row9297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9297, Integer.Sparse.eval_collectBalanced, rawRowCheck9297]

def rawRow9298 : Integer.Sparse Key := [(key1602, -6), (key1602, -6), (key1249, -6), (key1803, -6), (key1602, 2), (key1524, 2), (key1645, 2), (key1602, 2), (key1249, 2), (key1803, 2), (key1524, 2), (key1645, 2), (key1249, 2), (key1803, 2), (key1262, 2), (key1762, 2)]

theorem rawRowCheck9298 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form10 = rawRow9298 := by decide +kernel

def row9298 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9298 : row9298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9298 := by decide +kernel

theorem rowEval9298 (x : Key → ℝ) : Integer.Sparse.eval row9298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck9298, Integer.Sparse.eval_collectBalanced, rawRowCheck9298]

def rawRow9299 : Integer.Sparse Key := [(key1602, -6), (key1602, -6), (key1803, -6), (key1249, -6), (key1602, 2), (key1645, 2), (key1524, 2), (key1602, 2), (key1803, 2), (key1249, 2), (key1645, 2), (key1524, 2), (key1803, 2), (key1249, 2), (key1762, 2), (key1262, 2)]

theorem rawRowCheck9299 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form10 = rawRow9299 := by decide +kernel

def row9299 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9299 : row9299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9299 := by decide +kernel

theorem rowEval9299 (x : Key → ℝ) : Integer.Sparse.eval row9299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9299, Integer.Sparse.eval_collectBalanced, rawRowCheck9299]

def rawRow9300 : Integer.Sparse Key := [(key1602, -6), (key1803, -6), (key1249, -6), (key1602, -6), (key1645, 2), (key1524, 2), (key1602, 2), (key1803, 2), (key1249, 2), (key1602, 2), (key1762, 2), (key1803, 2), (key1262, 2), (key1645, 2), (key1249, 2), (key1524, 2)]

theorem rawRowCheck9300 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form10 = rawRow9300 := by decide +kernel

def row9300 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9300 : row9300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9300 := by decide +kernel

theorem rowEval9300 (x : Key → ℝ) : Integer.Sparse.eval row9300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9300, Integer.Sparse.eval_collectBalanced, rawRowCheck9300]

def rawRow9301 : Integer.Sparse Key := [(key1602, -6), (key1803, -6), (key1602, -6), (key1249, -6), (key1645, 2), (key1602, 2), (key1524, 2), (key1803, 2), (key1602, 2), (key1249, 2), (key1803, 2), (key1762, 2), (key1645, 2), (key1262, 2), (key1524, 2), (key1249, 2)]

theorem rawRowCheck9301 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form10 = rawRow9301 := by decide +kernel

def row9301 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9301 : row9301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9301 := by decide +kernel

theorem rowEval9301 (x : Key → ℝ) : Integer.Sparse.eval row9301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9301, Integer.Sparse.eval_collectBalanced, rawRowCheck9301]

def rawRow9302 : Integer.Sparse Key := [(key1803, -6), (key1249, -6), (key1602, -6), (key1602, -6), (key1762, 2), (key1803, 2), (key1803, 2), (key1262, 2), (key1645, 2), (key1645, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2)]

theorem rawRowCheck9302 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form10 = rawRow9302 := by decide +kernel

def row9302 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9302 : row9302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9302 := by decide +kernel

theorem rowEval9302 (x : Key → ℝ) : Integer.Sparse.eval row9302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9302, Integer.Sparse.eval_collectBalanced, rawRowCheck9302]

def rawRow9303 : Integer.Sparse Key := [(key1803, -6), (key1602, -6), (key1249, -6), (key1602, -6), (key1803, 2), (key1762, 2), (key1803, 2), (key1645, 2), (key1262, 2), (key1645, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1249, 2), (key1524, 2)]

theorem rawRowCheck9303 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form10 = rawRow9303 := by decide +kernel

def row9303 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9303 : row9303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9303 := by decide +kernel

theorem rowEval9303 (x : Key → ℝ) : Integer.Sparse.eval row9303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck9303, Integer.Sparse.eval_collectBalanced, rawRowCheck9303]

def rawRow9304 : Integer.Sparse Key := [(key1803, -6), (key1602, -6), (key1602, -6), (key1249, -6), (key1803, 2), (key1803, 2), (key1762, 2), (key1645, 2), (key1645, 2), (key1262, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1524, 2), (key1249, 2)]

theorem rawRowCheck9304 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form10 = rawRow9304 := by decide +kernel

def row9304 : Integer.Sparse Key := [(key1249, -2), (key1262, 2), (key1524, 4), (key1602, -8), (key1645, 4), (key1762, 2), (key1803, -2)]

theorem rowCheck9304 : row9304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9304 := by decide +kernel

theorem rowEval9304 (x : Key → ℝ) : Integer.Sparse.eval row9304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form10) x := by
  rw [rowCheck9304, Integer.Sparse.eval_collectBalanced, rawRowCheck9304]

def rawRow9305 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2451, 6), (key2513, 6), (key2356, -6), (key2451, -6), (key2451, -6), (key2513, -6)]

theorem rawRowCheck9305 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form11 = rawRow9305 := by decide +kernel

def row9305 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9305 : row9305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9305 := by decide +kernel

theorem rowEval9305 (x : Key → ℝ) : Integer.Sparse.eval row9305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9305, Integer.Sparse.eval_collectBalanced, rawRowCheck9305]

def rawRow9306 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2451, 6), (key2513, 6), (key2356, -6), (key2451, -6), (key2513, -6), (key2451, -6)]

theorem rawRowCheck9306 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form11 = rawRow9306 := by decide +kernel

def row9306 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9306 : row9306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9306 := by decide +kernel

theorem rowEval9306 (x : Key → ℝ) : Integer.Sparse.eval row9306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9306, Integer.Sparse.eval_collectBalanced, rawRowCheck9306]

def rawRow9307 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2448, 6), (key2513, 6), (key2356, -6), (key2513, -6), (key2451, -6), (key2451, -6)]

theorem rawRowCheck9307 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form11 = rawRow9307 := by decide +kernel

def row9307 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9307 : row9307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9307 := by decide +kernel

theorem rowEval9307 (x : Key → ℝ) : Integer.Sparse.eval row9307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9307, Integer.Sparse.eval_collectBalanced, rawRowCheck9307]

def rawRow9308 : Integer.Sparse Key := [(key2448, 6), (key2451, 6), (key2513, 6), (key2451, 6), (key2451, -6), (key2356, -6), (key2451, -6), (key2513, -6)]

theorem rawRowCheck9308 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form11 = rawRow9308 := by decide +kernel

def row9308 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9308 : row9308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9308 := by decide +kernel

theorem rowEval9308 (x : Key → ℝ) : Integer.Sparse.eval row9308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9308, Integer.Sparse.eval_collectBalanced, rawRowCheck9308]

def rawRow9309 : Integer.Sparse Key := [(key2451, 6), (key2448, 6), (key2513, 6), (key2451, 6), (key2451, -6), (key2356, -6), (key2513, -6), (key2451, -6)]

theorem rawRowCheck9309 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form11 = rawRow9309 := by decide +kernel

def row9309 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9309 : row9309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9309 := by decide +kernel

theorem rowEval9309 (x : Key → ℝ) : Integer.Sparse.eval row9309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9309, Integer.Sparse.eval_collectBalanced, rawRowCheck9309]

def rawRow9310 : Integer.Sparse Key := [(key2448, 6), (key2513, 6), (key2451, 6), (key2451, 6), (key2451, -6), (key2451, -6), (key2356, -6), (key2513, -6)]

theorem rawRowCheck9310 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form11 = rawRow9310 := by decide +kernel

def row9310 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9310 : row9310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9310 := by decide +kernel

theorem rowEval9310 (x : Key → ℝ) : Integer.Sparse.eval row9310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck9310, Integer.Sparse.eval_collectBalanced, rawRowCheck9310]

def rawRow9311 : Integer.Sparse Key := [(key2513, 6), (key2448, 6), (key2451, 6), (key2451, 6), (key2451, -6), (key2451, -6), (key2513, -6), (key2356, -6)]

theorem rawRowCheck9311 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form11 = rawRow9311 := by decide +kernel

def row9311 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9311 : row9311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9311 := by decide +kernel

theorem rowEval9311 (x : Key → ℝ) : Integer.Sparse.eval row9311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9311, Integer.Sparse.eval_collectBalanced, rawRowCheck9311]

def rawRow9312 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2448, 6), (key2451, 6), (key2451, -6), (key2513, -6), (key2356, -6), (key2451, -6)]

theorem rawRowCheck9312 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form11 = rawRow9312 := by decide +kernel

def row9312 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9312 : row9312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9312 := by decide +kernel

theorem rowEval9312 (x : Key → ℝ) : Integer.Sparse.eval row9312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9312, Integer.Sparse.eval_collectBalanced, rawRowCheck9312]

def rawRow9313 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2448, 6), (key2451, 6), (key2451, -6), (key2513, -6), (key2451, -6), (key2356, -6)]

theorem rawRowCheck9313 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form11 = rawRow9313 := by decide +kernel

def row9313 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9313 : row9313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9313 := by decide +kernel

theorem rowEval9313 (x : Key → ℝ) : Integer.Sparse.eval row9313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9313, Integer.Sparse.eval_collectBalanced, rawRowCheck9313]

def rawRow9314 : Integer.Sparse Key := [(key2451, 6), (key2451, 6), (key2513, 6), (key2448, 6), (key2513, -6), (key2356, -6), (key2451, -6), (key2451, -6)]

theorem rawRowCheck9314 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form11 = rawRow9314 := by decide +kernel

def row9314 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9314 : row9314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9314 := by decide +kernel

theorem rowEval9314 (x : Key → ℝ) : Integer.Sparse.eval row9314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9314, Integer.Sparse.eval_collectBalanced, rawRowCheck9314]

def rawRow9315 : Integer.Sparse Key := [(key2451, 6), (key2513, 6), (key2451, 6), (key2448, 6), (key2513, -6), (key2451, -6), (key2356, -6), (key2451, -6)]

theorem rawRowCheck9315 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form11 = rawRow9315 := by decide +kernel

def row9315 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9315 : row9315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9315 := by decide +kernel

theorem rowEval9315 (x : Key → ℝ) : Integer.Sparse.eval row9315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck9315, Integer.Sparse.eval_collectBalanced, rawRowCheck9315]

def rawRow9316 : Integer.Sparse Key := [(key2513, 6), (key2451, 6), (key2451, 6), (key2448, 6), (key2513, -6), (key2451, -6), (key2451, -6), (key2356, -6)]

theorem rawRowCheck9316 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form11 = rawRow9316 := by decide +kernel

def row9316 : Integer.Sparse Key := [(key2356, -6), (key2448, 6)]

theorem rowCheck9316 : row9316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9316 := by decide +kernel

theorem rowEval9316 (x : Key → ℝ) : Integer.Sparse.eval row9316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form11) x := by
  rw [rowCheck9316, Integer.Sparse.eval_collectBalanced, rawRowCheck9316]

def rawRow9317 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2514, -6), (key2514, -6), (key2514, -6), (key2559, -6)]

theorem rawRowCheck9317 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form12 = rawRow9317 := by decide +kernel

def row9317 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

theorem rowCheck9317 : row9317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9317 := by decide +kernel

theorem rowEval9317 (x : Key → ℝ) : Integer.Sparse.eval row9317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9317, Integer.Sparse.eval_collectBalanced, rawRowCheck9317]

def rawRow9318 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2514, -6), (key2514, -6), (key2559, -6), (key2514, -6)]

theorem rawRowCheck9318 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form12 = rawRow9318 := by decide +kernel

def row9318 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

theorem rowCheck9318 : row9318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9318 := by decide +kernel

theorem rowEval9318 (x : Key → ℝ) : Integer.Sparse.eval row9318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9318, Integer.Sparse.eval_collectBalanced, rawRowCheck9318]

def rawRow9319 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2514, -6), (key2559, -6), (key2514, -6), (key2514, -6)]

theorem rawRowCheck9319 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form12 = rawRow9319 := by decide +kernel

def row9319 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

theorem rowCheck9319 : row9319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9319 := by decide +kernel

theorem rowEval9319 (x : Key → ℝ) : Integer.Sparse.eval row9319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9319, Integer.Sparse.eval_collectBalanced, rawRowCheck9319]

def rawRow9320 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2559, -6), (key2514, -6), (key2514, -6), (key2514, -6)]

theorem rawRowCheck9320 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form12 = rawRow9320 := by decide +kernel

def row9320 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2514, -18), (key2559, -6)]

theorem rowCheck9320 : row9320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9320 := by decide +kernel

theorem rowEval9320 (x : Key → ℝ) : Integer.Sparse.eval row9320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9320, Integer.Sparse.eval_collectBalanced, rawRowCheck9320]

def rawRow9321 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, -6), (key2453, -6), (key2453, -6), (key2529, -6)]

theorem rawRowCheck9321 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form12 = rawRow9321 := by decide +kernel

def row9321 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9321 : row9321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9321 := by decide +kernel

theorem rowEval9321 (x : Key → ℝ) : Integer.Sparse.eval row9321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9321, Integer.Sparse.eval_collectBalanced, rawRowCheck9321]

def rawRow9322 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2358, -6), (key2453, -6), (key2529, -6), (key2453, -6)]

theorem rawRowCheck9322 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form12 = rawRow9322 := by decide +kernel

def row9322 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9322 : row9322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9322 := by decide +kernel

theorem rowEval9322 (x : Key → ℝ) : Integer.Sparse.eval row9322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9322, Integer.Sparse.eval_collectBalanced, rawRowCheck9322]

def rawRow9323 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, -6), (key2529, -6), (key2453, -6), (key2453, -6)]

theorem rawRowCheck9323 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form12 = rawRow9323 := by decide +kernel

def row9323 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9323 : row9323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9323 := by decide +kernel

theorem rowEval9323 (x : Key → ℝ) : Integer.Sparse.eval row9323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9323, Integer.Sparse.eval_collectBalanced, rawRowCheck9323]

def rawRow9324 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2453, -6), (key2358, -6), (key2453, -6), (key2529, -6)]

theorem rawRowCheck9324 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form12 = rawRow9324 := by decide +kernel

def row9324 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9324 : row9324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9324 := by decide +kernel

theorem rowEval9324 (x : Key → ℝ) : Integer.Sparse.eval row9324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9324, Integer.Sparse.eval_collectBalanced, rawRowCheck9324]

def rawRow9325 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2453, -6), (key2358, -6), (key2529, -6), (key2453, -6)]

theorem rawRowCheck9325 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form12 = rawRow9325 := by decide +kernel

def row9325 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9325 : row9325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9325 := by decide +kernel

theorem rowEval9325 (x : Key → ℝ) : Integer.Sparse.eval row9325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9325, Integer.Sparse.eval_collectBalanced, rawRowCheck9325]

def rawRow9326 : Integer.Sparse Key := [(key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2453, -6), (key2453, -6), (key2358, -6), (key2529, -6)]

theorem rawRowCheck9326 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form12 = rawRow9326 := by decide +kernel

def row9326 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9326 : row9326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9326 := by decide +kernel

theorem rowEval9326 (x : Key → ℝ) : Integer.Sparse.eval row9326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck9326, Integer.Sparse.eval_collectBalanced, rawRowCheck9326]

def rawRow9327 : Integer.Sparse Key := [(key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2453, -6), (key2453, -6), (key2529, -6), (key2358, -6)]

theorem rawRowCheck9327 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form12 = rawRow9327 := by decide +kernel

def row9327 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9327 : row9327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9327 := by decide +kernel

theorem rowEval9327 (x : Key → ℝ) : Integer.Sparse.eval row9327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9327, Integer.Sparse.eval_collectBalanced, rawRowCheck9327]

def rawRow9328 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2453, -6), (key2529, -6), (key2358, -6), (key2453, -6)]

theorem rawRowCheck9328 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form12 = rawRow9328 := by decide +kernel

def row9328 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9328 : row9328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9328 := by decide +kernel

theorem rowEval9328 (x : Key → ℝ) : Integer.Sparse.eval row9328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9328, Integer.Sparse.eval_collectBalanced, rawRowCheck9328]

def rawRow9329 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2453, -6), (key2529, -6), (key2453, -6), (key2358, -6)]

theorem rawRowCheck9329 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form12 = rawRow9329 := by decide +kernel

def row9329 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9329 : row9329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9329 := by decide +kernel

theorem rowEval9329 (x : Key → ℝ) : Integer.Sparse.eval row9329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9329, Integer.Sparse.eval_collectBalanced, rawRowCheck9329]

def rawRow9330 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, -6), (key2358, -6), (key2453, -6), (key2453, -6)]

theorem rawRowCheck9330 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form12 = rawRow9330 := by decide +kernel

def row9330 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9330 : row9330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9330 := by decide +kernel

theorem rowEval9330 (x : Key → ℝ) : Integer.Sparse.eval row9330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9330, Integer.Sparse.eval_collectBalanced, rawRowCheck9330]

def rawRow9331 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2529, -6), (key2453, -6), (key2358, -6), (key2453, -6)]

theorem rawRowCheck9331 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form12 = rawRow9331 := by decide +kernel

def row9331 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9331 : row9331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9331 := by decide +kernel

theorem rowEval9331 (x : Key → ℝ) : Integer.Sparse.eval row9331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck9331, Integer.Sparse.eval_collectBalanced, rawRowCheck9331]

def rawRow9332 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, -6), (key2453, -6), (key2453, -6), (key2358, -6)]

theorem rawRowCheck9332 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form12 = rawRow9332 := by decide +kernel

def row9332 : Integer.Sparse Key := [(key2358, -6), (key2449, 6), (key2514, 6), (key2529, -6)]

theorem rowCheck9332 : row9332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9332 := by decide +kernel

theorem rowEval9332 (x : Key → ℝ) : Integer.Sparse.eval row9332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block3.form12) x := by
  rw [rowCheck9332, Integer.Sparse.eval_collectBalanced, rawRowCheck9332]

def rawRow9333 : Integer.Sparse Key := [(key2006, -6), (key2007, -6), (key2007, -6), (key2007, -6), (key2299, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2340, 2)]

theorem rawRowCheck9333 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form13 = rawRow9333 := by decide +kernel

def row9333 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

theorem rowCheck9333 : row9333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9333 := by decide +kernel

theorem rowEval9333 (x : Key → ℝ) : Integer.Sparse.eval row9333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9333, Integer.Sparse.eval_collectBalanced, rawRowCheck9333]

def rawRow9334 : Integer.Sparse Key := [(key2007, -6), (key2006, -6), (key2007, -6), (key2007, -6), (key2300, 2), (key2299, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2340, 2), (key2300, 2)]

theorem rawRowCheck9334 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form13 = rawRow9334 := by decide +kernel

def row9334 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

theorem rowCheck9334 : row9334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9334 := by decide +kernel

theorem rowEval9334 (x : Key → ℝ) : Integer.Sparse.eval row9334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9334, Integer.Sparse.eval_collectBalanced, rawRowCheck9334]

def rawRow9335 : Integer.Sparse Key := [(key2007, -6), (key2007, -6), (key2006, -6), (key2007, -6), (key2300, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2300, 2)]

theorem rawRowCheck9335 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form13 = rawRow9335 := by decide +kernel

def row9335 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

theorem rowCheck9335 : row9335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9335 := by decide +kernel

theorem rowEval9335 (x : Key → ℝ) : Integer.Sparse.eval row9335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9335, Integer.Sparse.eval_collectBalanced, rawRowCheck9335]

def rawRow9336 : Integer.Sparse Key := [(key2007, -6), (key2007, -6), (key2007, -6), (key2006, -6), (key2340, 2), (key2340, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2299, 2), (key2299, 2)]

theorem rawRowCheck9336 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9336 := by decide +kernel

def row9336 : Integer.Sparse Key := [(key2006, -6), (key2007, -18), (key2299, 6), (key2300, 12), (key2340, 6)]

theorem rowCheck9336 : row9336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9336 := by decide +kernel

theorem rowEval9336 (x : Key → ℝ) : Integer.Sparse.eval row9336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9336, Integer.Sparse.eval_collectBalanced, rawRowCheck9336]

def rawRow9337 : Integer.Sparse Key := [(key2299, -6), (key2300, -6), (key2300, -6), (key2313, -6), (key2006, 2), (key2007, 2), (key2007, 2), (key2299, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2340, 2), (key2313, 2), (key2313, 2), (key2349, 2)]

theorem rawRowCheck9337 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form13 = rawRow9337 := by decide +kernel

def row9337 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9337 : row9337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9337 := by decide +kernel

theorem rowEval9337 (x : Key → ℝ) : Integer.Sparse.eval row9337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9337, Integer.Sparse.eval_collectBalanced, rawRowCheck9337]

def rawRow9338 : Integer.Sparse Key := [(key2300, -6), (key2299, -6), (key2300, -6), (key2313, -6), (key2007, 2), (key2006, 2), (key2007, 2), (key2300, 2), (key2299, 2), (key2340, 2), (key2299, 2), (key2340, 2), (key2300, 2), (key2313, 2), (key2349, 2), (key2313, 2)]

theorem rawRowCheck9338 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form13 = rawRow9338 := by decide +kernel

def row9338 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9338 : row9338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9338 := by decide +kernel

theorem rowEval9338 (x : Key → ℝ) : Integer.Sparse.eval row9338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9338, Integer.Sparse.eval_collectBalanced, rawRowCheck9338]

def rawRow9339 : Integer.Sparse Key := [(key2300, -6), (key2300, -6), (key2299, -6), (key2313, -6), (key2007, 2), (key2007, 2), (key2006, 2), (key2340, 2), (key2340, 2), (key2300, 2), (key2300, 2), (key2299, 2), (key2299, 2), (key2349, 2), (key2313, 2), (key2313, 2)]

theorem rawRowCheck9339 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form13 = rawRow9339 := by decide +kernel

def row9339 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9339 : row9339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9339 := by decide +kernel

theorem rowEval9339 (x : Key → ℝ) : Integer.Sparse.eval row9339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9339, Integer.Sparse.eval_collectBalanced, rawRowCheck9339]

def rawRow9340 : Integer.Sparse Key := [(key2299, -6), (key2300, -6), (key2313, -6), (key2300, -6), (key2299, 2), (key2300, 2), (key2313, 2), (key2006, 2), (key2007, 2), (key2299, 2), (key2340, 2), (key2313, 2), (key2349, 2), (key2007, 2), (key2300, 2), (key2340, 2)]

theorem rawRowCheck9340 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form13 = rawRow9340 := by decide +kernel

def row9340 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9340 : row9340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9340 := by decide +kernel

theorem rowEval9340 (x : Key → ℝ) : Integer.Sparse.eval row9340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 0, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9340, Integer.Sparse.eval_collectBalanced, rawRowCheck9340]

def rawRow9341 : Integer.Sparse Key := [(key2300, -6), (key2299, -6), (key2313, -6), (key2300, -6), (key2300, 2), (key2299, 2), (key2313, 2), (key2007, 2), (key2006, 2), (key2340, 2), (key2299, 2), (key2349, 2), (key2313, 2), (key2007, 2), (key2340, 2), (key2300, 2)]

theorem rawRowCheck9341 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form13 = rawRow9341 := by decide +kernel

def row9341 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9341 : row9341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9341 := by decide +kernel

theorem rowEval9341 (x : Key → ℝ) : Integer.Sparse.eval row9341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -3, 1, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9341, Integer.Sparse.eval_collectBalanced, rawRowCheck9341]

def rawRow9342 : Integer.Sparse Key := [(key2299, -6), (key2313, -6), (key2300, -6), (key2300, -6), (key2299, 2), (key2313, 2), (key2300, 2), (key2299, 2), (key2313, 2), (key2006, 2), (key2349, 2), (key2007, 2), (key2340, 2), (key2300, 2), (key2007, 2), (key2340, 2)]

theorem rawRowCheck9342 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form13 = rawRow9342 := by decide +kernel

def row9342 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9342 : row9342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9342 := by decide +kernel

theorem rowEval9342 (x : Key → ℝ) : Integer.Sparse.eval row9342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, -3, 1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9342, Integer.Sparse.eval_collectBalanced, rawRowCheck9342]

def rawRow9343 : Integer.Sparse Key := [(key2313, -6), (key2299, -6), (key2300, -6), (key2300, -6), (key2313, 2), (key2299, 2), (key2300, 2), (key2313, 2), (key2299, 2), (key2349, 2), (key2006, 2), (key2340, 2), (key2007, 2), (key2300, 2), (key2340, 2), (key2007, 2)]

theorem rawRowCheck9343 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form13 = rawRow9343 := by decide +kernel

def row9343 : Integer.Sparse Key := [(key2006, 2), (key2007, 4), (key2299, -2), (key2300, -8), (key2313, -2), (key2340, 4), (key2349, 2)]

theorem rowCheck9343 : row9343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9343 := by decide +kernel

theorem rowEval9343 (x : Key → ℝ) : Integer.Sparse.eval row9343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 0, 1, -3] GramFunctions.Block3.form13) x := by
  rw [rowCheck9343, Integer.Sparse.eval_collectBalanced, rawRowCheck9343]

end MUB6.Certificate.GramRows

end OAI
