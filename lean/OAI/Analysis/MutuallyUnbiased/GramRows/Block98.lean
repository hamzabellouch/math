import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
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

def rawRow9472 : Integer.Sparse Key := [(key2099, -6), (key2098, -6), (key2098, -6), (key2098, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2203, 2), (key2317, 2), (key2317, 2), (key2203, 2)]

theorem rawRowCheck9472 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form13 = rawRow9472 := by decide +kernel

def row9472 : Integer.Sparse Key := [(key2098, -18), (key2099, -6), (key2203, 6), (key2317, 12), (key2318, 6)]

theorem rowCheck9472 : row9472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9472 := by decide +kernel

theorem rowEval9472 (x : Key → ℝ) : Integer.Sparse.eval row9472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9472, Integer.Sparse.eval_collectBalanced, rawRowCheck9472]

def rawRow9473 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2203, -6), (key2206, -6), (key2098, 2), (key2098, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2321, 2)]

theorem rawRowCheck9473 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow9473 := by decide +kernel

def row9473 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

theorem rowCheck9473 : row9473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9473 := by decide +kernel

theorem rowEval9473 (x : Key → ℝ) : Integer.Sparse.eval row9473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9473, Integer.Sparse.eval_collectBalanced, rawRowCheck9473]

def rawRow9474 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2206, -6), (key2203, -6), (key2317, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2317, 2)]

theorem rawRowCheck9474 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form13 = rawRow9474 := by decide +kernel

def row9474 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

theorem rowCheck9474 : row9474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9474 := by decide +kernel

theorem rowEval9474 (x : Key → ℝ) : Integer.Sparse.eval row9474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9474, Integer.Sparse.eval_collectBalanced, rawRowCheck9474]

def rawRow9475 : Integer.Sparse Key := [(key2203, -6), (key2206, -6), (key2203, -6), (key2203, -6), (key2317, 2), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2098, 2), (key2317, 2)]

theorem rawRowCheck9475 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form13 = rawRow9475 := by decide +kernel

def row9475 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

theorem rowCheck9475 : row9475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9475 := by decide +kernel

theorem rowEval9475 (x : Key → ℝ) : Integer.Sparse.eval row9475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck9475, Integer.Sparse.eval_collectBalanced, rawRowCheck9475]

def rawRow9476 : Integer.Sparse Key := [(key2206, -6), (key2203, -6), (key2203, -6), (key2203, -6), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2098, 2), (key2317, 2), (key2317, 2), (key2098, 2)]

theorem rawRowCheck9476 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form13 = rawRow9476 := by decide +kernel

def row9476 : Integer.Sparse Key := [(key2098, 6), (key2203, -18), (key2206, -6), (key2317, 12), (key2321, 6)]

theorem rowCheck9476 : row9476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9476 := by decide +kernel

theorem rowEval9476 (x : Key → ℝ) : Integer.Sparse.eval row9476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck9476, Integer.Sparse.eval_collectBalanced, rawRowCheck9476]

def rawRow9477 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key995, 6), (key1011, 6), (key1067, -6), (key1146, -6), (key1146, -6), (key1146, -6)]

theorem rawRowCheck9477 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9477 := by decide +kernel

def row9477 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

theorem rowCheck9477 : row9477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9477 := by decide +kernel

theorem rowEval9477 (x : Key → ℝ) : Integer.Sparse.eval row9477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9477, Integer.Sparse.eval_collectBalanced, rawRowCheck9477]

def rawRow9478 : Integer.Sparse Key := [(key995, 6), (key995, 6), (key1011, 6), (key995, 6), (key1146, -6), (key1067, -6), (key1146, -6), (key1146, -6)]

theorem rawRowCheck9478 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form14 = rawRow9478 := by decide +kernel

def row9478 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

theorem rowCheck9478 : row9478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9478 := by decide +kernel

theorem rowEval9478 (x : Key → ℝ) : Integer.Sparse.eval row9478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9478, Integer.Sparse.eval_collectBalanced, rawRowCheck9478]

def rawRow9479 : Integer.Sparse Key := [(key995, 6), (key1011, 6), (key995, 6), (key995, 6), (key1146, -6), (key1146, -6), (key1067, -6), (key1146, -6)]

theorem rawRowCheck9479 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form14 = rawRow9479 := by decide +kernel

def row9479 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

theorem rowCheck9479 : row9479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9479 := by decide +kernel

theorem rowEval9479 (x : Key → ℝ) : Integer.Sparse.eval row9479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9479, Integer.Sparse.eval_collectBalanced, rawRowCheck9479]

def rawRow9480 : Integer.Sparse Key := [(key1011, 6), (key995, 6), (key995, 6), (key995, 6), (key1146, -6), (key1146, -6), (key1146, -6), (key1067, -6)]

theorem rawRowCheck9480 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form14 = rawRow9480 := by decide +kernel

def row9480 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1067, -6), (key1146, -18)]

theorem rowCheck9480 : row9480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9480 := by decide +kernel

theorem rowEval9480 (x : Key → ℝ) : Integer.Sparse.eval row9480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form14) x := by
  rw [rowCheck9480, Integer.Sparse.eval_collectBalanced, rawRowCheck9480]

def rawRow9481 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1030, 6), (key1067, 6), (key1011, -6), (key1119, -6), (key1119, -6), (key1119, -6)]

theorem rawRowCheck9481 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow9481 := by decide +kernel

def row9481 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

theorem rowCheck9481 : row9481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9481 := by decide +kernel

theorem rowEval9481 (x : Key → ℝ) : Integer.Sparse.eval row9481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9481, Integer.Sparse.eval_collectBalanced, rawRowCheck9481]

def rawRow9482 : Integer.Sparse Key := [(key1030, 6), (key1030, 6), (key1067, 6), (key1030, 6), (key1119, -6), (key1011, -6), (key1119, -6), (key1119, -6)]

theorem rawRowCheck9482 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form14 = rawRow9482 := by decide +kernel

def row9482 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

theorem rowCheck9482 : row9482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9482 := by decide +kernel

theorem rowEval9482 (x : Key → ℝ) : Integer.Sparse.eval row9482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9482, Integer.Sparse.eval_collectBalanced, rawRowCheck9482]

def rawRow9483 : Integer.Sparse Key := [(key1030, 6), (key1067, 6), (key1030, 6), (key1030, 6), (key1119, -6), (key1119, -6), (key1011, -6), (key1119, -6)]

theorem rawRowCheck9483 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form14 = rawRow9483 := by decide +kernel

def row9483 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

theorem rowCheck9483 : row9483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9483 := by decide +kernel

theorem rowEval9483 (x : Key → ℝ) : Integer.Sparse.eval row9483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck9483, Integer.Sparse.eval_collectBalanced, rawRowCheck9483]

def rawRow9484 : Integer.Sparse Key := [(key1067, 6), (key1030, 6), (key1030, 6), (key1030, 6), (key1119, -6), (key1119, -6), (key1119, -6), (key1011, -6)]

theorem rawRowCheck9484 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form14 = rawRow9484 := by decide +kernel

def row9484 : Integer.Sparse Key := [(key1011, -6), (key1030, 18), (key1067, 6), (key1119, -18)]

theorem rowCheck9484 : row9484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9484 := by decide +kernel

theorem rowEval9484 (x : Key → ℝ) : Integer.Sparse.eval row9484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck9484, Integer.Sparse.eval_collectBalanced, rawRowCheck9484]

def rawRow9485 : Integer.Sparse Key := [(key2369, -6), (key2369, -6), (key2369, -6), (key2384, -6), (key2397, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2474, 2), (key2474, 2)]

theorem rawRowCheck9485 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9485 := by decide +kernel

def row9485 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

theorem rowCheck9485 : row9485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9485 := by decide +kernel

theorem rowEval9485 (x : Key → ℝ) : Integer.Sparse.eval row9485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9485, Integer.Sparse.eval_collectBalanced, rawRowCheck9485]

def rawRow9486 : Integer.Sparse Key := [(key2369, -6), (key2369, -6), (key2384, -6), (key2369, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck9486 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form15 = rawRow9486 := by decide +kernel

def row9486 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

theorem rowCheck9486 : row9486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9486 := by decide +kernel

theorem rowEval9486 (x : Key → ℝ) : Integer.Sparse.eval row9486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9486, Integer.Sparse.eval_collectBalanced, rawRowCheck9486]

def rawRow9487 : Integer.Sparse Key := [(key2369, -6), (key2384, -6), (key2369, -6), (key2369, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2397, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2397, 2), (key2463, 2)]

theorem rawRowCheck9487 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form15 = rawRow9487 := by decide +kernel

def row9487 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

theorem rowCheck9487 : row9487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9487 := by decide +kernel

theorem rowEval9487 (x : Key → ℝ) : Integer.Sparse.eval row9487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9487, Integer.Sparse.eval_collectBalanced, rawRowCheck9487]

def rawRow9488 : Integer.Sparse Key := [(key2384, -6), (key2369, -6), (key2369, -6), (key2369, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2474, 2), (key2397, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2397, 2)]

theorem rawRowCheck9488 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form15 = rawRow9488 := by decide +kernel

def row9488 : Integer.Sparse Key := [(key2369, -18), (key2384, -6), (key2397, 6), (key2463, 12), (key2474, 6)]

theorem rowCheck9488 : row9488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9488 := by decide +kernel

theorem rowEval9488 (x : Key → ℝ) : Integer.Sparse.eval row9488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form15) x := by
  rw [rowCheck9488, Integer.Sparse.eval_collectBalanced, rawRowCheck9488]

def rawRow9489 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2397, -6), (key2431, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2497, 2)]

theorem rawRowCheck9489 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow9489 := by decide +kernel

def row9489 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

theorem rowCheck9489 : row9489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9489 := by decide +kernel

theorem rowEval9489 (x : Key → ℝ) : Integer.Sparse.eval row9489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9489, Integer.Sparse.eval_collectBalanced, rawRowCheck9489]

def rawRow9490 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2431, -6), (key2397, -6), (key2463, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2463, 2)]

theorem rawRowCheck9490 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form15 = rawRow9490 := by decide +kernel

def row9490 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

theorem rowCheck9490 : row9490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9490 := by decide +kernel

theorem rowEval9490 (x : Key → ℝ) : Integer.Sparse.eval row9490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9490, Integer.Sparse.eval_collectBalanced, rawRowCheck9490]

def rawRow9491 : Integer.Sparse Key := [(key2397, -6), (key2431, -6), (key2397, -6), (key2397, -6), (key2463, 2), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2)]

theorem rawRowCheck9491 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form15 = rawRow9491 := by decide +kernel

def row9491 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

theorem rowCheck9491 : row9491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9491 := by decide +kernel

theorem rowEval9491 (x : Key → ℝ) : Integer.Sparse.eval row9491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck9491, Integer.Sparse.eval_collectBalanced, rawRowCheck9491]

def rawRow9492 : Integer.Sparse Key := [(key2431, -6), (key2397, -6), (key2397, -6), (key2397, -6), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2)]

theorem rawRowCheck9492 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form15 = rawRow9492 := by decide +kernel

def row9492 : Integer.Sparse Key := [(key2369, 6), (key2397, -18), (key2431, -6), (key2463, 12), (key2497, 6)]

theorem rowCheck9492 : row9492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9492 := by decide +kernel

theorem rowEval9492 (x : Key → ℝ) : Integer.Sparse.eval row9492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck9492, Integer.Sparse.eval_collectBalanced, rawRowCheck9492]

def rawRow9493 : Integer.Sparse Key := [(key2606, -6), (key2622, -6), (key2622, -6), (key2622, -6), (key2661, 6), (key2696, 6), (key2696, 6), (key2696, 6)]

theorem rawRowCheck9493 : GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form16 = rawRow9493 := by decide +kernel

def row9493 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

theorem rowCheck9493 : row9493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9493 := by decide +kernel

theorem rowEval9493 (x : Key → ℝ) : Integer.Sparse.eval row9493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, -1, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9493, Integer.Sparse.eval_collectBalanced, rawRowCheck9493]

def rawRow9494 : Integer.Sparse Key := [(key2622, -6), (key2606, -6), (key2622, -6), (key2622, -6), (key2696, 6), (key2661, 6), (key2696, 6), (key2696, 6)]

theorem rawRowCheck9494 : GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form16 = rawRow9494 := by decide +kernel

def row9494 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

theorem rowCheck9494 : row9494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9494 := by decide +kernel

theorem rowEval9494 (x : Key → ℝ) : Integer.Sparse.eval row9494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, -1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9494, Integer.Sparse.eval_collectBalanced, rawRowCheck9494]

def rawRow9495 : Integer.Sparse Key := [(key2622, -6), (key2622, -6), (key2606, -6), (key2622, -6), (key2696, 6), (key2696, 6), (key2661, 6), (key2696, 6)]

theorem rawRowCheck9495 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form16 = rawRow9495 := by decide +kernel

def row9495 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

theorem rowCheck9495 : row9495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9495 := by decide +kernel

theorem rowEval9495 (x : Key → ℝ) : Integer.Sparse.eval row9495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, -1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9495, Integer.Sparse.eval_collectBalanced, rawRowCheck9495]

def rawRow9496 : Integer.Sparse Key := [(key2622, -6), (key2622, -6), (key2622, -6), (key2606, -6), (key2696, 6), (key2696, 6), (key2696, 6), (key2661, 6)]

theorem rawRowCheck9496 : GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form16 = rawRow9496 := by decide +kernel

def row9496 : Integer.Sparse Key := [(key2606, -6), (key2622, -18), (key2661, 6), (key2696, 18)]

theorem rowCheck9496 : row9496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9496 := by decide +kernel

theorem rowEval9496 (x : Key → ℝ) : Integer.Sparse.eval row9496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -2, 0, 0, 0, -1] GramFunctions.Block3.form16) x := by
  rw [rowCheck9496, Integer.Sparse.eval_collectBalanced, rawRowCheck9496]

def rawRow9497 : Integer.Sparse Key := [(key2661, -6), (key2696, -6), (key2696, -6), (key2696, -6), (key2606, 6), (key2799, 6), (key2799, 6), (key2799, 6)]

theorem rawRowCheck9497 : GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow9497 := by decide +kernel

def row9497 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

theorem rowCheck9497 : row9497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9497 := by decide +kernel

theorem rowEval9497 (x : Key → ℝ) : Integer.Sparse.eval row9497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, -2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9497, Integer.Sparse.eval_collectBalanced, rawRowCheck9497]

def rawRow9498 : Integer.Sparse Key := [(key2696, -6), (key2661, -6), (key2696, -6), (key2696, -6), (key2799, 6), (key2606, 6), (key2799, 6), (key2799, 6)]

theorem rawRowCheck9498 : GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form16 = rawRow9498 := by decide +kernel

def row9498 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

theorem rowCheck9498 : row9498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9498 := by decide +kernel

theorem rowEval9498 (x : Key → ℝ) : Integer.Sparse.eval row9498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9498, Integer.Sparse.eval_collectBalanced, rawRowCheck9498]

def rawRow9499 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2661, -6), (key2696, -6), (key2799, 6), (key2799, 6), (key2606, 6), (key2799, 6)]

theorem rawRowCheck9499 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form16 = rawRow9499 := by decide +kernel

def row9499 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

theorem rowCheck9499 : row9499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9499 := by decide +kernel

theorem rowEval9499 (x : Key → ℝ) : Integer.Sparse.eval row9499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck9499, Integer.Sparse.eval_collectBalanced, rawRowCheck9499]

def rawRow9500 : Integer.Sparse Key := [(key2696, -6), (key2696, -6), (key2696, -6), (key2661, -6), (key2799, 6), (key2799, 6), (key2799, 6), (key2606, 6)]

theorem rawRowCheck9500 : GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form16 = rawRow9500 := by decide +kernel

def row9500 : Integer.Sparse Key := [(key2606, 6), (key2661, -6), (key2696, -18), (key2799, 18)]

theorem rowCheck9500 : row9500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9500 := by decide +kernel

theorem rowEval9500 (x : Key → ℝ) : Integer.Sparse.eval row9500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, -1, 0, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck9500, Integer.Sparse.eval_collectBalanced, rawRowCheck9500]

def rawRow9501 : Integer.Sparse Key := [(key2592, 2), (key2595, 2), (key2595, 2), (key2848, 2), (key2882, 2), (key2882, 2), (key2970, 2), (key2970, 2), (key2991, 2), (key2991, 2), (key2993, 2), (key2993, 2), (key2602, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2891, -2), (key2912, -2), (key2912, -2), (key2914, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key3003, -2)]

theorem rawRowCheck9501 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form0 = rawRow9501 := by decide +kernel

def row9501 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9501 : row9501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9501 := by decide +kernel

theorem rowEval9501 (x : Key → ℝ) : Integer.Sparse.eval row9501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9501, Integer.Sparse.eval_collectBalanced, rawRowCheck9501]

def rawRow9502 : Integer.Sparse Key := [(key2595, 2), (key2592, 2), (key2595, 2), (key2882, 2), (key2848, 2), (key2882, 2), (key2991, 2), (key2993, 2), (key2970, 2), (key2993, 2), (key2970, 2), (key2991, 2), (key2602, -2), (key2603, -2), (key2602, -2), (key2912, -2), (key2914, -2), (key2891, -2), (key2914, -2), (key2891, -2), (key2912, -2), (key3003, -2), (key2996, -2), (key3003, -2)]

theorem rawRowCheck9502 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form0 = rawRow9502 := by decide +kernel

def row9502 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9502 : row9502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9502 := by decide +kernel

theorem rowEval9502 (x : Key → ℝ) : Integer.Sparse.eval row9502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9502, Integer.Sparse.eval_collectBalanced, rawRowCheck9502]

def rawRow9503 : Integer.Sparse Key := [(key2595, 2), (key2595, 2), (key2592, 2), (key2882, 2), (key2882, 2), (key2848, 2), (key2993, 2), (key2991, 2), (key2993, 2), (key2970, 2), (key2991, 2), (key2970, 2), (key2603, -2), (key2602, -2), (key2602, -2), (key2914, -2), (key2912, -2), (key2914, -2), (key2891, -2), (key2912, -2), (key2891, -2), (key3003, -2), (key3003, -2), (key2996, -2)]

theorem rawRowCheck9503 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form0 = rawRow9503 := by decide +kernel

def row9503 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9503 : row9503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9503 := by decide +kernel

theorem rowEval9503 (x : Key → ℝ) : Integer.Sparse.eval row9503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9503, Integer.Sparse.eval_collectBalanced, rawRowCheck9503]

def rawRow9504 : Integer.Sparse Key := [(key2848, 2), (key2970, 2), (key2970, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2595, 2), (key2595, 2), (key2882, 2), (key2882, 2), (key2993, 2), (key2993, 2), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2914, -2)]

theorem rawRowCheck9504 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form0 = rawRow9504 := by decide +kernel

def row9504 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9504 : row9504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9504 := by decide +kernel

theorem rowEval9504 (x : Key → ℝ) : Integer.Sparse.eval row9504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9504, Integer.Sparse.eval_collectBalanced, rawRowCheck9504]

def rawRow9505 : Integer.Sparse Key := [(key2970, 2), (key2848, 2), (key2970, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2882, 2), (key2993, 2), (key2595, 2), (key2993, 2), (key2595, 2), (key2882, 2), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2914, -2), (key2603, -2), (key2914, -2)]

theorem rawRowCheck9505 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form0 = rawRow9505 := by decide +kernel

def row9505 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9505 : row9505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9505 := by decide +kernel

theorem rowEval9505 (x : Key → ℝ) : Integer.Sparse.eval row9505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9505, Integer.Sparse.eval_collectBalanced, rawRowCheck9505]

def rawRow9506 : Integer.Sparse Key := [(key2970, 2), (key2970, 2), (key2848, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key2993, 2), (key2882, 2), (key2993, 2), (key2595, 2), (key2882, 2), (key2595, 2), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2914, -2), (key2914, -2), (key2603, -2)]

theorem rawRowCheck9506 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form0 = rawRow9506 := by decide +kernel

def row9506 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9506 : row9506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9506 := by decide +kernel

theorem rowEval9506 (x : Key → ℝ) : Integer.Sparse.eval row9506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9506, Integer.Sparse.eval_collectBalanced, rawRowCheck9506]

def rawRow9507 : Integer.Sparse Key := [(key2882, 2), (key2991, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2993, 2), (key2592, 2), (key2595, 2), (key2848, 2), (key2882, 2), (key2970, 2), (key2991, 2), (key2912, -2), (key2914, -2), (key3003, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key2602, -2), (key2891, -2), (key2912, -2)]

theorem rawRowCheck9507 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form0 = rawRow9507 := by decide +kernel

def row9507 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9507 : row9507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9507 := by decide +kernel

theorem rowEval9507 (x : Key → ℝ) : Integer.Sparse.eval row9507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9507, Integer.Sparse.eval_collectBalanced, rawRowCheck9507]

def rawRow9508 : Integer.Sparse Key := [(key2882, 2), (key2993, 2), (key2991, 2), (key2595, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2592, 2), (key2882, 2), (key2848, 2), (key2991, 2), (key2970, 2), (key2914, -2), (key2912, -2), (key3003, -2), (key2603, -2), (key2602, -2), (key2914, -2), (key2891, -2), (key3003, -2), (key2996, -2), (key2602, -2), (key2912, -2), (key2891, -2)]

theorem rawRowCheck9508 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form0 = rawRow9508 := by decide +kernel

def row9508 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9508 : row9508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9508 := by decide +kernel

theorem rowEval9508 (x : Key → ℝ) : Integer.Sparse.eval row9508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9508, Integer.Sparse.eval_collectBalanced, rawRowCheck9508]

def rawRow9509 : Integer.Sparse Key := [(key2991, 2), (key2882, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2993, 2), (key2848, 2), (key2970, 2), (key2592, 2), (key2991, 2), (key2595, 2), (key2882, 2), (key2912, -2), (key3003, -2), (key2914, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2891, -2), (key2602, -2), (key2912, -2)]

theorem rawRowCheck9509 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form0 = rawRow9509 := by decide +kernel

def row9509 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9509 : row9509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9509 := by decide +kernel

theorem rowEval9509 (x : Key → ℝ) : Integer.Sparse.eval row9509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9509, Integer.Sparse.eval_collectBalanced, rawRowCheck9509]

def rawRow9510 : Integer.Sparse Key := [(key2991, 2), (key2993, 2), (key2882, 2), (key2970, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2848, 2), (key2991, 2), (key2592, 2), (key2882, 2), (key2595, 2), (key3003, -2), (key2912, -2), (key2914, -2), (key2996, -2), (key2891, -2), (key3003, -2), (key2602, -2), (key2914, -2), (key2603, -2), (key2891, -2), (key2912, -2), (key2602, -2)]

theorem rawRowCheck9510 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form0 = rawRow9510 := by decide +kernel

def row9510 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9510 : row9510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9510 := by decide +kernel

theorem rowEval9510 (x : Key → ℝ) : Integer.Sparse.eval row9510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9510, Integer.Sparse.eval_collectBalanced, rawRowCheck9510]

def rawRow9511 : Integer.Sparse Key := [(key2993, 2), (key2882, 2), (key2991, 2), (key2993, 2), (key2595, 2), (key2970, 2), (key2882, 2), (key2991, 2), (key2595, 2), (key2970, 2), (key2592, 2), (key2848, 2), (key2914, -2), (key3003, -2), (key2912, -2), (key2914, -2), (key3003, -2), (key2603, -2), (key2996, -2), (key2602, -2), (key2891, -2), (key2912, -2), (key2602, -2), (key2891, -2)]

theorem rawRowCheck9511 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form0 = rawRow9511 := by decide +kernel

def row9511 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9511 : row9511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9511 := by decide +kernel

theorem rowEval9511 (x : Key → ℝ) : Integer.Sparse.eval row9511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck9511, Integer.Sparse.eval_collectBalanced, rawRowCheck9511]

def rawRow9512 : Integer.Sparse Key := [(key2993, 2), (key2991, 2), (key2882, 2), (key2993, 2), (key2970, 2), (key2595, 2), (key2991, 2), (key2882, 2), (key2970, 2), (key2595, 2), (key2848, 2), (key2592, 2), (key3003, -2), (key2914, -2), (key2912, -2), (key3003, -2), (key2914, -2), (key2996, -2), (key2603, -2), (key2891, -2), (key2602, -2), (key2912, -2), (key2891, -2), (key2602, -2)]

theorem rawRowCheck9512 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form0 = rawRow9512 := by decide +kernel

def row9512 : Integer.Sparse Key := [(key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2848, 2), (key2882, 4), (key2891, -4), (key2912, -4), (key2914, -4), (key2970, 4), (key2991, 4), (key2993, 4), (key2996, -2), (key3003, -4)]

theorem rowCheck9512 : row9512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9512 := by decide +kernel

theorem rowEval9512 (x : Key → ℝ) : Integer.Sparse.eval row9512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9512, Integer.Sparse.eval_collectBalanced, rawRowCheck9512]

def rawRow9513 : Integer.Sparse Key := [(key2379, 2), (key2393, 2), (key2393, 2), (key2771, 2), (key2912, 2), (key2912, 2), (key2933, 2), (key2933, 2), (key2991, 2), (key2991, 2), (key3003, 2), (key3003, 2), (key2595, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2774, -2), (key2882, -2), (key2882, -2), (key2914, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2993, -2)]

theorem rawRowCheck9513 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form0 = rawRow9513 := by decide +kernel

def row9513 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2933, 4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

theorem rowCheck9513 : row9513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9513 := by decide +kernel

theorem rowEval9513 (x : Key → ℝ) : Integer.Sparse.eval row9513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9513, Integer.Sparse.eval_collectBalanced, rawRowCheck9513]

def rawRow9514 : Integer.Sparse Key := [(key2393, 2), (key2379, 2), (key2393, 2), (key2912, 2), (key2771, 2), (key2912, 2), (key2991, 2), (key3003, 2), (key2933, 2), (key3003, 2), (key2933, 2), (key2991, 2), (key2595, -2), (key2603, -2), (key2595, -2), (key2882, -2), (key2914, -2), (key2774, -2), (key2914, -2), (key2774, -2), (key2882, -2), (key2993, -2), (key2934, -2), (key2993, -2)]

theorem rawRowCheck9514 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form0 = rawRow9514 := by decide +kernel

def row9514 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2933, 4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

theorem rowCheck9514 : row9514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9514 := by decide +kernel

theorem rowEval9514 (x : Key → ℝ) : Integer.Sparse.eval row9514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9514, Integer.Sparse.eval_collectBalanced, rawRowCheck9514]

def rawRow9515 : Integer.Sparse Key := [(key2393, 2), (key2393, 2), (key2379, 2), (key2912, 2), (key2912, 2), (key2771, 2), (key3003, 2), (key2991, 2), (key3003, 2), (key2933, 2), (key2991, 2), (key2933, 2), (key2603, -2), (key2595, -2), (key2595, -2), (key2914, -2), (key2882, -2), (key2914, -2), (key2774, -2), (key2882, -2), (key2774, -2), (key2993, -2), (key2993, -2), (key2934, -2)]

theorem rawRowCheck9515 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form0 = rawRow9515 := by decide +kernel

def row9515 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2933, 4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

theorem rowCheck9515 : row9515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9515 := by decide +kernel

theorem rowEval9515 (x : Key → ℝ) : Integer.Sparse.eval row9515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9515, Integer.Sparse.eval_collectBalanced, rawRowCheck9515]

def rawRow9516 : Integer.Sparse Key := [(key2407, 2), (key2441, 2), (key2441, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2602, 2), (key2602, 2), (key2912, 2), (key2912, 2), (key3003, 2), (key3003, 2), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2914, -2)]

theorem rawRowCheck9516 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form0 = rawRow9516 := by decide +kernel

def row9516 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2592, 2), (key2595, -4), (key2602, 4), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

theorem rowCheck9516 : row9516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9516 := by decide +kernel

theorem rowEval9516 (x : Key → ℝ) : Integer.Sparse.eval row9516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9516, Integer.Sparse.eval_collectBalanced, rawRowCheck9516]

def rawRow9517 : Integer.Sparse Key := [(key2441, 2), (key2407, 2), (key2441, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2914, -2), (key2603, -2), (key2914, -2)]

theorem rawRowCheck9517 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form0 = rawRow9517 := by decide +kernel

def row9517 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2592, 2), (key2595, -4), (key2602, 4), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

theorem rowCheck9517 : row9517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9517 := by decide +kernel

theorem rowEval9517 (x : Key → ℝ) : Integer.Sparse.eval row9517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9517, Integer.Sparse.eval_collectBalanced, rawRowCheck9517]

def rawRow9518 : Integer.Sparse Key := [(key2441, 2), (key2441, 2), (key2407, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key3003, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2602, 2), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key2914, -2), (key2914, -2), (key2603, -2)]

theorem rawRowCheck9518 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form0 = rawRow9518 := by decide +kernel

def row9518 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2592, 2), (key2595, -4), (key2602, 4), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 4), (key2914, -4), (key2934, -2), (key2991, 4), (key2993, -4), (key3003, 4)]

theorem rowCheck9518 : row9518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9518 := by decide +kernel

theorem rowEval9518 (x : Key → ℝ) : Integer.Sparse.eval row9518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9518, Integer.Sparse.eval_collectBalanced, rawRowCheck9518]

def rawRow9519 : Integer.Sparse Key := [(key2544, 2), (key2555, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2565, 2), (key2379, 2), (key2393, 2), (key2771, 2), (key2912, 2), (key2933, 2), (key2991, 2), (key2882, -2), (key2914, -2), (key2993, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2595, -2), (key2774, -2), (key2882, -2)]

theorem rawRowCheck9519 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form0 = rawRow9519 := by decide +kernel

def row9519 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2441, 2), (key2544, 2), (key2555, 2), (key2565, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2933, 2), (key2934, -2), (key2991, 2), (key2993, -4)]

theorem rowCheck9519 : row9519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9519 := by decide +kernel

theorem rowEval9519 (x : Key → ℝ) : Integer.Sparse.eval row9519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9519, Integer.Sparse.eval_collectBalanced, rawRowCheck9519]

def rawRow9520 : Integer.Sparse Key := [(key2544, 2), (key2565, 2), (key2555, 2), (key2393, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2379, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2933, 2), (key2914, -2), (key2882, -2), (key2993, -2), (key2603, -2), (key2595, -2), (key2914, -2), (key2774, -2), (key2993, -2), (key2934, -2), (key2595, -2), (key2882, -2), (key2774, -2)]

theorem rawRowCheck9520 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form0 = rawRow9520 := by decide +kernel

def row9520 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2441, 2), (key2544, 2), (key2555, 2), (key2565, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2933, 2), (key2934, -2), (key2991, 2), (key2993, -4)]

theorem rowCheck9520 : row9520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9520 := by decide +kernel

theorem rowEval9520 (x : Key → ℝ) : Integer.Sparse.eval row9520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9520, Integer.Sparse.eval_collectBalanced, rawRowCheck9520]

def rawRow9521 : Integer.Sparse Key := [(key2555, 2), (key2544, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2565, 2), (key2407, 2), (key2441, 2), (key2592, 2), (key2991, 2), (key2602, 2), (key2912, 2), (key2882, -2), (key2993, -2), (key2914, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2774, -2), (key2595, -2), (key2882, -2)]

theorem rawRowCheck9521 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form0 = rawRow9521 := by decide +kernel

def row9521 : Integer.Sparse Key := [(key2393, 2), (key2407, 2), (key2441, 4), (key2544, 2), (key2555, 2), (key2565, 4), (key2592, 2), (key2595, -4), (key2602, 2), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2934, -2), (key2991, 2), (key2993, -4)]

theorem rowCheck9521 : row9521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9521 := by decide +kernel

theorem rowEval9521 (x : Key → ℝ) : Integer.Sparse.eval row9521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9521, Integer.Sparse.eval_collectBalanced, rawRowCheck9521]

def rawRow9522 : Integer.Sparse Key := [(key2555, 2), (key2565, 2), (key2544, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2407, 2), (key2991, 2), (key2592, 2), (key2912, 2), (key2602, 2), (key2993, -2), (key2882, -2), (key2914, -2), (key2934, -2), (key2774, -2), (key2993, -2), (key2595, -2), (key2914, -2), (key2603, -2), (key2774, -2), (key2882, -2), (key2595, -2)]

theorem rawRowCheck9522 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form0 = rawRow9522 := by decide +kernel

def row9522 : Integer.Sparse Key := [(key2393, 2), (key2407, 2), (key2441, 4), (key2544, 2), (key2555, 2), (key2565, 4), (key2592, 2), (key2595, -4), (key2602, 2), (key2603, -2), (key2774, -4), (key2882, -4), (key2912, 2), (key2914, -4), (key2934, -2), (key2991, 2), (key2993, -4)]

theorem rowCheck9522 : row9522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9522 := by decide +kernel

theorem rowEval9522 (x : Key → ℝ) : Integer.Sparse.eval row9522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9522, Integer.Sparse.eval_collectBalanced, rawRowCheck9522]

def rawRow9523 : Integer.Sparse Key := [(key2565, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2544, 2), (key2555, 2), (key2393, 2), (key2441, 2), (key2379, 2), (key2771, 2), (key2914, -2), (key2993, -2), (key2882, -2), (key2914, -2), (key2993, -2), (key2603, -2), (key2934, -2), (key2595, -2), (key2774, -2), (key2882, -2), (key2595, -2), (key2774, -2)]

theorem rawRowCheck9523 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form0 = rawRow9523 := by decide +kernel

def row9523 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2595, -4), (key2603, -2), (key2771, 2), (key2774, -4), (key2882, -4), (key2914, -4), (key2934, -2), (key2993, -4)]

theorem rowCheck9523 : row9523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9523 := by decide +kernel

theorem rowEval9523 (x : Key → ℝ) : Integer.Sparse.eval row9523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck9523, Integer.Sparse.eval_collectBalanced, rawRowCheck9523]

def rawRow9524 : Integer.Sparse Key := [(key2565, 2), (key2555, 2), (key2544, 2), (key2565, 2), (key2441, 2), (key2393, 2), (key2555, 2), (key2544, 2), (key2441, 2), (key2393, 2), (key2407, 2), (key2592, 2), (key2993, -2), (key2914, -2), (key2882, -2), (key2993, -2), (key2914, -2), (key2934, -2), (key2603, -2), (key2774, -2), (key2595, -2), (key2882, -2), (key2774, -2), (key2595, -2)]

theorem rawRowCheck9524 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form0 = rawRow9524 := by decide +kernel

def row9524 : Integer.Sparse Key := [(key2393, 4), (key2407, 2), (key2441, 4), (key2544, 4), (key2555, 4), (key2565, 4), (key2592, 2), (key2595, -4), (key2603, -2), (key2774, -4), (key2882, -4), (key2914, -4), (key2934, -2), (key2993, -4)]

theorem rowCheck9524 : row9524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9524 := by decide +kernel

theorem rowEval9524 (x : Key → ℝ) : Integer.Sparse.eval row9524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck9524, Integer.Sparse.eval_collectBalanced, rawRowCheck9524]

def rawRow9525 : Integer.Sparse Key := [(key1031, -24), (key996, 6), (key1109, 6), (key1188, 6), (key1188, 6)]

theorem rawRowCheck9525 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form1 = rawRow9525 := by decide +kernel

def row9525 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9525 : row9525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9525 := by decide +kernel

theorem rowEval9525 (x : Key → ℝ) : Integer.Sparse.eval row9525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9525, Integer.Sparse.eval_collectBalanced, rawRowCheck9525]

def rawRow9526 : Integer.Sparse Key := [(key1031, -24), (key996, 6), (key1188, 6), (key1109, 6), (key1188, 6)]

theorem rawRowCheck9526 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form1 = rawRow9526 := by decide +kernel

def row9526 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9526 : row9526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9526 := by decide +kernel

theorem rowEval9526 (x : Key → ℝ) : Integer.Sparse.eval row9526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9526, Integer.Sparse.eval_collectBalanced, rawRowCheck9526]

def rawRow9527 : Integer.Sparse Key := [(key1031, -24), (key996, 6), (key1188, 6), (key1188, 6), (key1109, 6)]

theorem rawRowCheck9527 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form1 = rawRow9527 := by decide +kernel

def row9527 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9527 : row9527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9527 := by decide +kernel

theorem rowEval9527 (x : Key → ℝ) : Integer.Sparse.eval row9527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9527, Integer.Sparse.eval_collectBalanced, rawRowCheck9527]

def rawRow9528 : Integer.Sparse Key := [(key1031, -24), (key1109, 6), (key996, 6), (key1188, 6), (key1188, 6)]

theorem rawRowCheck9528 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form1 = rawRow9528 := by decide +kernel

def row9528 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9528 : row9528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9528 := by decide +kernel

theorem rowEval9528 (x : Key → ℝ) : Integer.Sparse.eval row9528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9528, Integer.Sparse.eval_collectBalanced, rawRowCheck9528]

def rawRow9529 : Integer.Sparse Key := [(key1031, -24), (key1109, 6), (key1188, 6), (key996, 6), (key1188, 6)]

theorem rawRowCheck9529 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form1 = rawRow9529 := by decide +kernel

def row9529 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9529 : row9529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9529 := by decide +kernel

theorem rowEval9529 (x : Key → ℝ) : Integer.Sparse.eval row9529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9529, Integer.Sparse.eval_collectBalanced, rawRowCheck9529]

def rawRow9530 : Integer.Sparse Key := [(key1031, -24), (key1109, 6), (key1188, 6), (key1188, 6), (key996, 6)]

theorem rawRowCheck9530 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form1 = rawRow9530 := by decide +kernel

def row9530 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9530 : row9530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9530 := by decide +kernel

theorem rowEval9530 (x : Key → ℝ) : Integer.Sparse.eval row9530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9530, Integer.Sparse.eval_collectBalanced, rawRowCheck9530]

def rawRow9531 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key996, 6), (key1109, 6), (key1188, 6)]

theorem rawRowCheck9531 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form1 = rawRow9531 := by decide +kernel

def row9531 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9531 : row9531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9531 := by decide +kernel

theorem rowEval9531 (x : Key → ℝ) : Integer.Sparse.eval row9531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9531, Integer.Sparse.eval_collectBalanced, rawRowCheck9531]

def rawRow9532 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key996, 6), (key1188, 6), (key1109, 6)]

theorem rawRowCheck9532 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form1 = rawRow9532 := by decide +kernel

def row9532 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9532 : row9532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9532 := by decide +kernel

theorem rowEval9532 (x : Key → ℝ) : Integer.Sparse.eval row9532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9532, Integer.Sparse.eval_collectBalanced, rawRowCheck9532]

def rawRow9533 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1109, 6), (key996, 6), (key1188, 6)]

theorem rawRowCheck9533 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form1 = rawRow9533 := by decide +kernel

def row9533 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9533 : row9533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9533 := by decide +kernel

theorem rowEval9533 (x : Key → ℝ) : Integer.Sparse.eval row9533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9533, Integer.Sparse.eval_collectBalanced, rawRowCheck9533]

def rawRow9534 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1109, 6), (key1188, 6), (key996, 6)]

theorem rawRowCheck9534 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form1 = rawRow9534 := by decide +kernel

def row9534 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9534 : row9534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9534 := by decide +kernel

theorem rowEval9534 (x : Key → ℝ) : Integer.Sparse.eval row9534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9534, Integer.Sparse.eval_collectBalanced, rawRowCheck9534]

def rawRow9535 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1188, 6), (key996, 6), (key1109, 6)]

theorem rawRowCheck9535 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form1 = rawRow9535 := by decide +kernel

def row9535 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9535 : row9535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9535 := by decide +kernel

theorem rowEval9535 (x : Key → ℝ) : Integer.Sparse.eval row9535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck9535, Integer.Sparse.eval_collectBalanced, rawRowCheck9535]

def rawRow9536 : Integer.Sparse Key := [(key1031, -24), (key1188, 6), (key1188, 6), (key1109, 6), (key996, 6)]

theorem rawRowCheck9536 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form1 = rawRow9536 := by decide +kernel

def row9536 : Integer.Sparse Key := [(key996, 6), (key1031, -24), (key1109, 6), (key1188, 12)]

theorem rowCheck9536 : row9536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9536 := by decide +kernel

theorem rowEval9536 (x : Key → ℝ) : Integer.Sparse.eval row9536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9536, Integer.Sparse.eval_collectBalanced, rawRowCheck9536]

def rawRow9537 : Integer.Sparse Key := [(key1109, -24), (key996, 6), (key1031, 6), (key1188, 6), (key1188, 6)]

theorem rawRowCheck9537 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form1 = rawRow9537 := by decide +kernel

def row9537 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9537 : row9537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9537 := by decide +kernel

theorem rowEval9537 (x : Key → ℝ) : Integer.Sparse.eval row9537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9537, Integer.Sparse.eval_collectBalanced, rawRowCheck9537]

def rawRow9538 : Integer.Sparse Key := [(key1109, -24), (key996, 6), (key1188, 6), (key1031, 6), (key1188, 6)]

theorem rawRowCheck9538 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form1 = rawRow9538 := by decide +kernel

def row9538 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9538 : row9538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9538 := by decide +kernel

theorem rowEval9538 (x : Key → ℝ) : Integer.Sparse.eval row9538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9538, Integer.Sparse.eval_collectBalanced, rawRowCheck9538]

def rawRow9539 : Integer.Sparse Key := [(key1109, -24), (key996, 6), (key1188, 6), (key1188, 6), (key1031, 6)]

theorem rawRowCheck9539 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form1 = rawRow9539 := by decide +kernel

def row9539 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9539 : row9539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9539 := by decide +kernel

theorem rowEval9539 (x : Key → ℝ) : Integer.Sparse.eval row9539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9539, Integer.Sparse.eval_collectBalanced, rawRowCheck9539]

def rawRow9540 : Integer.Sparse Key := [(key1109, -24), (key1031, 6), (key996, 6), (key1188, 6), (key1188, 6)]

theorem rawRowCheck9540 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form1 = rawRow9540 := by decide +kernel

def row9540 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9540 : row9540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9540 := by decide +kernel

theorem rowEval9540 (x : Key → ℝ) : Integer.Sparse.eval row9540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9540, Integer.Sparse.eval_collectBalanced, rawRowCheck9540]

def rawRow9541 : Integer.Sparse Key := [(key1109, -24), (key1031, 6), (key1188, 6), (key996, 6), (key1188, 6)]

theorem rawRowCheck9541 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form1 = rawRow9541 := by decide +kernel

def row9541 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9541 : row9541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9541 := by decide +kernel

theorem rowEval9541 (x : Key → ℝ) : Integer.Sparse.eval row9541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9541, Integer.Sparse.eval_collectBalanced, rawRowCheck9541]

def rawRow9542 : Integer.Sparse Key := [(key1109, -24), (key1031, 6), (key1188, 6), (key1188, 6), (key996, 6)]

theorem rawRowCheck9542 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form1 = rawRow9542 := by decide +kernel

def row9542 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9542 : row9542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9542 := by decide +kernel

theorem rowEval9542 (x : Key → ℝ) : Integer.Sparse.eval row9542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9542, Integer.Sparse.eval_collectBalanced, rawRowCheck9542]

def rawRow9543 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key996, 6), (key1031, 6), (key1188, 6)]

theorem rawRowCheck9543 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form1 = rawRow9543 := by decide +kernel

def row9543 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9543 : row9543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9543 := by decide +kernel

theorem rowEval9543 (x : Key → ℝ) : Integer.Sparse.eval row9543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9543, Integer.Sparse.eval_collectBalanced, rawRowCheck9543]

def rawRow9544 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key996, 6), (key1188, 6), (key1031, 6)]

theorem rawRowCheck9544 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form1 = rawRow9544 := by decide +kernel

def row9544 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9544 : row9544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9544 := by decide +kernel

theorem rowEval9544 (x : Key → ℝ) : Integer.Sparse.eval row9544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9544, Integer.Sparse.eval_collectBalanced, rawRowCheck9544]

def rawRow9545 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1031, 6), (key996, 6), (key1188, 6)]

theorem rawRowCheck9545 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form1 = rawRow9545 := by decide +kernel

def row9545 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9545 : row9545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9545 := by decide +kernel

theorem rowEval9545 (x : Key → ℝ) : Integer.Sparse.eval row9545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9545, Integer.Sparse.eval_collectBalanced, rawRowCheck9545]

def rawRow9546 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1031, 6), (key1188, 6), (key996, 6)]

theorem rawRowCheck9546 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form1 = rawRow9546 := by decide +kernel

def row9546 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9546 : row9546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9546 := by decide +kernel

theorem rowEval9546 (x : Key → ℝ) : Integer.Sparse.eval row9546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9546, Integer.Sparse.eval_collectBalanced, rawRowCheck9546]

def rawRow9547 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1188, 6), (key996, 6), (key1031, 6)]

theorem rawRowCheck9547 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form1 = rawRow9547 := by decide +kernel

def row9547 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9547 : row9547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9547 := by decide +kernel

theorem rowEval9547 (x : Key → ℝ) : Integer.Sparse.eval row9547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck9547, Integer.Sparse.eval_collectBalanced, rawRowCheck9547]

def rawRow9548 : Integer.Sparse Key := [(key1109, -24), (key1188, 6), (key1188, 6), (key1031, 6), (key996, 6)]

theorem rawRowCheck9548 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form1 = rawRow9548 := by decide +kernel

def row9548 : Integer.Sparse Key := [(key996, 6), (key1031, 6), (key1109, -24), (key1188, 12)]

theorem rowCheck9548 : row9548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9548 := by decide +kernel

theorem rowEval9548 (x : Key → ℝ) : Integer.Sparse.eval row9548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck9548, Integer.Sparse.eval_collectBalanced, rawRowCheck9548]

def rawRow9549 : Integer.Sparse Key := [(key1033, -6), (key1033, -6), (key1041, -6), (key1076, -6), (key998, 2), (key998, 2), (key1006, 2), (key1111, 2), (key1111, 2), (key1190, 2), (key1190, 2), (key1193, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key1212, 2)]

theorem rawRowCheck9549 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form2 = rawRow9549 := by decide +kernel

def row9549 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9549 : row9549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9549 := by decide +kernel

theorem rowEval9549 (x : Key → ℝ) : Integer.Sparse.eval row9549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9549, Integer.Sparse.eval_collectBalanced, rawRowCheck9549]

def rawRow9550 : Integer.Sparse Key := [(key1033, -6), (key1041, -6), (key1033, -6), (key1076, -6), (key998, 2), (key1006, 2), (key998, 2), (key1190, 2), (key1193, 2), (key1111, 2), (key1193, 2), (key1111, 2), (key1190, 2), (key1212, 2), (key1155, 2), (key1212, 2)]

theorem rawRowCheck9550 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form2 = rawRow9550 := by decide +kernel

def row9550 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9550 : row9550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9550 := by decide +kernel

theorem rowEval9550 (x : Key → ℝ) : Integer.Sparse.eval row9550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9550, Integer.Sparse.eval_collectBalanced, rawRowCheck9550]

def rawRow9551 : Integer.Sparse Key := [(key1041, -6), (key1033, -6), (key1033, -6), (key1076, -6), (key1006, 2), (key998, 2), (key998, 2), (key1193, 2), (key1190, 2), (key1193, 2), (key1111, 2), (key1190, 2), (key1111, 2), (key1212, 2), (key1212, 2), (key1155, 2)]

theorem rawRowCheck9551 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form2 = rawRow9551 := by decide +kernel

def row9551 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9551 : row9551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9551 := by decide +kernel

theorem rowEval9551 (x : Key → ℝ) : Integer.Sparse.eval row9551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9551, Integer.Sparse.eval_collectBalanced, rawRowCheck9551]

def rawRow9552 : Integer.Sparse Key := [(key1033, -6), (key1033, -6), (key1076, -6), (key1041, -6), (key1111, 2), (key1111, 2), (key1155, 2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1193, 2)]

theorem rawRowCheck9552 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form2 = rawRow9552 := by decide +kernel

def row9552 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9552 : row9552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9552 := by decide +kernel

theorem rowEval9552 (x : Key → ℝ) : Integer.Sparse.eval row9552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9552, Integer.Sparse.eval_collectBalanced, rawRowCheck9552]

def rawRow9553 : Integer.Sparse Key := [(key1033, -6), (key1076, -6), (key1033, -6), (key1041, -6), (key1111, 2), (key1155, 2), (key1111, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1193, 2), (key1006, 2), (key1193, 2)]

theorem rawRowCheck9553 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form2 = rawRow9553 := by decide +kernel

def row9553 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9553 : row9553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9553 := by decide +kernel

theorem rowEval9553 (x : Key → ℝ) : Integer.Sparse.eval row9553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9553, Integer.Sparse.eval_collectBalanced, rawRowCheck9553]

def rawRow9554 : Integer.Sparse Key := [(key1076, -6), (key1033, -6), (key1033, -6), (key1041, -6), (key1155, 2), (key1111, 2), (key1111, 2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1193, 2), (key1193, 2), (key1006, 2)]

theorem rawRowCheck9554 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form2 = rawRow9554 := by decide +kernel

def row9554 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9554 : row9554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9554 := by decide +kernel

theorem rowEval9554 (x : Key → ℝ) : Integer.Sparse.eval row9554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9554, Integer.Sparse.eval_collectBalanced, rawRowCheck9554]

def rawRow9555 : Integer.Sparse Key := [(key1033, -6), (key1041, -6), (key1076, -6), (key1033, -6), (key1190, 2), (key1193, 2), (key1212, 2), (key998, 2), (key1006, 2), (key1111, 2), (key1193, 2), (key1155, 2), (key1212, 2), (key998, 2), (key1111, 2), (key1190, 2)]

theorem rawRowCheck9555 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form2 = rawRow9555 := by decide +kernel

def row9555 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9555 : row9555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9555 := by decide +kernel

theorem rowEval9555 (x : Key → ℝ) : Integer.Sparse.eval row9555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9555, Integer.Sparse.eval_collectBalanced, rawRowCheck9555]

def rawRow9556 : Integer.Sparse Key := [(key1041, -6), (key1033, -6), (key1076, -6), (key1033, -6), (key1193, 2), (key1190, 2), (key1212, 2), (key1006, 2), (key998, 2), (key1193, 2), (key1111, 2), (key1212, 2), (key1155, 2), (key998, 2), (key1190, 2), (key1111, 2)]

theorem rawRowCheck9556 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form2 = rawRow9556 := by decide +kernel

def row9556 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9556 : row9556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9556 := by decide +kernel

theorem rowEval9556 (x : Key → ℝ) : Integer.Sparse.eval row9556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9556, Integer.Sparse.eval_collectBalanced, rawRowCheck9556]

def rawRow9557 : Integer.Sparse Key := [(key1033, -6), (key1076, -6), (key1041, -6), (key1033, -6), (key1190, 2), (key1212, 2), (key1193, 2), (key1111, 2), (key1155, 2), (key998, 2), (key1212, 2), (key1006, 2), (key1193, 2), (key1111, 2), (key998, 2), (key1190, 2)]

theorem rawRowCheck9557 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form2 = rawRow9557 := by decide +kernel

def row9557 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9557 : row9557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9557 := by decide +kernel

theorem rowEval9557 (x : Key → ℝ) : Integer.Sparse.eval row9557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9557, Integer.Sparse.eval_collectBalanced, rawRowCheck9557]

def rawRow9558 : Integer.Sparse Key := [(key1076, -6), (key1033, -6), (key1041, -6), (key1033, -6), (key1212, 2), (key1190, 2), (key1193, 2), (key1155, 2), (key1111, 2), (key1212, 2), (key998, 2), (key1193, 2), (key1006, 2), (key1111, 2), (key1190, 2), (key998, 2)]

theorem rawRowCheck9558 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form2 = rawRow9558 := by decide +kernel

def row9558 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9558 : row9558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9558 := by decide +kernel

theorem rowEval9558 (x : Key → ℝ) : Integer.Sparse.eval row9558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9558, Integer.Sparse.eval_collectBalanced, rawRowCheck9558]

def rawRow9559 : Integer.Sparse Key := [(key1041, -6), (key1076, -6), (key1033, -6), (key1033, -6), (key1193, 2), (key1212, 2), (key1190, 2), (key1193, 2), (key1212, 2), (key1006, 2), (key1155, 2), (key998, 2), (key1111, 2), (key1190, 2), (key998, 2), (key1111, 2)]

theorem rawRowCheck9559 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form2 = rawRow9559 := by decide +kernel

def row9559 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9559 : row9559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9559 := by decide +kernel

theorem rowEval9559 (x : Key → ℝ) : Integer.Sparse.eval row9559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck9559, Integer.Sparse.eval_collectBalanced, rawRowCheck9559]

def rawRow9560 : Integer.Sparse Key := [(key1076, -6), (key1041, -6), (key1033, -6), (key1033, -6), (key1212, 2), (key1193, 2), (key1190, 2), (key1212, 2), (key1193, 2), (key1155, 2), (key1006, 2), (key1111, 2), (key998, 2), (key1190, 2), (key1111, 2), (key998, 2)]

theorem rawRowCheck9560 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form2 = rawRow9560 := by decide +kernel

def row9560 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1033, -12), (key1041, -6), (key1076, -6), (key1111, 4), (key1155, 2), (key1190, 4), (key1193, 4), (key1212, 4)]

theorem rowCheck9560 : row9560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9560 := by decide +kernel

theorem rowEval9560 (x : Key → ℝ) : Integer.Sparse.eval row9560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9560, Integer.Sparse.eval_collectBalanced, rawRowCheck9560]

def rawRow9561 : Integer.Sparse Key := [(key1111, -6), (key1111, -6), (key1127, -6), (key1155, -6), (key998, 2), (key998, 2), (key1019, 2), (key1033, 2), (key1033, 2), (key1190, 2), (key1190, 2), (key1199, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key1212, 2)]

theorem rawRowCheck9561 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form2 = rawRow9561 := by decide +kernel

def row9561 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9561 : row9561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9561 := by decide +kernel

theorem rowEval9561 (x : Key → ℝ) : Integer.Sparse.eval row9561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9561, Integer.Sparse.eval_collectBalanced, rawRowCheck9561]

def rawRow9562 : Integer.Sparse Key := [(key1111, -6), (key1127, -6), (key1111, -6), (key1155, -6), (key998, 2), (key1019, 2), (key998, 2), (key1190, 2), (key1199, 2), (key1033, 2), (key1199, 2), (key1033, 2), (key1190, 2), (key1212, 2), (key1076, 2), (key1212, 2)]

theorem rawRowCheck9562 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form2 = rawRow9562 := by decide +kernel

def row9562 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9562 : row9562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9562 := by decide +kernel

theorem rowEval9562 (x : Key → ℝ) : Integer.Sparse.eval row9562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9562, Integer.Sparse.eval_collectBalanced, rawRowCheck9562]

def rawRow9563 : Integer.Sparse Key := [(key1127, -6), (key1111, -6), (key1111, -6), (key1155, -6), (key1019, 2), (key998, 2), (key998, 2), (key1199, 2), (key1190, 2), (key1199, 2), (key1033, 2), (key1190, 2), (key1033, 2), (key1212, 2), (key1212, 2), (key1076, 2)]

theorem rawRowCheck9563 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form2 = rawRow9563 := by decide +kernel

def row9563 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9563 : row9563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9563 := by decide +kernel

theorem rowEval9563 (x : Key → ℝ) : Integer.Sparse.eval row9563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9563, Integer.Sparse.eval_collectBalanced, rawRowCheck9563]

def rawRow9564 : Integer.Sparse Key := [(key1111, -6), (key1111, -6), (key1155, -6), (key1127, -6), (key1033, 2), (key1033, 2), (key1076, 2), (key998, 2), (key998, 2), (key1190, 2), (key1190, 2), (key1212, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1199, 2)]

theorem rawRowCheck9564 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form2 = rawRow9564 := by decide +kernel

def row9564 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9564 : row9564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9564 := by decide +kernel

theorem rowEval9564 (x : Key → ℝ) : Integer.Sparse.eval row9564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9564, Integer.Sparse.eval_collectBalanced, rawRowCheck9564]

def rawRow9565 : Integer.Sparse Key := [(key1111, -6), (key1155, -6), (key1111, -6), (key1127, -6), (key1033, 2), (key1076, 2), (key1033, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1212, 2), (key998, 2), (key1190, 2), (key1199, 2), (key1019, 2), (key1199, 2)]

theorem rawRowCheck9565 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form2 = rawRow9565 := by decide +kernel

def row9565 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9565 : row9565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9565 := by decide +kernel

theorem rowEval9565 (x : Key → ℝ) : Integer.Sparse.eval row9565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9565, Integer.Sparse.eval_collectBalanced, rawRowCheck9565]

def rawRow9566 : Integer.Sparse Key := [(key1155, -6), (key1111, -6), (key1111, -6), (key1127, -6), (key1076, 2), (key1033, 2), (key1033, 2), (key1212, 2), (key1190, 2), (key1212, 2), (key998, 2), (key1190, 2), (key998, 2), (key1199, 2), (key1199, 2), (key1019, 2)]

theorem rawRowCheck9566 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form2 = rawRow9566 := by decide +kernel

def row9566 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9566 : row9566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9566 := by decide +kernel

theorem rowEval9566 (x : Key → ℝ) : Integer.Sparse.eval row9566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9566, Integer.Sparse.eval_collectBalanced, rawRowCheck9566]

def rawRow9567 : Integer.Sparse Key := [(key1111, -6), (key1127, -6), (key1155, -6), (key1111, -6), (key1190, 2), (key1199, 2), (key1212, 2), (key998, 2), (key1019, 2), (key1033, 2), (key1199, 2), (key1076, 2), (key1212, 2), (key998, 2), (key1033, 2), (key1190, 2)]

theorem rawRowCheck9567 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form2 = rawRow9567 := by decide +kernel

def row9567 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9567 : row9567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9567 := by decide +kernel

theorem rowEval9567 (x : Key → ℝ) : Integer.Sparse.eval row9567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9567, Integer.Sparse.eval_collectBalanced, rawRowCheck9567]

def rawRow9568 : Integer.Sparse Key := [(key1127, -6), (key1111, -6), (key1155, -6), (key1111, -6), (key1199, 2), (key1190, 2), (key1212, 2), (key1019, 2), (key998, 2), (key1199, 2), (key1033, 2), (key1212, 2), (key1076, 2), (key998, 2), (key1190, 2), (key1033, 2)]

theorem rawRowCheck9568 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form2 = rawRow9568 := by decide +kernel

def row9568 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9568 : row9568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9568 := by decide +kernel

theorem rowEval9568 (x : Key → ℝ) : Integer.Sparse.eval row9568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9568, Integer.Sparse.eval_collectBalanced, rawRowCheck9568]

def rawRow9569 : Integer.Sparse Key := [(key1111, -6), (key1155, -6), (key1127, -6), (key1111, -6), (key1190, 2), (key1212, 2), (key1199, 2), (key1033, 2), (key1076, 2), (key998, 2), (key1212, 2), (key1019, 2), (key1199, 2), (key1033, 2), (key998, 2), (key1190, 2)]

theorem rawRowCheck9569 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form2 = rawRow9569 := by decide +kernel

def row9569 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9569 : row9569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9569 := by decide +kernel

theorem rowEval9569 (x : Key → ℝ) : Integer.Sparse.eval row9569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9569, Integer.Sparse.eval_collectBalanced, rawRowCheck9569]

def rawRow9570 : Integer.Sparse Key := [(key1155, -6), (key1111, -6), (key1127, -6), (key1111, -6), (key1212, 2), (key1190, 2), (key1199, 2), (key1076, 2), (key1033, 2), (key1212, 2), (key998, 2), (key1199, 2), (key1019, 2), (key1033, 2), (key1190, 2), (key998, 2)]

theorem rawRowCheck9570 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form2 = rawRow9570 := by decide +kernel

def row9570 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9570 : row9570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9570 := by decide +kernel

theorem rowEval9570 (x : Key → ℝ) : Integer.Sparse.eval row9570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9570, Integer.Sparse.eval_collectBalanced, rawRowCheck9570]

def rawRow9571 : Integer.Sparse Key := [(key1127, -6), (key1155, -6), (key1111, -6), (key1111, -6), (key1199, 2), (key1212, 2), (key1190, 2), (key1199, 2), (key1212, 2), (key1019, 2), (key1076, 2), (key998, 2), (key1033, 2), (key1190, 2), (key998, 2), (key1033, 2)]

theorem rawRowCheck9571 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form2 = rawRow9571 := by decide +kernel

def row9571 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9571 : row9571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9571 := by decide +kernel

theorem rowEval9571 (x : Key → ℝ) : Integer.Sparse.eval row9571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck9571, Integer.Sparse.eval_collectBalanced, rawRowCheck9571]

def rawRow9572 : Integer.Sparse Key := [(key1155, -6), (key1127, -6), (key1111, -6), (key1111, -6), (key1212, 2), (key1199, 2), (key1190, 2), (key1212, 2), (key1199, 2), (key1076, 2), (key1019, 2), (key1033, 2), (key998, 2), (key1190, 2), (key1033, 2), (key998, 2)]

theorem rawRowCheck9572 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form2 = rawRow9572 := by decide +kernel

def row9572 : Integer.Sparse Key := [(key998, 4), (key1019, 2), (key1033, 4), (key1076, 2), (key1111, -12), (key1127, -6), (key1155, -6), (key1190, 4), (key1199, 4), (key1212, 4)]

theorem rowCheck9572 : row9572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9572 := by decide +kernel

theorem rowEval9572 (x : Key → ℝ) : Integer.Sparse.eval row9572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck9572, Integer.Sparse.eval_collectBalanced, rawRowCheck9572]

def rawRow9573 : Integer.Sparse Key := [(key2615, -6), (key2808, -6), (key2828, -6), (key2828, -6), (key2631, 2), (key2639, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2725, 2), (key2859, 2), (key2859, 2), (key2869, 2), (key2869, 2), (key2879, 2), (key2879, 2)]

theorem rawRowCheck9573 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form3 = rawRow9573 := by decide +kernel

def row9573 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9573 : row9573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9573 := by decide +kernel

theorem rowEval9573 (x : Key → ℝ) : Integer.Sparse.eval row9573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9573, Integer.Sparse.eval_collectBalanced, rawRowCheck9573]

def rawRow9574 : Integer.Sparse Key := [(key2615, -6), (key2828, -6), (key2808, -6), (key2828, -6), (key2639, 2), (key2631, 2), (key2639, 2), (key2725, 2), (key2705, 2), (key2725, 2), (key2869, 2), (key2879, 2), (key2859, 2), (key2879, 2), (key2859, 2), (key2869, 2)]

theorem rawRowCheck9574 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form3 = rawRow9574 := by decide +kernel

def row9574 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9574 : row9574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9574 := by decide +kernel

theorem rowEval9574 (x : Key → ℝ) : Integer.Sparse.eval row9574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9574, Integer.Sparse.eval_collectBalanced, rawRowCheck9574]

def rawRow9575 : Integer.Sparse Key := [(key2615, -6), (key2828, -6), (key2828, -6), (key2808, -6), (key2639, 2), (key2639, 2), (key2631, 2), (key2725, 2), (key2725, 2), (key2705, 2), (key2879, 2), (key2869, 2), (key2879, 2), (key2859, 2), (key2869, 2), (key2859, 2)]

theorem rawRowCheck9575 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form3 = rawRow9575 := by decide +kernel

def row9575 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9575 : row9575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9575 := by decide +kernel

theorem rowEval9575 (x : Key → ℝ) : Integer.Sparse.eval row9575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9575, Integer.Sparse.eval_collectBalanced, rawRowCheck9575]

def rawRow9576 : Integer.Sparse Key := [(key2808, -6), (key2615, -6), (key2828, -6), (key2828, -6), (key2705, 2), (key2859, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2869, 2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

theorem rawRowCheck9576 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form3 = rawRow9576 := by decide +kernel

def row9576 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9576 : row9576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9576 := by decide +kernel

theorem rowEval9576 (x : Key → ℝ) : Integer.Sparse.eval row9576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9576, Integer.Sparse.eval_collectBalanced, rawRowCheck9576]

def rawRow9577 : Integer.Sparse Key := [(key2808, -6), (key2828, -6), (key2615, -6), (key2828, -6), (key2859, 2), (key2705, 2), (key2859, 2), (key2869, 2), (key2631, 2), (key2869, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck9577 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form3 = rawRow9577 := by decide +kernel

def row9577 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9577 : row9577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9577 := by decide +kernel

theorem rowEval9577 (x : Key → ℝ) : Integer.Sparse.eval row9577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9577, Integer.Sparse.eval_collectBalanced, rawRowCheck9577]

def rawRow9578 : Integer.Sparse Key := [(key2808, -6), (key2828, -6), (key2828, -6), (key2615, -6), (key2859, 2), (key2859, 2), (key2705, 2), (key2869, 2), (key2869, 2), (key2631, 2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck9578 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form3 = rawRow9578 := by decide +kernel

def row9578 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9578 : row9578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9578 := by decide +kernel

theorem rowEval9578 (x : Key → ℝ) : Integer.Sparse.eval row9578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9578, Integer.Sparse.eval_collectBalanced, rawRowCheck9578]

def rawRow9579 : Integer.Sparse Key := [(key2828, -6), (key2615, -6), (key2808, -6), (key2828, -6), (key2725, 2), (key2869, 2), (key2879, 2), (key2639, 2), (key2859, 2), (key2879, 2), (key2631, 2), (key2639, 2), (key2705, 2), (key2725, 2), (key2859, 2), (key2869, 2)]

theorem rawRowCheck9579 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form3 = rawRow9579 := by decide +kernel

def row9579 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9579 : row9579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9579 := by decide +kernel

theorem rowEval9579 (x : Key → ℝ) : Integer.Sparse.eval row9579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9579, Integer.Sparse.eval_collectBalanced, rawRowCheck9579]

def rawRow9580 : Integer.Sparse Key := [(key2828, -6), (key2615, -6), (key2828, -6), (key2808, -6), (key2725, 2), (key2879, 2), (key2869, 2), (key2639, 2), (key2879, 2), (key2859, 2), (key2639, 2), (key2631, 2), (key2725, 2), (key2705, 2), (key2869, 2), (key2859, 2)]

theorem rawRowCheck9580 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form3 = rawRow9580 := by decide +kernel

def row9580 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9580 : row9580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9580 := by decide +kernel

theorem rowEval9580 (x : Key → ℝ) : Integer.Sparse.eval row9580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9580, Integer.Sparse.eval_collectBalanced, rawRowCheck9580]

def rawRow9581 : Integer.Sparse Key := [(key2828, -6), (key2808, -6), (key2615, -6), (key2828, -6), (key2869, 2), (key2725, 2), (key2879, 2), (key2859, 2), (key2639, 2), (key2879, 2), (key2705, 2), (key2859, 2), (key2631, 2), (key2869, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck9581 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form3 = rawRow9581 := by decide +kernel

def row9581 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9581 : row9581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9581 := by decide +kernel

theorem rowEval9581 (x : Key → ℝ) : Integer.Sparse.eval row9581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9581, Integer.Sparse.eval_collectBalanced, rawRowCheck9581]

def rawRow9582 : Integer.Sparse Key := [(key2828, -6), (key2808, -6), (key2828, -6), (key2615, -6), (key2869, 2), (key2879, 2), (key2725, 2), (key2859, 2), (key2879, 2), (key2639, 2), (key2859, 2), (key2705, 2), (key2869, 2), (key2631, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck9582 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form3 = rawRow9582 := by decide +kernel

def row9582 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9582 : row9582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9582 := by decide +kernel

theorem rowEval9582 (x : Key → ℝ) : Integer.Sparse.eval row9582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9582, Integer.Sparse.eval_collectBalanced, rawRowCheck9582]

def rawRow9583 : Integer.Sparse Key := [(key2828, -6), (key2828, -6), (key2615, -6), (key2808, -6), (key2879, 2), (key2725, 2), (key2869, 2), (key2879, 2), (key2639, 2), (key2859, 2), (key2725, 2), (key2869, 2), (key2639, 2), (key2859, 2), (key2631, 2), (key2705, 2)]

theorem rawRowCheck9583 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form3 = rawRow9583 := by decide +kernel

def row9583 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9583 : row9583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9583 := by decide +kernel

theorem rowEval9583 (x : Key → ℝ) : Integer.Sparse.eval row9583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck9583, Integer.Sparse.eval_collectBalanced, rawRowCheck9583]

def rawRow9584 : Integer.Sparse Key := [(key2828, -6), (key2828, -6), (key2808, -6), (key2615, -6), (key2879, 2), (key2869, 2), (key2725, 2), (key2879, 2), (key2859, 2), (key2639, 2), (key2869, 2), (key2725, 2), (key2859, 2), (key2639, 2), (key2705, 2), (key2631, 2)]

theorem rawRowCheck9584 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form3 = rawRow9584 := by decide +kernel

def row9584 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2705, 2), (key2725, 4), (key2808, -6), (key2828, -12), (key2859, 4), (key2869, 4), (key2879, 4)]

theorem rowCheck9584 : row9584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9584 := by decide +kernel

theorem rowEval9584 (x : Key → ℝ) : Integer.Sparse.eval row9584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9584, Integer.Sparse.eval_collectBalanced, rawRowCheck9584]

def rawRow9585 : Integer.Sparse Key := [(key2631, -6), (key2785, -6), (key2869, -6), (key2869, -6), (key2615, 2), (key2639, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2725, 2), (key2793, 2), (key2793, 2), (key2828, 2), (key2828, 2), (key2879, 2), (key2879, 2)]

theorem rawRowCheck9585 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form3 = rawRow9585 := by decide +kernel

def row9585 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9585 : row9585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9585 := by decide +kernel

theorem rowEval9585 (x : Key → ℝ) : Integer.Sparse.eval row9585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9585, Integer.Sparse.eval_collectBalanced, rawRowCheck9585]

def rawRow9586 : Integer.Sparse Key := [(key2631, -6), (key2869, -6), (key2785, -6), (key2869, -6), (key2639, 2), (key2615, 2), (key2639, 2), (key2725, 2), (key2670, 2), (key2725, 2), (key2828, 2), (key2879, 2), (key2793, 2), (key2879, 2), (key2793, 2), (key2828, 2)]

theorem rawRowCheck9586 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form3 = rawRow9586 := by decide +kernel

def row9586 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9586 : row9586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9586 := by decide +kernel

theorem rowEval9586 (x : Key → ℝ) : Integer.Sparse.eval row9586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9586, Integer.Sparse.eval_collectBalanced, rawRowCheck9586]

def rawRow9587 : Integer.Sparse Key := [(key2631, -6), (key2869, -6), (key2869, -6), (key2785, -6), (key2639, 2), (key2639, 2), (key2615, 2), (key2725, 2), (key2725, 2), (key2670, 2), (key2879, 2), (key2828, 2), (key2879, 2), (key2793, 2), (key2828, 2), (key2793, 2)]

theorem rawRowCheck9587 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form3 = rawRow9587 := by decide +kernel

def row9587 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9587 : row9587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9587 := by decide +kernel

theorem rowEval9587 (x : Key → ℝ) : Integer.Sparse.eval row9587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 1, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9587, Integer.Sparse.eval_collectBalanced, rawRowCheck9587]

def rawRow9588 : Integer.Sparse Key := [(key2785, -6), (key2631, -6), (key2869, -6), (key2869, -6), (key2670, 2), (key2793, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2828, 2), (key2639, 2), (key2639, 2), (key2725, 2), (key2725, 2), (key2879, 2), (key2879, 2)]

theorem rawRowCheck9588 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form3 = rawRow9588 := by decide +kernel

def row9588 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9588 : row9588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9588 := by decide +kernel

theorem rowEval9588 (x : Key → ℝ) : Integer.Sparse.eval row9588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9588, Integer.Sparse.eval_collectBalanced, rawRowCheck9588]

def rawRow9589 : Integer.Sparse Key := [(key2785, -6), (key2869, -6), (key2631, -6), (key2869, -6), (key2793, 2), (key2670, 2), (key2793, 2), (key2828, 2), (key2615, 2), (key2828, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2879, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck9589 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form3 = rawRow9589 := by decide +kernel

def row9589 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9589 : row9589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9589 := by decide +kernel

theorem rowEval9589 (x : Key → ℝ) : Integer.Sparse.eval row9589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9589, Integer.Sparse.eval_collectBalanced, rawRowCheck9589]

def rawRow9590 : Integer.Sparse Key := [(key2785, -6), (key2869, -6), (key2869, -6), (key2631, -6), (key2793, 2), (key2793, 2), (key2670, 2), (key2828, 2), (key2828, 2), (key2615, 2), (key2879, 2), (key2725, 2), (key2879, 2), (key2639, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck9590 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form3 = rawRow9590 := by decide +kernel

def row9590 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9590 : row9590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9590 := by decide +kernel

theorem rowEval9590 (x : Key → ℝ) : Integer.Sparse.eval row9590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9590, Integer.Sparse.eval_collectBalanced, rawRowCheck9590]

def rawRow9591 : Integer.Sparse Key := [(key2869, -6), (key2631, -6), (key2785, -6), (key2869, -6), (key2725, 2), (key2828, 2), (key2879, 2), (key2639, 2), (key2793, 2), (key2879, 2), (key2615, 2), (key2639, 2), (key2670, 2), (key2725, 2), (key2793, 2), (key2828, 2)]

theorem rawRowCheck9591 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form3 = rawRow9591 := by decide +kernel

def row9591 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9591 : row9591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9591 := by decide +kernel

theorem rowEval9591 (x : Key → ℝ) : Integer.Sparse.eval row9591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9591, Integer.Sparse.eval_collectBalanced, rawRowCheck9591]

def rawRow9592 : Integer.Sparse Key := [(key2869, -6), (key2631, -6), (key2869, -6), (key2785, -6), (key2725, 2), (key2879, 2), (key2828, 2), (key2639, 2), (key2879, 2), (key2793, 2), (key2639, 2), (key2615, 2), (key2725, 2), (key2670, 2), (key2828, 2), (key2793, 2)]

theorem rawRowCheck9592 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form3 = rawRow9592 := by decide +kernel

def row9592 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9592 : row9592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9592 := by decide +kernel

theorem rowEval9592 (x : Key → ℝ) : Integer.Sparse.eval row9592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9592, Integer.Sparse.eval_collectBalanced, rawRowCheck9592]

def rawRow9593 : Integer.Sparse Key := [(key2869, -6), (key2785, -6), (key2631, -6), (key2869, -6), (key2828, 2), (key2725, 2), (key2879, 2), (key2793, 2), (key2639, 2), (key2879, 2), (key2670, 2), (key2793, 2), (key2615, 2), (key2828, 2), (key2639, 2), (key2725, 2)]

theorem rawRowCheck9593 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form3 = rawRow9593 := by decide +kernel

def row9593 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9593 : row9593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9593 := by decide +kernel

theorem rowEval9593 (x : Key → ℝ) : Integer.Sparse.eval row9593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9593, Integer.Sparse.eval_collectBalanced, rawRowCheck9593]

def rawRow9594 : Integer.Sparse Key := [(key2869, -6), (key2785, -6), (key2869, -6), (key2631, -6), (key2828, 2), (key2879, 2), (key2725, 2), (key2793, 2), (key2879, 2), (key2639, 2), (key2793, 2), (key2670, 2), (key2828, 2), (key2615, 2), (key2725, 2), (key2639, 2)]

theorem rawRowCheck9594 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form3 = rawRow9594 := by decide +kernel

def row9594 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9594 : row9594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9594 := by decide +kernel

theorem rowEval9594 (x : Key → ℝ) : Integer.Sparse.eval row9594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9594, Integer.Sparse.eval_collectBalanced, rawRowCheck9594]

def rawRow9595 : Integer.Sparse Key := [(key2869, -6), (key2869, -6), (key2631, -6), (key2785, -6), (key2879, 2), (key2725, 2), (key2828, 2), (key2879, 2), (key2639, 2), (key2793, 2), (key2725, 2), (key2828, 2), (key2639, 2), (key2793, 2), (key2615, 2), (key2670, 2)]

theorem rawRowCheck9595 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form3 = rawRow9595 := by decide +kernel

def row9595 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9595 : row9595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9595 := by decide +kernel

theorem rowEval9595 (x : Key → ℝ) : Integer.Sparse.eval row9595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block3.form3) x := by
  rw [rowCheck9595, Integer.Sparse.eval_collectBalanced, rawRowCheck9595]

def rawRow9596 : Integer.Sparse Key := [(key2869, -6), (key2869, -6), (key2785, -6), (key2631, -6), (key2879, 2), (key2828, 2), (key2725, 2), (key2879, 2), (key2793, 2), (key2639, 2), (key2828, 2), (key2725, 2), (key2793, 2), (key2639, 2), (key2670, 2), (key2615, 2)]

theorem rawRowCheck9596 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form3 = rawRow9596 := by decide +kernel

def row9596 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, 2), (key2725, 4), (key2785, -6), (key2793, 4), (key2828, 4), (key2869, -12), (key2879, 4)]

theorem rowCheck9596 : row9596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9596 := by decide +kernel

theorem rowEval9596 (x : Key → ℝ) : Integer.Sparse.eval row9596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck9596, Integer.Sparse.eval_collectBalanced, rawRowCheck9596]

def rawRow9597 : Integer.Sparse Key := [(key2402, -6), (key2402, -6), (key2408, -6), (key2439, -6), (key2591, 2), (key2591, 2), (key2596, 2), (key2847, 2), (key2847, 2), (key2878, 2), (key2878, 2), (key2884, 2), (key2884, 2), (key3020, 2), (key3029, 2), (key3029, 2)]

theorem rawRowCheck9597 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form4 = rawRow9597 := by decide +kernel

def row9597 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9597 : row9597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9597 := by decide +kernel

theorem rowEval9597 (x : Key → ℝ) : Integer.Sparse.eval row9597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 1, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9597, Integer.Sparse.eval_collectBalanced, rawRowCheck9597]

def rawRow9598 : Integer.Sparse Key := [(key2402, -6), (key2408, -6), (key2402, -6), (key2439, -6), (key2591, 2), (key2596, 2), (key2591, 2), (key2878, 2), (key2884, 2), (key2847, 2), (key2884, 2), (key2847, 2), (key2878, 2), (key3029, 2), (key3020, 2), (key3029, 2)]

theorem rawRowCheck9598 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form4 = rawRow9598 := by decide +kernel

def row9598 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9598 : row9598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9598 := by decide +kernel

theorem rowEval9598 (x : Key → ℝ) : Integer.Sparse.eval row9598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 0, 1] GramFunctions.Block3.form4) x := by
  rw [rowCheck9598, Integer.Sparse.eval_collectBalanced, rawRowCheck9598]

def rawRow9599 : Integer.Sparse Key := [(key2408, -6), (key2402, -6), (key2402, -6), (key2439, -6), (key2596, 2), (key2591, 2), (key2591, 2), (key2884, 2), (key2878, 2), (key2884, 2), (key2847, 2), (key2878, 2), (key2847, 2), (key3029, 2), (key3029, 2), (key3020, 2)]

theorem rawRowCheck9599 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form4 = rawRow9599 := by decide +kernel

def row9599 : Integer.Sparse Key := [(key2402, -12), (key2408, -6), (key2439, -6), (key2591, 4), (key2596, 2), (key2847, 4), (key2878, 4), (key2884, 4), (key3020, 2), (key3029, 4)]

theorem rowCheck9599 : row9599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow9599 := by decide +kernel

theorem rowEval9599 (x : Key → ℝ) : Integer.Sparse.eval row9599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 1, 1, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck9599, Integer.Sparse.eval_collectBalanced, rawRowCheck9599]

end MUB6.Certificate.GramRows

end OAI
