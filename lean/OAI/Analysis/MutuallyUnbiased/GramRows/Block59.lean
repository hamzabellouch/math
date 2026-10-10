import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow4480 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2856, 2), (key2790, 2), (key2895, 2), (key2698, 2), (key2722, 2), (key2701, 2), (key2856, -2), (key2636, -2), (key2974, -2), (key2781, -2), (key2666, -2), (key2790, -2), (key2804, 2), (key2611, 2), (key2825, 2)]

theorem rawRowCheck4480 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form16 = rawRow4480 := by decide +kernel

def row4480 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

theorem rowCheck4480 : row4480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4480 := by decide +kernel

theorem rowEval4480 (x : Key → ℝ) : Integer.Sparse.eval row4480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4480, Integer.Sparse.eval_collectBalanced, rawRowCheck4480]

def rawRow4481 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2856, 2), (key2895, 2), (key2790, 2), (key2722, 2), (key2698, 2), (key2701, 2), (key2856, -2), (key2974, -2), (key2636, -2), (key2781, -2), (key2790, -2), (key2666, -2), (key2804, 2), (key2825, 2), (key2611, 2)]

theorem rawRowCheck4481 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form16 = rawRow4481 := by decide +kernel

def row4481 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

theorem rowCheck4481 : row4481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4481 := by decide +kernel

theorem rowEval4481 (x : Key → ℝ) : Integer.Sparse.eval row4481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4481, Integer.Sparse.eval_collectBalanced, rawRowCheck4481]

def rawRow4482 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2895, 2), (key2790, 2), (key2856, 2), (key2701, 2), (key2722, 2), (key2698, 2), (key2974, -2), (key2636, -2), (key2856, -2), (key2790, -2), (key2666, -2), (key2781, -2), (key2825, 2), (key2611, 2), (key2804, 2)]

theorem rawRowCheck4482 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form16 = rawRow4482 := by decide +kernel

def row4482 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

theorem rowCheck4482 : row4482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4482 := by decide +kernel

theorem rowEval4482 (x : Key → ℝ) : Integer.Sparse.eval row4482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4482, Integer.Sparse.eval_collectBalanced, rawRowCheck4482]

def rawRow4483 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2895, 2), (key2856, 2), (key2790, 2), (key2722, 2), (key2701, 2), (key2698, 2), (key2974, -2), (key2856, -2), (key2636, -2), (key2790, -2), (key2781, -2), (key2666, -2), (key2825, 2), (key2804, 2), (key2611, 2)]

theorem rawRowCheck4483 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form16 = rawRow4483 := by decide +kernel

def row4483 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

theorem rowCheck4483 : row4483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4483 := by decide +kernel

theorem rowEval4483 (x : Key → ℝ) : Integer.Sparse.eval row4483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4483, Integer.Sparse.eval_collectBalanced, rawRowCheck4483]

def rawRow4484 : Integer.Sparse Key := [(key2892, -2), (key2895, -2), (key2902, -2), (key2778, 2), (key2801, 2), (key2851, 2), (key2971, 2), (key2974, 2), (key2981, 2), (key2624, -2), (key2698, -2), (key2851, -2), (key2722, -2), (key2825, -2), (key2866, -2), (key2636, 2), (key2790, 2), (key2856, 2)]

theorem rawRowCheck4484 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form16 = rawRow4484 := by decide +kernel

def row4484 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck4484 : row4484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4484 := by decide +kernel

theorem rowEval4484 (x : Key → ℝ) : Integer.Sparse.eval row4484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4484, Integer.Sparse.eval_collectBalanced, rawRowCheck4484]

def rawRow4485 : Integer.Sparse Key := [(key2895, -2), (key2892, -2), (key2902, -2), (key2778, 2), (key2851, 2), (key2801, 2), (key2974, 2), (key2971, 2), (key2981, 2), (key2624, -2), (key2851, -2), (key2698, -2), (key2722, -2), (key2866, -2), (key2825, -2), (key2636, 2), (key2856, 2), (key2790, 2)]

theorem rawRowCheck4485 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form16 = rawRow4485 := by decide +kernel

def row4485 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck4485 : row4485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4485 := by decide +kernel

theorem rowEval4485 (x : Key → ℝ) : Integer.Sparse.eval row4485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4485, Integer.Sparse.eval_collectBalanced, rawRowCheck4485]

def rawRow4486 : Integer.Sparse Key := [(key2892, -2), (key2902, -2), (key2895, -2), (key2801, 2), (key2778, 2), (key2851, 2), (key2971, 2), (key2981, 2), (key2974, 2), (key2698, -2), (key2624, -2), (key2851, -2), (key2825, -2), (key2722, -2), (key2866, -2), (key2790, 2), (key2636, 2), (key2856, 2)]

theorem rawRowCheck4486 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form16 = rawRow4486 := by decide +kernel

def row4486 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck4486 : row4486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4486 := by decide +kernel

theorem rowEval4486 (x : Key → ℝ) : Integer.Sparse.eval row4486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4486, Integer.Sparse.eval_collectBalanced, rawRowCheck4486]

def rawRow4487 : Integer.Sparse Key := [(key2902, -2), (key2892, -2), (key2895, -2), (key2801, 2), (key2851, 2), (key2778, 2), (key2981, 2), (key2971, 2), (key2974, 2), (key2698, -2), (key2851, -2), (key2624, -2), (key2825, -2), (key2866, -2), (key2722, -2), (key2790, 2), (key2856, 2), (key2636, 2)]

theorem rawRowCheck4487 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form16 = rawRow4487 := by decide +kernel

def row4487 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck4487 : row4487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4487 := by decide +kernel

theorem rowEval4487 (x : Key → ℝ) : Integer.Sparse.eval row4487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4487, Integer.Sparse.eval_collectBalanced, rawRowCheck4487]

def rawRow4488 : Integer.Sparse Key := [(key2895, -2), (key2902, -2), (key2892, -2), (key2851, 2), (key2778, 2), (key2801, 2), (key2974, 2), (key2981, 2), (key2971, 2), (key2851, -2), (key2624, -2), (key2698, -2), (key2866, -2), (key2722, -2), (key2825, -2), (key2856, 2), (key2636, 2), (key2790, 2)]

theorem rawRowCheck4488 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form16 = rawRow4488 := by decide +kernel

def row4488 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck4488 : row4488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4488 := by decide +kernel

theorem rowEval4488 (x : Key → ℝ) : Integer.Sparse.eval row4488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4488, Integer.Sparse.eval_collectBalanced, rawRowCheck4488]

def rawRow4489 : Integer.Sparse Key := [(key2902, -2), (key2895, -2), (key2892, -2), (key2851, 2), (key2801, 2), (key2778, 2), (key2981, 2), (key2974, 2), (key2971, 2), (key2851, -2), (key2698, -2), (key2624, -2), (key2866, -2), (key2825, -2), (key2722, -2), (key2856, 2), (key2790, 2), (key2636, 2)]

theorem rawRowCheck4489 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form16 = rawRow4489 := by decide +kernel

def row4489 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

theorem rowCheck4489 : row4489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4489 := by decide +kernel

theorem rowEval4489 (x : Key → ℝ) : Integer.Sparse.eval row4489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4489, Integer.Sparse.eval_collectBalanced, rawRowCheck4489]

def rawRow4490 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2935, 2), (key2947, 2), (key2971, 2), (key2892, 2), (key2895, 2), (key2902, 2), (key2645, -2), (key2734, -2), (key2892, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, 2), (key2698, 2), (key2851, 2)]

theorem rawRowCheck4490 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form16 = rawRow4490 := by decide +kernel

def row4490 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck4490 : row4490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4490 := by decide +kernel

theorem rowEval4490 (x : Key → ℝ) : Integer.Sparse.eval row4490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4490, Integer.Sparse.eval_collectBalanced, rawRowCheck4490]

def rawRow4491 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2935, 2), (key2971, 2), (key2947, 2), (key2895, 2), (key2892, 2), (key2902, 2), (key2645, -2), (key2892, -2), (key2734, -2), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, 2), (key2851, 2), (key2698, 2)]

theorem rawRowCheck4491 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form16 = rawRow4491 := by decide +kernel

def row4491 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck4491 : row4491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4491 := by decide +kernel

theorem rowEval4491 (x : Key → ℝ) : Integer.Sparse.eval row4491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4491, Integer.Sparse.eval_collectBalanced, rawRowCheck4491]

def rawRow4492 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2947, 2), (key2935, 2), (key2971, 2), (key2892, 2), (key2902, 2), (key2895, 2), (key2734, -2), (key2645, -2), (key2892, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, 2), (key2624, 2), (key2851, 2)]

theorem rawRowCheck4492 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form16 = rawRow4492 := by decide +kernel

def row4492 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck4492 : row4492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4492 := by decide +kernel

theorem rowEval4492 (x : Key → ℝ) : Integer.Sparse.eval row4492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form16) x := by
  rw [rowCheck4492, Integer.Sparse.eval_collectBalanced, rawRowCheck4492]

def rawRow4493 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2947, 2), (key2971, 2), (key2935, 2), (key2902, 2), (key2892, 2), (key2895, 2), (key2734, -2), (key2892, -2), (key2645, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, 2), (key2851, 2), (key2624, 2)]

theorem rawRowCheck4493 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form16 = rawRow4493 := by decide +kernel

def row4493 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck4493 : row4493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4493 := by decide +kernel

theorem rowEval4493 (x : Key → ℝ) : Integer.Sparse.eval row4493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4493, Integer.Sparse.eval_collectBalanced, rawRowCheck4493]

def rawRow4494 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2971, 2), (key2935, 2), (key2947, 2), (key2895, 2), (key2902, 2), (key2892, 2), (key2892, -2), (key2645, -2), (key2734, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, 2), (key2624, 2), (key2698, 2)]

theorem rawRowCheck4494 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form16 = rawRow4494 := by decide +kernel

def row4494 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck4494 : row4494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4494 := by decide +kernel

theorem rowEval4494 (x : Key → ℝ) : Integer.Sparse.eval row4494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form16) x := by
  rw [rowCheck4494, Integer.Sparse.eval_collectBalanced, rawRowCheck4494]

def rawRow4495 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2971, 2), (key2947, 2), (key2935, 2), (key2902, 2), (key2895, 2), (key2892, 2), (key2892, -2), (key2734, -2), (key2645, -2), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, 2), (key2698, 2), (key2624, 2)]

theorem rawRowCheck4495 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form16 = rawRow4495 := by decide +kernel

def row4495 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

theorem rowCheck4495 : row4495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4495 := by decide +kernel

theorem rowEval4495 (x : Key → ℝ) : Integer.Sparse.eval row4495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4495, Integer.Sparse.eval_collectBalanced, rawRowCheck4495]

def rawRow4496 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1568, -1), (key1787, -1), (key1591, -1), (key1796, -1), (key1295, 2), (key1572, 2), (key1787, 2), (key1311, 1), (key1315, 1), (key1617, 1), (key1812, 1), (key1631, 1), (key1823, 1), (key1315, -1), (key1336, -1), (key1545, -1), (key1771, -1), (key1654, -1), (key1812, -1), (key1324, -2), (key1622, -2), (key1815, -2), (key1324, 1), (key1343, 1), (key1554, 1), (key1778, 1), (key1657, 1), (key1815, 1)]

theorem rawRowCheck4496 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form17 = rawRow4496 := by decide +kernel

def row4496 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4496 : row4496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4496 := by decide +kernel

theorem rowEval4496 (x : Key → ℝ) : Integer.Sparse.eval row4496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4496, Integer.Sparse.eval_collectBalanced, rawRowCheck4496]

def rawRow4497 : Integer.Sparse Key := [(key1295, -1), (key1291, -1), (key1787, -1), (key1568, -1), (key1796, -1), (key1591, -1), (key1295, 2), (key1787, 2), (key1572, 2), (key1315, 1), (key1311, 1), (key1812, 1), (key1617, 1), (key1823, 1), (key1631, 1), (key1336, -1), (key1315, -1), (key1771, -1), (key1545, -1), (key1812, -1), (key1654, -1), (key1324, -2), (key1815, -2), (key1622, -2), (key1343, 1), (key1324, 1), (key1778, 1), (key1554, 1), (key1815, 1), (key1657, 1)]

theorem rawRowCheck4497 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form17 = rawRow4497 := by decide +kernel

def row4497 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4497 : row4497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4497 := by decide +kernel

theorem rowEval4497 (x : Key → ℝ) : Integer.Sparse.eval row4497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4497, Integer.Sparse.eval_collectBalanced, rawRowCheck4497]

def rawRow4498 : Integer.Sparse Key := [(key1568, -1), (key1591, -1), (key1291, -1), (key1796, -1), (key1295, -1), (key1787, -1), (key1572, 2), (key1295, 2), (key1787, 2), (key1617, 1), (key1631, 1), (key1311, 1), (key1823, 1), (key1315, 1), (key1812, 1), (key1545, -1), (key1654, -1), (key1315, -1), (key1812, -1), (key1336, -1), (key1771, -1), (key1622, -2), (key1324, -2), (key1815, -2), (key1554, 1), (key1657, 1), (key1324, 1), (key1815, 1), (key1343, 1), (key1778, 1)]

theorem rawRowCheck4498 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form17 = rawRow4498 := by decide +kernel

def row4498 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4498 : row4498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4498 := by decide +kernel

theorem rowEval4498 (x : Key → ℝ) : Integer.Sparse.eval row4498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4498, Integer.Sparse.eval_collectBalanced, rawRowCheck4498]

def rawRow4499 : Integer.Sparse Key := [(key1591, -1), (key1568, -1), (key1796, -1), (key1291, -1), (key1787, -1), (key1295, -1), (key1572, 2), (key1787, 2), (key1295, 2), (key1631, 1), (key1617, 1), (key1823, 1), (key1311, 1), (key1812, 1), (key1315, 1), (key1654, -1), (key1545, -1), (key1812, -1), (key1315, -1), (key1771, -1), (key1336, -1), (key1622, -2), (key1815, -2), (key1324, -2), (key1657, 1), (key1554, 1), (key1815, 1), (key1324, 1), (key1778, 1), (key1343, 1)]

theorem rawRowCheck4499 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form17 = rawRow4499 := by decide +kernel

def row4499 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4499 : row4499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4499 := by decide +kernel

theorem rowEval4499 (x : Key → ℝ) : Integer.Sparse.eval row4499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4499, Integer.Sparse.eval_collectBalanced, rawRowCheck4499]

def rawRow4500 : Integer.Sparse Key := [(key1787, -1), (key1796, -1), (key1295, -1), (key1591, -1), (key1291, -1), (key1568, -1), (key1787, 2), (key1295, 2), (key1572, 2), (key1812, 1), (key1823, 1), (key1315, 1), (key1631, 1), (key1311, 1), (key1617, 1), (key1771, -1), (key1812, -1), (key1336, -1), (key1654, -1), (key1315, -1), (key1545, -1), (key1815, -2), (key1324, -2), (key1622, -2), (key1778, 1), (key1815, 1), (key1343, 1), (key1657, 1), (key1324, 1), (key1554, 1)]

theorem rawRowCheck4500 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form17 = rawRow4500 := by decide +kernel

def row4500 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4500 : row4500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4500 := by decide +kernel

theorem rowEval4500 (x : Key → ℝ) : Integer.Sparse.eval row4500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4500, Integer.Sparse.eval_collectBalanced, rawRowCheck4500]

def rawRow4501 : Integer.Sparse Key := [(key1796, -1), (key1787, -1), (key1591, -1), (key1295, -1), (key1568, -1), (key1291, -1), (key1787, 2), (key1572, 2), (key1295, 2), (key1823, 1), (key1812, 1), (key1631, 1), (key1315, 1), (key1617, 1), (key1311, 1), (key1812, -1), (key1771, -1), (key1654, -1), (key1336, -1), (key1545, -1), (key1315, -1), (key1815, -2), (key1622, -2), (key1324, -2), (key1815, 1), (key1778, 1), (key1657, 1), (key1343, 1), (key1554, 1), (key1324, 1)]

theorem rawRowCheck4501 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form17 = rawRow4501 := by decide +kernel

def row4501 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

theorem rowCheck4501 : row4501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4501 := by decide +kernel

theorem rowEval4501 (x : Key → ℝ) : Integer.Sparse.eval row4501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4501, Integer.Sparse.eval_collectBalanced, rawRowCheck4501]

def rawRow4502 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1572, -1), (key1572, -1), (key1591, -1), (key1591, -1), (key1291, 2), (key1568, 2), (key1568, 2), (key1336, 1), (key1336, 1), (key1654, 1), (key1654, 1), (key1665, 1), (key1665, 1), (key1311, -1), (key1311, -1), (key1541, -1), (key1541, -1), (key1617, -1), (key1617, -1), (key1343, -2), (key1657, -2), (key1657, -2), (key1324, 1), (key1324, 1), (key1554, 1), (key1554, 1), (key1622, 1), (key1622, 1)]

theorem rawRowCheck4502 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4502 := by decide +kernel

def row4502 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

theorem rowCheck4502 : row4502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4502 := by decide +kernel

theorem rowEval4502 (x : Key → ℝ) : Integer.Sparse.eval row4502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4502, Integer.Sparse.eval_collectBalanced, rawRowCheck4502]

def rawRow4503 : Integer.Sparse Key := [(key1572, -1), (key1591, -1), (key1295, -1), (key1591, -1), (key1295, -1), (key1572, -1), (key1568, 2), (key1291, 2), (key1568, 2), (key1654, 1), (key1665, 1), (key1336, 1), (key1665, 1), (key1336, 1), (key1654, 1), (key1541, -1), (key1617, -1), (key1311, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1657, -2), (key1343, -2), (key1657, -2), (key1554, 1), (key1622, 1), (key1324, 1), (key1622, 1), (key1324, 1), (key1554, 1)]

theorem rawRowCheck4503 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4503 := by decide +kernel

def row4503 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

theorem rowCheck4503 : row4503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4503 := by decide +kernel

theorem rowEval4503 (x : Key → ℝ) : Integer.Sparse.eval row4503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4503, Integer.Sparse.eval_collectBalanced, rawRowCheck4503]

def rawRow4504 : Integer.Sparse Key := [(key1591, -1), (key1572, -1), (key1591, -1), (key1295, -1), (key1572, -1), (key1295, -1), (key1568, 2), (key1568, 2), (key1291, 2), (key1665, 1), (key1654, 1), (key1665, 1), (key1336, 1), (key1654, 1), (key1336, 1), (key1617, -1), (key1541, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1311, -1), (key1657, -2), (key1657, -2), (key1343, -2), (key1622, 1), (key1554, 1), (key1622, 1), (key1324, 1), (key1554, 1), (key1324, 1)]

theorem rawRowCheck4504 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4504 := by decide +kernel

def row4504 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

theorem rowCheck4504 : row4504 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4504 := by decide +kernel

theorem rowEval4504 (x : Key → ℝ) : Integer.Sparse.eval row4504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4504, Integer.Sparse.eval_collectBalanced, rawRowCheck4504]

def rawRow4505 : Integer.Sparse Key := [(key1311, -1), (key1315, -1), (key1617, -1), (key1812, -1), (key1631, -1), (key1823, -1), (key1324, 2), (key1622, 2), (key1815, 2), (key1291, 1), (key1295, 1), (key1568, 1), (key1787, 1), (key1591, 1), (key1796, 1), (key1324, -1), (key1343, -1), (key1554, -1), (key1778, -1), (key1657, -1), (key1815, -1), (key1295, -2), (key1572, -2), (key1787, -2), (key1315, 1), (key1336, 1), (key1545, 1), (key1771, 1), (key1654, 1), (key1812, 1)]

theorem rawRowCheck4505 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form17 = rawRow4505 := by decide +kernel

def row4505 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4505 : row4505 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4505 := by decide +kernel

theorem rowEval4505 (x : Key → ℝ) : Integer.Sparse.eval row4505 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4505, Integer.Sparse.eval_collectBalanced, rawRowCheck4505]

def rawRow4506 : Integer.Sparse Key := [(key1315, -1), (key1311, -1), (key1812, -1), (key1617, -1), (key1823, -1), (key1631, -1), (key1324, 2), (key1815, 2), (key1622, 2), (key1295, 1), (key1291, 1), (key1787, 1), (key1568, 1), (key1796, 1), (key1591, 1), (key1343, -1), (key1324, -1), (key1778, -1), (key1554, -1), (key1815, -1), (key1657, -1), (key1295, -2), (key1787, -2), (key1572, -2), (key1336, 1), (key1315, 1), (key1771, 1), (key1545, 1), (key1812, 1), (key1654, 1)]

theorem rawRowCheck4506 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form17 = rawRow4506 := by decide +kernel

def row4506 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4506 : row4506 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4506 := by decide +kernel

theorem rowEval4506 (x : Key → ℝ) : Integer.Sparse.eval row4506 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4506, Integer.Sparse.eval_collectBalanced, rawRowCheck4506]

def rawRow4507 : Integer.Sparse Key := [(key1617, -1), (key1631, -1), (key1311, -1), (key1823, -1), (key1315, -1), (key1812, -1), (key1622, 2), (key1324, 2), (key1815, 2), (key1568, 1), (key1591, 1), (key1291, 1), (key1796, 1), (key1295, 1), (key1787, 1), (key1554, -1), (key1657, -1), (key1324, -1), (key1815, -1), (key1343, -1), (key1778, -1), (key1572, -2), (key1295, -2), (key1787, -2), (key1545, 1), (key1654, 1), (key1315, 1), (key1812, 1), (key1336, 1), (key1771, 1)]

theorem rawRowCheck4507 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form17 = rawRow4507 := by decide +kernel

def row4507 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4507 : row4507 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4507 := by decide +kernel

theorem rowEval4507 (x : Key → ℝ) : Integer.Sparse.eval row4507 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4507, Integer.Sparse.eval_collectBalanced, rawRowCheck4507]

def rawRow4508 : Integer.Sparse Key := [(key1631, -1), (key1617, -1), (key1823, -1), (key1311, -1), (key1812, -1), (key1315, -1), (key1622, 2), (key1815, 2), (key1324, 2), (key1591, 1), (key1568, 1), (key1796, 1), (key1291, 1), (key1787, 1), (key1295, 1), (key1657, -1), (key1554, -1), (key1815, -1), (key1324, -1), (key1778, -1), (key1343, -1), (key1572, -2), (key1787, -2), (key1295, -2), (key1654, 1), (key1545, 1), (key1812, 1), (key1315, 1), (key1771, 1), (key1336, 1)]

theorem rawRowCheck4508 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form17 = rawRow4508 := by decide +kernel

def row4508 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4508 : row4508 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4508 := by decide +kernel

theorem rowEval4508 (x : Key → ℝ) : Integer.Sparse.eval row4508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4508, Integer.Sparse.eval_collectBalanced, rawRowCheck4508]

def rawRow4509 : Integer.Sparse Key := [(key1812, -1), (key1823, -1), (key1315, -1), (key1631, -1), (key1311, -1), (key1617, -1), (key1815, 2), (key1324, 2), (key1622, 2), (key1787, 1), (key1796, 1), (key1295, 1), (key1591, 1), (key1291, 1), (key1568, 1), (key1778, -1), (key1815, -1), (key1343, -1), (key1657, -1), (key1324, -1), (key1554, -1), (key1787, -2), (key1295, -2), (key1572, -2), (key1771, 1), (key1812, 1), (key1336, 1), (key1654, 1), (key1315, 1), (key1545, 1)]

theorem rawRowCheck4509 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form17 = rawRow4509 := by decide +kernel

def row4509 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4509 : row4509 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4509 := by decide +kernel

theorem rowEval4509 (x : Key → ℝ) : Integer.Sparse.eval row4509 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4509, Integer.Sparse.eval_collectBalanced, rawRowCheck4509]

def rawRow4510 : Integer.Sparse Key := [(key1823, -1), (key1812, -1), (key1631, -1), (key1315, -1), (key1617, -1), (key1311, -1), (key1815, 2), (key1622, 2), (key1324, 2), (key1796, 1), (key1787, 1), (key1591, 1), (key1295, 1), (key1568, 1), (key1291, 1), (key1815, -1), (key1778, -1), (key1657, -1), (key1343, -1), (key1554, -1), (key1324, -1), (key1787, -2), (key1572, -2), (key1295, -2), (key1812, 1), (key1771, 1), (key1654, 1), (key1336, 1), (key1545, 1), (key1315, 1)]

theorem rawRowCheck4510 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form17 = rawRow4510 := by decide +kernel

def row4510 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

theorem rowCheck4510 : row4510 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4510 := by decide +kernel

theorem rowEval4510 (x : Key → ℝ) : Integer.Sparse.eval row4510 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4510, Integer.Sparse.eval_collectBalanced, rawRowCheck4510]

def rawRow4511 : Integer.Sparse Key := [(key1315, -1), (key1324, -1), (key1423, -1), (key1622, -1), (key1442, -1), (key1631, -1), (key1311, 2), (key1419, 2), (key1617, 2), (key1336, 1), (key1343, 1), (key1454, 1), (key1657, 1), (key1464, 1), (key1665, 1), (key1291, -1), (key1311, -1), (key1386, -1), (key1541, -1), (key1419, -1), (key1568, -1), (key1336, -2), (key1454, -2), (key1654, -2), (key1295, 1), (key1315, 1), (key1390, 1), (key1545, 1), (key1423, 1), (key1572, 1)]

theorem rawRowCheck4511 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form17 = rawRow4511 := by decide +kernel

def row4511 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

theorem rowCheck4511 : row4511 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4511 := by decide +kernel

theorem rowEval4511 (x : Key → ℝ) : Integer.Sparse.eval row4511 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4511, Integer.Sparse.eval_collectBalanced, rawRowCheck4511]

def rawRow4512 : Integer.Sparse Key := [(key1324, -1), (key1315, -1), (key1622, -1), (key1423, -1), (key1631, -1), (key1442, -1), (key1311, 2), (key1617, 2), (key1419, 2), (key1343, 1), (key1336, 1), (key1657, 1), (key1454, 1), (key1665, 1), (key1464, 1), (key1311, -1), (key1291, -1), (key1541, -1), (key1386, -1), (key1568, -1), (key1419, -1), (key1336, -2), (key1654, -2), (key1454, -2), (key1315, 1), (key1295, 1), (key1545, 1), (key1390, 1), (key1572, 1), (key1423, 1)]

theorem rawRowCheck4512 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form17 = rawRow4512 := by decide +kernel

def row4512 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

theorem rowCheck4512 : row4512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4512 := by decide +kernel

theorem rowEval4512 (x : Key → ℝ) : Integer.Sparse.eval row4512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4512, Integer.Sparse.eval_collectBalanced, rawRowCheck4512]

def rawRow4513 : Integer.Sparse Key := [(key1423, -1), (key1442, -1), (key1315, -1), (key1631, -1), (key1324, -1), (key1622, -1), (key1419, 2), (key1311, 2), (key1617, 2), (key1454, 1), (key1464, 1), (key1336, 1), (key1665, 1), (key1343, 1), (key1657, 1), (key1386, -1), (key1419, -1), (key1291, -1), (key1568, -1), (key1311, -1), (key1541, -1), (key1454, -2), (key1336, -2), (key1654, -2), (key1390, 1), (key1423, 1), (key1295, 1), (key1572, 1), (key1315, 1), (key1545, 1)]

theorem rawRowCheck4513 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form17 = rawRow4513 := by decide +kernel

def row4513 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

theorem rowCheck4513 : row4513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4513 := by decide +kernel

theorem rowEval4513 (x : Key → ℝ) : Integer.Sparse.eval row4513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4513, Integer.Sparse.eval_collectBalanced, rawRowCheck4513]

def rawRow4514 : Integer.Sparse Key := [(key1442, -1), (key1423, -1), (key1631, -1), (key1315, -1), (key1622, -1), (key1324, -1), (key1419, 2), (key1617, 2), (key1311, 2), (key1464, 1), (key1454, 1), (key1665, 1), (key1336, 1), (key1657, 1), (key1343, 1), (key1419, -1), (key1386, -1), (key1568, -1), (key1291, -1), (key1541, -1), (key1311, -1), (key1454, -2), (key1654, -2), (key1336, -2), (key1423, 1), (key1390, 1), (key1572, 1), (key1295, 1), (key1545, 1), (key1315, 1)]

theorem rawRowCheck4514 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form17 = rawRow4514 := by decide +kernel

def row4514 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

theorem rowCheck4514 : row4514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4514 := by decide +kernel

theorem rowEval4514 (x : Key → ℝ) : Integer.Sparse.eval row4514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4514, Integer.Sparse.eval_collectBalanced, rawRowCheck4514]

def rawRow4515 : Integer.Sparse Key := [(key1622, -1), (key1631, -1), (key1324, -1), (key1442, -1), (key1315, -1), (key1423, -1), (key1617, 2), (key1311, 2), (key1419, 2), (key1657, 1), (key1665, 1), (key1343, 1), (key1464, 1), (key1336, 1), (key1454, 1), (key1541, -1), (key1568, -1), (key1311, -1), (key1419, -1), (key1291, -1), (key1386, -1), (key1654, -2), (key1336, -2), (key1454, -2), (key1545, 1), (key1572, 1), (key1315, 1), (key1423, 1), (key1295, 1), (key1390, 1)]

theorem rawRowCheck4515 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form17 = rawRow4515 := by decide +kernel

def row4515 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

theorem rowCheck4515 : row4515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4515 := by decide +kernel

theorem rowEval4515 (x : Key → ℝ) : Integer.Sparse.eval row4515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4515, Integer.Sparse.eval_collectBalanced, rawRowCheck4515]

def rawRow4516 : Integer.Sparse Key := [(key1631, -1), (key1622, -1), (key1442, -1), (key1324, -1), (key1423, -1), (key1315, -1), (key1617, 2), (key1419, 2), (key1311, 2), (key1665, 1), (key1657, 1), (key1464, 1), (key1343, 1), (key1454, 1), (key1336, 1), (key1568, -1), (key1541, -1), (key1419, -1), (key1311, -1), (key1386, -1), (key1291, -1), (key1654, -2), (key1454, -2), (key1336, -2), (key1572, 1), (key1545, 1), (key1423, 1), (key1315, 1), (key1390, 1), (key1295, 1)]

theorem rawRowCheck4516 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form17 = rawRow4516 := by decide +kernel

def row4516 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

theorem rowCheck4516 : row4516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4516 := by decide +kernel

theorem rowEval4516 (x : Key → ℝ) : Integer.Sparse.eval row4516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4516, Integer.Sparse.eval_collectBalanced, rawRowCheck4516]

def rawRow4517 : Integer.Sparse Key := [(key1336, -1), (key1336, -1), (key1654, -1), (key1654, -1), (key1665, -1), (key1665, -1), (key1343, 2), (key1657, 2), (key1657, 2), (key1295, 1), (key1295, 1), (key1572, 1), (key1572, 1), (key1591, 1), (key1591, 1), (key1324, -1), (key1324, -1), (key1554, -1), (key1554, -1), (key1622, -1), (key1622, -1), (key1291, -2), (key1568, -2), (key1568, -2), (key1311, 1), (key1311, 1), (key1541, 1), (key1541, 1), (key1617, 1), (key1617, 1)]

theorem rawRowCheck4517 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form17 = rawRow4517 := by decide +kernel

def row4517 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

theorem rowCheck4517 : row4517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4517 := by decide +kernel

theorem rowEval4517 (x : Key → ℝ) : Integer.Sparse.eval row4517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4517, Integer.Sparse.eval_collectBalanced, rawRowCheck4517]

def rawRow4518 : Integer.Sparse Key := [(key1654, -1), (key1665, -1), (key1336, -1), (key1665, -1), (key1336, -1), (key1654, -1), (key1657, 2), (key1343, 2), (key1657, 2), (key1572, 1), (key1591, 1), (key1295, 1), (key1591, 1), (key1295, 1), (key1572, 1), (key1554, -1), (key1622, -1), (key1324, -1), (key1622, -1), (key1324, -1), (key1554, -1), (key1568, -2), (key1291, -2), (key1568, -2), (key1541, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1541, 1)]

theorem rawRowCheck4518 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form17 = rawRow4518 := by decide +kernel

def row4518 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

theorem rowCheck4518 : row4518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4518 := by decide +kernel

theorem rowEval4518 (x : Key → ℝ) : Integer.Sparse.eval row4518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4518, Integer.Sparse.eval_collectBalanced, rawRowCheck4518]

def rawRow4519 : Integer.Sparse Key := [(key1665, -1), (key1654, -1), (key1665, -1), (key1336, -1), (key1654, -1), (key1336, -1), (key1657, 2), (key1657, 2), (key1343, 2), (key1591, 1), (key1572, 1), (key1591, 1), (key1295, 1), (key1572, 1), (key1295, 1), (key1622, -1), (key1554, -1), (key1622, -1), (key1324, -1), (key1554, -1), (key1324, -1), (key1568, -2), (key1568, -2), (key1291, -2), (key1617, 1), (key1541, 1), (key1617, 1), (key1311, 1), (key1541, 1), (key1311, 1)]

theorem rawRowCheck4519 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form17 = rawRow4519 := by decide +kernel

def row4519 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

theorem rowCheck4519 : row4519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4519 := by decide +kernel

theorem rowEval4519 (x : Key → ℝ) : Integer.Sparse.eval row4519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4519, Integer.Sparse.eval_collectBalanced, rawRowCheck4519]

def rawRow4520 : Integer.Sparse Key := [(key1336, -1), (key1343, -1), (key1454, -1), (key1657, -1), (key1464, -1), (key1665, -1), (key1336, 2), (key1454, 2), (key1654, 2), (key1315, 1), (key1324, 1), (key1423, 1), (key1622, 1), (key1442, 1), (key1631, 1), (key1295, -1), (key1315, -1), (key1390, -1), (key1545, -1), (key1423, -1), (key1572, -1), (key1311, -2), (key1419, -2), (key1617, -2), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

theorem rawRowCheck4520 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form17 = rawRow4520 := by decide +kernel

def row4520 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

theorem rowCheck4520 : row4520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4520 := by decide +kernel

theorem rowEval4520 (x : Key → ℝ) : Integer.Sparse.eval row4520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4520, Integer.Sparse.eval_collectBalanced, rawRowCheck4520]

def rawRow4521 : Integer.Sparse Key := [(key1343, -1), (key1336, -1), (key1657, -1), (key1454, -1), (key1665, -1), (key1464, -1), (key1336, 2), (key1654, 2), (key1454, 2), (key1324, 1), (key1315, 1), (key1622, 1), (key1423, 1), (key1631, 1), (key1442, 1), (key1315, -1), (key1295, -1), (key1545, -1), (key1390, -1), (key1572, -1), (key1423, -1), (key1311, -2), (key1617, -2), (key1419, -2), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

theorem rawRowCheck4521 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form17 = rawRow4521 := by decide +kernel

def row4521 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

theorem rowCheck4521 : row4521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4521 := by decide +kernel

theorem rowEval4521 (x : Key → ℝ) : Integer.Sparse.eval row4521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4521, Integer.Sparse.eval_collectBalanced, rawRowCheck4521]

def rawRow4522 : Integer.Sparse Key := [(key1454, -1), (key1464, -1), (key1336, -1), (key1665, -1), (key1343, -1), (key1657, -1), (key1454, 2), (key1336, 2), (key1654, 2), (key1423, 1), (key1442, 1), (key1315, 1), (key1631, 1), (key1324, 1), (key1622, 1), (key1390, -1), (key1423, -1), (key1295, -1), (key1572, -1), (key1315, -1), (key1545, -1), (key1419, -2), (key1311, -2), (key1617, -2), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

theorem rawRowCheck4522 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form17 = rawRow4522 := by decide +kernel

def row4522 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

theorem rowCheck4522 : row4522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4522 := by decide +kernel

theorem rowEval4522 (x : Key → ℝ) : Integer.Sparse.eval row4522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form17) x := by
  rw [rowCheck4522, Integer.Sparse.eval_collectBalanced, rawRowCheck4522]

def rawRow4523 : Integer.Sparse Key := [(key1464, -1), (key1454, -1), (key1665, -1), (key1336, -1), (key1657, -1), (key1343, -1), (key1454, 2), (key1654, 2), (key1336, 2), (key1442, 1), (key1423, 1), (key1631, 1), (key1315, 1), (key1622, 1), (key1324, 1), (key1423, -1), (key1390, -1), (key1572, -1), (key1295, -1), (key1545, -1), (key1315, -1), (key1419, -2), (key1617, -2), (key1311, -2), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

theorem rawRowCheck4523 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form17 = rawRow4523 := by decide +kernel

def row4523 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

theorem rowCheck4523 : row4523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4523 := by decide +kernel

theorem rowEval4523 (x : Key → ℝ) : Integer.Sparse.eval row4523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4523, Integer.Sparse.eval_collectBalanced, rawRowCheck4523]

def rawRow4524 : Integer.Sparse Key := [(key1657, -1), (key1665, -1), (key1343, -1), (key1464, -1), (key1336, -1), (key1454, -1), (key1654, 2), (key1336, 2), (key1454, 2), (key1622, 1), (key1631, 1), (key1324, 1), (key1442, 1), (key1315, 1), (key1423, 1), (key1545, -1), (key1572, -1), (key1315, -1), (key1423, -1), (key1295, -1), (key1390, -1), (key1617, -2), (key1311, -2), (key1419, -2), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

theorem rawRowCheck4524 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form17 = rawRow4524 := by decide +kernel

def row4524 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

theorem rowCheck4524 : row4524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4524 := by decide +kernel

theorem rowEval4524 (x : Key → ℝ) : Integer.Sparse.eval row4524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form17) x := by
  rw [rowCheck4524, Integer.Sparse.eval_collectBalanced, rawRowCheck4524]

def rawRow4525 : Integer.Sparse Key := [(key1665, -1), (key1657, -1), (key1464, -1), (key1343, -1), (key1454, -1), (key1336, -1), (key1654, 2), (key1454, 2), (key1336, 2), (key1631, 1), (key1622, 1), (key1442, 1), (key1324, 1), (key1423, 1), (key1315, 1), (key1572, -1), (key1545, -1), (key1423, -1), (key1315, -1), (key1390, -1), (key1295, -1), (key1617, -2), (key1419, -2), (key1311, -2), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

theorem rawRowCheck4525 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form17 = rawRow4525 := by decide +kernel

def row4525 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

theorem rowCheck4525 : row4525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4525 := by decide +kernel

theorem rowEval4525 (x : Key → ℝ) : Integer.Sparse.eval row4525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form17) x := by
  rw [rowCheck4525, Integer.Sparse.eval_collectBalanced, rawRowCheck4525]

def rawRow4526 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1), (key2645, -2), (key2892, -2), (key2902, -2), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1)]

theorem rawRowCheck4526 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form18 = rawRow4526 := by decide +kernel

def row4526 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

theorem rowCheck4526 : row4526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4526 := by decide +kernel

theorem rowEval4526 (x : Key → ℝ) : Integer.Sparse.eval row4526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4526, Integer.Sparse.eval_collectBalanced, rawRowCheck4526]

def rawRow4527 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1), (key2645, -2), (key2902, -2), (key2892, -2), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1)]

theorem rawRowCheck4527 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form18 = rawRow4527 := by decide +kernel

def row4527 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

theorem rowCheck4527 : row4527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4527 := by decide +kernel

theorem rowEval4527 (x : Key → ℝ) : Integer.Sparse.eval row4527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4527, Integer.Sparse.eval_collectBalanced, rawRowCheck4527]

def rawRow4528 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2892, -2), (key2645, -2), (key2902, -2), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1)]

theorem rawRowCheck4528 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form18 = rawRow4528 := by decide +kernel

def row4528 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

theorem rowCheck4528 : row4528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4528 := by decide +kernel

theorem rowEval4528 (x : Key → ℝ) : Integer.Sparse.eval row4528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4528, Integer.Sparse.eval_collectBalanced, rawRowCheck4528]

def rawRow4529 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1), (key2892, -2), (key2902, -2), (key2645, -2), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1)]

theorem rawRowCheck4529 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form18 = rawRow4529 := by decide +kernel

def row4529 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

theorem rowCheck4529 : row4529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4529 := by decide +kernel

theorem rowEval4529 (x : Key → ℝ) : Integer.Sparse.eval row4529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4529, Integer.Sparse.eval_collectBalanced, rawRowCheck4529]

def rawRow4530 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1), (key2902, -2), (key2645, -2), (key2892, -2), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1)]

theorem rawRowCheck4530 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form18 = rawRow4530 := by decide +kernel

def row4530 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

theorem rowCheck4530 : row4530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4530 := by decide +kernel

theorem rowEval4530 (x : Key → ℝ) : Integer.Sparse.eval row4530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4530, Integer.Sparse.eval_collectBalanced, rawRowCheck4530]

def rawRow4531 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2902, -2), (key2892, -2), (key2645, -2), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

theorem rawRowCheck4531 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form18 = rawRow4531 := by decide +kernel

def row4531 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

theorem rowCheck4531 : row4531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4531 := by decide +kernel

theorem rowEval4531 (x : Key → ℝ) : Integer.Sparse.eval row4531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4531, Integer.Sparse.eval_collectBalanced, rawRowCheck4531]

def rawRow4532 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2651, -2), (key2895, -2), (key2895, -2), (key2645, 1), (key2645, 1), (key2734, 1), (key2734, 1), (key2892, 1), (key2892, 1)]

theorem rawRowCheck4532 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form18 = rawRow4532 := by decide +kernel

def row4532 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

theorem rowCheck4532 : row4532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4532 := by decide +kernel

theorem rowEval4532 (x : Key → ℝ) : Integer.Sparse.eval row4532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4532, Integer.Sparse.eval_collectBalanced, rawRowCheck4532]

def rawRow4533 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2895, -2), (key2651, -2), (key2895, -2), (key2734, 1), (key2892, 1), (key2645, 1), (key2892, 1), (key2645, 1), (key2734, 1)]

theorem rawRowCheck4533 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form18 = rawRow4533 := by decide +kernel

def row4533 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

theorem rowCheck4533 : row4533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4533 := by decide +kernel

theorem rowEval4533 (x : Key → ℝ) : Integer.Sparse.eval row4533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4533, Integer.Sparse.eval_collectBalanced, rawRowCheck4533]

def rawRow4534 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2895, -2), (key2895, -2), (key2651, -2), (key2892, 1), (key2734, 1), (key2892, 1), (key2645, 1), (key2734, 1), (key2645, 1)]

theorem rawRowCheck4534 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form18 = rawRow4534 := by decide +kernel

def row4534 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

theorem rowCheck4534 : row4534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4534 := by decide +kernel

theorem rowEval4534 (x : Key → ℝ) : Integer.Sparse.eval row4534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4534, Integer.Sparse.eval_collectBalanced, rawRowCheck4534]

def rawRow4535 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2636, 2), (key2856, 2), (key2974, 2), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1), (key2611, -2), (key2804, -2), (key2825, -2), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1)]

theorem rawRowCheck4535 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form18 = rawRow4535 := by decide +kernel

def row4535 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck4535 : row4535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4535 := by decide +kernel

theorem rowEval4535 (x : Key → ℝ) : Integer.Sparse.eval row4535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4535, Integer.Sparse.eval_collectBalanced, rawRowCheck4535]

def rawRow4536 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2636, 2), (key2974, 2), (key2856, 2), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1), (key2611, -2), (key2825, -2), (key2804, -2), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1)]

theorem rawRowCheck4536 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form18 = rawRow4536 := by decide +kernel

def row4536 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck4536 : row4536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4536 := by decide +kernel

theorem rowEval4536 (x : Key → ℝ) : Integer.Sparse.eval row4536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4536, Integer.Sparse.eval_collectBalanced, rawRowCheck4536]

def rawRow4537 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2856, 2), (key2636, 2), (key2974, 2), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2804, -2), (key2611, -2), (key2825, -2), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1)]

theorem rawRowCheck4537 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form18 = rawRow4537 := by decide +kernel

def row4537 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck4537 : row4537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4537 := by decide +kernel

theorem rowEval4537 (x : Key → ℝ) : Integer.Sparse.eval row4537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4537, Integer.Sparse.eval_collectBalanced, rawRowCheck4537]

def rawRow4538 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2856, 2), (key2974, 2), (key2636, 2), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1), (key2804, -2), (key2825, -2), (key2611, -2), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1)]

theorem rawRowCheck4538 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form18 = rawRow4538 := by decide +kernel

def row4538 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck4538 : row4538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4538 := by decide +kernel

theorem rowEval4538 (x : Key → ℝ) : Integer.Sparse.eval row4538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4538, Integer.Sparse.eval_collectBalanced, rawRowCheck4538]

def rawRow4539 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2974, 2), (key2636, 2), (key2856, 2), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1), (key2825, -2), (key2611, -2), (key2804, -2), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1)]

theorem rawRowCheck4539 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form18 = rawRow4539 := by decide +kernel

def row4539 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck4539 : row4539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4539 := by decide +kernel

theorem rowEval4539 (x : Key → ℝ) : Integer.Sparse.eval row4539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4539, Integer.Sparse.eval_collectBalanced, rawRowCheck4539]

def rawRow4540 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2974, 2), (key2856, 2), (key2636, 2), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, -2), (key2804, -2), (key2611, -2), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

theorem rawRowCheck4540 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form18 = rawRow4540 := by decide +kernel

def row4540 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck4540 : row4540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4540 := by decide +kernel

theorem rowEval4540 (x : Key → ℝ) : Integer.Sparse.eval row4540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4540, Integer.Sparse.eval_collectBalanced, rawRowCheck4540]

def rawRow4541 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2636, -2), (key2790, -2), (key2856, -2), (key2611, 1), (key2627, 1), (key2666, 1), (key2701, 1), (key2781, 1), (key2804, 1)]

theorem rawRowCheck4541 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form18 = rawRow4541 := by decide +kernel

def row4541 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

theorem rowCheck4541 : row4541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4541 := by decide +kernel

theorem rowEval4541 (x : Key → ℝ) : Integer.Sparse.eval row4541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4541, Integer.Sparse.eval_collectBalanced, rawRowCheck4541]

def rawRow4542 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2636, -2), (key2856, -2), (key2790, -2), (key2627, 1), (key2611, 1), (key2701, 1), (key2666, 1), (key2804, 1), (key2781, 1)]

theorem rawRowCheck4542 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form18 = rawRow4542 := by decide +kernel

def row4542 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

theorem rowCheck4542 : row4542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4542 := by decide +kernel

theorem rowEval4542 (x : Key → ℝ) : Integer.Sparse.eval row4542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4542, Integer.Sparse.eval_collectBalanced, rawRowCheck4542]

def rawRow4543 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2790, -2), (key2636, -2), (key2856, -2), (key2666, 1), (key2781, 1), (key2611, 1), (key2804, 1), (key2627, 1), (key2701, 1)]

theorem rawRowCheck4543 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form18 = rawRow4543 := by decide +kernel

def row4543 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

theorem rowCheck4543 : row4543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4543 := by decide +kernel

theorem rowEval4543 (x : Key → ℝ) : Integer.Sparse.eval row4543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4543, Integer.Sparse.eval_collectBalanced, rawRowCheck4543]

def rawRow4544 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2790, -2), (key2856, -2), (key2636, -2), (key2781, 1), (key2666, 1), (key2804, 1), (key2611, 1), (key2701, 1), (key2627, 1)]

theorem rawRowCheck4544 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form18 = rawRow4544 := by decide +kernel

def row4544 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

theorem rowCheck4544 : row4544 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4544 := by decide +kernel

theorem rowEval4544 (x : Key → ℝ) : Integer.Sparse.eval row4544 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4544, Integer.Sparse.eval_collectBalanced, rawRowCheck4544]

def rawRow4545 : Integer.Sparse Key := [(key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2856, -2), (key2636, -2), (key2790, -2), (key2701, 1), (key2804, 1), (key2627, 1), (key2781, 1), (key2611, 1), (key2666, 1)]

theorem rawRowCheck4545 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form18 = rawRow4545 := by decide +kernel

def row4545 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

theorem rowCheck4545 : row4545 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4545 := by decide +kernel

theorem rowEval4545 (x : Key → ℝ) : Integer.Sparse.eval row4545 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4545, Integer.Sparse.eval_collectBalanced, rawRowCheck4545]

def rawRow4546 : Integer.Sparse Key := [(key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2856, -2), (key2790, -2), (key2636, -2), (key2804, 1), (key2701, 1), (key2781, 1), (key2627, 1), (key2666, 1), (key2611, 1)]

theorem rawRowCheck4546 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form18 = rawRow4546 := by decide +kernel

def row4546 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

theorem rowCheck4546 : row4546 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4546 := by decide +kernel

theorem rowEval4546 (x : Key → ℝ) : Integer.Sparse.eval row4546 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4546, Integer.Sparse.eval_collectBalanced, rawRowCheck4546]

def rawRow4547 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2636, -1), (key2636, -1), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

theorem rawRowCheck4547 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form18 = rawRow4547 := by decide +kernel

def row4547 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

theorem rowCheck4547 : row4547 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4547 := by decide +kernel

theorem rowEval4547 (x : Key → ℝ) : Integer.Sparse.eval row4547 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4547, Integer.Sparse.eval_collectBalanced, rawRowCheck4547]

def rawRow4548 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2790, -1), (key2856, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck4548 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form18 = rawRow4548 := by decide +kernel

def row4548 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

theorem rowCheck4548 : row4548 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4548 := by decide +kernel

theorem rowEval4548 (x : Key → ℝ) : Integer.Sparse.eval row4548 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4548, Integer.Sparse.eval_collectBalanced, rawRowCheck4548]

def rawRow4549 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2856, -1), (key2790, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2636, -1), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck4549 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form18 = rawRow4549 := by decide +kernel

def row4549 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

theorem rowCheck4549 : row4549 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4549 := by decide +kernel

theorem rowEval4549 (x : Key → ℝ) : Integer.Sparse.eval row4549 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4549, Integer.Sparse.eval_collectBalanced, rawRowCheck4549]

def rawRow4550 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2645, 2), (key2734, 2), (key2892, 2), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1), (key2611, -1), (key2627, -1), (key2666, -1), (key2781, -1), (key2701, -1), (key2804, -1), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

theorem rawRowCheck4550 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form18 = rawRow4550 := by decide +kernel

def row4550 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck4550 : row4550 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4550 := by decide +kernel

theorem rowEval4550 (x : Key → ℝ) : Integer.Sparse.eval row4550 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4550, Integer.Sparse.eval_collectBalanced, rawRowCheck4550]

def rawRow4551 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2645, 2), (key2892, 2), (key2734, 2), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1), (key2627, -1), (key2611, -1), (key2781, -1), (key2666, -1), (key2804, -1), (key2701, -1), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

theorem rawRowCheck4551 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form18 = rawRow4551 := by decide +kernel

def row4551 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck4551 : row4551 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4551 := by decide +kernel

theorem rowEval4551 (x : Key → ℝ) : Integer.Sparse.eval row4551 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4551, Integer.Sparse.eval_collectBalanced, rawRowCheck4551]

def rawRow4552 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2734, 2), (key2645, 2), (key2892, 2), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2666, -1), (key2701, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

theorem rawRowCheck4552 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form18 = rawRow4552 := by decide +kernel

def row4552 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck4552 : row4552 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4552 := by decide +kernel

theorem rowEval4552 (x : Key → ℝ) : Integer.Sparse.eval row4552 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block1.form18) x := by
  rw [rowCheck4552, Integer.Sparse.eval_collectBalanced, rawRowCheck4552]

def rawRow4553 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2734, 2), (key2892, 2), (key2645, 2), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1), (key2701, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2781, -1), (key2627, -1), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

theorem rawRowCheck4553 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form18 = rawRow4553 := by decide +kernel

def row4553 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck4553 : row4553 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4553 := by decide +kernel

theorem rowEval4553 (x : Key → ℝ) : Integer.Sparse.eval row4553 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4553, Integer.Sparse.eval_collectBalanced, rawRowCheck4553]

def rawRow4554 : Integer.Sparse Key := [(key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2892, 2), (key2645, 2), (key2734, 2), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1), (key2781, -1), (key2804, -1), (key2627, -1), (key2701, -1), (key2611, -1), (key2666, -1), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

theorem rawRowCheck4554 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form18 = rawRow4554 := by decide +kernel

def row4554 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck4554 : row4554 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4554 := by decide +kernel

theorem rowEval4554 (x : Key → ℝ) : Integer.Sparse.eval row4554 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block1.form18) x := by
  rw [rowCheck4554, Integer.Sparse.eval_collectBalanced, rawRowCheck4554]

def rawRow4555 : Integer.Sparse Key := [(key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2892, 2), (key2734, 2), (key2645, 2), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2804, -1), (key2781, -1), (key2701, -1), (key2627, -1), (key2666, -1), (key2611, -1), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

theorem rawRowCheck4555 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form18 = rawRow4555 := by decide +kernel

def row4555 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

theorem rowCheck4555 : row4555 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4555 := by decide +kernel

theorem rowEval4555 (x : Key → ℝ) : Integer.Sparse.eval row4555 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block1.form18) x := by
  rw [rowCheck4555, Integer.Sparse.eval_collectBalanced, rawRowCheck4555]

def rawRow4556 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1519, -2), (key1492, 1), (key1496, 1), (key1492, 1), (key1519, 1), (key1496, 1), (key1519, 1), (key1718, 2), (key1718, 2), (key1747, 2), (key1718, -1), (key1728, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1747, -1), (key1863, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1880, -1), (key1863, 1), (key1870, 1), (key1863, 1), (key1880, 1), (key1870, 1), (key1880, 1)]

theorem rawRowCheck4556 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form0 = rawRow4556 := by decide +kernel

def row4556 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

theorem rowCheck4556 : row4556 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4556 := by decide +kernel

theorem rowEval4556 (x : Key → ℝ) : Integer.Sparse.eval row4556 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4556, Integer.Sparse.eval_collectBalanced, rawRowCheck4556]

def rawRow4557 : Integer.Sparse Key := [(key1492, -2), (key1519, -2), (key1492, -2), (key1496, 1), (key1492, 1), (key1519, 1), (key1492, 1), (key1519, 1), (key1496, 1), (key1718, 2), (key1747, 2), (key1718, 2), (key1728, -1), (key1718, -1), (key1747, -1), (key1718, -1), (key1747, -1), (key1728, -1), (key1865, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1865, -1), (key1870, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1870, 1)]

theorem rawRowCheck4557 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form0 = rawRow4557 := by decide +kernel

def row4557 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

theorem rowCheck4557 : row4557 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4557 := by decide +kernel

theorem rowEval4557 (x : Key → ℝ) : Integer.Sparse.eval row4557 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4557, Integer.Sparse.eval_collectBalanced, rawRowCheck4557]

def rawRow4558 : Integer.Sparse Key := [(key1519, -2), (key1492, -2), (key1492, -2), (key1519, 1), (key1519, 1), (key1496, 1), (key1496, 1), (key1492, 1), (key1492, 1), (key1747, 2), (key1718, 2), (key1718, 2), (key1747, -1), (key1747, -1), (key1728, -1), (key1728, -1), (key1718, -1), (key1718, -1), (key1880, -1), (key1880, -1), (key1865, -1), (key1865, -1), (key1863, -1), (key1863, -1), (key1880, 1), (key1880, 1), (key1870, 1), (key1870, 1), (key1863, 1), (key1863, 1)]

theorem rawRowCheck4558 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form0 = rawRow4558 := by decide +kernel

def row4558 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

theorem rowCheck4558 : row4558 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4558 := by decide +kernel

theorem rowEval4558 (x : Key → ℝ) : Integer.Sparse.eval row4558 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4558, Integer.Sparse.eval_collectBalanced, rawRowCheck4558]

def rawRow4559 : Integer.Sparse Key := [(key1496, -2), (key1496, -2), (key1496, -2), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1728, 2), (key1728, 2), (key1728, 2), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1)]

theorem rawRowCheck4559 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form0 = rawRow4559 := by decide +kernel

def row4559 : Integer.Sparse Key := [(key1492, 6), (key1496, -6), (key1718, -6), (key1728, 6), (key1865, 6), (key1870, -6)]

theorem rowCheck4559 : row4559 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4559 := by decide +kernel

theorem rowEval4559 (x : Key → ℝ) : Integer.Sparse.eval row4559 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4559, Integer.Sparse.eval_collectBalanced, rawRowCheck4559]

def rawRow4560 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1747, -2), (key1863, 1), (key1865, 1), (key1863, 1), (key1880, 1), (key1865, 1), (key1880, 1), (key1492, 2), (key1492, 2), (key1519, 2), (key1863, -1), (key1870, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1880, -1), (key1492, -1), (key1496, -1), (key1492, -1), (key1519, -1), (key1496, -1), (key1519, -1), (key1718, 1), (key1728, 1), (key1718, 1), (key1747, 1), (key1728, 1), (key1747, 1)]

theorem rawRowCheck4560 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form0 = rawRow4560 := by decide +kernel

def row4560 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

theorem rowCheck4560 : row4560 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4560 := by decide +kernel

theorem rowEval4560 (x : Key → ℝ) : Integer.Sparse.eval row4560 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck4560, Integer.Sparse.eval_collectBalanced, rawRowCheck4560]

def rawRow4561 : Integer.Sparse Key := [(key1718, -2), (key1747, -2), (key1718, -2), (key1865, 1), (key1863, 1), (key1880, 1), (key1863, 1), (key1880, 1), (key1865, 1), (key1492, 2), (key1519, 2), (key1492, 2), (key1870, -1), (key1863, -1), (key1880, -1), (key1863, -1), (key1880, -1), (key1870, -1), (key1496, -1), (key1492, -1), (key1519, -1), (key1492, -1), (key1519, -1), (key1496, -1), (key1728, 1), (key1718, 1), (key1747, 1), (key1718, 1), (key1747, 1), (key1728, 1)]

theorem rawRowCheck4561 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form0 = rawRow4561 := by decide +kernel

def row4561 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

theorem rowCheck4561 : row4561 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4561 := by decide +kernel

theorem rowEval4561 (x : Key → ℝ) : Integer.Sparse.eval row4561 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4561, Integer.Sparse.eval_collectBalanced, rawRowCheck4561]

def rawRow4562 : Integer.Sparse Key := [(key1747, -2), (key1718, -2), (key1718, -2), (key1880, 1), (key1880, 1), (key1865, 1), (key1865, 1), (key1863, 1), (key1863, 1), (key1519, 2), (key1492, 2), (key1492, 2), (key1880, -1), (key1880, -1), (key1870, -1), (key1870, -1), (key1863, -1), (key1863, -1), (key1519, -1), (key1519, -1), (key1496, -1), (key1496, -1), (key1492, -1), (key1492, -1), (key1747, 1), (key1747, 1), (key1728, 1), (key1728, 1), (key1718, 1), (key1718, 1)]

theorem rawRowCheck4562 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form0 = rawRow4562 := by decide +kernel

def row4562 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

theorem rowCheck4562 : row4562 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4562 := by decide +kernel

theorem rowEval4562 (x : Key → ℝ) : Integer.Sparse.eval row4562 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4562, Integer.Sparse.eval_collectBalanced, rawRowCheck4562]

def rawRow4563 : Integer.Sparse Key := [(key1370, -2), (key1865, -2), (key1865, -2), (key1366, 1), (key1366, 1), (key1718, 1), (key1718, 1), (key1863, 1), (key1863, 1), (key1379, 2), (key1870, 2), (key1870, 2), (key1366, -1), (key1366, -1), (key1492, -1), (key1492, -1), (key1863, -1), (key1863, -1), (key1379, -1), (key1379, -1), (key1728, -1), (key1728, -1), (key1870, -1), (key1870, -1), (key1370, 1), (key1370, 1), (key1496, 1), (key1496, 1), (key1865, 1), (key1865, 1)]

theorem rawRowCheck4563 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form0 = rawRow4563 := by decide +kernel

def row4563 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

theorem rowCheck4563 : row4563 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4563 := by decide +kernel

theorem rowEval4563 (x : Key → ℝ) : Integer.Sparse.eval row4563 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4563, Integer.Sparse.eval_collectBalanced, rawRowCheck4563]

def rawRow4564 : Integer.Sparse Key := [(key1865, -2), (key1370, -2), (key1865, -2), (key1718, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1718, 1), (key1870, 2), (key1379, 2), (key1870, 2), (key1492, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1728, -1), (key1870, -1), (key1379, -1), (key1870, -1), (key1379, -1), (key1728, -1), (key1496, 1), (key1865, 1), (key1370, 1), (key1865, 1), (key1370, 1), (key1496, 1)]

theorem rawRowCheck4564 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form0 = rawRow4564 := by decide +kernel

def row4564 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

theorem rowCheck4564 : row4564 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4564 := by decide +kernel

theorem rowEval4564 (x : Key → ℝ) : Integer.Sparse.eval row4564 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4564, Integer.Sparse.eval_collectBalanced, rawRowCheck4564]

def rawRow4565 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1370, -2), (key1863, 1), (key1718, 1), (key1863, 1), (key1366, 1), (key1718, 1), (key1366, 1), (key1870, 2), (key1870, 2), (key1379, 2), (key1863, -1), (key1492, -1), (key1863, -1), (key1366, -1), (key1492, -1), (key1366, -1), (key1870, -1), (key1728, -1), (key1870, -1), (key1379, -1), (key1728, -1), (key1379, -1), (key1865, 1), (key1496, 1), (key1865, 1), (key1370, 1), (key1496, 1), (key1370, 1)]

theorem rawRowCheck4565 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form0 = rawRow4565 := by decide +kernel

def row4565 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

theorem rowCheck4565 : row4565 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4565 := by decide +kernel

theorem rowEval4565 (x : Key → ℝ) : Integer.Sparse.eval row4565 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4565, Integer.Sparse.eval_collectBalanced, rawRowCheck4565]

def rawRow4566 : Integer.Sparse Key := [(key1728, -2), (key1728, -2), (key1728, -2), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1496, 2), (key1496, 2), (key1496, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1)]

theorem rawRowCheck4566 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form0 = rawRow4566 := by decide +kernel

def row4566 : Integer.Sparse Key := [(key1492, -6), (key1496, 6), (key1718, 6), (key1728, -6), (key1865, -6), (key1870, 6)]

theorem rowCheck4566 : row4566 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4566 := by decide +kernel

theorem rowEval4566 (x : Key → ℝ) : Integer.Sparse.eval row4566 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4566, Integer.Sparse.eval_collectBalanced, rawRowCheck4566]

def rawRow4567 : Integer.Sparse Key := [(key1379, -2), (key1870, -2), (key1870, -2), (key1379, 1), (key1379, 1), (key1728, 1), (key1728, 1), (key1870, 1), (key1870, 1), (key1370, 2), (key1865, 2), (key1865, 2), (key1370, -1), (key1370, -1), (key1496, -1), (key1496, -1), (key1865, -1), (key1865, -1), (key1366, -1), (key1366, -1), (key1718, -1), (key1718, -1), (key1863, -1), (key1863, -1), (key1366, 1), (key1366, 1), (key1492, 1), (key1492, 1), (key1863, 1), (key1863, 1)]

theorem rawRowCheck4567 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form0 = rawRow4567 := by decide +kernel

def row4567 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

theorem rowCheck4567 : row4567 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4567 := by decide +kernel

theorem rowEval4567 (x : Key → ℝ) : Integer.Sparse.eval row4567 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4567, Integer.Sparse.eval_collectBalanced, rawRowCheck4567]

def rawRow4568 : Integer.Sparse Key := [(key1870, -2), (key1379, -2), (key1870, -2), (key1728, 1), (key1870, 1), (key1379, 1), (key1870, 1), (key1379, 1), (key1728, 1), (key1865, 2), (key1370, 2), (key1865, 2), (key1496, -1), (key1865, -1), (key1370, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1718, -1), (key1863, -1), (key1366, -1), (key1863, -1), (key1366, -1), (key1718, -1), (key1492, 1), (key1863, 1), (key1366, 1), (key1863, 1), (key1366, 1), (key1492, 1)]

theorem rawRowCheck4568 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form0 = rawRow4568 := by decide +kernel

def row4568 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

theorem rowCheck4568 : row4568 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4568 := by decide +kernel

theorem rowEval4568 (x : Key → ℝ) : Integer.Sparse.eval row4568 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck4568, Integer.Sparse.eval_collectBalanced, rawRowCheck4568]

def rawRow4569 : Integer.Sparse Key := [(key1870, -2), (key1870, -2), (key1379, -2), (key1870, 1), (key1728, 1), (key1870, 1), (key1379, 1), (key1728, 1), (key1379, 1), (key1865, 2), (key1865, 2), (key1370, 2), (key1865, -1), (key1496, -1), (key1865, -1), (key1370, -1), (key1496, -1), (key1370, -1), (key1863, -1), (key1718, -1), (key1863, -1), (key1366, -1), (key1718, -1), (key1366, -1), (key1863, 1), (key1492, 1), (key1863, 1), (key1366, 1), (key1492, 1), (key1366, 1)]

theorem rawRowCheck4569 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form0 = rawRow4569 := by decide +kernel

def row4569 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

theorem rowCheck4569 : row4569 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4569 := by decide +kernel

theorem rowEval4569 (x : Key → ℝ) : Integer.Sparse.eval row4569 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck4569, Integer.Sparse.eval_collectBalanced, rawRowCheck4569]

def rawRow4570 : Integer.Sparse Key := [(key281, -6), (key281, 2), (key281, 2), (key290, 2), (key350, 6), (key350, -2), (key350, -2), (key367, -2), (key507, -2), (key507, -2), (key516, -2), (key507, 2), (key507, 2), (key538, 2)]

theorem rawRowCheck4570 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form1 = rawRow4570 := by decide +kernel

def row4570 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

theorem rowCheck4570 : row4570 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4570 := by decide +kernel

theorem rowEval4570 (x : Key → ℝ) : Integer.Sparse.eval row4570 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4570, Integer.Sparse.eval_collectBalanced, rawRowCheck4570]

def rawRow4571 : Integer.Sparse Key := [(key281, -6), (key281, 2), (key290, 2), (key281, 2), (key350, 6), (key350, -2), (key367, -2), (key350, -2), (key507, -2), (key516, -2), (key507, -2), (key507, 2), (key538, 2), (key507, 2)]

theorem rawRowCheck4571 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form1 = rawRow4571 := by decide +kernel

def row4571 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

theorem rowCheck4571 : row4571 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4571 := by decide +kernel

theorem rowEval4571 (x : Key → ℝ) : Integer.Sparse.eval row4571 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4571, Integer.Sparse.eval_collectBalanced, rawRowCheck4571]

def rawRow4572 : Integer.Sparse Key := [(key281, -6), (key290, 2), (key281, 2), (key281, 2), (key350, 6), (key367, -2), (key350, -2), (key350, -2), (key516, -2), (key507, -2), (key507, -2), (key538, 2), (key507, 2), (key507, 2)]

theorem rawRowCheck4572 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form1 = rawRow4572 := by decide +kernel

def row4572 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

theorem rowCheck4572 : row4572 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4572 := by decide +kernel

theorem rowEval4572 (x : Key → ℝ) : Integer.Sparse.eval row4572 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4572, Integer.Sparse.eval_collectBalanced, rawRowCheck4572]

def rawRow4573 : Integer.Sparse Key := [(key290, -6), (key281, 2), (key281, 2), (key281, 2), (key367, 6), (key350, -2), (key350, -2), (key350, -2), (key538, -2), (key538, -2), (key538, -2), (key516, 2), (key516, 2), (key516, 2)]

theorem rawRowCheck4573 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form1 = rawRow4573 := by decide +kernel

def row4573 : Integer.Sparse Key := [(key281, 6), (key290, -6), (key350, -6), (key367, 6), (key516, 6), (key538, -6)]

theorem rowCheck4573 : row4573 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4573 := by decide +kernel

theorem rowEval4573 (x : Key → ℝ) : Integer.Sparse.eval row4573 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4573, Integer.Sparse.eval_collectBalanced, rawRowCheck4573]

def rawRow4574 : Integer.Sparse Key := [(key350, -6), (key507, 2), (key507, 2), (key516, 2), (key281, 6), (key507, -2), (key507, -2), (key538, -2), (key281, -2), (key281, -2), (key290, -2), (key350, 2), (key350, 2), (key367, 2)]

theorem rawRowCheck4574 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form1 = rawRow4574 := by decide +kernel

def row4574 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

theorem rowCheck4574 : row4574 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4574 := by decide +kernel

theorem rowEval4574 (x : Key → ℝ) : Integer.Sparse.eval row4574 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck4574, Integer.Sparse.eval_collectBalanced, rawRowCheck4574]

def rawRow4575 : Integer.Sparse Key := [(key350, -6), (key507, 2), (key516, 2), (key507, 2), (key281, 6), (key507, -2), (key538, -2), (key507, -2), (key281, -2), (key290, -2), (key281, -2), (key350, 2), (key367, 2), (key350, 2)]

theorem rawRowCheck4575 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form1 = rawRow4575 := by decide +kernel

def row4575 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

theorem rowCheck4575 : row4575 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4575 := by decide +kernel

theorem rowEval4575 (x : Key → ℝ) : Integer.Sparse.eval row4575 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4575, Integer.Sparse.eval_collectBalanced, rawRowCheck4575]

def rawRow4576 : Integer.Sparse Key := [(key350, -6), (key516, 2), (key507, 2), (key507, 2), (key281, 6), (key538, -2), (key507, -2), (key507, -2), (key290, -2), (key281, -2), (key281, -2), (key367, 2), (key350, 2), (key350, 2)]

theorem rawRowCheck4576 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form1 = rawRow4576 := by decide +kernel

def row4576 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

theorem rowCheck4576 : row4576 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4576 := by decide +kernel

theorem rowEval4576 (x : Key → ℝ) : Integer.Sparse.eval row4576 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4576, Integer.Sparse.eval_collectBalanced, rawRowCheck4576]

def rawRow4577 : Integer.Sparse Key := [(key516, -6), (key350, 2), (key507, 2), (key507, 2), (key538, 6), (key281, -2), (key507, -2), (key507, -2), (key367, -2), (key538, -2), (key538, -2), (key290, 2), (key516, 2), (key516, 2)]

theorem rawRowCheck4577 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow4577 := by decide +kernel

def row4577 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

theorem rowCheck4577 : row4577 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4577 := by decide +kernel

theorem rowEval4577 (x : Key → ℝ) : Integer.Sparse.eval row4577 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4577, Integer.Sparse.eval_collectBalanced, rawRowCheck4577]

def rawRow4578 : Integer.Sparse Key := [(key516, -6), (key507, 2), (key350, 2), (key507, 2), (key538, 6), (key507, -2), (key281, -2), (key507, -2), (key538, -2), (key367, -2), (key538, -2), (key516, 2), (key290, 2), (key516, 2)]

theorem rawRowCheck4578 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow4578 := by decide +kernel

def row4578 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

theorem rowCheck4578 : row4578 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4578 := by decide +kernel

theorem rowEval4578 (x : Key → ℝ) : Integer.Sparse.eval row4578 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4578, Integer.Sparse.eval_collectBalanced, rawRowCheck4578]

def rawRow4579 : Integer.Sparse Key := [(key516, -6), (key507, 2), (key507, 2), (key350, 2), (key538, 6), (key507, -2), (key507, -2), (key281, -2), (key538, -2), (key538, -2), (key367, -2), (key516, 2), (key516, 2), (key290, 2)]

theorem rawRowCheck4579 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow4579 := by decide +kernel

def row4579 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

theorem rowCheck4579 : row4579 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4579 := by decide +kernel

theorem rowEval4579 (x : Key → ℝ) : Integer.Sparse.eval row4579 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4579, Integer.Sparse.eval_collectBalanced, rawRowCheck4579]

def rawRow4580 : Integer.Sparse Key := [(key367, -6), (key538, 2), (key538, 2), (key538, 2), (key290, 6), (key516, -2), (key516, -2), (key516, -2), (key281, -2), (key281, -2), (key281, -2), (key350, 2), (key350, 2), (key350, 2)]

theorem rawRowCheck4580 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form1 = rawRow4580 := by decide +kernel

def row4580 : Integer.Sparse Key := [(key281, -6), (key290, 6), (key350, 6), (key367, -6), (key516, -6), (key538, 6)]

theorem rowCheck4580 : row4580 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4580 := by decide +kernel

theorem rowEval4580 (x : Key → ℝ) : Integer.Sparse.eval row4580 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4580, Integer.Sparse.eval_collectBalanced, rawRowCheck4580]

def rawRow4581 : Integer.Sparse Key := [(key538, -6), (key367, 2), (key538, 2), (key538, 2), (key516, 6), (key290, -2), (key516, -2), (key516, -2), (key350, -2), (key507, -2), (key507, -2), (key281, 2), (key507, 2), (key507, 2)]

theorem rawRowCheck4581 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form1 = rawRow4581 := by decide +kernel

def row4581 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

theorem rowCheck4581 : row4581 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4581 := by decide +kernel

theorem rowEval4581 (x : Key → ℝ) : Integer.Sparse.eval row4581 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4581, Integer.Sparse.eval_collectBalanced, rawRowCheck4581]

def rawRow4582 : Integer.Sparse Key := [(key538, -6), (key538, 2), (key367, 2), (key538, 2), (key516, 6), (key516, -2), (key290, -2), (key516, -2), (key507, -2), (key350, -2), (key507, -2), (key507, 2), (key281, 2), (key507, 2)]

theorem rawRowCheck4582 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form1 = rawRow4582 := by decide +kernel

def row4582 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

theorem rowCheck4582 : row4582 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4582 := by decide +kernel

theorem rowEval4582 (x : Key → ℝ) : Integer.Sparse.eval row4582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck4582, Integer.Sparse.eval_collectBalanced, rawRowCheck4582]

def rawRow4583 : Integer.Sparse Key := [(key538, -6), (key538, 2), (key538, 2), (key367, 2), (key516, 6), (key516, -2), (key516, -2), (key290, -2), (key507, -2), (key507, -2), (key350, -2), (key507, 2), (key507, 2), (key281, 2)]

theorem rawRowCheck4583 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form1 = rawRow4583 := by decide +kernel

def row4583 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

theorem rowCheck4583 : row4583 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4583 := by decide +kernel

theorem rowEval4583 (x : Key → ℝ) : Integer.Sparse.eval row4583 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck4583, Integer.Sparse.eval_collectBalanced, rawRowCheck4583]

def rawRow4584 : Integer.Sparse Key := [(key1362, -2), (key1367, -2), (key1367, -2), (key1362, 1), (key1367, 1), (key1362, 1), (key1376, 1), (key1367, 1), (key1376, 1), (key1488, 2), (key1493, 2), (key1493, 2), (key1488, -1), (key1493, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1515, -1), (key1714, -1), (key1719, -1), (key1714, -1), (key1725, -1), (key1719, -1), (key1725, -1), (key1714, 1), (key1719, 1), (key1714, 1), (key1743, 1), (key1719, 1), (key1743, 1)]

theorem rawRowCheck4584 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form2 = rawRow4584 := by decide +kernel

def row4584 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

theorem rowCheck4584 : row4584 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4584 := by decide +kernel

theorem rowEval4584 (x : Key → ℝ) : Integer.Sparse.eval row4584 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4584, Integer.Sparse.eval_collectBalanced, rawRowCheck4584]

def rawRow4585 : Integer.Sparse Key := [(key1367, -2), (key1362, -2), (key1367, -2), (key1367, 1), (key1362, 1), (key1376, 1), (key1362, 1), (key1376, 1), (key1367, 1), (key1493, 2), (key1488, 2), (key1493, 2), (key1493, -1), (key1488, -1), (key1515, -1), (key1488, -1), (key1515, -1), (key1493, -1), (key1719, -1), (key1714, -1), (key1725, -1), (key1714, -1), (key1725, -1), (key1719, -1), (key1719, 1), (key1714, 1), (key1743, 1), (key1714, 1), (key1743, 1), (key1719, 1)]

theorem rawRowCheck4585 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form2 = rawRow4585 := by decide +kernel

def row4585 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

theorem rowCheck4585 : row4585 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4585 := by decide +kernel

theorem rowEval4585 (x : Key → ℝ) : Integer.Sparse.eval row4585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4585, Integer.Sparse.eval_collectBalanced, rawRowCheck4585]

def rawRow4586 : Integer.Sparse Key := [(key1367, -2), (key1367, -2), (key1362, -2), (key1376, 1), (key1376, 1), (key1367, 1), (key1367, 1), (key1362, 1), (key1362, 1), (key1493, 2), (key1493, 2), (key1488, 2), (key1515, -1), (key1515, -1), (key1493, -1), (key1493, -1), (key1488, -1), (key1488, -1), (key1725, -1), (key1725, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1743, 1), (key1743, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1)]

theorem rawRowCheck4586 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form2 = rawRow4586 := by decide +kernel

def row4586 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

theorem rowCheck4586 : row4586 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4586 := by decide +kernel

theorem rowEval4586 (x : Key → ℝ) : Integer.Sparse.eval row4586 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4586, Integer.Sparse.eval_collectBalanced, rawRowCheck4586]

def rawRow4587 : Integer.Sparse Key := [(key1376, -2), (key1376, -2), (key1376, -2), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1515, 2), (key1515, 2), (key1515, 2), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1)]

theorem rawRowCheck4587 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form2 = rawRow4587 := by decide +kernel

def row4587 : Integer.Sparse Key := [(key1367, 6), (key1376, -6), (key1493, -6), (key1515, 6), (key1725, 6), (key1743, -6)]

theorem rowCheck4587 : row4587 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4587 := by decide +kernel

theorem rowEval4587 (x : Key → ℝ) : Integer.Sparse.eval row4587 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4587, Integer.Sparse.eval_collectBalanced, rawRowCheck4587]

def rawRow4588 : Integer.Sparse Key := [(key1488, -2), (key1493, -2), (key1493, -2), (key1714, 1), (key1719, 1), (key1714, 1), (key1725, 1), (key1719, 1), (key1725, 1), (key1362, 2), (key1367, 2), (key1367, 2), (key1714, -1), (key1719, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1743, -1), (key1362, -1), (key1367, -1), (key1362, -1), (key1376, -1), (key1367, -1), (key1376, -1), (key1488, 1), (key1493, 1), (key1488, 1), (key1515, 1), (key1493, 1), (key1515, 1)]

theorem rawRowCheck4588 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form2 = rawRow4588 := by decide +kernel

def row4588 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

theorem rowCheck4588 : row4588 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4588 := by decide +kernel

theorem rowEval4588 (x : Key → ℝ) : Integer.Sparse.eval row4588 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck4588, Integer.Sparse.eval_collectBalanced, rawRowCheck4588]

def rawRow4589 : Integer.Sparse Key := [(key1493, -2), (key1488, -2), (key1493, -2), (key1719, 1), (key1714, 1), (key1725, 1), (key1714, 1), (key1725, 1), (key1719, 1), (key1367, 2), (key1362, 2), (key1367, 2), (key1719, -1), (key1714, -1), (key1743, -1), (key1714, -1), (key1743, -1), (key1719, -1), (key1367, -1), (key1362, -1), (key1376, -1), (key1362, -1), (key1376, -1), (key1367, -1), (key1493, 1), (key1488, 1), (key1515, 1), (key1488, 1), (key1515, 1), (key1493, 1)]

theorem rawRowCheck4589 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form2 = rawRow4589 := by decide +kernel

def row4589 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

theorem rowCheck4589 : row4589 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4589 := by decide +kernel

theorem rowEval4589 (x : Key → ℝ) : Integer.Sparse.eval row4589 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4589, Integer.Sparse.eval_collectBalanced, rawRowCheck4589]

def rawRow4590 : Integer.Sparse Key := [(key1493, -2), (key1493, -2), (key1488, -2), (key1725, 1), (key1725, 1), (key1719, 1), (key1719, 1), (key1714, 1), (key1714, 1), (key1367, 2), (key1367, 2), (key1362, 2), (key1743, -1), (key1743, -1), (key1719, -1), (key1719, -1), (key1714, -1), (key1714, -1), (key1376, -1), (key1376, -1), (key1367, -1), (key1367, -1), (key1362, -1), (key1362, -1), (key1515, 1), (key1515, 1), (key1493, 1), (key1493, 1), (key1488, 1), (key1488, 1)]

theorem rawRowCheck4590 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form2 = rawRow4590 := by decide +kernel

def row4590 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

theorem rowCheck4590 : row4590 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4590 := by decide +kernel

theorem rowEval4590 (x : Key → ℝ) : Integer.Sparse.eval row4590 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4590, Integer.Sparse.eval_collectBalanced, rawRowCheck4590]

def rawRow4591 : Integer.Sparse Key := [(key1725, -2), (key1725, -2), (key1941, -2), (key1493, 1), (key1493, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1), (key1743, 2), (key1743, 2), (key1950, 2), (key1367, -1), (key1367, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1515, -1), (key1515, -1), (key1743, -1), (key1743, -1), (key1950, -1), (key1950, -1), (key1376, 1), (key1376, 1), (key1725, 1), (key1725, 1), (key1941, 1), (key1941, 1)]

theorem rawRowCheck4591 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form2 = rawRow4591 := by decide +kernel

def row4591 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

theorem rowCheck4591 : row4591 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4591 := by decide +kernel

theorem rowEval4591 (x : Key → ℝ) : Integer.Sparse.eval row4591 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4591, Integer.Sparse.eval_collectBalanced, rawRowCheck4591]

def rawRow4592 : Integer.Sparse Key := [(key1725, -2), (key1941, -2), (key1725, -2), (key1719, 1), (key1938, 1), (key1493, 1), (key1938, 1), (key1493, 1), (key1719, 1), (key1743, 2), (key1950, 2), (key1743, 2), (key1719, -1), (key1938, -1), (key1367, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1743, -1), (key1950, -1), (key1515, -1), (key1950, -1), (key1515, -1), (key1743, -1), (key1725, 1), (key1941, 1), (key1376, 1), (key1941, 1), (key1376, 1), (key1725, 1)]

theorem rawRowCheck4592 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form2 = rawRow4592 := by decide +kernel

def row4592 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

theorem rowCheck4592 : row4592 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4592 := by decide +kernel

theorem rowEval4592 (x : Key → ℝ) : Integer.Sparse.eval row4592 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4592, Integer.Sparse.eval_collectBalanced, rawRowCheck4592]

def rawRow4593 : Integer.Sparse Key := [(key1941, -2), (key1725, -2), (key1725, -2), (key1938, 1), (key1719, 1), (key1938, 1), (key1493, 1), (key1719, 1), (key1493, 1), (key1950, 2), (key1743, 2), (key1743, 2), (key1938, -1), (key1719, -1), (key1938, -1), (key1367, -1), (key1719, -1), (key1367, -1), (key1950, -1), (key1743, -1), (key1950, -1), (key1515, -1), (key1743, -1), (key1515, -1), (key1941, 1), (key1725, 1), (key1941, 1), (key1376, 1), (key1725, 1), (key1376, 1)]

theorem rawRowCheck4593 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form2 = rawRow4593 := by decide +kernel

def row4593 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

theorem rowCheck4593 : row4593 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4593 := by decide +kernel

theorem rowEval4593 (x : Key → ℝ) : Integer.Sparse.eval row4593 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4593, Integer.Sparse.eval_collectBalanced, rawRowCheck4593]

def rawRow4594 : Integer.Sparse Key := [(key1515, -2), (key1515, -2), (key1515, -2), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1376, 2), (key1376, 2), (key1376, 2), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1)]

theorem rawRowCheck4594 : GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form2 = rawRow4594 := by decide +kernel

def row4594 : Integer.Sparse Key := [(key1367, -6), (key1376, 6), (key1493, 6), (key1515, -6), (key1725, -6), (key1743, 6)]

theorem rowCheck4594 : row4594 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4594 := by decide +kernel

theorem rowEval4594 (x : Key → ℝ) : Integer.Sparse.eval row4594 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -2, 0, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4594, Integer.Sparse.eval_collectBalanced, rawRowCheck4594]

def rawRow4595 : Integer.Sparse Key := [(key1743, -2), (key1743, -2), (key1950, -2), (key1515, 1), (key1515, 1), (key1743, 1), (key1743, 1), (key1950, 1), (key1950, 1), (key1725, 2), (key1725, 2), (key1941, 2), (key1376, -1), (key1376, -1), (key1725, -1), (key1725, -1), (key1941, -1), (key1941, -1), (key1493, -1), (key1493, -1), (key1719, -1), (key1719, -1), (key1938, -1), (key1938, -1), (key1367, 1), (key1367, 1), (key1719, 1), (key1719, 1), (key1938, 1), (key1938, 1)]

theorem rawRowCheck4595 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form2 = rawRow4595 := by decide +kernel

def row4595 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

theorem rowCheck4595 : row4595 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4595 := by decide +kernel

theorem rowEval4595 (x : Key → ℝ) : Integer.Sparse.eval row4595 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -2, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4595, Integer.Sparse.eval_collectBalanced, rawRowCheck4595]

def rawRow4596 : Integer.Sparse Key := [(key1743, -2), (key1950, -2), (key1743, -2), (key1743, 1), (key1950, 1), (key1515, 1), (key1950, 1), (key1515, 1), (key1743, 1), (key1725, 2), (key1941, 2), (key1725, 2), (key1725, -1), (key1941, -1), (key1376, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1719, -1), (key1938, -1), (key1493, -1), (key1938, -1), (key1493, -1), (key1719, -1), (key1719, 1), (key1938, 1), (key1367, 1), (key1938, 1), (key1367, 1), (key1719, 1)]

theorem rawRowCheck4596 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form2 = rawRow4596 := by decide +kernel

def row4596 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

theorem rowCheck4596 : row4596 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4596 := by decide +kernel

theorem rowEval4596 (x : Key → ℝ) : Integer.Sparse.eval row4596 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck4596, Integer.Sparse.eval_collectBalanced, rawRowCheck4596]

def rawRow4597 : Integer.Sparse Key := [(key1950, -2), (key1743, -2), (key1743, -2), (key1950, 1), (key1743, 1), (key1950, 1), (key1515, 1), (key1743, 1), (key1515, 1), (key1941, 2), (key1725, 2), (key1725, 2), (key1941, -1), (key1725, -1), (key1941, -1), (key1376, -1), (key1725, -1), (key1376, -1), (key1938, -1), (key1719, -1), (key1938, -1), (key1493, -1), (key1719, -1), (key1493, -1), (key1938, 1), (key1719, 1), (key1938, 1), (key1367, 1), (key1719, 1), (key1367, 1)]

theorem rawRowCheck4597 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form2 = rawRow4597 := by decide +kernel

def row4597 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

theorem rowCheck4597 : row4597 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4597 := by decide +kernel

theorem rowEval4597 (x : Key → ℝ) : Integer.Sparse.eval row4597 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck4597, Integer.Sparse.eval_collectBalanced, rawRowCheck4597]

def rawRow4598 : Integer.Sparse Key := [(key29, -2), (key33, -2), (key33, -2), (key33, 6), (key495, 2), (key500, 2), (key500, 2), (key500, -2), (key500, -2), (key554, -2), (key665, -6), (key665, 2), (key665, 2), (key682, 2)]

theorem rawRowCheck4598 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form3 = rawRow4598 := by decide +kernel

def row4598 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

theorem rowCheck4598 : row4598 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4598 := by decide +kernel

theorem rowEval4598 (x : Key → ℝ) : Integer.Sparse.eval row4598 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4598, Integer.Sparse.eval_collectBalanced, rawRowCheck4598]

def rawRow4599 : Integer.Sparse Key := [(key33, -2), (key29, -2), (key33, -2), (key33, 6), (key500, 2), (key495, 2), (key500, 2), (key500, -2), (key554, -2), (key500, -2), (key665, -6), (key665, 2), (key682, 2), (key665, 2)]

theorem rawRowCheck4599 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form3 = rawRow4599 := by decide +kernel

def row4599 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

theorem rowCheck4599 : row4599 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4599 := by decide +kernel

theorem rowEval4599 (x : Key → ℝ) : Integer.Sparse.eval row4599 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4599, Integer.Sparse.eval_collectBalanced, rawRowCheck4599]

def rawRow4600 : Integer.Sparse Key := [(key33, -2), (key33, -2), (key29, -2), (key33, 6), (key500, 2), (key500, 2), (key495, 2), (key554, -2), (key500, -2), (key500, -2), (key665, -6), (key682, 2), (key665, 2), (key665, 2)]

theorem rawRowCheck4600 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form3 = rawRow4600 := by decide +kernel

def row4600 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

theorem rowCheck4600 : row4600 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4600 := by decide +kernel

theorem rowEval4600 (x : Key → ℝ) : Integer.Sparse.eval row4600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4600, Integer.Sparse.eval_collectBalanced, rawRowCheck4600]

def rawRow4601 : Integer.Sparse Key := [(key33, -2), (key33, -2), (key33, -2), (key29, 6), (key554, 2), (key554, 2), (key554, 2), (key495, -2), (key495, -2), (key495, -2), (key682, -6), (key665, 2), (key665, 2), (key665, 2)]

theorem rawRowCheck4601 : GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form3 = rawRow4601 := by decide +kernel

def row4601 : Integer.Sparse Key := [(key29, 6), (key33, -6), (key495, -6), (key554, 6), (key665, 6), (key682, -6)]

theorem rowCheck4601 : row4601 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4601 := by decide +kernel

theorem rowEval4601 (x : Key → ℝ) : Integer.Sparse.eval row4601 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 1, 0, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4601, Integer.Sparse.eval_collectBalanced, rawRowCheck4601]

def rawRow4602 : Integer.Sparse Key := [(key109, -2), (key113, -2), (key113, -2), (key149, 6), (key29, 2), (key33, 2), (key33, 2), (key665, -2), (key665, -2), (key682, -2), (key228, -6), (key500, 2), (key500, 2), (key554, 2)]

theorem rawRowCheck4602 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form3 = rawRow4602 := by decide +kernel

def row4602 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

theorem rowCheck4602 : row4602 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4602 := by decide +kernel

theorem rowEval4602 (x : Key → ℝ) : Integer.Sparse.eval row4602 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 0, 1] GramFunctions.Block1.form3) x := by
  rw [rowCheck4602, Integer.Sparse.eval_collectBalanced, rawRowCheck4602]

def rawRow4603 : Integer.Sparse Key := [(key113, -2), (key109, -2), (key113, -2), (key149, 6), (key33, 2), (key29, 2), (key33, 2), (key665, -2), (key682, -2), (key665, -2), (key228, -6), (key500, 2), (key554, 2), (key500, 2)]

theorem rawRowCheck4603 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form3 = rawRow4603 := by decide +kernel

def row4603 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

theorem rowCheck4603 : row4603 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4603 := by decide +kernel

theorem rowEval4603 (x : Key → ℝ) : Integer.Sparse.eval row4603 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 1, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4603, Integer.Sparse.eval_collectBalanced, rawRowCheck4603]

def rawRow4604 : Integer.Sparse Key := [(key113, -2), (key113, -2), (key109, -2), (key149, 6), (key33, 2), (key33, 2), (key29, 2), (key682, -2), (key665, -2), (key665, -2), (key228, -6), (key554, 2), (key500, 2), (key500, 2)]

theorem rawRowCheck4604 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form3 = rawRow4604 := by decide +kernel

def row4604 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

theorem rowCheck4604 : row4604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4604 := by decide +kernel

theorem rowEval4604 (x : Key → ℝ) : Integer.Sparse.eval row4604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 1, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4604, Integer.Sparse.eval_collectBalanced, rawRowCheck4604]

def rawRow4605 : Integer.Sparse Key := [(key113, -2), (key113, -2), (key149, -2), (key109, 6), (key175, 2), (key175, 2), (key185, 2), (key223, -2), (key495, -2), (key495, -2), (key554, -6), (key228, 2), (key500, 2), (key500, 2)]

theorem rawRowCheck4605 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form3 = rawRow4605 := by decide +kernel

def row4605 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

theorem rowCheck4605 : row4605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4605 := by decide +kernel

theorem rowEval4605 (x : Key → ℝ) : Integer.Sparse.eval row4605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -2, 0, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4605, Integer.Sparse.eval_collectBalanced, rawRowCheck4605]

def rawRow4606 : Integer.Sparse Key := [(key113, -2), (key149, -2), (key113, -2), (key109, 6), (key175, 2), (key185, 2), (key175, 2), (key495, -2), (key223, -2), (key495, -2), (key554, -6), (key500, 2), (key228, 2), (key500, 2)]

theorem rawRowCheck4606 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form3 = rawRow4606 := by decide +kernel

def row4606 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

theorem rowCheck4606 : row4606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4606 := by decide +kernel

theorem rowEval4606 (x : Key → ℝ) : Integer.Sparse.eval row4606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck4606, Integer.Sparse.eval_collectBalanced, rawRowCheck4606]

def rawRow4607 : Integer.Sparse Key := [(key149, -2), (key113, -2), (key113, -2), (key109, 6), (key185, 2), (key175, 2), (key175, 2), (key495, -2), (key495, -2), (key223, -2), (key554, -6), (key500, 2), (key500, 2), (key228, 2)]

theorem rawRowCheck4607 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form3 = rawRow4607 := by decide +kernel

def row4607 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

theorem rowCheck4607 : row4607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow4607 := by decide +kernel

theorem rowEval4607 (x : Key → ℝ) : Integer.Sparse.eval row4607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 0, -2] GramFunctions.Block1.form3) x := by
  rw [rowCheck4607, Integer.Sparse.eval_collectBalanced, rawRowCheck4607]

end MUB6.Certificate.GramRows

end OAI
