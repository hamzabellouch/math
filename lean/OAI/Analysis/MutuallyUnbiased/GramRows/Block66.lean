import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
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

def rawRow5376 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2804, 2), (key2851, -1), (key2866, -1), (key2778, 2), (key2902, 2), (key2781, -1), (key2892, -1), (key2856, 2), (key2790, -1), (key2895, -1), (key2698, 1), (key2722, 1), (key2701, -2), (key2851, 1), (key2866, 1), (key2624, -2), (key2981, -2), (key2627, 1), (key2971, 1), (key2856, -2), (key2636, 1), (key2974, 1), (key2663, -1), (key2745, -1), (key2666, 1), (key2734, 1), (key2608, 1), (key2958, 1), (key2611, -1), (key2825, -1), (key2698, -1), (key2974, -1), (key2624, 1), (key2981, 1), (key2734, 1), (key2895, 1), (key2645, -1), (key2902, -1)]

theorem rawRowCheck5376 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form2 = rawRow5376 := by decide +kernel

def row5376 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2636, 1), (key2645, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 2), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5376 : row5376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5376 := by decide +kernel

theorem rowEval5376 (x : Key → ℝ) : Integer.Sparse.eval row5376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5376, Integer.Sparse.eval_collectBalanced, rawRowCheck5376]

def rawRow5377 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2804, 2), (key2866, -1), (key2851, -1), (key2902, 2), (key2778, 2), (key2892, -1), (key2781, -1), (key2856, 2), (key2895, -1), (key2790, -1), (key2722, 1), (key2698, 1), (key2701, -2), (key2866, 1), (key2851, 1), (key2981, -2), (key2624, -2), (key2971, 1), (key2627, 1), (key2856, -2), (key2974, 1), (key2636, 1), (key2745, -1), (key2663, -1), (key2734, 1), (key2666, 1), (key2958, 1), (key2608, 1), (key2825, -1), (key2611, -1), (key2974, -1), (key2698, -1), (key2981, 1), (key2624, 1), (key2895, 1), (key2734, 1), (key2902, -1), (key2645, -1)]

theorem rawRowCheck5377 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form2 = rawRow5377 := by decide +kernel

def row5377 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2636, 1), (key2645, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 2), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5377 : row5377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5377 := by decide +kernel

theorem rowEval5377 (x : Key → ℝ) : Integer.Sparse.eval row5377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5377, Integer.Sparse.eval_collectBalanced, rawRowCheck5377]

def rawRow5378 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2801, 2), (key2892, -1), (key2902, -1), (key2781, 2), (key2866, 2), (key2778, -1), (key2851, -1), (key2895, 2), (key2790, -1), (key2856, -1), (key2701, 1), (key2722, 1), (key2698, -2), (key2971, 1), (key2981, 1), (key2627, -2), (key2866, -2), (key2624, 1), (key2851, 1), (key2974, -2), (key2636, 1), (key2856, 1), (key2666, -1), (key2722, -1), (key2663, 1), (key2698, 1), (key2611, 1), (key2825, 1), (key2608, -1), (key2801, -1), (key2722, -1), (key2981, -1), (key2636, 1), (key2974, 1), (key2745, 1), (key2902, 1), (key2651, -1), (key2895, -1)]

theorem rawRowCheck5378 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form2 = rawRow5378 := by decide +kernel

def row5378 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5378 : row5378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5378 := by decide +kernel

theorem rowEval5378 (x : Key → ℝ) : Integer.Sparse.eval row5378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5378, Integer.Sparse.eval_collectBalanced, rawRowCheck5378]

def rawRow5379 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2801, 2), (key2902, -1), (key2892, -1), (key2866, 2), (key2781, 2), (key2851, -1), (key2778, -1), (key2895, 2), (key2856, -1), (key2790, -1), (key2722, 1), (key2701, 1), (key2698, -2), (key2981, 1), (key2971, 1), (key2866, -2), (key2627, -2), (key2851, 1), (key2624, 1), (key2974, -2), (key2856, 1), (key2636, 1), (key2722, -1), (key2666, -1), (key2698, 1), (key2663, 1), (key2825, 1), (key2611, 1), (key2801, -1), (key2608, -1), (key2981, -1), (key2722, -1), (key2974, 1), (key2636, 1), (key2902, 1), (key2745, 1), (key2895, -1), (key2651, -1)]

theorem rawRowCheck5379 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form2 = rawRow5379 := by decide +kernel

def row5379 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5379 : row5379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5379 := by decide +kernel

theorem rowEval5379 (x : Key → ℝ) : Integer.Sparse.eval row5379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5379, Integer.Sparse.eval_collectBalanced, rawRowCheck5379]

def rawRow5380 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2866, 2), (key2778, -1), (key2790, -1), (key2801, 2), (key2895, 2), (key2825, -1), (key2902, -1), (key2781, 2), (key2804, -1), (key2892, -1), (key2851, 1), (key2856, 1), (key2866, -2), (key2624, 1), (key2636, 1), (key2698, -2), (key2974, -2), (key2722, 1), (key2981, 1), (key2627, -2), (key2701, 1), (key2971, 1), (key2801, -1), (key2895, -1), (key2825, 1), (key2902, 1), (key2698, 1), (key2974, 1), (key2722, -1), (key2981, -1), (key2608, -1), (key2651, -1), (key2663, 1), (key2745, 1), (key2611, 1), (key2636, 1), (key2666, -1), (key2722, -1)]

theorem rawRowCheck5380 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form2 = rawRow5380 := by decide +kernel

def row5380 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5380 : row5380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5380 := by decide +kernel

theorem rowEval5380 (x : Key → ℝ) : Integer.Sparse.eval row5380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5380, Integer.Sparse.eval_collectBalanced, rawRowCheck5380]

def rawRow5381 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2866, 2), (key2790, -1), (key2778, -1), (key2895, 2), (key2801, 2), (key2902, -1), (key2825, -1), (key2781, 2), (key2892, -1), (key2804, -1), (key2856, 1), (key2851, 1), (key2866, -2), (key2636, 1), (key2624, 1), (key2974, -2), (key2698, -2), (key2981, 1), (key2722, 1), (key2627, -2), (key2971, 1), (key2701, 1), (key2895, -1), (key2801, -1), (key2902, 1), (key2825, 1), (key2974, 1), (key2698, 1), (key2981, -1), (key2722, -1), (key2651, -1), (key2608, -1), (key2745, 1), (key2663, 1), (key2636, 1), (key2611, 1), (key2722, -1), (key2666, -1)]

theorem rawRowCheck5381 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form2 = rawRow5381 := by decide +kernel

def row5381 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5381 : row5381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5381 := by decide +kernel

theorem rowEval5381 (x : Key → ℝ) : Integer.Sparse.eval row5381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5381, Integer.Sparse.eval_collectBalanced, rawRowCheck5381]

def rawRow5382 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2856, 2), (key2801, -1), (key2825, -1), (key2778, 2), (key2902, 2), (key2790, -1), (key2895, -1), (key2804, 2), (key2781, -1), (key2892, -1), (key2851, 1), (key2866, 1), (key2856, -2), (key2698, 1), (key2722, 1), (key2624, -2), (key2981, -2), (key2636, 1), (key2974, 1), (key2701, -2), (key2627, 1), (key2971, 1), (key2778, -1), (key2902, -1), (key2790, 1), (key2895, 1), (key2624, 1), (key2981, 1), (key2636, -1), (key2974, -1), (key2663, -1), (key2745, -1), (key2608, 1), (key2958, 1), (key2666, 1), (key2790, 1), (key2611, -1), (key2825, -1)]

theorem rawRowCheck5382 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form2 = rawRow5382 := by decide +kernel

def row5382 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2790, 1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5382 : row5382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5382 := by decide +kernel

theorem rowEval5382 (x : Key → ℝ) : Integer.Sparse.eval row5382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5382, Integer.Sparse.eval_collectBalanced, rawRowCheck5382]

def rawRow5383 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2856, 2), (key2825, -1), (key2801, -1), (key2902, 2), (key2778, 2), (key2895, -1), (key2790, -1), (key2804, 2), (key2892, -1), (key2781, -1), (key2866, 1), (key2851, 1), (key2856, -2), (key2722, 1), (key2698, 1), (key2981, -2), (key2624, -2), (key2974, 1), (key2636, 1), (key2701, -2), (key2971, 1), (key2627, 1), (key2902, -1), (key2778, -1), (key2895, 1), (key2790, 1), (key2981, 1), (key2624, 1), (key2974, -1), (key2636, -1), (key2745, -1), (key2663, -1), (key2958, 1), (key2608, 1), (key2790, 1), (key2666, 1), (key2825, -1), (key2611, -1)]

theorem rawRowCheck5383 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form2 = rawRow5383 := by decide +kernel

def row5383 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2790, 1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5383 : row5383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5383 := by decide +kernel

theorem rowEval5383 (x : Key → ℝ) : Integer.Sparse.eval row5383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5383, Integer.Sparse.eval_collectBalanced, rawRowCheck5383]

def rawRow5384 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2902, 2), (key2781, -1), (key2790, -1), (key2804, 2), (key2856, 2), (key2825, -1), (key2866, -1), (key2778, 2), (key2801, -1), (key2851, -1), (key2971, 1), (key2974, 1), (key2981, -2), (key2627, 1), (key2636, 1), (key2701, -2), (key2856, -2), (key2722, 1), (key2866, 1), (key2624, -2), (key2698, 1), (key2851, 1), (key2947, -1), (key2974, -1), (key2958, 1), (key2981, 1), (key2734, 1), (key2895, 1), (key2745, -1), (key2902, -1), (key2611, -1), (key2636, -1), (key2666, 1), (key2790, 1), (key2608, 1), (key2624, 1), (key2663, -1), (key2698, -1)]

theorem rawRowCheck5384 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form2 = rawRow5384 := by decide +kernel

def row5384 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2892, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5384 : row5384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5384 := by decide +kernel

theorem rowEval5384 (x : Key → ℝ) : Integer.Sparse.eval row5384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5384, Integer.Sparse.eval_collectBalanced, rawRowCheck5384]

def rawRow5385 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2902, 2), (key2790, -1), (key2781, -1), (key2856, 2), (key2804, 2), (key2866, -1), (key2825, -1), (key2778, 2), (key2851, -1), (key2801, -1), (key2974, 1), (key2971, 1), (key2981, -2), (key2636, 1), (key2627, 1), (key2856, -2), (key2701, -2), (key2866, 1), (key2722, 1), (key2624, -2), (key2851, 1), (key2698, 1), (key2974, -1), (key2947, -1), (key2981, 1), (key2958, 1), (key2895, 1), (key2734, 1), (key2902, -1), (key2745, -1), (key2636, -1), (key2611, -1), (key2790, 1), (key2666, 1), (key2624, 1), (key2608, 1), (key2698, -1), (key2663, -1)]

theorem rawRowCheck5385 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form2 = rawRow5385 := by decide +kernel

def row5385 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2892, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

theorem rowCheck5385 : row5385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5385 := by decide +kernel

theorem rowEval5385 (x : Key → ℝ) : Integer.Sparse.eval row5385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5385, Integer.Sparse.eval_collectBalanced, rawRowCheck5385]

def rawRow5386 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2895, 2), (key2804, -1), (key2825, -1), (key2781, 2), (key2866, 2), (key2790, -1), (key2856, -1), (key2801, 2), (key2778, -1), (key2851, -1), (key2971, 1), (key2981, 1), (key2974, -2), (key2701, 1), (key2722, 1), (key2627, -2), (key2866, -2), (key2636, 1), (key2856, 1), (key2698, -2), (key2624, 1), (key2851, 1), (key2935, -1), (key2981, -1), (key2941, 1), (key2974, 1), (key2645, 1), (key2902, 1), (key2651, -1), (key2895, -1), (key2666, -1), (key2722, -1), (key2611, 1), (key2825, 1), (key2663, 1), (key2698, 1), (key2608, -1), (key2801, -1)]

theorem rawRowCheck5386 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form2 = rawRow5386 := by decide +kernel

def row5386 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2941, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5386 : row5386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5386 := by decide +kernel

theorem rowEval5386 (x : Key → ℝ) : Integer.Sparse.eval row5386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5386, Integer.Sparse.eval_collectBalanced, rawRowCheck5386]

def rawRow5387 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2895, 2), (key2825, -1), (key2804, -1), (key2866, 2), (key2781, 2), (key2856, -1), (key2790, -1), (key2801, 2), (key2851, -1), (key2778, -1), (key2981, 1), (key2971, 1), (key2974, -2), (key2722, 1), (key2701, 1), (key2866, -2), (key2627, -2), (key2856, 1), (key2636, 1), (key2698, -2), (key2851, 1), (key2624, 1), (key2981, -1), (key2935, -1), (key2974, 1), (key2941, 1), (key2902, 1), (key2645, 1), (key2895, -1), (key2651, -1), (key2722, -1), (key2666, -1), (key2825, 1), (key2611, 1), (key2698, 1), (key2663, 1), (key2801, -1), (key2608, -1)]

theorem rawRowCheck5387 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form2 = rawRow5387 := by decide +kernel

def row5387 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2941, 1), (key2971, 1), (key2974, -1)]

theorem rowCheck5387 : row5387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5387 := by decide +kernel

theorem rowEval5387 (x : Key → ℝ) : Integer.Sparse.eval row5387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5387, Integer.Sparse.eval_collectBalanced, rawRowCheck5387]

def rawRow5388 : Integer.Sparse Key := [(key1003, -1), (key1003, -1), (key1009, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1017, 2), (key1022, -1), (key1022, -1), (key1009, 2), (key1022, -1), (key1022, -1), (key1038, 1), (key1038, 1), (key1044, -2), (key1038, 1), (key1038, 1), (key1073, -2), (key1073, -2), (key1080, 1), (key1080, 1), (key1044, -2), (key1080, 1), (key1080, 1), (key1125, -1), (key1125, -1), (key1130, 1), (key1130, 1), (key1152, 1), (key1152, 1), (key1159, -1), (key1159, -1), (key1125, -1), (key1125, -1), (key1152, 1), (key1152, 1), (key1130, 1), (key1130, 1), (key1159, -1), (key1159, -1)]

theorem rawRowCheck5388 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form0 = rawRow5388 := by decide +kernel

def row5388 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1125, -4), (key1130, 4), (key1152, 4), (key1159, -4)]

theorem rowCheck5388 : row5388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5388 := by decide +kernel

theorem rowEval5388 (x : Key → ℝ) : Integer.Sparse.eval row5388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5388, Integer.Sparse.eval_collectBalanced, rawRowCheck5388]

def rawRow5389 : Integer.Sparse Key := [(key1003, -1), (key1009, -1), (key1003, 2), (key1017, -1), (key1022, -1), (key1003, 2), (key1022, 2), (key1003, -1), (key1017, -1), (key1022, 2), (key1009, -1), (key1022, -1), (key1038, 1), (key1044, 1), (key1038, -2), (key1073, 1), (key1080, 1), (key1038, -2), (key1080, -2), (key1038, 1), (key1073, 1), (key1080, -2), (key1044, 1), (key1080, 1), (key1116, -1), (key1130, -1), (key1116, 1), (key1125, 1), (key1116, 1), (key1159, 1), (key1116, -1), (key1152, -1), (key1152, -1), (key1174, -1), (key1125, 1), (key1174, 1), (key1159, 1), (key1174, 1), (key1130, -1), (key1174, -1)]

theorem rawRowCheck5389 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form0 = rawRow5389 := by decide +kernel

def row5389 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5389 : row5389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5389 := by decide +kernel

theorem rowEval5389 (x : Key → ℝ) : Integer.Sparse.eval row5389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5389, Integer.Sparse.eval_collectBalanced, rawRowCheck5389]

def rawRow5390 : Integer.Sparse Key := [(key1009, -1), (key1003, -1), (key1003, 2), (key1022, -1), (key1017, -1), (key1022, 2), (key1003, 2), (key1017, -1), (key1003, -1), (key1022, 2), (key1022, -1), (key1009, -1), (key1044, 1), (key1038, 1), (key1038, -2), (key1080, 1), (key1073, 1), (key1080, -2), (key1038, -2), (key1073, 1), (key1038, 1), (key1080, -2), (key1080, 1), (key1044, 1), (key1130, -1), (key1116, -1), (key1125, 1), (key1116, 1), (key1159, 1), (key1116, 1), (key1152, -1), (key1116, -1), (key1174, -1), (key1152, -1), (key1174, 1), (key1125, 1), (key1174, 1), (key1159, 1), (key1174, -1), (key1130, -1)]

theorem rawRowCheck5390 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form0 = rawRow5390 := by decide +kernel

def row5390 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5390 : row5390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5390 := by decide +kernel

theorem rowEval5390 (x : Key → ℝ) : Integer.Sparse.eval row5390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5390, Integer.Sparse.eval_collectBalanced, rawRowCheck5390]

def rawRow5391 : Integer.Sparse Key := [(key1017, -1), (key1022, -1), (key1022, 2), (key1003, -1), (key1009, -1), (key1003, 2), (key1022, 2), (key1009, -1), (key1022, -1), (key1003, 2), (key1003, -1), (key1017, -1), (key1073, 1), (key1080, 1), (key1080, -2), (key1038, 1), (key1044, 1), (key1038, -2), (key1080, -2), (key1044, 1), (key1080, 1), (key1038, -2), (key1038, 1), (key1073, 1), (key1152, -1), (key1174, -1), (key1159, 1), (key1174, 1), (key1125, 1), (key1174, 1), (key1130, -1), (key1174, -1), (key1116, -1), (key1130, -1), (key1116, 1), (key1159, 1), (key1116, 1), (key1125, 1), (key1116, -1), (key1152, -1)]

theorem rawRowCheck5391 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5391 := by decide +kernel

def row5391 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5391 : row5391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5391 := by decide +kernel

theorem rowEval5391 (x : Key → ℝ) : Integer.Sparse.eval row5391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5391, Integer.Sparse.eval_collectBalanced, rawRowCheck5391]

def rawRow5392 : Integer.Sparse Key := [(key1022, -1), (key1017, -1), (key1022, 2), (key1009, -1), (key1003, -1), (key1022, 2), (key1003, 2), (key1022, -1), (key1009, -1), (key1003, 2), (key1017, -1), (key1003, -1), (key1080, 1), (key1073, 1), (key1080, -2), (key1044, 1), (key1038, 1), (key1080, -2), (key1038, -2), (key1080, 1), (key1044, 1), (key1038, -2), (key1073, 1), (key1038, 1), (key1174, -1), (key1152, -1), (key1174, 1), (key1159, 1), (key1174, 1), (key1125, 1), (key1174, -1), (key1130, -1), (key1130, -1), (key1116, -1), (key1159, 1), (key1116, 1), (key1125, 1), (key1116, 1), (key1152, -1), (key1116, -1)]

theorem rawRowCheck5392 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5392 := by decide +kernel

def row5392 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5392 : row5392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5392 := by decide +kernel

theorem rowEval5392 (x : Key → ℝ) : Integer.Sparse.eval row5392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5392, Integer.Sparse.eval_collectBalanced, rawRowCheck5392]

def rawRow5393 : Integer.Sparse Key := [(key1022, -1), (key1022, -1), (key1017, 2), (key1022, -1), (key1022, -1), (key1009, 2), (key1009, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1003, -1), (key1003, -1), (key1080, 1), (key1080, 1), (key1073, -2), (key1080, 1), (key1080, 1), (key1044, -2), (key1044, -2), (key1038, 1), (key1038, 1), (key1073, -2), (key1038, 1), (key1038, 1), (key1159, -1), (key1159, -1), (key1152, 1), (key1152, 1), (key1130, 1), (key1130, 1), (key1125, -1), (key1125, -1), (key1159, -1), (key1159, -1), (key1130, 1), (key1130, 1), (key1152, 1), (key1152, 1), (key1125, -1), (key1125, -1)]

theorem rawRowCheck5393 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5393 := by decide +kernel

def row5393 : Integer.Sparse Key := [(key1003, -4), (key1009, 4), (key1017, 4), (key1022, -4), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1125, -4), (key1130, 4), (key1152, 4), (key1159, -4)]

theorem rowCheck5393 : row5393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5393 := by decide +kernel

theorem rowEval5393 (x : Key → ℝ) : Integer.Sparse.eval row5393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5393, Integer.Sparse.eval_collectBalanced, rawRowCheck5393]

def rawRow5394 : Integer.Sparse Key := [(key1038, -1), (key1038, -1), (key1044, 2), (key1116, -1), (key1116, -1), (key1125, 2), (key1125, 2), (key1130, -1), (key1130, -1), (key1233, 2), (key1236, -1), (key1236, -1), (key1003, 1), (key1003, 1), (key1009, -2), (key1116, 1), (key1116, 1), (key1152, -2), (key1152, -2), (key1159, 1), (key1159, 1), (key1233, -2), (key1243, 1), (key1243, 1), (key1017, -1), (key1017, -1), (key1022, 1), (key1022, 1), (key1073, 1), (key1073, 1), (key1080, -1), (key1080, -1), (key1125, -1), (key1125, -1), (key1152, 1), (key1152, 1), (key1236, 1), (key1236, 1), (key1243, -1), (key1243, -1)]

theorem rawRowCheck5394 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form0 = rawRow5394 := by decide +kernel

def row5394 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5394 : row5394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5394 := by decide +kernel

theorem rowEval5394 (x : Key → ℝ) : Integer.Sparse.eval row5394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5394, Integer.Sparse.eval_collectBalanced, rawRowCheck5394]

def rawRow5395 : Integer.Sparse Key := [(key1038, -1), (key1044, -1), (key1038, 2), (key1125, -1), (key1130, -1), (key1116, 2), (key1130, 2), (key1116, -1), (key1125, -1), (key1236, 2), (key1233, -1), (key1236, -1), (key1003, 1), (key1009, 1), (key1003, -2), (key1152, 1), (key1159, 1), (key1116, -2), (key1159, -2), (key1116, 1), (key1152, 1), (key1243, -2), (key1233, 1), (key1243, 1), (key1003, -1), (key1022, -1), (key1003, 1), (key1017, 1), (key1038, 1), (key1080, 1), (key1038, -1), (key1073, -1), (key1152, -1), (key1174, -1), (key1125, 1), (key1174, 1), (key1243, 1), (key1247, 1), (key1236, -1), (key1247, -1)]

theorem rawRowCheck5395 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form0 = rawRow5395 := by decide +kernel

def row5395 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5395 : row5395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5395 := by decide +kernel

theorem rowEval5395 (x : Key → ℝ) : Integer.Sparse.eval row5395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5395, Integer.Sparse.eval_collectBalanced, rawRowCheck5395]

def rawRow5396 : Integer.Sparse Key := [(key1044, -1), (key1038, -1), (key1038, 2), (key1130, -1), (key1125, -1), (key1130, 2), (key1116, 2), (key1125, -1), (key1116, -1), (key1236, 2), (key1236, -1), (key1233, -1), (key1009, 1), (key1003, 1), (key1003, -2), (key1159, 1), (key1152, 1), (key1159, -2), (key1116, -2), (key1152, 1), (key1116, 1), (key1243, -2), (key1243, 1), (key1233, 1), (key1022, -1), (key1003, -1), (key1017, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1073, -1), (key1038, -1), (key1174, -1), (key1152, -1), (key1174, 1), (key1125, 1), (key1247, 1), (key1243, 1), (key1247, -1), (key1236, -1)]

theorem rawRowCheck5396 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form0 = rawRow5396 := by decide +kernel

def row5396 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5396 : row5396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5396 := by decide +kernel

theorem rowEval5396 (x : Key → ℝ) : Integer.Sparse.eval row5396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5396, Integer.Sparse.eval_collectBalanced, rawRowCheck5396]

def rawRow5397 : Integer.Sparse Key := [(key1116, -1), (key1116, -1), (key1233, 2), (key1038, -1), (key1038, -1), (key1125, 2), (key1125, 2), (key1236, -1), (key1236, -1), (key1044, 2), (key1130, -1), (key1130, -1), (key1116, 1), (key1116, 1), (key1233, -2), (key1003, 1), (key1003, 1), (key1152, -2), (key1152, -2), (key1243, 1), (key1243, 1), (key1009, -2), (key1159, 1), (key1159, 1), (key1125, -1), (key1125, -1), (key1236, 1), (key1236, 1), (key1152, 1), (key1152, 1), (key1243, -1), (key1243, -1), (key1017, -1), (key1017, -1), (key1073, 1), (key1073, 1), (key1022, 1), (key1022, 1), (key1080, -1), (key1080, -1)]

theorem rawRowCheck5397 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form0 = rawRow5397 := by decide +kernel

def row5397 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5397 : row5397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5397 := by decide +kernel

theorem rowEval5397 (x : Key → ℝ) : Integer.Sparse.eval row5397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5397, Integer.Sparse.eval_collectBalanced, rawRowCheck5397]

def rawRow5398 : Integer.Sparse Key := [(key1116, -1), (key1233, -1), (key1116, 2), (key1125, -1), (key1236, -1), (key1038, 2), (key1236, 2), (key1038, -1), (key1125, -1), (key1130, 2), (key1044, -1), (key1130, -1), (key1116, 1), (key1233, 1), (key1116, -2), (key1152, 1), (key1243, 1), (key1003, -2), (key1243, -2), (key1003, 1), (key1152, 1), (key1159, -2), (key1009, 1), (key1159, 1), (key1038, -1), (key1236, -1), (key1038, 1), (key1125, 1), (key1003, 1), (key1243, 1), (key1003, -1), (key1152, -1), (key1073, -1), (key1247, -1), (key1017, 1), (key1247, 1), (key1080, 1), (key1174, 1), (key1022, -1), (key1174, -1)]

theorem rawRowCheck5398 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form0 = rawRow5398 := by decide +kernel

def row5398 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5398 : row5398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5398 := by decide +kernel

theorem rowEval5398 (x : Key → ℝ) : Integer.Sparse.eval row5398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5398, Integer.Sparse.eval_collectBalanced, rawRowCheck5398]

def rawRow5399 : Integer.Sparse Key := [(key1233, -1), (key1116, -1), (key1116, 2), (key1236, -1), (key1125, -1), (key1236, 2), (key1038, 2), (key1125, -1), (key1038, -1), (key1130, 2), (key1130, -1), (key1044, -1), (key1233, 1), (key1116, 1), (key1116, -2), (key1243, 1), (key1152, 1), (key1243, -2), (key1003, -2), (key1152, 1), (key1003, 1), (key1159, -2), (key1159, 1), (key1009, 1), (key1236, -1), (key1038, -1), (key1125, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1152, -1), (key1003, -1), (key1247, -1), (key1073, -1), (key1247, 1), (key1017, 1), (key1174, 1), (key1080, 1), (key1174, -1), (key1022, -1)]

theorem rawRowCheck5399 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form0 = rawRow5399 := by decide +kernel

def row5399 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5399 : row5399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5399 := by decide +kernel

theorem rowEval5399 (x : Key → ℝ) : Integer.Sparse.eval row5399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5399, Integer.Sparse.eval_collectBalanced, rawRowCheck5399]

def rawRow5400 : Integer.Sparse Key := [(key1125, -1), (key1130, -1), (key1236, 2), (key1038, -1), (key1044, -1), (key1116, 2), (key1130, 2), (key1233, -1), (key1236, -1), (key1038, 2), (key1116, -1), (key1125, -1), (key1152, 1), (key1159, 1), (key1243, -2), (key1003, 1), (key1009, 1), (key1116, -2), (key1159, -2), (key1233, 1), (key1243, 1), (key1003, -2), (key1116, 1), (key1152, 1), (key1152, -1), (key1174, -1), (key1243, 1), (key1247, 1), (key1125, 1), (key1174, 1), (key1236, -1), (key1247, -1), (key1003, -1), (key1022, -1), (key1038, 1), (key1080, 1), (key1003, 1), (key1017, 1), (key1038, -1), (key1073, -1)]

theorem rawRowCheck5400 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form0 = rawRow5400 := by decide +kernel

def row5400 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5400 : row5400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5400 := by decide +kernel

theorem rowEval5400 (x : Key → ℝ) : Integer.Sparse.eval row5400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5400, Integer.Sparse.eval_collectBalanced, rawRowCheck5400]

def rawRow5401 : Integer.Sparse Key := [(key1130, -1), (key1125, -1), (key1236, 2), (key1044, -1), (key1038, -1), (key1130, 2), (key1116, 2), (key1236, -1), (key1233, -1), (key1038, 2), (key1125, -1), (key1116, -1), (key1159, 1), (key1152, 1), (key1243, -2), (key1009, 1), (key1003, 1), (key1159, -2), (key1116, -2), (key1243, 1), (key1233, 1), (key1003, -2), (key1152, 1), (key1116, 1), (key1174, -1), (key1152, -1), (key1247, 1), (key1243, 1), (key1174, 1), (key1125, 1), (key1247, -1), (key1236, -1), (key1022, -1), (key1003, -1), (key1080, 1), (key1038, 1), (key1017, 1), (key1003, 1), (key1073, -1), (key1038, -1)]

theorem rawRowCheck5401 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form0 = rawRow5401 := by decide +kernel

def row5401 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5401 : row5401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5401 := by decide +kernel

theorem rowEval5401 (x : Key → ℝ) : Integer.Sparse.eval row5401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5401, Integer.Sparse.eval_collectBalanced, rawRowCheck5401]

def rawRow5402 : Integer.Sparse Key := [(key1125, -1), (key1236, -1), (key1130, 2), (key1116, -1), (key1233, -1), (key1038, 2), (key1236, 2), (key1044, -1), (key1130, -1), (key1116, 2), (key1038, -1), (key1125, -1), (key1152, 1), (key1243, 1), (key1159, -2), (key1116, 1), (key1233, 1), (key1003, -2), (key1243, -2), (key1009, 1), (key1159, 1), (key1116, -2), (key1003, 1), (key1152, 1), (key1073, -1), (key1247, -1), (key1080, 1), (key1174, 1), (key1017, 1), (key1247, 1), (key1022, -1), (key1174, -1), (key1038, -1), (key1236, -1), (key1003, 1), (key1243, 1), (key1038, 1), (key1125, 1), (key1003, -1), (key1152, -1)]

theorem rawRowCheck5402 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form0 = rawRow5402 := by decide +kernel

def row5402 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5402 : row5402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5402 := by decide +kernel

theorem rowEval5402 (x : Key → ℝ) : Integer.Sparse.eval row5402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5402, Integer.Sparse.eval_collectBalanced, rawRowCheck5402]

def rawRow5403 : Integer.Sparse Key := [(key1236, -1), (key1125, -1), (key1130, 2), (key1233, -1), (key1116, -1), (key1236, 2), (key1038, 2), (key1130, -1), (key1044, -1), (key1116, 2), (key1125, -1), (key1038, -1), (key1243, 1), (key1152, 1), (key1159, -2), (key1233, 1), (key1116, 1), (key1243, -2), (key1003, -2), (key1159, 1), (key1009, 1), (key1116, -2), (key1152, 1), (key1003, 1), (key1247, -1), (key1073, -1), (key1174, 1), (key1080, 1), (key1247, 1), (key1017, 1), (key1174, -1), (key1022, -1), (key1236, -1), (key1038, -1), (key1243, 1), (key1003, 1), (key1125, 1), (key1038, 1), (key1152, -1), (key1003, -1)]

theorem rawRowCheck5403 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form0 = rawRow5403 := by decide +kernel

def row5403 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5403 : row5403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5403 := by decide +kernel

theorem rowEval5403 (x : Key → ℝ) : Integer.Sparse.eval row5403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5403, Integer.Sparse.eval_collectBalanced, rawRowCheck5403]

def rawRow5404 : Integer.Sparse Key := [(key1130, -1), (key1236, -1), (key1125, 2), (key1130, -1), (key1236, -1), (key1044, 2), (key1233, 2), (key1038, -1), (key1116, -1), (key1125, 2), (key1038, -1), (key1116, -1), (key1159, 1), (key1243, 1), (key1152, -2), (key1159, 1), (key1243, 1), (key1009, -2), (key1233, -2), (key1003, 1), (key1116, 1), (key1152, -2), (key1003, 1), (key1116, 1), (key1080, -1), (key1243, -1), (key1073, 1), (key1152, 1), (key1022, 1), (key1236, 1), (key1017, -1), (key1125, -1), (key1080, -1), (key1243, -1), (key1022, 1), (key1236, 1), (key1073, 1), (key1152, 1), (key1017, -1), (key1125, -1)]

theorem rawRowCheck5404 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form0 = rawRow5404 := by decide +kernel

def row5404 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5404 : row5404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5404 := by decide +kernel

theorem rowEval5404 (x : Key → ℝ) : Integer.Sparse.eval row5404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5404, Integer.Sparse.eval_collectBalanced, rawRowCheck5404]

def rawRow5405 : Integer.Sparse Key := [(key1236, -1), (key1130, -1), (key1125, 2), (key1236, -1), (key1130, -1), (key1233, 2), (key1044, 2), (key1116, -1), (key1038, -1), (key1125, 2), (key1116, -1), (key1038, -1), (key1243, 1), (key1159, 1), (key1152, -2), (key1243, 1), (key1159, 1), (key1233, -2), (key1009, -2), (key1116, 1), (key1003, 1), (key1152, -2), (key1116, 1), (key1003, 1), (key1243, -1), (key1080, -1), (key1152, 1), (key1073, 1), (key1236, 1), (key1022, 1), (key1125, -1), (key1017, -1), (key1243, -1), (key1080, -1), (key1236, 1), (key1022, 1), (key1152, 1), (key1073, 1), (key1125, -1), (key1017, -1)]

theorem rawRowCheck5405 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form0 = rawRow5405 := by decide +kernel

def row5405 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5405 : row5405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5405 := by decide +kernel

theorem rowEval5405 (x : Key → ℝ) : Integer.Sparse.eval row5405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5405, Integer.Sparse.eval_collectBalanced, rawRowCheck5405]

def rawRow5406 : Integer.Sparse Key := [(key1073, -1), (key1080, -1), (key1080, 2), (key1152, -1), (key1159, -1), (key1152, 2), (key1174, 2), (key1159, -1), (key1174, -1), (key1243, 2), (key1243, -1), (key1247, -1), (key1017, 1), (key1022, 1), (key1022, -2), (key1125, 1), (key1130, 1), (key1125, -2), (key1174, -2), (key1130, 1), (key1174, 1), (key1236, -2), (key1236, 1), (key1247, 1), (key1003, -1), (key1022, -1), (key1009, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1044, -1), (key1080, -1), (key1116, -1), (key1130, -1), (key1116, 1), (key1159, 1), (key1233, 1), (key1236, 1), (key1233, -1), (key1243, -1)]

theorem rawRowCheck5406 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form0 = rawRow5406 := by decide +kernel

def row5406 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5406 : row5406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5406 := by decide +kernel

theorem rowEval5406 (x : Key → ℝ) : Integer.Sparse.eval row5406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5406, Integer.Sparse.eval_collectBalanced, rawRowCheck5406]

def rawRow5407 : Integer.Sparse Key := [(key1080, -1), (key1073, -1), (key1080, 2), (key1159, -1), (key1152, -1), (key1174, 2), (key1152, 2), (key1174, -1), (key1159, -1), (key1243, 2), (key1247, -1), (key1243, -1), (key1022, 1), (key1017, 1), (key1022, -2), (key1130, 1), (key1125, 1), (key1174, -2), (key1125, -2), (key1174, 1), (key1130, 1), (key1236, -2), (key1247, 1), (key1236, 1), (key1022, -1), (key1003, -1), (key1022, 1), (key1009, 1), (key1080, 1), (key1038, 1), (key1080, -1), (key1044, -1), (key1130, -1), (key1116, -1), (key1159, 1), (key1116, 1), (key1236, 1), (key1233, 1), (key1243, -1), (key1233, -1)]

theorem rawRowCheck5407 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form0 = rawRow5407 := by decide +kernel

def row5407 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5407 : row5407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5407 := by decide +kernel

theorem rowEval5407 (x : Key → ℝ) : Integer.Sparse.eval row5407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5407, Integer.Sparse.eval_collectBalanced, rawRowCheck5407]

def rawRow5408 : Integer.Sparse Key := [(key1080, -1), (key1080, -1), (key1073, 2), (key1174, -1), (key1174, -1), (key1159, 2), (key1159, 2), (key1152, -1), (key1152, -1), (key1247, 2), (key1243, -1), (key1243, -1), (key1022, 1), (key1022, 1), (key1017, -2), (key1174, 1), (key1174, 1), (key1130, -2), (key1130, -2), (key1125, 1), (key1125, 1), (key1247, -2), (key1236, 1), (key1236, 1), (key1009, -1), (key1009, -1), (key1003, 1), (key1003, 1), (key1044, 1), (key1044, 1), (key1038, -1), (key1038, -1), (key1159, -1), (key1159, -1), (key1130, 1), (key1130, 1), (key1243, 1), (key1243, 1), (key1236, -1), (key1236, -1)]

theorem rawRowCheck5408 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form0 = rawRow5408 := by decide +kernel

def row5408 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5408 : row5408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5408 := by decide +kernel

theorem rowEval5408 (x : Key → ℝ) : Integer.Sparse.eval row5408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5408, Integer.Sparse.eval_collectBalanced, rawRowCheck5408]

def rawRow5409 : Integer.Sparse Key := [(key1152, -1), (key1159, -1), (key1243, 2), (key1073, -1), (key1080, -1), (key1152, 2), (key1174, 2), (key1243, -1), (key1247, -1), (key1080, 2), (key1159, -1), (key1174, -1), (key1125, 1), (key1130, 1), (key1236, -2), (key1017, 1), (key1022, 1), (key1125, -2), (key1174, -2), (key1236, 1), (key1247, 1), (key1022, -2), (key1130, 1), (key1174, 1), (key1116, -1), (key1130, -1), (key1233, 1), (key1236, 1), (key1116, 1), (key1159, 1), (key1233, -1), (key1243, -1), (key1003, -1), (key1022, -1), (key1038, 1), (key1080, 1), (key1009, 1), (key1022, 1), (key1044, -1), (key1080, -1)]

theorem rawRowCheck5409 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form0 = rawRow5409 := by decide +kernel

def row5409 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5409 : row5409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5409 := by decide +kernel

theorem rowEval5409 (x : Key → ℝ) : Integer.Sparse.eval row5409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5409, Integer.Sparse.eval_collectBalanced, rawRowCheck5409]

def rawRow5410 : Integer.Sparse Key := [(key1159, -1), (key1152, -1), (key1243, 2), (key1080, -1), (key1073, -1), (key1174, 2), (key1152, 2), (key1247, -1), (key1243, -1), (key1080, 2), (key1174, -1), (key1159, -1), (key1130, 1), (key1125, 1), (key1236, -2), (key1022, 1), (key1017, 1), (key1174, -2), (key1125, -2), (key1247, 1), (key1236, 1), (key1022, -2), (key1174, 1), (key1130, 1), (key1130, -1), (key1116, -1), (key1236, 1), (key1233, 1), (key1159, 1), (key1116, 1), (key1243, -1), (key1233, -1), (key1022, -1), (key1003, -1), (key1080, 1), (key1038, 1), (key1022, 1), (key1009, 1), (key1080, -1), (key1044, -1)]

theorem rawRowCheck5410 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form0 = rawRow5410 := by decide +kernel

def row5410 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5410 : row5410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5410 := by decide +kernel

theorem rowEval5410 (x : Key → ℝ) : Integer.Sparse.eval row5410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5410, Integer.Sparse.eval_collectBalanced, rawRowCheck5410]

def rawRow5411 : Integer.Sparse Key := [(key1152, -1), (key1243, -1), (key1159, 2), (key1152, -1), (key1243, -1), (key1073, 2), (key1247, 2), (key1080, -1), (key1174, -1), (key1159, 2), (key1080, -1), (key1174, -1), (key1125, 1), (key1236, 1), (key1130, -2), (key1125, 1), (key1236, 1), (key1017, -2), (key1247, -2), (key1022, 1), (key1174, 1), (key1130, -2), (key1022, 1), (key1174, 1), (key1038, -1), (key1236, -1), (key1044, 1), (key1130, 1), (key1003, 1), (key1243, 1), (key1009, -1), (key1159, -1), (key1038, -1), (key1236, -1), (key1003, 1), (key1243, 1), (key1044, 1), (key1130, 1), (key1009, -1), (key1159, -1)]

theorem rawRowCheck5411 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form0 = rawRow5411 := by decide +kernel

def row5411 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5411 : row5411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5411 := by decide +kernel

theorem rowEval5411 (x : Key → ℝ) : Integer.Sparse.eval row5411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form0) x := by
  rw [rowCheck5411, Integer.Sparse.eval_collectBalanced, rawRowCheck5411]

def rawRow5412 : Integer.Sparse Key := [(key1243, -1), (key1152, -1), (key1159, 2), (key1243, -1), (key1152, -1), (key1247, 2), (key1073, 2), (key1174, -1), (key1080, -1), (key1159, 2), (key1174, -1), (key1080, -1), (key1236, 1), (key1125, 1), (key1130, -2), (key1236, 1), (key1125, 1), (key1247, -2), (key1017, -2), (key1174, 1), (key1022, 1), (key1130, -2), (key1174, 1), (key1022, 1), (key1236, -1), (key1038, -1), (key1130, 1), (key1044, 1), (key1243, 1), (key1003, 1), (key1159, -1), (key1009, -1), (key1236, -1), (key1038, -1), (key1243, 1), (key1003, 1), (key1130, 1), (key1044, 1), (key1159, -1), (key1009, -1)]

theorem rawRowCheck5412 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form0 = rawRow5412 := by decide +kernel

def row5412 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5412 : row5412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5412 := by decide +kernel

theorem rowEval5412 (x : Key → ℝ) : Integer.Sparse.eval row5412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5412, Integer.Sparse.eval_collectBalanced, rawRowCheck5412]

def rawRow5413 : Integer.Sparse Key := [(key1159, -1), (key1243, -1), (key1152, 2), (key1174, -1), (key1247, -1), (key1080, 2), (key1243, 2), (key1073, -1), (key1152, -1), (key1174, 2), (key1080, -1), (key1159, -1), (key1130, 1), (key1236, 1), (key1125, -2), (key1174, 1), (key1247, 1), (key1022, -2), (key1236, -2), (key1017, 1), (key1125, 1), (key1174, -2), (key1022, 1), (key1130, 1), (key1044, -1), (key1233, -1), (key1038, 1), (key1116, 1), (key1009, 1), (key1233, 1), (key1003, -1), (key1116, -1), (key1080, -1), (key1243, -1), (key1022, 1), (key1236, 1), (key1080, 1), (key1159, 1), (key1022, -1), (key1130, -1)]

theorem rawRowCheck5413 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form0 = rawRow5413 := by decide +kernel

def row5413 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5413 : row5413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5413 := by decide +kernel

theorem rowEval5413 (x : Key → ℝ) : Integer.Sparse.eval row5413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5413, Integer.Sparse.eval_collectBalanced, rawRowCheck5413]

def rawRow5414 : Integer.Sparse Key := [(key1243, -1), (key1159, -1), (key1152, 2), (key1247, -1), (key1174, -1), (key1243, 2), (key1080, 2), (key1152, -1), (key1073, -1), (key1174, 2), (key1159, -1), (key1080, -1), (key1236, 1), (key1130, 1), (key1125, -2), (key1247, 1), (key1174, 1), (key1236, -2), (key1022, -2), (key1125, 1), (key1017, 1), (key1174, -2), (key1130, 1), (key1022, 1), (key1233, -1), (key1044, -1), (key1116, 1), (key1038, 1), (key1233, 1), (key1009, 1), (key1116, -1), (key1003, -1), (key1243, -1), (key1080, -1), (key1236, 1), (key1022, 1), (key1159, 1), (key1080, 1), (key1130, -1), (key1022, -1)]

theorem rawRowCheck5414 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form0 = rawRow5414 := by decide +kernel

def row5414 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5414 : row5414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5414 := by decide +kernel

theorem rowEval5414 (x : Key → ℝ) : Integer.Sparse.eval row5414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5414, Integer.Sparse.eval_collectBalanced, rawRowCheck5414]

def rawRow5415 : Integer.Sparse Key := [(key1174, -1), (key1174, -1), (key1247, 2), (key1080, -1), (key1080, -1), (key1159, 2), (key1159, 2), (key1243, -1), (key1243, -1), (key1073, 2), (key1152, -1), (key1152, -1), (key1174, 1), (key1174, 1), (key1247, -2), (key1022, 1), (key1022, 1), (key1130, -2), (key1130, -2), (key1236, 1), (key1236, 1), (key1017, -2), (key1125, 1), (key1125, 1), (key1159, -1), (key1159, -1), (key1243, 1), (key1243, 1), (key1130, 1), (key1130, 1), (key1236, -1), (key1236, -1), (key1009, -1), (key1009, -1), (key1044, 1), (key1044, 1), (key1003, 1), (key1003, 1), (key1038, -1), (key1038, -1)]

theorem rawRowCheck5415 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form0 = rawRow5415 := by decide +kernel

def row5415 : Integer.Sparse Key := [(key1003, 2), (key1009, -2), (key1017, -2), (key1022, 2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1125, 2), (key1130, -2), (key1152, -2), (key1159, 2)]

theorem rowCheck5415 : row5415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5415 := by decide +kernel

theorem rowEval5415 (x : Key → ℝ) : Integer.Sparse.eval row5415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5415, Integer.Sparse.eval_collectBalanced, rawRowCheck5415]

def rawRow5416 : Integer.Sparse Key := [(key1174, -1), (key1247, -1), (key1174, 2), (key1159, -1), (key1243, -1), (key1080, 2), (key1243, 2), (key1080, -1), (key1159, -1), (key1152, 2), (key1073, -1), (key1152, -1), (key1174, 1), (key1247, 1), (key1174, -2), (key1130, 1), (key1236, 1), (key1022, -2), (key1236, -2), (key1022, 1), (key1130, 1), (key1125, -2), (key1017, 1), (key1125, 1), (key1080, -1), (key1243, -1), (key1080, 1), (key1159, 1), (key1022, 1), (key1236, 1), (key1022, -1), (key1130, -1), (key1044, -1), (key1233, -1), (key1009, 1), (key1233, 1), (key1038, 1), (key1116, 1), (key1003, -1), (key1116, -1)]

theorem rawRowCheck5416 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form0 = rawRow5416 := by decide +kernel

def row5416 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5416 : row5416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5416 := by decide +kernel

theorem rowEval5416 (x : Key → ℝ) : Integer.Sparse.eval row5416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form0) x := by
  rw [rowCheck5416, Integer.Sparse.eval_collectBalanced, rawRowCheck5416]

def rawRow5417 : Integer.Sparse Key := [(key1247, -1), (key1174, -1), (key1174, 2), (key1243, -1), (key1159, -1), (key1243, 2), (key1080, 2), (key1159, -1), (key1080, -1), (key1152, 2), (key1152, -1), (key1073, -1), (key1247, 1), (key1174, 1), (key1174, -2), (key1236, 1), (key1130, 1), (key1236, -2), (key1022, -2), (key1130, 1), (key1022, 1), (key1125, -2), (key1125, 1), (key1017, 1), (key1243, -1), (key1080, -1), (key1159, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1130, -1), (key1022, -1), (key1233, -1), (key1044, -1), (key1233, 1), (key1009, 1), (key1116, 1), (key1038, 1), (key1116, -1), (key1003, -1)]

theorem rawRowCheck5417 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form0 = rawRow5417 := by decide +kernel

def row5417 : Integer.Sparse Key := [(key1003, -1), (key1009, 1), (key1017, 1), (key1022, -1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1125, -1), (key1130, 1), (key1152, 1), (key1159, -1)]

theorem rowCheck5417 : row5417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5417 := by decide +kernel

theorem rowEval5417 (x : Key → ℝ) : Integer.Sparse.eval row5417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form0) x := by
  rw [rowCheck5417, Integer.Sparse.eval_collectBalanced, rawRowCheck5417]

def rawRow5418 : Integer.Sparse Key := [(key25, -1), (key25, -1), (key27, 2), (key25, -1), (key25, -1), (key37, 2), (key37, 2), (key40, -1), (key40, -1), (key27, 2), (key40, -1), (key40, -1), (key50, 1), (key50, 1), (key52, -2), (key50, 1), (key50, 1), (key76, -2), (key76, -2), (key81, 1), (key81, 1), (key52, -2), (key81, 1), (key81, 1), (key117, -1), (key117, -1), (key120, 1), (key120, 1), (key139, 1), (key139, 1), (key144, -1), (key144, -1), (key117, -1), (key117, -1), (key139, 1), (key139, 1), (key120, 1), (key120, 1), (key144, -1), (key144, -1)]

theorem rawRowCheck5418 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5418 := by decide +kernel

def row5418 : Integer.Sparse Key := [(key25, -4), (key27, 4), (key37, 4), (key40, -4), (key50, 4), (key52, -4), (key76, -4), (key81, 4), (key117, -4), (key120, 4), (key139, 4), (key144, -4)]

theorem rowCheck5418 : row5418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5418 := by decide +kernel

theorem rowEval5418 (x : Key → ℝ) : Integer.Sparse.eval row5418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5418, Integer.Sparse.eval_collectBalanced, rawRowCheck5418]

def rawRow5419 : Integer.Sparse Key := [(key25, -1), (key27, -1), (key25, 2), (key37, -1), (key40, -1), (key25, 2), (key40, 2), (key25, -1), (key37, -1), (key40, 2), (key27, -1), (key40, -1), (key50, 1), (key52, 1), (key50, -2), (key76, 1), (key81, 1), (key50, -2), (key81, -2), (key50, 1), (key76, 1), (key81, -2), (key52, 1), (key81, 1), (key107, -1), (key120, -1), (key107, 1), (key117, 1), (key107, 1), (key144, 1), (key107, -1), (key139, -1), (key139, -1), (key162, -1), (key117, 1), (key162, 1), (key144, 1), (key162, 1), (key120, -1), (key162, -1)]

theorem rawRowCheck5419 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5419 := by decide +kernel

def row5419 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

theorem rowCheck5419 : row5419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5419 := by decide +kernel

theorem rowEval5419 (x : Key → ℝ) : Integer.Sparse.eval row5419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5419, Integer.Sparse.eval_collectBalanced, rawRowCheck5419]

def rawRow5420 : Integer.Sparse Key := [(key27, -1), (key25, -1), (key25, 2), (key40, -1), (key37, -1), (key40, 2), (key25, 2), (key37, -1), (key25, -1), (key40, 2), (key40, -1), (key27, -1), (key52, 1), (key50, 1), (key50, -2), (key81, 1), (key76, 1), (key81, -2), (key50, -2), (key76, 1), (key50, 1), (key81, -2), (key81, 1), (key52, 1), (key120, -1), (key107, -1), (key117, 1), (key107, 1), (key144, 1), (key107, 1), (key139, -1), (key107, -1), (key162, -1), (key139, -1), (key162, 1), (key117, 1), (key162, 1), (key144, 1), (key162, -1), (key120, -1)]

theorem rawRowCheck5420 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5420 := by decide +kernel

def row5420 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

theorem rowCheck5420 : row5420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5420 := by decide +kernel

theorem rowEval5420 (x : Key → ℝ) : Integer.Sparse.eval row5420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5420, Integer.Sparse.eval_collectBalanced, rawRowCheck5420]

def rawRow5421 : Integer.Sparse Key := [(key37, -1), (key40, -1), (key40, 2), (key25, -1), (key27, -1), (key25, 2), (key40, 2), (key27, -1), (key40, -1), (key25, 2), (key25, -1), (key37, -1), (key76, 1), (key81, 1), (key81, -2), (key50, 1), (key52, 1), (key50, -2), (key81, -2), (key52, 1), (key81, 1), (key50, -2), (key50, 1), (key76, 1), (key139, -1), (key162, -1), (key144, 1), (key162, 1), (key117, 1), (key162, 1), (key120, -1), (key162, -1), (key107, -1), (key120, -1), (key107, 1), (key144, 1), (key107, 1), (key117, 1), (key107, -1), (key139, -1)]

theorem rawRowCheck5421 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5421 := by decide +kernel

def row5421 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

theorem rowCheck5421 : row5421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5421 := by decide +kernel

theorem rowEval5421 (x : Key → ℝ) : Integer.Sparse.eval row5421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5421, Integer.Sparse.eval_collectBalanced, rawRowCheck5421]

def rawRow5422 : Integer.Sparse Key := [(key40, -1), (key37, -1), (key40, 2), (key27, -1), (key25, -1), (key40, 2), (key25, 2), (key40, -1), (key27, -1), (key25, 2), (key37, -1), (key25, -1), (key81, 1), (key76, 1), (key81, -2), (key52, 1), (key50, 1), (key81, -2), (key50, -2), (key81, 1), (key52, 1), (key50, -2), (key76, 1), (key50, 1), (key162, -1), (key139, -1), (key162, 1), (key144, 1), (key162, 1), (key117, 1), (key162, -1), (key120, -1), (key120, -1), (key107, -1), (key144, 1), (key107, 1), (key117, 1), (key107, 1), (key139, -1), (key107, -1)]

theorem rawRowCheck5422 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5422 := by decide +kernel

def row5422 : Integer.Sparse Key := [(key25, 2), (key27, -2), (key37, -2), (key40, 2), (key50, -2), (key52, 2), (key76, 2), (key81, -2), (key117, 2), (key120, -2), (key139, -2), (key144, 2)]

theorem rowCheck5422 : row5422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5422 := by decide +kernel

theorem rowEval5422 (x : Key → ℝ) : Integer.Sparse.eval row5422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5422, Integer.Sparse.eval_collectBalanced, rawRowCheck5422]

def rawRow5423 : Integer.Sparse Key := [(key40, -1), (key40, -1), (key37, 2), (key40, -1), (key40, -1), (key27, 2), (key27, 2), (key25, -1), (key25, -1), (key37, 2), (key25, -1), (key25, -1), (key81, 1), (key81, 1), (key76, -2), (key81, 1), (key81, 1), (key52, -2), (key52, -2), (key50, 1), (key50, 1), (key76, -2), (key50, 1), (key50, 1), (key144, -1), (key144, -1), (key139, 1), (key139, 1), (key120, 1), (key120, 1), (key117, -1), (key117, -1), (key144, -1), (key144, -1), (key120, 1), (key120, 1), (key139, 1), (key139, 1), (key117, -1), (key117, -1)]

theorem rawRowCheck5423 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5423 := by decide +kernel

def row5423 : Integer.Sparse Key := [(key25, -4), (key27, 4), (key37, 4), (key40, -4), (key50, 4), (key52, -4), (key76, -4), (key81, 4), (key117, -4), (key120, 4), (key139, 4), (key144, -4)]

theorem rowCheck5423 : row5423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5423 := by decide +kernel

theorem rowEval5423 (x : Key → ℝ) : Integer.Sparse.eval row5423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5423, Integer.Sparse.eval_collectBalanced, rawRowCheck5423]

def rawRow5424 : Integer.Sparse Key := [(key379, -1), (key379, -1), (key382, 2), (key430, -1), (key430, -1), (key464, 2), (key464, 2), (key466, -1), (key466, -1), (key461, 2), (key483, -1), (key483, -1), (key210, 1), (key210, 1), (key213, -2), (key430, 1), (key430, 1), (key590, -2), (key590, -2), (key592, 1), (key592, 1), (key461, -2), (key609, 1), (key609, 1), (key37, -1), (key37, -1), (key40, 1), (key40, 1), (key76, 1), (key76, 1), (key81, -1), (key81, -1), (key117, -1), (key117, -1), (key139, 1), (key139, 1), (key197, 1), (key197, 1), (key201, -1), (key201, -1)]

theorem rawRowCheck5424 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1 = rawRow5424 := by decide +kernel

def row5424 : Integer.Sparse Key := [(key37, -2), (key40, 2), (key76, 2), (key81, -2), (key117, -2), (key139, 2), (key197, 2), (key201, -2), (key210, 2), (key213, -2), (key379, -2), (key382, 2), (key464, 4), (key466, -2), (key483, -2), (key590, -4), (key592, 2), (key609, 2)]

theorem rowCheck5424 : row5424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5424 := by decide +kernel

theorem rowEval5424 (x : Key → ℝ) : Integer.Sparse.eval row5424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5424, Integer.Sparse.eval_collectBalanced, rawRowCheck5424]

def rawRow5425 : Integer.Sparse Key := [(key379, -1), (key382, -1), (key379, 2), (key464, -1), (key466, -1), (key430, 2), (key466, 2), (key430, -1), (key464, -1), (key483, 2), (key461, -1), (key483, -1), (key210, 1), (key213, 1), (key210, -2), (key590, 1), (key592, 1), (key430, -2), (key592, -2), (key430, 1), (key590, 1), (key609, -2), (key461, 1), (key609, 1), (key25, -1), (key40, -1), (key25, 1), (key37, 1), (key50, 1), (key81, 1), (key50, -1), (key76, -1), (key139, -1), (key162, -1), (key117, 1), (key162, 1), (key201, 1), (key204, 1), (key197, -1), (key204, -1)]

theorem rawRowCheck5425 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1 = rawRow5425 := by decide +kernel

def row5425 : Integer.Sparse Key := [(key37, 1), (key40, -1), (key76, -1), (key81, 1), (key117, 1), (key139, -1), (key197, -1), (key201, 1), (key210, -1), (key213, 1), (key379, 1), (key382, -1), (key464, -2), (key466, 1), (key483, 1), (key590, 2), (key592, -1), (key609, -1)]

theorem rowCheck5425 : row5425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5425 := by decide +kernel

theorem rowEval5425 (x : Key → ℝ) : Integer.Sparse.eval row5425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5425, Integer.Sparse.eval_collectBalanced, rawRowCheck5425]

def rawRow5426 : Integer.Sparse Key := [(key382, -1), (key379, -1), (key379, 2), (key466, -1), (key464, -1), (key466, 2), (key430, 2), (key464, -1), (key430, -1), (key483, 2), (key483, -1), (key461, -1), (key213, 1), (key210, 1), (key210, -2), (key592, 1), (key590, 1), (key592, -2), (key430, -2), (key590, 1), (key430, 1), (key609, -2), (key609, 1), (key461, 1), (key40, -1), (key25, -1), (key37, 1), (key25, 1), (key81, 1), (key50, 1), (key76, -1), (key50, -1), (key162, -1), (key139, -1), (key162, 1), (key117, 1), (key204, 1), (key201, 1), (key204, -1), (key197, -1)]

theorem rawRowCheck5426 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1 = rawRow5426 := by decide +kernel

def row5426 : Integer.Sparse Key := [(key37, 1), (key40, -1), (key76, -1), (key81, 1), (key117, 1), (key139, -1), (key197, -1), (key201, 1), (key210, -1), (key213, 1), (key379, 1), (key382, -1), (key464, -2), (key466, 1), (key483, 1), (key590, 2), (key592, -1), (key609, -1)]

theorem rowCheck5426 : row5426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5426 := by decide +kernel

theorem rowEval5426 (x : Key → ℝ) : Integer.Sparse.eval row5426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5426, Integer.Sparse.eval_collectBalanced, rawRowCheck5426]

def rawRow5427 : Integer.Sparse Key := [(key430, -1), (key430, -1), (key461, 2), (key379, -1), (key379, -1), (key464, 2), (key464, 2), (key483, -1), (key483, -1), (key382, 2), (key466, -1), (key466, -1), (key430, 1), (key430, 1), (key461, -2), (key210, 1), (key210, 1), (key590, -2), (key590, -2), (key609, 1), (key609, 1), (key213, -2), (key592, 1), (key592, 1), (key464, -1), (key464, -1), (key483, 1), (key483, 1), (key590, 1), (key590, 1), (key609, -1), (key609, -1), (key37, -1), (key37, -1), (key76, 1), (key76, 1), (key40, 1), (key40, 1), (key81, -1), (key81, -1)]

theorem rawRowCheck5427 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1 = rawRow5427 := by decide +kernel

def row5427 : Integer.Sparse Key := [(key37, -2), (key40, 2), (key76, 2), (key81, -2), (key210, 2), (key213, -2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key590, -2), (key592, 2)]

theorem rowCheck5427 : row5427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5427 := by decide +kernel

theorem rowEval5427 (x : Key → ℝ) : Integer.Sparse.eval row5427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5427, Integer.Sparse.eval_collectBalanced, rawRowCheck5427]

def rawRow5428 : Integer.Sparse Key := [(key430, -1), (key461, -1), (key430, 2), (key464, -1), (key483, -1), (key379, 2), (key483, 2), (key379, -1), (key464, -1), (key466, 2), (key382, -1), (key466, -1), (key430, 1), (key461, 1), (key430, -2), (key590, 1), (key609, 1), (key210, -2), (key609, -2), (key210, 1), (key590, 1), (key592, -2), (key213, 1), (key592, 1), (key379, -1), (key483, -1), (key379, 1), (key464, 1), (key210, 1), (key609, 1), (key210, -1), (key590, -1), (key565, -1), (key615, -1), (key215, 1), (key615, 1), (key81, 1), (key162, 1), (key40, -1), (key162, -1)]

theorem rawRowCheck5428 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1 = rawRow5428 := by decide +kernel

def row5428 : Integer.Sparse Key := [(key40, -1), (key81, 1), (key210, -1), (key213, 1), (key215, 1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key590, 1), (key592, -1)]

theorem rowCheck5428 : row5428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5428 := by decide +kernel

theorem rowEval5428 (x : Key → ℝ) : Integer.Sparse.eval row5428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5428, Integer.Sparse.eval_collectBalanced, rawRowCheck5428]

def rawRow5429 : Integer.Sparse Key := [(key461, -1), (key430, -1), (key430, 2), (key483, -1), (key464, -1), (key483, 2), (key379, 2), (key464, -1), (key379, -1), (key466, 2), (key466, -1), (key382, -1), (key461, 1), (key430, 1), (key430, -2), (key609, 1), (key590, 1), (key609, -2), (key210, -2), (key590, 1), (key210, 1), (key592, -2), (key592, 1), (key213, 1), (key483, -1), (key379, -1), (key464, 1), (key379, 1), (key609, 1), (key210, 1), (key590, -1), (key210, -1), (key615, -1), (key565, -1), (key615, 1), (key215, 1), (key162, 1), (key81, 1), (key162, -1), (key40, -1)]

theorem rawRowCheck5429 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1 = rawRow5429 := by decide +kernel

def row5429 : Integer.Sparse Key := [(key40, -1), (key81, 1), (key210, -1), (key213, 1), (key215, 1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key590, 1), (key592, -1)]

theorem rowCheck5429 : row5429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5429 := by decide +kernel

theorem rowEval5429 (x : Key → ℝ) : Integer.Sparse.eval row5429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5429, Integer.Sparse.eval_collectBalanced, rawRowCheck5429]

def rawRow5430 : Integer.Sparse Key := [(key464, -1), (key466, -1), (key483, 2), (key379, -1), (key382, -1), (key430, 2), (key466, 2), (key461, -1), (key483, -1), (key379, 2), (key430, -1), (key464, -1), (key590, 1), (key592, 1), (key609, -2), (key210, 1), (key213, 1), (key430, -2), (key592, -2), (key461, 1), (key609, 1), (key210, -2), (key430, 1), (key590, 1), (key590, -1), (key612, -1), (key609, 1), (key615, 1), (key464, 1), (key612, 1), (key483, -1), (key615, -1), (key210, -1), (key217, -1), (key379, 1), (key567, 1), (key25, 1), (key37, 1), (key50, -1), (key76, -1)]

theorem rawRowCheck5430 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5430 := by decide +kernel

def row5430 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, -1), (key76, -1), (key210, -2), (key213, 1), (key217, -1), (key379, 2), (key382, -1), (key464, -1), (key466, 1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5430 : row5430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5430 := by decide +kernel

theorem rowEval5430 (x : Key → ℝ) : Integer.Sparse.eval row5430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5430, Integer.Sparse.eval_collectBalanced, rawRowCheck5430]

def rawRow5431 : Integer.Sparse Key := [(key466, -1), (key464, -1), (key483, 2), (key382, -1), (key379, -1), (key466, 2), (key430, 2), (key483, -1), (key461, -1), (key379, 2), (key464, -1), (key430, -1), (key592, 1), (key590, 1), (key609, -2), (key213, 1), (key210, 1), (key592, -2), (key430, -2), (key609, 1), (key461, 1), (key210, -2), (key590, 1), (key430, 1), (key612, -1), (key590, -1), (key615, 1), (key609, 1), (key612, 1), (key464, 1), (key615, -1), (key483, -1), (key217, -1), (key210, -1), (key567, 1), (key379, 1), (key37, 1), (key25, 1), (key76, -1), (key50, -1)]

theorem rawRowCheck5431 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5431 := by decide +kernel

def row5431 : Integer.Sparse Key := [(key25, 1), (key37, 1), (key50, -1), (key76, -1), (key210, -2), (key213, 1), (key217, -1), (key379, 2), (key382, -1), (key464, -1), (key466, 1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5431 : row5431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5431 := by decide +kernel

theorem rowEval5431 (x : Key → ℝ) : Integer.Sparse.eval row5431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5431, Integer.Sparse.eval_collectBalanced, rawRowCheck5431]

def rawRow5432 : Integer.Sparse Key := [(key464, -1), (key483, -1), (key466, 2), (key430, -1), (key461, -1), (key379, 2), (key483, 2), (key382, -1), (key466, -1), (key430, 2), (key379, -1), (key464, -1), (key590, 1), (key609, 1), (key592, -2), (key430, 1), (key461, 1), (key210, -2), (key609, -2), (key213, 1), (key592, 1), (key430, -2), (key210, 1), (key590, 1), (key565, -1), (key615, -1), (key567, 1), (key612, 1), (key215, 1), (key615, 1), (key217, -1), (key612, -1), (key379, -1), (key483, -1), (key210, 1), (key609, 1), (key50, 1), (key117, 1), (key25, -1), (key139, -1)]

theorem rawRowCheck5432 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5432 := by decide +kernel

def row5432 : Integer.Sparse Key := [(key25, -1), (key50, 1), (key117, 1), (key139, -1), (key213, 1), (key215, 1), (key217, -1), (key382, -1), (key464, -2), (key466, 1), (key565, -1), (key567, 1), (key590, 2), (key592, -1)]

theorem rowCheck5432 : row5432 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5432 := by decide +kernel

theorem rowEval5432 (x : Key → ℝ) : Integer.Sparse.eval row5432 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5432, Integer.Sparse.eval_collectBalanced, rawRowCheck5432]

def rawRow5433 : Integer.Sparse Key := [(key483, -1), (key464, -1), (key466, 2), (key461, -1), (key430, -1), (key483, 2), (key379, 2), (key466, -1), (key382, -1), (key430, 2), (key464, -1), (key379, -1), (key609, 1), (key590, 1), (key592, -2), (key461, 1), (key430, 1), (key609, -2), (key210, -2), (key592, 1), (key213, 1), (key430, -2), (key590, 1), (key210, 1), (key615, -1), (key565, -1), (key612, 1), (key567, 1), (key615, 1), (key215, 1), (key612, -1), (key217, -1), (key483, -1), (key379, -1), (key609, 1), (key210, 1), (key117, 1), (key50, 1), (key139, -1), (key25, -1)]

theorem rawRowCheck5433 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5433 := by decide +kernel

def row5433 : Integer.Sparse Key := [(key25, -1), (key50, 1), (key117, 1), (key139, -1), (key213, 1), (key215, 1), (key217, -1), (key382, -1), (key464, -2), (key466, 1), (key565, -1), (key567, 1), (key590, 2), (key592, -1)]

theorem rowCheck5433 : row5433 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5433 := by decide +kernel

theorem rowEval5433 (x : Key → ℝ) : Integer.Sparse.eval row5433 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5433, Integer.Sparse.eval_collectBalanced, rawRowCheck5433]

def rawRow5434 : Integer.Sparse Key := [(key466, -1), (key483, -1), (key464, 2), (key466, -1), (key483, -1), (key382, 2), (key461, 2), (key379, -1), (key430, -1), (key464, 2), (key379, -1), (key430, -1), (key592, 1), (key609, 1), (key590, -2), (key592, 1), (key609, 1), (key213, -2), (key461, -2), (key210, 1), (key430, 1), (key590, -2), (key210, 1), (key430, 1), (key567, -1), (key609, -1), (key565, 1), (key590, 1), (key217, 1), (key483, 1), (key215, -1), (key464, -1), (key567, -1), (key609, -1), (key217, 1), (key483, 1), (key76, 1), (key139, 1), (key37, -1), (key117, -1)]

theorem rawRowCheck5434 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5434 := by decide +kernel

def row5434 : Integer.Sparse Key := [(key37, -1), (key76, 1), (key117, -1), (key139, 1), (key210, 2), (key213, -2), (key215, -1), (key217, 2), (key379, -2), (key382, 2), (key464, 3), (key466, -2), (key565, 1), (key567, -2), (key590, -3), (key592, 2)]

theorem rowCheck5434 : row5434 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5434 := by decide +kernel

theorem rowEval5434 (x : Key → ℝ) : Integer.Sparse.eval row5434 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5434, Integer.Sparse.eval_collectBalanced, rawRowCheck5434]

def rawRow5435 : Integer.Sparse Key := [(key483, -1), (key466, -1), (key464, 2), (key483, -1), (key466, -1), (key461, 2), (key382, 2), (key430, -1), (key379, -1), (key464, 2), (key430, -1), (key379, -1), (key609, 1), (key592, 1), (key590, -2), (key609, 1), (key592, 1), (key461, -2), (key213, -2), (key430, 1), (key210, 1), (key590, -2), (key430, 1), (key210, 1), (key609, -1), (key567, -1), (key590, 1), (key565, 1), (key483, 1), (key217, 1), (key464, -1), (key215, -1), (key609, -1), (key567, -1), (key483, 1), (key217, 1), (key139, 1), (key76, 1), (key117, -1), (key37, -1)]

theorem rawRowCheck5435 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5435 := by decide +kernel

def row5435 : Integer.Sparse Key := [(key37, -1), (key76, 1), (key117, -1), (key139, 1), (key210, 2), (key213, -2), (key215, -1), (key217, 2), (key379, -2), (key382, 2), (key464, 3), (key466, -2), (key565, 1), (key567, -2), (key590, -3), (key592, 2)]

theorem rowCheck5435 : row5435 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5435 := by decide +kernel

theorem rowEval5435 (x : Key → ℝ) : Integer.Sparse.eval row5435 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5435, Integer.Sparse.eval_collectBalanced, rawRowCheck5435]

def rawRow5436 : Integer.Sparse Key := [(key565, -1), (key567, -1), (key567, 2), (key590, -1), (key592, -1), (key590, 2), (key612, 2), (key592, -1), (key612, -1), (key609, 2), (key609, -1), (key615, -1), (key215, 1), (key217, 1), (key217, -2), (key464, 1), (key466, 1), (key464, -2), (key612, -2), (key466, 1), (key612, 1), (key483, -2), (key483, 1), (key615, 1), (key210, -1), (key217, -1), (key213, 1), (key217, 1), (key379, 1), (key567, 1), (key382, -1), (key567, -1), (key430, -1), (key466, -1), (key430, 1), (key592, 1), (key461, 1), (key483, 1), (key461, -1), (key609, -1)]

theorem rawRowCheck5436 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1 = rawRow5436 := by decide +kernel

def row5436 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5436 : row5436 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5436 := by decide +kernel

theorem rowEval5436 (x : Key → ℝ) : Integer.Sparse.eval row5436 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5436, Integer.Sparse.eval_collectBalanced, rawRowCheck5436]

def rawRow5437 : Integer.Sparse Key := [(key567, -1), (key565, -1), (key567, 2), (key592, -1), (key590, -1), (key612, 2), (key590, 2), (key612, -1), (key592, -1), (key609, 2), (key615, -1), (key609, -1), (key217, 1), (key215, 1), (key217, -2), (key466, 1), (key464, 1), (key612, -2), (key464, -2), (key612, 1), (key466, 1), (key483, -2), (key615, 1), (key483, 1), (key217, -1), (key210, -1), (key217, 1), (key213, 1), (key567, 1), (key379, 1), (key567, -1), (key382, -1), (key466, -1), (key430, -1), (key592, 1), (key430, 1), (key483, 1), (key461, 1), (key609, -1), (key461, -1)]

theorem rawRowCheck5437 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1 = rawRow5437 := by decide +kernel

def row5437 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5437 : row5437 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5437 := by decide +kernel

theorem rowEval5437 (x : Key → ℝ) : Integer.Sparse.eval row5437 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5437, Integer.Sparse.eval_collectBalanced, rawRowCheck5437]

def rawRow5438 : Integer.Sparse Key := [(key567, -1), (key567, -1), (key565, 2), (key612, -1), (key612, -1), (key592, 2), (key592, 2), (key590, -1), (key590, -1), (key615, 2), (key609, -1), (key609, -1), (key217, 1), (key217, 1), (key215, -2), (key612, 1), (key612, 1), (key466, -2), (key466, -2), (key464, 1), (key464, 1), (key615, -2), (key483, 1), (key483, 1), (key213, -1), (key213, -1), (key210, 1), (key210, 1), (key382, 1), (key382, 1), (key379, -1), (key379, -1), (key592, -1), (key592, -1), (key466, 1), (key466, 1), (key609, 1), (key609, 1), (key483, -1), (key483, -1)]

theorem rawRowCheck5438 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1 = rawRow5438 := by decide +kernel

def row5438 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

theorem rowCheck5438 : row5438 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5438 := by decide +kernel

theorem rowEval5438 (x : Key → ℝ) : Integer.Sparse.eval row5438 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5438, Integer.Sparse.eval_collectBalanced, rawRowCheck5438]

def rawRow5439 : Integer.Sparse Key := [(key590, -1), (key592, -1), (key609, 2), (key565, -1), (key567, -1), (key590, 2), (key612, 2), (key609, -1), (key615, -1), (key567, 2), (key592, -1), (key612, -1), (key464, 1), (key466, 1), (key483, -2), (key215, 1), (key217, 1), (key464, -2), (key612, -2), (key483, 1), (key615, 1), (key217, -2), (key466, 1), (key612, 1), (key430, -1), (key466, -1), (key461, 1), (key483, 1), (key430, 1), (key592, 1), (key461, -1), (key609, -1), (key210, -1), (key217, -1), (key379, 1), (key567, 1), (key213, 1), (key217, 1), (key382, -1), (key567, -1)]

theorem rawRowCheck5439 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1 = rawRow5439 := by decide +kernel

def row5439 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5439 : row5439 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5439 := by decide +kernel

theorem rowEval5439 (x : Key → ℝ) : Integer.Sparse.eval row5439 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5439, Integer.Sparse.eval_collectBalanced, rawRowCheck5439]

def rawRow5440 : Integer.Sparse Key := [(key592, -1), (key590, -1), (key609, 2), (key567, -1), (key565, -1), (key612, 2), (key590, 2), (key615, -1), (key609, -1), (key567, 2), (key612, -1), (key592, -1), (key466, 1), (key464, 1), (key483, -2), (key217, 1), (key215, 1), (key612, -2), (key464, -2), (key615, 1), (key483, 1), (key217, -2), (key612, 1), (key466, 1), (key466, -1), (key430, -1), (key483, 1), (key461, 1), (key592, 1), (key430, 1), (key609, -1), (key461, -1), (key217, -1), (key210, -1), (key567, 1), (key379, 1), (key217, 1), (key213, 1), (key567, -1), (key382, -1)]

theorem rawRowCheck5440 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1 = rawRow5440 := by decide +kernel

def row5440 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5440 : row5440 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5440 := by decide +kernel

theorem rowEval5440 (x : Key → ℝ) : Integer.Sparse.eval row5440 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5440, Integer.Sparse.eval_collectBalanced, rawRowCheck5440]

def rawRow5441 : Integer.Sparse Key := [(key590, -1), (key609, -1), (key592, 2), (key590, -1), (key609, -1), (key565, 2), (key615, 2), (key567, -1), (key612, -1), (key592, 2), (key567, -1), (key612, -1), (key464, 1), (key483, 1), (key466, -2), (key464, 1), (key483, 1), (key215, -2), (key615, -2), (key217, 1), (key612, 1), (key466, -2), (key217, 1), (key612, 1), (key379, -1), (key483, -1), (key382, 1), (key466, 1), (key210, 1), (key609, 1), (key213, -1), (key592, -1), (key379, -1), (key483, -1), (key210, 1), (key609, 1), (key382, 1), (key466, 1), (key213, -1), (key592, -1)]

theorem rawRowCheck5441 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1 = rawRow5441 := by decide +kernel

def row5441 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

theorem rowCheck5441 : row5441 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5441 := by decide +kernel

theorem rowEval5441 (x : Key → ℝ) : Integer.Sparse.eval row5441 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck5441, Integer.Sparse.eval_collectBalanced, rawRowCheck5441]

def rawRow5442 : Integer.Sparse Key := [(key609, -1), (key590, -1), (key592, 2), (key609, -1), (key590, -1), (key615, 2), (key565, 2), (key612, -1), (key567, -1), (key592, 2), (key612, -1), (key567, -1), (key483, 1), (key464, 1), (key466, -2), (key483, 1), (key464, 1), (key615, -2), (key215, -2), (key612, 1), (key217, 1), (key466, -2), (key612, 1), (key217, 1), (key483, -1), (key379, -1), (key466, 1), (key382, 1), (key609, 1), (key210, 1), (key592, -1), (key213, -1), (key483, -1), (key379, -1), (key609, 1), (key210, 1), (key466, 1), (key382, 1), (key592, -1), (key213, -1)]

theorem rawRowCheck5442 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1 = rawRow5442 := by decide +kernel

def row5442 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

theorem rowCheck5442 : row5442 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5442 := by decide +kernel

theorem rowEval5442 (x : Key → ℝ) : Integer.Sparse.eval row5442 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5442, Integer.Sparse.eval_collectBalanced, rawRowCheck5442]

def rawRow5443 : Integer.Sparse Key := [(key592, -1), (key609, -1), (key590, 2), (key612, -1), (key615, -1), (key567, 2), (key609, 2), (key565, -1), (key590, -1), (key612, 2), (key567, -1), (key592, -1), (key466, 1), (key483, 1), (key464, -2), (key612, 1), (key615, 1), (key217, -2), (key483, -2), (key215, 1), (key464, 1), (key612, -2), (key217, 1), (key466, 1), (key382, -1), (key461, -1), (key379, 1), (key430, 1), (key213, 1), (key461, 1), (key210, -1), (key430, -1), (key567, -1), (key609, -1), (key217, 1), (key483, 1), (key567, 1), (key592, 1), (key217, -1), (key466, -1)]

theorem rawRowCheck5443 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1 = rawRow5443 := by decide +kernel

def row5443 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5443 : row5443 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5443 := by decide +kernel

theorem rowEval5443 (x : Key → ℝ) : Integer.Sparse.eval row5443 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5443, Integer.Sparse.eval_collectBalanced, rawRowCheck5443]

def rawRow5444 : Integer.Sparse Key := [(key609, -1), (key592, -1), (key590, 2), (key615, -1), (key612, -1), (key609, 2), (key567, 2), (key590, -1), (key565, -1), (key612, 2), (key592, -1), (key567, -1), (key483, 1), (key466, 1), (key464, -2), (key615, 1), (key612, 1), (key483, -2), (key217, -2), (key464, 1), (key215, 1), (key612, -2), (key466, 1), (key217, 1), (key461, -1), (key382, -1), (key430, 1), (key379, 1), (key461, 1), (key213, 1), (key430, -1), (key210, -1), (key609, -1), (key567, -1), (key483, 1), (key217, 1), (key592, 1), (key567, 1), (key466, -1), (key217, -1)]

theorem rawRowCheck5444 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1 = rawRow5444 := by decide +kernel

def row5444 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5444 : row5444 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5444 := by decide +kernel

theorem rowEval5444 (x : Key → ℝ) : Integer.Sparse.eval row5444 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5444, Integer.Sparse.eval_collectBalanced, rawRowCheck5444]

def rawRow5445 : Integer.Sparse Key := [(key612, -1), (key612, -1), (key615, 2), (key567, -1), (key567, -1), (key592, 2), (key592, 2), (key609, -1), (key609, -1), (key565, 2), (key590, -1), (key590, -1), (key612, 1), (key612, 1), (key615, -2), (key217, 1), (key217, 1), (key466, -2), (key466, -2), (key483, 1), (key483, 1), (key215, -2), (key464, 1), (key464, 1), (key592, -1), (key592, -1), (key609, 1), (key609, 1), (key466, 1), (key466, 1), (key483, -1), (key483, -1), (key213, -1), (key213, -1), (key382, 1), (key382, 1), (key210, 1), (key210, 1), (key379, -1), (key379, -1)]

theorem rawRowCheck5445 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1 = rawRow5445 := by decide +kernel

def row5445 : Integer.Sparse Key := [(key210, 2), (key213, -2), (key215, -2), (key217, 2), (key379, -2), (key382, 2), (key464, 2), (key466, -2), (key565, 2), (key567, -2), (key590, -2), (key592, 2)]

theorem rowCheck5445 : row5445 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5445 := by decide +kernel

theorem rowEval5445 (x : Key → ℝ) : Integer.Sparse.eval row5445 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5445, Integer.Sparse.eval_collectBalanced, rawRowCheck5445]

def rawRow5446 : Integer.Sparse Key := [(key612, -1), (key615, -1), (key612, 2), (key592, -1), (key609, -1), (key567, 2), (key609, 2), (key567, -1), (key592, -1), (key590, 2), (key565, -1), (key590, -1), (key612, 1), (key615, 1), (key612, -2), (key466, 1), (key483, 1), (key217, -2), (key483, -2), (key217, 1), (key466, 1), (key464, -2), (key215, 1), (key464, 1), (key567, -1), (key609, -1), (key567, 1), (key592, 1), (key217, 1), (key483, 1), (key217, -1), (key466, -1), (key382, -1), (key461, -1), (key213, 1), (key461, 1), (key379, 1), (key430, 1), (key210, -1), (key430, -1)]

theorem rawRowCheck5446 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1 = rawRow5446 := by decide +kernel

def row5446 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5446 : row5446 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5446 := by decide +kernel

theorem rowEval5446 (x : Key → ℝ) : Integer.Sparse.eval row5446 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck5446, Integer.Sparse.eval_collectBalanced, rawRowCheck5446]

def rawRow5447 : Integer.Sparse Key := [(key615, -1), (key612, -1), (key612, 2), (key609, -1), (key592, -1), (key609, 2), (key567, 2), (key592, -1), (key567, -1), (key590, 2), (key590, -1), (key565, -1), (key615, 1), (key612, 1), (key612, -2), (key483, 1), (key466, 1), (key483, -2), (key217, -2), (key466, 1), (key217, 1), (key464, -2), (key464, 1), (key215, 1), (key609, -1), (key567, -1), (key592, 1), (key567, 1), (key483, 1), (key217, 1), (key466, -1), (key217, -1), (key461, -1), (key382, -1), (key461, 1), (key213, 1), (key430, 1), (key379, 1), (key430, -1), (key210, -1)]

theorem rawRowCheck5447 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1 = rawRow5447 := by decide +kernel

def row5447 : Integer.Sparse Key := [(key210, -1), (key213, 1), (key215, 1), (key217, -1), (key379, 1), (key382, -1), (key464, -1), (key466, 1), (key565, -1), (key567, 1), (key590, 1), (key592, -1)]

theorem rowCheck5447 : row5447 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5447 := by decide +kernel

theorem rowEval5447 (x : Key → ℝ) : Integer.Sparse.eval row5447 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form1) x := by
  rw [rowCheck5447, Integer.Sparse.eval_collectBalanced, rawRowCheck5447]

def rawRow5448 : Integer.Sparse Key := [(key1003, -1), (key1003, -1), (key1007, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1017, 2), (key1020, -1), (key1020, -1), (key1007, 2), (key1020, -1), (key1020, -1), (key1038, 1), (key1038, 1), (key1042, -2), (key1038, 1), (key1038, 1), (key1073, -2), (key1073, -2), (key1077, 1), (key1077, 1), (key1042, -2), (key1077, 1), (key1077, 1), (key1125, -1), (key1125, -1), (key1128, 1), (key1128, 1), (key1152, 1), (key1152, 1), (key1156, -1), (key1156, -1), (key1125, -1), (key1125, -1), (key1152, 1), (key1152, 1), (key1128, 1), (key1128, 1), (key1156, -1), (key1156, -1)]

theorem rawRowCheck5448 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form2 = rawRow5448 := by decide +kernel

def row5448 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, 4), (key1042, -4), (key1073, -4), (key1077, 4), (key1125, -4), (key1128, 4), (key1152, 4), (key1156, -4)]

theorem rowCheck5448 : row5448 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5448 := by decide +kernel

theorem rowEval5448 (x : Key → ℝ) : Integer.Sparse.eval row5448 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5448, Integer.Sparse.eval_collectBalanced, rawRowCheck5448]

def rawRow5449 : Integer.Sparse Key := [(key1003, -1), (key1007, -1), (key1003, 2), (key1017, -1), (key1020, -1), (key1003, 2), (key1020, 2), (key1003, -1), (key1017, -1), (key1020, 2), (key1007, -1), (key1020, -1), (key1038, 1), (key1042, 1), (key1038, -2), (key1073, 1), (key1077, 1), (key1038, -2), (key1077, -2), (key1038, 1), (key1073, 1), (key1077, -2), (key1042, 1), (key1077, 1), (key1116, -1), (key1128, -1), (key1116, 1), (key1125, 1), (key1116, 1), (key1156, 1), (key1116, -1), (key1152, -1), (key1152, -1), (key1172, -1), (key1125, 1), (key1172, 1), (key1156, 1), (key1172, 1), (key1128, -1), (key1172, -1)]

theorem rawRowCheck5449 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form2 = rawRow5449 := by decide +kernel

def row5449 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5449 : row5449 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5449 := by decide +kernel

theorem rowEval5449 (x : Key → ℝ) : Integer.Sparse.eval row5449 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5449, Integer.Sparse.eval_collectBalanced, rawRowCheck5449]

def rawRow5450 : Integer.Sparse Key := [(key1007, -1), (key1003, -1), (key1003, 2), (key1020, -1), (key1017, -1), (key1020, 2), (key1003, 2), (key1017, -1), (key1003, -1), (key1020, 2), (key1020, -1), (key1007, -1), (key1042, 1), (key1038, 1), (key1038, -2), (key1077, 1), (key1073, 1), (key1077, -2), (key1038, -2), (key1073, 1), (key1038, 1), (key1077, -2), (key1077, 1), (key1042, 1), (key1128, -1), (key1116, -1), (key1125, 1), (key1116, 1), (key1156, 1), (key1116, 1), (key1152, -1), (key1116, -1), (key1172, -1), (key1152, -1), (key1172, 1), (key1125, 1), (key1172, 1), (key1156, 1), (key1172, -1), (key1128, -1)]

theorem rawRowCheck5450 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form2 = rawRow5450 := by decide +kernel

def row5450 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5450 : row5450 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5450 := by decide +kernel

theorem rowEval5450 (x : Key → ℝ) : Integer.Sparse.eval row5450 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5450, Integer.Sparse.eval_collectBalanced, rawRowCheck5450]

def rawRow5451 : Integer.Sparse Key := [(key1017, -1), (key1020, -1), (key1020, 2), (key1003, -1), (key1007, -1), (key1003, 2), (key1020, 2), (key1007, -1), (key1020, -1), (key1003, 2), (key1003, -1), (key1017, -1), (key1073, 1), (key1077, 1), (key1077, -2), (key1038, 1), (key1042, 1), (key1038, -2), (key1077, -2), (key1042, 1), (key1077, 1), (key1038, -2), (key1038, 1), (key1073, 1), (key1152, -1), (key1172, -1), (key1156, 1), (key1172, 1), (key1125, 1), (key1172, 1), (key1128, -1), (key1172, -1), (key1116, -1), (key1128, -1), (key1116, 1), (key1156, 1), (key1116, 1), (key1125, 1), (key1116, -1), (key1152, -1)]

theorem rawRowCheck5451 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5451 := by decide +kernel

def row5451 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5451 : row5451 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5451 := by decide +kernel

theorem rowEval5451 (x : Key → ℝ) : Integer.Sparse.eval row5451 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5451, Integer.Sparse.eval_collectBalanced, rawRowCheck5451]

def rawRow5452 : Integer.Sparse Key := [(key1020, -1), (key1017, -1), (key1020, 2), (key1007, -1), (key1003, -1), (key1020, 2), (key1003, 2), (key1020, -1), (key1007, -1), (key1003, 2), (key1017, -1), (key1003, -1), (key1077, 1), (key1073, 1), (key1077, -2), (key1042, 1), (key1038, 1), (key1077, -2), (key1038, -2), (key1077, 1), (key1042, 1), (key1038, -2), (key1073, 1), (key1038, 1), (key1172, -1), (key1152, -1), (key1172, 1), (key1156, 1), (key1172, 1), (key1125, 1), (key1172, -1), (key1128, -1), (key1128, -1), (key1116, -1), (key1156, 1), (key1116, 1), (key1125, 1), (key1116, 1), (key1152, -1), (key1116, -1)]

theorem rawRowCheck5452 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5452 := by decide +kernel

def row5452 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5452 : row5452 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5452 := by decide +kernel

theorem rowEval5452 (x : Key → ℝ) : Integer.Sparse.eval row5452 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5452, Integer.Sparse.eval_collectBalanced, rawRowCheck5452]

def rawRow5453 : Integer.Sparse Key := [(key1020, -1), (key1020, -1), (key1017, 2), (key1020, -1), (key1020, -1), (key1007, 2), (key1007, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1003, -1), (key1003, -1), (key1077, 1), (key1077, 1), (key1073, -2), (key1077, 1), (key1077, 1), (key1042, -2), (key1042, -2), (key1038, 1), (key1038, 1), (key1073, -2), (key1038, 1), (key1038, 1), (key1156, -1), (key1156, -1), (key1152, 1), (key1152, 1), (key1128, 1), (key1128, 1), (key1125, -1), (key1125, -1), (key1156, -1), (key1156, -1), (key1128, 1), (key1128, 1), (key1152, 1), (key1152, 1), (key1125, -1), (key1125, -1)]

theorem rawRowCheck5453 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5453 := by decide +kernel

def row5453 : Integer.Sparse Key := [(key1003, -4), (key1007, 4), (key1017, 4), (key1020, -4), (key1038, 4), (key1042, -4), (key1073, -4), (key1077, 4), (key1125, -4), (key1128, 4), (key1152, 4), (key1156, -4)]

theorem rowCheck5453 : row5453 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5453 := by decide +kernel

theorem rowEval5453 (x : Key → ℝ) : Integer.Sparse.eval row5453 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5453, Integer.Sparse.eval_collectBalanced, rawRowCheck5453]

def rawRow5454 : Integer.Sparse Key := [(key1038, -1), (key1038, -1), (key1042, 2), (key1116, -1), (key1116, -1), (key1125, 2), (key1125, 2), (key1128, -1), (key1128, -1), (key1194, 2), (key1200, -1), (key1200, -1), (key1003, 1), (key1003, 1), (key1007, -2), (key1116, 1), (key1116, 1), (key1152, -2), (key1152, -2), (key1156, 1), (key1156, 1), (key1194, -2), (key1213, 1), (key1213, 1), (key1017, -1), (key1017, -1), (key1020, 1), (key1020, 1), (key1073, 1), (key1073, 1), (key1077, -1), (key1077, -1), (key1125, -1), (key1125, -1), (key1152, 1), (key1152, 1), (key1200, 1), (key1200, 1), (key1213, -1), (key1213, -1)]

theorem rawRowCheck5454 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form2 = rawRow5454 := by decide +kernel

def row5454 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5454 : row5454 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5454 := by decide +kernel

theorem rowEval5454 (x : Key → ℝ) : Integer.Sparse.eval row5454 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5454, Integer.Sparse.eval_collectBalanced, rawRowCheck5454]

def rawRow5455 : Integer.Sparse Key := [(key1038, -1), (key1042, -1), (key1038, 2), (key1125, -1), (key1128, -1), (key1116, 2), (key1128, 2), (key1116, -1), (key1125, -1), (key1200, 2), (key1194, -1), (key1200, -1), (key1003, 1), (key1007, 1), (key1003, -2), (key1152, 1), (key1156, 1), (key1116, -2), (key1156, -2), (key1116, 1), (key1152, 1), (key1213, -2), (key1194, 1), (key1213, 1), (key1003, -1), (key1020, -1), (key1003, 1), (key1017, 1), (key1038, 1), (key1077, 1), (key1038, -1), (key1073, -1), (key1152, -1), (key1172, -1), (key1125, 1), (key1172, 1), (key1213, 1), (key1223, 1), (key1200, -1), (key1223, -1)]

theorem rawRowCheck5455 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form2 = rawRow5455 := by decide +kernel

def row5455 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5455 : row5455 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5455 := by decide +kernel

theorem rowEval5455 (x : Key → ℝ) : Integer.Sparse.eval row5455 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5455, Integer.Sparse.eval_collectBalanced, rawRowCheck5455]

def rawRow5456 : Integer.Sparse Key := [(key1042, -1), (key1038, -1), (key1038, 2), (key1128, -1), (key1125, -1), (key1128, 2), (key1116, 2), (key1125, -1), (key1116, -1), (key1200, 2), (key1200, -1), (key1194, -1), (key1007, 1), (key1003, 1), (key1003, -2), (key1156, 1), (key1152, 1), (key1156, -2), (key1116, -2), (key1152, 1), (key1116, 1), (key1213, -2), (key1213, 1), (key1194, 1), (key1020, -1), (key1003, -1), (key1017, 1), (key1003, 1), (key1077, 1), (key1038, 1), (key1073, -1), (key1038, -1), (key1172, -1), (key1152, -1), (key1172, 1), (key1125, 1), (key1223, 1), (key1213, 1), (key1223, -1), (key1200, -1)]

theorem rawRowCheck5456 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form2 = rawRow5456 := by decide +kernel

def row5456 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5456 : row5456 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5456 := by decide +kernel

theorem rowEval5456 (x : Key → ℝ) : Integer.Sparse.eval row5456 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5456, Integer.Sparse.eval_collectBalanced, rawRowCheck5456]

def rawRow5457 : Integer.Sparse Key := [(key1116, -1), (key1116, -1), (key1194, 2), (key1038, -1), (key1038, -1), (key1125, 2), (key1125, 2), (key1200, -1), (key1200, -1), (key1042, 2), (key1128, -1), (key1128, -1), (key1116, 1), (key1116, 1), (key1194, -2), (key1003, 1), (key1003, 1), (key1152, -2), (key1152, -2), (key1213, 1), (key1213, 1), (key1007, -2), (key1156, 1), (key1156, 1), (key1125, -1), (key1125, -1), (key1200, 1), (key1200, 1), (key1152, 1), (key1152, 1), (key1213, -1), (key1213, -1), (key1017, -1), (key1017, -1), (key1073, 1), (key1073, 1), (key1020, 1), (key1020, 1), (key1077, -1), (key1077, -1)]

theorem rawRowCheck5457 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form2 = rawRow5457 := by decide +kernel

def row5457 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5457 : row5457 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5457 := by decide +kernel

theorem rowEval5457 (x : Key → ℝ) : Integer.Sparse.eval row5457 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5457, Integer.Sparse.eval_collectBalanced, rawRowCheck5457]

def rawRow5458 : Integer.Sparse Key := [(key1116, -1), (key1194, -1), (key1116, 2), (key1125, -1), (key1200, -1), (key1038, 2), (key1200, 2), (key1038, -1), (key1125, -1), (key1128, 2), (key1042, -1), (key1128, -1), (key1116, 1), (key1194, 1), (key1116, -2), (key1152, 1), (key1213, 1), (key1003, -2), (key1213, -2), (key1003, 1), (key1152, 1), (key1156, -2), (key1007, 1), (key1156, 1), (key1038, -1), (key1200, -1), (key1038, 1), (key1125, 1), (key1003, 1), (key1213, 1), (key1003, -1), (key1152, -1), (key1073, -1), (key1223, -1), (key1017, 1), (key1223, 1), (key1077, 1), (key1172, 1), (key1020, -1), (key1172, -1)]

theorem rawRowCheck5458 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form2 = rawRow5458 := by decide +kernel

def row5458 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5458 : row5458 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5458 := by decide +kernel

theorem rowEval5458 (x : Key → ℝ) : Integer.Sparse.eval row5458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5458, Integer.Sparse.eval_collectBalanced, rawRowCheck5458]

def rawRow5459 : Integer.Sparse Key := [(key1194, -1), (key1116, -1), (key1116, 2), (key1200, -1), (key1125, -1), (key1200, 2), (key1038, 2), (key1125, -1), (key1038, -1), (key1128, 2), (key1128, -1), (key1042, -1), (key1194, 1), (key1116, 1), (key1116, -2), (key1213, 1), (key1152, 1), (key1213, -2), (key1003, -2), (key1152, 1), (key1003, 1), (key1156, -2), (key1156, 1), (key1007, 1), (key1200, -1), (key1038, -1), (key1125, 1), (key1038, 1), (key1213, 1), (key1003, 1), (key1152, -1), (key1003, -1), (key1223, -1), (key1073, -1), (key1223, 1), (key1017, 1), (key1172, 1), (key1077, 1), (key1172, -1), (key1020, -1)]

theorem rawRowCheck5459 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form2 = rawRow5459 := by decide +kernel

def row5459 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5459 : row5459 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5459 := by decide +kernel

theorem rowEval5459 (x : Key → ℝ) : Integer.Sparse.eval row5459 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5459, Integer.Sparse.eval_collectBalanced, rawRowCheck5459]

def rawRow5460 : Integer.Sparse Key := [(key1125, -1), (key1128, -1), (key1200, 2), (key1038, -1), (key1042, -1), (key1116, 2), (key1128, 2), (key1194, -1), (key1200, -1), (key1038, 2), (key1116, -1), (key1125, -1), (key1152, 1), (key1156, 1), (key1213, -2), (key1003, 1), (key1007, 1), (key1116, -2), (key1156, -2), (key1194, 1), (key1213, 1), (key1003, -2), (key1116, 1), (key1152, 1), (key1152, -1), (key1172, -1), (key1213, 1), (key1223, 1), (key1125, 1), (key1172, 1), (key1200, -1), (key1223, -1), (key1003, -1), (key1020, -1), (key1038, 1), (key1077, 1), (key1003, 1), (key1017, 1), (key1038, -1), (key1073, -1)]

theorem rawRowCheck5460 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form2 = rawRow5460 := by decide +kernel

def row5460 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5460 : row5460 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5460 := by decide +kernel

theorem rowEval5460 (x : Key → ℝ) : Integer.Sparse.eval row5460 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5460, Integer.Sparse.eval_collectBalanced, rawRowCheck5460]

def rawRow5461 : Integer.Sparse Key := [(key1128, -1), (key1125, -1), (key1200, 2), (key1042, -1), (key1038, -1), (key1128, 2), (key1116, 2), (key1200, -1), (key1194, -1), (key1038, 2), (key1125, -1), (key1116, -1), (key1156, 1), (key1152, 1), (key1213, -2), (key1007, 1), (key1003, 1), (key1156, -2), (key1116, -2), (key1213, 1), (key1194, 1), (key1003, -2), (key1152, 1), (key1116, 1), (key1172, -1), (key1152, -1), (key1223, 1), (key1213, 1), (key1172, 1), (key1125, 1), (key1223, -1), (key1200, -1), (key1020, -1), (key1003, -1), (key1077, 1), (key1038, 1), (key1017, 1), (key1003, 1), (key1073, -1), (key1038, -1)]

theorem rawRowCheck5461 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form2 = rawRow5461 := by decide +kernel

def row5461 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5461 : row5461 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5461 := by decide +kernel

theorem rowEval5461 (x : Key → ℝ) : Integer.Sparse.eval row5461 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5461, Integer.Sparse.eval_collectBalanced, rawRowCheck5461]

def rawRow5462 : Integer.Sparse Key := [(key1125, -1), (key1200, -1), (key1128, 2), (key1116, -1), (key1194, -1), (key1038, 2), (key1200, 2), (key1042, -1), (key1128, -1), (key1116, 2), (key1038, -1), (key1125, -1), (key1152, 1), (key1213, 1), (key1156, -2), (key1116, 1), (key1194, 1), (key1003, -2), (key1213, -2), (key1007, 1), (key1156, 1), (key1116, -2), (key1003, 1), (key1152, 1), (key1073, -1), (key1223, -1), (key1077, 1), (key1172, 1), (key1017, 1), (key1223, 1), (key1020, -1), (key1172, -1), (key1038, -1), (key1200, -1), (key1003, 1), (key1213, 1), (key1038, 1), (key1125, 1), (key1003, -1), (key1152, -1)]

theorem rawRowCheck5462 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form2 = rawRow5462 := by decide +kernel

def row5462 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5462 : row5462 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5462 := by decide +kernel

theorem rowEval5462 (x : Key → ℝ) : Integer.Sparse.eval row5462 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5462, Integer.Sparse.eval_collectBalanced, rawRowCheck5462]

def rawRow5463 : Integer.Sparse Key := [(key1200, -1), (key1125, -1), (key1128, 2), (key1194, -1), (key1116, -1), (key1200, 2), (key1038, 2), (key1128, -1), (key1042, -1), (key1116, 2), (key1125, -1), (key1038, -1), (key1213, 1), (key1152, 1), (key1156, -2), (key1194, 1), (key1116, 1), (key1213, -2), (key1003, -2), (key1156, 1), (key1007, 1), (key1116, -2), (key1152, 1), (key1003, 1), (key1223, -1), (key1073, -1), (key1172, 1), (key1077, 1), (key1223, 1), (key1017, 1), (key1172, -1), (key1020, -1), (key1200, -1), (key1038, -1), (key1213, 1), (key1003, 1), (key1125, 1), (key1038, 1), (key1152, -1), (key1003, -1)]

theorem rawRowCheck5463 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form2 = rawRow5463 := by decide +kernel

def row5463 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5463 : row5463 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5463 := by decide +kernel

theorem rowEval5463 (x : Key → ℝ) : Integer.Sparse.eval row5463 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5463, Integer.Sparse.eval_collectBalanced, rawRowCheck5463]

def rawRow5464 : Integer.Sparse Key := [(key1128, -1), (key1200, -1), (key1125, 2), (key1128, -1), (key1200, -1), (key1042, 2), (key1194, 2), (key1038, -1), (key1116, -1), (key1125, 2), (key1038, -1), (key1116, -1), (key1156, 1), (key1213, 1), (key1152, -2), (key1156, 1), (key1213, 1), (key1007, -2), (key1194, -2), (key1003, 1), (key1116, 1), (key1152, -2), (key1003, 1), (key1116, 1), (key1077, -1), (key1213, -1), (key1073, 1), (key1152, 1), (key1020, 1), (key1200, 1), (key1017, -1), (key1125, -1), (key1077, -1), (key1213, -1), (key1020, 1), (key1200, 1), (key1073, 1), (key1152, 1), (key1017, -1), (key1125, -1)]

theorem rawRowCheck5464 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form2 = rawRow5464 := by decide +kernel

def row5464 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5464 : row5464 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5464 := by decide +kernel

theorem rowEval5464 (x : Key → ℝ) : Integer.Sparse.eval row5464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5464, Integer.Sparse.eval_collectBalanced, rawRowCheck5464]

def rawRow5465 : Integer.Sparse Key := [(key1200, -1), (key1128, -1), (key1125, 2), (key1200, -1), (key1128, -1), (key1194, 2), (key1042, 2), (key1116, -1), (key1038, -1), (key1125, 2), (key1116, -1), (key1038, -1), (key1213, 1), (key1156, 1), (key1152, -2), (key1213, 1), (key1156, 1), (key1194, -2), (key1007, -2), (key1116, 1), (key1003, 1), (key1152, -2), (key1116, 1), (key1003, 1), (key1213, -1), (key1077, -1), (key1152, 1), (key1073, 1), (key1200, 1), (key1020, 1), (key1125, -1), (key1017, -1), (key1213, -1), (key1077, -1), (key1200, 1), (key1020, 1), (key1152, 1), (key1073, 1), (key1125, -1), (key1017, -1)]

theorem rawRowCheck5465 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form2 = rawRow5465 := by decide +kernel

def row5465 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5465 : row5465 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5465 := by decide +kernel

theorem rowEval5465 (x : Key → ℝ) : Integer.Sparse.eval row5465 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5465, Integer.Sparse.eval_collectBalanced, rawRowCheck5465]

def rawRow5466 : Integer.Sparse Key := [(key1073, -1), (key1077, -1), (key1077, 2), (key1152, -1), (key1156, -1), (key1152, 2), (key1172, 2), (key1156, -1), (key1172, -1), (key1213, 2), (key1213, -1), (key1223, -1), (key1017, 1), (key1020, 1), (key1020, -2), (key1125, 1), (key1128, 1), (key1125, -2), (key1172, -2), (key1128, 1), (key1172, 1), (key1200, -2), (key1200, 1), (key1223, 1), (key1003, -1), (key1020, -1), (key1007, 1), (key1020, 1), (key1038, 1), (key1077, 1), (key1042, -1), (key1077, -1), (key1116, -1), (key1128, -1), (key1116, 1), (key1156, 1), (key1194, 1), (key1200, 1), (key1194, -1), (key1213, -1)]

theorem rawRowCheck5466 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form2 = rawRow5466 := by decide +kernel

def row5466 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5466 : row5466 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5466 := by decide +kernel

theorem rowEval5466 (x : Key → ℝ) : Integer.Sparse.eval row5466 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5466, Integer.Sparse.eval_collectBalanced, rawRowCheck5466]

def rawRow5467 : Integer.Sparse Key := [(key1077, -1), (key1073, -1), (key1077, 2), (key1156, -1), (key1152, -1), (key1172, 2), (key1152, 2), (key1172, -1), (key1156, -1), (key1213, 2), (key1223, -1), (key1213, -1), (key1020, 1), (key1017, 1), (key1020, -2), (key1128, 1), (key1125, 1), (key1172, -2), (key1125, -2), (key1172, 1), (key1128, 1), (key1200, -2), (key1223, 1), (key1200, 1), (key1020, -1), (key1003, -1), (key1020, 1), (key1007, 1), (key1077, 1), (key1038, 1), (key1077, -1), (key1042, -1), (key1128, -1), (key1116, -1), (key1156, 1), (key1116, 1), (key1200, 1), (key1194, 1), (key1213, -1), (key1194, -1)]

theorem rawRowCheck5467 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form2 = rawRow5467 := by decide +kernel

def row5467 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5467 : row5467 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5467 := by decide +kernel

theorem rowEval5467 (x : Key → ℝ) : Integer.Sparse.eval row5467 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5467, Integer.Sparse.eval_collectBalanced, rawRowCheck5467]

def rawRow5468 : Integer.Sparse Key := [(key1077, -1), (key1077, -1), (key1073, 2), (key1172, -1), (key1172, -1), (key1156, 2), (key1156, 2), (key1152, -1), (key1152, -1), (key1223, 2), (key1213, -1), (key1213, -1), (key1020, 1), (key1020, 1), (key1017, -2), (key1172, 1), (key1172, 1), (key1128, -2), (key1128, -2), (key1125, 1), (key1125, 1), (key1223, -2), (key1200, 1), (key1200, 1), (key1007, -1), (key1007, -1), (key1003, 1), (key1003, 1), (key1042, 1), (key1042, 1), (key1038, -1), (key1038, -1), (key1156, -1), (key1156, -1), (key1128, 1), (key1128, 1), (key1213, 1), (key1213, 1), (key1200, -1), (key1200, -1)]

theorem rawRowCheck5468 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form2 = rawRow5468 := by decide +kernel

def row5468 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5468 : row5468 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5468 := by decide +kernel

theorem rowEval5468 (x : Key → ℝ) : Integer.Sparse.eval row5468 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5468, Integer.Sparse.eval_collectBalanced, rawRowCheck5468]

def rawRow5469 : Integer.Sparse Key := [(key1152, -1), (key1156, -1), (key1213, 2), (key1073, -1), (key1077, -1), (key1152, 2), (key1172, 2), (key1213, -1), (key1223, -1), (key1077, 2), (key1156, -1), (key1172, -1), (key1125, 1), (key1128, 1), (key1200, -2), (key1017, 1), (key1020, 1), (key1125, -2), (key1172, -2), (key1200, 1), (key1223, 1), (key1020, -2), (key1128, 1), (key1172, 1), (key1116, -1), (key1128, -1), (key1194, 1), (key1200, 1), (key1116, 1), (key1156, 1), (key1194, -1), (key1213, -1), (key1003, -1), (key1020, -1), (key1038, 1), (key1077, 1), (key1007, 1), (key1020, 1), (key1042, -1), (key1077, -1)]

theorem rawRowCheck5469 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form2 = rawRow5469 := by decide +kernel

def row5469 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5469 : row5469 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5469 := by decide +kernel

theorem rowEval5469 (x : Key → ℝ) : Integer.Sparse.eval row5469 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5469, Integer.Sparse.eval_collectBalanced, rawRowCheck5469]

def rawRow5470 : Integer.Sparse Key := [(key1156, -1), (key1152, -1), (key1213, 2), (key1077, -1), (key1073, -1), (key1172, 2), (key1152, 2), (key1223, -1), (key1213, -1), (key1077, 2), (key1172, -1), (key1156, -1), (key1128, 1), (key1125, 1), (key1200, -2), (key1020, 1), (key1017, 1), (key1172, -2), (key1125, -2), (key1223, 1), (key1200, 1), (key1020, -2), (key1172, 1), (key1128, 1), (key1128, -1), (key1116, -1), (key1200, 1), (key1194, 1), (key1156, 1), (key1116, 1), (key1213, -1), (key1194, -1), (key1020, -1), (key1003, -1), (key1077, 1), (key1038, 1), (key1020, 1), (key1007, 1), (key1077, -1), (key1042, -1)]

theorem rawRowCheck5470 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form2 = rawRow5470 := by decide +kernel

def row5470 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5470 : row5470 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5470 := by decide +kernel

theorem rowEval5470 (x : Key → ℝ) : Integer.Sparse.eval row5470 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5470, Integer.Sparse.eval_collectBalanced, rawRowCheck5470]

def rawRow5471 : Integer.Sparse Key := [(key1152, -1), (key1213, -1), (key1156, 2), (key1152, -1), (key1213, -1), (key1073, 2), (key1223, 2), (key1077, -1), (key1172, -1), (key1156, 2), (key1077, -1), (key1172, -1), (key1125, 1), (key1200, 1), (key1128, -2), (key1125, 1), (key1200, 1), (key1017, -2), (key1223, -2), (key1020, 1), (key1172, 1), (key1128, -2), (key1020, 1), (key1172, 1), (key1038, -1), (key1200, -1), (key1042, 1), (key1128, 1), (key1003, 1), (key1213, 1), (key1007, -1), (key1156, -1), (key1038, -1), (key1200, -1), (key1003, 1), (key1213, 1), (key1042, 1), (key1128, 1), (key1007, -1), (key1156, -1)]

theorem rawRowCheck5471 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form2 = rawRow5471 := by decide +kernel

def row5471 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5471 : row5471 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5471 := by decide +kernel

theorem rowEval5471 (x : Key → ℝ) : Integer.Sparse.eval row5471 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck5471, Integer.Sparse.eval_collectBalanced, rawRowCheck5471]

def rawRow5472 : Integer.Sparse Key := [(key1213, -1), (key1152, -1), (key1156, 2), (key1213, -1), (key1152, -1), (key1223, 2), (key1073, 2), (key1172, -1), (key1077, -1), (key1156, 2), (key1172, -1), (key1077, -1), (key1200, 1), (key1125, 1), (key1128, -2), (key1200, 1), (key1125, 1), (key1223, -2), (key1017, -2), (key1172, 1), (key1020, 1), (key1128, -2), (key1172, 1), (key1020, 1), (key1200, -1), (key1038, -1), (key1128, 1), (key1042, 1), (key1213, 1), (key1003, 1), (key1156, -1), (key1007, -1), (key1200, -1), (key1038, -1), (key1213, 1), (key1003, 1), (key1128, 1), (key1042, 1), (key1156, -1), (key1007, -1)]

theorem rawRowCheck5472 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form2 = rawRow5472 := by decide +kernel

def row5472 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5472 : row5472 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5472 := by decide +kernel

theorem rowEval5472 (x : Key → ℝ) : Integer.Sparse.eval row5472 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5472, Integer.Sparse.eval_collectBalanced, rawRowCheck5472]

def rawRow5473 : Integer.Sparse Key := [(key1156, -1), (key1213, -1), (key1152, 2), (key1172, -1), (key1223, -1), (key1077, 2), (key1213, 2), (key1073, -1), (key1152, -1), (key1172, 2), (key1077, -1), (key1156, -1), (key1128, 1), (key1200, 1), (key1125, -2), (key1172, 1), (key1223, 1), (key1020, -2), (key1200, -2), (key1017, 1), (key1125, 1), (key1172, -2), (key1020, 1), (key1128, 1), (key1042, -1), (key1194, -1), (key1038, 1), (key1116, 1), (key1007, 1), (key1194, 1), (key1003, -1), (key1116, -1), (key1077, -1), (key1213, -1), (key1020, 1), (key1200, 1), (key1077, 1), (key1156, 1), (key1020, -1), (key1128, -1)]

theorem rawRowCheck5473 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form2 = rawRow5473 := by decide +kernel

def row5473 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5473 : row5473 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5473 := by decide +kernel

theorem rowEval5473 (x : Key → ℝ) : Integer.Sparse.eval row5473 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5473, Integer.Sparse.eval_collectBalanced, rawRowCheck5473]

def rawRow5474 : Integer.Sparse Key := [(key1213, -1), (key1156, -1), (key1152, 2), (key1223, -1), (key1172, -1), (key1213, 2), (key1077, 2), (key1152, -1), (key1073, -1), (key1172, 2), (key1156, -1), (key1077, -1), (key1200, 1), (key1128, 1), (key1125, -2), (key1223, 1), (key1172, 1), (key1200, -2), (key1020, -2), (key1125, 1), (key1017, 1), (key1172, -2), (key1128, 1), (key1020, 1), (key1194, -1), (key1042, -1), (key1116, 1), (key1038, 1), (key1194, 1), (key1007, 1), (key1116, -1), (key1003, -1), (key1213, -1), (key1077, -1), (key1200, 1), (key1020, 1), (key1156, 1), (key1077, 1), (key1128, -1), (key1020, -1)]

theorem rawRowCheck5474 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form2 = rawRow5474 := by decide +kernel

def row5474 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5474 : row5474 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5474 := by decide +kernel

theorem rowEval5474 (x : Key → ℝ) : Integer.Sparse.eval row5474 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, 0, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5474, Integer.Sparse.eval_collectBalanced, rawRowCheck5474]

def rawRow5475 : Integer.Sparse Key := [(key1172, -1), (key1172, -1), (key1223, 2), (key1077, -1), (key1077, -1), (key1156, 2), (key1156, 2), (key1213, -1), (key1213, -1), (key1073, 2), (key1152, -1), (key1152, -1), (key1172, 1), (key1172, 1), (key1223, -2), (key1020, 1), (key1020, 1), (key1128, -2), (key1128, -2), (key1200, 1), (key1200, 1), (key1017, -2), (key1125, 1), (key1125, 1), (key1156, -1), (key1156, -1), (key1213, 1), (key1213, 1), (key1128, 1), (key1128, 1), (key1200, -1), (key1200, -1), (key1007, -1), (key1007, -1), (key1042, 1), (key1042, 1), (key1003, 1), (key1003, 1), (key1038, -1), (key1038, -1)]

theorem rawRowCheck5475 : GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form2 = rawRow5475 := by decide +kernel

def row5475 : Integer.Sparse Key := [(key1003, 2), (key1007, -2), (key1017, -2), (key1020, 2), (key1038, -2), (key1042, 2), (key1073, 2), (key1077, -2), (key1125, 2), (key1128, -2), (key1152, -2), (key1156, 2)]

theorem rowCheck5475 : row5475 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5475 := by decide +kernel

theorem rowEval5475 (x : Key → ℝ) : Integer.Sparse.eval row5475 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, -3, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5475, Integer.Sparse.eval_collectBalanced, rawRowCheck5475]

def rawRow5476 : Integer.Sparse Key := [(key1172, -1), (key1223, -1), (key1172, 2), (key1156, -1), (key1213, -1), (key1077, 2), (key1213, 2), (key1077, -1), (key1156, -1), (key1152, 2), (key1073, -1), (key1152, -1), (key1172, 1), (key1223, 1), (key1172, -2), (key1128, 1), (key1200, 1), (key1020, -2), (key1200, -2), (key1020, 1), (key1128, 1), (key1125, -2), (key1017, 1), (key1125, 1), (key1077, -1), (key1213, -1), (key1077, 1), (key1156, 1), (key1020, 1), (key1200, 1), (key1020, -1), (key1128, -1), (key1042, -1), (key1194, -1), (key1007, 1), (key1194, 1), (key1038, 1), (key1116, 1), (key1003, -1), (key1116, -1)]

theorem rawRowCheck5476 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form2 = rawRow5476 := by decide +kernel

def row5476 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5476 : row5476 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5476 := by decide +kernel

theorem rowEval5476 (x : Key → ℝ) : Integer.Sparse.eval row5476 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, -3, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck5476, Integer.Sparse.eval_collectBalanced, rawRowCheck5476]

def rawRow5477 : Integer.Sparse Key := [(key1223, -1), (key1172, -1), (key1172, 2), (key1213, -1), (key1156, -1), (key1213, 2), (key1077, 2), (key1156, -1), (key1077, -1), (key1152, 2), (key1152, -1), (key1073, -1), (key1223, 1), (key1172, 1), (key1172, -2), (key1200, 1), (key1128, 1), (key1200, -2), (key1020, -2), (key1128, 1), (key1020, 1), (key1125, -2), (key1125, 1), (key1017, 1), (key1213, -1), (key1077, -1), (key1156, 1), (key1077, 1), (key1200, 1), (key1020, 1), (key1128, -1), (key1020, -1), (key1194, -1), (key1042, -1), (key1194, 1), (key1007, 1), (key1116, 1), (key1038, 1), (key1116, -1), (key1003, -1)]

theorem rawRowCheck5477 : GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form2 = rawRow5477 := by decide +kernel

def row5477 : Integer.Sparse Key := [(key1003, -1), (key1007, 1), (key1017, 1), (key1020, -1), (key1038, 1), (key1042, -1), (key1073, -1), (key1077, 1), (key1125, -1), (key1128, 1), (key1152, 1), (key1156, -1)]

theorem rowCheck5477 : row5477 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5477 := by decide +kernel

theorem rowEval5477 (x : Key → ℝ) : Integer.Sparse.eval row5477 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 1, 0, 0, -3] GramFunctions.Block2.form2) x := by
  rw [rowCheck5477, Integer.Sparse.eval_collectBalanced, rawRowCheck5477]

def rawRow5478 : Integer.Sparse Key := [(key10, -4), (key13, 2), (key13, 2), (key13, 2), (key13, 2), (key15, -4), (key93, 2), (key96, -1), (key96, -1), (key93, 2), (key158, -1), (key158, -1), (key96, -1), (key96, -1), (key158, -1), (key158, -1), (key163, 2), (key163, 2), (key169, -1), (key169, -1), (key170, 2), (key169, -1), (key169, -1), (key189, 2), (key189, 2), (key192, -1), (key192, -1), (key170, 2), (key192, -1), (key192, -1)]

theorem rawRowCheck5478 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5478 := by decide +kernel

def row5478 : Integer.Sparse Key := [(key10, -4), (key13, 8), (key15, -4), (key93, 4), (key96, -4), (key158, -4), (key163, 4), (key169, -4), (key170, 4), (key189, 4), (key192, -4)]

theorem rowCheck5478 : row5478 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5478 := by decide +kernel

theorem rowEval5478 (x : Key → ℝ) : Integer.Sparse.eval row5478 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5478, Integer.Sparse.eval_collectBalanced, rawRowCheck5478]

def rawRow5479 : Integer.Sparse Key := [(key13, -4), (key10, 2), (key13, 2), (key13, 2), (key15, 2), (key13, -4), (key96, 2), (key93, -1), (key96, -1), (key158, 2), (key93, -1), (key158, -1), (key158, -1), (key163, -1), (key96, -1), (key163, -1), (key96, 2), (key158, 2), (key169, -1), (key170, -1), (key169, 2), (key189, -1), (key192, -1), (key169, 2), (key192, 2), (key169, -1), (key189, -1), (key192, 2), (key170, -1), (key192, -1)]

theorem rawRowCheck5479 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5479 := by decide +kernel

def row5479 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5479 : row5479 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5479 := by decide +kernel

theorem rowEval5479 (x : Key → ℝ) : Integer.Sparse.eval row5479 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5479, Integer.Sparse.eval_collectBalanced, rawRowCheck5479]

def rawRow5480 : Integer.Sparse Key := [(key13, -4), (key13, 2), (key10, 2), (key15, 2), (key13, 2), (key13, -4), (key96, 2), (key96, -1), (key93, -1), (key158, 2), (key158, -1), (key93, -1), (key163, -1), (key158, -1), (key163, -1), (key96, -1), (key158, 2), (key96, 2), (key170, -1), (key169, -1), (key169, 2), (key192, -1), (key189, -1), (key192, 2), (key169, 2), (key189, -1), (key169, -1), (key192, 2), (key192, -1), (key170, -1)]

theorem rawRowCheck5480 : GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5480 := by decide +kernel

def row5480 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5480 : row5480 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5480 := by decide +kernel

theorem rowEval5480 (x : Key → ℝ) : Integer.Sparse.eval row5480 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5480, Integer.Sparse.eval_collectBalanced, rawRowCheck5480]

def rawRow5481 : Integer.Sparse Key := [(key13, -4), (key13, 2), (key15, 2), (key10, 2), (key13, 2), (key13, -4), (key158, 2), (key158, -1), (key163, -1), (key96, 2), (key96, -1), (key163, -1), (key93, -1), (key96, -1), (key93, -1), (key158, -1), (key96, 2), (key158, 2), (key189, -1), (key192, -1), (key192, 2), (key169, -1), (key170, -1), (key169, 2), (key192, 2), (key170, -1), (key192, -1), (key169, 2), (key169, -1), (key189, -1)]

theorem rawRowCheck5481 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5481 := by decide +kernel

def row5481 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5481 : row5481 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5481 := by decide +kernel

theorem rowEval5481 (x : Key → ℝ) : Integer.Sparse.eval row5481 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5481, Integer.Sparse.eval_collectBalanced, rawRowCheck5481]

def rawRow5482 : Integer.Sparse Key := [(key13, -4), (key15, 2), (key13, 2), (key13, 2), (key10, 2), (key13, -4), (key158, 2), (key163, -1), (key158, -1), (key96, 2), (key163, -1), (key96, -1), (key96, -1), (key93, -1), (key158, -1), (key93, -1), (key158, 2), (key96, 2), (key192, -1), (key189, -1), (key192, 2), (key170, -1), (key169, -1), (key192, 2), (key169, 2), (key192, -1), (key170, -1), (key169, 2), (key189, -1), (key169, -1)]

theorem rawRowCheck5482 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5482 := by decide +kernel

def row5482 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5482 : row5482 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5482 := by decide +kernel

theorem rowEval5482 (x : Key → ℝ) : Integer.Sparse.eval row5482 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5482, Integer.Sparse.eval_collectBalanced, rawRowCheck5482]

def rawRow5483 : Integer.Sparse Key := [(key15, -4), (key13, 2), (key13, 2), (key13, 2), (key13, 2), (key10, -4), (key163, 2), (key158, -1), (key158, -1), (key163, 2), (key96, -1), (key96, -1), (key158, -1), (key158, -1), (key96, -1), (key96, -1), (key93, 2), (key93, 2), (key192, -1), (key192, -1), (key189, 2), (key192, -1), (key192, -1), (key170, 2), (key170, 2), (key169, -1), (key169, -1), (key189, 2), (key169, -1), (key169, -1)]

theorem rawRowCheck5483 : GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5483 := by decide +kernel

def row5483 : Integer.Sparse Key := [(key10, -4), (key13, 8), (key15, -4), (key93, 4), (key96, -4), (key158, -4), (key163, 4), (key169, -4), (key170, 4), (key189, 4), (key192, -4)]

theorem rowCheck5483 : row5483 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5483 := by decide +kernel

theorem rowEval5483 (x : Key → ℝ) : Integer.Sparse.eval row5483 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -3, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5483, Integer.Sparse.eval_collectBalanced, rawRowCheck5483]

def rawRow5484 : Integer.Sparse Key := [(key93, -4), (key96, 2), (key96, 2), (key158, 2), (key158, 2), (key163, -4), (key10, 2), (key13, -1), (key13, -1), (key93, 2), (key158, -1), (key158, -1), (key169, -1), (key169, -1), (key189, -1), (key189, -1), (key192, 2), (key192, 2), (key13, -1), (key13, -1), (key15, 2), (key96, -1), (key96, -1), (key158, 2), (key158, 2), (key163, -1), (key163, -1), (key170, 2), (key192, -1), (key192, -1)]

theorem rawRowCheck5484 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3 = rawRow5484 := by decide +kernel

def row5484 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

theorem rowCheck5484 : row5484 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5484 := by decide +kernel

theorem rowEval5484 (x : Key → ℝ) : Integer.Sparse.eval row5484 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5484, Integer.Sparse.eval_collectBalanced, rawRowCheck5484]

def rawRow5485 : Integer.Sparse Key := [(key96, -4), (key93, 2), (key96, 2), (key158, 2), (key163, 2), (key158, -4), (key13, 2), (key10, -1), (key13, -1), (key158, 2), (key93, -1), (key158, -1), (key189, -1), (key192, -1), (key169, -1), (key192, -1), (key169, 2), (key189, 2), (key13, -1), (key15, -1), (key13, 2), (key158, -1), (key163, -1), (key96, 2), (key163, 2), (key96, -1), (key158, -1), (key192, 2), (key170, -1), (key192, -1)]

theorem rawRowCheck5485 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3 = rawRow5485 := by decide +kernel

def row5485 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -3), (key163, 3), (key169, 1), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5485 : row5485 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5485 := by decide +kernel

theorem rowEval5485 (x : Key → ℝ) : Integer.Sparse.eval row5485 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5485, Integer.Sparse.eval_collectBalanced, rawRowCheck5485]

def rawRow5486 : Integer.Sparse Key := [(key96, -4), (key96, 2), (key93, 2), (key163, 2), (key158, 2), (key158, -4), (key13, 2), (key13, -1), (key10, -1), (key158, 2), (key158, -1), (key93, -1), (key192, -1), (key189, -1), (key192, -1), (key169, -1), (key189, 2), (key169, 2), (key15, -1), (key13, -1), (key13, 2), (key163, -1), (key158, -1), (key163, 2), (key96, 2), (key158, -1), (key96, -1), (key192, 2), (key192, -1), (key170, -1)]

theorem rawRowCheck5486 : GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3 = rawRow5486 := by decide +kernel

def row5486 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -3), (key163, 3), (key169, 1), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5486 : row5486 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5486 := by decide +kernel

theorem rowEval5486 (x : Key → ℝ) : Integer.Sparse.eval row5486 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -3, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5486, Integer.Sparse.eval_collectBalanced, rawRowCheck5486]

def rawRow5487 : Integer.Sparse Key := [(key93, -4), (key158, 2), (key158, 2), (key96, 2), (key96, 2), (key163, -4), (key93, 2), (key158, -1), (key158, -1), (key10, 2), (key189, -1), (key189, -1), (key13, -1), (key13, -1), (key158, -1), (key158, -1), (key192, 2), (key192, 2), (key96, -1), (key96, -1), (key170, 2), (key13, -1), (key13, -1), (key158, 2), (key158, 2), (key192, -1), (key192, -1), (key15, 2), (key163, -1), (key163, -1)]

theorem rawRowCheck5487 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3 = rawRow5487 := by decide +kernel

def row5487 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 4), (key163, -6), (key170, 2), (key189, -2), (key192, 2)]

theorem rowCheck5487 : row5487 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5487 := by decide +kernel

theorem rowEval5487 (x : Key → ℝ) : Integer.Sparse.eval row5487 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -3, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5487, Integer.Sparse.eval_collectBalanced, rawRowCheck5487]

def rawRow5488 : Integer.Sparse Key := [(key158, -4), (key93, 2), (key158, 2), (key96, 2), (key163, 2), (key96, -4), (key158, 2), (key93, -1), (key158, -1), (key189, 2), (key10, -1), (key189, -1), (key158, -1), (key192, -1), (key13, -1), (key192, -1), (key13, 2), (key158, 2), (key96, -1), (key170, -1), (key96, 2), (key158, -1), (key192, -1), (key13, 2), (key192, 2), (key13, -1), (key158, -1), (key163, 2), (key15, -1), (key163, -1)]

theorem rawRowCheck5488 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3 = rawRow5488 := by decide +kernel

def row5488 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -2), (key163, 3), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5488 : row5488 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5488 := by decide +kernel

theorem rowEval5488 (x : Key → ℝ) : Integer.Sparse.eval row5488 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5488, Integer.Sparse.eval_collectBalanced, rawRowCheck5488]

def rawRow5489 : Integer.Sparse Key := [(key158, -4), (key158, 2), (key93, 2), (key163, 2), (key96, 2), (key96, -4), (key158, 2), (key158, -1), (key93, -1), (key189, 2), (key189, -1), (key10, -1), (key192, -1), (key158, -1), (key192, -1), (key13, -1), (key158, 2), (key13, 2), (key170, -1), (key96, -1), (key96, 2), (key192, -1), (key158, -1), (key192, 2), (key13, 2), (key158, -1), (key13, -1), (key163, 2), (key163, -1), (key15, -1)]

theorem rawRowCheck5489 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3 = rawRow5489 := by decide +kernel

def row5489 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -2), (key163, 3), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5489 : row5489 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5489 := by decide +kernel

theorem rowEval5489 (x : Key → ℝ) : Integer.Sparse.eval row5489 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 1, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5489, Integer.Sparse.eval_collectBalanced, rawRowCheck5489]

def rawRow5490 : Integer.Sparse Key := [(key96, -4), (key158, 2), (key163, 2), (key93, 2), (key96, 2), (key158, -4), (key169, 2), (key189, -1), (key192, -1), (key13, 2), (key158, -1), (key192, -1), (key10, -1), (key13, -1), (key93, -1), (key158, -1), (key169, 2), (key189, 2), (key158, -1), (key163, -1), (key192, 2), (key13, -1), (key15, -1), (key96, 2), (key163, 2), (key170, -1), (key192, -1), (key13, 2), (key96, -1), (key158, -1)]

theorem rawRowCheck5490 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5490 := by decide +kernel

def row5490 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -6), (key163, 3), (key169, 4), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5490 : row5490 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5490 := by decide +kernel

theorem rowEval5490 (x : Key → ℝ) : Integer.Sparse.eval row5490 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5490, Integer.Sparse.eval_collectBalanced, rawRowCheck5490]

def rawRow5491 : Integer.Sparse Key := [(key96, -4), (key163, 2), (key158, 2), (key96, 2), (key93, 2), (key158, -4), (key169, 2), (key192, -1), (key189, -1), (key13, 2), (key192, -1), (key158, -1), (key13, -1), (key10, -1), (key158, -1), (key93, -1), (key189, 2), (key169, 2), (key163, -1), (key158, -1), (key192, 2), (key15, -1), (key13, -1), (key163, 2), (key96, 2), (key192, -1), (key170, -1), (key13, 2), (key158, -1), (key96, -1)]

theorem rawRowCheck5491 : GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5491 := by decide +kernel

def row5491 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -6), (key163, 3), (key169, 4), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5491 : row5491 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5491 := by decide +kernel

theorem rowEval5491 (x : Key → ℝ) : Integer.Sparse.eval row5491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5491, Integer.Sparse.eval_collectBalanced, rawRowCheck5491]

def rawRow5492 : Integer.Sparse Key := [(key158, -4), (key96, 2), (key163, 2), (key93, 2), (key158, 2), (key96, -4), (key189, 2), (key169, -1), (key192, -1), (key158, 2), (key13, -1), (key192, -1), (key93, -1), (key158, -1), (key10, -1), (key189, -1), (key13, 2), (key158, 2), (key158, -1), (key192, -1), (key163, 2), (key96, -1), (key170, -1), (key13, 2), (key192, 2), (key15, -1), (key163, -1), (key96, 2), (key13, -1), (key158, -1)]

theorem rawRowCheck5492 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5492 := by decide +kernel

def row5492 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 3), (key169, -1), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5492 : row5492 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5492 := by decide +kernel

theorem rowEval5492 (x : Key → ℝ) : Integer.Sparse.eval row5492 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5492, Integer.Sparse.eval_collectBalanced, rawRowCheck5492]

def rawRow5493 : Integer.Sparse Key := [(key158, -4), (key163, 2), (key96, 2), (key158, 2), (key93, 2), (key96, -4), (key189, 2), (key192, -1), (key169, -1), (key158, 2), (key192, -1), (key13, -1), (key158, -1), (key93, -1), (key189, -1), (key10, -1), (key158, 2), (key13, 2), (key192, -1), (key158, -1), (key163, 2), (key170, -1), (key96, -1), (key192, 2), (key13, 2), (key163, -1), (key15, -1), (key96, 2), (key158, -1), (key13, -1)]

theorem rawRowCheck5493 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5493 := by decide +kernel

def row5493 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 3), (key169, -1), (key170, -1), (key189, 1), (key192, -1)]

theorem rowCheck5493 : row5493 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5493 := by decide +kernel

theorem rowEval5493 (x : Key → ℝ) : Integer.Sparse.eval row5493 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5493, Integer.Sparse.eval_collectBalanced, rawRowCheck5493]

def rawRow5494 : Integer.Sparse Key := [(key163, -4), (key96, 2), (key158, 2), (key96, 2), (key158, 2), (key93, -4), (key192, 2), (key169, -1), (key189, -1), (key192, 2), (key13, -1), (key158, -1), (key169, -1), (key189, -1), (key13, -1), (key158, -1), (key10, 2), (key93, 2), (key163, -1), (key192, -1), (key158, 2), (key163, -1), (key192, -1), (key15, 2), (key170, 2), (key13, -1), (key96, -1), (key158, 2), (key13, -1), (key96, -1)]

theorem rawRowCheck5494 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5494 := by decide +kernel

def row5494 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

theorem rowCheck5494 : row5494 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5494 := by decide +kernel

theorem rowEval5494 (x : Key → ℝ) : Integer.Sparse.eval row5494 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5494, Integer.Sparse.eval_collectBalanced, rawRowCheck5494]

def rawRow5495 : Integer.Sparse Key := [(key163, -4), (key158, 2), (key96, 2), (key158, 2), (key96, 2), (key93, -4), (key192, 2), (key189, -1), (key169, -1), (key192, 2), (key158, -1), (key13, -1), (key189, -1), (key169, -1), (key158, -1), (key13, -1), (key93, 2), (key10, 2), (key192, -1), (key163, -1), (key158, 2), (key192, -1), (key163, -1), (key170, 2), (key15, 2), (key96, -1), (key13, -1), (key158, 2), (key96, -1), (key13, -1)]

theorem rawRowCheck5495 : GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3 = rawRow5495 := by decide +kernel

def row5495 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 6), (key163, -6), (key169, -2), (key170, 2), (key189, -2), (key192, 2)]

theorem rowCheck5495 : row5495 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5495 := by decide +kernel

theorem rowEval5495 (x : Key → ℝ) : Integer.Sparse.eval row5495 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 1, 1, 0, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5495, Integer.Sparse.eval_collectBalanced, rawRowCheck5495]

def rawRow5496 : Integer.Sparse Key := [(key169, -4), (key169, 2), (key170, 2), (key189, 2), (key192, 2), (key192, -4), (key13, 2), (key13, -1), (key15, -1), (key96, 2), (key96, -1), (key170, -1), (key158, -1), (key163, -1), (key158, -1), (key192, -1), (key163, 2), (key192, 2), (key10, -1), (key13, -1), (key13, 2), (key93, -1), (key96, -1), (key93, 2), (key158, 2), (key96, -1), (key158, -1), (key169, 2), (key169, -1), (key189, -1)]

theorem rawRowCheck5496 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3 = rawRow5496 := by decide +kernel

def row5496 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5496 : row5496 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5496 := by decide +kernel

theorem rowEval5496 (x : Key → ℝ) : Integer.Sparse.eval row5496 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5496, Integer.Sparse.eval_collectBalanced, rawRowCheck5496]

def rawRow5497 : Integer.Sparse Key := [(key169, -4), (key170, 2), (key169, 2), (key192, 2), (key189, 2), (key192, -4), (key13, 2), (key15, -1), (key13, -1), (key96, 2), (key170, -1), (key96, -1), (key163, -1), (key158, -1), (key192, -1), (key158, -1), (key192, 2), (key163, 2), (key13, -1), (key10, -1), (key13, 2), (key96, -1), (key93, -1), (key158, 2), (key93, 2), (key158, -1), (key96, -1), (key169, 2), (key189, -1), (key169, -1)]

theorem rawRowCheck5497 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3 = rawRow5497 := by decide +kernel

def row5497 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, -1), (key163, 1), (key169, -1), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5497 : row5497 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5497 := by decide +kernel

theorem rowEval5497 (x : Key → ℝ) : Integer.Sparse.eval row5497 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5497, Integer.Sparse.eval_collectBalanced, rawRowCheck5497]

def rawRow5498 : Integer.Sparse Key := [(key170, -4), (key169, 2), (key169, 2), (key192, 2), (key192, 2), (key189, -4), (key15, 2), (key13, -1), (key13, -1), (key170, 2), (key96, -1), (key96, -1), (key192, -1), (key192, -1), (key163, -1), (key163, -1), (key158, 2), (key158, 2), (key13, -1), (key13, -1), (key10, 2), (key158, -1), (key158, -1), (key96, 2), (key96, 2), (key93, -1), (key93, -1), (key189, 2), (key169, -1), (key169, -1)]

theorem rawRowCheck5498 : GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3 = rawRow5498 := by decide +kernel

def row5498 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key158, 2), (key163, -2), (key169, 2), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5498 : row5498 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5498 := by decide +kernel

theorem rowEval5498 (x : Key → ℝ) : Integer.Sparse.eval row5498 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -3, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5498, Integer.Sparse.eval_collectBalanced, rawRowCheck5498]

def rawRow5499 : Integer.Sparse Key := [(key169, -4), (key189, 2), (key192, 2), (key169, 2), (key170, 2), (key192, -4), (key96, 2), (key158, -1), (key163, -1), (key13, 2), (key158, -1), (key192, -1), (key13, -1), (key15, -1), (key96, -1), (key170, -1), (key163, 2), (key192, 2), (key93, -1), (key96, -1), (key158, 2), (key10, -1), (key13, -1), (key93, 2), (key158, 2), (key169, -1), (key189, -1), (key13, 2), (key96, -1), (key158, -1)]

theorem rawRowCheck5499 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3 = rawRow5499 := by decide +kernel

def row5499 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5499 : row5499 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5499 := by decide +kernel

theorem rowEval5499 (x : Key → ℝ) : Integer.Sparse.eval row5499 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5499, Integer.Sparse.eval_collectBalanced, rawRowCheck5499]

def rawRow5500 : Integer.Sparse Key := [(key169, -4), (key192, 2), (key189, 2), (key170, 2), (key169, 2), (key192, -4), (key96, 2), (key163, -1), (key158, -1), (key13, 2), (key192, -1), (key158, -1), (key15, -1), (key13, -1), (key170, -1), (key96, -1), (key192, 2), (key163, 2), (key96, -1), (key93, -1), (key158, 2), (key13, -1), (key10, -1), (key158, 2), (key93, 2), (key189, -1), (key169, -1), (key13, 2), (key158, -1), (key96, -1)]

theorem rawRowCheck5500 : GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3 = rawRow5500 := by decide +kernel

def row5500 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5500 : row5500 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5500 := by decide +kernel

theorem rowEval5500 (x : Key → ℝ) : Integer.Sparse.eval row5500 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, -3, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5500, Integer.Sparse.eval_collectBalanced, rawRowCheck5500]

def rawRow5501 : Integer.Sparse Key := [(key189, -4), (key169, 2), (key192, 2), (key169, 2), (key192, 2), (key170, -4), (key158, 2), (key96, -1), (key163, -1), (key158, 2), (key13, -1), (key192, -1), (key96, -1), (key163, -1), (key13, -1), (key192, -1), (key15, 2), (key170, 2), (key93, -1), (key158, -1), (key96, 2), (key93, -1), (key158, -1), (key10, 2), (key189, 2), (key13, -1), (key158, -1), (key96, 2), (key13, -1), (key158, -1)]

theorem rawRowCheck5501 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3 = rawRow5501 := by decide +kernel

def row5501 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key163, -2), (key169, 4), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5501 : row5501 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5501 := by decide +kernel

theorem rowEval5501 (x : Key → ℝ) : Integer.Sparse.eval row5501 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, -3, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck5501, Integer.Sparse.eval_collectBalanced, rawRowCheck5501]

def rawRow5502 : Integer.Sparse Key := [(key189, -4), (key192, 2), (key169, 2), (key192, 2), (key169, 2), (key170, -4), (key158, 2), (key163, -1), (key96, -1), (key158, 2), (key192, -1), (key13, -1), (key163, -1), (key96, -1), (key192, -1), (key13, -1), (key170, 2), (key15, 2), (key158, -1), (key93, -1), (key96, 2), (key158, -1), (key93, -1), (key189, 2), (key10, 2), (key158, -1), (key13, -1), (key96, 2), (key158, -1), (key13, -1)]

theorem rawRowCheck5502 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3 = rawRow5502 := by decide +kernel

def row5502 : Integer.Sparse Key := [(key10, 2), (key13, -4), (key15, 2), (key93, -2), (key96, 2), (key163, -2), (key169, 4), (key170, -2), (key189, -2), (key192, 2)]

theorem rowCheck5502 : row5502 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5502 := by decide +kernel

theorem rowEval5502 (x : Key → ℝ) : Integer.Sparse.eval row5502 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 0, 1, -3] GramFunctions.Block2.form3) x := by
  rw [rowCheck5502, Integer.Sparse.eval_collectBalanced, rawRowCheck5502]

def rawRow5503 : Integer.Sparse Key := [(key192, -4), (key169, 2), (key189, 2), (key170, 2), (key192, 2), (key169, -4), (key163, 2), (key96, -1), (key158, -1), (key192, 2), (key13, -1), (key158, -1), (key170, -1), (key192, -1), (key15, -1), (key163, -1), (key13, 2), (key96, 2), (key96, -1), (key158, -1), (key93, 2), (key169, -1), (key189, -1), (key13, 2), (key158, 2), (key10, -1), (key93, -1), (key158, 2), (key13, -1), (key96, -1)]

theorem rawRowCheck5503 : GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3 = rawRow5503 := by decide +kernel

def row5503 : Integer.Sparse Key := [(key10, -1), (key13, 2), (key15, -1), (key93, 1), (key96, -1), (key158, 1), (key163, 1), (key169, -3), (key170, 1), (key189, 1), (key192, -1)]

theorem rowCheck5503 : row5503 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow5503 := by decide +kernel

theorem rowEval5503 (x : Key → ℝ) : Integer.Sparse.eval row5503 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, 0, 1, -3, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck5503, Integer.Sparse.eval_collectBalanced, rawRowCheck5503]

end MUB6.Certificate.GramRows

end OAI
