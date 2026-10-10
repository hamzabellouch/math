import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow608 : Integer.Sparse Key := [(key2778, -1), (key2781, -1), (key2790, 2), (key2801, 1), (key2804, 1), (key2856, -1), (key2895, -1), (key2825, -2), (key2866, 1), (key2902, 1), (key2624, 1), (key2627, 1), (key2636, -2), (key2698, -1), (key2701, -1), (key2856, 1), (key2974, 1), (key2722, 2), (key2866, -1), (key2981, -1), (key2608, -1), (key2611, -1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2734, -1), (key2745, -1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2611, 2), (key2627, -1), (key2636, -1), (key2666, -2), (key2701, 1), (key2722, 1), (key2781, 1), (key2790, 1), (key2804, -1), (key2825, -1)]

theorem rawRowCheck608 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form4 = rawRow608 := by decide +kernel

def row608 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck608 : row608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow608 := by decide +kernel

theorem rowEval608 (x : Key → ℝ) : Integer.Sparse.eval row608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck608, Integer.Sparse.eval_collectBalanced, rawRowCheck608]

def rawRow609 : Integer.Sparse Key := [(key2781, -1), (key2778, -1), (key2790, 2), (key2804, 1), (key2801, 1), (key2895, -1), (key2856, -1), (key2825, -2), (key2902, 1), (key2866, 1), (key2627, 1), (key2624, 1), (key2636, -2), (key2701, -1), (key2698, -1), (key2974, 1), (key2856, 1), (key2722, 2), (key2981, -1), (key2866, -1), (key2611, -1), (key2608, -1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2745, -1), (key2734, -1), (key2941, -1), (key2935, -1), (key2958, 1), (key2947, 1), (key2611, 2), (key2636, -1), (key2627, -1), (key2666, -2), (key2722, 1), (key2701, 1), (key2790, 1), (key2781, 1), (key2825, -1), (key2804, -1)]

theorem rawRowCheck609 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form4 = rawRow609 := by decide +kernel

def row609 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck609 : row609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow609 := by decide +kernel

theorem rowEval609 (x : Key → ℝ) : Integer.Sparse.eval row609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck609, Integer.Sparse.eval_collectBalanced, rawRowCheck609]

def rawRow610 : Integer.Sparse Key := [(key2781, -1), (key2790, -1), (key2778, 2), (key2892, 1), (key2895, 1), (key2801, -1), (key2851, -1), (key2902, -2), (key2825, 1), (key2866, 1), (key2627, 1), (key2636, 1), (key2624, -2), (key2971, -1), (key2974, -1), (key2698, 1), (key2851, 1), (key2981, 2), (key2722, -1), (key2866, -1), (key2645, -1), (key2651, -1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2663, -1), (key2698, -1), (key2958, -1), (key2981, -1), (key2941, 1), (key2974, 1), (key2636, 2), (key2611, -1), (key2627, -1), (key2722, -2), (key2666, 1), (key2701, 1), (key2825, 1), (key2866, 1), (key2790, -1), (key2856, -1)]

theorem rawRowCheck610 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form4 = rawRow610 := by decide +kernel

def row610 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, 1), (key2722, -2), (key2745, 1), (key2778, 2), (key2781, -1), (key2790, -2), (key2801, -1), (key2825, 2), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2941, 1), (key2958, -1), (key2971, -1), (key2981, 1)]

theorem rowCheck610 : row610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow610 := by decide +kernel

theorem rowEval610 (x : Key → ℝ) : Integer.Sparse.eval row610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck610, Integer.Sparse.eval_collectBalanced, rawRowCheck610]

def rawRow611 : Integer.Sparse Key := [(key2790, -1), (key2781, -1), (key2778, 2), (key2895, 1), (key2892, 1), (key2851, -1), (key2801, -1), (key2902, -2), (key2866, 1), (key2825, 1), (key2636, 1), (key2627, 1), (key2624, -2), (key2974, -1), (key2971, -1), (key2851, 1), (key2698, 1), (key2981, 2), (key2866, -1), (key2722, -1), (key2651, -1), (key2645, -1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2698, -1), (key2663, -1), (key2981, -1), (key2958, -1), (key2974, 1), (key2941, 1), (key2636, 2), (key2627, -1), (key2611, -1), (key2722, -2), (key2701, 1), (key2666, 1), (key2866, 1), (key2825, 1), (key2856, -1), (key2790, -1)]

theorem rawRowCheck611 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form4 = rawRow611 := by decide +kernel

def row611 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2701, 1), (key2722, -2), (key2745, 1), (key2778, 2), (key2781, -1), (key2790, -2), (key2801, -1), (key2825, 2), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2941, 1), (key2958, -1), (key2971, -1), (key2981, 1)]

theorem rowCheck611 : row611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow611 := by decide +kernel

theorem rowEval611 (x : Key → ℝ) : Integer.Sparse.eval row611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck611, Integer.Sparse.eval_collectBalanced, rawRowCheck611]

def rawRow612 : Integer.Sparse Key := [(key2801, -1), (key2804, -1), (key2825, 2), (key2778, 1), (key2781, 1), (key2866, -1), (key2902, -1), (key2790, -2), (key2856, 1), (key2895, 1), (key2698, 1), (key2701, 1), (key2722, -2), (key2624, -1), (key2627, -1), (key2866, 1), (key2981, 1), (key2636, 2), (key2856, -1), (key2974, -1), (key2663, -1), (key2666, -1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2947, -1), (key2958, -1), (key2645, -1), (key2651, -1), (key2734, 1), (key2745, 1), (key2666, 2), (key2781, -1), (key2790, -1), (key2611, -2), (key2804, 1), (key2825, 1), (key2627, 1), (key2636, 1), (key2701, -1), (key2722, -1)]

theorem rawRowCheck612 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form4 = rawRow612 := by decide +kernel

def row612 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -2), (key2734, 1), (key2745, 2), (key2778, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck612 : row612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow612 := by decide +kernel

theorem rowEval612 (x : Key → ℝ) : Integer.Sparse.eval row612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form4) x := by
  rw [rowCheck612, Integer.Sparse.eval_collectBalanced, rawRowCheck612]

def rawRow613 : Integer.Sparse Key := [(key2804, -1), (key2801, -1), (key2825, 2), (key2781, 1), (key2778, 1), (key2902, -1), (key2866, -1), (key2790, -2), (key2895, 1), (key2856, 1), (key2701, 1), (key2698, 1), (key2722, -2), (key2627, -1), (key2624, -1), (key2981, 1), (key2866, 1), (key2636, 2), (key2974, -1), (key2856, -1), (key2666, -1), (key2663, -1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2958, -1), (key2947, -1), (key2651, -1), (key2645, -1), (key2745, 1), (key2734, 1), (key2666, 2), (key2790, -1), (key2781, -1), (key2611, -2), (key2825, 1), (key2804, 1), (key2636, 1), (key2627, 1), (key2722, -1), (key2701, -1)]

theorem rawRowCheck613 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form4 = rawRow613 := by decide +kernel

def row613 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -2), (key2734, 1), (key2745, 2), (key2778, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck613 : row613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow613 := by decide +kernel

theorem rowEval613 (x : Key → ℝ) : Integer.Sparse.eval row613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck613, Integer.Sparse.eval_collectBalanced, rawRowCheck613]

def rawRow614 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2801, 2), (key2892, 1), (key2902, 1), (key2778, -1), (key2851, -1), (key2895, -2), (key2790, 1), (key2856, 1), (key2701, 1), (key2722, 1), (key2698, -2), (key2971, -1), (key2981, -1), (key2624, 1), (key2851, 1), (key2974, 2), (key2636, -1), (key2856, -1), (key2734, -1), (key2745, -1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2608, -1), (key2801, -1), (key2745, -1), (key2902, -1), (key2651, 1), (key2895, 1), (key2790, 2), (key2666, -1), (key2781, -1), (key2825, -2), (key2611, 1), (key2804, 1), (key2722, 1), (key2866, 1), (key2636, -1), (key2856, -1)]

theorem rawRowCheck614 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form4 = rawRow614 := by decide +kernel

def row614 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, 2), (key2734, -1), (key2745, -2), (key2778, -1), (key2781, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck614 : row614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow614 := by decide +kernel

theorem rowEval614 (x : Key → ℝ) : Integer.Sparse.eval row614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck614, Integer.Sparse.eval_collectBalanced, rawRowCheck614]

def rawRow615 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2801, 2), (key2902, 1), (key2892, 1), (key2851, -1), (key2778, -1), (key2895, -2), (key2856, 1), (key2790, 1), (key2722, 1), (key2701, 1), (key2698, -2), (key2981, -1), (key2971, -1), (key2851, 1), (key2624, 1), (key2974, 2), (key2856, -1), (key2636, -1), (key2745, -1), (key2734, -1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2801, -1), (key2608, -1), (key2902, -1), (key2745, -1), (key2895, 1), (key2651, 1), (key2790, 2), (key2781, -1), (key2666, -1), (key2825, -2), (key2804, 1), (key2611, 1), (key2866, 1), (key2722, 1), (key2856, -1), (key2636, -1)]

theorem rawRowCheck615 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form4 = rawRow615 := by decide +kernel

def row615 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -2), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, 2), (key2734, -1), (key2745, -2), (key2778, -1), (key2781, -1), (key2790, 3), (key2801, 1), (key2825, -3), (key2856, -1), (key2866, 1), (key2892, 1), (key2895, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

theorem rowCheck615 : row615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow615 := by decide +kernel

theorem rowEval615 (x : Key → ℝ) : Integer.Sparse.eval row615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck615, Integer.Sparse.eval_collectBalanced, rawRowCheck615]

def rawRow616 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2902, 2), (key2781, 1), (key2790, 1), (key2825, -1), (key2866, -1), (key2778, -2), (key2801, 1), (key2851, 1), (key2971, 1), (key2974, 1), (key2981, -2), (key2627, -1), (key2636, -1), (key2722, 1), (key2866, 1), (key2624, 2), (key2698, -1), (key2851, -1), (key2935, -1), (key2941, -1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2745, -1), (key2902, -1), (key2608, -1), (key2624, -1), (key2663, 1), (key2698, 1), (key2722, 2), (key2825, -1), (key2866, -1), (key2636, -2), (key2790, 1), (key2856, 1), (key2611, 1), (key2627, 1), (key2666, -1), (key2701, -1)]

theorem rawRowCheck616 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form4 = rawRow616 := by decide +kernel

def row616 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2701, -1), (key2722, 3), (key2745, -1), (key2778, -2), (key2781, 1), (key2790, 2), (key2801, 1), (key2825, -2), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2958, 1), (key2971, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck616 : row616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow616 := by decide +kernel

theorem rowEval616 (x : Key → ℝ) : Integer.Sparse.eval row616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck616, Integer.Sparse.eval_collectBalanced, rawRowCheck616]

def rawRow617 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2902, 2), (key2790, 1), (key2781, 1), (key2866, -1), (key2825, -1), (key2778, -2), (key2851, 1), (key2801, 1), (key2974, 1), (key2971, 1), (key2981, -2), (key2636, -1), (key2627, -1), (key2866, 1), (key2722, 1), (key2624, 2), (key2851, -1), (key2698, -1), (key2941, -1), (key2935, -1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2902, -1), (key2745, -1), (key2624, -1), (key2608, -1), (key2698, 1), (key2663, 1), (key2722, 2), (key2866, -1), (key2825, -1), (key2636, -2), (key2856, 1), (key2790, 1), (key2627, 1), (key2611, 1), (key2701, -1), (key2666, -1)]

theorem rawRowCheck617 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form4 = rawRow617 := by decide +kernel

def row617 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, -1), (key2701, -1), (key2722, 3), (key2745, -1), (key2778, -2), (key2781, 1), (key2790, 2), (key2801, 1), (key2825, -2), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, -1), (key2902, 1), (key2935, -1), (key2941, -1), (key2958, 1), (key2971, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck617 : row617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow617 := by decide +kernel

theorem rowEval617 (x : Key → ℝ) : Integer.Sparse.eval row617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck617, Integer.Sparse.eval_collectBalanced, rawRowCheck617]

def rawRow618 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2895, 2), (key2804, 1), (key2825, 1), (key2790, -1), (key2856, -1), (key2801, -2), (key2778, 1), (key2851, 1), (key2971, 1), (key2981, 1), (key2974, -2), (key2701, -1), (key2722, -1), (key2636, 1), (key2856, 1), (key2698, 2), (key2624, -1), (key2851, -1), (key2947, -1), (key2958, -1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2651, -1), (key2895, -1), (key2663, -1), (key2698, -1), (key2608, 1), (key2801, 1), (key2825, 2), (key2722, -1), (key2866, -1), (key2790, -2), (key2636, 1), (key2856, 1), (key2666, 1), (key2781, 1), (key2611, -1), (key2804, -1)]

theorem rawRowCheck618 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form4 = rawRow618 := by decide +kernel

def row618 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 2), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -1), (key2722, -2), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, 1), (key2902, -1), (key2941, 1), (key2947, -1), (key2958, -1), (key2971, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck618 : row618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow618 := by decide +kernel

theorem rowEval618 (x : Key → ℝ) : Integer.Sparse.eval row618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck618, Integer.Sparse.eval_collectBalanced, rawRowCheck618]

def rawRow619 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2895, 2), (key2825, 1), (key2804, 1), (key2856, -1), (key2790, -1), (key2801, -2), (key2851, 1), (key2778, 1), (key2981, 1), (key2971, 1), (key2974, -2), (key2722, -1), (key2701, -1), (key2856, 1), (key2636, 1), (key2698, 2), (key2851, -1), (key2624, -1), (key2958, -1), (key2947, -1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2895, -1), (key2651, -1), (key2698, -1), (key2663, -1), (key2801, 1), (key2608, 1), (key2825, 2), (key2866, -1), (key2722, -1), (key2790, -2), (key2856, 1), (key2636, 1), (key2781, 1), (key2666, 1), (key2804, -1), (key2611, -1)]

theorem rawRowCheck619 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form4 = rawRow619 := by decide +kernel

def row619 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 2), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -1), (key2722, -2), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2790, -3), (key2801, -1), (key2825, 3), (key2856, 1), (key2866, -1), (key2892, -1), (key2895, 1), (key2902, -1), (key2941, 1), (key2947, -1), (key2958, -1), (key2971, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck619 : row619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow619 := by decide +kernel

theorem rowEval619 (x : Key → ℝ) : Integer.Sparse.eval row619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck619, Integer.Sparse.eval_collectBalanced, rawRowCheck619]

def rawRow620 : Integer.Sparse Key := [(key2935, -1), (key2935, -1), (key2941, 2), (key2947, 1), (key2947, 1), (key2974, -1), (key2974, -1), (key2958, -2), (key2981, 1), (key2981, 1), (key2645, 1), (key2645, 1), (key2651, -2), (key2734, -1), (key2734, -1), (key2895, 1), (key2895, 1), (key2745, 2), (key2902, -1), (key2902, -1), (key2611, -1), (key2611, -1), (key2636, 1), (key2636, 1), (key2666, 1), (key2666, 1), (key2790, -1), (key2790, -1), (key2722, -1), (key2722, -1), (key2825, 1), (key2825, 1), (key2608, 2), (key2624, -1), (key2624, -1), (key2663, -2), (key2698, 1), (key2698, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

theorem rawRowCheck620 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form4 = rawRow620 := by decide +kernel

def row620 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2663, -2), (key2666, 2), (key2698, 2), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, 2), (key2790, -2), (key2801, -2), (key2825, 2), (key2895, 2), (key2902, -2), (key2935, -2), (key2941, 2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

theorem rowCheck620 : row620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow620 := by decide +kernel

theorem rowEval620 (x : Key → ℝ) : Integer.Sparse.eval row620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck620, Integer.Sparse.eval_collectBalanced, rawRowCheck620]

def rawRow621 : Integer.Sparse Key := [(key2935, -1), (key2941, -1), (key2935, 2), (key2971, 1), (key2974, 1), (key2947, -1), (key2971, -1), (key2981, -2), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2645, -2), (key2892, -1), (key2895, -1), (key2734, 1), (key2892, 1), (key2902, 2), (key2745, -1), (key2902, -1), (key2627, -1), (key2636, -1), (key2611, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2666, -1), (key2781, -1), (key2825, -1), (key2866, -1), (key2722, 1), (key2866, 1), (key2624, 2), (key2608, -1), (key2624, -1), (key2698, -2), (key2663, 1), (key2698, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

theorem rawRowCheck621 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form4 = rawRow621 := by decide +kernel

def row621 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck621 : row621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow621 := by decide +kernel

theorem rowEval621 (x : Key → ℝ) : Integer.Sparse.eval row621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck621, Integer.Sparse.eval_collectBalanced, rawRowCheck621]

def rawRow622 : Integer.Sparse Key := [(key2941, -1), (key2935, -1), (key2935, 2), (key2974, 1), (key2971, 1), (key2971, -1), (key2947, -1), (key2981, -2), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2645, -2), (key2895, -1), (key2892, -1), (key2892, 1), (key2734, 1), (key2902, 2), (key2902, -1), (key2745, -1), (key2636, -1), (key2627, -1), (key2627, 1), (key2611, 1), (key2790, 1), (key2781, 1), (key2781, -1), (key2666, -1), (key2866, -1), (key2825, -1), (key2866, 1), (key2722, 1), (key2624, 2), (key2624, -1), (key2608, -1), (key2698, -2), (key2698, 1), (key2663, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

theorem rawRowCheck622 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form4 = rawRow622 := by decide +kernel

def row622 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck622 : row622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow622 := by decide +kernel

theorem rowEval622 (x : Key → ℝ) : Integer.Sparse.eval row622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck622, Integer.Sparse.eval_collectBalanced, rawRowCheck622]

def rawRow623 : Integer.Sparse Key := [(key2947, -1), (key2947, -1), (key2958, 2), (key2935, 1), (key2935, 1), (key2981, -1), (key2981, -1), (key2941, -2), (key2974, 1), (key2974, 1), (key2734, 1), (key2734, 1), (key2745, -2), (key2645, -1), (key2645, -1), (key2902, 1), (key2902, 1), (key2651, 2), (key2895, -1), (key2895, -1), (key2666, -1), (key2666, -1), (key2722, 1), (key2722, 1), (key2611, 1), (key2611, 1), (key2825, -1), (key2825, -1), (key2636, -1), (key2636, -1), (key2790, 1), (key2790, 1), (key2663, 2), (key2698, -1), (key2698, -1), (key2608, -2), (key2801, 1), (key2801, 1), (key2624, 1), (key2624, 1), (key2698, -1), (key2698, -1)]

theorem rawRowCheck623 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form4 = rawRow623 := by decide +kernel

def row623 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, 2), (key2666, -2), (key2698, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2790, 2), (key2801, 2), (key2825, -2), (key2895, -2), (key2902, 2), (key2935, 2), (key2941, -2), (key2947, -2), (key2958, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck623 : row623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow623 := by decide +kernel

theorem rowEval623 (x : Key → ℝ) : Integer.Sparse.eval row623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck623, Integer.Sparse.eval_collectBalanced, rawRowCheck623]

def rawRow624 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2947, 2), (key2971, 1), (key2981, 1), (key2935, -1), (key2971, -1), (key2974, -2), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2734, -2), (key2892, -1), (key2902, -1), (key2645, 1), (key2892, 1), (key2895, 2), (key2651, -1), (key2895, -1), (key2701, -1), (key2722, -1), (key2666, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2611, -1), (key2804, -1), (key2790, -1), (key2856, -1), (key2636, 1), (key2856, 1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, -2), (key2608, 1), (key2801, 1), (key2698, 1), (key2851, 1), (key2624, -1), (key2851, -1)]

theorem rawRowCheck624 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form4 = rawRow624 := by decide +kernel

def row624 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck624 : row624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow624 := by decide +kernel

theorem rowEval624 (x : Key → ℝ) : Integer.Sparse.eval row624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck624, Integer.Sparse.eval_collectBalanced, rawRowCheck624]

def rawRow625 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2947, 2), (key2981, 1), (key2971, 1), (key2971, -1), (key2935, -1), (key2974, -2), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2734, -2), (key2902, -1), (key2892, -1), (key2892, 1), (key2645, 1), (key2895, 2), (key2895, -1), (key2651, -1), (key2722, -1), (key2701, -1), (key2701, 1), (key2666, 1), (key2825, 1), (key2804, 1), (key2804, -1), (key2611, -1), (key2856, -1), (key2790, -1), (key2856, 1), (key2636, 1), (key2698, 2), (key2698, -1), (key2663, -1), (key2801, -2), (key2801, 1), (key2608, 1), (key2851, 1), (key2698, 1), (key2851, -1), (key2624, -1)]

theorem rawRowCheck625 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form4 = rawRow625 := by decide +kernel

def row625 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2698, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck625 : row625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow625 := by decide +kernel

theorem rowEval625 (x : Key → ℝ) : Integer.Sparse.eval row625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck625, Integer.Sparse.eval_collectBalanced, rawRowCheck625]

def rawRow626 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2981, 2), (key2935, 1), (key2941, 1), (key2958, -1), (key2981, -1), (key2935, -2), (key2947, 1), (key2971, 1), (key2892, 1), (key2895, 1), (key2902, -2), (key2645, -1), (key2651, -1), (key2745, 1), (key2902, 1), (key2645, 2), (key2734, -1), (key2892, -1), (key2781, -1), (key2790, -1), (key2825, 1), (key2866, 1), (key2627, 1), (key2636, 1), (key2722, -1), (key2866, -1), (key2611, -1), (key2627, -1), (key2666, 1), (key2781, 1), (key2778, 2), (key2801, -1), (key2851, -1), (key2624, -2), (key2698, 1), (key2851, 1), (key2608, 1), (key2624, 1), (key2663, -1), (key2698, -1)]

theorem rawRowCheck626 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form4 = rawRow626 := by decide +kernel

def row626 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 2), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck626 : row626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow626 := by decide +kernel

theorem rowEval626 (x : Key → ℝ) : Integer.Sparse.eval row626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck626, Integer.Sparse.eval_collectBalanced, rawRowCheck626]

def rawRow627 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2981, 2), (key2941, 1), (key2935, 1), (key2981, -1), (key2958, -1), (key2935, -2), (key2971, 1), (key2947, 1), (key2895, 1), (key2892, 1), (key2902, -2), (key2651, -1), (key2645, -1), (key2902, 1), (key2745, 1), (key2645, 2), (key2892, -1), (key2734, -1), (key2790, -1), (key2781, -1), (key2866, 1), (key2825, 1), (key2636, 1), (key2627, 1), (key2866, -1), (key2722, -1), (key2627, -1), (key2611, -1), (key2781, 1), (key2666, 1), (key2778, 2), (key2851, -1), (key2801, -1), (key2624, -2), (key2851, 1), (key2698, 1), (key2624, 1), (key2608, 1), (key2698, -1), (key2663, -1)]

theorem rawRowCheck627 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form4 = rawRow627 := by decide +kernel

def row627 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, 2), (key2790, -1), (key2801, -1), (key2825, 1), (key2895, 1), (key2902, -1), (key2935, -1), (key2941, 1), (key2947, 1), (key2958, -1), (key2974, -1), (key2981, 1)]

theorem rowCheck627 : row627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow627 := by decide +kernel

theorem rowEval627 (x : Key → ℝ) : Integer.Sparse.eval row627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form4) x := by
  rw [rowCheck627, Integer.Sparse.eval_collectBalanced, rawRowCheck627]

def rawRow628 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2974, 2), (key2947, 1), (key2958, 1), (key2941, -1), (key2974, -1), (key2947, -2), (key2935, 1), (key2971, 1), (key2892, 1), (key2902, 1), (key2895, -2), (key2734, -1), (key2745, -1), (key2651, 1), (key2895, 1), (key2734, 2), (key2645, -1), (key2892, -1), (key2804, -1), (key2825, -1), (key2790, 1), (key2856, 1), (key2701, 1), (key2722, 1), (key2636, -1), (key2856, -1), (key2666, -1), (key2701, -1), (key2611, 1), (key2804, 1), (key2801, 2), (key2778, -1), (key2851, -1), (key2698, -2), (key2624, 1), (key2851, 1), (key2663, 1), (key2698, 1), (key2608, -1), (key2801, -1)]

theorem rawRowCheck628 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form4 = rawRow628 := by decide +kernel

def row628 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck628 : row628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow628 := by decide +kernel

theorem rowEval628 (x : Key → ℝ) : Integer.Sparse.eval row628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block0.form4) x := by
  rw [rowCheck628, Integer.Sparse.eval_collectBalanced, rawRowCheck628]

def rawRow629 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2974, 2), (key2958, 1), (key2947, 1), (key2974, -1), (key2941, -1), (key2947, -2), (key2971, 1), (key2935, 1), (key2902, 1), (key2892, 1), (key2895, -2), (key2745, -1), (key2734, -1), (key2895, 1), (key2651, 1), (key2734, 2), (key2892, -1), (key2645, -1), (key2825, -1), (key2804, -1), (key2856, 1), (key2790, 1), (key2722, 1), (key2701, 1), (key2856, -1), (key2636, -1), (key2701, -1), (key2666, -1), (key2804, 1), (key2611, 1), (key2801, 2), (key2851, -1), (key2778, -1), (key2698, -2), (key2851, 1), (key2624, 1), (key2698, 1), (key2663, 1), (key2801, -1), (key2608, -1)]

theorem rawRowCheck629 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form4 = rawRow629 := by decide +kernel

def row629 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, -1), (key2790, 1), (key2801, 1), (key2825, -1), (key2895, -1), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

theorem rowCheck629 : row629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow629 := by decide +kernel

theorem rowEval629 (x : Key → ℝ) : Integer.Sparse.eval row629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block0.form4) x := by
  rw [rowCheck629, Integer.Sparse.eval_collectBalanced, rawRowCheck629]

def rawRow630 : Integer.Sparse Key := [(key2617, -2), (key2962, -2), (key2962, -2), (key2620, 1), (key2620, 1), (key2833, 1), (key2833, 1), (key2964, 1), (key2964, 1), (key2633, 2), (key2985, 2), (key2985, 2), (key2643, -1), (key2643, -1), (key2730, -1), (key2730, -1), (key2994, -1), (key2994, -1), (key2650, -1), (key2650, -1), (key2906, -1), (key2906, -1), (key3001, -1), (key3001, -1), (key2655, 1), (key2655, 1), (key2749, 1), (key2749, 1), (key3004, 1), (key3004, 1)]

theorem rawRowCheck630 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form0 = rawRow630 := by decide +kernel

def row630 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

theorem rowCheck630 : row630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow630 := by decide +kernel

theorem rowEval630 (x : Key → ℝ) : Integer.Sparse.eval row630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck630, Integer.Sparse.eval_collectBalanced, rawRowCheck630]

def rawRow631 : Integer.Sparse Key := [(key2962, -2), (key2617, -2), (key2962, -2), (key2833, 1), (key2964, 1), (key2620, 1), (key2964, 1), (key2620, 1), (key2833, 1), (key2985, 2), (key2633, 2), (key2985, 2), (key2730, -1), (key2994, -1), (key2643, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2906, -1), (key3001, -1), (key2650, -1), (key3001, -1), (key2650, -1), (key2906, -1), (key2749, 1), (key3004, 1), (key2655, 1), (key3004, 1), (key2655, 1), (key2749, 1)]

theorem rawRowCheck631 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form0 = rawRow631 := by decide +kernel

def row631 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

theorem rowCheck631 : row631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow631 := by decide +kernel

theorem rowEval631 (x : Key → ℝ) : Integer.Sparse.eval row631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck631, Integer.Sparse.eval_collectBalanced, rawRowCheck631]

def rawRow632 : Integer.Sparse Key := [(key2962, -2), (key2962, -2), (key2617, -2), (key2964, 1), (key2833, 1), (key2964, 1), (key2620, 1), (key2833, 1), (key2620, 1), (key2985, 2), (key2985, 2), (key2633, 2), (key2994, -1), (key2730, -1), (key2994, -1), (key2643, -1), (key2730, -1), (key2643, -1), (key3001, -1), (key2906, -1), (key3001, -1), (key2650, -1), (key2906, -1), (key2650, -1), (key3004, 1), (key2749, 1), (key3004, 1), (key2655, 1), (key2749, 1), (key2655, 1)]

theorem rawRowCheck632 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form0 = rawRow632 := by decide +kernel

def row632 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2633, 2), (key2643, -2), (key2650, -2), (key2655, 2), (key2730, -2), (key2749, 2), (key2833, 2), (key2906, -2), (key2962, -4), (key2964, 2), (key2985, 4), (key2994, -2), (key3001, -2), (key3004, 2)]

theorem rowCheck632 : row632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow632 := by decide +kernel

theorem rowEval632 (x : Key → ℝ) : Integer.Sparse.eval row632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck632, Integer.Sparse.eval_collectBalanced, rawRowCheck632]

def rawRow633 : Integer.Sparse Key := [(key2620, -2), (key2833, -2), (key2964, -2), (key2617, 1), (key2620, 1), (key2810, 1), (key2833, 1), (key2952, 1), (key2962, 1), (key2643, 2), (key2978, 2), (key2994, 2), (key2633, -1), (key2643, -1), (key2707, -1), (key2730, -1), (key2978, -1), (key2985, -1), (key2655, -1), (key2656, -1), (key2899, -1), (key2915, -1), (key2999, -1), (key3004, -1), (key2650, 1), (key2656, 1), (key2739, 1), (key2751, 1), (key2999, 1), (key3001, 1)]

theorem rawRowCheck633 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block1.form0 = rawRow633 := by decide +kernel

def row633 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

theorem rowCheck633 : row633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow633 := by decide +kernel

theorem rowEval633 (x : Key → ℝ) : Integer.Sparse.eval row633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck633, Integer.Sparse.eval_collectBalanced, rawRowCheck633]

def rawRow634 : Integer.Sparse Key := [(key2620, -2), (key2964, -2), (key2833, -2), (key2620, 1), (key2617, 1), (key2833, 1), (key2810, 1), (key2962, 1), (key2952, 1), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2915, -1), (key2899, -1), (key3004, -1), (key2999, -1), (key2656, 1), (key2650, 1), (key2751, 1), (key2739, 1), (key3001, 1), (key2999, 1)]

theorem rawRowCheck634 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block1.form0 = rawRow634 := by decide +kernel

def row634 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

theorem rowCheck634 : row634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow634 := by decide +kernel

theorem rowEval634 (x : Key → ℝ) : Integer.Sparse.eval row634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck634, Integer.Sparse.eval_collectBalanced, rawRowCheck634]

def rawRow635 : Integer.Sparse Key := [(key2833, -2), (key2620, -2), (key2964, -2), (key2810, 1), (key2833, 1), (key2617, 1), (key2962, 1), (key2620, 1), (key2833, 1), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2655, -1), (key3004, -1), (key2656, -1), (key2915, -1), (key2739, 1), (key2999, 1), (key2650, 1), (key3001, 1), (key2656, 1), (key2751, 1)]

theorem rawRowCheck635 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block1.form0 = rawRow635 := by decide +kernel

def row635 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2899, -1), (key2915, -1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

theorem rowCheck635 : row635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow635 := by decide +kernel

theorem rowEval635 (x : Key → ℝ) : Integer.Sparse.eval row635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck635, Integer.Sparse.eval_collectBalanced, rawRowCheck635]

def rawRow636 : Integer.Sparse Key := [(key2833, -2), (key2964, -2), (key2620, -2), (key2833, 1), (key2810, 1), (key2962, 1), (key2617, 1), (key2833, 1), (key2620, 1), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key3004, -1), (key2655, -1), (key2915, -1), (key2656, -1), (key2999, 1), (key2739, 1), (key3001, 1), (key2650, 1), (key2751, 1), (key2656, 1)]

theorem rawRowCheck636 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block1.form0 = rawRow636 := by decide +kernel

def row636 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2899, -1), (key2915, -1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

theorem rowCheck636 : row636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow636 := by decide +kernel

theorem rowEval636 (x : Key → ℝ) : Integer.Sparse.eval row636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck636, Integer.Sparse.eval_collectBalanced, rawRowCheck636]

def rawRow637 : Integer.Sparse Key := [(key2964, -2), (key2620, -2), (key2833, -2), (key2952, 1), (key2962, 1), (key2620, 1), (key2833, 1), (key2617, 1), (key2810, 1), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, -1), (key2707, -1), (key2915, -1), (key3004, -1), (key2656, -1), (key2999, -1), (key2655, -1), (key2899, -1), (key2751, 1), (key3001, 1), (key2656, 1), (key2999, 1), (key2650, 1), (key2739, 1)]

theorem rawRowCheck637 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block1.form0 = rawRow637 := by decide +kernel

def row637 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

theorem rowCheck637 : row637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow637 := by decide +kernel

theorem rowEval637 (x : Key → ℝ) : Integer.Sparse.eval row637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck637, Integer.Sparse.eval_collectBalanced, rawRowCheck637]

def rawRow638 : Integer.Sparse Key := [(key2964, -2), (key2833, -2), (key2620, -2), (key2962, 1), (key2952, 1), (key2833, 1), (key2620, 1), (key2810, 1), (key2617, 1), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key3004, -1), (key2915, -1), (key2999, -1), (key2656, -1), (key2899, -1), (key2655, -1), (key3001, 1), (key2751, 1), (key2999, 1), (key2656, 1), (key2739, 1), (key2650, 1)]

theorem rawRowCheck638 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block1.form0 = rawRow638 := by decide +kernel

def row638 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2707, -1), (key2730, -1), (key2739, 1), (key2751, 1), (key2810, 1), (key2833, -1), (key2899, -1), (key2915, -1), (key2952, 1), (key2962, 1), (key2964, -2), (key2978, 1), (key2985, -1), (key2994, 2), (key3001, 1), (key3004, -1)]

theorem rowCheck638 : row638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow638 := by decide +kernel

theorem rowEval638 (x : Key → ℝ) : Integer.Sparse.eval row638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck638, Integer.Sparse.eval_collectBalanced, rawRowCheck638]

def rawRow639 : Integer.Sparse Key := [(key2633, -2), (key2985, -2), (key2985, -2), (key2643, 1), (key2643, 1), (key2978, 1), (key2978, 1), (key2994, 1), (key2994, 1), (key2617, 2), (key2962, 2), (key2962, 2), (key2655, -1), (key2655, -1), (key2749, -1), (key2749, -1), (key3004, -1), (key3004, -1), (key2620, -1), (key2620, -1), (key2833, -1), (key2833, -1), (key2964, -1), (key2964, -1), (key2643, 1), (key2643, 1), (key2730, 1), (key2730, 1), (key2994, 1), (key2994, 1)]

theorem rawRowCheck639 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form0 = rawRow639 := by decide +kernel

def row639 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2633, -2), (key2643, 4), (key2655, -2), (key2730, 2), (key2749, -2), (key2833, -2), (key2962, 4), (key2964, -2), (key2978, 2), (key2985, -4), (key2994, 4), (key3004, -2)]

theorem rowCheck639 : row639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow639 := by decide +kernel

theorem rowEval639 (x : Key → ℝ) : Integer.Sparse.eval row639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck639, Integer.Sparse.eval_collectBalanced, rawRowCheck639]

end MUB6.Certificate.GramRows

end OAI
