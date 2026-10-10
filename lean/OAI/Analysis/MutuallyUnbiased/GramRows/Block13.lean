import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow512 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2647, 2), (key2629, 1), (key2637, 1), (key2613, -1), (key2629, -1), (key2625, -2), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2937, -2), (key2783, -1), (key2791, -1), (key2668, 1), (key2783, 1), (key2779, 2), (key2664, -1), (key2779, -1), (key2973, -1), (key2975, -1), (key2949, 1), (key2973, 1), (key2894, 1), (key2896, 1), (key2736, -1), (key2894, -1), (key2802, -1), (key2852, -1), (key2699, 1), (key2852, 1), (key2982, 2), (key2959, -1), (key2982, -1), (key2903, -2), (key2746, 1), (key2903, 1), (key2826, 1), (key2867, 1), (key2723, -1), (key2867, -1)]

theorem rawRowCheck512 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form2 = rawRow512 := by decide +kernel

def row512 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck512 : row512 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow512 := by decide +kernel

theorem rowEval512 (x : Key → ℝ) : Integer.Sparse.eval row512 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck512, Integer.Sparse.eval_collectBalanced, rawRowCheck512]

def rawRow513 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2647, 2), (key2637, 1), (key2629, 1), (key2629, -1), (key2613, -1), (key2625, -2), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2937, -2), (key2791, -1), (key2783, -1), (key2783, 1), (key2668, 1), (key2779, 2), (key2779, -1), (key2664, -1), (key2975, -1), (key2973, -1), (key2973, 1), (key2949, 1), (key2896, 1), (key2894, 1), (key2894, -1), (key2736, -1), (key2852, -1), (key2802, -1), (key2852, 1), (key2699, 1), (key2982, 2), (key2982, -1), (key2959, -1), (key2903, -2), (key2903, 1), (key2746, 1), (key2867, 1), (key2826, 1), (key2867, -1), (key2723, -1)]

theorem rawRowCheck513 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form2 = rawRow513 := by decide +kernel

def row513 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck513 : row513 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow513 := by decide +kernel

theorem rowEval513 (x : Key → ℝ) : Integer.Sparse.eval row513 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck513, Integer.Sparse.eval_collectBalanced, rawRowCheck513]

def rawRow514 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2668, 2), (key2699, 1), (key2703, 1), (key2703, -1), (key2736, -1), (key2723, -2), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2613, -2), (key2802, -1), (key2806, -1), (key2806, 1), (key2949, 1), (key2826, 2), (key2826, -1), (key2959, -1), (key2625, -1), (key2629, -1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2783, -1), (key2937, -1), (key2867, -1), (key2903, -1), (key2867, 1), (key2982, 1), (key2637, 2), (key2637, -1), (key2652, -1), (key2791, -2), (key2791, 1), (key2942, 1), (key2857, 1), (key2896, 1), (key2857, -1), (key2975, -1)]

theorem rawRowCheck514 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form2 = rawRow514 := by decide +kernel

def row514 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck514 : row514 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow514 := by decide +kernel

theorem rowEval514 (x : Key → ℝ) : Integer.Sparse.eval row514 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck514, Integer.Sparse.eval_collectBalanced, rawRowCheck514]

def rawRow515 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2668, 2), (key2703, 1), (key2699, 1), (key2736, -1), (key2703, -1), (key2723, -2), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2613, -2), (key2806, -1), (key2802, -1), (key2949, 1), (key2806, 1), (key2826, 2), (key2959, -1), (key2826, -1), (key2629, -1), (key2625, -1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, -1), (key2783, -1), (key2903, -1), (key2867, -1), (key2982, 1), (key2867, 1), (key2637, 2), (key2652, -1), (key2637, -1), (key2791, -2), (key2942, 1), (key2791, 1), (key2896, 1), (key2857, 1), (key2975, -1), (key2857, -1)]

theorem rawRowCheck515 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form2 = rawRow515 := by decide +kernel

def row515 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck515 : row515 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow515 := by decide +kernel

theorem rowEval515 (x : Key → ℝ) : Integer.Sparse.eval row515 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck515, Integer.Sparse.eval_collectBalanced, rawRowCheck515]

def rawRow516 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2664, 2), (key2736, 1), (key2736, 1), (key2699, -1), (key2699, -1), (key2746, -2), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2609, -2), (key2949, -1), (key2949, -1), (key2802, 1), (key2802, 1), (key2959, 2), (key2826, -1), (key2826, -1), (key2647, -1), (key2647, -1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2779, -1), (key2779, -1), (key2982, -1), (key2982, -1), (key2903, 1), (key2903, 1), (key2652, 2), (key2637, -1), (key2637, -1), (key2942, -2), (key2791, 1), (key2791, 1), (key2975, 1), (key2975, 1), (key2896, -1), (key2896, -1)]

theorem rawRowCheck516 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form2 = rawRow516 := by decide +kernel

def row516 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck516 : row516 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow516 := by decide +kernel

theorem rowEval516 (x : Key → ℝ) : Integer.Sparse.eval row516 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck516, Integer.Sparse.eval_collectBalanced, rawRowCheck516]

def rawRow517 : Integer.Sparse Key := [(key2699, -1), (key2703, -1), (key2723, 2), (key2664, 1), (key2668, 1), (key2723, -1), (key2746, -1), (key2668, -2), (key2703, 1), (key2736, 1), (key2802, 1), (key2806, 1), (key2826, -2), (key2609, -1), (key2613, -1), (key2826, 1), (key2959, 1), (key2613, 2), (key2806, -1), (key2949, -1), (key2779, -1), (key2783, -1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2867, -1), (key2982, -1), (key2629, -1), (key2647, -1), (key2783, 1), (key2937, 1), (key2791, 2), (key2857, -1), (key2896, -1), (key2637, -2), (key2857, 1), (key2975, 1), (key2637, 1), (key2652, 1), (key2791, -1), (key2942, -1)]

theorem rawRowCheck517 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form2 = rawRow517 := by decide +kernel

def row517 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck517 : row517 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow517 := by decide +kernel

theorem rowEval517 (x : Key → ℝ) : Integer.Sparse.eval row517 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck517, Integer.Sparse.eval_collectBalanced, rawRowCheck517]

def rawRow518 : Integer.Sparse Key := [(key2703, -1), (key2699, -1), (key2723, 2), (key2668, 1), (key2664, 1), (key2746, -1), (key2723, -1), (key2668, -2), (key2736, 1), (key2703, 1), (key2806, 1), (key2802, 1), (key2826, -2), (key2613, -1), (key2609, -1), (key2959, 1), (key2826, 1), (key2613, 2), (key2949, -1), (key2806, -1), (key2783, -1), (key2779, -1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2982, -1), (key2867, -1), (key2647, -1), (key2629, -1), (key2937, 1), (key2783, 1), (key2791, 2), (key2896, -1), (key2857, -1), (key2637, -2), (key2975, 1), (key2857, 1), (key2652, 1), (key2637, 1), (key2942, -1), (key2791, -1)]

theorem rawRowCheck518 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form2 = rawRow518 := by decide +kernel

def row518 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck518 : row518 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow518 := by decide +kernel

theorem rowEval518 (x : Key → ℝ) : Integer.Sparse.eval row518 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck518, Integer.Sparse.eval_collectBalanced, rawRowCheck518]

def rawRow519 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2699, 2), (key2736, 1), (key2746, 1), (key2664, -1), (key2699, -1), (key2736, -2), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2802, -2), (key2949, -1), (key2959, -1), (key2609, 1), (key2802, 1), (key2949, 2), (key2613, -1), (key2806, -1), (key2894, -1), (key2903, -1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2625, -1), (key2852, -1), (key2937, -1), (key2973, -1), (key2647, 1), (key2894, 1), (key2896, 2), (key2791, -1), (key2857, -1), (key2975, -2), (key2637, 1), (key2857, 1), (key2942, 1), (key2975, 1), (key2652, -1), (key2896, -1)]

theorem rawRowCheck519 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form2 = rawRow519 := by decide +kernel

def row519 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck519 : row519 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow519 := by decide +kernel

theorem rowEval519 (x : Key → ℝ) : Integer.Sparse.eval row519 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck519, Integer.Sparse.eval_collectBalanced, rawRowCheck519]

def rawRow520 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2699, 2), (key2746, 1), (key2736, 1), (key2699, -1), (key2664, -1), (key2736, -2), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2802, -2), (key2959, -1), (key2949, -1), (key2802, 1), (key2609, 1), (key2949, 2), (key2806, -1), (key2613, -1), (key2903, -1), (key2894, -1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2852, -1), (key2625, -1), (key2973, -1), (key2937, -1), (key2894, 1), (key2647, 1), (key2896, 2), (key2857, -1), (key2791, -1), (key2975, -2), (key2857, 1), (key2637, 1), (key2975, 1), (key2942, 1), (key2896, -1), (key2652, -1)]

theorem rawRowCheck520 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form2 = rawRow520 := by decide +kernel

def row520 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck520 : row520 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow520 := by decide +kernel

theorem rowEval520 (x : Key → ℝ) : Integer.Sparse.eval row520 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck520, Integer.Sparse.eval_collectBalanced, rawRowCheck520]

def rawRow521 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2746, 2), (key2668, 1), (key2668, 1), (key2723, -1), (key2723, -1), (key2664, -2), (key2699, 1), (key2699, 1), (key2949, 1), (key2949, 1), (key2959, -2), (key2613, -1), (key2613, -1), (key2826, 1), (key2826, 1), (key2609, 2), (key2802, -1), (key2802, -1), (key2937, -1), (key2937, -1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2903, -1), (key2903, -1), (key2625, -1), (key2625, -1), (key2779, 1), (key2779, 1), (key2942, 2), (key2975, -1), (key2975, -1), (key2652, -2), (key2896, 1), (key2896, 1), (key2637, 1), (key2637, 1), (key2791, -1), (key2791, -1)]

theorem rawRowCheck521 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form2 = rawRow521 := by decide +kernel

def row521 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck521 : row521 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow521 := by decide +kernel

theorem rowEval521 (x : Key → ℝ) : Integer.Sparse.eval row521 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck521, Integer.Sparse.eval_collectBalanced, rawRowCheck521]

def rawRow522 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2736, 2), (key2703, 1), (key2723, 1), (key2668, -1), (key2703, -1), (key2699, -2), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2949, -2), (key2806, -1), (key2826, -1), (key2613, 1), (key2806, 1), (key2802, 2), (key2609, -1), (key2802, -1), (key2973, -1), (key2982, -1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, -1), (key2894, -1), (key2779, -1), (key2852, -1), (key2625, 1), (key2852, 1), (key2975, 2), (key2942, -1), (key2975, -1), (key2896, -2), (key2652, 1), (key2896, 1), (key2791, 1), (key2857, 1), (key2637, -1), (key2857, -1)]

theorem rawRowCheck522 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form2 = rawRow522 := by decide +kernel

def row522 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck522 : row522 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow522 := by decide +kernel

theorem rowEval522 (x : Key → ℝ) : Integer.Sparse.eval row522 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck522, Integer.Sparse.eval_collectBalanced, rawRowCheck522]

def rawRow523 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2736, 2), (key2723, 1), (key2703, 1), (key2703, -1), (key2668, -1), (key2699, -2), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2949, -2), (key2826, -1), (key2806, -1), (key2806, 1), (key2613, 1), (key2802, 2), (key2802, -1), (key2609, -1), (key2982, -1), (key2973, -1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2894, -1), (key2647, -1), (key2852, -1), (key2779, -1), (key2852, 1), (key2625, 1), (key2975, 2), (key2975, -1), (key2942, -1), (key2896, -2), (key2896, 1), (key2652, 1), (key2857, 1), (key2791, 1), (key2857, -1), (key2637, -1)]

theorem rawRowCheck523 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form2 = rawRow523 := by decide +kernel

def row523 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck523 : row523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow523 := by decide +kernel

theorem rowEval523 (x : Key → ℝ) : Integer.Sparse.eval row523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck523, Integer.Sparse.eval_collectBalanced, rawRowCheck523]

def rawRow524 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, 1), (key2857, -1), (key2896, -1), (key2826, -2), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2637, -2), (key2699, -1), (key2703, -1), (key2857, 1), (key2975, 1), (key2723, 2), (key2867, -1), (key2982, -1), (key2609, -1), (key2613, -1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2791, -1), (key2942, -1), (key2723, -1), (key2746, -1), (key2826, 1), (key2959, 1), (key2613, 2), (key2629, -1), (key2647, -1), (key2668, -2), (key2783, 1), (key2937, 1), (key2703, 1), (key2736, 1), (key2806, -1), (key2949, -1)]

theorem rawRowCheck524 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form2 = rawRow524 := by decide +kernel

def row524 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck524 : row524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow524 := by decide +kernel

theorem rowEval524 (x : Key → ℝ) : Integer.Sparse.eval row524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck524, Integer.Sparse.eval_collectBalanced, rawRowCheck524]

def rawRow525 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2791, 2), (key2806, 1), (key2802, 1), (key2896, -1), (key2857, -1), (key2826, -2), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2637, -2), (key2703, -1), (key2699, -1), (key2975, 1), (key2857, 1), (key2723, 2), (key2982, -1), (key2867, -1), (key2613, -1), (key2609, -1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2942, -1), (key2791, -1), (key2746, -1), (key2723, -1), (key2959, 1), (key2826, 1), (key2613, 2), (key2647, -1), (key2629, -1), (key2668, -2), (key2937, 1), (key2783, 1), (key2736, 1), (key2703, 1), (key2949, -1), (key2806, -1)]

theorem rawRowCheck525 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form2 = rawRow525 := by decide +kernel

def row525 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck525 : row525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow525 := by decide +kernel

theorem rowEval525 (x : Key → ℝ) : Integer.Sparse.eval row525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck525, Integer.Sparse.eval_collectBalanced, rawRowCheck525]

def rawRow526 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2779, 2), (key2894, 1), (key2896, 1), (key2802, -1), (key2852, -1), (key2903, -2), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2625, -2), (key2973, -1), (key2975, -1), (key2699, 1), (key2852, 1), (key2982, 2), (key2723, -1), (key2867, -1), (key2647, -1), (key2652, -1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2664, -1), (key2779, -1), (key2959, -1), (key2982, -1), (key2746, 1), (key2903, 1), (key2647, 2), (key2613, -1), (key2629, -1), (key2937, -2), (key2668, 1), (key2783, 1), (key2949, 1), (key2973, 1), (key2736, -1), (key2894, -1)]

theorem rawRowCheck526 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form2 = rawRow526 := by decide +kernel

def row526 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck526 : row526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow526 := by decide +kernel

theorem rowEval526 (x : Key → ℝ) : Integer.Sparse.eval row526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck526, Integer.Sparse.eval_collectBalanced, rawRowCheck526]

def rawRow527 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2779, 2), (key2896, 1), (key2894, 1), (key2852, -1), (key2802, -1), (key2903, -2), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2625, -2), (key2975, -1), (key2973, -1), (key2852, 1), (key2699, 1), (key2982, 2), (key2867, -1), (key2723, -1), (key2652, -1), (key2647, -1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2779, -1), (key2664, -1), (key2982, -1), (key2959, -1), (key2903, 1), (key2746, 1), (key2647, 2), (key2629, -1), (key2613, -1), (key2937, -2), (key2783, 1), (key2668, 1), (key2973, 1), (key2949, 1), (key2894, -1), (key2736, -1)]

theorem rawRowCheck527 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form2 = rawRow527 := by decide +kernel

def row527 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck527 : row527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow527 := by decide +kernel

theorem rowEval527 (x : Key → ℝ) : Integer.Sparse.eval row527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck527, Integer.Sparse.eval_collectBalanced, rawRowCheck527]

def rawRow528 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2826, 2), (key2779, 1), (key2783, 1), (key2867, -1), (key2903, -1), (key2791, -2), (key2857, 1), (key2896, 1), (key2699, 1), (key2703, 1), (key2723, -2), (key2625, -1), (key2629, -1), (key2867, 1), (key2982, 1), (key2637, 2), (key2857, -1), (key2975, -1), (key2664, -1), (key2668, -1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2826, -1), (key2959, -1), (key2637, -1), (key2652, -1), (key2791, 1), (key2942, 1), (key2668, 2), (key2703, -1), (key2736, -1), (key2613, -2), (key2806, 1), (key2949, 1), (key2629, 1), (key2647, 1), (key2783, -1), (key2937, -1)]

theorem rawRowCheck528 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form2 = rawRow528 := by decide +kernel

def row528 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck528 : row528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow528 := by decide +kernel

theorem rowEval528 (x : Key → ℝ) : Integer.Sparse.eval row528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block0.form2) x := by
  rw [rowCheck528, Integer.Sparse.eval_collectBalanced, rawRowCheck528]

def rawRow529 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2826, 2), (key2783, 1), (key2779, 1), (key2903, -1), (key2867, -1), (key2791, -2), (key2896, 1), (key2857, 1), (key2703, 1), (key2699, 1), (key2723, -2), (key2629, -1), (key2625, -1), (key2982, 1), (key2867, 1), (key2637, 2), (key2975, -1), (key2857, -1), (key2668, -1), (key2664, -1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2959, -1), (key2826, -1), (key2652, -1), (key2637, -1), (key2942, 1), (key2791, 1), (key2668, 2), (key2736, -1), (key2703, -1), (key2613, -2), (key2949, 1), (key2806, 1), (key2647, 1), (key2629, 1), (key2937, -1), (key2783, -1)]

theorem rawRowCheck529 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form2 = rawRow529 := by decide +kernel

def row529 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck529 : row529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow529 := by decide +kernel

theorem rowEval529 (x : Key → ℝ) : Integer.Sparse.eval row529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck529, Integer.Sparse.eval_collectBalanced, rawRowCheck529]

def rawRow530 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2802, 2), (key2894, 1), (key2903, 1), (key2779, -1), (key2852, -1), (key2896, -2), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2699, -2), (key2973, -1), (key2982, -1), (key2625, 1), (key2852, 1), (key2975, 2), (key2637, -1), (key2857, -1), (key2736, -1), (key2746, -1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2609, -1), (key2802, -1), (key2942, -1), (key2975, -1), (key2652, 1), (key2896, 1), (key2736, 2), (key2668, -1), (key2703, -1), (key2949, -2), (key2613, 1), (key2806, 1), (key2937, 1), (key2973, 1), (key2647, -1), (key2894, -1)]

theorem rawRowCheck530 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form2 = rawRow530 := by decide +kernel

def row530 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck530 : row530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow530 := by decide +kernel

theorem rowEval530 (x : Key → ℝ) : Integer.Sparse.eval row530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck530, Integer.Sparse.eval_collectBalanced, rawRowCheck530]

def rawRow531 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2802, 2), (key2903, 1), (key2894, 1), (key2852, -1), (key2779, -1), (key2896, -2), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2699, -2), (key2982, -1), (key2973, -1), (key2852, 1), (key2625, 1), (key2975, 2), (key2857, -1), (key2637, -1), (key2746, -1), (key2736, -1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2802, -1), (key2609, -1), (key2975, -1), (key2942, -1), (key2896, 1), (key2652, 1), (key2736, 2), (key2703, -1), (key2668, -1), (key2949, -2), (key2806, 1), (key2613, 1), (key2973, 1), (key2937, 1), (key2894, -1), (key2647, -1)]

theorem rawRowCheck531 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form2 = rawRow531 := by decide +kernel

def row531 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck531 : row531 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow531 := by decide +kernel

theorem rowEval531 (x : Key → ℝ) : Integer.Sparse.eval row531 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck531, Integer.Sparse.eval_collectBalanced, rawRowCheck531]

def rawRow532 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2903, 2), (key2783, 1), (key2791, 1), (key2826, -1), (key2867, -1), (key2779, -2), (key2802, 1), (key2852, 1), (key2973, 1), (key2975, 1), (key2982, -2), (key2629, -1), (key2637, -1), (key2723, 1), (key2867, 1), (key2625, 2), (key2699, -1), (key2852, -1), (key2937, -1), (key2942, -1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2746, -1), (key2903, -1), (key2609, -1), (key2625, -1), (key2664, 1), (key2779, 1), (key2937, 2), (key2949, -1), (key2973, -1), (key2647, -2), (key2736, 1), (key2894, 1), (key2613, 1), (key2629, 1), (key2668, -1), (key2783, -1)]

theorem rawRowCheck532 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form2 = rawRow532 := by decide +kernel

def row532 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck532 : row532 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow532 := by decide +kernel

theorem rowEval532 (x : Key → ℝ) : Integer.Sparse.eval row532 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck532, Integer.Sparse.eval_collectBalanced, rawRowCheck532]

def rawRow533 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2903, 2), (key2791, 1), (key2783, 1), (key2867, -1), (key2826, -1), (key2779, -2), (key2852, 1), (key2802, 1), (key2975, 1), (key2973, 1), (key2982, -2), (key2637, -1), (key2629, -1), (key2867, 1), (key2723, 1), (key2625, 2), (key2852, -1), (key2699, -1), (key2942, -1), (key2937, -1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2903, -1), (key2746, -1), (key2625, -1), (key2609, -1), (key2779, 1), (key2664, 1), (key2937, 2), (key2973, -1), (key2949, -1), (key2647, -2), (key2894, 1), (key2736, 1), (key2629, 1), (key2613, 1), (key2783, -1), (key2668, -1)]

theorem rawRowCheck533 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form2 = rawRow533 := by decide +kernel

def row533 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck533 : row533 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow533 := by decide +kernel

theorem rowEval533 (x : Key → ℝ) : Integer.Sparse.eval row533 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck533, Integer.Sparse.eval_collectBalanced, rawRowCheck533]

def rawRow534 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2896, 2), (key2806, 1), (key2826, 1), (key2791, -1), (key2857, -1), (key2802, -2), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2975, -2), (key2703, -1), (key2723, -1), (key2637, 1), (key2857, 1), (key2699, 2), (key2625, -1), (key2852, -1), (key2949, -1), (key2959, -1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2652, -1), (key2896, -1), (key2664, -1), (key2699, -1), (key2609, 1), (key2802, 1), (key2949, 2), (key2937, -1), (key2973, -1), (key2736, -2), (key2647, 1), (key2894, 1), (key2668, 1), (key2703, 1), (key2613, -1), (key2806, -1)]

theorem rawRowCheck534 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form2 = rawRow534 := by decide +kernel

def row534 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck534 : row534 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow534 := by decide +kernel

theorem rowEval534 (x : Key → ℝ) : Integer.Sparse.eval row534 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck534, Integer.Sparse.eval_collectBalanced, rawRowCheck534]

def rawRow535 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2896, 2), (key2826, 1), (key2806, 1), (key2857, -1), (key2791, -1), (key2802, -2), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2975, -2), (key2723, -1), (key2703, -1), (key2857, 1), (key2637, 1), (key2699, 2), (key2852, -1), (key2625, -1), (key2959, -1), (key2949, -1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2896, -1), (key2652, -1), (key2699, -1), (key2664, -1), (key2802, 1), (key2609, 1), (key2949, 2), (key2973, -1), (key2937, -1), (key2736, -2), (key2894, 1), (key2647, 1), (key2703, 1), (key2668, 1), (key2806, -1), (key2613, -1)]

theorem rawRowCheck535 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form2 = rawRow535 := by decide +kernel

def row535 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck535 : row535 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow535 := by decide +kernel

theorem rowEval535 (x : Key → ℝ) : Integer.Sparse.eval row535 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck535, Integer.Sparse.eval_collectBalanced, rawRowCheck535]

def rawRow536 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2942, 2), (key2949, 1), (key2949, 1), (key2975, -1), (key2975, -1), (key2959, -2), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2652, -2), (key2736, -1), (key2736, -1), (key2896, 1), (key2896, 1), (key2746, 2), (key2903, -1), (key2903, -1), (key2613, -1), (key2613, -1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2791, -1), (key2791, -1), (key2723, -1), (key2723, -1), (key2826, 1), (key2826, 1), (key2609, 2), (key2625, -1), (key2625, -1), (key2664, -2), (key2779, 1), (key2779, 1), (key2699, 1), (key2699, 1), (key2802, -1), (key2802, -1)]

theorem rawRowCheck536 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form2 = rawRow536 := by decide +kernel

def row536 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 2), (key2791, -2), (key2802, -2), (key2826, 2), (key2896, 2), (key2903, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

theorem rowCheck536 : row536 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow536 := by decide +kernel

theorem rowEval536 (x : Key → ℝ) : Integer.Sparse.eval row536 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck536, Integer.Sparse.eval_collectBalanced, rawRowCheck536]

def rawRow537 : Integer.Sparse Key := [(key2937, -1), (key2942, -1), (key2937, 2), (key2973, 1), (key2975, 1), (key2949, -1), (key2973, -1), (key2982, -2), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2647, -2), (key2894, -1), (key2896, -1), (key2736, 1), (key2894, 1), (key2903, 2), (key2746, -1), (key2903, -1), (key2629, -1), (key2637, -1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, -1), (key2783, -1), (key2826, -1), (key2867, -1), (key2723, 1), (key2867, 1), (key2625, 2), (key2609, -1), (key2625, -1), (key2779, -2), (key2664, 1), (key2779, 1), (key2802, 1), (key2852, 1), (key2699, -1), (key2852, -1)]

theorem rawRowCheck537 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form2 = rawRow537 := by decide +kernel

def row537 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck537 : row537 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow537 := by decide +kernel

theorem rowEval537 (x : Key → ℝ) : Integer.Sparse.eval row537 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck537, Integer.Sparse.eval_collectBalanced, rawRowCheck537]

def rawRow538 : Integer.Sparse Key := [(key2942, -1), (key2937, -1), (key2937, 2), (key2975, 1), (key2973, 1), (key2973, -1), (key2949, -1), (key2982, -2), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2647, -2), (key2896, -1), (key2894, -1), (key2894, 1), (key2736, 1), (key2903, 2), (key2903, -1), (key2746, -1), (key2637, -1), (key2629, -1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2783, -1), (key2668, -1), (key2867, -1), (key2826, -1), (key2867, 1), (key2723, 1), (key2625, 2), (key2625, -1), (key2609, -1), (key2779, -2), (key2779, 1), (key2664, 1), (key2852, 1), (key2802, 1), (key2852, -1), (key2699, -1)]

theorem rawRowCheck538 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form2 = rawRow538 := by decide +kernel

def row538 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2791, 1), (key2802, 1), (key2826, -1), (key2896, -1), (key2903, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

theorem rowCheck538 : row538 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow538 := by decide +kernel

theorem rowEval538 (x : Key → ℝ) : Integer.Sparse.eval row538 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck538, Integer.Sparse.eval_collectBalanced, rawRowCheck538]

def rawRow539 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2959, 2), (key2937, 1), (key2937, 1), (key2982, -1), (key2982, -1), (key2942, -2), (key2975, 1), (key2975, 1), (key2736, 1), (key2736, 1), (key2746, -2), (key2647, -1), (key2647, -1), (key2903, 1), (key2903, 1), (key2652, 2), (key2896, -1), (key2896, -1), (key2668, -1), (key2668, -1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2826, -1), (key2826, -1), (key2637, -1), (key2637, -1), (key2791, 1), (key2791, 1), (key2664, 2), (key2699, -1), (key2699, -1), (key2609, -2), (key2802, 1), (key2802, 1), (key2625, 1), (key2625, 1), (key2779, -1), (key2779, -1)]

theorem rawRowCheck539 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form2 = rawRow539 := by decide +kernel

def row539 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, -2), (key2791, 2), (key2802, 2), (key2826, -2), (key2896, -2), (key2903, 2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck539 : row539 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow539 := by decide +kernel

theorem rowEval539 (x : Key → ℝ) : Integer.Sparse.eval row539 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck539, Integer.Sparse.eval_collectBalanced, rawRowCheck539]

def rawRow540 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2949, 2), (key2973, 1), (key2982, 1), (key2937, -1), (key2973, -1), (key2975, -2), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2736, -2), (key2894, -1), (key2903, -1), (key2647, 1), (key2894, 1), (key2896, 2), (key2652, -1), (key2896, -1), (key2703, -1), (key2723, -1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, -1), (key2806, -1), (key2791, -1), (key2857, -1), (key2637, 1), (key2857, 1), (key2699, 2), (key2664, -1), (key2699, -1), (key2802, -2), (key2609, 1), (key2802, 1), (key2779, 1), (key2852, 1), (key2625, -1), (key2852, -1)]

theorem rawRowCheck540 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form2 = rawRow540 := by decide +kernel

def row540 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck540 : row540 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow540 := by decide +kernel

theorem rowEval540 (x : Key → ℝ) : Integer.Sparse.eval row540 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck540, Integer.Sparse.eval_collectBalanced, rawRowCheck540]

def rawRow541 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2949, 2), (key2982, 1), (key2973, 1), (key2973, -1), (key2937, -1), (key2975, -2), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2736, -2), (key2903, -1), (key2894, -1), (key2894, 1), (key2647, 1), (key2896, 2), (key2896, -1), (key2652, -1), (key2723, -1), (key2703, -1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2806, -1), (key2613, -1), (key2857, -1), (key2791, -1), (key2857, 1), (key2637, 1), (key2699, 2), (key2699, -1), (key2664, -1), (key2802, -2), (key2802, 1), (key2609, 1), (key2852, 1), (key2779, 1), (key2852, -1), (key2625, -1)]

theorem rawRowCheck541 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form2 = rawRow541 := by decide +kernel

def row541 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck541 : row541 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow541 := by decide +kernel

theorem rowEval541 (x : Key → ℝ) : Integer.Sparse.eval row541 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck541, Integer.Sparse.eval_collectBalanced, rawRowCheck541]

def rawRow542 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2982, 2), (key2937, 1), (key2942, 1), (key2959, -1), (key2982, -1), (key2937, -2), (key2949, 1), (key2973, 1), (key2894, 1), (key2896, 1), (key2903, -2), (key2647, -1), (key2652, -1), (key2746, 1), (key2903, 1), (key2647, 2), (key2736, -1), (key2894, -1), (key2783, -1), (key2791, -1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2723, -1), (key2867, -1), (key2613, -1), (key2629, -1), (key2668, 1), (key2783, 1), (key2779, 2), (key2802, -1), (key2852, -1), (key2625, -2), (key2699, 1), (key2852, 1), (key2609, 1), (key2625, 1), (key2664, -1), (key2779, -1)]

theorem rawRowCheck542 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form2 = rawRow542 := by decide +kernel

def row542 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck542 : row542 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow542 := by decide +kernel

theorem rowEval542 (x : Key → ℝ) : Integer.Sparse.eval row542 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block0.form2) x := by
  rw [rowCheck542, Integer.Sparse.eval_collectBalanced, rawRowCheck542]

def rawRow543 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2982, 2), (key2942, 1), (key2937, 1), (key2982, -1), (key2959, -1), (key2937, -2), (key2973, 1), (key2949, 1), (key2896, 1), (key2894, 1), (key2903, -2), (key2652, -1), (key2647, -1), (key2903, 1), (key2746, 1), (key2647, 2), (key2894, -1), (key2736, -1), (key2791, -1), (key2783, -1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2867, -1), (key2723, -1), (key2629, -1), (key2613, -1), (key2783, 1), (key2668, 1), (key2779, 2), (key2852, -1), (key2802, -1), (key2625, -2), (key2852, 1), (key2699, 1), (key2625, 1), (key2609, 1), (key2779, -1), (key2664, -1)]

theorem rawRowCheck543 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form2 = rawRow543 := by decide +kernel

def row543 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, 1), (key2791, -1), (key2802, -1), (key2826, 1), (key2896, 1), (key2903, -1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck543 : row543 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow543 := by decide +kernel

theorem rowEval543 (x : Key → ℝ) : Integer.Sparse.eval row543 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck543, Integer.Sparse.eval_collectBalanced, rawRowCheck543]

end MUB6.Certificate.GramRows

end OAI
