import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16000 : Integer.Sparse Key := [(key2703, 2), (key2723, 2), (key2699, 2), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2)]

theorem rawRowCheck16000 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form13 = rawRow16000 := by decide +kernel

def row16000 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16000 : row16000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16000 := by decide +kernel

theorem rowEval16000 (x : Key → ℝ) : Integer.Sparse.eval row16000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16000, Integer.Sparse.eval_collectBalanced, rawRowCheck16000]

def rawRow16001 : Integer.Sparse Key := [(key2723, 2), (key2703, 2), (key2699, 2), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2)]

theorem rawRowCheck16001 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form13 = rawRow16001 := by decide +kernel

def row16001 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16001 : row16001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16001 := by decide +kernel

theorem rowEval16001 (x : Key → ℝ) : Integer.Sparse.eval row16001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16001, Integer.Sparse.eval_collectBalanced, rawRowCheck16001]

def rawRow16002 : Integer.Sparse Key := [(key2736, 2), (key2736, 2), (key2746, 2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2)]

theorem rawRowCheck16002 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form13 = rawRow16002 := by decide +kernel

def row16002 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck16002 : row16002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16002 := by decide +kernel

theorem rowEval16002 (x : Key → ℝ) : Integer.Sparse.eval row16002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16002, Integer.Sparse.eval_collectBalanced, rawRowCheck16002]

def rawRow16003 : Integer.Sparse Key := [(key2736, 2), (key2746, 2), (key2736, 2), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2)]

theorem rawRowCheck16003 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form13 = rawRow16003 := by decide +kernel

def row16003 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck16003 : row16003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16003 := by decide +kernel

theorem rowEval16003 (x : Key → ℝ) : Integer.Sparse.eval row16003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16003, Integer.Sparse.eval_collectBalanced, rawRowCheck16003]

def rawRow16004 : Integer.Sparse Key := [(key2746, 2), (key2736, 2), (key2736, 2), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2)]

theorem rawRowCheck16004 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form13 = rawRow16004 := by decide +kernel

def row16004 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck16004 : row16004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16004 := by decide +kernel

theorem rowEval16004 (x : Key → ℝ) : Integer.Sparse.eval row16004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16004, Integer.Sparse.eval_collectBalanced, rawRowCheck16004]

def rawRow16005 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, 2), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2699, 2), (key2736, 2), (key2802, 2), (key2949, 2), (key2896, 2), (key2975, 2)]

theorem rawRowCheck16005 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form13 = rawRow16005 := by decide +kernel

def row16005 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck16005 : row16005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16005 := by decide +kernel

theorem rowEval16005 (x : Key → ℝ) : Integer.Sparse.eval row16005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16005, Integer.Sparse.eval_collectBalanced, rawRowCheck16005]

def rawRow16006 : Integer.Sparse Key := [(key2783, 2), (key2779, 2), (key2791, 2), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2736, 2), (key2699, 2), (key2949, 2), (key2802, 2), (key2975, 2), (key2896, 2)]

theorem rawRowCheck16006 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form13 = rawRow16006 := by decide +kernel

def row16006 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck16006 : row16006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16006 := by decide +kernel

theorem rowEval16006 (x : Key → ℝ) : Integer.Sparse.eval row16006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16006, Integer.Sparse.eval_collectBalanced, rawRowCheck16006]

def rawRow16007 : Integer.Sparse Key := [(key2779, 2), (key2791, 2), (key2783, 2), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2802, 2), (key2896, 2), (key2699, 2), (key2975, 2), (key2736, 2), (key2949, 2)]

theorem rawRowCheck16007 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form13 = rawRow16007 := by decide +kernel

def row16007 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck16007 : row16007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16007 := by decide +kernel

theorem rowEval16007 (x : Key → ℝ) : Integer.Sparse.eval row16007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16007, Integer.Sparse.eval_collectBalanced, rawRowCheck16007]

def rawRow16008 : Integer.Sparse Key := [(key2791, 2), (key2779, 2), (key2783, 2), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2896, 2), (key2802, 2), (key2975, 2), (key2699, 2), (key2949, 2), (key2736, 2)]

theorem rawRowCheck16008 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form13 = rawRow16008 := by decide +kernel

def row16008 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck16008 : row16008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16008 := by decide +kernel

theorem rowEval16008 (x : Key → ℝ) : Integer.Sparse.eval row16008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16008, Integer.Sparse.eval_collectBalanced, rawRowCheck16008]

def rawRow16009 : Integer.Sparse Key := [(key2783, 2), (key2791, 2), (key2779, 2), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2949, 2), (key2975, 2), (key2736, 2), (key2896, 2), (key2699, 2), (key2802, 2)]

theorem rawRowCheck16009 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form13 = rawRow16009 := by decide +kernel

def row16009 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck16009 : row16009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16009 := by decide +kernel

theorem rowEval16009 (x : Key → ℝ) : Integer.Sparse.eval row16009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16009, Integer.Sparse.eval_collectBalanced, rawRowCheck16009]

def rawRow16010 : Integer.Sparse Key := [(key2791, 2), (key2783, 2), (key2779, 2), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2975, 2), (key2949, 2), (key2896, 2), (key2736, 2), (key2802, 2), (key2699, 2)]

theorem rawRowCheck16010 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form13 = rawRow16010 := by decide +kernel

def row16010 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

theorem rowCheck16010 : row16010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16010 := by decide +kernel

theorem rowEval16010 (x : Key → ℝ) : Integer.Sparse.eval row16010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16010, Integer.Sparse.eval_collectBalanced, rawRowCheck16010]

def rawRow16011 : Integer.Sparse Key := [(key2802, 2), (key2806, 2), (key2826, 2), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2625, 2), (key2647, 2), (key2779, 2), (key2937, 2), (key2903, 2), (key2982, 2)]

theorem rawRowCheck16011 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form13 = rawRow16011 := by decide +kernel

def row16011 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16011 : row16011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16011 := by decide +kernel

theorem rowEval16011 (x : Key → ℝ) : Integer.Sparse.eval row16011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16011, Integer.Sparse.eval_collectBalanced, rawRowCheck16011]

def rawRow16012 : Integer.Sparse Key := [(key2806, 2), (key2802, 2), (key2826, 2), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2647, 2), (key2625, 2), (key2937, 2), (key2779, 2), (key2982, 2), (key2903, 2)]

theorem rawRowCheck16012 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form13 = rawRow16012 := by decide +kernel

def row16012 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16012 : row16012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16012 := by decide +kernel

theorem rowEval16012 (x : Key → ℝ) : Integer.Sparse.eval row16012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16012, Integer.Sparse.eval_collectBalanced, rawRowCheck16012]

def rawRow16013 : Integer.Sparse Key := [(key2802, 2), (key2826, 2), (key2806, 2), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2779, 2), (key2903, 2), (key2625, 2), (key2982, 2), (key2647, 2), (key2937, 2)]

theorem rawRowCheck16013 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form13 = rawRow16013 := by decide +kernel

def row16013 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16013 : row16013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16013 := by decide +kernel

theorem rowEval16013 (x : Key → ℝ) : Integer.Sparse.eval row16013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16013, Integer.Sparse.eval_collectBalanced, rawRowCheck16013]

def rawRow16014 : Integer.Sparse Key := [(key2826, 2), (key2802, 2), (key2806, 2), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2903, 2), (key2779, 2), (key2982, 2), (key2625, 2), (key2937, 2), (key2647, 2)]

theorem rawRowCheck16014 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form13 = rawRow16014 := by decide +kernel

def row16014 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16014 : row16014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16014 := by decide +kernel

theorem rowEval16014 (x : Key → ℝ) : Integer.Sparse.eval row16014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16014, Integer.Sparse.eval_collectBalanced, rawRowCheck16014]

def rawRow16015 : Integer.Sparse Key := [(key2806, 2), (key2826, 2), (key2802, 2), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2937, 2), (key2982, 2), (key2647, 2), (key2903, 2), (key2625, 2), (key2779, 2)]

theorem rawRowCheck16015 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form13 = rawRow16015 := by decide +kernel

def row16015 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16015 : row16015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16015 := by decide +kernel

theorem rowEval16015 (x : Key → ℝ) : Integer.Sparse.eval row16015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16015, Integer.Sparse.eval_collectBalanced, rawRowCheck16015]

def rawRow16016 : Integer.Sparse Key := [(key2826, 2), (key2806, 2), (key2802, 2), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2982, 2), (key2937, 2), (key2903, 2), (key2647, 2), (key2779, 2), (key2625, 2)]

theorem rawRowCheck16016 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form13 = rawRow16016 := by decide +kernel

def row16016 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

theorem rowCheck16016 : row16016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16016 := by decide +kernel

theorem rowEval16016 (x : Key → ℝ) : Integer.Sparse.eval row16016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16016, Integer.Sparse.eval_collectBalanced, rawRowCheck16016]

def rawRow16017 : Integer.Sparse Key := [(key2937, 2), (key2937, 2), (key2942, 2), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2703, 2), (key2703, 2), (key2806, 2), (key2806, 2), (key2857, 2), (key2857, 2)]

theorem rawRowCheck16017 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form13 = rawRow16017 := by decide +kernel

def row16017 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck16017 : row16017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16017 := by decide +kernel

theorem rowEval16017 (x : Key → ℝ) : Integer.Sparse.eval row16017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16017, Integer.Sparse.eval_collectBalanced, rawRowCheck16017]

def rawRow16018 : Integer.Sparse Key := [(key2937, 2), (key2942, 2), (key2937, 2), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2806, 2), (key2857, 2), (key2703, 2), (key2857, 2), (key2703, 2), (key2806, 2)]

theorem rawRowCheck16018 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form13 = rawRow16018 := by decide +kernel

def row16018 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck16018 : row16018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16018 := by decide +kernel

theorem rowEval16018 (x : Key → ℝ) : Integer.Sparse.eval row16018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16018, Integer.Sparse.eval_collectBalanced, rawRowCheck16018]

def rawRow16019 : Integer.Sparse Key := [(key2942, 2), (key2937, 2), (key2937, 2), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2857, 2), (key2806, 2), (key2857, 2), (key2703, 2), (key2806, 2), (key2703, 2)]

theorem rawRowCheck16019 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form13 = rawRow16019 := by decide +kernel

def row16019 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

theorem rowCheck16019 : row16019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16019 := by decide +kernel

theorem rowEval16019 (x : Key → ℝ) : Integer.Sparse.eval row16019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck16019, Integer.Sparse.eval_collectBalanced, rawRowCheck16019]

def rawRow16020 : Integer.Sparse Key := [(key2949, 2), (key2949, 2), (key2959, 2), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2629, 2), (key2629, 2), (key2783, 2), (key2783, 2), (key2867, 2), (key2867, 2)]

theorem rawRowCheck16020 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form13 = rawRow16020 := by decide +kernel

def row16020 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck16020 : row16020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16020 := by decide +kernel

theorem rowEval16020 (x : Key → ℝ) : Integer.Sparse.eval row16020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16020, Integer.Sparse.eval_collectBalanced, rawRowCheck16020]

def rawRow16021 : Integer.Sparse Key := [(key2949, 2), (key2959, 2), (key2949, 2), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2783, 2), (key2867, 2), (key2629, 2), (key2867, 2), (key2629, 2), (key2783, 2)]

theorem rawRowCheck16021 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form13 = rawRow16021 := by decide +kernel

def row16021 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck16021 : row16021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16021 := by decide +kernel

theorem rowEval16021 (x : Key → ℝ) : Integer.Sparse.eval row16021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck16021, Integer.Sparse.eval_collectBalanced, rawRowCheck16021]

def rawRow16022 : Integer.Sparse Key := [(key2959, 2), (key2949, 2), (key2949, 2), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2867, 2), (key2783, 2), (key2867, 2), (key2629, 2), (key2783, 2), (key2629, 2)]

theorem rawRowCheck16022 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form13 = rawRow16022 := by decide +kernel

def row16022 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

theorem rowCheck16022 : row16022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16022 := by decide +kernel

theorem rowEval16022 (x : Key → ℝ) : Integer.Sparse.eval row16022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck16022, Integer.Sparse.eval_collectBalanced, rawRowCheck16022]

def rawRow16023 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2613, 2), (key2629, 2), (key2647, 2), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2668, -2), (key2783, -2), (key2937, -2), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1), (key2826, 2), (key2867, 2), (key2903, 2), (key2723, -2), (key2867, -2), (key2982, -2)]

theorem rawRowCheck16023 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form14 = rawRow16023 := by decide +kernel

def row16023 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16023 : row16023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16023 := by decide +kernel

theorem rowEval16023 (x : Key → ℝ) : Integer.Sparse.eval row16023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16023, Integer.Sparse.eval_collectBalanced, rawRowCheck16023]

def rawRow16024 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2613, 2), (key2647, 2), (key2629, 2), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2668, -2), (key2937, -2), (key2783, -2), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1), (key2826, 2), (key2903, 2), (key2867, 2), (key2723, -2), (key2982, -2), (key2867, -2)]

theorem rawRowCheck16024 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form14 = rawRow16024 := by decide +kernel

def row16024 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16024 : row16024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16024 := by decide +kernel

theorem rowEval16024 (x : Key → ℝ) : Integer.Sparse.eval row16024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16024, Integer.Sparse.eval_collectBalanced, rawRowCheck16024]

def rawRow16025 : Integer.Sparse Key := [(key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2629, 2), (key2613, 2), (key2647, 2), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2783, -2), (key2668, -2), (key2937, -2), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2867, 2), (key2826, 2), (key2903, 2), (key2867, -2), (key2723, -2), (key2982, -2)]

theorem rawRowCheck16025 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form14 = rawRow16025 := by decide +kernel

def row16025 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16025 : row16025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16025 := by decide +kernel

theorem rowEval16025 (x : Key → ℝ) : Integer.Sparse.eval row16025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16025, Integer.Sparse.eval_collectBalanced, rawRowCheck16025]

def rawRow16026 : Integer.Sparse Key := [(key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2629, 2), (key2647, 2), (key2613, 2), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2783, -2), (key2937, -2), (key2668, -2), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1), (key2867, 2), (key2903, 2), (key2826, 2), (key2867, -2), (key2982, -2), (key2723, -2)]

theorem rawRowCheck16026 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form14 = rawRow16026 := by decide +kernel

def row16026 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16026 : row16026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16026 := by decide +kernel

theorem rowEval16026 (x : Key → ℝ) : Integer.Sparse.eval row16026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16026, Integer.Sparse.eval_collectBalanced, rawRowCheck16026]

def rawRow16027 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2647, 2), (key2613, 2), (key2629, 2), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2937, -2), (key2668, -2), (key2783, -2), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1), (key2903, 2), (key2826, 2), (key2867, 2), (key2982, -2), (key2723, -2), (key2867, -2)]

theorem rawRowCheck16027 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form14 = rawRow16027 := by decide +kernel

def row16027 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16027 : row16027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16027 := by decide +kernel

theorem rowEval16027 (x : Key → ℝ) : Integer.Sparse.eval row16027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16027, Integer.Sparse.eval_collectBalanced, rawRowCheck16027]

def rawRow16028 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2647, 2), (key2629, 2), (key2613, 2), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2937, -2), (key2783, -2), (key2668, -2), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2903, 2), (key2867, 2), (key2826, 2), (key2982, -2), (key2867, -2), (key2723, -2)]

theorem rawRowCheck16028 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form14 = rawRow16028 := by decide +kernel

def row16028 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16028 : row16028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16028 := by decide +kernel

theorem rowEval16028 (x : Key → ℝ) : Integer.Sparse.eval row16028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16028, Integer.Sparse.eval_collectBalanced, rawRowCheck16028]

def rawRow16029 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2609, 2), (key2625, 2), (key2625, 2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2664, -2), (key2779, -2), (key2779, -2), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2959, 2), (key2982, 2), (key2982, 2), (key2746, -2), (key2903, -2), (key2903, -2)]

theorem rawRowCheck16029 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form14 = rawRow16029 := by decide +kernel

def row16029 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

theorem rowCheck16029 : row16029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16029 := by decide +kernel

theorem rowEval16029 (x : Key → ℝ) : Integer.Sparse.eval row16029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16029, Integer.Sparse.eval_collectBalanced, rawRowCheck16029]

def rawRow16030 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2625, 2), (key2609, 2), (key2625, 2), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2779, -2), (key2664, -2), (key2779, -2), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2982, 2), (key2959, 2), (key2982, 2), (key2903, -2), (key2746, -2), (key2903, -2)]

theorem rawRowCheck16030 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form14 = rawRow16030 := by decide +kernel

def row16030 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

theorem rowCheck16030 : row16030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16030 := by decide +kernel

theorem rowEval16030 (x : Key → ℝ) : Integer.Sparse.eval row16030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16030, Integer.Sparse.eval_collectBalanced, rawRowCheck16030]

def rawRow16031 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2625, 2), (key2625, 2), (key2609, 2), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2779, -2), (key2779, -2), (key2664, -2), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2982, 2), (key2982, 2), (key2959, 2), (key2903, -2), (key2903, -2), (key2746, -2)]

theorem rawRowCheck16031 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form14 = rawRow16031 := by decide +kernel

def row16031 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

theorem rowCheck16031 : row16031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16031 := by decide +kernel

theorem rowEval16031 (x : Key → ℝ) : Integer.Sparse.eval row16031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16031, Integer.Sparse.eval_collectBalanced, rawRowCheck16031]

def rawRow16032 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2668, 2), (key2703, 2), (key2736, 2), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2613, -2), (key2806, -2), (key2949, -2), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2791, 2), (key2857, 2), (key2896, 2), (key2637, -2), (key2857, -2), (key2975, -2)]

theorem rawRowCheck16032 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form14 = rawRow16032 := by decide +kernel

def row16032 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16032 : row16032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16032 := by decide +kernel

theorem rowEval16032 (x : Key → ℝ) : Integer.Sparse.eval row16032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16032, Integer.Sparse.eval_collectBalanced, rawRowCheck16032]

def rawRow16033 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2668, 2), (key2736, 2), (key2703, 2), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2613, -2), (key2949, -2), (key2806, -2), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2791, 2), (key2896, 2), (key2857, 2), (key2637, -2), (key2975, -2), (key2857, -2)]

theorem rawRowCheck16033 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form14 = rawRow16033 := by decide +kernel

def row16033 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16033 : row16033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16033 := by decide +kernel

theorem rowEval16033 (x : Key → ℝ) : Integer.Sparse.eval row16033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16033, Integer.Sparse.eval_collectBalanced, rawRowCheck16033]

def rawRow16034 : Integer.Sparse Key := [(key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2703, 2), (key2668, 2), (key2736, 2), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2806, -2), (key2613, -2), (key2949, -2), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2857, 2), (key2791, 2), (key2896, 2), (key2857, -2), (key2637, -2), (key2975, -2)]

theorem rawRowCheck16034 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form14 = rawRow16034 := by decide +kernel

def row16034 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16034 : row16034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16034 := by decide +kernel

theorem rowEval16034 (x : Key → ℝ) : Integer.Sparse.eval row16034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16034, Integer.Sparse.eval_collectBalanced, rawRowCheck16034]

def rawRow16035 : Integer.Sparse Key := [(key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2703, 2), (key2736, 2), (key2668, 2), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2806, -2), (key2949, -2), (key2613, -2), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2857, 2), (key2896, 2), (key2791, 2), (key2857, -2), (key2975, -2), (key2637, -2)]

theorem rawRowCheck16035 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form14 = rawRow16035 := by decide +kernel

def row16035 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16035 : row16035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16035 := by decide +kernel

theorem rowEval16035 (x : Key → ℝ) : Integer.Sparse.eval row16035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16035, Integer.Sparse.eval_collectBalanced, rawRowCheck16035]

def rawRow16036 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2736, 2), (key2668, 2), (key2703, 2), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2949, -2), (key2613, -2), (key2806, -2), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2896, 2), (key2791, 2), (key2857, 2), (key2975, -2), (key2637, -2), (key2857, -2)]

theorem rawRowCheck16036 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form14 = rawRow16036 := by decide +kernel

def row16036 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16036 : row16036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16036 := by decide +kernel

theorem rowEval16036 (x : Key → ℝ) : Integer.Sparse.eval row16036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16036, Integer.Sparse.eval_collectBalanced, rawRowCheck16036]

def rawRow16037 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2736, 2), (key2703, 2), (key2668, 2), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2949, -2), (key2806, -2), (key2613, -2), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2896, 2), (key2857, 2), (key2791, 2), (key2975, -2), (key2857, -2), (key2637, -2)]

theorem rawRowCheck16037 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form14 = rawRow16037 := by decide +kernel

def row16037 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16037 : row16037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16037 := by decide +kernel

theorem rowEval16037 (x : Key → ℝ) : Integer.Sparse.eval row16037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16037, Integer.Sparse.eval_collectBalanced, rawRowCheck16037]

def rawRow16038 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2609, -2), (key2802, -2), (key2802, -2), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2942, 2), (key2975, 2), (key2975, 2), (key2652, -2), (key2896, -2), (key2896, -2)]

theorem rawRowCheck16038 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form14 = rawRow16038 := by decide +kernel

def row16038 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

theorem rowCheck16038 : row16038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16038 := by decide +kernel

theorem rowEval16038 (x : Key → ℝ) : Integer.Sparse.eval row16038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16038, Integer.Sparse.eval_collectBalanced, rawRowCheck16038]

def rawRow16039 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2802, -2), (key2609, -2), (key2802, -2), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2975, 2), (key2942, 2), (key2975, 2), (key2896, -2), (key2652, -2), (key2896, -2)]

theorem rawRowCheck16039 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form14 = rawRow16039 := by decide +kernel

def row16039 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

theorem rowCheck16039 : row16039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16039 := by decide +kernel

theorem rowEval16039 (x : Key → ℝ) : Integer.Sparse.eval row16039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16039, Integer.Sparse.eval_collectBalanced, rawRowCheck16039]

def rawRow16040 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2802, -2), (key2802, -2), (key2609, -2), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2975, 2), (key2975, 2), (key2942, 2), (key2896, -2), (key2896, -2), (key2652, -2)]

theorem rawRowCheck16040 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form14 = rawRow16040 := by decide +kernel

def row16040 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

theorem rowCheck16040 : row16040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16040 := by decide +kernel

theorem rowEval16040 (x : Key → ℝ) : Integer.Sparse.eval row16040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16040, Integer.Sparse.eval_collectBalanced, rawRowCheck16040]

def rawRow16041 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2826, 2), (key2867, 2), (key2903, 2), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1), (key2723, -2), (key2867, -2), (key2982, -2), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2613, 2), (key2629, 2), (key2647, 2), (key2668, -2), (key2783, -2), (key2937, -2)]

theorem rawRowCheck16041 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form14 = rawRow16041 := by decide +kernel

def row16041 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16041 : row16041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16041 := by decide +kernel

theorem rowEval16041 (x : Key → ℝ) : Integer.Sparse.eval row16041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16041, Integer.Sparse.eval_collectBalanced, rawRowCheck16041]

def rawRow16042 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2826, 2), (key2903, 2), (key2867, 2), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1), (key2723, -2), (key2982, -2), (key2867, -2), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2613, 2), (key2647, 2), (key2629, 2), (key2668, -2), (key2937, -2), (key2783, -2)]

theorem rawRowCheck16042 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form14 = rawRow16042 := by decide +kernel

def row16042 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16042 : row16042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16042 := by decide +kernel

theorem rowEval16042 (x : Key → ℝ) : Integer.Sparse.eval row16042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16042, Integer.Sparse.eval_collectBalanced, rawRowCheck16042]

def rawRow16043 : Integer.Sparse Key := [(key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2867, 2), (key2826, 2), (key2903, 2), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2867, -2), (key2723, -2), (key2982, -2), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2629, 2), (key2613, 2), (key2647, 2), (key2783, -2), (key2668, -2), (key2937, -2)]

theorem rawRowCheck16043 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form14 = rawRow16043 := by decide +kernel

def row16043 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16043 : row16043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16043 := by decide +kernel

theorem rowEval16043 (x : Key → ℝ) : Integer.Sparse.eval row16043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16043, Integer.Sparse.eval_collectBalanced, rawRowCheck16043]

def rawRow16044 : Integer.Sparse Key := [(key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2867, 2), (key2903, 2), (key2826, 2), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1), (key2867, -2), (key2982, -2), (key2723, -2), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2629, 2), (key2647, 2), (key2613, 2), (key2783, -2), (key2937, -2), (key2668, -2)]

theorem rawRowCheck16044 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form14 = rawRow16044 := by decide +kernel

def row16044 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16044 : row16044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16044 := by decide +kernel

theorem rowEval16044 (x : Key → ℝ) : Integer.Sparse.eval row16044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16044, Integer.Sparse.eval_collectBalanced, rawRowCheck16044]

def rawRow16045 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2903, 2), (key2826, 2), (key2867, 2), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1), (key2982, -2), (key2723, -2), (key2867, -2), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2647, 2), (key2613, 2), (key2629, 2), (key2937, -2), (key2668, -2), (key2783, -2)]

theorem rawRowCheck16045 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form14 = rawRow16045 := by decide +kernel

def row16045 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16045 : row16045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16045 := by decide +kernel

theorem rowEval16045 (x : Key → ℝ) : Integer.Sparse.eval row16045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16045, Integer.Sparse.eval_collectBalanced, rawRowCheck16045]

def rawRow16046 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2903, 2), (key2867, 2), (key2826, 2), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2982, -2), (key2867, -2), (key2723, -2), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2647, 2), (key2629, 2), (key2613, 2), (key2937, -2), (key2783, -2), (key2668, -2)]

theorem rawRowCheck16046 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form14 = rawRow16046 := by decide +kernel

def row16046 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

theorem rowCheck16046 : row16046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16046 := by decide +kernel

theorem rowEval16046 (x : Key → ℝ) : Integer.Sparse.eval row16046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16046, Integer.Sparse.eval_collectBalanced, rawRowCheck16046]

def rawRow16047 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2791, 2), (key2857, 2), (key2896, 2), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2637, -2), (key2857, -2), (key2975, -2), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2668, 2), (key2703, 2), (key2736, 2), (key2613, -2), (key2806, -2), (key2949, -2)]

theorem rawRowCheck16047 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form14 = rawRow16047 := by decide +kernel

def row16047 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16047 : row16047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16047 := by decide +kernel

theorem rowEval16047 (x : Key → ℝ) : Integer.Sparse.eval row16047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16047, Integer.Sparse.eval_collectBalanced, rawRowCheck16047]

def rawRow16048 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2791, 2), (key2896, 2), (key2857, 2), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2637, -2), (key2975, -2), (key2857, -2), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2668, 2), (key2736, 2), (key2703, 2), (key2613, -2), (key2949, -2), (key2806, -2)]

theorem rawRowCheck16048 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form14 = rawRow16048 := by decide +kernel

def row16048 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16048 : row16048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16048 := by decide +kernel

theorem rowEval16048 (x : Key → ℝ) : Integer.Sparse.eval row16048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16048, Integer.Sparse.eval_collectBalanced, rawRowCheck16048]

def rawRow16049 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2857, 2), (key2791, 2), (key2896, 2), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2857, -2), (key2637, -2), (key2975, -2), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2703, 2), (key2668, 2), (key2736, 2), (key2806, -2), (key2613, -2), (key2949, -2)]

theorem rawRowCheck16049 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form14 = rawRow16049 := by decide +kernel

def row16049 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16049 : row16049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16049 := by decide +kernel

theorem rowEval16049 (x : Key → ℝ) : Integer.Sparse.eval row16049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16049, Integer.Sparse.eval_collectBalanced, rawRowCheck16049]

def rawRow16050 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2857, 2), (key2896, 2), (key2791, 2), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2857, -2), (key2975, -2), (key2637, -2), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2703, 2), (key2736, 2), (key2668, 2), (key2806, -2), (key2949, -2), (key2613, -2)]

theorem rawRowCheck16050 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form14 = rawRow16050 := by decide +kernel

def row16050 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16050 : row16050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16050 := by decide +kernel

theorem rowEval16050 (x : Key → ℝ) : Integer.Sparse.eval row16050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16050, Integer.Sparse.eval_collectBalanced, rawRowCheck16050]

def rawRow16051 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2896, 2), (key2791, 2), (key2857, 2), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2975, -2), (key2637, -2), (key2857, -2), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2736, 2), (key2668, 2), (key2703, 2), (key2949, -2), (key2613, -2), (key2806, -2)]

theorem rawRowCheck16051 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form14 = rawRow16051 := by decide +kernel

def row16051 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16051 : row16051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16051 := by decide +kernel

theorem rowEval16051 (x : Key → ℝ) : Integer.Sparse.eval row16051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16051, Integer.Sparse.eval_collectBalanced, rawRowCheck16051]

def rawRow16052 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2896, 2), (key2857, 2), (key2791, 2), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2975, -2), (key2857, -2), (key2637, -2), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2736, 2), (key2703, 2), (key2668, 2), (key2949, -2), (key2806, -2), (key2613, -2)]

theorem rawRowCheck16052 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form14 = rawRow16052 := by decide +kernel

def row16052 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

theorem rowCheck16052 : row16052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16052 := by decide +kernel

theorem rowEval16052 (x : Key → ℝ) : Integer.Sparse.eval row16052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16052, Integer.Sparse.eval_collectBalanced, rawRowCheck16052]

def rawRow16053 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2959, 2), (key2982, 2), (key2982, 2), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2746, -2), (key2903, -2), (key2903, -2), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2609, 2), (key2625, 2), (key2625, 2), (key2664, -2), (key2779, -2), (key2779, -2)]

theorem rawRowCheck16053 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form14 = rawRow16053 := by decide +kernel

def row16053 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

theorem rowCheck16053 : row16053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16053 := by decide +kernel

theorem rowEval16053 (x : Key → ℝ) : Integer.Sparse.eval row16053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16053, Integer.Sparse.eval_collectBalanced, rawRowCheck16053]

def rawRow16054 : Integer.Sparse Key := [(key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2982, 2), (key2959, 2), (key2982, 2), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2903, -2), (key2746, -2), (key2903, -2), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2625, 2), (key2609, 2), (key2625, 2), (key2779, -2), (key2664, -2), (key2779, -2)]

theorem rawRowCheck16054 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form14 = rawRow16054 := by decide +kernel

def row16054 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

theorem rowCheck16054 : row16054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16054 := by decide +kernel

theorem rowEval16054 (x : Key → ℝ) : Integer.Sparse.eval row16054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16054, Integer.Sparse.eval_collectBalanced, rawRowCheck16054]

def rawRow16055 : Integer.Sparse Key := [(key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2982, 2), (key2982, 2), (key2959, 2), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2903, -2), (key2903, -2), (key2746, -2), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2625, 2), (key2625, 2), (key2609, 2), (key2779, -2), (key2779, -2), (key2664, -2)]

theorem rawRowCheck16055 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form14 = rawRow16055 := by decide +kernel

def row16055 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

theorem rowCheck16055 : row16055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16055 := by decide +kernel

theorem rowEval16055 (x : Key → ℝ) : Integer.Sparse.eval row16055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck16055, Integer.Sparse.eval_collectBalanced, rawRowCheck16055]

def rawRow16056 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2652, -2), (key2896, -2), (key2896, -2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2664, 2), (key2699, 2), (key2699, 2), (key2609, -2), (key2802, -2), (key2802, -2)]

theorem rawRowCheck16056 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form14 = rawRow16056 := by decide +kernel

def row16056 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

theorem rowCheck16056 : row16056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16056 := by decide +kernel

theorem rowEval16056 (x : Key → ℝ) : Integer.Sparse.eval row16056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16056, Integer.Sparse.eval_collectBalanced, rawRowCheck16056]

def rawRow16057 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2896, -2), (key2652, -2), (key2896, -2), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2699, 2), (key2664, 2), (key2699, 2), (key2802, -2), (key2609, -2), (key2802, -2)]

theorem rawRowCheck16057 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form14 = rawRow16057 := by decide +kernel

def row16057 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

theorem rowCheck16057 : row16057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16057 := by decide +kernel

theorem rowEval16057 (x : Key → ℝ) : Integer.Sparse.eval row16057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck16057, Integer.Sparse.eval_collectBalanced, rawRowCheck16057]

def rawRow16058 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2896, -2), (key2896, -2), (key2652, -2), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2699, 2), (key2699, 2), (key2664, 2), (key2802, -2), (key2802, -2), (key2609, -2)]

theorem rawRowCheck16058 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form14 = rawRow16058 := by decide +kernel

def row16058 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

theorem rowCheck16058 : row16058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16058 := by decide +kernel

theorem rowEval16058 (x : Key → ℝ) : Integer.Sparse.eval row16058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck16058, Integer.Sparse.eval_collectBalanced, rawRowCheck16058]

def rawRow16059 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2611, 2), (key2627, 2), (key2636, 2), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2666, -2), (key2701, -2), (key2722, -2), (key2801, -1), (key2804, -1), (key2851, -1), (key2856, -1), (key2892, -1), (key2895, -1), (key2778, 1), (key2781, 1), (key2851, 1), (key2866, 1), (key2892, 1), (key2902, 1), (key2947, 2), (key2971, 2), (key2974, 2), (key2935, -2), (key2971, -2), (key2981, -2)]

theorem rawRowCheck16059 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form15 = rawRow16059 := by decide +kernel

def row16059 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck16059 : row16059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16059 := by decide +kernel

theorem rowEval16059 (x : Key → ℝ) : Integer.Sparse.eval row16059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16059, Integer.Sparse.eval_collectBalanced, rawRowCheck16059]

def rawRow16060 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2611, 2), (key2636, 2), (key2627, 2), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2666, -2), (key2722, -2), (key2701, -2), (key2804, -1), (key2801, -1), (key2856, -1), (key2851, -1), (key2895, -1), (key2892, -1), (key2781, 1), (key2778, 1), (key2866, 1), (key2851, 1), (key2902, 1), (key2892, 1), (key2947, 2), (key2974, 2), (key2971, 2), (key2935, -2), (key2981, -2), (key2971, -2)]

theorem rawRowCheck16060 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form15 = rawRow16060 := by decide +kernel

def row16060 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck16060 : row16060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16060 := by decide +kernel

theorem rowEval16060 (x : Key → ℝ) : Integer.Sparse.eval row16060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16060, Integer.Sparse.eval_collectBalanced, rawRowCheck16060]

def rawRow16061 : Integer.Sparse Key := [(key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2627, 2), (key2611, 2), (key2636, 2), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2701, -2), (key2666, -2), (key2722, -2), (key2851, -1), (key2892, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2851, 1), (key2892, 1), (key2778, 1), (key2902, 1), (key2781, 1), (key2866, 1), (key2971, 2), (key2947, 2), (key2974, 2), (key2971, -2), (key2935, -2), (key2981, -2)]

theorem rawRowCheck16061 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form15 = rawRow16061 := by decide +kernel

def row16061 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck16061 : row16061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16061 := by decide +kernel

theorem rowEval16061 (x : Key → ℝ) : Integer.Sparse.eval row16061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16061, Integer.Sparse.eval_collectBalanced, rawRowCheck16061]

def rawRow16062 : Integer.Sparse Key := [(key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2627, 2), (key2636, 2), (key2611, 2), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2701, -2), (key2722, -2), (key2666, -2), (key2892, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2856, -1), (key2804, -1), (key2892, 1), (key2851, 1), (key2902, 1), (key2778, 1), (key2866, 1), (key2781, 1), (key2971, 2), (key2974, 2), (key2947, 2), (key2971, -2), (key2981, -2), (key2935, -2)]

theorem rawRowCheck16062 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form15 = rawRow16062 := by decide +kernel

def row16062 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck16062 : row16062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16062 := by decide +kernel

theorem rowEval16062 (x : Key → ℝ) : Integer.Sparse.eval row16062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16062, Integer.Sparse.eval_collectBalanced, rawRowCheck16062]

def rawRow16063 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2636, 2), (key2611, 2), (key2627, 2), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2722, -2), (key2666, -2), (key2701, -2), (key2856, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2801, -1), (key2851, -1), (key2866, 1), (key2902, 1), (key2781, 1), (key2892, 1), (key2778, 1), (key2851, 1), (key2974, 2), (key2947, 2), (key2971, 2), (key2981, -2), (key2935, -2), (key2971, -2)]

theorem rawRowCheck16063 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form15 = rawRow16063 := by decide +kernel

def row16063 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck16063 : row16063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16063 := by decide +kernel

theorem rowEval16063 (x : Key → ℝ) : Integer.Sparse.eval row16063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16063, Integer.Sparse.eval_collectBalanced, rawRowCheck16063]

def rawRow16064 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2636, 2), (key2627, 2), (key2611, 2), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2722, -2), (key2701, -2), (key2666, -2), (key2895, -1), (key2856, -1), (key2892, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 1), (key2866, 1), (key2892, 1), (key2781, 1), (key2851, 1), (key2778, 1), (key2974, 2), (key2971, 2), (key2947, 2), (key2981, -2), (key2971, -2), (key2935, -2)]

theorem rawRowCheck16064 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form15 = rawRow16064 := by decide +kernel

def row16064 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

theorem rowCheck16064 : row16064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16064 := by decide +kernel

theorem rowEval16064 (x : Key → ℝ) : Integer.Sparse.eval row16064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16064, Integer.Sparse.eval_collectBalanced, rawRowCheck16064]

def rawRow16065 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2608, 2), (key2624, 2), (key2624, 2), (key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2734, 1), (key2734, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2902, -1), (key2902, -1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2895, 1), (key2895, 1), (key2958, 2), (key2981, 2), (key2981, 2), (key2941, -2), (key2974, -2), (key2974, -2)]

theorem rawRowCheck16065 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form15 = rawRow16065 := by decide +kernel

def row16065 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

theorem rowCheck16065 : row16065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16065 := by decide +kernel

theorem rowEval16065 (x : Key → ℝ) : Integer.Sparse.eval row16065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16065, Integer.Sparse.eval_collectBalanced, rawRowCheck16065]

def rawRow16066 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2624, 2), (key2608, 2), (key2624, 2), (key2701, 1), (key2734, 1), (key2666, 1), (key2734, 1), (key2666, 1), (key2701, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2866, -1), (key2902, -1), (key2825, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2856, 1), (key2895, 1), (key2790, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2981, 2), (key2958, 2), (key2981, 2), (key2974, -2), (key2941, -2), (key2974, -2)]

theorem rawRowCheck16066 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form15 = rawRow16066 := by decide +kernel

def row16066 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

theorem rowCheck16066 : row16066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16066 := by decide +kernel

theorem rowEval16066 (x : Key → ℝ) : Integer.Sparse.eval row16066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16066, Integer.Sparse.eval_collectBalanced, rawRowCheck16066]

def rawRow16067 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2624, 2), (key2624, 2), (key2608, 2), (key2734, 1), (key2701, 1), (key2734, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2902, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2825, -1), (key2895, 1), (key2856, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2790, 1), (key2981, 2), (key2981, 2), (key2958, 2), (key2974, -2), (key2974, -2), (key2941, -2)]

theorem rawRowCheck16067 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form15 = rawRow16067 := by decide +kernel

def row16067 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

theorem rowCheck16067 : row16067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16067 := by decide +kernel

theorem rowEval16067 (x : Key → ℝ) : Integer.Sparse.eval row16067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16067, Integer.Sparse.eval_collectBalanced, rawRowCheck16067]

def rawRow16068 : Integer.Sparse Key := [(key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2666, 2), (key2701, 2), (key2734, 2), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2611, -2), (key2804, -2), (key2825, -2), (key2698, -1), (key2701, -1), (key2851, -1), (key2856, -1), (key2971, -1), (key2974, -1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2734, 2), (key2892, 2), (key2895, 2), (key2645, -2), (key2892, -2), (key2902, -2)]

theorem rawRowCheck16068 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form15 = rawRow16068 := by decide +kernel

def row16068 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck16068 : row16068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16068 := by decide +kernel

theorem rowEval16068 (x : Key → ℝ) : Integer.Sparse.eval row16068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16068, Integer.Sparse.eval_collectBalanced, rawRowCheck16068]

def rawRow16069 : Integer.Sparse Key := [(key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2666, 2), (key2734, 2), (key2701, 2), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2611, -2), (key2825, -2), (key2804, -2), (key2701, -1), (key2698, -1), (key2856, -1), (key2851, -1), (key2974, -1), (key2971, -1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2734, 2), (key2895, 2), (key2892, 2), (key2645, -2), (key2902, -2), (key2892, -2)]

theorem rawRowCheck16069 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form15 = rawRow16069 := by decide +kernel

def row16069 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck16069 : row16069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16069 := by decide +kernel

theorem rowEval16069 (x : Key → ℝ) : Integer.Sparse.eval row16069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16069, Integer.Sparse.eval_collectBalanced, rawRowCheck16069]

def rawRow16070 : Integer.Sparse Key := [(key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2701, 2), (key2666, 2), (key2734, 2), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2804, -2), (key2611, -2), (key2825, -2), (key2851, -1), (key2971, -1), (key2698, -1), (key2974, -1), (key2701, -1), (key2856, -1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2892, 2), (key2734, 2), (key2895, 2), (key2892, -2), (key2645, -2), (key2902, -2)]

theorem rawRowCheck16070 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form15 = rawRow16070 := by decide +kernel

def row16070 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2958, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck16070 : row16070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16070 := by decide +kernel

theorem rowEval16070 (x : Key → ℝ) : Integer.Sparse.eval row16070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16070, Integer.Sparse.eval_collectBalanced, rawRowCheck16070]

def rawRow16071 : Integer.Sparse Key := [(key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2701, 2), (key2734, 2), (key2666, 2), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2804, -2), (key2825, -2), (key2611, -2), (key2971, -1), (key2851, -1), (key2974, -1), (key2698, -1), (key2856, -1), (key2701, -1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2892, 2), (key2895, 2), (key2734, 2), (key2892, -2), (key2902, -2), (key2645, -2)]

theorem rawRowCheck16071 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form15 = rawRow16071 := by decide +kernel

def row16071 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2958, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck16071 : row16071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16071 := by decide +kernel

theorem rowEval16071 (x : Key → ℝ) : Integer.Sparse.eval row16071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16071, Integer.Sparse.eval_collectBalanced, rawRowCheck16071]

def rawRow16072 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2734, 2), (key2666, 2), (key2701, 2), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2825, -2), (key2611, -2), (key2804, -2), (key2856, -1), (key2974, -1), (key2701, -1), (key2971, -1), (key2698, -1), (key2851, -1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2895, 2), (key2734, 2), (key2892, 2), (key2902, -2), (key2645, -2), (key2892, -2)]

theorem rawRowCheck16072 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form15 = rawRow16072 := by decide +kernel

def row16072 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck16072 : row16072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16072 := by decide +kernel

theorem rowEval16072 (x : Key → ℝ) : Integer.Sparse.eval row16072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16072, Integer.Sparse.eval_collectBalanced, rawRowCheck16072]

def rawRow16073 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2734, 2), (key2701, 2), (key2666, 2), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2825, -2), (key2804, -2), (key2611, -2), (key2974, -1), (key2856, -1), (key2971, -1), (key2701, -1), (key2851, -1), (key2698, -1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2895, 2), (key2892, 2), (key2734, 2), (key2902, -2), (key2892, -2), (key2645, -2)]

theorem rawRowCheck16073 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form15 = rawRow16073 := by decide +kernel

def row16073 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

theorem rowCheck16073 : row16073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16073 := by decide +kernel

theorem rowEval16073 (x : Key → ℝ) : Integer.Sparse.eval row16073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16073, Integer.Sparse.eval_collectBalanced, rawRowCheck16073]

def rawRow16074 : Integer.Sparse Key := [(key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2608, -2), (key2801, -2), (key2801, -2), (key2722, -1), (key2722, -1), (key2866, -1), (key2866, -1), (key2981, -1), (key2981, -1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2745, 2), (key2902, 2), (key2902, 2), (key2651, -2), (key2895, -2), (key2895, -2)]

theorem rawRowCheck16074 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form15 = rawRow16074 := by decide +kernel

def row16074 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

theorem rowCheck16074 : row16074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16074 := by decide +kernel

theorem rowEval16074 (x : Key → ℝ) : Integer.Sparse.eval row16074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -2, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16074, Integer.Sparse.eval_collectBalanced, rawRowCheck16074]

def rawRow16075 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2801, -2), (key2608, -2), (key2801, -2), (key2866, -1), (key2981, -1), (key2722, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2902, 2), (key2745, 2), (key2902, 2), (key2895, -2), (key2651, -2), (key2895, -2)]

theorem rawRowCheck16075 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form15 = rawRow16075 := by decide +kernel

def row16075 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

theorem rowCheck16075 : row16075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16075 := by decide +kernel

theorem rowEval16075 (x : Key → ℝ) : Integer.Sparse.eval row16075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16075, Integer.Sparse.eval_collectBalanced, rawRowCheck16075]

def rawRow16076 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2801, -2), (key2801, -2), (key2608, -2), (key2981, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2902, 2), (key2902, 2), (key2745, 2), (key2895, -2), (key2895, -2), (key2651, -2)]

theorem rawRowCheck16076 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form15 = rawRow16076 := by decide +kernel

def row16076 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

theorem rowCheck16076 : row16076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16076 := by decide +kernel

theorem rowEval16076 (x : Key → ℝ) : Integer.Sparse.eval row16076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16076, Integer.Sparse.eval_collectBalanced, rawRowCheck16076]

def rawRow16077 : Integer.Sparse Key := [(key2801, -1), (key2804, -1), (key2851, -1), (key2892, -1), (key2856, -1), (key2895, -1), (key2825, 2), (key2866, 2), (key2902, 2), (key2698, 1), (key2701, 1), (key2851, 1), (key2971, 1), (key2856, 1), (key2974, 1), (key2722, -2), (key2866, -2), (key2981, -2), (key2608, -1), (key2611, -1), (key2624, -1), (key2636, -1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2611, 2), (key2627, 2), (key2636, 2), (key2666, -2), (key2701, -2), (key2722, -2)]

theorem rawRowCheck16077 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form15 = rawRow16077 := by decide +kernel

def row16077 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

theorem rowCheck16077 : row16077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16077 := by decide +kernel

theorem rowEval16077 (x : Key → ℝ) : Integer.Sparse.eval row16077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16077, Integer.Sparse.eval_collectBalanced, rawRowCheck16077]

def rawRow16078 : Integer.Sparse Key := [(key2804, -1), (key2801, -1), (key2892, -1), (key2851, -1), (key2895, -1), (key2856, -1), (key2825, 2), (key2902, 2), (key2866, 2), (key2701, 1), (key2698, 1), (key2971, 1), (key2851, 1), (key2974, 1), (key2856, 1), (key2722, -2), (key2981, -2), (key2866, -2), (key2611, -1), (key2608, -1), (key2636, -1), (key2624, -1), (key2651, -1), (key2645, -1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2611, 2), (key2636, 2), (key2627, 2), (key2666, -2), (key2722, -2), (key2701, -2)]

theorem rawRowCheck16078 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form15 = rawRow16078 := by decide +kernel

def row16078 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

theorem rowCheck16078 : row16078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16078 := by decide +kernel

theorem rowEval16078 (x : Key → ℝ) : Integer.Sparse.eval row16078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16078, Integer.Sparse.eval_collectBalanced, rawRowCheck16078]

def rawRow16079 : Integer.Sparse Key := [(key2851, -1), (key2856, -1), (key2801, -1), (key2895, -1), (key2804, -1), (key2892, -1), (key2866, 2), (key2825, 2), (key2902, 2), (key2851, 1), (key2856, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2866, -2), (key2722, -2), (key2981, -2), (key2624, -1), (key2636, -1), (key2608, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2627, 2), (key2611, 2), (key2636, 2), (key2701, -2), (key2666, -2), (key2722, -2)]

theorem rawRowCheck16079 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form15 = rawRow16079 := by decide +kernel

def row16079 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

theorem rowCheck16079 : row16079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16079 := by decide +kernel

theorem rowEval16079 (x : Key → ℝ) : Integer.Sparse.eval row16079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16079, Integer.Sparse.eval_collectBalanced, rawRowCheck16079]

def rawRow16080 : Integer.Sparse Key := [(key2856, -1), (key2851, -1), (key2895, -1), (key2801, -1), (key2892, -1), (key2804, -1), (key2866, 2), (key2902, 2), (key2825, 2), (key2856, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2971, 1), (key2701, 1), (key2866, -2), (key2981, -2), (key2722, -2), (key2636, -1), (key2624, -1), (key2651, -1), (key2608, -1), (key2636, -1), (key2611, -1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2627, 2), (key2636, 2), (key2611, 2), (key2701, -2), (key2722, -2), (key2666, -2)]

theorem rawRowCheck16080 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form15 = rawRow16080 := by decide +kernel

def row16080 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

theorem rowCheck16080 : row16080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16080 := by decide +kernel

theorem rowEval16080 (x : Key → ℝ) : Integer.Sparse.eval row16080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16080, Integer.Sparse.eval_collectBalanced, rawRowCheck16080]

def rawRow16081 : Integer.Sparse Key := [(key2892, -1), (key2895, -1), (key2804, -1), (key2856, -1), (key2801, -1), (key2851, -1), (key2902, 2), (key2825, 2), (key2866, 2), (key2971, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2698, 1), (key2851, 1), (key2981, -2), (key2722, -2), (key2866, -2), (key2645, -1), (key2651, -1), (key2611, -1), (key2636, -1), (key2608, -1), (key2624, -1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2636, 2), (key2611, 2), (key2627, 2), (key2722, -2), (key2666, -2), (key2701, -2)]

theorem rawRowCheck16081 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form15 = rawRow16081 := by decide +kernel

def row16081 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

theorem rowCheck16081 : row16081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16081 := by decide +kernel

theorem rowEval16081 (x : Key → ℝ) : Integer.Sparse.eval row16081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16081, Integer.Sparse.eval_collectBalanced, rawRowCheck16081]

def rawRow16082 : Integer.Sparse Key := [(key2895, -1), (key2892, -1), (key2856, -1), (key2804, -1), (key2851, -1), (key2801, -1), (key2902, 2), (key2866, 2), (key2825, 2), (key2974, 1), (key2971, 1), (key2856, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, -2), (key2866, -2), (key2722, -2), (key2651, -1), (key2645, -1), (key2636, -1), (key2611, -1), (key2624, -1), (key2608, -1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2636, 2), (key2627, 2), (key2611, 2), (key2722, -2), (key2701, -2), (key2666, -2)]

theorem rawRowCheck16082 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form15 = rawRow16082 := by decide +kernel

def row16082 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

theorem rowCheck16082 : row16082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16082 := by decide +kernel

theorem rowEval16082 (x : Key → ℝ) : Integer.Sparse.eval row16082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16082, Integer.Sparse.eval_collectBalanced, rawRowCheck16082]

def rawRow16083 : Integer.Sparse Key := [(key2778, -1), (key2781, -1), (key2851, -1), (key2892, -1), (key2866, -1), (key2902, -1), (key2790, 2), (key2856, 2), (key2895, 2), (key2624, 1), (key2627, 1), (key2851, 1), (key2971, 1), (key2866, 1), (key2981, 1), (key2636, -2), (key2856, -2), (key2974, -2), (key2663, -1), (key2666, -1), (key2698, -1), (key2734, -1), (key2722, -1), (key2745, -1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2666, 2), (key2781, 2), (key2790, 2), (key2611, -2), (key2804, -2), (key2825, -2)]

theorem rawRowCheck16083 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form15 = rawRow16083 := by decide +kernel

def row16083 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

theorem rowCheck16083 : row16083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16083 := by decide +kernel

theorem rowEval16083 (x : Key → ℝ) : Integer.Sparse.eval row16083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16083, Integer.Sparse.eval_collectBalanced, rawRowCheck16083]

def rawRow16084 : Integer.Sparse Key := [(key2781, -1), (key2778, -1), (key2892, -1), (key2851, -1), (key2902, -1), (key2866, -1), (key2790, 2), (key2895, 2), (key2856, 2), (key2627, 1), (key2624, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2866, 1), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, -1), (key2663, -1), (key2734, -1), (key2698, -1), (key2745, -1), (key2722, -1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2666, 2), (key2790, 2), (key2781, 2), (key2611, -2), (key2825, -2), (key2804, -2)]

theorem rawRowCheck16084 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form15 = rawRow16084 := by decide +kernel

def row16084 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

theorem rowCheck16084 : row16084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16084 := by decide +kernel

theorem rowEval16084 (x : Key → ℝ) : Integer.Sparse.eval row16084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16084, Integer.Sparse.eval_collectBalanced, rawRowCheck16084]

def rawRow16085 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2778, -1), (key2902, -1), (key2781, -1), (key2892, -1), (key2856, 2), (key2790, 2), (key2895, 2), (key2851, 1), (key2866, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2856, -2), (key2636, -2), (key2974, -2), (key2698, -1), (key2722, -1), (key2663, -1), (key2745, -1), (key2666, -1), (key2734, -1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2781, 2), (key2666, 2), (key2790, 2), (key2804, -2), (key2611, -2), (key2825, -2)]

theorem rawRowCheck16085 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form15 = rawRow16085 := by decide +kernel

def row16085 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2892, -1), (key2895, 2), (key2902, -1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

theorem rowCheck16085 : row16085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16085 := by decide +kernel

theorem rowEval16085 (x : Key → ℝ) : Integer.Sparse.eval row16085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16085, Integer.Sparse.eval_collectBalanced, rawRowCheck16085]

def rawRow16086 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2902, -1), (key2778, -1), (key2892, -1), (key2781, -1), (key2856, 2), (key2895, 2), (key2790, 2), (key2866, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2971, 1), (key2627, 1), (key2856, -2), (key2974, -2), (key2636, -2), (key2722, -1), (key2698, -1), (key2745, -1), (key2663, -1), (key2734, -1), (key2666, -1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2781, 2), (key2790, 2), (key2666, 2), (key2804, -2), (key2825, -2), (key2611, -2)]

theorem rawRowCheck16086 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form15 = rawRow16086 := by decide +kernel

def row16086 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2892, -1), (key2895, 2), (key2902, -1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

theorem rowCheck16086 : row16086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16086 := by decide +kernel

theorem rowEval16086 (x : Key → ℝ) : Integer.Sparse.eval row16086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16086, Integer.Sparse.eval_collectBalanced, rawRowCheck16086]

def rawRow16087 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2781, -1), (key2866, -1), (key2778, -1), (key2851, -1), (key2895, 2), (key2790, 2), (key2856, 2), (key2971, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2624, 1), (key2851, 1), (key2974, -2), (key2636, -2), (key2856, -2), (key2734, -1), (key2745, -1), (key2666, -1), (key2722, -1), (key2663, -1), (key2698, -1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2790, 2), (key2666, 2), (key2781, 2), (key2825, -2), (key2611, -2), (key2804, -2)]

theorem rawRowCheck16087 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form15 = rawRow16087 := by decide +kernel

def row16087 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

theorem rowCheck16087 : row16087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16087 := by decide +kernel

theorem rowEval16087 (x : Key → ℝ) : Integer.Sparse.eval row16087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16087, Integer.Sparse.eval_collectBalanced, rawRowCheck16087]

def rawRow16088 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2866, -1), (key2781, -1), (key2851, -1), (key2778, -1), (key2895, 2), (key2856, 2), (key2790, 2), (key2981, 1), (key2971, 1), (key2866, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2974, -2), (key2856, -2), (key2636, -2), (key2745, -1), (key2734, -1), (key2722, -1), (key2666, -1), (key2698, -1), (key2663, -1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2790, 2), (key2781, 2), (key2666, 2), (key2825, -2), (key2804, -2), (key2611, -2)]

theorem rawRowCheck16088 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form15 = rawRow16088 := by decide +kernel

def row16088 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

theorem rowCheck16088 : row16088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16088 := by decide +kernel

theorem rowEval16088 (x : Key → ℝ) : Integer.Sparse.eval row16088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16088, Integer.Sparse.eval_collectBalanced, rawRowCheck16088]

def rawRow16089 : Integer.Sparse Key := [(key2947, -1), (key2947, -1), (key2971, -1), (key2971, -1), (key2974, -1), (key2974, -1), (key2958, 2), (key2981, 2), (key2981, 2), (key2734, 1), (key2734, 1), (key2892, 1), (key2892, 1), (key2895, 1), (key2895, 1), (key2745, -2), (key2902, -2), (key2902, -2), (key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, -2), (key2698, -2), (key2698, -2)]

theorem rawRowCheck16089 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form15 = rawRow16089 := by decide +kernel

def row16089 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

theorem rowCheck16089 : row16089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16089 := by decide +kernel

theorem rowEval16089 (x : Key → ℝ) : Integer.Sparse.eval row16089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16089, Integer.Sparse.eval_collectBalanced, rawRowCheck16089]

def rawRow16090 : Integer.Sparse Key := [(key2971, -1), (key2974, -1), (key2947, -1), (key2974, -1), (key2947, -1), (key2971, -1), (key2981, 2), (key2958, 2), (key2981, 2), (key2892, 1), (key2895, 1), (key2734, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2902, -2), (key2745, -2), (key2902, -2), (key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, -2), (key2663, -2), (key2698, -2)]

theorem rawRowCheck16090 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form15 = rawRow16090 := by decide +kernel

def row16090 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

theorem rowCheck16090 : row16090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16090 := by decide +kernel

theorem rowEval16090 (x : Key → ℝ) : Integer.Sparse.eval row16090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16090, Integer.Sparse.eval_collectBalanced, rawRowCheck16090]

def rawRow16091 : Integer.Sparse Key := [(key2974, -1), (key2971, -1), (key2974, -1), (key2947, -1), (key2971, -1), (key2947, -1), (key2981, 2), (key2981, 2), (key2958, 2), (key2895, 1), (key2892, 1), (key2895, 1), (key2734, 1), (key2892, 1), (key2734, 1), (key2902, -2), (key2902, -2), (key2745, -2), (key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, -2), (key2698, -2), (key2663, -2)]

theorem rawRowCheck16091 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form15 = rawRow16091 := by decide +kernel

def row16091 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

theorem rowCheck16091 : row16091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16091 := by decide +kernel

theorem rowEval16091 (x : Key → ℝ) : Integer.Sparse.eval row16091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck16091, Integer.Sparse.eval_collectBalanced, rawRowCheck16091]

def rawRow16092 : Integer.Sparse Key := [(key2935, -1), (key2935, -1), (key2971, -1), (key2971, -1), (key2981, -1), (key2981, -1), (key2941, 2), (key2974, 2), (key2974, 2), (key2645, 1), (key2645, 1), (key2892, 1), (key2892, 1), (key2902, 1), (key2902, 1), (key2651, -2), (key2895, -2), (key2895, -2), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, -2), (key2801, -2), (key2801, -2)]

theorem rawRowCheck16092 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form15 = rawRow16092 := by decide +kernel

def row16092 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

theorem rowCheck16092 : row16092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16092 := by decide +kernel

theorem rowEval16092 (x : Key → ℝ) : Integer.Sparse.eval row16092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16092, Integer.Sparse.eval_collectBalanced, rawRowCheck16092]

def rawRow16093 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2935, -1), (key2981, -1), (key2935, -1), (key2971, -1), (key2974, 2), (key2941, 2), (key2974, 2), (key2892, 1), (key2902, 1), (key2645, 1), (key2902, 1), (key2645, 1), (key2892, 1), (key2895, -2), (key2651, -2), (key2895, -2), (key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -2), (key2608, -2), (key2801, -2)]

theorem rawRowCheck16093 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form15 = rawRow16093 := by decide +kernel

def row16093 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

theorem rowCheck16093 : row16093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16093 := by decide +kernel

theorem rowEval16093 (x : Key → ℝ) : Integer.Sparse.eval row16093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck16093, Integer.Sparse.eval_collectBalanced, rawRowCheck16093]

def rawRow16094 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2981, -1), (key2935, -1), (key2971, -1), (key2935, -1), (key2974, 2), (key2974, 2), (key2941, 2), (key2902, 1), (key2892, 1), (key2902, 1), (key2645, 1), (key2892, 1), (key2645, 1), (key2895, -2), (key2895, -2), (key2651, -2), (key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, -2), (key2801, -2), (key2608, -2)]

theorem rawRowCheck16094 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form15 = rawRow16094 := by decide +kernel

def row16094 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

theorem rowCheck16094 : row16094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16094 := by decide +kernel

theorem rowEval16094 (x : Key → ℝ) : Integer.Sparse.eval row16094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block4.form15) x := by
  rw [rowCheck16094, Integer.Sparse.eval_collectBalanced, rawRowCheck16094]

def rawRow16095 : Integer.Sparse Key := [(key2592, 4), (key2991, 4), (key2991, 4), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2603, 4), (key2914, 4), (key2914, 4)]

theorem rawRowCheck16095 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form0 = rawRow16095 := by decide +kernel

def row16095 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

theorem rowCheck16095 : row16095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16095 := by decide +kernel

theorem rowEval16095 (x : Key → ℝ) : Integer.Sparse.eval row16095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16095, Integer.Sparse.eval_collectBalanced, rawRowCheck16095]

def rawRow16096 : Integer.Sparse Key := [(key2991, 4), (key2592, 4), (key2991, 4), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2914, 4), (key2603, 4), (key2914, 4)]

theorem rawRowCheck16096 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form0 = rawRow16096 := by decide +kernel

def row16096 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

theorem rowCheck16096 : row16096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16096 := by decide +kernel

theorem rowEval16096 (x : Key → ℝ) : Integer.Sparse.eval row16096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16096, Integer.Sparse.eval_collectBalanced, rawRowCheck16096]

def rawRow16097 : Integer.Sparse Key := [(key2991, 4), (key2991, 4), (key2592, 4), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2914, 4), (key2914, 4), (key2603, 4)]

theorem rawRowCheck16097 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form0 = rawRow16097 := by decide +kernel

def row16097 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

theorem rowCheck16097 : row16097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16097 := by decide +kernel

theorem rowEval16097 (x : Key → ℝ) : Integer.Sparse.eval row16097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 1, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16097, Integer.Sparse.eval_collectBalanced, rawRowCheck16097]

def rawRow16098 : Integer.Sparse Key := [(key2595, 4), (key2970, 4), (key2993, 4), (key2592, -2), (key2595, -2), (key2848, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2602, -2), (key2603, -2), (key2891, -2), (key2914, -2), (key2996, -2), (key3003, -2), (key2602, 4), (key2891, 4), (key2912, 4)]

theorem rawRowCheck16098 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form0 = rawRow16098 := by decide +kernel

def row16098 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

theorem rowCheck16098 : row16098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16098 := by decide +kernel

theorem rowEval16098 (x : Key → ℝ) : Integer.Sparse.eval row16098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16098, Integer.Sparse.eval_collectBalanced, rawRowCheck16098]

def rawRow16099 : Integer.Sparse Key := [(key2595, 4), (key2993, 4), (key2970, 4), (key2595, -2), (key2592, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2970, -2), (key2603, -2), (key2602, -2), (key2914, -2), (key2891, -2), (key3003, -2), (key2996, -2), (key2602, 4), (key2912, 4), (key2891, 4)]

theorem rawRowCheck16099 : GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form0 = rawRow16099 := by decide +kernel

def row16099 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

theorem rowCheck16099 : row16099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16099 := by decide +kernel

theorem rowEval16099 (x : Key → ℝ) : Integer.Sparse.eval row16099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16099, Integer.Sparse.eval_collectBalanced, rawRowCheck16099]

def rawRow16100 : Integer.Sparse Key := [(key2970, 4), (key2595, 4), (key2993, 4), (key2848, -2), (key2970, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2891, -2), (key2996, -2), (key2602, -2), (key3003, -2), (key2603, -2), (key2914, -2), (key2891, 4), (key2602, 4), (key2912, 4)]

theorem rawRowCheck16100 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form0 = rawRow16100 := by decide +kernel

def row16100 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

theorem rowCheck16100 : row16100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16100 := by decide +kernel

theorem rowEval16100 (x : Key → ℝ) : Integer.Sparse.eval row16100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16100, Integer.Sparse.eval_collectBalanced, rawRowCheck16100]

def rawRow16101 : Integer.Sparse Key := [(key2970, 4), (key2993, 4), (key2595, 4), (key2970, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2882, -2), (key2595, -2), (key2996, -2), (key2891, -2), (key3003, -2), (key2602, -2), (key2914, -2), (key2603, -2), (key2891, 4), (key2912, 4), (key2602, 4)]

theorem rawRowCheck16101 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form0 = rawRow16101 := by decide +kernel

def row16101 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

theorem rowCheck16101 : row16101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16101 := by decide +kernel

theorem rowEval16101 (x : Key → ℝ) : Integer.Sparse.eval row16101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16101, Integer.Sparse.eval_collectBalanced, rawRowCheck16101]

def rawRow16102 : Integer.Sparse Key := [(key2993, 4), (key2595, 4), (key2970, 4), (key2882, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2592, -2), (key2848, -2), (key2914, -2), (key3003, -2), (key2603, -2), (key2996, -2), (key2602, -2), (key2891, -2), (key2912, 4), (key2602, 4), (key2891, 4)]

theorem rawRowCheck16102 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form0 = rawRow16102 := by decide +kernel

def row16102 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

theorem rowCheck16102 : row16102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16102 := by decide +kernel

theorem rowEval16102 (x : Key → ℝ) : Integer.Sparse.eval row16102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16102, Integer.Sparse.eval_collectBalanced, rawRowCheck16102]

def rawRow16103 : Integer.Sparse Key := [(key2993, 4), (key2970, 4), (key2595, 4), (key2991, -2), (key2882, -2), (key2970, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key3003, -2), (key2914, -2), (key2996, -2), (key2603, -2), (key2891, -2), (key2602, -2), (key2912, 4), (key2891, 4), (key2602, 4)]

theorem rawRowCheck16103 : GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form0 = rawRow16103 := by decide +kernel

def row16103 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

theorem rowCheck16103 : row16103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16103 := by decide +kernel

theorem rowEval16103 (x : Key → ℝ) : Integer.Sparse.eval row16103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16103, Integer.Sparse.eval_collectBalanced, rawRowCheck16103]

def rawRow16104 : Integer.Sparse Key := [(key2592, 4), (key2991, 4), (key2991, 4), (key2602, -2), (key2602, -2), (key2912, -2), (key2912, -2), (key3003, -2), (key3003, -2), (key2595, -2), (key2595, -2), (key2882, -2), (key2882, -2), (key2993, -2), (key2993, -2), (key2603, 4), (key2914, 4), (key2914, 4)]

theorem rawRowCheck16104 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form0 = rawRow16104 := by decide +kernel

def row16104 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

theorem rowCheck16104 : row16104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16104 := by decide +kernel

theorem rowEval16104 (x : Key → ℝ) : Integer.Sparse.eval row16104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16104, Integer.Sparse.eval_collectBalanced, rawRowCheck16104]

def rawRow16105 : Integer.Sparse Key := [(key2991, 4), (key2592, 4), (key2991, 4), (key2912, -2), (key3003, -2), (key2602, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2914, 4), (key2603, 4), (key2914, 4)]

theorem rawRowCheck16105 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form0 = rawRow16105 := by decide +kernel

def row16105 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

theorem rowCheck16105 : row16105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16105 := by decide +kernel

theorem rowEval16105 (x : Key → ℝ) : Integer.Sparse.eval row16105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16105, Integer.Sparse.eval_collectBalanced, rawRowCheck16105]

def rawRow16106 : Integer.Sparse Key := [(key2991, 4), (key2991, 4), (key2592, 4), (key3003, -2), (key2912, -2), (key3003, -2), (key2602, -2), (key2912, -2), (key2602, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2595, -2), (key2914, 4), (key2914, 4), (key2603, 4)]

theorem rawRowCheck16106 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form0 = rawRow16106 := by decide +kernel

def row16106 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

theorem rowCheck16106 : row16106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16106 := by decide +kernel

theorem rowEval16106 (x : Key → ℝ) : Integer.Sparse.eval row16106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 1, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16106, Integer.Sparse.eval_collectBalanced, rawRowCheck16106]

def rawRow16107 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2379, -2), (key2393, -2), (key2771, -2), (key2912, -2), (key2933, -2), (key2991, -2), (key2595, -2), (key2603, -2), (key2774, -2), (key2914, -2), (key2934, -2), (key2993, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

theorem rawRowCheck16107 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form0 = rawRow16107 := by decide +kernel

def row16107 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 4), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck16107 : row16107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16107 := by decide +kernel

theorem rowEval16107 (x : Key → ℝ) : Integer.Sparse.eval row16107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16107, Integer.Sparse.eval_collectBalanced, rawRowCheck16107]

def rawRow16108 : Integer.Sparse Key := [(key2393, 4), (key2565, 4), (key2441, 4), (key2393, -2), (key2379, -2), (key2912, -2), (key2771, -2), (key2991, -2), (key2933, -2), (key2603, -2), (key2595, -2), (key2914, -2), (key2774, -2), (key2993, -2), (key2934, -2), (key2595, 4), (key2882, 4), (key2774, 4)]

theorem rawRowCheck16108 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form0 = rawRow16108 := by decide +kernel

def row16108 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 4), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck16108 : row16108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16108 := by decide +kernel

theorem rowEval16108 (x : Key → ℝ) : Integer.Sparse.eval row16108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16108, Integer.Sparse.eval_collectBalanced, rawRowCheck16108]

def rawRow16109 : Integer.Sparse Key := [(key2441, 4), (key2393, 4), (key2565, 4), (key2407, -2), (key2441, -2), (key2592, -2), (key2991, -2), (key2602, -2), (key2912, -2), (key2774, -2), (key2934, -2), (key2595, -2), (key2993, -2), (key2603, -2), (key2914, -2), (key2774, 4), (key2595, 4), (key2882, 4)]

theorem rawRowCheck16109 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form0 = rawRow16109 := by decide +kernel

def row16109 : Integer.Sparse Key := [(key2393, 4), (key2407, -2), (key2441, 2), (key2565, 4), (key2592, -2), (key2595, 2), (key2602, -2), (key2603, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck16109 : row16109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16109 := by decide +kernel

theorem rowEval16109 (x : Key → ℝ) : Integer.Sparse.eval row16109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16109, Integer.Sparse.eval_collectBalanced, rawRowCheck16109]

def rawRow16110 : Integer.Sparse Key := [(key2441, 4), (key2565, 4), (key2393, 4), (key2441, -2), (key2407, -2), (key2991, -2), (key2592, -2), (key2912, -2), (key2602, -2), (key2934, -2), (key2774, -2), (key2993, -2), (key2595, -2), (key2914, -2), (key2603, -2), (key2774, 4), (key2882, 4), (key2595, 4)]

theorem rawRowCheck16110 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form0 = rawRow16110 := by decide +kernel

def row16110 : Integer.Sparse Key := [(key2393, 4), (key2407, -2), (key2441, 2), (key2565, 4), (key2592, -2), (key2595, 2), (key2602, -2), (key2603, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

theorem rowCheck16110 : row16110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16110 := by decide +kernel

theorem rowEval16110 (x : Key → ℝ) : Integer.Sparse.eval row16110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -1, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16110, Integer.Sparse.eval_collectBalanced, rawRowCheck16110]

def rawRow16111 : Integer.Sparse Key := [(key2565, 4), (key2393, 4), (key2441, 4), (key2544, -2), (key2555, -2), (key2393, -2), (key2441, -2), (key2379, -2), (key2771, -2), (key2914, -2), (key2993, -2), (key2603, -2), (key2934, -2), (key2595, -2), (key2774, -2), (key2882, 4), (key2595, 4), (key2774, 4)]

theorem rawRowCheck16111 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form0 = rawRow16111 := by decide +kernel

def row16111 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 2), (key2544, -2), (key2555, -2), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2914, -2), (key2934, -2), (key2993, -2)]

theorem rowCheck16111 : row16111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16111 := by decide +kernel

theorem rowEval16111 (x : Key → ℝ) : Integer.Sparse.eval row16111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16111, Integer.Sparse.eval_collectBalanced, rawRowCheck16111]

def rawRow16112 : Integer.Sparse Key := [(key2565, 4), (key2441, 4), (key2393, 4), (key2555, -2), (key2544, -2), (key2441, -2), (key2393, -2), (key2407, -2), (key2592, -2), (key2993, -2), (key2914, -2), (key2934, -2), (key2603, -2), (key2774, -2), (key2595, -2), (key2882, 4), (key2774, 4), (key2595, 4)]

theorem rawRowCheck16112 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form0 = rawRow16112 := by decide +kernel

def row16112 : Integer.Sparse Key := [(key2393, 2), (key2407, -2), (key2441, 2), (key2544, -2), (key2555, -2), (key2565, 4), (key2592, -2), (key2595, 2), (key2603, -2), (key2774, 2), (key2882, 4), (key2914, -2), (key2934, -2), (key2993, -2)]

theorem rowCheck16112 : row16112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16112 := by decide +kernel

theorem rowEval16112 (x : Key → ℝ) : Integer.Sparse.eval row16112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16112, Integer.Sparse.eval_collectBalanced, rawRowCheck16112]

def rawRow16113 : Integer.Sparse Key := [(key2382, 4), (key2507, 4), (key2557, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2545, -2), (key2526, -2), (key2565, -2), (key2592, -2), (key2595, -2), (key2848, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2602, 4), (key2891, 4), (key2912, 4)]

theorem rawRowCheck16113 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form0 = rawRow16113 := by decide +kernel

def row16113 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

theorem rowCheck16113 : row16113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16113 := by decide +kernel

theorem rowEval16113 (x : Key → ℝ) : Integer.Sparse.eval row16113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16113, Integer.Sparse.eval_collectBalanced, rawRowCheck16113]

def rawRow16114 : Integer.Sparse Key := [(key2382, 4), (key2557, 4), (key2507, 4), (key2395, -2), (key2393, -2), (key2545, -2), (key2483, -2), (key2565, -2), (key2526, -2), (key2595, -2), (key2592, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2970, -2), (key2602, 4), (key2912, 4), (key2891, 4)]

theorem rawRowCheck16114 : GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form0 = rawRow16114 := by decide +kernel

def row16114 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

theorem rowCheck16114 : row16114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16114 := by decide +kernel

theorem rowEval16114 (x : Key → ℝ) : Integer.Sparse.eval row16114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, -2, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16114, Integer.Sparse.eval_collectBalanced, rawRowCheck16114]

def rawRow16115 : Integer.Sparse Key := [(key2507, 4), (key2382, 4), (key2557, 4), (key2483, -2), (key2526, -2), (key2393, -2), (key2565, -2), (key2395, -2), (key2545, -2), (key2848, -2), (key2970, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2891, 4), (key2602, 4), (key2912, 4)]

theorem rawRowCheck16115 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form0 = rawRow16115 := by decide +kernel

def row16115 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

theorem rowCheck16115 : row16115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16115 := by decide +kernel

theorem rowEval16115 (x : Key → ℝ) : Integer.Sparse.eval row16115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16115, Integer.Sparse.eval_collectBalanced, rawRowCheck16115]

def rawRow16116 : Integer.Sparse Key := [(key2507, 4), (key2557, 4), (key2382, 4), (key2526, -2), (key2483, -2), (key2565, -2), (key2393, -2), (key2545, -2), (key2395, -2), (key2970, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2882, -2), (key2595, -2), (key2891, 4), (key2912, 4), (key2602, 4)]

theorem rawRowCheck16116 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form0 = rawRow16116 := by decide +kernel

def row16116 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

theorem rowCheck16116 : row16116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16116 := by decide +kernel

theorem rowEval16116 (x : Key → ℝ) : Integer.Sparse.eval row16116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 0, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16116, Integer.Sparse.eval_collectBalanced, rawRowCheck16116]

def rawRow16117 : Integer.Sparse Key := [(key2557, 4), (key2382, 4), (key2507, 4), (key2545, -2), (key2565, -2), (key2395, -2), (key2526, -2), (key2393, -2), (key2483, -2), (key2882, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2592, -2), (key2848, -2), (key2912, 4), (key2602, 4), (key2891, 4)]

theorem rawRowCheck16117 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form0 = rawRow16117 := by decide +kernel

def row16117 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

theorem rowCheck16117 : row16117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16117 := by decide +kernel

theorem rowEval16117 (x : Key → ℝ) : Integer.Sparse.eval row16117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16117, Integer.Sparse.eval_collectBalanced, rawRowCheck16117]

def rawRow16118 : Integer.Sparse Key := [(key2557, 4), (key2507, 4), (key2382, 4), (key2565, -2), (key2545, -2), (key2526, -2), (key2395, -2), (key2483, -2), (key2393, -2), (key2991, -2), (key2882, -2), (key2970, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key2912, 4), (key2891, 4), (key2602, 4)]

theorem rawRowCheck16118 : GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form0 = rawRow16118 := by decide +kernel

def row16118 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

theorem rowCheck16118 : row16118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16118 := by decide +kernel

theorem rowEval16118 (x : Key → ℝ) : Integer.Sparse.eval row16118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -1, 1, 0, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16118, Integer.Sparse.eval_collectBalanced, rawRowCheck16118]

def rawRow16119 : Integer.Sparse Key := [(key2393, 4), (key2441, 4), (key2565, 4), (key2382, -2), (key2395, -2), (key2410, -2), (key2545, -2), (key2445, -2), (key2557, -2), (key2379, -2), (key2393, -2), (key2771, -2), (key2912, -2), (key2933, -2), (key2991, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

theorem rawRowCheck16119 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form0 = rawRow16119 := by decide +kernel

def row16119 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 4), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2933, -2), (key2991, -2)]

theorem rowCheck16119 : row16119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16119 := by decide +kernel

theorem rowEval16119 (x : Key → ℝ) : Integer.Sparse.eval row16119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16119, Integer.Sparse.eval_collectBalanced, rawRowCheck16119]

def rawRow16120 : Integer.Sparse Key := [(key2393, 4), (key2565, 4), (key2441, 4), (key2395, -2), (key2382, -2), (key2545, -2), (key2410, -2), (key2557, -2), (key2445, -2), (key2393, -2), (key2379, -2), (key2912, -2), (key2771, -2), (key2991, -2), (key2933, -2), (key2595, 4), (key2882, 4), (key2774, 4)]

theorem rawRowCheck16120 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form0 = rawRow16120 := by decide +kernel

def row16120 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 4), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2933, -2), (key2991, -2)]

theorem rowCheck16120 : row16120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16120 := by decide +kernel

theorem rowEval16120 (x : Key → ℝ) : Integer.Sparse.eval row16120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16120, Integer.Sparse.eval_collectBalanced, rawRowCheck16120]

def rawRow16121 : Integer.Sparse Key := [(key2441, 4), (key2393, 4), (key2565, 4), (key2410, -2), (key2445, -2), (key2382, -2), (key2557, -2), (key2395, -2), (key2545, -2), (key2407, -2), (key2441, -2), (key2592, -2), (key2991, -2), (key2602, -2), (key2912, -2), (key2774, 4), (key2595, 4), (key2882, 4)]

theorem rawRowCheck16121 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form0 = rawRow16121 := by decide +kernel

def row16121 : Integer.Sparse Key := [(key2382, -2), (key2393, 4), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2602, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2991, -2)]

theorem rowCheck16121 : row16121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16121 := by decide +kernel

theorem rowEval16121 (x : Key → ℝ) : Integer.Sparse.eval row16121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, -2, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16121, Integer.Sparse.eval_collectBalanced, rawRowCheck16121]

def rawRow16122 : Integer.Sparse Key := [(key2441, 4), (key2565, 4), (key2393, 4), (key2445, -2), (key2410, -2), (key2557, -2), (key2382, -2), (key2545, -2), (key2395, -2), (key2441, -2), (key2407, -2), (key2991, -2), (key2592, -2), (key2912, -2), (key2602, -2), (key2774, 4), (key2882, 4), (key2595, 4)]

theorem rawRowCheck16122 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form0 = rawRow16122 := by decide +kernel

def row16122 : Integer.Sparse Key := [(key2382, -2), (key2393, 4), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2602, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2991, -2)]

theorem rowCheck16122 : row16122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16122 := by decide +kernel

theorem rowEval16122 (x : Key → ℝ) : Integer.Sparse.eval row16122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -1, 1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16122, Integer.Sparse.eval_collectBalanced, rawRowCheck16122]

def rawRow16123 : Integer.Sparse Key := [(key2565, 4), (key2393, 4), (key2441, 4), (key2545, -2), (key2557, -2), (key2395, -2), (key2445, -2), (key2382, -2), (key2410, -2), (key2544, -2), (key2555, -2), (key2393, -2), (key2441, -2), (key2379, -2), (key2771, -2), (key2882, 4), (key2595, 4), (key2774, 4)]

theorem rawRowCheck16123 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form0 = rawRow16123 := by decide +kernel

def row16123 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2544, -2), (key2545, -2), (key2555, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4)]

theorem rowCheck16123 : row16123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16123 := by decide +kernel

theorem rowEval16123 (x : Key → ℝ) : Integer.Sparse.eval row16123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -2, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16123, Integer.Sparse.eval_collectBalanced, rawRowCheck16123]

def rawRow16124 : Integer.Sparse Key := [(key2565, 4), (key2441, 4), (key2393, 4), (key2557, -2), (key2545, -2), (key2445, -2), (key2395, -2), (key2410, -2), (key2382, -2), (key2555, -2), (key2544, -2), (key2441, -2), (key2393, -2), (key2407, -2), (key2592, -2), (key2882, 4), (key2774, 4), (key2595, 4)]

theorem rawRowCheck16124 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form0 = rawRow16124 := by decide +kernel

def row16124 : Integer.Sparse Key := [(key2382, -2), (key2393, 2), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2544, -2), (key2545, -2), (key2555, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

theorem rowCheck16124 : row16124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16124 := by decide +kernel

theorem rowEval16124 (x : Key → ℝ) : Integer.Sparse.eval row16124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -1, -2] GramFunctions.Block4.form0) x := by
  rw [rowCheck16124, Integer.Sparse.eval_collectBalanced, rawRowCheck16124]

def rawRow16125 : Integer.Sparse Key := [(key2395, 4), (key2445, 4), (key2526, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2483, -2), (key2441, -2), (key2507, -2), (key2382, -2), (key2393, -2), (key2410, -2), (key2483, -2), (key2441, -2), (key2507, -2), (key2379, 4), (key2771, 4), (key2848, 4)]

theorem rawRowCheck16125 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form0 = rawRow16125 := by decide +kernel

def row16125 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4), (key2848, 4)]

theorem rowCheck16125 : row16125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16125 := by decide +kernel

theorem rowEval16125 (x : Key → ℝ) : Integer.Sparse.eval row16125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16125, Integer.Sparse.eval_collectBalanced, rawRowCheck16125]

def rawRow16126 : Integer.Sparse Key := [(key2395, 4), (key2526, 4), (key2445, 4), (key2393, -2), (key2382, -2), (key2483, -2), (key2410, -2), (key2507, -2), (key2441, -2), (key2393, -2), (key2382, -2), (key2483, -2), (key2410, -2), (key2507, -2), (key2441, -2), (key2379, 4), (key2848, 4), (key2771, 4)]

theorem rawRowCheck16126 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form0 = rawRow16126 := by decide +kernel

def row16126 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4), (key2848, 4)]

theorem rowCheck16126 : row16126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16126 := by decide +kernel

theorem rowEval16126 (x : Key → ℝ) : Integer.Sparse.eval row16126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -2, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck16126, Integer.Sparse.eval_collectBalanced, rawRowCheck16126]

def rawRow16127 : Integer.Sparse Key := [(key2445, 4), (key2395, 4), (key2526, 4), (key2410, -2), (key2441, -2), (key2382, -2), (key2507, -2), (key2393, -2), (key2483, -2), (key2410, -2), (key2441, -2), (key2382, -2), (key2507, -2), (key2393, -2), (key2483, -2), (key2407, 4), (key2592, 4), (key2848, 4)]

theorem rawRowCheck16127 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form0 = rawRow16127 := by decide +kernel

def row16127 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4), (key2848, 4)]

theorem rowCheck16127 : row16127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow16127 := by decide +kernel

theorem rowEval16127 (x : Key → ℝ) : Integer.Sparse.eval row16127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, -2, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck16127, Integer.Sparse.eval_collectBalanced, rawRowCheck16127]

end MUB6.Certificate.GramRows

end OAI
