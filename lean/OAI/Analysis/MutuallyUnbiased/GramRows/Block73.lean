import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6272 : Integer.Sparse Key := [(key2867, -1), (key2903, -1), (key2982, 2), (key2723, -1), (key2746, -1), (key2826, 2), (key2903, 2), (key2959, -1), (key2982, -1), (key2723, 2), (key2826, -1), (key2867, -1), (key2857, 1), (key2896, 1), (key2975, -2), (key2637, 1), (key2652, 1), (key2791, -2), (key2896, -2), (key2942, 1), (key2975, 1), (key2637, -2), (key2791, 1), (key2857, 1), (key2806, -1), (key2894, -1), (key2949, 1), (key2973, 1), (key2783, 1), (key2894, 1), (key2937, -1), (key2973, -1), (key2613, -1), (key2647, -1), (key2668, 1), (key2736, 1), (key2613, 1), (key2629, 1), (key2668, -1), (key2703, -1)]

theorem rawRowCheck6272 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form2 = rawRow6272 := by decide +kernel

def row6272 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6272 : row6272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6272 := by decide +kernel

theorem rowEval6272 (x : Key → ℝ) : Integer.Sparse.eval row6272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6272, Integer.Sparse.eval_collectBalanced, rawRowCheck6272]

def rawRow6273 : Integer.Sparse Key := [(key2903, -1), (key2867, -1), (key2982, 2), (key2746, -1), (key2723, -1), (key2903, 2), (key2826, 2), (key2982, -1), (key2959, -1), (key2723, 2), (key2867, -1), (key2826, -1), (key2896, 1), (key2857, 1), (key2975, -2), (key2652, 1), (key2637, 1), (key2896, -2), (key2791, -2), (key2975, 1), (key2942, 1), (key2637, -2), (key2857, 1), (key2791, 1), (key2894, -1), (key2806, -1), (key2973, 1), (key2949, 1), (key2894, 1), (key2783, 1), (key2973, -1), (key2937, -1), (key2647, -1), (key2613, -1), (key2736, 1), (key2668, 1), (key2629, 1), (key2613, 1), (key2703, -1), (key2668, -1)]

theorem rawRowCheck6273 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form2 = rawRow6273 := by decide +kernel

def row6273 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6273 : row6273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6273 := by decide +kernel

theorem rowEval6273 (x : Key → ℝ) : Integer.Sparse.eval row6273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6273, Integer.Sparse.eval_collectBalanced, rawRowCheck6273]

def rawRow6274 : Integer.Sparse Key := [(key2867, -1), (key2982, -1), (key2903, 2), (key2826, -1), (key2959, -1), (key2723, 2), (key2982, 2), (key2746, -1), (key2903, -1), (key2826, 2), (key2723, -1), (key2867, -1), (key2857, 1), (key2975, 1), (key2896, -2), (key2791, 1), (key2942, 1), (key2637, -2), (key2975, -2), (key2652, 1), (key2896, 1), (key2791, -2), (key2637, 1), (key2857, 1), (key2703, -1), (key2973, -1), (key2736, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, -1), (key2894, -1), (key2668, -1), (key2937, -1), (key2613, 1), (key2949, 1), (key2668, 1), (key2783, 1), (key2613, -1), (key2806, -1)]

theorem rawRowCheck6274 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form2 = rawRow6274 := by decide +kernel

def row6274 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6274 : row6274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6274 := by decide +kernel

theorem rowEval6274 (x : Key → ℝ) : Integer.Sparse.eval row6274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck6274, Integer.Sparse.eval_collectBalanced, rawRowCheck6274]

def rawRow6275 : Integer.Sparse Key := [(key2982, -1), (key2867, -1), (key2903, 2), (key2959, -1), (key2826, -1), (key2982, 2), (key2723, 2), (key2903, -1), (key2746, -1), (key2826, 2), (key2867, -1), (key2723, -1), (key2975, 1), (key2857, 1), (key2896, -2), (key2942, 1), (key2791, 1), (key2975, -2), (key2637, -2), (key2896, 1), (key2652, 1), (key2791, -2), (key2857, 1), (key2637, 1), (key2973, -1), (key2703, -1), (key2894, 1), (key2736, 1), (key2973, 1), (key2629, 1), (key2894, -1), (key2647, -1), (key2937, -1), (key2668, -1), (key2949, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, -1), (key2613, -1)]

theorem rawRowCheck6275 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form2 = rawRow6275 := by decide +kernel

def row6275 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

theorem rowCheck6275 : row6275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6275 := by decide +kernel

theorem rowEval6275 (x : Key → ℝ) : Integer.Sparse.eval row6275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6275, Integer.Sparse.eval_collectBalanced, rawRowCheck6275]

def rawRow6276 : Integer.Sparse Key := [(key2903, -1), (key2982, -1), (key2867, 2), (key2903, -1), (key2982, -1), (key2746, 2), (key2959, 2), (key2723, -1), (key2826, -1), (key2867, 2), (key2723, -1), (key2826, -1), (key2896, 1), (key2975, 1), (key2857, -2), (key2896, 1), (key2975, 1), (key2652, -2), (key2942, -2), (key2637, 1), (key2791, 1), (key2857, -2), (key2637, 1), (key2791, 1), (key2736, -1), (key2949, -1), (key2703, 1), (key2806, 1), (key2647, 1), (key2937, 1), (key2629, -1), (key2783, -1), (key2736, -1), (key2949, -1), (key2647, 1), (key2937, 1), (key2703, 1), (key2806, 1), (key2629, -1), (key2783, -1)]

theorem rawRowCheck6276 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form2 = rawRow6276 := by decide +kernel

def row6276 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck6276 : row6276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6276 := by decide +kernel

theorem rowEval6276 (x : Key → ℝ) : Integer.Sparse.eval row6276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck6276, Integer.Sparse.eval_collectBalanced, rawRowCheck6276]

def rawRow6277 : Integer.Sparse Key := [(key2982, -1), (key2903, -1), (key2867, 2), (key2982, -1), (key2903, -1), (key2959, 2), (key2746, 2), (key2826, -1), (key2723, -1), (key2867, 2), (key2826, -1), (key2723, -1), (key2975, 1), (key2896, 1), (key2857, -2), (key2975, 1), (key2896, 1), (key2942, -2), (key2652, -2), (key2791, 1), (key2637, 1), (key2857, -2), (key2791, 1), (key2637, 1), (key2949, -1), (key2736, -1), (key2806, 1), (key2703, 1), (key2937, 1), (key2647, 1), (key2783, -1), (key2629, -1), (key2949, -1), (key2736, -1), (key2937, 1), (key2647, 1), (key2806, 1), (key2703, 1), (key2783, -1), (key2629, -1)]

theorem rawRowCheck6277 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form2 = rawRow6277 := by decide +kernel

def row6277 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

theorem rowCheck6277 : row6277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6277 := by decide +kernel

theorem rowEval6277 (x : Key → ℝ) : Integer.Sparse.eval row6277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck6277, Integer.Sparse.eval_collectBalanced, rawRowCheck6277]

def rawRow6278 : Integer.Sparse Key := [(key1038, -4), (key1038, 2), (key1044, 2), (key1073, 2), (key1080, 2), (key1080, -4), (key1003, 2), (key1003, -1), (key1009, -1), (key1116, 2), (key1116, -1), (key1233, -1), (key1152, -1), (key1159, -1), (key1152, -1), (key1243, -1), (key1159, 2), (key1243, 2), (key1017, -1), (key1022, -1), (key1022, 2), (key1125, -1), (key1130, -1), (key1125, 2), (key1236, 2), (key1130, -1), (key1236, -1), (key1174, 2), (key1174, -1), (key1247, -1)]

theorem rawRowCheck6278 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form3 = rawRow6278 := by decide +kernel

def row6278 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6278 : row6278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6278 := by decide +kernel

theorem rowEval6278 (x : Key → ℝ) : Integer.Sparse.eval row6278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6278, Integer.Sparse.eval_collectBalanced, rawRowCheck6278]

def rawRow6279 : Integer.Sparse Key := [(key1038, -4), (key1044, 2), (key1038, 2), (key1080, 2), (key1073, 2), (key1080, -4), (key1003, 2), (key1009, -1), (key1003, -1), (key1116, 2), (key1233, -1), (key1116, -1), (key1159, -1), (key1152, -1), (key1243, -1), (key1152, -1), (key1243, 2), (key1159, 2), (key1022, -1), (key1017, -1), (key1022, 2), (key1130, -1), (key1125, -1), (key1236, 2), (key1125, 2), (key1236, -1), (key1130, -1), (key1174, 2), (key1247, -1), (key1174, -1)]

theorem rawRowCheck6279 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form3 = rawRow6279 := by decide +kernel

def row6279 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6279 : row6279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6279 := by decide +kernel

theorem rowEval6279 (x : Key → ℝ) : Integer.Sparse.eval row6279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6279, Integer.Sparse.eval_collectBalanced, rawRowCheck6279]

def rawRow6280 : Integer.Sparse Key := [(key1044, -4), (key1038, 2), (key1038, 2), (key1080, 2), (key1080, 2), (key1073, -4), (key1009, 2), (key1003, -1), (key1003, -1), (key1233, 2), (key1116, -1), (key1116, -1), (key1243, -1), (key1243, -1), (key1159, -1), (key1159, -1), (key1152, 2), (key1152, 2), (key1022, -1), (key1022, -1), (key1017, 2), (key1236, -1), (key1236, -1), (key1130, 2), (key1130, 2), (key1125, -1), (key1125, -1), (key1247, 2), (key1174, -1), (key1174, -1)]

theorem rawRowCheck6280 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form3 = rawRow6280 := by decide +kernel

def row6280 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6280 : row6280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6280 := by decide +kernel

theorem rowEval6280 (x : Key → ℝ) : Integer.Sparse.eval row6280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6280, Integer.Sparse.eval_collectBalanced, rawRowCheck6280]

def rawRow6281 : Integer.Sparse Key := [(key1038, -4), (key1073, 2), (key1080, 2), (key1038, 2), (key1044, 2), (key1080, -4), (key1116, 2), (key1152, -1), (key1159, -1), (key1003, 2), (key1152, -1), (key1243, -1), (key1003, -1), (key1009, -1), (key1116, -1), (key1233, -1), (key1159, 2), (key1243, 2), (key1125, -1), (key1130, -1), (key1174, 2), (key1017, -1), (key1022, -1), (key1125, 2), (key1236, 2), (key1174, -1), (key1247, -1), (key1022, 2), (key1130, -1), (key1236, -1)]

theorem rawRowCheck6281 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form3 = rawRow6281 := by decide +kernel

def row6281 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6281 : row6281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6281 := by decide +kernel

theorem rowEval6281 (x : Key → ℝ) : Integer.Sparse.eval row6281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6281, Integer.Sparse.eval_collectBalanced, rawRowCheck6281]

def rawRow6282 : Integer.Sparse Key := [(key1038, -4), (key1080, 2), (key1073, 2), (key1044, 2), (key1038, 2), (key1080, -4), (key1116, 2), (key1159, -1), (key1152, -1), (key1003, 2), (key1243, -1), (key1152, -1), (key1009, -1), (key1003, -1), (key1233, -1), (key1116, -1), (key1243, 2), (key1159, 2), (key1130, -1), (key1125, -1), (key1174, 2), (key1022, -1), (key1017, -1), (key1236, 2), (key1125, 2), (key1247, -1), (key1174, -1), (key1022, 2), (key1236, -1), (key1130, -1)]

theorem rawRowCheck6282 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form3 = rawRow6282 := by decide +kernel

def row6282 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6282 : row6282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6282 := by decide +kernel

theorem rowEval6282 (x : Key → ℝ) : Integer.Sparse.eval row6282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6282, Integer.Sparse.eval_collectBalanced, rawRowCheck6282]

def rawRow6283 : Integer.Sparse Key := [(key1073, -4), (key1038, 2), (key1080, 2), (key1038, 2), (key1080, 2), (key1044, -4), (key1152, 2), (key1116, -1), (key1159, -1), (key1152, 2), (key1003, -1), (key1243, -1), (key1116, -1), (key1159, -1), (key1003, -1), (key1243, -1), (key1009, 2), (key1233, 2), (key1125, -1), (key1174, -1), (key1130, 2), (key1125, -1), (key1174, -1), (key1017, 2), (key1247, 2), (key1022, -1), (key1236, -1), (key1130, 2), (key1022, -1), (key1236, -1)]

theorem rawRowCheck6283 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form3 = rawRow6283 := by decide +kernel

def row6283 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6283 : row6283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6283 := by decide +kernel

theorem rowEval6283 (x : Key → ℝ) : Integer.Sparse.eval row6283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6283, Integer.Sparse.eval_collectBalanced, rawRowCheck6283]

def rawRow6284 : Integer.Sparse Key := [(key1073, -4), (key1080, 2), (key1038, 2), (key1080, 2), (key1038, 2), (key1044, -4), (key1152, 2), (key1159, -1), (key1116, -1), (key1152, 2), (key1243, -1), (key1003, -1), (key1159, -1), (key1116, -1), (key1243, -1), (key1003, -1), (key1233, 2), (key1009, 2), (key1174, -1), (key1125, -1), (key1130, 2), (key1174, -1), (key1125, -1), (key1247, 2), (key1017, 2), (key1236, -1), (key1022, -1), (key1130, 2), (key1236, -1), (key1022, -1)]

theorem rawRowCheck6284 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form3 = rawRow6284 := by decide +kernel

def row6284 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6284 : row6284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6284 := by decide +kernel

theorem rowEval6284 (x : Key → ℝ) : Integer.Sparse.eval row6284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6284, Integer.Sparse.eval_collectBalanced, rawRowCheck6284]

def rawRow6285 : Integer.Sparse Key := [(key1080, -4), (key1038, 2), (key1073, 2), (key1044, 2), (key1080, 2), (key1038, -4), (key1159, 2), (key1116, -1), (key1152, -1), (key1243, 2), (key1003, -1), (key1152, -1), (key1233, -1), (key1243, -1), (key1009, -1), (key1159, -1), (key1003, 2), (key1116, 2), (key1130, -1), (key1174, -1), (key1125, 2), (key1236, -1), (key1247, -1), (key1022, 2), (key1174, 2), (key1017, -1), (key1125, -1), (key1236, 2), (key1022, -1), (key1130, -1)]

theorem rawRowCheck6285 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form3 = rawRow6285 := by decide +kernel

def row6285 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6285 : row6285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6285 := by decide +kernel

theorem rowEval6285 (x : Key → ℝ) : Integer.Sparse.eval row6285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6285, Integer.Sparse.eval_collectBalanced, rawRowCheck6285]

def rawRow6286 : Integer.Sparse Key := [(key1080, -4), (key1073, 2), (key1038, 2), (key1080, 2), (key1044, 2), (key1038, -4), (key1159, 2), (key1152, -1), (key1116, -1), (key1243, 2), (key1152, -1), (key1003, -1), (key1243, -1), (key1233, -1), (key1159, -1), (key1009, -1), (key1116, 2), (key1003, 2), (key1174, -1), (key1130, -1), (key1125, 2), (key1247, -1), (key1236, -1), (key1174, 2), (key1022, 2), (key1125, -1), (key1017, -1), (key1236, 2), (key1130, -1), (key1022, -1)]

theorem rawRowCheck6286 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form3 = rawRow6286 := by decide +kernel

def row6286 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6286 : row6286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6286 := by decide +kernel

theorem rowEval6286 (x : Key → ℝ) : Integer.Sparse.eval row6286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6286, Integer.Sparse.eval_collectBalanced, rawRowCheck6286]

def rawRow6287 : Integer.Sparse Key := [(key1044, -4), (key1080, 2), (key1080, 2), (key1038, 2), (key1038, 2), (key1073, -4), (key1233, 2), (key1243, -1), (key1243, -1), (key1009, 2), (key1159, -1), (key1159, -1), (key1003, -1), (key1003, -1), (key1116, -1), (key1116, -1), (key1152, 2), (key1152, 2), (key1236, -1), (key1236, -1), (key1247, 2), (key1022, -1), (key1022, -1), (key1130, 2), (key1130, 2), (key1174, -1), (key1174, -1), (key1017, 2), (key1125, -1), (key1125, -1)]

theorem rawRowCheck6287 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form3 = rawRow6287 := by decide +kernel

def row6287 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, 4), (key1044, -4), (key1073, -4), (key1080, 4), (key1116, -2), (key1125, -2), (key1130, 4), (key1152, 4), (key1159, -2), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6287 : row6287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6287 := by decide +kernel

theorem rowEval6287 (x : Key → ℝ) : Integer.Sparse.eval row6287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6287, Integer.Sparse.eval_collectBalanced, rawRowCheck6287]

def rawRow6288 : Integer.Sparse Key := [(key1080, -4), (key1044, 2), (key1080, 2), (key1038, 2), (key1073, 2), (key1038, -4), (key1243, 2), (key1233, -1), (key1243, -1), (key1159, 2), (key1009, -1), (key1159, -1), (key1116, -1), (key1152, -1), (key1003, -1), (key1152, -1), (key1003, 2), (key1116, 2), (key1236, -1), (key1247, -1), (key1236, 2), (key1130, -1), (key1174, -1), (key1022, 2), (key1174, 2), (key1022, -1), (key1130, -1), (key1125, 2), (key1017, -1), (key1125, -1)]

theorem rawRowCheck6288 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form3 = rawRow6288 := by decide +kernel

def row6288 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6288 : row6288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6288 := by decide +kernel

theorem rowEval6288 (x : Key → ℝ) : Integer.Sparse.eval row6288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6288, Integer.Sparse.eval_collectBalanced, rawRowCheck6288]

def rawRow6289 : Integer.Sparse Key := [(key1080, -4), (key1080, 2), (key1044, 2), (key1073, 2), (key1038, 2), (key1038, -4), (key1243, 2), (key1243, -1), (key1233, -1), (key1159, 2), (key1159, -1), (key1009, -1), (key1152, -1), (key1116, -1), (key1152, -1), (key1003, -1), (key1116, 2), (key1003, 2), (key1247, -1), (key1236, -1), (key1236, 2), (key1174, -1), (key1130, -1), (key1174, 2), (key1022, 2), (key1130, -1), (key1022, -1), (key1125, 2), (key1125, -1), (key1017, -1)]

theorem rawRowCheck6289 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form3 = rawRow6289 := by decide +kernel

def row6289 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6289 : row6289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6289 := by decide +kernel

theorem rowEval6289 (x : Key → ℝ) : Integer.Sparse.eval row6289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6289, Integer.Sparse.eval_collectBalanced, rawRowCheck6289]

def rawRow6290 : Integer.Sparse Key := [(key1116, -4), (key1125, 2), (key1130, 2), (key1152, 2), (key1159, 2), (key1174, -4), (key1003, 2), (key1017, -1), (key1022, -1), (key1038, 2), (key1125, -1), (key1236, -1), (key1073, -1), (key1080, -1), (key1152, -1), (key1243, -1), (key1174, 2), (key1247, 2), (key1003, -1), (key1009, -1), (key1022, 2), (key1038, -1), (key1044, -1), (key1116, 2), (key1233, 2), (key1130, -1), (key1236, -1), (key1080, 2), (key1159, -1), (key1243, -1)]

theorem rawRowCheck6290 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form3 = rawRow6290 := by decide +kernel

def row6290 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6290 : row6290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6290 := by decide +kernel

theorem rowEval6290 (x : Key → ℝ) : Integer.Sparse.eval row6290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6290, Integer.Sparse.eval_collectBalanced, rawRowCheck6290]

def rawRow6291 : Integer.Sparse Key := [(key1116, -4), (key1130, 2), (key1125, 2), (key1159, 2), (key1152, 2), (key1174, -4), (key1003, 2), (key1022, -1), (key1017, -1), (key1038, 2), (key1236, -1), (key1125, -1), (key1080, -1), (key1073, -1), (key1243, -1), (key1152, -1), (key1247, 2), (key1174, 2), (key1009, -1), (key1003, -1), (key1022, 2), (key1044, -1), (key1038, -1), (key1233, 2), (key1116, 2), (key1236, -1), (key1130, -1), (key1080, 2), (key1243, -1), (key1159, -1)]

theorem rawRowCheck6291 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form3 = rawRow6291 := by decide +kernel

def row6291 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6291 : row6291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6291 := by decide +kernel

theorem rowEval6291 (x : Key → ℝ) : Integer.Sparse.eval row6291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6291, Integer.Sparse.eval_collectBalanced, rawRowCheck6291]

def rawRow6292 : Integer.Sparse Key := [(key1130, -4), (key1116, 2), (key1125, 2), (key1159, 2), (key1174, 2), (key1152, -4), (key1022, 2), (key1003, -1), (key1017, -1), (key1236, 2), (key1038, -1), (key1125, -1), (key1243, -1), (key1247, -1), (key1080, -1), (key1174, -1), (key1073, 2), (key1152, 2), (key1009, -1), (key1022, -1), (key1003, 2), (key1233, -1), (key1236, -1), (key1044, 2), (key1130, 2), (key1038, -1), (key1116, -1), (key1243, 2), (key1080, -1), (key1159, -1)]

theorem rawRowCheck6292 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form3 = rawRow6292 := by decide +kernel

def row6292 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6292 : row6292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6292 := by decide +kernel

theorem rowEval6292 (x : Key → ℝ) : Integer.Sparse.eval row6292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6292, Integer.Sparse.eval_collectBalanced, rawRowCheck6292]

def rawRow6293 : Integer.Sparse Key := [(key1130, -4), (key1125, 2), (key1116, 2), (key1174, 2), (key1159, 2), (key1152, -4), (key1022, 2), (key1017, -1), (key1003, -1), (key1236, 2), (key1125, -1), (key1038, -1), (key1247, -1), (key1243, -1), (key1174, -1), (key1080, -1), (key1152, 2), (key1073, 2), (key1022, -1), (key1009, -1), (key1003, 2), (key1236, -1), (key1233, -1), (key1130, 2), (key1044, 2), (key1116, -1), (key1038, -1), (key1243, 2), (key1159, -1), (key1080, -1)]

theorem rawRowCheck6293 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form3 = rawRow6293 := by decide +kernel

def row6293 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6293 : row6293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6293 := by decide +kernel

theorem rowEval6293 (x : Key → ℝ) : Integer.Sparse.eval row6293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6293, Integer.Sparse.eval_collectBalanced, rawRowCheck6293]

def rawRow6294 : Integer.Sparse Key := [(key1116, -4), (key1152, 2), (key1159, 2), (key1125, 2), (key1130, 2), (key1174, -4), (key1038, 2), (key1073, -1), (key1080, -1), (key1003, 2), (key1152, -1), (key1243, -1), (key1017, -1), (key1022, -1), (key1125, -1), (key1236, -1), (key1174, 2), (key1247, 2), (key1038, -1), (key1044, -1), (key1080, 2), (key1003, -1), (key1009, -1), (key1116, 2), (key1233, 2), (key1159, -1), (key1243, -1), (key1022, 2), (key1130, -1), (key1236, -1)]

theorem rawRowCheck6294 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form3 = rawRow6294 := by decide +kernel

def row6294 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6294 : row6294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6294 := by decide +kernel

theorem rowEval6294 (x : Key → ℝ) : Integer.Sparse.eval row6294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6294, Integer.Sparse.eval_collectBalanced, rawRowCheck6294]

def rawRow6295 : Integer.Sparse Key := [(key1116, -4), (key1159, 2), (key1152, 2), (key1130, 2), (key1125, 2), (key1174, -4), (key1038, 2), (key1080, -1), (key1073, -1), (key1003, 2), (key1243, -1), (key1152, -1), (key1022, -1), (key1017, -1), (key1236, -1), (key1125, -1), (key1247, 2), (key1174, 2), (key1044, -1), (key1038, -1), (key1080, 2), (key1009, -1), (key1003, -1), (key1233, 2), (key1116, 2), (key1243, -1), (key1159, -1), (key1022, 2), (key1236, -1), (key1130, -1)]

theorem rawRowCheck6295 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form3 = rawRow6295 := by decide +kernel

def row6295 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6295 : row6295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6295 := by decide +kernel

theorem rowEval6295 (x : Key → ℝ) : Integer.Sparse.eval row6295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6295, Integer.Sparse.eval_collectBalanced, rawRowCheck6295]

def rawRow6296 : Integer.Sparse Key := [(key1152, -4), (key1116, 2), (key1159, 2), (key1125, 2), (key1174, 2), (key1130, -4), (key1073, 2), (key1038, -1), (key1080, -1), (key1152, 2), (key1003, -1), (key1243, -1), (key1125, -1), (key1174, -1), (key1017, -1), (key1247, -1), (key1022, 2), (key1236, 2), (key1038, -1), (key1080, -1), (key1044, 2), (key1116, -1), (key1159, -1), (key1003, 2), (key1243, 2), (key1009, -1), (key1233, -1), (key1130, 2), (key1022, -1), (key1236, -1)]

theorem rawRowCheck6296 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form3 = rawRow6296 := by decide +kernel

def row6296 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6296 : row6296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6296 := by decide +kernel

theorem rowEval6296 (x : Key → ℝ) : Integer.Sparse.eval row6296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6296, Integer.Sparse.eval_collectBalanced, rawRowCheck6296]

def rawRow6297 : Integer.Sparse Key := [(key1152, -4), (key1159, 2), (key1116, 2), (key1174, 2), (key1125, 2), (key1130, -4), (key1073, 2), (key1080, -1), (key1038, -1), (key1152, 2), (key1243, -1), (key1003, -1), (key1174, -1), (key1125, -1), (key1247, -1), (key1017, -1), (key1236, 2), (key1022, 2), (key1080, -1), (key1038, -1), (key1044, 2), (key1159, -1), (key1116, -1), (key1243, 2), (key1003, 2), (key1233, -1), (key1009, -1), (key1130, 2), (key1236, -1), (key1022, -1)]

theorem rawRowCheck6297 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form3 = rawRow6297 := by decide +kernel

def row6297 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6297 : row6297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6297 := by decide +kernel

theorem rowEval6297 (x : Key → ℝ) : Integer.Sparse.eval row6297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6297, Integer.Sparse.eval_collectBalanced, rawRowCheck6297]

def rawRow6298 : Integer.Sparse Key := [(key1152, -4), (key1125, 2), (key1174, 2), (key1116, 2), (key1159, 2), (key1130, -4), (key1152, 2), (key1125, -1), (key1174, -1), (key1073, 2), (key1017, -1), (key1247, -1), (key1038, -1), (key1080, -1), (key1003, -1), (key1243, -1), (key1022, 2), (key1236, 2), (key1116, -1), (key1159, -1), (key1130, 2), (key1038, -1), (key1080, -1), (key1003, 2), (key1243, 2), (key1022, -1), (key1236, -1), (key1044, 2), (key1009, -1), (key1233, -1)]

theorem rawRowCheck6298 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form3 = rawRow6298 := by decide +kernel

def row6298 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6298 : row6298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6298 := by decide +kernel

theorem rowEval6298 (x : Key → ℝ) : Integer.Sparse.eval row6298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6298, Integer.Sparse.eval_collectBalanced, rawRowCheck6298]

def rawRow6299 : Integer.Sparse Key := [(key1152, -4), (key1174, 2), (key1125, 2), (key1159, 2), (key1116, 2), (key1130, -4), (key1152, 2), (key1174, -1), (key1125, -1), (key1073, 2), (key1247, -1), (key1017, -1), (key1080, -1), (key1038, -1), (key1243, -1), (key1003, -1), (key1236, 2), (key1022, 2), (key1159, -1), (key1116, -1), (key1130, 2), (key1080, -1), (key1038, -1), (key1243, 2), (key1003, 2), (key1236, -1), (key1022, -1), (key1044, 2), (key1233, -1), (key1009, -1)]

theorem rawRowCheck6299 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form3 = rawRow6299 := by decide +kernel

def row6299 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6299 : row6299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6299 := by decide +kernel

theorem rowEval6299 (x : Key → ℝ) : Integer.Sparse.eval row6299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6299, Integer.Sparse.eval_collectBalanced, rawRowCheck6299]

def rawRow6300 : Integer.Sparse Key := [(key1174, -4), (key1125, 2), (key1152, 2), (key1130, 2), (key1159, 2), (key1116, -4), (key1174, 2), (key1125, -1), (key1152, -1), (key1247, 2), (key1017, -1), (key1073, -1), (key1236, -1), (key1243, -1), (key1022, -1), (key1080, -1), (key1003, 2), (key1038, 2), (key1130, -1), (key1159, -1), (key1116, 2), (key1236, -1), (key1243, -1), (key1022, 2), (key1080, 2), (key1003, -1), (key1038, -1), (key1233, 2), (key1009, -1), (key1044, -1)]

theorem rawRowCheck6300 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form3 = rawRow6300 := by decide +kernel

def row6300 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6300 : row6300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6300 := by decide +kernel

theorem rowEval6300 (x : Key → ℝ) : Integer.Sparse.eval row6300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6300, Integer.Sparse.eval_collectBalanced, rawRowCheck6300]

def rawRow6301 : Integer.Sparse Key := [(key1174, -4), (key1152, 2), (key1125, 2), (key1159, 2), (key1130, 2), (key1116, -4), (key1174, 2), (key1152, -1), (key1125, -1), (key1247, 2), (key1073, -1), (key1017, -1), (key1243, -1), (key1236, -1), (key1080, -1), (key1022, -1), (key1038, 2), (key1003, 2), (key1159, -1), (key1130, -1), (key1116, 2), (key1243, -1), (key1236, -1), (key1080, 2), (key1022, 2), (key1038, -1), (key1003, -1), (key1233, 2), (key1044, -1), (key1009, -1)]

theorem rawRowCheck6301 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form3 = rawRow6301 := by decide +kernel

def row6301 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6301 : row6301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6301 := by decide +kernel

theorem rowEval6301 (x : Key → ℝ) : Integer.Sparse.eval row6301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6301, Integer.Sparse.eval_collectBalanced, rawRowCheck6301]

def rawRow6302 : Integer.Sparse Key := [(key1130, -4), (key1159, 2), (key1174, 2), (key1116, 2), (key1125, 2), (key1152, -4), (key1236, 2), (key1243, -1), (key1247, -1), (key1022, 2), (key1080, -1), (key1174, -1), (key1003, -1), (key1017, -1), (key1038, -1), (key1125, -1), (key1073, 2), (key1152, 2), (key1233, -1), (key1236, -1), (key1243, 2), (key1009, -1), (key1022, -1), (key1044, 2), (key1130, 2), (key1080, -1), (key1159, -1), (key1003, 2), (key1038, -1), (key1116, -1)]

theorem rawRowCheck6302 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form3 = rawRow6302 := by decide +kernel

def row6302 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6302 : row6302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6302 := by decide +kernel

theorem rowEval6302 (x : Key → ℝ) : Integer.Sparse.eval row6302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6302, Integer.Sparse.eval_collectBalanced, rawRowCheck6302]

def rawRow6303 : Integer.Sparse Key := [(key1130, -4), (key1174, 2), (key1159, 2), (key1125, 2), (key1116, 2), (key1152, -4), (key1236, 2), (key1247, -1), (key1243, -1), (key1022, 2), (key1174, -1), (key1080, -1), (key1017, -1), (key1003, -1), (key1125, -1), (key1038, -1), (key1152, 2), (key1073, 2), (key1236, -1), (key1233, -1), (key1243, 2), (key1022, -1), (key1009, -1), (key1130, 2), (key1044, 2), (key1159, -1), (key1080, -1), (key1003, 2), (key1116, -1), (key1038, -1)]

theorem rawRowCheck6303 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form3 = rawRow6303 := by decide +kernel

def row6303 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 1), (key1125, 1), (key1130, -2), (key1152, -2), (key1159, 1), (key1174, 1), (key1233, -1), (key1236, 1), (key1243, 1), (key1247, -1)]

theorem rowCheck6303 : row6303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6303 := by decide +kernel

theorem rowEval6303 (x : Key → ℝ) : Integer.Sparse.eval row6303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6303, Integer.Sparse.eval_collectBalanced, rawRowCheck6303]

def rawRow6304 : Integer.Sparse Key := [(key1174, -4), (key1130, 2), (key1159, 2), (key1125, 2), (key1152, 2), (key1116, -4), (key1247, 2), (key1236, -1), (key1243, -1), (key1174, 2), (key1022, -1), (key1080, -1), (key1125, -1), (key1152, -1), (key1017, -1), (key1073, -1), (key1003, 2), (key1038, 2), (key1236, -1), (key1243, -1), (key1233, 2), (key1130, -1), (key1159, -1), (key1022, 2), (key1080, 2), (key1009, -1), (key1044, -1), (key1116, 2), (key1003, -1), (key1038, -1)]

theorem rawRowCheck6304 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form3 = rawRow6304 := by decide +kernel

def row6304 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6304 : row6304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6304 := by decide +kernel

theorem rowEval6304 (x : Key → ℝ) : Integer.Sparse.eval row6304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6304, Integer.Sparse.eval_collectBalanced, rawRowCheck6304]

def rawRow6305 : Integer.Sparse Key := [(key1174, -4), (key1159, 2), (key1130, 2), (key1152, 2), (key1125, 2), (key1116, -4), (key1247, 2), (key1243, -1), (key1236, -1), (key1174, 2), (key1080, -1), (key1022, -1), (key1152, -1), (key1125, -1), (key1073, -1), (key1017, -1), (key1038, 2), (key1003, 2), (key1243, -1), (key1236, -1), (key1233, 2), (key1159, -1), (key1130, -1), (key1080, 2), (key1022, 2), (key1044, -1), (key1009, -1), (key1116, 2), (key1038, -1), (key1003, -1)]

theorem rawRowCheck6305 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form3 = rawRow6305 := by decide +kernel

def row6305 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6305 : row6305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6305 := by decide +kernel

theorem rowEval6305 (x : Key → ℝ) : Integer.Sparse.eval row6305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6305, Integer.Sparse.eval_collectBalanced, rawRowCheck6305]

def rawRow6306 : Integer.Sparse Key := [(key1233, -4), (key1236, 2), (key1236, 2), (key1243, 2), (key1243, 2), (key1247, -4), (key1009, 2), (key1022, -1), (key1022, -1), (key1044, 2), (key1130, -1), (key1130, -1), (key1080, -1), (key1080, -1), (key1159, -1), (key1159, -1), (key1174, 2), (key1174, 2), (key1003, -1), (key1003, -1), (key1017, 2), (key1038, -1), (key1038, -1), (key1116, 2), (key1116, 2), (key1125, -1), (key1125, -1), (key1073, 2), (key1152, -1), (key1152, -1)]

theorem rawRowCheck6306 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form3 = rawRow6306 := by decide +kernel

def row6306 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

theorem rowCheck6306 : row6306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6306 := by decide +kernel

theorem rowEval6306 (x : Key → ℝ) : Integer.Sparse.eval row6306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6306, Integer.Sparse.eval_collectBalanced, rawRowCheck6306]

def rawRow6307 : Integer.Sparse Key := [(key1236, -4), (key1233, 2), (key1236, 2), (key1243, 2), (key1247, 2), (key1243, -4), (key1022, 2), (key1009, -1), (key1022, -1), (key1130, 2), (key1044, -1), (key1130, -1), (key1159, -1), (key1174, -1), (key1080, -1), (key1174, -1), (key1080, 2), (key1159, 2), (key1003, -1), (key1017, -1), (key1003, 2), (key1116, -1), (key1125, -1), (key1038, 2), (key1125, 2), (key1038, -1), (key1116, -1), (key1152, 2), (key1073, -1), (key1152, -1)]

theorem rawRowCheck6307 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form3 = rawRow6307 := by decide +kernel

def row6307 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6307 : row6307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6307 := by decide +kernel

theorem rowEval6307 (x : Key → ℝ) : Integer.Sparse.eval row6307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6307, Integer.Sparse.eval_collectBalanced, rawRowCheck6307]

def rawRow6308 : Integer.Sparse Key := [(key1236, -4), (key1236, 2), (key1233, 2), (key1247, 2), (key1243, 2), (key1243, -4), (key1022, 2), (key1022, -1), (key1009, -1), (key1130, 2), (key1130, -1), (key1044, -1), (key1174, -1), (key1159, -1), (key1174, -1), (key1080, -1), (key1159, 2), (key1080, 2), (key1017, -1), (key1003, -1), (key1003, 2), (key1125, -1), (key1116, -1), (key1125, 2), (key1038, 2), (key1116, -1), (key1038, -1), (key1152, 2), (key1152, -1), (key1073, -1)]

theorem rawRowCheck6308 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form3 = rawRow6308 := by decide +kernel

def row6308 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6308 : row6308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6308 := by decide +kernel

theorem rowEval6308 (x : Key → ℝ) : Integer.Sparse.eval row6308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6308, Integer.Sparse.eval_collectBalanced, rawRowCheck6308]

def rawRow6309 : Integer.Sparse Key := [(key1233, -4), (key1243, 2), (key1243, 2), (key1236, 2), (key1236, 2), (key1247, -4), (key1044, 2), (key1080, -1), (key1080, -1), (key1009, 2), (key1159, -1), (key1159, -1), (key1022, -1), (key1022, -1), (key1130, -1), (key1130, -1), (key1174, 2), (key1174, 2), (key1038, -1), (key1038, -1), (key1073, 2), (key1003, -1), (key1003, -1), (key1116, 2), (key1116, 2), (key1152, -1), (key1152, -1), (key1017, 2), (key1125, -1), (key1125, -1)]

theorem rawRowCheck6309 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form3 = rawRow6309 := by decide +kernel

def row6309 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

theorem rowCheck6309 : row6309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6309 := by decide +kernel

theorem rowEval6309 (x : Key → ℝ) : Integer.Sparse.eval row6309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6309, Integer.Sparse.eval_collectBalanced, rawRowCheck6309]

def rawRow6310 : Integer.Sparse Key := [(key1243, -4), (key1233, 2), (key1243, 2), (key1236, 2), (key1247, 2), (key1236, -4), (key1080, 2), (key1044, -1), (key1080, -1), (key1159, 2), (key1009, -1), (key1159, -1), (key1130, -1), (key1174, -1), (key1022, -1), (key1174, -1), (key1022, 2), (key1130, 2), (key1038, -1), (key1073, -1), (key1038, 2), (key1116, -1), (key1152, -1), (key1003, 2), (key1152, 2), (key1003, -1), (key1116, -1), (key1125, 2), (key1017, -1), (key1125, -1)]

theorem rawRowCheck6310 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form3 = rawRow6310 := by decide +kernel

def row6310 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6310 : row6310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6310 := by decide +kernel

theorem rowEval6310 (x : Key → ℝ) : Integer.Sparse.eval row6310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6310, Integer.Sparse.eval_collectBalanced, rawRowCheck6310]

def rawRow6311 : Integer.Sparse Key := [(key1243, -4), (key1243, 2), (key1233, 2), (key1247, 2), (key1236, 2), (key1236, -4), (key1080, 2), (key1080, -1), (key1044, -1), (key1159, 2), (key1159, -1), (key1009, -1), (key1174, -1), (key1130, -1), (key1174, -1), (key1022, -1), (key1130, 2), (key1022, 2), (key1073, -1), (key1038, -1), (key1038, 2), (key1152, -1), (key1116, -1), (key1152, 2), (key1003, 2), (key1116, -1), (key1003, -1), (key1125, 2), (key1125, -1), (key1017, -1)]

theorem rawRowCheck6311 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form3 = rawRow6311 := by decide +kernel

def row6311 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6311 : row6311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6311 := by decide +kernel

theorem rowEval6311 (x : Key → ℝ) : Integer.Sparse.eval row6311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6311, Integer.Sparse.eval_collectBalanced, rawRowCheck6311]

def rawRow6312 : Integer.Sparse Key := [(key1236, -4), (key1243, 2), (key1247, 2), (key1233, 2), (key1236, 2), (key1243, -4), (key1130, 2), (key1159, -1), (key1174, -1), (key1022, 2), (key1080, -1), (key1174, -1), (key1009, -1), (key1022, -1), (key1044, -1), (key1130, -1), (key1080, 2), (key1159, 2), (key1116, -1), (key1125, -1), (key1152, 2), (key1003, -1), (key1017, -1), (key1038, 2), (key1125, 2), (key1073, -1), (key1152, -1), (key1003, 2), (key1038, -1), (key1116, -1)]

theorem rawRowCheck6312 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form3 = rawRow6312 := by decide +kernel

def row6312 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6312 : row6312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6312 := by decide +kernel

theorem rowEval6312 (x : Key → ℝ) : Integer.Sparse.eval row6312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6312, Integer.Sparse.eval_collectBalanced, rawRowCheck6312]

def rawRow6313 : Integer.Sparse Key := [(key1236, -4), (key1247, 2), (key1243, 2), (key1236, 2), (key1233, 2), (key1243, -4), (key1130, 2), (key1174, -1), (key1159, -1), (key1022, 2), (key1174, -1), (key1080, -1), (key1022, -1), (key1009, -1), (key1130, -1), (key1044, -1), (key1159, 2), (key1080, 2), (key1125, -1), (key1116, -1), (key1152, 2), (key1017, -1), (key1003, -1), (key1125, 2), (key1038, 2), (key1152, -1), (key1073, -1), (key1003, 2), (key1116, -1), (key1038, -1)]

theorem rawRowCheck6313 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form3 = rawRow6313 := by decide +kernel

def row6313 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6313 : row6313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6313 := by decide +kernel

theorem rowEval6313 (x : Key → ℝ) : Integer.Sparse.eval row6313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6313, Integer.Sparse.eval_collectBalanced, rawRowCheck6313]

def rawRow6314 : Integer.Sparse Key := [(key1243, -4), (key1236, 2), (key1247, 2), (key1233, 2), (key1243, 2), (key1236, -4), (key1159, 2), (key1130, -1), (key1174, -1), (key1080, 2), (key1022, -1), (key1174, -1), (key1044, -1), (key1080, -1), (key1009, -1), (key1159, -1), (key1022, 2), (key1130, 2), (key1116, -1), (key1152, -1), (key1125, 2), (key1038, -1), (key1073, -1), (key1003, 2), (key1152, 2), (key1017, -1), (key1125, -1), (key1038, 2), (key1003, -1), (key1116, -1)]

theorem rawRowCheck6314 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form3 = rawRow6314 := by decide +kernel

def row6314 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6314 : row6314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6314 := by decide +kernel

theorem rowEval6314 (x : Key → ℝ) : Integer.Sparse.eval row6314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck6314, Integer.Sparse.eval_collectBalanced, rawRowCheck6314]

def rawRow6315 : Integer.Sparse Key := [(key1243, -4), (key1247, 2), (key1236, 2), (key1243, 2), (key1233, 2), (key1236, -4), (key1159, 2), (key1174, -1), (key1130, -1), (key1080, 2), (key1174, -1), (key1022, -1), (key1080, -1), (key1044, -1), (key1159, -1), (key1009, -1), (key1130, 2), (key1022, 2), (key1152, -1), (key1116, -1), (key1125, 2), (key1073, -1), (key1038, -1), (key1152, 2), (key1003, 2), (key1125, -1), (key1017, -1), (key1038, 2), (key1116, -1), (key1003, -1)]

theorem rawRowCheck6315 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form3 = rawRow6315 := by decide +kernel

def row6315 : Integer.Sparse Key := [(key1003, 1), (key1009, -1), (key1017, -1), (key1022, 1), (key1038, 1), (key1044, -1), (key1073, -1), (key1080, 1), (key1116, -2), (key1125, 1), (key1130, 1), (key1152, 1), (key1159, 1), (key1174, -2), (key1233, 2), (key1236, -2), (key1243, -2), (key1247, 2)]

theorem rowCheck6315 : row6315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6315 := by decide +kernel

theorem rowEval6315 (x : Key → ℝ) : Integer.Sparse.eval row6315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6315, Integer.Sparse.eval_collectBalanced, rawRowCheck6315]

def rawRow6316 : Integer.Sparse Key := [(key1247, -4), (key1236, 2), (key1243, 2), (key1236, 2), (key1243, 2), (key1233, -4), (key1174, 2), (key1130, -1), (key1159, -1), (key1174, 2), (key1022, -1), (key1080, -1), (key1130, -1), (key1159, -1), (key1022, -1), (key1080, -1), (key1009, 2), (key1044, 2), (key1125, -1), (key1152, -1), (key1116, 2), (key1125, -1), (key1152, -1), (key1017, 2), (key1073, 2), (key1003, -1), (key1038, -1), (key1116, 2), (key1003, -1), (key1038, -1)]

theorem rawRowCheck6316 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form3 = rawRow6316 := by decide +kernel

def row6316 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

theorem rowCheck6316 : row6316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6316 := by decide +kernel

theorem rowEval6316 (x : Key → ℝ) : Integer.Sparse.eval row6316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck6316, Integer.Sparse.eval_collectBalanced, rawRowCheck6316]

def rawRow6317 : Integer.Sparse Key := [(key1247, -4), (key1243, 2), (key1236, 2), (key1243, 2), (key1236, 2), (key1233, -4), (key1174, 2), (key1159, -1), (key1130, -1), (key1174, 2), (key1080, -1), (key1022, -1), (key1159, -1), (key1130, -1), (key1080, -1), (key1022, -1), (key1044, 2), (key1009, 2), (key1152, -1), (key1125, -1), (key1116, 2), (key1152, -1), (key1125, -1), (key1073, 2), (key1017, 2), (key1038, -1), (key1003, -1), (key1116, 2), (key1038, -1), (key1003, -1)]

theorem rawRowCheck6317 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form3 = rawRow6317 := by decide +kernel

def row6317 : Integer.Sparse Key := [(key1003, -2), (key1009, 2), (key1017, 2), (key1022, -2), (key1038, -2), (key1044, 2), (key1073, 2), (key1080, -2), (key1116, 4), (key1125, -2), (key1130, -2), (key1152, -2), (key1159, -2), (key1174, 4), (key1233, -4), (key1236, 4), (key1243, 4), (key1247, -4)]

theorem rowCheck6317 : row6317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6317 := by decide +kernel

theorem rowEval6317 (x : Key → ℝ) : Integer.Sparse.eval row6317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form3) x := by
  rw [rowCheck6317, Integer.Sparse.eval_collectBalanced, rawRowCheck6317]

def rawRow6318 : Integer.Sparse Key := [(key2406, -4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 2), (key2443, -4), (key2587, 2), (key2587, -1), (key2593, -1), (key2843, 2), (key2843, -1), (key2880, -1), (key2966, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2968, 2), (key2989, 2), (key2598, -1), (key2600, -1), (key2600, 2), (key2887, -1), (key2889, -1), (key2887, 2), (key2910, 2), (key2889, -1), (key2910, -1), (key2995, 2), (key2995, -1), (key3002, -1)]

theorem rawRowCheck6318 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form4 = rawRow6318 := by decide +kernel

def row6318 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6318 : row6318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6318 := by decide +kernel

theorem rowEval6318 (x : Key → ℝ) : Integer.Sparse.eval row6318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6318, Integer.Sparse.eval_collectBalanced, rawRowCheck6318]

def rawRow6319 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2443, -4), (key2587, 2), (key2593, -1), (key2587, -1), (key2843, 2), (key2880, -1), (key2843, -1), (key2968, -1), (key2966, -1), (key2989, -1), (key2966, -1), (key2989, 2), (key2968, 2), (key2600, -1), (key2598, -1), (key2600, 2), (key2889, -1), (key2887, -1), (key2910, 2), (key2887, 2), (key2910, -1), (key2889, -1), (key2995, 2), (key3002, -1), (key2995, -1)]

theorem rawRowCheck6319 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form4 = rawRow6319 := by decide +kernel

def row6319 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6319 : row6319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6319 := by decide +kernel

theorem rowEval6319 (x : Key → ℝ) : Integer.Sparse.eval row6319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6319, Integer.Sparse.eval_collectBalanced, rawRowCheck6319]

def rawRow6320 : Integer.Sparse Key := [(key2411, -4), (key2406, 2), (key2406, 2), (key2443, 2), (key2443, 2), (key2437, -4), (key2593, 2), (key2587, -1), (key2587, -1), (key2880, 2), (key2843, -1), (key2843, -1), (key2989, -1), (key2989, -1), (key2968, -1), (key2968, -1), (key2966, 2), (key2966, 2), (key2600, -1), (key2600, -1), (key2598, 2), (key2910, -1), (key2910, -1), (key2889, 2), (key2889, 2), (key2887, -1), (key2887, -1), (key3002, 2), (key2995, -1), (key2995, -1)]

theorem rawRowCheck6320 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form4 = rawRow6320 := by decide +kernel

def row6320 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck6320 : row6320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6320 := by decide +kernel

theorem rowEval6320 (x : Key → ℝ) : Integer.Sparse.eval row6320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6320, Integer.Sparse.eval_collectBalanced, rawRowCheck6320]

def rawRow6321 : Integer.Sparse Key := [(key2406, -4), (key2437, 2), (key2443, 2), (key2406, 2), (key2411, 2), (key2443, -4), (key2843, 2), (key2966, -1), (key2968, -1), (key2587, 2), (key2966, -1), (key2989, -1), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, 2), (key2989, 2), (key2887, -1), (key2889, -1), (key2995, 2), (key2598, -1), (key2600, -1), (key2887, 2), (key2910, 2), (key2995, -1), (key3002, -1), (key2600, 2), (key2889, -1), (key2910, -1)]

theorem rawRowCheck6321 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form4 = rawRow6321 := by decide +kernel

def row6321 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6321 : row6321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6321 := by decide +kernel

theorem rowEval6321 (x : Key → ℝ) : Integer.Sparse.eval row6321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6321, Integer.Sparse.eval_collectBalanced, rawRowCheck6321]

def rawRow6322 : Integer.Sparse Key := [(key2406, -4), (key2443, 2), (key2437, 2), (key2411, 2), (key2406, 2), (key2443, -4), (key2843, 2), (key2968, -1), (key2966, -1), (key2587, 2), (key2989, -1), (key2966, -1), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, 2), (key2968, 2), (key2889, -1), (key2887, -1), (key2995, 2), (key2600, -1), (key2598, -1), (key2910, 2), (key2887, 2), (key3002, -1), (key2995, -1), (key2600, 2), (key2910, -1), (key2889, -1)]

theorem rawRowCheck6322 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form4 = rawRow6322 := by decide +kernel

def row6322 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6322 : row6322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6322 := by decide +kernel

theorem rowEval6322 (x : Key → ℝ) : Integer.Sparse.eval row6322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6322, Integer.Sparse.eval_collectBalanced, rawRowCheck6322]

def rawRow6323 : Integer.Sparse Key := [(key2437, -4), (key2406, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2411, -4), (key2966, 2), (key2843, -1), (key2968, -1), (key2966, 2), (key2587, -1), (key2989, -1), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, 2), (key2880, 2), (key2887, -1), (key2995, -1), (key2889, 2), (key2887, -1), (key2995, -1), (key2598, 2), (key3002, 2), (key2600, -1), (key2910, -1), (key2889, 2), (key2600, -1), (key2910, -1)]

theorem rawRowCheck6323 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form4 = rawRow6323 := by decide +kernel

def row6323 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck6323 : row6323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6323 := by decide +kernel

theorem rowEval6323 (x : Key → ℝ) : Integer.Sparse.eval row6323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6323, Integer.Sparse.eval_collectBalanced, rawRowCheck6323]

def rawRow6324 : Integer.Sparse Key := [(key2437, -4), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2411, -4), (key2966, 2), (key2968, -1), (key2843, -1), (key2966, 2), (key2989, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, 2), (key2593, 2), (key2995, -1), (key2887, -1), (key2889, 2), (key2995, -1), (key2887, -1), (key3002, 2), (key2598, 2), (key2910, -1), (key2600, -1), (key2889, 2), (key2910, -1), (key2600, -1)]

theorem rawRowCheck6324 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form4 = rawRow6324 := by decide +kernel

def row6324 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck6324 : row6324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6324 := by decide +kernel

theorem rowEval6324 (x : Key → ℝ) : Integer.Sparse.eval row6324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6324, Integer.Sparse.eval_collectBalanced, rawRowCheck6324]

def rawRow6325 : Integer.Sparse Key := [(key2443, -4), (key2406, 2), (key2437, 2), (key2411, 2), (key2443, 2), (key2406, -4), (key2968, 2), (key2843, -1), (key2966, -1), (key2989, 2), (key2587, -1), (key2966, -1), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, 2), (key2843, 2), (key2889, -1), (key2995, -1), (key2887, 2), (key2910, -1), (key3002, -1), (key2600, 2), (key2995, 2), (key2598, -1), (key2887, -1), (key2910, 2), (key2600, -1), (key2889, -1)]

theorem rawRowCheck6325 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form4 = rawRow6325 := by decide +kernel

def row6325 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6325 : row6325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6325 := by decide +kernel

theorem rowEval6325 (x : Key → ℝ) : Integer.Sparse.eval row6325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6325, Integer.Sparse.eval_collectBalanced, rawRowCheck6325]

def rawRow6326 : Integer.Sparse Key := [(key2443, -4), (key2437, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2406, -4), (key2968, 2), (key2966, -1), (key2843, -1), (key2989, 2), (key2966, -1), (key2587, -1), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, 2), (key2587, 2), (key2995, -1), (key2889, -1), (key2887, 2), (key3002, -1), (key2910, -1), (key2995, 2), (key2600, 2), (key2887, -1), (key2598, -1), (key2910, 2), (key2889, -1), (key2600, -1)]

theorem rawRowCheck6326 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form4 = rawRow6326 := by decide +kernel

def row6326 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6326 : row6326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6326 := by decide +kernel

theorem rowEval6326 (x : Key → ℝ) : Integer.Sparse.eval row6326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6326, Integer.Sparse.eval_collectBalanced, rawRowCheck6326]

def rawRow6327 : Integer.Sparse Key := [(key2411, -4), (key2443, 2), (key2443, 2), (key2406, 2), (key2406, 2), (key2437, -4), (key2880, 2), (key2989, -1), (key2989, -1), (key2593, 2), (key2968, -1), (key2968, -1), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, 2), (key2966, 2), (key2910, -1), (key2910, -1), (key3002, 2), (key2600, -1), (key2600, -1), (key2889, 2), (key2889, 2), (key2995, -1), (key2995, -1), (key2598, 2), (key2887, -1), (key2887, -1)]

theorem rawRowCheck6327 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form4 = rawRow6327 := by decide +kernel

def row6327 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck6327 : row6327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6327 := by decide +kernel

theorem rowEval6327 (x : Key → ℝ) : Integer.Sparse.eval row6327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6327, Integer.Sparse.eval_collectBalanced, rawRowCheck6327]

def rawRow6328 : Integer.Sparse Key := [(key2443, -4), (key2411, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, -4), (key2989, 2), (key2880, -1), (key2989, -1), (key2968, 2), (key2593, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, 2), (key2843, 2), (key2910, -1), (key3002, -1), (key2910, 2), (key2889, -1), (key2995, -1), (key2600, 2), (key2995, 2), (key2600, -1), (key2889, -1), (key2887, 2), (key2598, -1), (key2887, -1)]

theorem rawRowCheck6328 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form4 = rawRow6328 := by decide +kernel

def row6328 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6328 : row6328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6328 := by decide +kernel

theorem rowEval6328 (x : Key → ℝ) : Integer.Sparse.eval row6328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6328, Integer.Sparse.eval_collectBalanced, rawRowCheck6328]

def rawRow6329 : Integer.Sparse Key := [(key2443, -4), (key2443, 2), (key2411, 2), (key2437, 2), (key2406, 2), (key2406, -4), (key2989, 2), (key2989, -1), (key2880, -1), (key2968, 2), (key2968, -1), (key2593, -1), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, 2), (key2587, 2), (key3002, -1), (key2910, -1), (key2910, 2), (key2995, -1), (key2889, -1), (key2995, 2), (key2600, 2), (key2889, -1), (key2600, -1), (key2887, 2), (key2887, -1), (key2598, -1)]

theorem rawRowCheck6329 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form4 = rawRow6329 := by decide +kernel

def row6329 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck6329 : row6329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6329 := by decide +kernel

theorem rowEval6329 (x : Key → ℝ) : Integer.Sparse.eval row6329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6329, Integer.Sparse.eval_collectBalanced, rawRowCheck6329]

def rawRow6330 : Integer.Sparse Key := [(key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2378, 2), (key2390, -1), (key2394, -1), (key2766, 2), (key2887, -1), (key2910, -1), (key2929, -1), (key2931, -1), (key2966, -1), (key2989, -1), (key2995, 2), (key3002, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

theorem rawRowCheck6330 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form4 = rawRow6330 := by decide +kernel

def row6330 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2929, -1), (key2931, 1), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck6330 : row6330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6330 := by decide +kernel

theorem rowEval6330 (x : Key → ℝ) : Integer.Sparse.eval row6330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6330, Integer.Sparse.eval_collectBalanced, rawRowCheck6330]

def rawRow6331 : Integer.Sparse Key := [(key2472, -4), (key2484, 2), (key2480, 2), (key2509, 2), (key2503, 2), (key2524, -4), (key2378, 2), (key2394, -1), (key2390, -1), (key2766, 2), (key2910, -1), (key2887, -1), (key2931, -1), (key2929, -1), (key2989, -1), (key2966, -1), (key3002, 2), (key2995, 2), (key2593, -1), (key2587, -1), (key2600, 2), (key2772, -1), (key2766, -1), (key2880, 2), (key2843, 2), (key2910, -1), (key2889, -1), (key2931, 2), (key2989, -1), (key2968, -1)]

theorem rawRowCheck6331 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form4 = rawRow6331 := by decide +kernel

def row6331 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2929, -1), (key2931, 1), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck6331 : row6331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6331 := by decide +kernel

theorem rowEval6331 (x : Key → ℝ) : Integer.Sparse.eval row6331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6331, Integer.Sparse.eval_collectBalanced, rawRowCheck6331]

def rawRow6332 : Integer.Sparse Key := [(key2484, -4), (key2472, 2), (key2480, 2), (key2509, 2), (key2524, 2), (key2503, -4), (key2394, 2), (key2378, -1), (key2390, -1), (key2910, 2), (key2766, -1), (key2887, -1), (key2989, -1), (key3002, -1), (key2931, -1), (key2995, -1), (key2929, 2), (key2966, 2), (key2593, -1), (key2600, -1), (key2587, 2), (key2880, -1), (key2910, -1), (key2772, 2), (key2889, 2), (key2766, -1), (key2843, -1), (key2989, 2), (key2931, -1), (key2968, -1)]

theorem rawRowCheck6332 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form4 = rawRow6332 := by decide +kernel

def row6332 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2929, 2), (key2931, -2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck6332 : row6332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6332 := by decide +kernel

theorem rowEval6332 (x : Key → ℝ) : Integer.Sparse.eval row6332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6332, Integer.Sparse.eval_collectBalanced, rawRowCheck6332]

def rawRow6333 : Integer.Sparse Key := [(key2484, -4), (key2480, 2), (key2472, 2), (key2524, 2), (key2509, 2), (key2503, -4), (key2394, 2), (key2390, -1), (key2378, -1), (key2910, 2), (key2887, -1), (key2766, -1), (key3002, -1), (key2989, -1), (key2995, -1), (key2931, -1), (key2966, 2), (key2929, 2), (key2600, -1), (key2593, -1), (key2587, 2), (key2910, -1), (key2880, -1), (key2889, 2), (key2772, 2), (key2843, -1), (key2766, -1), (key2989, 2), (key2968, -1), (key2931, -1)]

theorem rawRowCheck6333 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form4 = rawRow6333 := by decide +kernel

def row6333 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2929, 2), (key2931, -2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck6333 : row6333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6333 := by decide +kernel

theorem rowEval6333 (x : Key → ℝ) : Integer.Sparse.eval row6333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6333, Integer.Sparse.eval_collectBalanced, rawRowCheck6333]

def rawRow6334 : Integer.Sparse Key := [(key2472, -4), (key2503, 2), (key2509, 2), (key2480, 2), (key2484, 2), (key2524, -4), (key2406, 2), (key2437, -1), (key2443, -1), (key2587, 2), (key2966, -1), (key2989, -1), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, 2), (key3002, 2), (key2766, -1), (key2772, -1), (key2931, 2), (key2587, -1), (key2593, -1), (key2843, 2), (key2880, 2), (key2968, -1), (key2989, -1), (key2600, 2), (key2889, -1), (key2910, -1)]

theorem rawRowCheck6334 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form4 = rawRow6334 := by decide +kernel

def row6334 : Integer.Sparse Key := [(key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2931, 2), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck6334 : row6334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6334 := by decide +kernel

theorem rowEval6334 (x : Key → ℝ) : Integer.Sparse.eval row6334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6334, Integer.Sparse.eval_collectBalanced, rawRowCheck6334]

def rawRow6335 : Integer.Sparse Key := [(key2472, -4), (key2509, 2), (key2503, 2), (key2484, 2), (key2480, 2), (key2524, -4), (key2406, 2), (key2443, -1), (key2437, -1), (key2587, 2), (key2989, -1), (key2966, -1), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, 2), (key2995, 2), (key2772, -1), (key2766, -1), (key2931, 2), (key2593, -1), (key2587, -1), (key2880, 2), (key2843, 2), (key2989, -1), (key2968, -1), (key2600, 2), (key2910, -1), (key2889, -1)]

theorem rawRowCheck6335 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form4 = rawRow6335 := by decide +kernel

def row6335 : Integer.Sparse Key := [(key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2931, 2), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

theorem rowCheck6335 : row6335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6335 := by decide +kernel

theorem rowEval6335 (x : Key → ℝ) : Integer.Sparse.eval row6335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6335, Integer.Sparse.eval_collectBalanced, rawRowCheck6335]

def rawRow6336 : Integer.Sparse Key := [(key2503, -4), (key2472, 2), (key2509, 2), (key2480, 2), (key2524, 2), (key2484, -4), (key2437, 2), (key2406, -1), (key2443, -1), (key2966, 2), (key2587, -1), (key2989, -1), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, 2), (key2910, 2), (key2766, -1), (key2931, -1), (key2772, 2), (key2843, -1), (key2968, -1), (key2587, 2), (key2989, 2), (key2593, -1), (key2880, -1), (key2889, 2), (key2600, -1), (key2910, -1)]

theorem rawRowCheck6336 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form4 = rawRow6336 := by decide +kernel

def row6336 : Integer.Sparse Key := [(key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2931, -1), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck6336 : row6336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6336 := by decide +kernel

theorem rowEval6336 (x : Key → ℝ) : Integer.Sparse.eval row6336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6336, Integer.Sparse.eval_collectBalanced, rawRowCheck6336]

def rawRow6337 : Integer.Sparse Key := [(key2503, -4), (key2509, 2), (key2472, 2), (key2524, 2), (key2480, 2), (key2484, -4), (key2437, 2), (key2443, -1), (key2406, -1), (key2966, 2), (key2989, -1), (key2587, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, 2), (key2600, 2), (key2931, -1), (key2766, -1), (key2772, 2), (key2968, -1), (key2843, -1), (key2989, 2), (key2587, 2), (key2880, -1), (key2593, -1), (key2889, 2), (key2910, -1), (key2600, -1)]

theorem rawRowCheck6337 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form4 = rawRow6337 := by decide +kernel

def row6337 : Integer.Sparse Key := [(key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2931, -1), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck6337 : row6337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6337 := by decide +kernel

theorem rowEval6337 (x : Key → ℝ) : Integer.Sparse.eval row6337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6337, Integer.Sparse.eval_collectBalanced, rawRowCheck6337]

def rawRow6338 : Integer.Sparse Key := [(key2503, -4), (key2480, 2), (key2524, 2), (key2472, 2), (key2509, 2), (key2484, -4), (key2503, 2), (key2480, -1), (key2524, -1), (key2437, 2), (key2598, -1), (key3002, -1), (key2766, -1), (key2931, -1), (key2587, -1), (key2989, -1), (key2600, 2), (key2910, 2), (key2843, -1), (key2968, -1), (key2889, 2), (key2766, -1), (key2931, -1), (key2587, 2), (key2989, 2), (key2600, -1), (key2910, -1), (key2772, 2), (key2593, -1), (key2880, -1)]

theorem rawRowCheck6338 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form4 = rawRow6338 := by decide +kernel

def row6338 : Integer.Sparse Key := [(key2437, 2), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, 1), (key2931, -2), (key2968, -1), (key2989, 1), (key3002, -1)]

theorem rowCheck6338 : row6338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6338 := by decide +kernel

theorem rowEval6338 (x : Key → ℝ) : Integer.Sparse.eval row6338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6338, Integer.Sparse.eval_collectBalanced, rawRowCheck6338]

def rawRow6339 : Integer.Sparse Key := [(key2503, -4), (key2524, 2), (key2480, 2), (key2509, 2), (key2472, 2), (key2484, -4), (key2503, 2), (key2524, -1), (key2480, -1), (key2437, 2), (key3002, -1), (key2598, -1), (key2931, -1), (key2766, -1), (key2989, -1), (key2587, -1), (key2910, 2), (key2600, 2), (key2968, -1), (key2843, -1), (key2889, 2), (key2931, -1), (key2766, -1), (key2989, 2), (key2587, 2), (key2910, -1), (key2600, -1), (key2772, 2), (key2880, -1), (key2593, -1)]

theorem rawRowCheck6339 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form4 = rawRow6339 := by decide +kernel

def row6339 : Integer.Sparse Key := [(key2437, 2), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, 1), (key2931, -2), (key2968, -1), (key2989, 1), (key3002, -1)]

theorem rowCheck6339 : row6339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6339 := by decide +kernel

theorem rowEval6339 (x : Key → ℝ) : Integer.Sparse.eval row6339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6339, Integer.Sparse.eval_collectBalanced, rawRowCheck6339]

def rawRow6340 : Integer.Sparse Key := [(key2524, -4), (key2480, 2), (key2503, 2), (key2484, 2), (key2509, 2), (key2472, -4), (key2524, 2), (key2480, -1), (key2503, -1), (key2580, 2), (key2390, -1), (key2437, -1), (key2910, -1), (key2989, -1), (key2600, -1), (key2931, -1), (key2587, 2), (key2766, 2), (key2889, -1), (key2968, -1), (key2843, 2), (key2910, -1), (key2989, -1), (key2600, 2), (key2931, 2), (key2587, -1), (key2766, -1), (key2880, 2), (key2593, -1), (key2772, -1)]

theorem rawRowCheck6340 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form4 = rawRow6340 := by decide +kernel

def row6340 : Integer.Sparse Key := [(key2390, -1), (key2437, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2580, 2), (key2587, 1), (key2593, -1), (key2600, 1), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -2), (key2931, 1), (key2968, -1), (key2989, -2)]

theorem rowCheck6340 : row6340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6340 := by decide +kernel

theorem rowEval6340 (x : Key → ℝ) : Integer.Sparse.eval row6340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6340, Integer.Sparse.eval_collectBalanced, rawRowCheck6340]

def rawRow6341 : Integer.Sparse Key := [(key2524, -4), (key2503, 2), (key2480, 2), (key2509, 2), (key2484, 2), (key2472, -4), (key2524, 2), (key2503, -1), (key2480, -1), (key2580, 2), (key2437, -1), (key2390, -1), (key2989, -1), (key2910, -1), (key2931, -1), (key2600, -1), (key2766, 2), (key2587, 2), (key2968, -1), (key2889, -1), (key2843, 2), (key2989, -1), (key2910, -1), (key2931, 2), (key2600, 2), (key2766, -1), (key2587, -1), (key2880, 2), (key2772, -1), (key2593, -1)]

theorem rawRowCheck6341 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form4 = rawRow6341 := by decide +kernel

def row6341 : Integer.Sparse Key := [(key2390, -1), (key2437, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2580, 2), (key2587, 1), (key2593, -1), (key2600, 1), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -2), (key2931, 1), (key2968, -1), (key2989, -2)]

theorem rowCheck6341 : row6341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6341 := by decide +kernel

theorem rowEval6341 (x : Key → ℝ) : Integer.Sparse.eval row6341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6341, Integer.Sparse.eval_collectBalanced, rawRowCheck6341]

def rawRow6342 : Integer.Sparse Key := [(key2484, -4), (key2509, 2), (key2524, 2), (key2472, 2), (key2480, 2), (key2503, -4), (key2571, 2), (key2576, -1), (key2580, -1), (key2394, 2), (key2443, -1), (key2524, -1), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, 2), (key2503, 2), (key2880, -1), (key2910, -1), (key2989, 2), (key2593, -1), (key2600, -1), (key2772, 2), (key2889, 2), (key2931, -1), (key2968, -1), (key2587, 2), (key2766, -1), (key2843, -1)]

theorem rawRowCheck6342 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form4 = rawRow6342 := by decide +kernel

def row6342 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2571, 2), (key2576, -1), (key2580, -1), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, -1), (key2931, -1), (key2968, -1), (key2989, 2)]

theorem rowCheck6342 : row6342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6342 := by decide +kernel

theorem rowEval6342 (x : Key → ℝ) : Integer.Sparse.eval row6342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6342, Integer.Sparse.eval_collectBalanced, rawRowCheck6342]

def rawRow6343 : Integer.Sparse Key := [(key2484, -4), (key2524, 2), (key2509, 2), (key2480, 2), (key2472, 2), (key2503, -4), (key2571, 2), (key2580, -1), (key2576, -1), (key2394, 2), (key2524, -1), (key2443, -1), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, 2), (key2437, 2), (key2910, -1), (key2880, -1), (key2989, 2), (key2600, -1), (key2593, -1), (key2889, 2), (key2772, 2), (key2968, -1), (key2931, -1), (key2587, 2), (key2843, -1), (key2766, -1)]

theorem rawRowCheck6343 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form4 = rawRow6343 := by decide +kernel

def row6343 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2571, 2), (key2576, -1), (key2580, -1), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, -1), (key2931, -1), (key2968, -1), (key2989, 2)]

theorem rowCheck6343 : row6343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6343 := by decide +kernel

theorem rowEval6343 (x : Key → ℝ) : Integer.Sparse.eval row6343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6343, Integer.Sparse.eval_collectBalanced, rawRowCheck6343]

def rawRow6344 : Integer.Sparse Key := [(key2524, -4), (key2484, 2), (key2509, 2), (key2480, 2), (key2503, 2), (key2472, -4), (key2580, 2), (key2571, -1), (key2576, -1), (key2524, 2), (key2394, -1), (key2443, -1), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, 2), (key2406, 2), (key2910, -1), (key2989, -1), (key2880, 2), (key2889, -1), (key2968, -1), (key2600, 2), (key2931, 2), (key2593, -1), (key2772, -1), (key2843, 2), (key2587, -1), (key2766, -1)]

theorem rawRowCheck6344 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form4 = rawRow6344 := by decide +kernel

def row6344 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2571, -1), (key2576, -1), (key2580, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

theorem rowCheck6344 : row6344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6344 := by decide +kernel

theorem rowEval6344 (x : Key → ℝ) : Integer.Sparse.eval row6344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6344, Integer.Sparse.eval_collectBalanced, rawRowCheck6344]

def rawRow6345 : Integer.Sparse Key := [(key2524, -4), (key2509, 2), (key2484, 2), (key2503, 2), (key2480, 2), (key2472, -4), (key2580, 2), (key2576, -1), (key2571, -1), (key2524, 2), (key2443, -1), (key2394, -1), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, 2), (key2378, 2), (key2989, -1), (key2910, -1), (key2880, 2), (key2968, -1), (key2889, -1), (key2931, 2), (key2600, 2), (key2772, -1), (key2593, -1), (key2843, 2), (key2766, -1), (key2587, -1)]

theorem rawRowCheck6345 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form4 = rawRow6345 := by decide +kernel

def row6345 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2571, -1), (key2576, -1), (key2580, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

theorem rowCheck6345 : row6345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6345 := by decide +kernel

theorem rowEval6345 (x : Key → ℝ) : Integer.Sparse.eval row6345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6345, Integer.Sparse.eval_collectBalanced, rawRowCheck6345]

def rawRow6346 : Integer.Sparse Key := [(key2569, -4), (key2571, 2), (key2571, 2), (key2576, 2), (key2576, 2), (key2580, -4), (key2383, 2), (key2394, -1), (key2394, -1), (key2411, 2), (key2484, -1), (key2484, -1), (key2443, -1), (key2443, -1), (key2509, -1), (key2509, -1), (key2524, 2), (key2524, 2), (key2378, -1), (key2378, -1), (key2390, 2), (key2406, -1), (key2406, -1), (key2472, 2), (key2472, 2), (key2480, -1), (key2480, -1), (key2437, 2), (key2503, -1), (key2503, -1)]

theorem rawRowCheck6346 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form4 = rawRow6346 := by decide +kernel

def row6346 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

theorem rowCheck6346 : row6346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6346 := by decide +kernel

theorem rowEval6346 (x : Key → ℝ) : Integer.Sparse.eval row6346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6346, Integer.Sparse.eval_collectBalanced, rawRowCheck6346]

def rawRow6347 : Integer.Sparse Key := [(key2571, -4), (key2569, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2576, -4), (key2394, 2), (key2383, -1), (key2394, -1), (key2484, 2), (key2411, -1), (key2484, -1), (key2509, -1), (key2524, -1), (key2443, -1), (key2524, -1), (key2443, 2), (key2509, 2), (key2378, -1), (key2390, -1), (key2378, 2), (key2472, -1), (key2480, -1), (key2406, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2503, 2), (key2437, -1), (key2503, -1)]

theorem rawRowCheck6347 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form4 = rawRow6347 := by decide +kernel

def row6347 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6347 : row6347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6347 := by decide +kernel

theorem rowEval6347 (x : Key → ℝ) : Integer.Sparse.eval row6347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6347, Integer.Sparse.eval_collectBalanced, rawRowCheck6347]

def rawRow6348 : Integer.Sparse Key := [(key2571, -4), (key2571, 2), (key2569, 2), (key2580, 2), (key2576, 2), (key2576, -4), (key2394, 2), (key2394, -1), (key2383, -1), (key2484, 2), (key2484, -1), (key2411, -1), (key2524, -1), (key2509, -1), (key2524, -1), (key2443, -1), (key2509, 2), (key2443, 2), (key2390, -1), (key2378, -1), (key2378, 2), (key2480, -1), (key2472, -1), (key2480, 2), (key2406, 2), (key2472, -1), (key2406, -1), (key2503, 2), (key2503, -1), (key2437, -1)]

theorem rawRowCheck6348 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form4 = rawRow6348 := by decide +kernel

def row6348 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6348 : row6348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6348 := by decide +kernel

theorem rowEval6348 (x : Key → ℝ) : Integer.Sparse.eval row6348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6348, Integer.Sparse.eval_collectBalanced, rawRowCheck6348]

def rawRow6349 : Integer.Sparse Key := [(key2569, -4), (key2576, 2), (key2576, 2), (key2571, 2), (key2571, 2), (key2580, -4), (key2411, 2), (key2443, -1), (key2443, -1), (key2383, 2), (key2509, -1), (key2509, -1), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, 2), (key2524, 2), (key2406, -1), (key2406, -1), (key2437, 2), (key2378, -1), (key2378, -1), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2390, 2), (key2480, -1), (key2480, -1)]

theorem rawRowCheck6349 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form4 = rawRow6349 := by decide +kernel

def row6349 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

theorem rowCheck6349 : row6349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6349 := by decide +kernel

theorem rowEval6349 (x : Key → ℝ) : Integer.Sparse.eval row6349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6349, Integer.Sparse.eval_collectBalanced, rawRowCheck6349]

def rawRow6350 : Integer.Sparse Key := [(key2576, -4), (key2569, 2), (key2576, 2), (key2571, 2), (key2580, 2), (key2571, -4), (key2443, 2), (key2411, -1), (key2443, -1), (key2509, 2), (key2383, -1), (key2509, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, 2), (key2484, 2), (key2406, -1), (key2437, -1), (key2406, 2), (key2472, -1), (key2503, -1), (key2378, 2), (key2503, 2), (key2378, -1), (key2472, -1), (key2480, 2), (key2390, -1), (key2480, -1)]

theorem rawRowCheck6350 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form4 = rawRow6350 := by decide +kernel

def row6350 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6350 : row6350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6350 := by decide +kernel

theorem rowEval6350 (x : Key → ℝ) : Integer.Sparse.eval row6350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6350, Integer.Sparse.eval_collectBalanced, rawRowCheck6350]

def rawRow6351 : Integer.Sparse Key := [(key2576, -4), (key2576, 2), (key2569, 2), (key2580, 2), (key2571, 2), (key2571, -4), (key2443, 2), (key2443, -1), (key2411, -1), (key2509, 2), (key2509, -1), (key2383, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, 2), (key2394, 2), (key2437, -1), (key2406, -1), (key2406, 2), (key2503, -1), (key2472, -1), (key2503, 2), (key2378, 2), (key2472, -1), (key2378, -1), (key2480, 2), (key2480, -1), (key2390, -1)]

theorem rawRowCheck6351 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form4 = rawRow6351 := by decide +kernel

def row6351 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6351 : row6351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6351 := by decide +kernel

theorem rowEval6351 (x : Key → ℝ) : Integer.Sparse.eval row6351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6351, Integer.Sparse.eval_collectBalanced, rawRowCheck6351]

def rawRow6352 : Integer.Sparse Key := [(key2571, -4), (key2576, 2), (key2580, 2), (key2569, 2), (key2571, 2), (key2576, -4), (key2484, 2), (key2509, -1), (key2524, -1), (key2394, 2), (key2443, -1), (key2524, -1), (key2383, -1), (key2394, -1), (key2411, -1), (key2484, -1), (key2443, 2), (key2509, 2), (key2472, -1), (key2480, -1), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, 2), (key2480, 2), (key2437, -1), (key2503, -1), (key2378, 2), (key2406, -1), (key2472, -1)]

theorem rawRowCheck6352 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form4 = rawRow6352 := by decide +kernel

def row6352 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6352 : row6352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6352 := by decide +kernel

theorem rowEval6352 (x : Key → ℝ) : Integer.Sparse.eval row6352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6352, Integer.Sparse.eval_collectBalanced, rawRowCheck6352]

def rawRow6353 : Integer.Sparse Key := [(key2571, -4), (key2580, 2), (key2576, 2), (key2571, 2), (key2569, 2), (key2576, -4), (key2484, 2), (key2524, -1), (key2509, -1), (key2394, 2), (key2524, -1), (key2443, -1), (key2394, -1), (key2383, -1), (key2484, -1), (key2411, -1), (key2509, 2), (key2443, 2), (key2480, -1), (key2472, -1), (key2503, 2), (key2390, -1), (key2378, -1), (key2480, 2), (key2406, 2), (key2503, -1), (key2437, -1), (key2378, 2), (key2472, -1), (key2406, -1)]

theorem rawRowCheck6353 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form4 = rawRow6353 := by decide +kernel

def row6353 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6353 : row6353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6353 := by decide +kernel

theorem rowEval6353 (x : Key → ℝ) : Integer.Sparse.eval row6353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6353, Integer.Sparse.eval_collectBalanced, rawRowCheck6353]

def rawRow6354 : Integer.Sparse Key := [(key2576, -4), (key2571, 2), (key2580, 2), (key2569, 2), (key2576, 2), (key2571, -4), (key2509, 2), (key2484, -1), (key2524, -1), (key2443, 2), (key2394, -1), (key2524, -1), (key2411, -1), (key2443, -1), (key2383, -1), (key2509, -1), (key2394, 2), (key2484, 2), (key2472, -1), (key2503, -1), (key2480, 2), (key2406, -1), (key2437, -1), (key2378, 2), (key2503, 2), (key2390, -1), (key2480, -1), (key2406, 2), (key2378, -1), (key2472, -1)]

theorem rawRowCheck6354 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form4 = rawRow6354 := by decide +kernel

def row6354 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6354 : row6354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6354 := by decide +kernel

theorem rowEval6354 (x : Key → ℝ) : Integer.Sparse.eval row6354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6354, Integer.Sparse.eval_collectBalanced, rawRowCheck6354]

def rawRow6355 : Integer.Sparse Key := [(key2576, -4), (key2580, 2), (key2571, 2), (key2576, 2), (key2569, 2), (key2571, -4), (key2509, 2), (key2524, -1), (key2484, -1), (key2443, 2), (key2524, -1), (key2394, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2484, 2), (key2394, 2), (key2503, -1), (key2472, -1), (key2480, 2), (key2437, -1), (key2406, -1), (key2503, 2), (key2378, 2), (key2480, -1), (key2390, -1), (key2406, 2), (key2472, -1), (key2378, -1)]

theorem rawRowCheck6355 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form4 = rawRow6355 := by decide +kernel

def row6355 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

theorem rowCheck6355 : row6355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6355 := by decide +kernel

theorem rowEval6355 (x : Key → ℝ) : Integer.Sparse.eval row6355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6355, Integer.Sparse.eval_collectBalanced, rawRowCheck6355]

def rawRow6356 : Integer.Sparse Key := [(key2580, -4), (key2571, 2), (key2576, 2), (key2571, 2), (key2576, 2), (key2569, -4), (key2524, 2), (key2484, -1), (key2509, -1), (key2524, 2), (key2394, -1), (key2443, -1), (key2484, -1), (key2509, -1), (key2394, -1), (key2443, -1), (key2383, 2), (key2411, 2), (key2480, -1), (key2503, -1), (key2472, 2), (key2480, -1), (key2503, -1), (key2390, 2), (key2437, 2), (key2378, -1), (key2406, -1), (key2472, 2), (key2378, -1), (key2406, -1)]

theorem rawRowCheck6356 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form4 = rawRow6356 := by decide +kernel

def row6356 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

theorem rowCheck6356 : row6356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6356 := by decide +kernel

theorem rowEval6356 (x : Key → ℝ) : Integer.Sparse.eval row6356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck6356, Integer.Sparse.eval_collectBalanced, rawRowCheck6356]

def rawRow6357 : Integer.Sparse Key := [(key2580, -4), (key2576, 2), (key2571, 2), (key2576, 2), (key2571, 2), (key2569, -4), (key2524, 2), (key2509, -1), (key2484, -1), (key2524, 2), (key2443, -1), (key2394, -1), (key2509, -1), (key2484, -1), (key2443, -1), (key2394, -1), (key2411, 2), (key2383, 2), (key2503, -1), (key2480, -1), (key2472, 2), (key2503, -1), (key2480, -1), (key2437, 2), (key2390, 2), (key2406, -1), (key2378, -1), (key2472, 2), (key2406, -1), (key2378, -1)]

theorem rawRowCheck6357 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form4 = rawRow6357 := by decide +kernel

def row6357 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

theorem rowCheck6357 : row6357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6357 := by decide +kernel

theorem rowEval6357 (x : Key → ℝ) : Integer.Sparse.eval row6357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form4) x := by
  rw [rowCheck6357, Integer.Sparse.eval_collectBalanced, rawRowCheck6357]

def rawRow6358 : Integer.Sparse Key := [(key2612, -2), (key2612, 1), (key2618, 1), (key2805, -2), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2948, 1), (key2960, 1), (key2950, -2), (key2960, -2), (key2628, 2), (key2628, -1), (key2641, -1), (key2702, 2), (key2702, -1), (key2728, -1), (key2972, -1), (key2976, -1), (key2972, -1), (key2983, -1), (key2976, 2), (key2983, 2), (key2646, -1), (key2648, -1), (key2646, 1), (key2653, 1), (key2735, -1), (key2737, -1), (key2737, 1), (key2747, 1), (key2893, 1), (key2897, 1), (key2897, -1), (key2904, -1), (key2997, 1), (key3000, 1), (key2998, -1), (key3000, -1)]

theorem rawRowCheck6358 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form5 = rawRow6358 := by decide +kernel

def row6358 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

theorem rowCheck6358 : row6358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6358 := by decide +kernel

theorem rowEval6358 (x : Key → ℝ) : Integer.Sparse.eval row6358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6358, Integer.Sparse.eval_collectBalanced, rawRowCheck6358]

def rawRow6359 : Integer.Sparse Key := [(key2616, -2), (key2618, 1), (key2612, 1), (key2805, -2), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2960, 1), (key2948, 1), (key2960, -2), (key2950, -2), (key2628, 2), (key2641, -1), (key2628, -1), (key2702, 2), (key2728, -1), (key2702, -1), (key2976, -1), (key2972, -1), (key2983, -1), (key2972, -1), (key2983, 2), (key2976, 2), (key2648, -1), (key2646, -1), (key2653, 1), (key2646, 1), (key2737, -1), (key2735, -1), (key2747, 1), (key2737, 1), (key2897, 1), (key2893, 1), (key2904, -1), (key2897, -1), (key3000, 1), (key2997, 1), (key3000, -1), (key2998, -1)]

theorem rawRowCheck6359 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form5 = rawRow6359 := by decide +kernel

def row6359 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

theorem rowCheck6359 : row6359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6359 := by decide +kernel

theorem rowEval6359 (x : Key → ℝ) : Integer.Sparse.eval row6359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6359, Integer.Sparse.eval_collectBalanced, rawRowCheck6359]

def rawRow6360 : Integer.Sparse Key := [(key2621, -2), (key2616, 1), (key2616, 1), (key2831, -2), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2950, 1), (key2950, 1), (key2948, -2), (key2948, -2), (key2641, 2), (key2628, -1), (key2628, -1), (key2728, 2), (key2702, -1), (key2702, -1), (key2983, -1), (key2983, -1), (key2976, -1), (key2976, -1), (key2972, 2), (key2972, 2), (key2653, -1), (key2653, -1), (key2648, 1), (key2648, 1), (key2747, -1), (key2747, -1), (key2735, 1), (key2735, 1), (key2904, 1), (key2904, 1), (key2893, -1), (key2893, -1), (key2998, 1), (key2998, 1), (key2997, -1), (key2997, -1)]

theorem rawRowCheck6360 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form5 = rawRow6360 := by decide +kernel

def row6360 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 2), (key2831, -2), (key2893, -2), (key2904, 2), (key2948, -4), (key2950, 2), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

theorem rowCheck6360 : row6360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6360 := by decide +kernel

theorem rowEval6360 (x : Key → ℝ) : Integer.Sparse.eval row6360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6360, Integer.Sparse.eval_collectBalanced, rawRowCheck6360]

def rawRow6361 : Integer.Sparse Key := [(key2809, -2), (key2829, 1), (key2835, 1), (key2612, -2), (key2948, 1), (key2960, 1), (key2612, 1), (key2618, 1), (key2805, 1), (key2831, 1), (key2950, -2), (key2960, -2), (key2702, 2), (key2972, -1), (key2976, -1), (key2628, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2641, -1), (key2702, -1), (key2728, -1), (key2976, 2), (key2983, 2), (key2735, -1), (key2737, -1), (key2893, 1), (key2897, 1), (key2646, -1), (key2648, -1), (key2997, 1), (key3000, 1), (key2646, 1), (key2653, 1), (key2998, -1), (key3000, -1), (key2737, 1), (key2747, 1), (key2897, -1), (key2904, -1)]

theorem rawRowCheck6361 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form5 = rawRow6361 := by decide +kernel

def row6361 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2893, 1), (key2904, -1), (key2948, 1), (key2950, -2), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

theorem rowCheck6361 : row6361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6361 := by decide +kernel

theorem rowEval6361 (x : Key → ℝ) : Integer.Sparse.eval row6361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6361, Integer.Sparse.eval_collectBalanced, rawRowCheck6361]

def rawRow6362 : Integer.Sparse Key := [(key2809, -2), (key2835, 1), (key2829, 1), (key2616, -2), (key2960, 1), (key2948, 1), (key2618, 1), (key2612, 1), (key2831, 1), (key2805, 1), (key2960, -2), (key2950, -2), (key2702, 2), (key2976, -1), (key2972, -1), (key2628, 2), (key2983, -1), (key2972, -1), (key2641, -1), (key2628, -1), (key2728, -1), (key2702, -1), (key2983, 2), (key2976, 2), (key2737, -1), (key2735, -1), (key2897, 1), (key2893, 1), (key2648, -1), (key2646, -1), (key3000, 1), (key2997, 1), (key2653, 1), (key2646, 1), (key3000, -1), (key2998, -1), (key2747, 1), (key2737, 1), (key2904, -1), (key2897, -1)]

theorem rawRowCheck6362 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form5 = rawRow6362 := by decide +kernel

def row6362 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2893, 1), (key2904, -1), (key2948, 1), (key2950, -2), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

theorem rowCheck6362 : row6362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6362 := by decide +kernel

theorem rowEval6362 (x : Key → ℝ) : Integer.Sparse.eval row6362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6362, Integer.Sparse.eval_collectBalanced, rawRowCheck6362]

def rawRow6363 : Integer.Sparse Key := [(key2829, -2), (key2809, 1), (key2835, 1), (key2829, -2), (key2612, 1), (key2960, 1), (key2805, 1), (key2950, 1), (key2612, 1), (key2960, 1), (key2618, -2), (key2831, -2), (key2972, 2), (key2702, -1), (key2976, -1), (key2972, 2), (key2628, -1), (key2983, -1), (key2702, -1), (key2976, -1), (key2628, -1), (key2983, -1), (key2641, 2), (key2728, 2), (key2893, -1), (key2997, -1), (key2735, 1), (key2998, 1), (key2893, -1), (key2997, -1), (key2648, 1), (key2904, 1), (key2735, 1), (key2998, 1), (key2653, -1), (key2747, -1), (key2648, 1), (key2904, 1), (key2653, -1), (key2747, -1)]

theorem rawRowCheck6363 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form5 = rawRow6363 := by decide +kernel

def row6363 : Integer.Sparse Key := [(key2612, 2), (key2618, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -4), (key2831, -2), (key2835, 1), (key2893, -2), (key2904, 2), (key2950, 1), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

theorem rowCheck6363 : row6363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6363 := by decide +kernel

theorem rowEval6363 (x : Key → ℝ) : Integer.Sparse.eval row6363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6363, Integer.Sparse.eval_collectBalanced, rawRowCheck6363]

def rawRow6364 : Integer.Sparse Key := [(key2829, -2), (key2835, 1), (key2809, 1), (key2829, -2), (key2960, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2831, -2), (key2618, -2), (key2972, 2), (key2976, -1), (key2702, -1), (key2972, 2), (key2983, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2728, 2), (key2641, 2), (key2997, -1), (key2893, -1), (key2998, 1), (key2735, 1), (key2997, -1), (key2893, -1), (key2904, 1), (key2648, 1), (key2998, 1), (key2735, 1), (key2747, -1), (key2653, -1), (key2904, 1), (key2648, 1), (key2747, -1), (key2653, -1)]

theorem rawRowCheck6364 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form5 = rawRow6364 := by decide +kernel

def row6364 : Integer.Sparse Key := [(key2612, 2), (key2618, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -4), (key2831, -2), (key2835, 1), (key2893, -2), (key2904, 2), (key2950, 1), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

theorem rowCheck6364 : row6364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6364 := by decide +kernel

theorem rowEval6364 (x : Key → ℝ) : Integer.Sparse.eval row6364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6364, Integer.Sparse.eval_collectBalanced, rawRowCheck6364]

def rawRow6365 : Integer.Sparse Key := [(key2835, -2), (key2809, 1), (key2829, 1), (key3017, -2), (key2616, 1), (key2829, 1), (key2831, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2612, -2), (key2805, -2), (key2976, 2), (key2702, -1), (key2972, -1), (key2983, 2), (key2628, -1), (key2972, -1), (key2728, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2628, 2), (key2702, 2), (key2897, -1), (key2998, -1), (key2737, 1), (key2997, 1), (key2904, -1), (key3000, -1), (key2646, 1), (key2893, 1), (key2747, 1), (key3000, 1), (key2646, -1), (key2735, -1), (key2653, 1), (key2897, 1), (key2648, -1), (key2737, -1)]

theorem rawRowCheck6365 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form5 = rawRow6365 := by decide +kernel

def row6365 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 2), (key2831, 1), (key2835, -2), (key2893, 1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3017, -2)]

theorem rowCheck6365 : row6365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6365 := by decide +kernel

theorem rowEval6365 (x : Key → ℝ) : Integer.Sparse.eval row6365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6365, Integer.Sparse.eval_collectBalanced, rawRowCheck6365]

def rawRow6366 : Integer.Sparse Key := [(key2835, -2), (key2829, 1), (key2809, 1), (key3017, -2), (key2829, 1), (key2616, 1), (key2960, 1), (key2831, 1), (key2950, 1), (key2618, 1), (key2805, -2), (key2612, -2), (key2976, 2), (key2972, -1), (key2702, -1), (key2983, 2), (key2972, -1), (key2628, -1), (key2983, -1), (key2728, -1), (key2976, -1), (key2641, -1), (key2702, 2), (key2628, 2), (key2998, -1), (key2897, -1), (key2997, 1), (key2737, 1), (key3000, -1), (key2904, -1), (key2893, 1), (key2646, 1), (key3000, 1), (key2747, 1), (key2735, -1), (key2646, -1), (key2897, 1), (key2653, 1), (key2737, -1), (key2648, -1)]

theorem rawRowCheck6366 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form5 = rawRow6366 := by decide +kernel

def row6366 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 2), (key2831, 1), (key2835, -2), (key2893, 1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3017, -2)]

theorem rowCheck6366 : row6366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6366 := by decide +kernel

theorem rowEval6366 (x : Key → ℝ) : Integer.Sparse.eval row6366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6366, Integer.Sparse.eval_collectBalanced, rawRowCheck6366]

def rawRow6367 : Integer.Sparse Key := [(key3012, -2), (key3017, 1), (key3017, 1), (key2621, -2), (key2835, 1), (key2835, 1), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, -2), (key2829, -2), (key2728, 2), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, -1), (key2976, -1), (key2628, -1), (key2628, -1), (key2702, -1), (key2702, -1), (key2972, 2), (key2972, 2), (key2747, -1), (key2747, -1), (key2904, 1), (key2904, 1), (key2653, -1), (key2653, -1), (key2998, 1), (key2998, 1), (key2648, 1), (key2648, 1), (key2997, -1), (key2997, -1), (key2735, 1), (key2735, 1), (key2893, -1), (key2893, -1)]

theorem rawRowCheck6367 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form5 = rawRow6367 := by decide +kernel

def row6367 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2809, 2), (key2829, -4), (key2835, 2), (key2893, -2), (key2904, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2), (key3012, -2), (key3017, 2)]

theorem rowCheck6367 : row6367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6367 := by decide +kernel

theorem rowEval6367 (x : Key → ℝ) : Integer.Sparse.eval row6367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6367, Integer.Sparse.eval_collectBalanced, rawRowCheck6367]

def rawRow6368 : Integer.Sparse Key := [(key3017, -2), (key3012, 1), (key3017, 1), (key2835, -2), (key2621, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, -2), (key2809, -2), (key2983, 2), (key2728, -1), (key2983, -1), (key2976, 2), (key2641, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2972, -1), (key2628, 2), (key2702, 2), (key2904, -1), (key3000, -1), (key2747, 1), (key3000, 1), (key2897, -1), (key2998, -1), (key2653, 1), (key2897, 1), (key2737, 1), (key2997, 1), (key2648, -1), (key2737, -1), (key2646, 1), (key2893, 1), (key2646, -1), (key2735, -1)]

theorem rawRowCheck6368 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form5 = rawRow6368 := by decide +kernel

def row6368 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2893, 1), (key2904, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3012, 1), (key3017, -1)]

theorem rowCheck6368 : row6368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6368 := by decide +kernel

theorem rowEval6368 (x : Key → ℝ) : Integer.Sparse.eval row6368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6368, Integer.Sparse.eval_collectBalanced, rawRowCheck6368]

def rawRow6369 : Integer.Sparse Key := [(key3017, -2), (key3017, 1), (key3012, 1), (key2835, -2), (key2835, 1), (key2621, 1), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, -2), (key2616, -2), (key2983, 2), (key2983, -1), (key2728, -1), (key2976, 2), (key2976, -1), (key2641, -1), (key2972, -1), (key2702, -1), (key2972, -1), (key2628, -1), (key2702, 2), (key2628, 2), (key3000, -1), (key2904, -1), (key3000, 1), (key2747, 1), (key2998, -1), (key2897, -1), (key2897, 1), (key2653, 1), (key2997, 1), (key2737, 1), (key2737, -1), (key2648, -1), (key2893, 1), (key2646, 1), (key2735, -1), (key2646, -1)]

theorem rawRowCheck6369 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form5 = rawRow6369 := by decide +kernel

def row6369 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2893, 1), (key2904, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3012, 1), (key3017, -1)]

theorem rowCheck6369 : row6369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6369 := by decide +kernel

theorem rowEval6369 (x : Key → ℝ) : Integer.Sparse.eval row6369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6369, Integer.Sparse.eval_collectBalanced, rawRowCheck6369]

def rawRow6370 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2644, 1), (key2706, -2), (key2860, 1), (key3023, 1), (key2726, 1), (key2732, 1), (key2870, 1), (key3026, 1), (key2885, -2), (key3030, -2), (key2612, 2), (key2646, -1), (key2653, -1), (key2667, 2), (key2735, -1), (key2747, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, 2), (key3000, 2), (key2612, -1), (key2618, -1), (key2628, 1), (key2641, 1), (key2667, -1), (key2673, -1), (key2737, 1), (key2747, 1), (key2782, 1), (key2795, 1), (key2897, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1)]

theorem rawRowCheck6370 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form5 = rawRow6370 := by decide +kernel

def row6370 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2726, 1), (key2732, 1), (key2735, -1), (key2737, 1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6370 : row6370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6370 := by decide +kernel

theorem rowEval6370 (x : Key → ℝ) : Integer.Sparse.eval row6370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6370, Integer.Sparse.eval_collectBalanced, rawRowCheck6370]

def rawRow6371 : Integer.Sparse Key := [(key2632, -2), (key2644, 1), (key2640, 1), (key2706, -2), (key3023, 1), (key2860, 1), (key2732, 1), (key2726, 1), (key3026, 1), (key2870, 1), (key3030, -2), (key2885, -2), (key2616, 2), (key2653, -1), (key2646, -1), (key2667, 2), (key2747, -1), (key2735, -1), (key2943, -1), (key2936, -1), (key2960, -1), (key2948, -1), (key3000, 2), (key2998, 2), (key2618, -1), (key2612, -1), (key2641, 1), (key2628, 1), (key2673, -1), (key2667, -1), (key2747, 1), (key2737, 1), (key2795, 1), (key2782, 1), (key2904, -1), (key2897, -1), (key2960, 1), (key2950, 1), (key2983, -1), (key2976, -1)]

theorem rawRowCheck6371 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form5 = rawRow6371 := by decide +kernel

def row6371 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2726, 1), (key2732, 1), (key2735, -1), (key2737, 1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6371 : row6371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6371 := by decide +kernel

theorem rowEval6371 (x : Key → ℝ) : Integer.Sparse.eval row6371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6371, Integer.Sparse.eval_collectBalanced, rawRowCheck6371]

def rawRow6372 : Integer.Sparse Key := [(key2644, -2), (key2632, 1), (key2640, 1), (key3023, -2), (key2706, 1), (key2860, 1), (key3026, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2726, -2), (key2870, -2), (key2660, 2), (key2616, -1), (key2640, -1), (key2747, 2), (key2667, -1), (key2735, -1), (key2960, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2936, 2), (key2948, 2), (key2641, -1), (key2653, -1), (key2618, 1), (key2648, 1), (key2728, -1), (key2747, -1), (key2667, 1), (key2702, 1), (key2831, 1), (key2904, 1), (key2782, -1), (key2805, -1), (key2943, 1), (key2976, 1), (key2938, -1), (key2950, -1)]

theorem rawRowCheck6372 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form5 = rawRow6372 := by decide +kernel

def row6372 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2782, -1), (key2805, -1), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2936, 2), (key2938, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck6372 : row6372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6372 := by decide +kernel

theorem rowEval6372 (x : Key → ℝ) : Integer.Sparse.eval row6372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6372, Integer.Sparse.eval_collectBalanced, rawRowCheck6372]

def rawRow6373 : Integer.Sparse Key := [(key2644, -2), (key2640, 1), (key2632, 1), (key3023, -2), (key2860, 1), (key2706, 1), (key3030, 1), (key3026, 1), (key2885, 1), (key2732, 1), (key2870, -2), (key2726, -2), (key2660, 2), (key2640, -1), (key2616, -1), (key2747, 2), (key2735, -1), (key2667, -1), (key3000, -1), (key2960, -1), (key2998, -1), (key2943, -1), (key2948, 2), (key2936, 2), (key2653, -1), (key2641, -1), (key2648, 1), (key2618, 1), (key2747, -1), (key2728, -1), (key2702, 1), (key2667, 1), (key2904, 1), (key2831, 1), (key2805, -1), (key2782, -1), (key2976, 1), (key2943, 1), (key2950, -1), (key2938, -1)]

theorem rawRowCheck6373 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form5 = rawRow6373 := by decide +kernel

def row6373 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2782, -1), (key2805, -1), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2936, 2), (key2938, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck6373 : row6373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6373 := by decide +kernel

theorem rowEval6373 (x : Key → ℝ) : Integer.Sparse.eval row6373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6373, Integer.Sparse.eval_collectBalanced, rawRowCheck6373]

def rawRow6374 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2732, 1), (key2632, -2), (key2870, 1), (key3026, 1), (key2640, 1), (key2644, 1), (key2860, 1), (key3023, 1), (key2885, -2), (key3030, -2), (key2671, 2), (key2726, -1), (key2758, -1), (key2612, 2), (key2948, -1), (key2960, -1), (key2646, -1), (key2653, -1), (key2735, -1), (key2747, -1), (key2998, 2), (key3000, 2), (key2667, -1), (key2673, -1), (key2782, 1), (key2795, 1), (key2612, -1), (key2618, -1), (key2950, 1), (key2960, 1), (key2628, 1), (key2641, 1), (key2976, -1), (key2983, -1), (key2737, 1), (key2747, 1), (key2897, -1), (key2904, -1)]

theorem rawRowCheck6374 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form5 = rawRow6374 := by decide +kernel

def row6374 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2735, -1), (key2737, 1), (key2758, -1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6374 : row6374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6374 := by decide +kernel

theorem rowEval6374 (x : Key → ℝ) : Integer.Sparse.eval row6374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6374, Integer.Sparse.eval_collectBalanced, rawRowCheck6374]

def rawRow6375 : Integer.Sparse Key := [(key2706, -2), (key2732, 1), (key2726, 1), (key2632, -2), (key3026, 1), (key2870, 1), (key2644, 1), (key2640, 1), (key3023, 1), (key2860, 1), (key3030, -2), (key2885, -2), (key2671, 2), (key2758, -1), (key2726, -1), (key2616, 2), (key2960, -1), (key2948, -1), (key2653, -1), (key2646, -1), (key2747, -1), (key2735, -1), (key3000, 2), (key2998, 2), (key2673, -1), (key2667, -1), (key2795, 1), (key2782, 1), (key2618, -1), (key2612, -1), (key2960, 1), (key2950, 1), (key2641, 1), (key2628, 1), (key2983, -1), (key2976, -1), (key2747, 1), (key2737, 1), (key2904, -1), (key2897, -1)]

theorem rawRowCheck6375 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form5 = rawRow6375 := by decide +kernel

def row6375 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2735, -1), (key2737, 1), (key2758, -1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

theorem rowCheck6375 : row6375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6375 := by decide +kernel

theorem rowEval6375 (x : Key → ℝ) : Integer.Sparse.eval row6375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6375, Integer.Sparse.eval_collectBalanced, rawRowCheck6375]

def rawRow6376 : Integer.Sparse Key := [(key2726, -2), (key2706, 1), (key2732, 1), (key2870, -2), (key2632, 1), (key3026, 1), (key2860, 1), (key2885, 1), (key2640, 1), (key3030, 1), (key2644, -2), (key3023, -2), (key2726, 2), (key2671, -1), (key2758, -1), (key2829, 2), (key2612, -1), (key2960, -1), (key2735, -1), (key2998, -1), (key2646, -1), (key3000, -1), (key2653, 2), (key2747, 2), (key2782, -1), (key2938, -1), (key2667, 1), (key2943, 1), (key2805, -1), (key2950, -1), (key2618, 1), (key2831, 1), (key2702, 1), (key2976, 1), (key2641, -1), (key2728, -1), (key2648, 1), (key2904, 1), (key2653, -1), (key2747, -1)]

theorem rawRowCheck6376 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form5 = rawRow6376 := by decide +kernel

def row6376 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2640, 1), (key2641, -1), (key2644, -2), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2758, -1), (key2782, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2938, -1), (key2943, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck6376 : row6376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6376 := by decide +kernel

theorem rowEval6376 (x : Key → ℝ) : Integer.Sparse.eval row6376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6376, Integer.Sparse.eval_collectBalanced, rawRowCheck6376]

def rawRow6377 : Integer.Sparse Key := [(key2726, -2), (key2732, 1), (key2706, 1), (key2870, -2), (key3026, 1), (key2632, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key3023, -2), (key2644, -2), (key2726, 2), (key2758, -1), (key2671, -1), (key2829, 2), (key2960, -1), (key2612, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2747, 2), (key2653, 2), (key2938, -1), (key2782, -1), (key2943, 1), (key2667, 1), (key2950, -1), (key2805, -1), (key2831, 1), (key2618, 1), (key2976, 1), (key2702, 1), (key2728, -1), (key2641, -1), (key2904, 1), (key2648, 1), (key2747, -1), (key2653, -1)]

theorem rawRowCheck6377 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form5 = rawRow6377 := by decide +kernel

def row6377 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2640, 1), (key2641, -1), (key2644, -2), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2758, -1), (key2782, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2938, -1), (key2943, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

theorem rowCheck6377 : row6377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6377 := by decide +kernel

theorem rowEval6377 (x : Key → ℝ) : Integer.Sparse.eval row6377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6377, Integer.Sparse.eval_collectBalanced, rawRowCheck6377]

def rawRow6378 : Integer.Sparse Key := [(key2870, -2), (key2860, 1), (key2885, 1), (key2726, -2), (key2640, 1), (key3030, 1), (key2706, 1), (key2732, 1), (key2632, 1), (key3026, 1), (key2644, -2), (key3023, -2), (key2829, 2), (key2794, -1), (key2927, -1), (key2726, 2), (key2640, -1), (key3030, -1), (key2667, -1), (key2943, -1), (key2612, -1), (key2960, -1), (key2653, 2), (key2747, 2), (key2805, -1), (key2950, -1), (key2702, 1), (key2976, 1), (key2782, -1), (key2938, -1), (key2648, 1), (key2904, 1), (key2667, 1), (key2943, 1), (key2653, -1), (key2747, -1), (key2618, 1), (key2831, 1), (key2641, -1), (key2728, -1)]

theorem rawRowCheck6378 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form5 = rawRow6378 := by decide +kernel

def row6378 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, 1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2950, -1), (key2960, -1), (key2976, 1), (key3023, -2), (key3026, 1)]

theorem rowCheck6378 : row6378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6378 := by decide +kernel

theorem rowEval6378 (x : Key → ℝ) : Integer.Sparse.eval row6378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, -2, 2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6378, Integer.Sparse.eval_collectBalanced, rawRowCheck6378]

def rawRow6379 : Integer.Sparse Key := [(key2870, -2), (key2885, 1), (key2860, 1), (key2726, -2), (key3030, 1), (key2640, 1), (key2732, 1), (key2706, 1), (key3026, 1), (key2632, 1), (key3023, -2), (key2644, -2), (key2829, 2), (key2927, -1), (key2794, -1), (key2726, 2), (key3030, -1), (key2640, -1), (key2943, -1), (key2667, -1), (key2960, -1), (key2612, -1), (key2747, 2), (key2653, 2), (key2950, -1), (key2805, -1), (key2976, 1), (key2702, 1), (key2938, -1), (key2782, -1), (key2904, 1), (key2648, 1), (key2943, 1), (key2667, 1), (key2747, -1), (key2653, -1), (key2831, 1), (key2618, 1), (key2728, -1), (key2641, -1)]

theorem rawRowCheck6379 : GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form5 = rawRow6379 := by decide +kernel

def row6379 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, 1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2950, -1), (key2960, -1), (key2976, 1), (key3023, -2), (key3026, 1)]

theorem rowCheck6379 : row6379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6379 := by decide +kernel

theorem rowEval6379 (x : Key → ℝ) : Integer.Sparse.eval row6379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, -1, 2, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6379, Integer.Sparse.eval_collectBalanced, rawRowCheck6379]

def rawRow6380 : Integer.Sparse Key := [(key2885, -2), (key2860, 1), (key2870, 1), (key3030, -2), (key2640, 1), (key2726, 1), (key3023, 1), (key3026, 1), (key2644, 1), (key2732, 1), (key2632, -2), (key2706, -2), (key2927, 2), (key2794, -1), (key2829, -1), (key3030, 2), (key2640, -1), (key2726, -1), (key2747, -1), (key2960, -1), (key2653, -1), (key2943, -1), (key2612, 2), (key2667, 2), (key2897, -1), (key2976, -1), (key2737, 1), (key2950, 1), (key2904, -1), (key2983, -1), (key2628, 1), (key2782, 1), (key2747, 1), (key2960, 1), (key2612, -1), (key2667, -1), (key2641, 1), (key2795, 1), (key2618, -1), (key2673, -1)]

theorem rawRowCheck6380 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form5 = rawRow6380 := by decide +kernel

def row6380 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2943, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key3023, 1), (key3026, 1)]

theorem rowCheck6380 : row6380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6380 := by decide +kernel

theorem rowEval6380 (x : Key → ℝ) : Integer.Sparse.eval row6380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -2, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6380, Integer.Sparse.eval_collectBalanced, rawRowCheck6380]

def rawRow6381 : Integer.Sparse Key := [(key2885, -2), (key2870, 1), (key2860, 1), (key3030, -2), (key2726, 1), (key2640, 1), (key3026, 1), (key3023, 1), (key2732, 1), (key2644, 1), (key2706, -2), (key2632, -2), (key2927, 2), (key2829, -1), (key2794, -1), (key3030, 2), (key2726, -1), (key2640, -1), (key2960, -1), (key2747, -1), (key2943, -1), (key2653, -1), (key2667, 2), (key2612, 2), (key2976, -1), (key2897, -1), (key2950, 1), (key2737, 1), (key2983, -1), (key2904, -1), (key2782, 1), (key2628, 1), (key2960, 1), (key2747, 1), (key2667, -1), (key2612, -1), (key2795, 1), (key2641, 1), (key2673, -1), (key2618, -1)]

theorem rawRowCheck6381 : GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form5 = rawRow6381 := by decide +kernel

def row6381 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2943, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key3023, 1), (key3026, 1)]

theorem rowCheck6381 : row6381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6381 := by decide +kernel

theorem rowEval6381 (x : Key → ℝ) : Integer.Sparse.eval row6381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 0, 2, -1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6381, Integer.Sparse.eval_collectBalanced, rawRowCheck6381]

def rawRow6382 : Integer.Sparse Key := [(key3023, -2), (key3026, 1), (key3030, 1), (key2644, -2), (key2732, 1), (key2885, 1), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, -2), (key2870, -2), (key3010, 2), (key3017, -1), (key3030, -1), (key2660, 2), (key2758, -1), (key2927, -1), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, 2), (key2829, 2), (key2728, -1), (key2747, -1), (key2831, 1), (key2904, 1), (key2641, -1), (key2653, -1), (key2943, 1), (key2976, 1), (key2618, 1), (key2648, 1), (key2938, -1), (key2950, -1), (key2667, 1), (key2702, 1), (key2782, -1), (key2805, -1)]

theorem rawRowCheck6382 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form5 = rawRow6382 := by decide +kernel

def row6382 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, -1), (key2758, -1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, -1), (key2976, 1), (key3010, 2), (key3017, -1), (key3023, -2), (key3026, 1)]

theorem rowCheck6382 : row6382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6382 := by decide +kernel

theorem rowEval6382 (x : Key → ℝ) : Integer.Sparse.eval row6382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6382, Integer.Sparse.eval_collectBalanced, rawRowCheck6382]

def rawRow6383 : Integer.Sparse Key := [(key3023, -2), (key3030, 1), (key3026, 1), (key2644, -2), (key2885, 1), (key2732, 1), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, -2), (key2726, -2), (key3010, 2), (key3030, -1), (key3017, -1), (key2660, 2), (key2927, -1), (key2758, -1), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, 2), (key2726, 2), (key2747, -1), (key2728, -1), (key2904, 1), (key2831, 1), (key2653, -1), (key2641, -1), (key2976, 1), (key2943, 1), (key2648, 1), (key2618, 1), (key2950, -1), (key2938, -1), (key2702, 1), (key2667, 1), (key2805, -1), (key2782, -1)]

theorem rawRowCheck6383 : GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form5 = rawRow6383 := by decide +kernel

def row6383 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, -1), (key2758, -1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, -1), (key2976, 1), (key3010, 2), (key3017, -1), (key3023, -2), (key3026, 1)]

theorem rowCheck6383 : row6383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6383 := by decide +kernel

theorem rowEval6383 (x : Key → ℝ) : Integer.Sparse.eval row6383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6383, Integer.Sparse.eval_collectBalanced, rawRowCheck6383]

def rawRow6384 : Integer.Sparse Key := [(key3030, -2), (key3023, 1), (key3026, 1), (key2885, -2), (key2644, 1), (key2732, 1), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, -2), (key2706, -2), (key3030, 2), (key3010, -1), (key3017, -1), (key2927, 2), (key2660, -1), (key2758, -1), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, 2), (key2671, 2), (key2904, -1), (key2983, -1), (key2747, 1), (key2960, 1), (key2897, -1), (key2976, -1), (key2641, 1), (key2795, 1), (key2737, 1), (key2950, 1), (key2618, -1), (key2673, -1), (key2628, 1), (key2782, 1), (key2612, -1), (key2667, -1)]

theorem rawRowCheck6384 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form5 = rawRow6384 := by decide +kernel

def row6384 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2747, 1), (key2758, -1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, -1), (key3023, 1), (key3026, 1)]

theorem rowCheck6384 : row6384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6384 := by decide +kernel

theorem rowEval6384 (x : Key → ℝ) : Integer.Sparse.eval row6384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6384, Integer.Sparse.eval_collectBalanced, rawRowCheck6384]

def rawRow6385 : Integer.Sparse Key := [(key3030, -2), (key3026, 1), (key3023, 1), (key2885, -2), (key2732, 1), (key2644, 1), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, -2), (key2632, -2), (key3030, 2), (key3017, -1), (key3010, -1), (key2927, 2), (key2758, -1), (key2660, -1), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, 2), (key2616, 2), (key2983, -1), (key2904, -1), (key2960, 1), (key2747, 1), (key2976, -1), (key2897, -1), (key2795, 1), (key2641, 1), (key2950, 1), (key2737, 1), (key2673, -1), (key2618, -1), (key2782, 1), (key2628, 1), (key2667, -1), (key2612, -1)]

theorem rawRowCheck6385 : GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form5 = rawRow6385 := by decide +kernel

def row6385 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2747, 1), (key2758, -1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, -1), (key3023, 1), (key3026, 1)]

theorem rowCheck6385 : row6385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6385 := by decide +kernel

theorem rowEval6385 (x : Key → ℝ) : Integer.Sparse.eval row6385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6385, Integer.Sparse.eval_collectBalanced, rawRowCheck6385]

def rawRow6386 : Integer.Sparse Key := [(key2658, -2), (key2660, 1), (key2660, 1), (key2753, -2), (key2920, 1), (key2920, 1), (key2758, 1), (key2758, 1), (key2923, 1), (key2923, 1), (key2927, -2), (key2927, -2), (key2621, 2), (key2644, -1), (key2644, -1), (key2676, 2), (key2798, -1), (key2798, -1), (key2732, -1), (key2732, -1), (key2835, -1), (key2835, -1), (key2885, 2), (key2885, 2), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2671, -1), (key2671, -1), (key2794, 1), (key2794, 1), (key2706, 1), (key2706, 1), (key2860, -1), (key2860, -1), (key2829, 1), (key2829, 1), (key2870, -1), (key2870, -1)]

theorem rawRowCheck6386 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form5 = rawRow6386 := by decide +kernel

def row6386 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

theorem rowCheck6386 : row6386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6386 := by decide +kernel

theorem rowEval6386 (x : Key → ℝ) : Integer.Sparse.eval row6386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6386, Integer.Sparse.eval_collectBalanced, rawRowCheck6386]

def rawRow6387 : Integer.Sparse Key := [(key2660, -2), (key2658, 1), (key2660, 1), (key2920, -2), (key2753, 1), (key2920, 1), (key2923, 1), (key2927, 1), (key2758, 1), (key2927, 1), (key2758, -2), (key2923, -2), (key2644, 2), (key2621, -1), (key2644, -1), (key2798, 2), (key2676, -1), (key2798, -1), (key2835, -1), (key2885, -1), (key2732, -1), (key2885, -1), (key2732, 2), (key2835, 2), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2786, -1), (key2794, -1), (key2671, 1), (key2786, 1), (key2809, 1), (key2860, 1), (key2706, -1), (key2809, -1), (key2726, 1), (key2870, 1), (key2726, -1), (key2829, -1)]

theorem rawRowCheck6387 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form5 = rawRow6387 := by decide +kernel

def row6387 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6387 : row6387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6387 := by decide +kernel

theorem rowEval6387 (x : Key → ℝ) : Integer.Sparse.eval row6387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6387, Integer.Sparse.eval_collectBalanced, rawRowCheck6387]

def rawRow6388 : Integer.Sparse Key := [(key2660, -2), (key2660, 1), (key2658, 1), (key2920, -2), (key2920, 1), (key2753, 1), (key2927, 1), (key2923, 1), (key2927, 1), (key2758, 1), (key2923, -2), (key2758, -2), (key2644, 2), (key2644, -1), (key2621, -1), (key2798, 2), (key2798, -1), (key2676, -1), (key2885, -1), (key2835, -1), (key2885, -1), (key2732, -1), (key2835, 2), (key2732, 2), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2794, -1), (key2786, -1), (key2786, 1), (key2671, 1), (key2860, 1), (key2809, 1), (key2809, -1), (key2706, -1), (key2870, 1), (key2726, 1), (key2829, -1), (key2726, -1)]

theorem rawRowCheck6388 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form5 = rawRow6388 := by decide +kernel

def row6388 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6388 : row6388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6388 := by decide +kernel

theorem rowEval6388 (x : Key → ℝ) : Integer.Sparse.eval row6388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6388, Integer.Sparse.eval_collectBalanced, rawRowCheck6388]

def rawRow6389 : Integer.Sparse Key := [(key2753, -2), (key2758, 1), (key2758, 1), (key2658, -2), (key2923, 1), (key2923, 1), (key2660, 1), (key2660, 1), (key2920, 1), (key2920, 1), (key2927, -2), (key2927, -2), (key2676, 2), (key2732, -1), (key2732, -1), (key2621, 2), (key2835, -1), (key2835, -1), (key2644, -1), (key2644, -1), (key2798, -1), (key2798, -1), (key2885, 2), (key2885, 2), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key2616, -1), (key2616, -1), (key2829, 1), (key2829, 1), (key2632, 1), (key2632, 1), (key2870, -1), (key2870, -1), (key2794, 1), (key2794, 1), (key2860, -1), (key2860, -1)]

theorem rawRowCheck6389 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form5 = rawRow6389 := by decide +kernel

def row6389 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

theorem rowCheck6389 : row6389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6389 := by decide +kernel

theorem rowEval6389 (x : Key → ℝ) : Integer.Sparse.eval row6389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6389, Integer.Sparse.eval_collectBalanced, rawRowCheck6389]

def rawRow6390 : Integer.Sparse Key := [(key2758, -2), (key2753, 1), (key2758, 1), (key2923, -2), (key2658, 1), (key2923, 1), (key2920, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, -2), (key2920, -2), (key2732, 2), (key2676, -1), (key2732, -1), (key2835, 2), (key2621, -1), (key2835, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, 2), (key2798, 2), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key2809, -1), (key2829, -1), (key2616, 1), (key2809, 1), (key2786, 1), (key2870, 1), (key2632, -1), (key2786, -1), (key2640, 1), (key2860, 1), (key2640, -1), (key2794, -1)]

theorem rawRowCheck6390 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form5 = rawRow6390 := by decide +kernel

def row6390 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6390 : row6390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6390 := by decide +kernel

theorem rowEval6390 (x : Key → ℝ) : Integer.Sparse.eval row6390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6390, Integer.Sparse.eval_collectBalanced, rawRowCheck6390]

def rawRow6391 : Integer.Sparse Key := [(key2758, -2), (key2758, 1), (key2753, 1), (key2923, -2), (key2923, 1), (key2658, 1), (key2927, 1), (key2920, 1), (key2927, 1), (key2660, 1), (key2920, -2), (key2660, -2), (key2732, 2), (key2732, -1), (key2676, -1), (key2835, 2), (key2835, -1), (key2621, -1), (key2885, -1), (key2798, -1), (key2885, -1), (key2644, -1), (key2798, 2), (key2644, 2), (key2726, -1), (key2706, -1), (key2726, 1), (key2671, 1), (key2829, -1), (key2809, -1), (key2809, 1), (key2616, 1), (key2870, 1), (key2786, 1), (key2786, -1), (key2632, -1), (key2860, 1), (key2640, 1), (key2794, -1), (key2640, -1)]

theorem rawRowCheck6391 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form5 = rawRow6391 := by decide +kernel

def row6391 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6391 : row6391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6391 := by decide +kernel

theorem rowEval6391 (x : Key → ℝ) : Integer.Sparse.eval row6391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6391, Integer.Sparse.eval_collectBalanced, rawRowCheck6391]

def rawRow6392 : Integer.Sparse Key := [(key2920, -2), (key2923, 1), (key2927, 1), (key2660, -2), (key2758, 1), (key2927, 1), (key2658, 1), (key2660, 1), (key2753, 1), (key2920, 1), (key2758, -2), (key2923, -2), (key2798, 2), (key2835, -1), (key2885, -1), (key2644, 2), (key2732, -1), (key2885, -1), (key2621, -1), (key2644, -1), (key2676, -1), (key2798, -1), (key2732, 2), (key2835, 2), (key2786, -1), (key2794, -1), (key2809, 1), (key2860, 1), (key2632, -1), (key2640, -1), (key2726, 1), (key2870, 1), (key2616, 1), (key2640, 1), (key2726, -1), (key2829, -1), (key2671, 1), (key2786, 1), (key2706, -1), (key2809, -1)]

theorem rawRowCheck6392 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form5 = rawRow6392 := by decide +kernel

def row6392 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6392 : row6392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6392 := by decide +kernel

theorem rowEval6392 (x : Key → ℝ) : Integer.Sparse.eval row6392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, -1, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6392, Integer.Sparse.eval_collectBalanced, rawRowCheck6392]

def rawRow6393 : Integer.Sparse Key := [(key2920, -2), (key2927, 1), (key2923, 1), (key2660, -2), (key2927, 1), (key2758, 1), (key2660, 1), (key2658, 1), (key2920, 1), (key2753, 1), (key2923, -2), (key2758, -2), (key2798, 2), (key2885, -1), (key2835, -1), (key2644, 2), (key2885, -1), (key2732, -1), (key2644, -1), (key2621, -1), (key2798, -1), (key2676, -1), (key2835, 2), (key2732, 2), (key2794, -1), (key2786, -1), (key2860, 1), (key2809, 1), (key2640, -1), (key2632, -1), (key2870, 1), (key2726, 1), (key2640, 1), (key2616, 1), (key2829, -1), (key2726, -1), (key2786, 1), (key2671, 1), (key2809, -1), (key2706, -1)]

theorem rawRowCheck6393 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form5 = rawRow6393 := by decide +kernel

def row6393 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6393 : row6393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6393 := by decide +kernel

theorem rowEval6393 (x : Key → ℝ) : Integer.Sparse.eval row6393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -2, 0, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6393, Integer.Sparse.eval_collectBalanced, rawRowCheck6393]

def rawRow6394 : Integer.Sparse Key := [(key2923, -2), (key2920, 1), (key2927, 1), (key2758, -2), (key2660, 1), (key2927, 1), (key2753, 1), (key2758, 1), (key2658, 1), (key2923, 1), (key2660, -2), (key2920, -2), (key2835, 2), (key2798, -1), (key2885, -1), (key2732, 2), (key2644, -1), (key2885, -1), (key2676, -1), (key2732, -1), (key2621, -1), (key2835, -1), (key2644, 2), (key2798, 2), (key2809, -1), (key2829, -1), (key2786, 1), (key2870, 1), (key2706, -1), (key2726, -1), (key2640, 1), (key2860, 1), (key2671, 1), (key2726, 1), (key2640, -1), (key2794, -1), (key2616, 1), (key2809, 1), (key2632, -1), (key2786, -1)]

theorem rawRowCheck6394 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form5 = rawRow6394 := by decide +kernel

def row6394 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6394 : row6394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6394 := by decide +kernel

theorem rowEval6394 (x : Key → ℝ) : Integer.Sparse.eval row6394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, -2, 0] GramFunctions.Block2.form5) x := by
  rw [rowCheck6394, Integer.Sparse.eval_collectBalanced, rawRowCheck6394]

def rawRow6395 : Integer.Sparse Key := [(key2923, -2), (key2927, 1), (key2920, 1), (key2758, -2), (key2927, 1), (key2660, 1), (key2758, 1), (key2753, 1), (key2923, 1), (key2658, 1), (key2920, -2), (key2660, -2), (key2835, 2), (key2885, -1), (key2798, -1), (key2732, 2), (key2885, -1), (key2644, -1), (key2732, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2798, 2), (key2644, 2), (key2829, -1), (key2809, -1), (key2870, 1), (key2786, 1), (key2726, -1), (key2706, -1), (key2860, 1), (key2640, 1), (key2726, 1), (key2671, 1), (key2794, -1), (key2640, -1), (key2809, 1), (key2616, 1), (key2786, -1), (key2632, -1)]

theorem rawRowCheck6395 : GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form5 = rawRow6395 := by decide +kernel

def row6395 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

theorem rowCheck6395 : row6395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6395 := by decide +kernel

theorem rowEval6395 (x : Key → ℝ) : Integer.Sparse.eval row6395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, -1, 0, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6395, Integer.Sparse.eval_collectBalanced, rawRowCheck6395]

def rawRow6396 : Integer.Sparse Key := [(key2927, -2), (key2920, 1), (key2923, 1), (key2927, -2), (key2660, 1), (key2758, 1), (key2920, 1), (key2923, 1), (key2660, 1), (key2758, 1), (key2658, -2), (key2753, -2), (key2885, 2), (key2798, -1), (key2835, -1), (key2885, 2), (key2644, -1), (key2732, -1), (key2798, -1), (key2835, -1), (key2644, -1), (key2732, -1), (key2621, 2), (key2676, 2), (key2860, -1), (key2870, -1), (key2794, 1), (key2829, 1), (key2860, -1), (key2870, -1), (key2632, 1), (key2706, 1), (key2794, 1), (key2829, 1), (key2616, -1), (key2671, -1), (key2632, 1), (key2706, 1), (key2616, -1), (key2671, -1)]

theorem rawRowCheck6396 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form5 = rawRow6396 := by decide +kernel

def row6396 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

theorem rowCheck6396 : row6396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6396 := by decide +kernel

theorem rowEval6396 (x : Key → ℝ) : Integer.Sparse.eval row6396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -2, -1] GramFunctions.Block2.form5) x := by
  rw [rowCheck6396, Integer.Sparse.eval_collectBalanced, rawRowCheck6396]

def rawRow6397 : Integer.Sparse Key := [(key2927, -2), (key2923, 1), (key2920, 1), (key2927, -2), (key2758, 1), (key2660, 1), (key2923, 1), (key2920, 1), (key2758, 1), (key2660, 1), (key2753, -2), (key2658, -2), (key2885, 2), (key2835, -1), (key2798, -1), (key2885, 2), (key2732, -1), (key2644, -1), (key2835, -1), (key2798, -1), (key2732, -1), (key2644, -1), (key2676, 2), (key2621, 2), (key2870, -1), (key2860, -1), (key2829, 1), (key2794, 1), (key2870, -1), (key2860, -1), (key2706, 1), (key2632, 1), (key2829, 1), (key2794, 1), (key2671, -1), (key2616, -1), (key2706, 1), (key2632, 1), (key2671, -1), (key2616, -1)]

theorem rawRowCheck6397 : GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form5 = rawRow6397 := by decide +kernel

def row6397 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

theorem rowCheck6397 : row6397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6397 := by decide +kernel

theorem rowEval6397 (x : Key → ℝ) : Integer.Sparse.eval row6397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, -1, -2] GramFunctions.Block2.form5) x := by
  rw [rowCheck6397, Integer.Sparse.eval_collectBalanced, rawRowCheck6397]

def rawRow6398 : Integer.Sparse Key := [(key1387, -1), (key1393, -1), (key1393, 2), (key1420, -1), (key1426, -1), (key1420, 2), (key1472, 2), (key1426, -1), (key1472, -1), (key1444, 2), (key1444, -1), (key1480, -1), (key1292, 1), (key1298, 1), (key1298, -2), (key1569, 1), (key1575, 1), (key1569, -2), (key1903, -2), (key1575, 1), (key1903, 1), (key1593, -2), (key1593, 1), (key1911, 1), (key1312, -1), (key1351, -1), (key1318, 1), (key1351, 1), (key1542, 1), (key1896, 1), (key1548, -1), (key1896, -1), (key1618, -1), (key1681, -1), (key1618, 1), (key1918, 1), (key1633, 1), (key1689, 1), (key1633, -1), (key1926, -1)]

theorem rawRowCheck6398 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form6 = rawRow6398 := by decide +kernel

def row6398 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6398 : row6398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6398 := by decide +kernel

theorem rowEval6398 (x : Key → ℝ) : Integer.Sparse.eval row6398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 0, 2] GramFunctions.Block2.form6) x := by
  rw [rowCheck6398, Integer.Sparse.eval_collectBalanced, rawRowCheck6398]

def rawRow6399 : Integer.Sparse Key := [(key1393, -1), (key1387, -1), (key1393, 2), (key1426, -1), (key1420, -1), (key1472, 2), (key1420, 2), (key1472, -1), (key1426, -1), (key1444, 2), (key1480, -1), (key1444, -1), (key1298, 1), (key1292, 1), (key1298, -2), (key1575, 1), (key1569, 1), (key1903, -2), (key1569, -2), (key1903, 1), (key1575, 1), (key1593, -2), (key1911, 1), (key1593, 1), (key1351, -1), (key1312, -1), (key1351, 1), (key1318, 1), (key1896, 1), (key1542, 1), (key1896, -1), (key1548, -1), (key1681, -1), (key1618, -1), (key1918, 1), (key1618, 1), (key1689, 1), (key1633, 1), (key1926, -1), (key1633, -1)]

theorem rawRowCheck6399 : GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form6 = rawRow6399 := by decide +kernel

def row6399 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1318, 1), (key1387, -1), (key1393, 1), (key1420, 1), (key1426, -2), (key1444, 1), (key1472, 1), (key1480, -1), (key1542, 1), (key1548, -1), (key1569, -1), (key1575, 2), (key1593, -1), (key1681, -1), (key1689, 1), (key1903, -1), (key1911, 1), (key1918, 1), (key1926, -1)]

theorem rowCheck6399 : row6399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow6399 := by decide +kernel

theorem rowEval6399 (x : Key → ℝ) : Integer.Sparse.eval row6399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 0, 2, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6399, Integer.Sparse.eval_collectBalanced, rawRowCheck6399]

end MUB6.Certificate.GramRows

end OAI
