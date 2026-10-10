import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.Foundation

theorem log_three_upper : Real.log 3 < (1098612289 : ℝ) / 10 ^ 9 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 16)
  norm_num [Finset.sum_range_succ, Nat.factorial]

end MatrixMultiplication.Foundation

end OAI
