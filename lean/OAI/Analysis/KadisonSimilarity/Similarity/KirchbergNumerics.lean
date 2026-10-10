import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! The scalar cancellation in Kirchberg, J. Operator Theory 36 (1996),
page 61. The analytic estimate preceding it is kept separate. -/

namespace KadisonSimilarity

/-- Cancellation of the nonzero `K - 1` in Kirchberg's integral estimate. -/
theorem log_le_of_kirchberg_inequality {K D : ℝ} (hK : 1 < K)
    (h : K ≤ 1 + D * ((K - 1) / Real.log K)) : Real.log K ≤ D := by
  have hl : 0 < Real.log K := Real.log_pos hK
  have hh : K - 1 ≤ D * ((K - 1) / Real.log K) := by linarith
  have hm := (le_div_iff₀ hl).mp (show K - 1 ≤ D * (K - 1) / Real.log K by
    simpa only [mul_div_assoc] using hh)
  nlinarith

/-- The estimate also covers completely contractive representations. -/
theorem le_exp_of_kirchberg_inequality {K D : ℝ} (hD : 0 ≤ D)
    (h : 1 < K → K ≤ 1 + D * ((K - 1) / Real.log K)) :
    K ≤ Real.exp D := by
  by_cases hK : 1 < K
  · exact (Real.log_le_iff_le_exp (by linarith : 0 < K)).mp
      (log_le_of_kirchberg_inequality hK (h hK))
  · exact (le_of_not_gt hK).trans (Real.one_le_exp hD)

end KadisonSimilarity

end OAI
