import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Choosing splitting smallness before the geometric neighborhood -/

namespace RegularPointCoordinates

/-- A single positive tolerance enforces the mean-comparison and cumulative
absorption thresholds. All constants are fixed before the map and radius. -/
theorem exists_cumulative_error_tolerance {a C W M cap : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hW : 0 ≤ W) (hM : 0 ≤ M) (hcap : 0 < cap) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ cap ∧ ε ≤ 1 ∧ ∀ e : ℝ, 0 ≤ e → e ≤ ε →
      a * e ≤ 1 / 64 ∧ 2 * C * W * (M * e) ≤ 1 / 2 := by
  let T := 1 + 64 * a + 4 * C * W * M
  have hT : 0 < T := by dsimp only [T]; positivity
  let ε := min cap (min 1 T⁻¹)
  have hε : 0 < ε := lt_min hcap (lt_min zero_lt_one (inv_pos.mpr hT))
  refine ⟨ε, hε, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro e he heε
  have heT : e ≤ T⁻¹ := heε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht := mul_le_mul_of_nonneg_left heT hT.le
  rw [mul_inv_cancel₀ hT.ne'] at ht
  dsimp only [T] at ht
  have hm : 0 ≤ 4 * C * W * M * e := by positivity
  have ham : 0 ≤ 64 * a * e := by positivity
  constructor
  · nlinarith only [ht, hm, he]
  · nlinarith only [ht, ham, he]

end RegularPointCoordinates

end OAI
