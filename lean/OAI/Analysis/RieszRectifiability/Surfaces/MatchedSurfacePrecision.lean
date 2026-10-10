import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaceModel

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem exists_matched_surface_precision (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 72057594037927936 ∧
      activeProjectionError d ε ≤ 1 / 4096 ∧
      281474976710656 * (ε + activeProjectionError d ε) ≤ δ := by
  let C : ℝ := 2048 + 1048576 * (9 : ℝ) ^ d
  have hC : 0 < C := by dsimp only [C]; positivity
  let ε : ℝ := min (1 / 72057594037927936) (min (1 / (4096 * C))
    (δ / (281474976710656 * (1 + C))))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have h₁ : ε ≤ 1 / (4096 * C) := (min_le_right _ _).trans (min_le_left _ _)
  have h₂ : ε ≤ δ / (281474976710656 * (1 + C)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, min_le_left _ _, ?_, ?_⟩
  · change C * ε ≤ 1 / 4096
    have heq : C * (1 / (4096 * C)) = 1 / 4096 := by field_simp
    exact (mul_le_mul_of_nonneg_left h₁ hC.le).trans_eq heq
  · change 281474976710656 * (ε + C * ε) ≤ δ
    have h := (le_div_iff₀ (by positivity : 0 < 281474976710656 * (1 + C))).mp h₂
    nlinarith

end

end RieszRectifiability

end OAI
