import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ProjectionStopShadowMass
import OAI.Analysis.RieszRectifiability.Surfaces.NativeCoreAreaFraction

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem exists_projection_region_thresholds (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ ∃ σ : ℝ, 0 < σ ∧
      σ + κ ≤ 1 ∧ 2048 * σ * (κ + 1) ≤ κ ∧
      projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G := by
  let θ := nativeCoreAreaFraction n G
  have hθ : 0 < θ := (nativeCoreAreaFraction_pos_le_half n G hG).1
  let B : ℝ := ((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
    (2 : ℝ) ^ n * (C * (8 : ℝ) ^ n)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let κ : ℝ := min (1 / 4) (θ / (4 * (B + 1)))
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκquarter : κ ≤ 1 / 4 := min_le_left _ _
  have hκbound : κ * (4 * (B + 1)) ≤ θ :=
    (le_div_iff₀ (by positivity : 0 < 4 * (B + 1))).mp (min_le_right _ _)
  let σ : ℝ := κ / (4096 * (κ + 1))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσeq : σ * (4096 * (κ + 1)) = κ := by
    dsimp only [σ]
    exact div_mul_cancel₀ _ (by positivity)
  have hσκ : σ ≤ κ := by nlinarith [mul_pos hσ hκ]
  refine ⟨κ, hκ, hκquarter, σ, hσ, ?_, ?_, ?_⟩
  · linarith
  · nlinarith
  · have hsum : B * (σ + κ) ≤ B * (κ + κ) :=
      mul_le_mul_of_nonneg_left (add_le_add hσκ le_rfl) hB
    have hBκ : 0 ≤ B * κ := mul_nonneg hB hκ.le
    have hid : projectionStopShadowConstant n C σ κ = B * (σ + κ) := by
      dsimp only [projectionStopShadowConstant, B]
      ring
    rw [hid]
    change B * (σ + κ) ≤ θ
    nlinarith

end

end RieszRectifiability

end OAI
