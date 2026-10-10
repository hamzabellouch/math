import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.HeightTailSplit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def heightTailLinearCoefficient (m : ℕ) (C B R b : ℝ) (K : ℝ≥0) (W : ℝ) : ℝ :=
  (B / R) / (1 - b / 2) + ((K : ℝ) + W / R) * (2 * (C * 2 ^ m))

theorem heightTailLinearCoefficient_nonneg (m : ℕ) (C B R b : ℝ) (K : ℝ≥0) (W : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 < R) (hb : b < 2) (hW : 0 ≤ W) :
    0 ≤ heightTailLinearCoefficient m C B R b K W := by
  have hden : 0 < 1 - b / 2 := by linarith
  unfold heightTailLinearCoefficient
  positivity

theorem weighted_height_tail_linear_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (δ b W : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hW : |w a| ≤ W) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        heightTailLinearCoefficient m C B R b K W * δ := by
  obtain ⟨hi, hbound⟩ := improved_weighted_height_tail_bound m C B μ hg hCB w K hw a R hR N
    δ b hδ hb0 hb2 hsecond
  have hC := hg.1
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hW
  have hT : R ≤ R * (2 : ℝ) ^ N := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  have hTpos : 0 < R * (2 : ℝ) ^ N := by positivity
  have hcenter : |w a| / (R * 2 ^ N) ≤ W / R :=
    (div_le_div_of_nonneg_right hW hTpos.le).trans
      (div_le_div_of_nonneg_left hW0 hR hT)
  have htail : 2 * (C * 2 ^ m / (R * 2 ^ N)) ≤ (2 * (C * 2 ^ m)) * δ := by
    simpa only [div_eq_mul_inv, mul_assoc] using!
      mul_le_mul_of_nonneg_left hlast (show 0 ≤ 2 * (C * 2 ^ m) by positivity)
  refine ⟨hi, hbound.trans ?_⟩
  calc
    _ ≤ (B * δ / R) / (1 - b / 2) +
        ((K : ℝ) + W / R) * ((2 * (C * 2 ^ m)) * δ) :=
      add_le_add le_rfl (mul_le_mul (add_le_add le_rfl hcenter) htail (by positivity) (by positivity))
    _ = _ := by unfold heightTailLinearCoefficient; ring

end

end RieszRectifiability

end OAI
