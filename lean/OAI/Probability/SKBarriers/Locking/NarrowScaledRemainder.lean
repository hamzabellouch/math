import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowScaleAlgebra

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrow_scaled_remainder (β : ℝ) {ρ δ : ℝ} (hρ : 0<ρ) (hρ1 : ρ≤1)
    (hδ : |δ|≤2*ρ^20) :
    tripleExpansionConstant (ρ^8/narrowExpansionDenominator β)*|δ|+
      β^2*δ^2*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤
      (2*narrowExpansionErrorConstant β+36*β^2)*ρ^4 := by
  have hh : 0<ρ^8 := pow_pos hρ _
  have hh1 : ρ^8≤1 := pow_le_one₀ hρ.le hρ1
  have hθ1 : ρ^2≤1 := pow_le_one₀ hρ.le hρ1
  have ha0 : 0≤1-ρ^2 := sub_nonneg.mpr hθ1
  have ha1 : 1-ρ^2≤1 := by nlinarith [sq_nonneg ρ]
  have hK0 : 0≤(2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8 := by positivity
  have hK : (2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8≤3/ρ^8 := by
    apply div_le_div_of_nonneg_right _ hh.le
    nlinarith [sq_nonneg (1-(1-ρ^2)),sq_nonneg (1-ρ^2)]
  have hK2 : ((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤(3/ρ^8)^2 := by
    exact (sq_le_sq₀ hK0 (by positivity)).mpr hK
  have hδ2 : δ^2≤4*ρ^40 := by
    calc
      _ = |δ|^2 := (sq_abs _).symm
      _ ≤ (2*ρ^20)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hδ
      _ = _ := by ring
  have hE := tripleExpansionConstant_scaled_bound β hh hh1
  have hE0 : 0≤narrowExpansionErrorConstant β/(ρ^8)^2 := by have := (narrowExpansionErrorConstant_pos β).le; positivity
  have H₁ : tripleExpansionConstant (ρ^8/narrowExpansionDenominator β)*|δ|≤2*narrowExpansionErrorConstant β*ρ^4 := by
    calc
      _ ≤ (narrowExpansionErrorConstant β/(ρ^8)^2)*(2*ρ^20) := mul_le_mul hE hδ (abs_nonneg _) hE0
      _ = _ := by field_simp
  have H₂ : β^2*δ^2*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤36*β^2*ρ^4 := by
    calc
      _ ≤ β^2*(4*ρ^40)*(3/ρ^8)^2 := mul_le_mul (mul_le_mul_of_nonneg_left hδ2 (sq_nonneg β)) hK2 (sq_nonneg _) (by positivity)
      _ = 36*β^2*ρ^24 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 (by decide : 4≤24)) (by positivity)
  linarith

end SK.Analytic

end
end

end OAI
