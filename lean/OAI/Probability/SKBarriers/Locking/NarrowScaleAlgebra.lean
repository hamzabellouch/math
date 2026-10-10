import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleFiniteExpansion

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def narrowExpansionDenominator (β : ℝ) : ℝ := 1+24*β^2+288*β^4

def narrowExpansionErrorConstant (β : ℝ) : ℝ :=
  (12*(susceptibilityLipschitzConstant:ℝ)+64)*(narrowExpansionDenominator β)^2

theorem narrowExpansionDenominator_ge_one (β : ℝ) : 1≤ narrowExpansionDenominator β := by
  unfold narrowExpansionDenominator; nlinarith [sq_nonneg β,sq_nonneg (β^2)]

theorem narrowExpansionErrorConstant_pos (β : ℝ) : 0< narrowExpansionErrorConstant β := by
  have hd : 0< narrowExpansionDenominator β := lt_of_lt_of_le zero_lt_one (narrowExpansionDenominator_ge_one β)
  unfold narrowExpansionErrorConstant
  positivity

theorem narrowExpansion_smallness (β : ℝ) {h a θ : ℝ} (hh : 0< h) (hh1 : h≤1)
    (ha : 0≤ a) (hθ : 0≤θ) (haθ : a+θ=1) :
    (h/narrowExpansionDenominator β)*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2 := by
  have ha1 : a≤1 := by linarith
  have hθ1 : θ≤1 := by linarith
  have hK : 2*a^2+θ^2≤3 := by nlinarith [sq_nonneg (1-a),sq_nonneg (1-θ)]
  have hscore : (5*a+θ)^2≤36 := by nlinarith [sq_nonneg (6-(5*a+θ))]
  have hd : 0< narrowExpansionDenominator β := lt_of_lt_of_le zero_lt_one (narrowExpansionDenominator_ge_one β)
  have HP : 4*β^2*(2*a^2+θ^2)+h*(2*β^2*(5*a+θ))^2≤12*β^2+144*β^4 := by
    have HK := mul_le_mul_of_nonneg_left hK (show 0≤4*β^2 by positivity)
    have HS := mul_le_mul_of_nonneg_left hscore (show 0≤4*β^4 by positivity)
    have HH := mul_le_mul_of_nonneg_left hh1 (show 0≤(2*β^2*(5*a+θ))^2 by positivity)
    nlinarith only [HK,HS,HH]
  have HE : (h/narrowExpansionDenominator β)*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)=
      (4*β^2*(2*a^2+θ^2)+h*(2*β^2*(5*a+θ))^2)/narrowExpansionDenominator β := by field_simp
  rw [HE,div_le_iff₀ hd]
  dsimp only [narrowExpansionDenominator]
  linarith

theorem tripleExpansionConstant_scaled_bound (β : ℝ) {h : ℝ} (hh : 0< h) (hh1 : h≤1) :
    tripleExpansionConstant (h/narrowExpansionDenominator β)≤ narrowExpansionErrorConstant β/h^2 := by
  have hd1 := narrowExpansionDenominator_ge_one β
  have hd : 0< narrowExpansionDenominator β := lt_of_lt_of_le zero_lt_one hd1
  have hL : 0≤(susceptibilityLipschitzConstant:ℝ) := NNReal.coe_nonneg _
  have hsq : h^2≤(narrowExpansionDenominator β)^2 := by nlinarith
  have HE : tripleExpansionConstant (h/narrowExpansionDenominator β)*h^2=
      4*(susceptibilityLipschitzConstant:ℝ)*h^2+(8*(susceptibilityLipschitzConstant:ℝ)+64)*(narrowExpansionDenominator β)^2 := by
    unfold tripleExpansionConstant
    field_simp
    ring
  rw [le_div_iff₀ (sq_pos_of_pos hh),HE]
  unfold narrowExpansionErrorConstant
  nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤4*(susceptibilityLipschitzConstant:ℝ) by positivity)]

end SK.Analytic

end
end

end OAI
