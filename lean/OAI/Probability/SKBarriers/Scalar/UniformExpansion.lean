import Mathlib
import OAI.Probability.SKBarriers.Gaussian.ExpExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

lemma abs_cube_le_one_add_fourth (y : ℝ) : |y|^3 ≤ 1+y^4 := by
  have hfour : y^4=|y|^4 := by calc
    y^4 = (y^2)^2 := by ring
    _ = (|y|^2)^2 := by rw [sq_abs]
    _ = |y|^4 := by ring
  rw [hfour]
  have ha := abs_nonneg y
  rcases le_total |y| 1 with h|h
  · have H := pow_le_pow_left₀ ha h 3
    norm_num at H
    nlinarith [pow_nonneg ha 4]
  · have H := mul_le_mul_of_nonneg_right h (pow_nonneg ha 3)
    nlinarith

lemma cube_integrable_of_exp_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) {c : ℝ} (hc : 0<c)
    (hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ) :
    Integrable (fun z => |Y z|^3) μ ∧
    (∫ z, |Y z|^3 ∂μ) ≤ (1+2/c^2)*(∫ z, Real.exp (c*(Y z)^2) ∂μ) := by
  have hb (z) : |Y z|^3 ≤ (1+2/c^2)*Real.exp (c*(Y z)^2) := by
    have H := fourth_pow_le_exp_square hc (Y z)
    have HE := Real.one_le_exp (mul_nonneg hc.le (sq_nonneg (Y z)))
    have HY := abs_cube_le_one_add_fourth (Y z)
    nlinarith
  have hi : Integrable (fun z => |Y z|^3) μ :=
    (hE.const_mul (1+2/c^2)).mono' ((continuous_abs.comp_aestronglyMeasurable hY).pow 3) (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg (Y z)) 3)] using hb z))
  refine ⟨hi,?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi (hE.const_mul _) hb

theorem log_integral_exp_cubic_expansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y Δ A : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (hΔ : Integrable Δ μ)
    (hA : Integrable (fun z => A z*(Y z)^2) μ)
    {c δ M B : ℝ} (hc : 0<c) (hδ : 4*δ^2 ≤ c) (hδ1 : |δ| ≤ 1) (hB : 0 ≤ B)
    (hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ)
    (hM : (∫ z, Real.exp (c*(Y z)^2) ∂μ) ≤ M)
    (hb : ∀ᵐ z ∂μ, |Δ z| ≤ 2*δ^2*(Y z)^2)
    (hr : ∀ᵐ z ∂μ, |Δ z-δ^2*A z*(Y z)^2| ≤ B*|δ|^3*|Y z|^3) :
    Real.log (∫ z, Real.exp (Δ z) ∂μ) ≤
      δ^2*(∫ z, A z*(Y z)^2 ∂μ)+
      ((B*(1+2/c^2)+32/c^2)*M)*|δ|^3 := by
  obtain ⟨hi,hI⟩ := cube_integrable_of_exp_square μ Y hY hc hE
  have hM0 : 0 ≤ M := (integral_nonneg (fun z => Real.exp_nonneg _)).trans hM
  have hpow : δ^4 ≤ |δ|^3 := by
    have H := mul_le_mul_of_nonneg_left hδ1 (pow_nonneg (abs_nonneg δ) 3)
    have he : δ^4=|δ|^4 := by
      calc
        δ^4 = (δ^2)^2 := by ring
        _ = (|δ|^2)^2 := by rw [sq_abs]
        _ = |δ|^4 := by ring
    rw [he]; nlinarith
  have HD : (∫ z, Δ z ∂μ) ≤ δ^2*(∫ z, A z*(Y z)^2 ∂μ)+
      (B*|δ|^3)*(∫ z, |Y z|^3 ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hA.const_mul _) (hi.const_mul _)]
    apply integral_mono_ae hΔ ((hA.const_mul _).add (hi.const_mul _))
    filter_upwards [hr] with z hz
    have H := le_abs_self (Δ z-δ^2*A z*(Y z)^2)
    simp only [Pi.add_apply]
    nlinarith
  have Hlog := log_integral_exp_quadratic_bound μ Y Δ hY hΔ hc hδ hE hM hb
  have HC : (∫ z, |Y z|^3 ∂μ) ≤ (1+2/c^2)*M :=
    hI.trans (mul_le_mul_of_nonneg_left hM (by positivity))
  have HH := mul_le_mul_of_nonneg_left HC (by positivity : 0 ≤ B*|δ|^3)
  have HP := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (32/c^2)*M)
  nlinarith

end SK.Analytic

end
end

end OAI
