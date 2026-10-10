import OAI.Probability.FirstPassage.ExponentialTilt
import OAI.Probability.FirstPassage.ProbabilityFoundations
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

namespace PlanarFPP
open Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem expMeasure_map_scale (α : ℝ) (hα : 0 < α) :
    Measure.map (fun x : ℝ => α*x) (expMeasure 1)=expMeasure (1/α) := by
  have hm : Measurable (fun x : ℝ => α*x) := by fun_prop
  let _ := isProbabilityMeasure_expMeasure (show 0 < 1/α by positivity)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hm measurableSet_Iic]
  have he : (fun y : ℝ => α*y) ⁻¹' Iic x=Iic (x/α) := by
    ext y
    simp only [mem_preimage,mem_Iic]
    rw [le_div_iff₀ hα,mul_comm]
  rw [he,← ofReal_cdf,← ofReal_cdf]
  congr 1
  rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ)<1),cdf_expMeasure_eq (by positivity : 0 < 1/α)]
  have hepos : (0 ≤ x/α) ↔ 0 ≤ x := by rw [le_div_iff₀ hα,zero_mul]
  simp only [hepos]
  simp [div_eq_mul_inv,mul_comm]

theorem exponential_likelihood_density (ρ : ℝ) (_hρ : 0 ≤ ρ) (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exponentialLikelihood ρ x)=exponentialPDF ρ x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold exponentialLikelihood
    simp only [one_mul]
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem expMeasure_withDensity_likelihood (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (expMeasure 1).withDensity (fun x => ENNReal.ofReal (exponentialLikelihood ρ x))=expMeasure ρ := by
  change (volume.withDensity (exponentialPDF 1)).withDensity _=volume.withDensity (exponentialPDF ρ)
  rw [← withDensity_mul volume (by unfold exponentialPDF; fun_prop)
    (by unfold exponentialLikelihood; fun_prop)]
  congr 1
  funext x
  exact exponential_likelihood_density ρ hρ x

theorem exponential_likelihood_square_density (ρ : ℝ) (hρ : 1/2 < ρ) (x : ℝ) :
    exponentialPDF 1 x * (ENNReal.ofReal (exponentialLikelihood ρ x))^2 =
      ENNReal.ofReal (ρ^2/(2*ρ-1))*exponentialPDF (2*ρ-1) x := by
  have hd : 0 < 2*ρ-1 := by linarith
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_pow (by unfold exponentialLikelihood; positivity),
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold exponentialLikelihood
    rw [mul_pow,← Real.exp_nat_mul]
    simp only [one_mul]
    rw [mul_left_comm,← Real.exp_add]
    have he : -x+2*(-(ρ-1)*x)= -((2*ρ-1)*x) := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he]
    have hd' : ρ*2-1 ≠ 0 := by linarith
    field_simp [hd']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_likelihood_second_moment (ρ : ℝ) (hρ : 1/2 < ρ) :
    (∫⁻ x, (ENNReal.ofReal (exponentialLikelihood ρ x))^2 ∂expMeasure 1)=
      ENNReal.ofReal (ρ^2/(2*ρ-1)) := by
  change (∫⁻ x, _ ∂volume.withDensity (exponentialPDF 1))=_
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by unfold exponentialLikelihood; fun_prop)]
  simp only [Pi.mul_apply,exponential_likelihood_square_density ρ hρ]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by linarith : 0 < 2*ρ-1),mul_one]

end PlanarFPP

end OAI
