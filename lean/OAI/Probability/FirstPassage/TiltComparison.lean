import OAI.Probability.FirstPassage.FiniteTiltLaw
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

namespace PlanarFPP
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem withDensity_sq_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L : Ω → ℝ≥0∞) (hL : Measurable L)
    (A : Set Ω) (hA : MeasurableSet A) :
    ((P.withDensity L) A)^2 ≤ (∫⁻ x, (L x)^2 ∂P)*P A := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hL.aemeasurable (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) (P.restrict A))
  simp only [Pi.mul_apply,mul_one,ENNReal.rpow_two,one_pow,lintegral_one,
    Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  have hsqrt (x : ℝ≥0∞) : (x^(1/(2 : ℝ)))^2=x := by
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hh2 := pow_le_pow_left' hh 2
  rw [mul_pow,hsqrt,hsqrt] at hh2
  rw [withDensity_apply L hA]
  exact hh2.trans (mul_le_mul' (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl)

variable {ι : Type*} [Fintype ι]

theorem finite_expMeasure_probability_sq_bound (ρ : ℝ) (hρ : 1/2 < ρ)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : ι => expMeasure ρ)).real A ^ 2 ≤
      (ρ^2/(2*ρ-1))^(Fintype.card ι)*(Measure.pi (fun _ : ι => expMeasure 1)).real A := by
  have hh := withDensity_sq_le_second_moment (Measure.pi (fun _ : ι => expMeasure 1))
    (finiteExponentialLikelihood ρ) (measurable_finiteExponentialLikelihood ρ) A hA
  rw [finite_expMeasure_withDensity ρ (by linarith),finite_exponential_likelihood_second_moment ρ hρ] at hh
  have hfin : (ENNReal.ofReal (ρ^2/(2*ρ-1)))^(Fintype.card ι)*
      (Measure.pi (fun _ : ι => expMeasure 1)) A ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  have hr := ENNReal.toReal_mono hfin hh
  have hc : 0 ≤ ρ^2/(2*ρ-1) := div_nonneg (sq_nonneg ρ) (by linarith)
  simpa only [measureReal_def,ENNReal.toReal_pow,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using hr

theorem finite_scaled_expMeasure_probability_sq_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    ((Measure.pi (fun _ : ι => expMeasure 1)).map (fun x i => (1-δ)*x i)).real A ^ 2 ≤
      (1/(1-δ^2))^(Fintype.card ι)*(Measure.pi (fun _ : ι => expMeasure 1)).real A := by
  have hα : 0 < 1-δ := by linarith
  have hρ : 1/2 < 1/(1-δ) := by
    apply (lt_div_iff₀ hα).mpr
    linarith
  have he : (1/(1-δ))^2/(2*(1/(1-δ))-1)=1/(1-δ^2) := by
    have hi := tilted_rate_second_moment δ hδ hδ'
    rwa [likelihood_second_moment_integral _ hρ] at hi
  rw [finite_expMeasure_map_scale _ hα]
  simpa only [he] using finite_expMeasure_probability_sq_bound (1/(1-δ)) hρ A hA

end PlanarFPP

end OAI
