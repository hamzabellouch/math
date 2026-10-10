import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

variable {X : Type*} [MeasurableSpace X]

lemma integrable_exp_neg_llr (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) : Integrable (fun x => Real.exp (-llr μ ν x)) μ := by
  exact ν.integrable_toReal_rnDeriv.congr (exp_neg_llr hac).symm

lemma entropy_test_positive_integrable (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ∞) {g : X → ℝ} (hg : Measurable g)
    (he : Integrable (fun x => Real.exp (g x)) ν) :
    Integrable (fun x => max (g x) 0) μ := by
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hkl
  have : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted he
  have hac' : μ ≪ ν.tilted g := hac.trans (absolutelyContinuous_tilted he)
  have hi := (hllr.norm.add (integrable_exp_neg_llr μ (ν.tilted g) hac')).add
    (integrable_const |Real.log (∫ x, Real.exp (g x) ∂ν)|)
  apply hi.mono' (by fun_prop)
  filter_upwards [llr_tilted_right hac he] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ 0)]
  simp only [Pi.add_apply, Real.norm_eq_abs]
  apply max_le
  · have h₁ := Real.add_one_le_exp (-llr μ (ν.tilted g) x)
    have h₂ := le_abs_self (llr μ ν x)
    have h₃ := le_abs_self (Real.log (∫ x, Real.exp (g x) ∂ν))
    linarith
  · positivity

lemma entropy_test_integral (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ∞) {g : X → ℝ} (hg : Integrable g μ)
    (he : Integrable (fun x => Real.exp (g x)) ν) :
    (∫ x, g x ∂μ) ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (g x) ∂ν) := by
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hkl
  have : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted he
  have hnon := integral_llr_add_sub_measure_univ_nonneg
    (hac.trans (absolutelyContinuous_tilted he)) (integrable_llr_tilted_right hac hg hllr he)
  rw [integral_llr_tilted_right hac hg he hllr] at hnon
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  simp only [probReal_univ, add_sub_cancel_right] at hnon
  linarith

lemma entropy_test_normalized (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ∞) {g : X → ℝ} (hg : Integrable g μ)
    (he : Integrable (fun x => Real.exp (g x)) ν)
    (hmean : (∫ x, Real.exp (g x) ∂ν) ≤ 1) :
    (∫ x, g x ∂μ) ≤ (klDiv μ ν).toReal := by
  have h := entropy_test_integral μ ν hkl hg he
  have hlog : Real.log (∫ x, Real.exp (g x) ∂ν) ≤ 0 :=
    Real.log_nonpos (integral_nonneg (fun _ => (Real.exp_pos _).le)) hmean
  linarith

lemma llr_withDensity_ae (ν : Measure X) [SigmaFinite ν] {g : X → ℝ≥0∞}
    (hg : Measurable g) [IsFiniteMeasure (ν.withDensity g)] :
    llr (ν.withDensity g) ν =ᵐ[ν.withDensity g] (fun x => Real.log (g x).toReal) := by
  filter_upwards [(withDensity_absolutelyContinuous ν g).ae_le (ν.rnDeriv_withDensity hg)] with x hx
  exact congrArg (fun t : ℝ≥0∞ => Real.log t.toReal) hx

lemma klDiv_withDensity_eq (ν : Measure X) [IsProbabilityMeasure ν] {g : X → ℝ≥0∞}
    (hg : Measurable g) [IsProbabilityMeasure (ν.withDensity g)]
    (hi : Integrable (fun x => Real.log (g x).toReal) (ν.withDensity g)) :
    klDiv (ν.withDensity g) ν = ENNReal.ofReal (∫ x, Real.log (g x).toReal ∂ν.withDensity g) := by
  have hi' : Integrable (llr (ν.withDensity g) ν) (ν.withDensity g) :=
    hi.congr (llr_withDensity_ae ν hg).symm
  rw [klDiv_of_ac_of_integrable (withDensity_absolutelyContinuous ν g) hi']
  simp only [probReal_univ, add_sub_cancel_right]
  congr 1
  exact integral_congr_ae (llr_withDensity_ae ν hg)

end PosteriorReplicas
end

end OAI
