import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
lemma interval_product_integrable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {B : ℝ × Ω → ℝ} (hB : Continuous B) {D : ℝ}
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ g, |B (t,g)| ≤ D) :
    Integrable B ((volume.restrict (Ioc (0:ℝ) 1)).prod μ) := by
  apply Integrable.of_bound hB.aestronglyMeasurable D
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hB.norm.measurable measurable_const)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1.le,ht.2⟩ g)

lemma bounded_interval_mean {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {B : ℝ × Ω → ℝ} (hB : Continuous B) {D c ε : ℝ}
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ∀ g, |B (t,g)| ≤ D)
    (hm : ∀ t ∈ Icc (0:ℝ) 1, |(∫ g, B (t,g) ∂μ)-t*c| ≤ ε) :
    Integrable (fun g => ∫ t in (0:ℝ)..1, B (t,g)) μ ∧
    |(∫ g, (∫ t in (0:ℝ)..1, B (t,g)) ∂μ)-c/2| ≤ ε := by
  have hi := interval_product_integrable (μ := μ) hB hb
  have hi' : Integrable (Function.uncurry (fun t g => B (t,g)))
      ((volume.restrict (uIoc (0:ℝ) 1)).prod μ) := by
    have he : Function.uncurry (fun t g => B (t,g)) = B := by
      funext x; rcases x with ⟨t,g⟩; rfl
    rw [he,uIoc_of_le (by norm_num : (0:ℝ)≤1)]
    exact hi
  constructor
  · simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hi.integral_prod_right
  · rw [← intervalIntegral_integral_swap hi']
    have hit : IntervalIntegrable (fun t => ∫ g, B (t,g) ∂μ) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)]
      exact hi.integral_prod_left
    have hid : IntervalIntegrable (fun t : ℝ => t*c) volume 0 1 := (continuous_id.mul_const c).intervalIntegrable 0 1
    have hc : (∫ t in (0:ℝ)..1, t*c)=c/2 := by rw [intervalIntegral.integral_mul_const,integral_id]; ring
    rw [← hc,← intervalIntegral.integral_sub hit hid]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun t => (∫ g, B (t,g) ∂μ)-t*c) (C := ε) (fun t ht => by
        have ht' : t ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using ht
        simpa only [Real.norm_eq_abs] using hm t ⟨ht'.1.le,ht'.2⟩)
    simpa using hh
end SKGap
end
end

end OAI
