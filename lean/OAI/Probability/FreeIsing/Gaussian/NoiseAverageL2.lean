import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  simpa only [Pi.pow_apply] using (sub_nonneg.mp h)

theorem memLp_integral_noise {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {μ : Measure Ω} {ν : Measure A} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω × A → ℝ} (hm : Measurable f) (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ ∧
      (∫ x, (∫ y, f (x,y) ∂ν)^2 ∂μ) ≤ ∫ z, (f z)^2 ∂μ.prod ν := by
  have havg : Measurable (fun x => ∫ y, f (x,y) ∂ν) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have hbound : ∀ᵐ x ∂μ, (∫ y, f (x,y) ∂ν)^2 ≤ ∫ y, (f (x,y))^2 ∂ν := by
    filter_upwards [hf.integrable_sq.prod_right_ae] with x hx
    apply sq_integral_le_integral_sq
    exact (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2 hx
  have hint : Integrable (fun x => (∫ y, f (x,y) ∂ν)^2) μ := by
    apply hf.integrable_sq.integral_prod_left.mono' (havg.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨(memLp_two_iff_integrable_sq havg.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_prod _ hf.integrable_sq]
  exact integral_mono_ae hint hf.integrable_sq.integral_prod_left hbound

end Problem367

end

end OAI
