import OAI.Geometry.RCD.Metric.SignedRadonLocal
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Square-integrable densities controlled by full positive mass -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A bound by the absolutely continuous density gives an L² estimate by
full positive mass. Singular mass is retained in the upper bound. -/
theorem memLp_two_of_sq_le_radon (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} {f : X → ℝ} (hf : AEStronglyMeasurable f (μ.restrict S))
    {B : ℝ} (hB : 0≤B)
    (hbound : ∀ᵐ x ∂μ.restrict S, (f x)^2≤B*(σ.rnDeriv μ x).toReal) :
    MemLp f 2 (μ.restrict S) ∧ (∫ x in S, (f x)^2 ∂μ)≤B*σ.real S := by
  have hden : Integrable (fun x => (σ.rnDeriv μ x).toReal) (μ.restrict S) :=
    Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ S)
  have hmajor := hden.const_mul B
  have hi : Integrable (fun x => (f x)^2) (μ.restrict S) := by
    apply hmajor.mono' (hf.pow 2)
    filter_upwards [hbound] with x hx
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))] using hx
  refine ⟨(memLp_two_iff_integrable_sq hf).mpr hi,?_⟩
  calc
    (∫ x in S, (f x)^2 ∂μ) ≤ ∫ x in S, B*(σ.rnDeriv μ x).toReal ∂μ :=
      integral_mono_ae hi hmajor hbound
    _ = B*(∫ x in S, (σ.rnDeriv μ x).toReal ∂μ) := integral_const_mul _ _
    _ ≤ B*σ.real S := mul_le_mul_of_nonneg_left
      (Measure.setIntegral_toReal_rnDeriv_le (μ := σ) (ν := μ) (measure_ne_top σ S)) hB

/-- A bounded direction turns the pointwise quadratic estimate into a
full-mass bound with the square of its energy bound. -/
theorem memLp_two_of_radon_direction (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} {f g : X → ℝ} (hf : AEStronglyMeasurable f (μ.restrict S))
    (C : ℝ) (hC : 0≤C)
    (hg : ∀ᵐ x ∂μ.restrict S, 0≤g x ∧ g x≤C)
    (hbound : ∀ᵐ x ∂μ.restrict S, (f x)^2≤(σ.rnDeriv μ x).toReal*(g x)^2) :
    MemLp f 2 (μ.restrict S) ∧ (∫ x in S, (f x)^2 ∂μ)≤C^2*σ.real S := by
  apply memLp_two_of_sq_le_radon μ σ hf (sq_nonneg C)
  filter_upwards [hg,hbound] with x hg hx
  calc
    (f x)^2 ≤ (σ.rnDeriv μ x).toReal*(g x)^2 := hx
    _ ≤ (σ.rnDeriv μ x).toReal*C^2 := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hg.1 hC).mpr hg.2) ENNReal.toReal_nonneg
    _ = C^2*(σ.rnDeriv μ x).toReal := mul_comm _ _

end RegularPointCoordinates

end

end OAI
