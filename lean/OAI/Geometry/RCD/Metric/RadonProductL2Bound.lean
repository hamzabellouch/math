import OAI.Geometry.RCD.Metric.RadonDensityL2Bound

namespace OAI

/-! # Full-mass bounds with two separately controlled directions -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem memLp_two_of_radon_product (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} {f g h : X → ℝ} (hf : AEStronglyMeasurable f (μ.restrict S))
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hg : ∀ᵐ x ∂μ.restrict S, 0≤g x ∧ g x≤C)
    (hh : ∀ᵐ x ∂μ.restrict S, 0≤h x ∧ h x≤D)
    (hbound : ∀ᵐ x ∂μ.restrict S, (f x)^2≤(σ.rnDeriv μ x).toReal*g x*h x) :
    MemLp f 2 (μ.restrict S) ∧ (∫ x in S, (f x)^2 ∂μ)≤(C*D)*σ.real S := by
  apply memLp_two_of_sq_le_radon μ σ hf (mul_nonneg hC hD)
  filter_upwards [hg,hh,hbound] with x hg hh hx
  calc
    (f x)^2 ≤ (σ.rnDeriv μ x).toReal*g x*h x := hx
    _ = (σ.rnDeriv μ x).toReal*(g x*h x) := mul_assoc _ _ _
    _ ≤ (σ.rnDeriv μ x).toReal*(C*D) := mul_le_mul_of_nonneg_left
      (mul_le_mul hg.2 hh.2 hh.1 hC) ENNReal.toReal_nonneg
    _ = (C*D)*(σ.rnDeriv μ x).toReal := mul_comm _ _

end RegularPointCoordinates

end

end OAI
