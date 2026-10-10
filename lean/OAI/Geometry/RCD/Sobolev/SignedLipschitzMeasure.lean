import OAI.Geometry.RCD.Sobolev.LipschitzMeasureOrder
import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure

namespace OAI

/-! # Positivity and uniqueness of finite signed distributions -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem signed_integral_jordan (ν : SignedMeasure X) (f : X →ᵇ ℝ) :
    (∫ᵛ x, f x ∂<•ν) = (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
      ∫ x, f x ∂ν.toJordanDecomposition.negPart := by
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  change (∫ᵛ x, f x ∂<•(ν.toJordanDecomposition.posPart.toSignedMeasure -
    ν.toJordanDecomposition.negPart.toSignedMeasure)) = _
  rw [VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight f _)
    (PositiveBilinearMeasure.integrable_weight f _),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]

theorem signedMeasure_nonneg_of_lipschitz_integral [SecondCountableTopology X] [ProperSpace X]
    (ν : SignedMeasure X)
    (h : ∀ (f : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L f → 0 ≤ f →
      0 ≤ ∫ᵛ x, f x ∂<•ν) : 0 ≤ ν := by
  have hle : ν.toJordanDecomposition.negPart ≤ ν.toJordanDecomposition.posPart := by
    apply measure_le_of_bounded_lipschitz_integral
    intro f L hf h0 hC
    obtain ⟨C, hC⟩ := hC
    let g : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous
      C (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using hC x)
    have hg : 0 ≤ g := h0
    have hh := h g L hf hg
    rw [signed_integral_jordan] at hh
    change 0 ≤ (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
      ∫ x, f x ∂ν.toJordanDecomposition.negPart at hh
    exact sub_nonneg.mp hh
  rw [← ν.toSignedMeasure_toJordanDecomposition]
  change 0 ≤ ν.toJordanDecomposition.posPart.toSignedMeasure -
    ν.toJordanDecomposition.negPart.toSignedMeasure
  exact sub_nonneg.mpr ((Measure.toSignedMeasure_le_toSignedMeasure_iff _ _).mpr hle)

theorem signedMeasure_eq_of_lipschitz_integral [SecondCountableTopology X] [ProperSpace X]
    (μ ν : SignedMeasure X)
    (h : ∀ (f : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L f → 0 ≤ f →
      (∫ᵛ x, f x ∂<•μ) = ∫ᵛ x, f x ∂<•ν) : μ = ν := by
  have hsub (s t : SignedMeasure X)
      (hst : ∀ (f : X →ᵇ ℝ) (L : ℝ≥0), LipschitzWith L f → 0 ≤ f →
        (∫ᵛ x, f x ∂<•s) = ∫ᵛ x, f x ∂<•t) : 0 ≤ s - t := by
    apply signedMeasure_nonneg_of_lipschitz_integral
    intro f L hf h0
    rw [VectorMeasure.integral_sub_vectorMeasure
      (PositiveBilinearMeasure.integrable_weight f _)
      (PositiveBilinearMeasure.integrable_weight f _), hst f L hf h0, sub_self]
  exact le_antisymm (sub_nonneg.mp (hsub ν μ (fun f L hf h0 => (h f L hf h0).symm)))
    (sub_nonneg.mp (hsub μ ν h))

end RegularPointCoordinates

end

end OAI
