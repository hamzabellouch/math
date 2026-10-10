import OAI.Geometry.RCD.Metric.SignedSourceDensity
import Mathlib.Topology.ContinuousMap.CompactlySupported

namespace OAI

/-!
# Bounded weights on full signed sources

The Jordan construction keeps both parts of the source, including any
singular mass. No absolute continuity with respect to volume is assumed.
-/

open Set MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Multiply a finite signed source by a bounded continuous weight. -/
def signedSourceWeight (ν : SignedMeasure X) (χ : X →ᵇ ℝ) : SignedMeasure X :=
  ν.toJordanDecomposition.posPart.withDensityᵥ χ -
    ν.toJordanDecomposition.negPart.withDensityᵥ χ

private theorem integrable_bounded_weight (μ : Measure X) [IsFiniteMeasure μ]
    (χ : X →ᵇ ℝ) : Integrable χ μ :=
  Integrable.of_bound χ.continuous.aestronglyMeasurable ‖χ‖
    (Filter.Eventually.of_forall χ.norm_coe_le_norm)

/-- Integration against a weighted full source is ordinary multiplication
of its bounded continuous test. -/
theorem integral_signedSourceWeight (ν : SignedMeasure X) (χ w : X →ᵇ ℝ) :
    (∫ᵛ x, w x ∂<•(signedSourceWeight ν χ)) =
      ∫ᵛ x, (w * χ) x ∂<•ν := by
  have hp := integrable_bounded_weight ν.toJordanDecomposition.posPart χ
  have hn := integrable_bounded_weight ν.toJordanDecomposition.negPart χ
  rw [signedSourceWeight, VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight w _)
    (PositiveBilinearMeasure.integrable_weight w _),
    integral_signedDensity _ hp w, integral_signedDensity _ hn w]
  have hj : (∫ᵛ x, (w * χ) x ∂<•(ν.toJordanDecomposition.posPart.toSignedMeasure -
      ν.toJordanDecomposition.negPart.toSignedMeasure)) =
      (∫ᵛ x, (w * χ) x ∂<•ν.toJordanDecomposition.posPart.toSignedMeasure) -
      (∫ᵛ x, (w * χ) x ∂<•ν.toJordanDecomposition.negPart.toSignedMeasure) :=
    VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight (w * χ)
      ν.toJordanDecomposition.posPart.toSignedMeasure)
    (PositiveBilinearMeasure.integrable_weight (w * χ)
      ν.toJordanDecomposition.negPart.toSignedMeasure)
  rw [← JordanDecomposition.toSignedMeasure,
    SignedMeasure.toSignedMeasure_toJordanDecomposition] at hj
  rw [hj, VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
  rfl

/-- The full variation of a weighted source vanishes off the weight's
support, even when the original source has singular mass there. -/
theorem signedSourceWeight_variation_compl (ν : SignedMeasure X) (χ : X →ᵇ ℝ)
    {K : Set X} (hK : MeasurableSet K) (hχ : ∀ x ∉ K, χ x = 0) :
    (signedSourceWeight ν χ).variation Kᶜ = 0 := by
  apply (VectorMeasure.variation_apply_eq_zero hK.compl).2
  intro s hs hsm
  rw [signedSourceWeight, sub_apply,
    withDensityᵥ_apply (integrable_bounded_weight _ χ) hsm,
    withDensityᵥ_apply (integrable_bounded_weight _ χ) hsm]
  have hp : (∫ x in s, χ x ∂ν.toJordanDecomposition.posPart) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun x hx => hχ x (hs hx)
  have hn : (∫ x in s, χ x ∂ν.toJordanDecomposition.negPart) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun x hx => hχ x (hs hx)
  rw [hp, hn, sub_self]

end RegularPointCoordinates

end

end OAI
