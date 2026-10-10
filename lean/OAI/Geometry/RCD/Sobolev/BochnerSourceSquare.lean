import OAI.Geometry.RCD.Sobolev.BochnerMixedRecovery
import OAI.Geometry.RCD.Sobolev.BochnerTestForm

namespace OAI

/-! # Eliminating the derivative of the source in a Bochner test

The actual mixed integration-by-parts identity rewrites the source-gradient
term using its square and a pairing against the test gradient.
-/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem bochner_source_square (u d H w : SobolevSpace μ hQ) (κ : ℝ)
    (C L : ℝ≥0) (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x≤L)
    (hd : IsWeakLaplacian μ hQ u (SobolevSpace.toLp μ hQ d)) :
    bochnerTestForm μ hQ κ H w-weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) u d =
      -(1/2:ℝ)*energyForm μ hQ H w+κ*inner ℝ (SobolevSpace.toLp μ hQ w)
        (SobolevSpace.toLp μ hQ H)+
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ d) u w+
      ∫ x, SobolevSpace.toLp μ hQ w x*(SobolevSpace.toLp μ hQ d x)^2 ∂μ := by
  have hh := weakLaplacian_mixed_identity_L2 μ hQ u d w C L hw hu hd
  rw [bochnerTestForm_apply]
  linarith only [hh]

theorem fisher_source_square_algebra (w d h a q : ℝ) (hq : q≠0) :
    2*(w*q)*(d/q-h)^2+2*(d/q-h)*(a+w*q*h) =
      2*w*d^2/q-2*w*d*h+2*d*a/q-2*h*a := by
  field_simp [hq]
  ring

end RegularPointCoordinates

end

end OAI
