import OAI.Geometry.RCD.Sobolev.WeakLaplacianWeightedProduct

namespace OAI

/-! # The two-factor source cancellation for a localized heat bridge

The cutoff-gradient term is retained. It is the boundary error in the
local osmotic-energy estimate.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weakLaplacian_two_factor_source
    (u v w : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (he : IsWeakLaplacian μ Q v e)
    (A B C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hv : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x| ≤ C) :
    (∫ x, SobolevSpace.toLp μ Q w x*SobolevSpace.toLp μ Q v x*d x ∂μ)+
      (∫ x, SobolevSpace.toLp μ Q w x*SobolevSpace.toLp μ Q u x*e x ∂μ) =
      -2*weightedGamma μ Q (SobolevSpace.toLp μ Q w) u v-
        (weightedGamma μ Q (SobolevSpace.toLp μ Q v) u w+
          weightedGamma μ Q (SobolevSpace.toLp μ Q u) v w) := by
  have h₁ := IsWeakLaplacian.weighted_product μ Q u v w d hd B C hv hw
  have h₂ := IsWeakLaplacian.weighted_product μ Q v u w e he A C hu hw
  rw [weightedGamma_comm μ Q (SobolevSpace.toLp μ Q w) v u] at h₂
  linarith only [h₁,h₂]

end RegularPointCoordinates

end

end OAI
