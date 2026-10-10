import OAI.Geometry.RCD.Coordinates.NormalizedPoissonCommutator
import OAI.Geometry.RCD.Harmonic.CommutatorRepresentatives

namespace OAI

/-! # The actual Poisson commutator for the chosen radial fit families -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The full-mass commutator bound applies to the exact Sobolev families
selected by radial approximation, simultaneously for every covector. -/
theorem normalized_poisson_commutator_for_fits {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    {κ B J C A Cχ epsilon r0 : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hCχ : 0 ≤ Cχ)
    (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon) (p₁ p₂ z : X)
    (S₁ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₁ r0)
    (S₂ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₂ r0)
    (T₁ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₁ B J C)
    (T₂ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₂ B J C)
    (i : ℕ)
    (hroom₁ : dist z p₁ ≤ distanceSourceRadius r0 i / 4)
    (hroom₂ : dist z p₂ ≤ distanceSourceRadius r0 i / 4)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball z (distanceSourceRadius r0 i / 4)) (u j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (hf₁ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₁.replacement i) (T₁.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (hf₂ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i) (T₂.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic z (distanceSourceRadius r0 i / 64) Cχ)
    (hvolume : |(hausdorff n X).real (ball z (distanceSourceRadius r0 i / 64)) /
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 64) ^ n) - 1| ≤ 1 / 4)
    (G H : Euclidean n →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : ∀ b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (G b) =ᵐ[
      (hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 64))]
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u b))
    (hH : ∀ b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H b) =ᵐ[
      (hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 64))]
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i - T₁.replacement i)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u b)) :
    ∀ b, let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball z (s / 64)
      (μ.real Ω)⁻¹ * (∫ x in Ω,
        (localGamma μ hX.quadratic (T₂.replacement i - T₁.replacement i) (G b) x -
          localGamma μ hX.quadratic (T₂.replacement i) (H b) x -
          localGamma μ hX.quadratic (T₂.replacement i - T₁.replacement i)
            (sobolevColumnMap μ hX.quadratic u b) x) ^ 2 ∂μ) ≤
        poissonCommutatorConstant n A epsilon B J Cχ * s ^ 2 * ‖b‖ ^ 2 *
          (normalizedPoissonDefect μ hX.quadratic S₁ i + normalizedPoissonDefect μ hX.quadratic S₂ i) := by
  intro b
  obtain ⟨g, h, hg, hh, he⟩ := normalized_poisson_commutator_error hX hhessian hκ hK
    hB hJ hCχ hA hepsilon p₁ p₂ z S₁ S₂ T₁ T₂ i hroom₁ hroom₂ u hu hgrad hf₁ hf₂ χ hvolume b
  have hi := commutator_error_transfer (hausdorff n X) hX.quadratic
    (T₂.replacement i) (T₂.replacement i - T₁.replacement i)
    (sobolevColumnMap (hausdorff n X) hX.quadratic u b) g h (G b) (H b)
    hg hh (hG b) (hH b) le_rfl
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans he

end RegularPointCoordinates

end

end OAI
