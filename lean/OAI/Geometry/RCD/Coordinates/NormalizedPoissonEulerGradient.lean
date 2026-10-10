import OAI.Geometry.RCD.Sobolev.ActualPoissonEulerGradient
import OAI.Geometry.RCD.Sobolev.PoissonPairDefect
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits
import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # The actual Euler-gradient error in normalized defect units -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- The coefficient is independent of the center and scale. -/
def poissonEulerGradientConstant (n : ℕ) (A B J Cχ : ℝ) : ℝ :=
  12 * A ^ 2 *
    (4096 * Cχ * (J + B / 2) + A ^ 2) *
    ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual gradient product rule gives a mean Euler-gradient error
controlled by the two original summable defects, at every dyadic scale. -/
theorem normalized_poisson_euler_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
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
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 64) ^ n) - 1| ≤ 1 / 4) :
    ∃ g : SobolevSpace (hausdorff n X) hX.quadratic,
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball z (s / 64)
      let v := T₂.replacement i - T₁.replacement i
      (SobolevSpace.toLp μ hX.quadratic g =ᵐ[μ.restrict Ω]
        localGamma μ hX.quadratic (T₂.replacement i) v) ∧
      (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hX.quadratic (g - v) (g - v) x ∂μ) ≤
        poissonEulerGradientConstant n A B J Cχ * s ^ 2 *
          (normalizedPoissonDefect μ hX.quadratic S₁ i + normalizedPoissonDefect μ hX.quadratic S₂ i) := by
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  let W := μ.real (ball z (s / 64))
  let P := normalizedPoissonDefect μ hQ S₁ i + normalizedPoissonDefect μ hQ S₂ i
  let H := 4096 * Cχ * (J + B / 2) + A ^ 2
  let Q := 4096 * Cχ * (J + B / 2) *
    ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s)) +
    κ * A ^ 2 * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s))
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  have hW : 0 < W := (quarter_volume_bounds (n := n) (by positivity : 0 < s / 64)
    (euclideanUnitVolume_pos n) hvolume).1
  have hP : 0 ≤ P := add_nonneg (normalizedPoissonDefect_nonneg μ hQ S₁ hκ i)
    (normalizedPoissonDefect_nonneg μ hQ S₂ hκ i)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hmass : Q ≤ H * s ^ (n : ℝ) * P :=
    poisson_pair_defect_bound μ hQ S₁ S₂ i hκ (by positivity)
  have hratio : s ^ (n : ℝ) / W ≤ (4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n :=
    radial_testing_volume_ratio hs (euclideanUnitVolume_pos n) hvolume
  obtain ⟨g, hg, he⟩ := actual_poisson_euler_gradient hX hhessian hproduct hκ hK hB hJ hCχ
    hA hepsilon p₁ p₂ z S₁ S₂ T₁ T₂ i hroom₁ hroom₂ u hu hgrad hf₁ hf₂ χ
  refine ⟨g, hg, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 12 * A ^ 2 * s ^ 2 by positivity)
  have havg := mul_le_mul_of_nonneg_left (he.trans hm) (inv_nonneg.mpr hW.le)
  have hr := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 12 * A ^ 2 * H * s ^ 2 * P by positivity)
  apply havg.trans
  convert hr using 1 <;> dsimp only [poissonEulerGradientConstant, H, s, P] <;> ring

end RegularPointCoordinates

end

end OAI
