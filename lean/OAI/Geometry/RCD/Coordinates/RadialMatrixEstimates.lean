import OAI.Geometry.RCD.Harmonic.UniformRadialMatrices

namespace OAI

/-! # The simultaneous value, coefficient and energy estimates -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The estimates already proved for the actual Poisson radial matrices,
packaged only to retain their common choices of rows. -/
def RadialMatrixEstimates {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    [IsFiniteMeasureOnCompacts (hausdorff n X)]
    {κ r0 B J C Cχ : ℝ} {p : X}
    (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (V : X → Euclidean n)
    (F : ℕ → Euclidean n ≃L[ℝ] Euclidean n)
    (χ : ∀ i, GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (δ Cg D Ca A : ℝ) : Prop :=
    ∀ i,
      ∃ coeff : Fin n → Euclidean n,
      ∃ g : Fin n → SobolevSpace (hausdorff n X) hX.quadratic,
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let r := s / 64
      let E := pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant n Cχ * δ)
        (normalizedPoissonDefect μ hX.quadratic S) i
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (radialCoefficientMatrix (F i) coeff) -
          ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤
        ((n : ℕ) : ℝ) ^ 2 *
          Real.sqrt (2 * Ca ^ 2 * (D ^ 2 * E + radialFitQualitativeConstant n Cχ * δ)) ∧
      ∀ j,
      let H := centeredAffineSobolev μ hX.quadratic u (χ i).sobolev (V p) (coeff j)
      (SobolevSpace.toLp μ hX.quadratic (g j) =ᵐ[μ.restrict (ball p r)]
        localGamma μ hX.quadratic (T.replacement i)
          (sobolevColumnMap μ hX.quadratic u (F i (EuclideanSpace.single j 1)))) ∧
      ‖normalizeLocalL2 μ (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic (ball p r) (g j - H))‖ ^ 2 ≤
        (2 * D ^ 2 + 8192 * (((n : ℕ) : ℝ) * 2) ^ 2 * B *
          ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n)) * r ^ 2 * E ∧
      (μ.real (ball p (r / 2)))⁻¹ *
        (∫ x in ball p (r / 2), localGamma μ hX.quadratic (g j - H) (g j - H) x ∂μ) ≤
        radialEnergyConstant K n Cg 1 A B J Cχ *
          ((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹ * D ^ 2 +
            (4 / (3 * euclideanUnitVolume n)) * (128 : ℝ) ^ n) * E

end RegularPointCoordinates

end

end OAI
