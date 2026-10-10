import OAI.Geometry.RCD.Sobolev.NoProjectedEulerSequence
import OAI.Geometry.RCD.Coordinates.RelativeErrorNormalization

namespace OAI

/-! # The uniform sharp projection bound from the proved analytic estimates

The Poisson, normalization and radial transport estimates provide a common
coordinate frame, residual bounds and an approximate Euler equation.
-/

open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The precise analytic data used in the sharp-projection contradiction.
The residual is the actual orthogonal projection residual. -/
structure SharpProjectionFamily {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (I : Type*) (S ρ : ℝ) where
  center : I → X
  radius : I → ℝ
  error : I → ℝ
  source : I → ℝ
  coordinates : I → Fin n → SobolevSpace (hausdorff n X) hX.quadratic
  coordinateValues : I → X → Euclidean n
  radial : I → SobolevSpace (hausdorff n X) hX.quadratic
  target : I → SobolevSpace (hausdorff n X) hX.quadratic
  residual : I → SobolevSpace (hausdorff n X) hX.quadratic
  forcing : I → SobolevSpace (hausdorff n X) hX.quadratic
  coefficient : I → Euclidean n
  constant : I → ℝ
  size : I → ℝ
  radialBound : ℝ
  outerConstant : ℝ
  coefficientConstant : ℝ
  sourceConstant : ℝ
  radius_pos : ∀ i, 0 < radius i
  curvature : ∀ i, -1 ≤ K * radius i ^ 2
  error_pos : ∀ i, 0 < error i
  source_pos : ∀ i, 0 < source i
  radialBound_nonneg : 0 ≤ radialBound
  outerConstant_nonneg : 0 ≤ outerConstant
  coefficientConstant_nonneg : 0 ≤ coefficientConstant
  measured : ∀ i, IsMeasuredEuclideanApproximation (hausdorff n X) n
    (center i) (radius i) S (error i) (coordinateValues i)
  representative : ∀ i j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (coordinates i j) =ᵐ[
    (hausdorff n X).restrict (ball (center i) (S * radius i))] fun x => coordinateValues i x j
  laplacianCoefficient : I → ℝ
  laplacianCoefficient_bound : ∀ i, |laplacianCoefficient i| ≤ radialBound
  laplacian : ∀ i, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
    (ball (center i) (S * radius i)) (radial i) (laplacianCoefficient i / radius i ^ 2)
  radial_norm : ∀ i, ‖normalizeLocalL2 (hausdorff n X) (ball (center i) (S * radius i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (center i) (S * radius i)) (radial i))‖ ≤ radialBound
  gradient : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball (center i) (S * radius i)),
    localGamma (hausdorff n X) hX.quadratic (radial i) (radial i) x ≤ radialBound / radius i ^ 2
  quadratic_error : ∀ i, ((hausdorff n X).real (ball (center i) (S * radius i)))⁻¹ *
    (∫ x in ball (center i) (S * radius i),
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (radial i) x -
        ‖coordinateValues i x‖ ^ 2 / 2) ^ 2 ∂hausdorff n X) ≤ error i
  harmonic : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
    (ball (center i) (S * radius i)) (residual i)
  projection : ∀ i, SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
    (ball (center i) (ρ * radius i)) (residual i) =
    affineResidual (hausdorff n X) hX.quadratic (coordinates i)
      (ball (center i) (ρ * radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (center i) (ρ * radius i)) (target i))
  size_eq : ∀ i, size i = ‖normalizeLocalL2 (hausdorff n X) (ball (center i) (ρ * radius i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (center i) (ρ * radius i)) (residual i))‖
  outer_bound : ∀ i, ‖normalizeLocalL2 (hausdorff n X) (ball (center i) (S * radius i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (center i) (S * radius i)) (residual i))‖ ≤ outerConstant * (size i + source i)
  coefficient_bound : ∀ i, ‖coefficient i‖ + |constant i| ≤ coefficientConstant * (size i + source i)
  forcing_bound : ∀ i, ‖normalizeLocalL2 (hausdorff n X) (ball (center i) (S * radius i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (center i) (S * radius i)) (forcing i))‖ ≤ sourceConstant * source i
  euler_identity : ∀ i, radius i ^ 2 • localRadialDerivative (hausdorff n X) hX.quadratic
    (ball (center i) (S * radius i)) (radial i) (gradient i) (residual i) =
    SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (center i) (S * radius i)) (residual i) +
    (∑ j, coefficient i j • SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (center i) (S * radius i)) (coordinates i j)) +
    constant i • restrictedOne (hausdorff n X) (ball (center i) (S * radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) +
    SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (center i) (S * radius i)) (forcing i)

/-- The radial potentials and coordinates form a compactness sequence;
the accompanying harmonic function is chosen to be zero. -/
def SharpProjectionFamily.compactnessSequence {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    {I : Type*} {S ρ : ℝ} (d : SharpProjectionFamily hX I S ρ)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n) (hS : 0 < S)
    (t : ℕ → I) (ht : Tendsto (d.error ∘ t) atTop (𝓝 0)) : RadialCompactnessSequence hX S where
  center := d.center ∘ t
  radius := d.radius ∘ t
  error := d.error ∘ t
  coordinates := d.coordinates ∘ t
  coordinateValues := d.coordinateValues ∘ t
  harmonicFunction := fun _ => 0
  radialFunction := d.radial ∘ t
  radius_pos := fun i => d.radius_pos (t i)
  curvature := fun i => d.curvature (t i)
  error_pos := fun i => d.error_pos (t i)
  error_zero := ht
  measured := fun i => d.measured (t i)
  representative := fun i => d.representative (t i)
  harmonic := by
    intro i φ hφ
    simp [energyForm]
  outer_norm := by intro i; simp [normalizeLocalL2]
  interior_energy := by
    intro a ha haS
    obtain ⟨C, hC, hb⟩ := hgradient.rescaled_interior_energy hn hS ha haS
    refine ⟨C, hC, fun i => hb _ _ (d.radius_pos (t i)) (d.curvature (t i)) 0 ?_ ?_⟩
    · intro φ hφ; simp [energyForm]
    · simp [normalizeLocalL2]
  radial_bounds := by
    refine ⟨d.radialBound, d.laplacianCoefficient ∘ t, d.radialBound_nonneg, fun i =>
      ⟨d.laplacianCoefficient_bound (t i), d.laplacian (t i), d.radial_norm (t i), ?_⟩⟩
    filter_upwards [d.gradient (t i)] with x hx
    exact (mul_le_mul_of_nonneg_left hx (sq_nonneg _)).trans_eq (by
      dsimp only [Function.comp_apply]
      field_simp [(d.radius_pos (t i)).ne'])
  quadratic_limit := by
    exact squeeze_zero
      (fun i => mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
      (fun i => d.quadratic_error (t i)) ht

end RegularPointCoordinates

end

end OAI
