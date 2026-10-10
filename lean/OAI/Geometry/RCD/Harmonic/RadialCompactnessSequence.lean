import OAI.Geometry.RCD.Sobolev.PoissonHarmonicCompactnessInput

namespace OAI

/-! # The concrete sequence data for the sharp projection argument -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- All analytic preconditions of the published local compactness theorem.
No projected Euler equation or affine approximation is part of this data. -/
structure RadialCompactnessSequence {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (S : ℝ) where
  center : ℕ → X
  radius : ℕ → ℝ
  error : ℕ → ℝ
  coordinates : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic
  coordinateValues : ℕ → X → Euclidean n
  harmonicFunction : ℕ → SobolevSpace (hausdorff n X) hX.quadratic
  radialFunction : ℕ → SobolevSpace (hausdorff n X) hX.quadratic
  radius_pos : ∀ i, 0 < radius i
  curvature : ∀ i, -1 ≤ K * radius i ^ 2
  error_pos : ∀ i, 0 < error i
  error_zero : Tendsto error atTop (𝓝 0)
  measured : ∀ i, IsMeasuredEuclideanApproximation (hausdorff n X) n
    (center i) (radius i) S (error i) (coordinateValues i)
  representative : ∀ i j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (coordinates i j) =ᵐ[
    (hausdorff n X).restrict (ball (center i) (S * radius i))] fun x => coordinateValues i x j
  harmonic : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
    (ball (center i) (S * radius i)) (harmonicFunction i)
  outer_norm : ∀ i, ‖normalizeLocalL2 (hausdorff n X) (ball (center i) (S * radius i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (center i) (S * radius i))
      (harmonicFunction i))‖ ≤ 1
  interior_energy : ∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
    radius i ^ 2 * ((hausdorff n X).real (ball (center i) (S * radius i)))⁻¹ *
      (∫ x in ball (center i) (ρ * radius i), localGamma (hausdorff n X) hX.quadratic
        (harmonicFunction i) (harmonicFunction i) x ∂hausdorff n X) ≤ C
  radial_bounds : ∃ (A : ℝ) (a : ℕ → ℝ), 0 ≤ A ∧ ∀ i,
    |a i| ≤ A ∧
    IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball (center i) (S * radius i))
      (radialFunction i) (a i / radius i ^ 2) ∧
    ‖normalizeLocalL2 (hausdorff n X) (ball (center i) (S * radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (center i) (S * radius i))
        (radialFunction i))‖ ≤ A ∧
    ∀ᵐ x ∂(hausdorff n X).restrict (ball (center i) (S * radius i)),
      radius i ^ 2 * localGamma (hausdorff n X) hX.quadratic (radialFunction i) (radialFunction i) x ≤ A
  quadratic_limit : Tendsto (fun i => ((hausdorff n X).real (ball (center i) (S * radius i)))⁻¹ *
    ∫ x in ball (center i) (S * radius i),
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (radialFunction i) x -
        ‖coordinateValues i x‖ ^ 2 / 2) ^ 2 ∂hausdorff n X) atTop (𝓝 0)

omit [ProperSpace X] in
theorem LocalPoissonHarmonicCompactnessInput.extract_sequence
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalPoissonHarmonicCompactnessInput hX) (hn : 2 ≤ n)
    {S : ℝ} (hS : 0 < S) (q : RadialCompactnessSequence hX S) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ model : EuclideanHarmonicModel n S,
      PoissonHarmonicLimit hX S (q.center ∘ t) (q.radius ∘ t) (q.coordinates ∘ t)
        (q.coordinateValues ∘ t) (q.harmonicFunction ∘ t) (q.radialFunction ∘ t) model :=
  hinput hn S hS q.center q.radius q.error q.radius_pos q.curvature q.error_pos q.error_zero
    q.coordinates q.coordinateValues q.harmonicFunction q.radialFunction q.measured q.representative
    q.harmonic q.outer_norm q.interior_energy q.radial_bounds q.quadratic_limit

end RegularPointCoordinates

end

end OAI
