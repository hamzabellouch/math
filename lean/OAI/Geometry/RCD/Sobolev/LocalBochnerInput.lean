import OAI.Geometry.RCD.Sobolev.CompactCutoffSource
import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-!
# The local harmonic Bochner input

The input is the finite-span, interior-ball specialization of Gigli,
*Non-smooth differential geometry*, Mem. AMS 251 (2018), no. 1196,
§3.1, equation (3.1.10), and Theorem 3.3.8. The local test-function
extension uses Connell et al. (2021), Lemmas 2.6--2.7. In particular,
Gamma of a locally Lipschitz harmonic function is locally W^{1,2},
and one half of its measure Laplacian plus kappa Gamma is positive.
The finite measure is obtained by restricting inside the larger ball;
the bounded global Sobolev representative is a cutoff extension.

This input asserts local calculus only. It does not include any mass
estimate, heat estimate, pinching, coordinate approximation or chart.
-/

open Set Metric MeasureTheory
open scoped BoundedContinuousFunction NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The exact local measure Laplacian of the harmonic energy density. -/
def harmonicBochnerSource (U : E →L[ℝ] SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X E) (κ : ℝ) (v : E) : SignedMeasure X :=
  (2 : ℝ) • M.bilinear v v -
    (2 * κ) • μ.withDensityᵥ (localGamma μ hQ (U v) (U v))

/-- The bounded representative and local measure equation furnished by
local harmonic test calculus on an interior ball. -/
structure LocalHarmonicEnergy (U : E →L[ℝ] SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X E) (κ : ℝ) (p : X) (r : ℝ)
    (L : ℝ≥0) (v : E) where
  energy : SobolevSpace μ hQ
  representative : SobolevSpace.toLp μ hQ energy =ᵐ[μ.restrict (ball p (2 * r))]
    localGamma μ hQ (U v) (U v)
  bounded : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ energy x| ≤
    ((L ^ 2 * ‖v‖₊ ^ 2 : ℝ≥0) : ℝ)
  measure_laplacian : IsMeasureLaplacianOn μ hQ (ball p (2 * r)) energy
    (harmonicBochnerSource μ hQ U M κ v)

/-- Local calculus on interior balls with eightfold room for regularity. -/
def LocalHarmonicBochnerInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → -κ ≤ K → ∀ (p : X) (r : ℝ), 0 < r →
    ∀ (L : ℝ≥0) (U : Euclidean n →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic),
      (∀ v, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (8 * r)) (U v)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤
          (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      ∃ M : PositiveBilinearMeasure X (Euclidean n),
        ∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)

end RegularPointCoordinates

end

end OAI
