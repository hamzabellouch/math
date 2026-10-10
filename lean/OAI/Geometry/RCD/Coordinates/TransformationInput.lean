import OAI.Geometry.RCD.Harmonic.TransformedColumns
import OAI.Geometry.RCD.Metric.NoExtraFactor
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-!
# The exact-normalization part of the published transformation theorem

This is the pointwise-in-scale consequence of Huang--Huang (2024),
Theorem 4.1(1)--(2), using the first-order criterion after Definition 2.7.
The initial first-order data are on a doubled ball. The additional
no-(n+1)-Euclidean condition is present explicitly, and will be supplied
by the proved finite-dimensional obstruction.
-/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

universe u

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem FirstOrderSplittingOn.mono_error {n : ℕ} {p : X} {r ε δ : ℝ}
    {u : Fin n → SobolevSpace μ hQ} {v : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p r ε u v) (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    FirstOrderSplittingOn μ hQ p r δ u v := by
  refine ⟨h.representative, h.continuous, h.harmonic, ?_, fun i j => (h.gram i j).trans hεδ⟩
  intro i
  filter_upwards [h.gradient i] with x hx
  have hs : (1 + ε) ^ 2 ≤ (1 + δ) ^ 2 := by nlinarith
  exact hx.trans hs

/-- A precisely cited conditional input. It retains both the flatness and
no-extra-factor hypotheses of Theorem 4.1. Only its first two conclusions
are requested here; interscale growth is not assumed as part of this input. -/
def LocalTransformationInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ β η : ℝ, 0 < β → 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ (p : X) (R : ℝ), 0 < R → -δ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * R) δ u v →
        (∀ r : ℝ, 0 < r → r ≤ R →
          (∃ f : X → Euclidean n, IsPointedApproximation p 0 r 1 δ f) ∧
          NoExtraEuclideanFactor n p r η) →
        ∀ r : ℝ, 0 < r → r ≤ R → ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p r β
            (transformedColumn (hausdorff n X) hX.quadratic u A)
            (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
          IsExactMeanNormalization (hausdorff n X) hX.quadratic
            (sobolevColumnMap (hausdorff n X) hX.quadratic u)
            (ball p r) measurableSet_ball A

end RegularPointCoordinates

end

end OAI
