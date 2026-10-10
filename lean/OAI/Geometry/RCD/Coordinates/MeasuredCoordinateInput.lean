import OAI.Geometry.RCD.Metric.MeasuredApproximation

namespace OAI

/-! # Measuring the actual coordinate approximations

De Philippis--Gigli (2018), Theorems1.2--1.3, specialize noncollapsed
measured convergence to Euclidean metric limits. On balls with Euclidean
boundary of zero measure, every measurable metric approximation has the
same normalized weak-measure limit. This fixed-radius bounded-Lipschitz
form retains the actual coordinate map used by the affine-fit argument.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Quantitative Euclidean specialization of noncollapsed measured
convergence. The input is metric approximation on a larger ball; the
output adds normalized test-integral control on the smaller ball. -/
def LocalMeasuredCoordinateInput {K : ℝ} {n : ℕ} (_hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ S ε : ℝ, 0 < S → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (p : X) (r : ℝ), 0 < r → -δ ≤ K * r ^ 2 →
      ∀ f : X → Euclidean n, Measurable f →
        IsPointedApproximation p 0 r (2 * S) δ f →
        IsMeasuredEuclideanApproximation (hausdorff n X) n p r S ε f

end RegularPointCoordinates

end

end OAI
