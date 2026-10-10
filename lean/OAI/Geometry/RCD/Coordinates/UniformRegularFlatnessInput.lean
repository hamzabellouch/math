import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # The precise local metric-flatness fact used by harmonic normalization -/

open Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def UniformRegularFlatnessInput {K : ℝ} {n : ℕ} (_hX : NoncollapsedRCD K n X) : Prop :=
  ∀ p : X, IsRegular n p → ∀ θ : ℝ, 0 < θ →
    ∃ D : ℝ, 0 < D ∧ ∀ q, dist p q ≤ D → ∀ r : ℝ, 0 < r → r ≤ D/4 →
      ∃ f : X → Euclidean n, IsPointedApproximation q 0 r 2 θ f

end RegularPointCoordinates

end

end OAI
