import OAI.Geometry.RCD.Metric.MeasuredBallLaw
import OAI.Geometry.RCD.Sobolev.MeasuredTestScaling

namespace OAI

/-! # The measured approximation controls every bounded Lipschitz law test -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem measured_law_test_bound {n : ℕ} {S : ℝ} (hS : 0<S)
    {μ : Measure X} {p : X} {r ε : ℝ} {V : X → Euclidean n}
    (hV : IsMeasuredEuclideanApproximation μ n p r S ε V)
    (hfin : μ (ball p (S*r))≠⊤) (hpos : 0<μ.real (ball p (S*r)))
    (C : ℝ≥0) (hC : 0<C) (F : Euclidean n → ℝ) (hF : LipschitzWith C F)
    (hFb : ∀ x, |F x|≤C) :
    |(∫ x, F x ∂(normalizedBallPushforward μ p r S V hfin : Measure (Euclidean n)))-
      (∫ x, F x ∂(euclideanBallProbability n S : Measure (Euclidean n)))|≤C*ε := by
  rw [euclideanBallProbability_integral hS]
  rw [normalizedBallPushforward_integral μ p r S V hfin hpos hV.measurable hF.continuous]
  exact hV.test_bound hC hF hFb

end RegularPointCoordinates

end

end OAI
