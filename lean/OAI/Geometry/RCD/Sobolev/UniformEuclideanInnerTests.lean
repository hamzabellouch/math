import OAI.Geometry.RCD.Sobolev.UniformLocalizedLipschitzTests
import OAI.Geometry.RCD.Sobolev.MeasuredLawTestBound
import OAI.Geometry.RCD.Sobolev.EuclideanLawLocalizedTests

namespace OAI

/-! # Uniform Lipschitz testing of the inner Euclidean law -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem uniform_euclidean_inner_tests {n : ℕ} {S R : ℝ} (hS : 0<S) (hR : 0<R)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ φ : Euclidean n →ᵇ ℝ, LipschitzWith 1 φ → ‖φ‖≤1 →
      |(∫ z in ball 0 R, φ z ∂(normalizedBallPushforward μ (p k) (r k) S (V k) (hfin k) : Measure (Euclidean n)))-
        (∫ z in ball 0 R, φ z ∂(euclideanBallProbability n S : Measure (Euclidean n)))|<η := by
  let ν := fun k => normalizedBallPushforward μ (p k) (r k) S (V k) (hfin k)
  have hν := measured_approximation_laws_tendsto hS hV hfin hpos hε
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν
    (euclideanBallProbability_null_frontier hS hR)
  have hmr := (ENNReal.tendsto_toReal (measure_ne_top
    (euclideanBallProbability n S : Measure (Euclidean n)) (ball 0 R))).comp hm
  obtain ⟨χ,L,hχL,hχ,hχ0,hχlim⟩ := inner_ball_lipschitz_cutoff_sequence (0:Euclidean n) hR
  exact uniform_localized_lipschitz_tests hν ε hε measurableSet_ball hmr χ L hχL hχ hχ0 hχlim
    (fun k C hC F hF hb => measured_law_test_bound hS (hV k) (hfin k) (hpos k) C hC F hF hb)

end RegularPointCoordinates

end

end OAI
