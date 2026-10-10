import OAI.Geometry.RCD.Coordinates.UniformNormalizedInnerTests
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # Restricting the actual measured approximation to an interior ball -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem inner_measured_approximation {n : ℕ} {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : R≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hεlim : Tendsto ε atTop (𝓝 0)) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, IsMeasuredEuclideanApproximation μ n (p k) (r k) R η (V k) := by
  intro η hη
  filter_upwards [hεlim.eventually (Iio_mem_nhds (show 0<η/3 by positivity)),
    uniform_normalized_inner_tests hS hR hRS hr hV hfin hpos hεlim η hη] with k hk htest
  refine ⟨((hV k).metric.restrict_radius (hr k) hR.le hRS (hε k)).mono_error (by linarith),
    (hV k).measurable,?_⟩
  intro φ hφ hb
  let F : Euclidean n →ᵇ ℝ := ⟨⟨φ,hφ.continuous⟩,⟨2,fun x y => by
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hb x,hb y])⟩⟩
  have hFn : ‖F‖≤1 := (BoundedContinuousFunction.norm_le zero_le_one).mpr
    (fun x => by change |φ x|≤1; exact hb x)
  exact (htest F hφ hFn).le

end RegularPointCoordinates

end

end OAI
