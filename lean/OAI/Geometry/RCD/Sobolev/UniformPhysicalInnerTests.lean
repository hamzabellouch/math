import OAI.Geometry.RCD.Sobolev.UniformEuclideanInnerTests
import OAI.Geometry.RCD.Sobolev.PointedBallTestError
import OAI.Geometry.RCD.Sobolev.VanishingAnnuli

namespace OAI

/-! # Uniform bounded Lipschitz testing on the physical inner balls -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem uniform_physical_inner_tests {n : ℕ} {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : R≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ φ : Euclidean n →ᵇ ℝ, LipschitzWith 1 φ → ‖φ‖≤1 →
      |(μ.real (ball (p k) (S*r k)))⁻¹*(∫ x in ball (p k) (R*r k), φ (V k x) ∂μ)-
        (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 R, φ z)|<η := by
  let ν := fun k => normalizedBallPushforward μ (p k) (r k) S (V k) (hfin k)
  have hν := measured_approximation_laws_tendsto hS hV hfin hpos hε
  intro η hη
  obtain ⟨δ,hδ,_,hann⟩ := vanishing_annuli_of_euclidean_weak_limit hS hR hν (η/3) (by positivity)
  have hsmall := hε.eventually (Iio_mem_nhds (half_pos hδ))
  have heuc := uniform_euclidean_inner_tests hS hR hV hfin hpos hε (η/3) (by positivity)
  filter_upwards [hann,hsmall,heuc] with k hk hεk hek
  intro φ hφ hφn
  have hphys := pointed_ball_test_error μ (hr k) hS.le hRS (show 2*ε k<δ by linarith)
    (hV k) (hfin k) (hpos k) φ
  have hb := hphys.trans (mul_le_of_le_one_left measureReal_nonneg hφn)
  have he := hek φ hφ hφn
  rw [euclideanBallProbability_setIntegral hS measurableSet_ball,
    inter_eq_left.mpr (ball_subset_ball hRS)] at he
  have htriangle := abs_sub_le
    ((μ.real (ball (p k) (S*r k)))⁻¹*(∫ x in ball (p k) (R*r k), φ (V k x) ∂μ))
    (∫ z in ball 0 R, φ z ∂(ν k : Measure (Euclidean n)))
    ((volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 R, φ z))
  linarith

end RegularPointCoordinates

end

end OAI
