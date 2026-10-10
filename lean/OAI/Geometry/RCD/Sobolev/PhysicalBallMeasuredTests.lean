import OAI.Geometry.RCD.Sobolev.PointedBallTestError
import OAI.Geometry.RCD.Sobolev.VanishingAnnuli

namespace OAI

/-! # Measured tests on the original physical inner balls -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem physical_ball_measured_test_tendsto {n : ℕ} {S ρ : ℝ}
    (hS : 0<S) (hρ : 0<ρ) (hρS : ρ≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0))
    (φ : Euclidean n →ᵇ ℝ) :
    Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (ρ*r k), φ (v k x) ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 ρ, φ z))) := by
  let ν := fun k => normalizedBallPushforward μ (p k) (r k) S (v k) (hfin k)
  have hν : Tendsto ν atTop (𝓝 (euclideanBallProbability n S)) :=
    measured_approximation_laws_tendsto hS hv hfin hpos hε
  have ht := euclidean_law_ball_test_tendsto hS hρ hν φ
  rw [euclideanBallProbability_setIntegral hS measurableSet_ball,
    inter_eq_left.mpr (ball_subset_ball hρS)] at ht
  have he : Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (ρ*r k), φ (v k x) ∂μ)-
      ∫ z in ball 0 ρ, φ z ∂(ν k : Measure (Euclidean n))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    let d := η/(2*(‖φ‖+1))
    have hd : 0<d := div_pos hη (by positivity)
    obtain ⟨δ,hδ,_,hevent⟩ := vanishing_annuli_of_euclidean_weak_limit hS hρ hν d hd
    have hsmall := hε.eventually (Iio_mem_nhds (half_pos hδ))
    filter_upwards [hevent,hsmall] with k hk hεk
    have hb := pointed_ball_test_error μ (hr k) hS.le hρS
      (show 2*ε k<δ by linarith) (hv k) (hfin k) (hpos k) φ
    rw [Real.dist_eq,sub_zero]
    apply hb.trans_lt
    have hm := mul_le_mul_of_nonneg_left hk.le (norm_nonneg φ)
    have hd' : ‖φ‖*d≤(‖φ‖+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
    have heq : (‖φ‖+1)*d=η/2 := by dsimp only [d]; field_simp
    rw [heq] at hd'
    exact (hm.trans hd').trans_lt (half_lt_self hη)
  simpa only [zero_add,sub_add_cancel] using he.add ht

end RegularPointCoordinates

end

end OAI
