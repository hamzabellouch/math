import OAI.Geometry.RCD.Sobolev.PointedMetricBallTestError
import OAI.Geometry.RCD.Sobolev.WeakLimitAnnuli

namespace OAI

/-! # Measured tests on the original physical inner balls -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem physical_ball_weak_test_tendsto {n : ℕ} {S ρ : ℝ}
    (hS : 0<S) (hρ : 0<ρ) (hρS : ρ≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hvm : ∀ k, Measurable (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0))
    {Q : ProbabilityMeasure (Euclidean n)}
    (hweak : Tendsto (fun k => normalizedBallPushforward μ (p k) (r k) S (v k) (hfin k))
      atTop (𝓝 Q))
    (hnull : (Q : Measure (Euclidean n)) (sphere 0 ρ)=0)
    (φ : Euclidean n →ᵇ ℝ) :
    Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (ρ*r k), φ (v k x) ∂μ) atTop
      (𝓝 (∫ z in ball 0 ρ, φ z ∂(Q : Measure (Euclidean n)))) := by
  let ν := fun k => normalizedBallPushforward μ (p k) (r k) S (v k) (hfin k)
  have hν : Tendsto ν atTop (𝓝 Q) := hweak
  have hfront : (Q : Measure (Euclidean n)) (frontier (ball 0 ρ))=0 :=
    measure_mono_null frontier_ball_subset_sphere hnull
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν hfront
  have hmr := (ENNReal.tendsto_toReal (measure_ne_top
    (Q : Measure (Euclidean n)) (ball 0 ρ))).comp hm
  obtain ⟨χ,hχ,hχ0,hχlim⟩ := inner_ball_cutoff_sequence (0:Euclidean n) hρ
  have ht := weak_localized_test_tendsto hν measurableSet_ball hmr χ hχ hχ0 hχlim φ
  have he : Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (ρ*r k), φ (v k x) ∂μ)-
      ∫ z in ball 0 ρ, φ z ∂(ν k : Measure (Euclidean n))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    let d := η/(2*(‖φ‖+1))
    have hd : 0<d := div_pos hη (by positivity)
    obtain ⟨δ,hδ,_,hevent⟩ := vanishing_annuli_of_weak_limit hρ hν hnull d hd
    have hsmall := hε.eventually (Iio_mem_nhds (half_pos hδ))
    filter_upwards [hevent,hsmall] with k hk hεk
    have hb := pointed_metric_ball_test_error μ (hr k) hS.le hρS
      (show 2*ε k<δ by linarith) (hv k) (hvm k) (hfin k) (hpos k) φ
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
