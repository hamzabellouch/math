import OAI.Geometry.RCD.Metric.MetricLimitAbsoluteContinuity
import OAI.Geometry.RCD.Transport.RestrictedMidpointContraction
import OAI.Geometry.RCD.Transport.LocalMidpointDensityConstant

namespace OAI

/-! # Locally constant density of the actual weak metric-law limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_local_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S : ℝ} (hS : 0 < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q))
    (hpositive : ∀ x ∈ ball (0 : Euclidean n) S, ∀ t : ℝ, 0 < t →
      0 < (Q : Measure (Euclidean n)).real (ball x t)) :
    ∀ z ∈ ball (0 : Euclidean n) S, ∃ d : ℝ, 0 < d ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ᵐ x ∂volume.restrict (ball z d),
        (((Q : Measure (Euclidean n)).restrict (ball 0 S)).rnDeriv volume x).toReal=c := by
  let ν : FiniteMeasure (Euclidean n) :=
    ⟨(Q : Measure (Euclidean n)).restrict (ball 0 S),inferInstance⟩
  have hac : (ν : Measure (Euclidean n)) ≪ volume :=
    hX.metric_limit_absolutelyContinuous hn hK hS p r ε V hr hε hcurv hVm hV hfin hlim hpositive
  intro z hz
  obtain ⟨δ,hδ,hc⟩ := hX.metric_limit_local_contraction hn hK hS p r ε V hr hε hcurv
    hVm hV hfin hlim hpositive z hz
  have hzS : ‖z‖ < S := by simpa only [mem_ball,dist_zero_right] using hz
  let d := min δ ((S-‖z‖)/4)
  have hd : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdS : d ≤ (S-‖z‖)/4 := min_le_right _ _
  have hsmall : ∀ u ∈ ball z d, ∀ v ∈ ball z d, ∀ t : ℝ, 0 < t → t ≤ d →
      (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball v t) ≤
        (Q : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (u+v)) (t/2)) := by
    intro u hu v hv t ht htd
    exact hc u (ball_subset_ball hdδ hu) v (ball_subset_ball hdδ hv) t ht (htd.trans hdδ)
  have hrst := restrict_midpoint_contraction (Q : Measure (Euclidean n)) z hd
    (show ‖z‖+2*d < S by linarith) hsmall
  obtain ⟨c,hc0,hvalue⟩ := local_midpoint_density_constant (by omega) ν hac z hd hrst
  exact ⟨d/4,by positivity,c,hc0,hvalue⟩

end RegularPointCoordinates

end

end OAI
