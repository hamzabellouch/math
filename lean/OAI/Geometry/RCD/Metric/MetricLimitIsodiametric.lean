import OAI.Geometry.RCD.Transport.MetricLimitCompactMidpoint
import OAI.Geometry.RCD.Transport.ReflectedMidpointMass

namespace OAI

/-! # Sharp local Euclidean diameter bounds from an actual RCD metric limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_isodiametric {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S a : ℝ} (ha : 0 ≤ a) (hroom : 3*a < S)
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
    ∀ A : Set (Euclidean n), IsCompact A → A ⊆ closedBall 0 a →
      volume.real A ≤ volume.real (closedBall (0 : Euclidean n) (diam A/2)) := by
  obtain ⟨c,hc,hQ⟩ := hX.metric_limit_measure hn hK (by linarith only [ha,hroom])
    p r ε V hr hε hcurv hVm hV hfin hlim hpositive
  intro A hA hAsub
  have hNsub : Neg.neg '' A ⊆ closedBall 0 a := by
    rintro x ⟨y,hy,rfl⟩
    simpa only [mem_closedBall,dist_zero_right,norm_neg] using hAsub hy
  exact compact_volume_le_diameter_ball_of_midpoint (Q : Measure (Euclidean n))
    (by linarith only [ha,hroom]) hc hQ hA hAsub
    (hX.metric_limit_compact_midpoint hn hK ha hroom hA (hA.image continuous_neg)
      hAsub hNsub p r ε V hr hε hcurv hVm hV hfin hlim)

end RegularPointCoordinates

end

end OAI
