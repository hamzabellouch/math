import OAI.Geometry.RCD.Transport.MetricLimitSetMidpoint
import OAI.Geometry.RCD.Transport.MidpointThickening
import OAI.Geometry.RCD.Metric.ClosedThickeningMass

namespace OAI

/-! # The exact compact-set midpoint inequality in the actual metric limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_compact_midpoint {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S a : ℝ} (ha : 0 ≤ a) (hroom : 3*a < S)
    {A B : Set (Euclidean n)} (hA : IsCompact A) (hB : IsCompact B)
    (hAsub : A ⊆ closedBall 0 a) (hBsub : B ⊆ closedBall 0 a)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q)) :
    min ((Q : Measure (Euclidean n)).real A) ((Q : Measure (Euclidean n)).real B) ≤
      (Q : Measure (Euclidean n)).real (midpointSet A B) := by
  apply finite_measure_closed_of_thickenings _ (isCompact_midpointSet hA hB).isClosed
  intro κ hκ
  let δ := min (κ/2) ((S-3*a)/8)
  have hδ : 0 < δ := lt_min (half_pos hκ) (by linarith only [hroom])
  have hδκ : δ ≤ κ/2 := min_le_left _ _
  have hδS : δ ≤ (S-3*a)/8 := min_le_right _ _
  have hAt : thickening δ A ⊆ closedBall 0 (a+δ) :=
    (thickening_subset_ball_of_subset_closedBall hAsub).trans ball_subset_closedBall
  have hBt : thickening δ B ⊆ closedBall 0 (a+δ) :=
    (thickening_subset_ball_of_subset_closedBall hBsub).trans ball_subset_closedBall
  have hm := hX.metric_limit_set_midpoint_enlarged hn hK
    (S := S) (ρ := a+2*δ) (σ := a+δ) (η := a+δ) (κ := κ-δ)
    (by linarith only [ha,hroom]) (by positivity)
    (by linarith only [ha,hroom,hδS]) (by linarith only [hδ])
    (by linarith only [hκ,hδκ]) 0 isOpen_thickening isOpen_thickening hAt hBt
    (fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hAt hx)
    (fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hBt hx)
    (by linarith only [hroom,hδS]) p r ε V hr hε hcurv hVm hV hfin hlim
  have hleft : min ((Q : Measure (Euclidean n)).real A) ((Q : Measure (Euclidean n)).real B) ≤
      min ((Q : Measure (Euclidean n)).real (thickening δ A))
        ((Q : Measure (Euclidean n)).real (thickening δ B)) :=
    min_le_min (measureReal_mono (self_subset_thickening hδ A) (measure_ne_top _ _))
      (measureReal_mono (self_subset_thickening hδ B) (measure_ne_top _ _))
  have hsub := cthickening_midpointSet_thickening_subset A B
    (κ := κ-δ) (δ := δ) (by linarith only [hκ,hδκ])
  rw [sub_add_cancel] at hsub
  exact hleft.trans (hm.trans (measureReal_mono hsub (measure_ne_top _ _)))

end RegularPointCoordinates

end

end OAI
