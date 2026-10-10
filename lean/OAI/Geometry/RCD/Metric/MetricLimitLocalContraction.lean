import OAI.Geometry.RCD.Transport.MetricLimitMidpointExact

namespace OAI

/-! # Local midpoint contraction after shrinking the pole ball

Every interior point has a neighborhood with the dimension-sharp ball
contraction inequality. Only positive interior mass of the actual weak
limit is used to shrink the pole; no density formula is assumed.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_local_contraction {K : ℝ} {n : ℕ}
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
    ∀ z ∈ ball (0 : Euclidean n) S, ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ ball z δ, ∀ y ∈ ball z δ, ∀ b : ℝ, 0 < b → b ≤ δ →
        (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b) ≤
          (Q : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (x+y)) (b/2)) := by
  intro z hz
  have hzS : ‖z‖ < S := by simpa only [mem_ball,dist_zero_right] using hz
  let g := S-‖z‖
  let δ := g/32
  let ρ := ‖z‖+g/2
  let η := g/8
  have hg : 0 < g := sub_pos.mpr hzS
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hρS : ρ < S := by dsimp only [ρ,g]; linarith
  have hroom : ρ+2*η < S := by dsimp only [ρ,η,g]; linarith
  have hδη : 2*δ ≤ η := by dsimp only [δ,η]; linarith
  have hδρ : ‖z‖+2*δ < ρ := by dsimp only [δ,ρ]; linarith
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy b hb hbδ
  have hxn : ‖x‖ < ‖z‖+δ := by
    have hh := dist_triangle x z 0
    have hx' : dist x z < δ := hx
    simp only [dist_zero_right] at hh
    linarith
  have hyn : ‖y‖ < ‖z‖+δ := by
    have hh := dist_triangle y z 0
    have hy' : dist y z < δ := hy
    simp only [dist_zero_right] at hh
    linarith
  have hxS : x ∈ ball (0 : Euclidean n) S := by
    rw [mem_ball,dist_zero_right]
    linarith
  have hyS : y ∈ ball (0 : Euclidean n) S := by
    rw [mem_ball,dist_zero_right]
    linarith
  apply finite_measure_closedBall_of_enlargements (Q : Measure (Euclidean n))
  intro κ hκ
  let a := min δ κ
  have ha : 0 < a := lt_min hδ hκ
  have haδ : a ≤ δ := min_le_left _ _
  have haκ : a ≤ κ := min_le_right _ _
  have hxa : ‖x‖+a < ρ := by linarith
  have hyb : ‖y‖+b < ρ := by linarith
  have hxaη : closedBall x a ⊆ closedBall z η := by
    intro u hu
    have hh := dist_triangle u x z
    have hu' : dist u x ≤ a := hu
    have hx' : dist x z < δ := hx
    change dist u z ≤ η
    linarith
  have hybη : closedBall y b ⊆ closedBall z η := by
    intro u hu
    have hh := dist_triangle u y z
    have hu' : dist u y ≤ b := hu
    have hy' : dist y z < δ := hy
    change dist u z ≤ η
    linarith
  have hm := hX.metric_limit_midpoint_exact hn hK hS hρ hρS x y z hxa hyb hxaη hybη
    hroom p r ε V hr hε hcurv hVm hV hfin hlim (hpositive x hxS a ha) (hpositive y hyS b hb)
  have hsub : closedBall ((1/2:ℝ) • (x+y)) ((a+b)/2) ⊆
      closedBall ((1/2:ℝ) • (x+y)) (b/2+κ) := closedBall_subset_closedBall (by linarith)
  exact hm.trans (measureReal_mono hsub (measure_ne_top _ _))

end RegularPointCoordinates

end

end OAI
