import OAI.Geometry.RCD.Metric.MetricLawMassGeneral
import OAI.Geometry.RCD.Metric.PointedBoundedLifts

namespace OAI

/-! # Physical ball inclusions through the prescribed pointed maps -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_ball_sandwich {p x : X} {q z : Y} {r S ε a t b : ℝ}
    (hr : 0 < r) {V : X → Y} (hV : IsPointedApproximation p q r S ε V)
    (hx : dist x p ≤ S*r) (hsub : ball x (a*r) ⊆ ball p (S*r))
    (hat : a+ε+dist (V x) z < t) (htb : t+ε+dist (V x) z < b) :
    ball x (a*r) ⊆ V ⁻¹' ball z t ∩ ball p (S*r) ∧
      V ⁻¹' closedBall z t ∩ ball p (S*r) ⊆ ball x (b*r) := by
  constructor
  · intro y hy
    refine ⟨?_,hsub hy⟩
    have hd := (abs_le.mp (hV.2.1 y x (hsub hy).le hx)).2
    have hsmall : dist y x/r < a := (div_lt_iff₀ hr).mpr hy
    have htri := dist_triangle (V y) (V x) z
    change dist (V y) z < t
    linarith
  · rintro y ⟨hy,hyS⟩
    have hd := (abs_le.mp (hV.2.1 y x hyS.le hx)).1
    have htri := dist_triangle (V y) z (V x)
    rw [dist_comm z (V x)] at htri
    change dist (V y) z ≤ t at hy
    change dist y x < b*r
    apply (div_lt_iff₀ hr).mp
    linarith

theorem pointed_ball_sandwich_eventually {q z : Y} {S a t b T : ℝ}
    (p x : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hx : ∀ k, dist (x k) (p k) ≤ T*r k)
    (hxz : Tendsto (fun k => V k (x k)) atTop (𝓝 z))
    (hTS : T ≤ S) (haT : a+T ≤ S) (hat : a < t) (htb : t < b) :
    ∀ᶠ k in atTop,
      ball (x k) (a*r k) ⊆ (V k) ⁻¹' ball z t ∩ ball (p k) (S*r k) ∧
      (V k) ⁻¹' closedBall z t ∩ ball (p k) (S*r k) ⊆ ball (x k) (b*r k) := by
  have he : Tendsto (fun k => ε k+dist (V k (x k)) z) atTop (𝓝 0) := by
    simpa only [dist_self,add_zero] using
      hε.add (hxz.dist (tendsto_const_nhds (x := z)))
  filter_upwards [he.eventually (gt_mem_nhds (sub_pos.mpr hat)),
    he.eventually (gt_mem_nhds (sub_pos.mpr htb))] with k hka hkb
  apply pointed_ball_sandwich (hr k) (hV k)
    ((hx k).trans (mul_le_mul_of_nonneg_right hTS (hr k).le))
  · apply ball_subset_ball'
    have hm := mul_le_mul_of_nonneg_right haT (hr k).le
    nlinarith [hx k]
  · linarith
  · linarith

end RegularPointCoordinates

end

end OAI
