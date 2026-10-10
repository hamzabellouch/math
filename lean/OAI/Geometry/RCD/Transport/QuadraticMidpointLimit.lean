import OAI.Geometry.RCD.Transport.QuadraticMidpointError
import OAI.Geometry.RCD.Metric.PointedLiftDistances

namespace OAI

/-! # Passing normalized midpoint defects through fixed metric approximation maps -/

open Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem rescaled_fullMidpointDefect_tendsto (z : ℕ → X) (γ : ℕ → C(Time,X))
    (r : ℕ → ℝ) (hr : ∀ k, r k ≠ 0) {a b c d : ℝ}
    (ha : Tendsto (fun k => dist (z k) (γ k quadraticMidpointTime)/r k) atTop (𝓝 a))
    (hb : Tendsto (fun k => dist (z k) (γ k 0)/r k) atTop (𝓝 b))
    (hc : Tendsto (fun k => dist (z k) (γ k 1)/r k) atTop (𝓝 c))
    (hd : Tendsto (fun k => dist (γ k 0) (γ k 1)/r k) atTop (𝓝 d)) :
    Tendsto (fun k => fullMidpointDefect (z k) (γ k)/(r k)^2) atTop
      (𝓝 (a^2/2-(b^2/2+c^2/2)/2+d^2/8)) := by
  have hh := ((ha.pow 2 |>.div_const 2).sub
    (((hb.pow 2 |>.div_const 2).add (hc.pow 2 |>.div_const 2)).div_const 2)).add
      (hd.pow 2 |>.div_const 8)
  apply hh.congr
  intro k
  dsimp only [fullMidpointDefect]
  field_simp [hr k]

theorem pointed_fullMidpointDefect_zero {q z₀ x y b : Y} {S : ℝ}
    (p z : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y) (γ : ℕ → C(Time,X))
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hz : ∀ᶠ k in atTop, dist (z k) (p k) ≤ S * r k)
    (hγ : ∀ᶠ k in atTop, ∀ t : Time, dist (γ k t) (p k) ≤ S * r k)
    (hVz : Tendsto (fun k => V k (z k)) atTop (𝓝 z₀))
    (hV0 : Tendsto (fun k => V k (γ k 0)) atTop (𝓝 x))
    (hV1 : Tendsto (fun k => V k (γ k 1)) atTop (𝓝 y))
    (hVb : Tendsto (fun k => V k (γ k quadraticMidpointTime)) atTop (𝓝 b))
    (hdef : Tendsto (fun k => fullMidpointDefect (z k) (γ k)/(r k)^2) atTop (𝓝 0)) :
    dist z₀ b^2 = (dist z₀ x^2+dist z₀ y^2)/2-dist x y^2/4 := by
  have hm := rescaled_fullMidpointDefect_tendsto z γ r (fun k => (hr k).ne')
    (pointed_lift_distance_tendsto p r ε V hε hV z (fun k => γ k quadraticMidpointTime) hz (hγ.mono fun _ h => h _) hVz hVb)
    (pointed_lift_distance_tendsto p r ε V hε hV z (fun k => γ k 0) hz (hγ.mono fun _ h => h _) hVz hV0)
    (pointed_lift_distance_tendsto p r ε V hε hV z (fun k => γ k 1) hz (hγ.mono fun _ h => h _) hVz hV1)
    (pointed_lift_distance_tendsto p r ε V hε hV (fun k => γ k 0) (fun k => γ k 1)
      (hγ.mono fun _ h => h _) (hγ.mono fun _ h => h _) hV0 hV1)
  have he := tendsto_nhds_unique hm hdef
  linarith

end RegularPointCoordinates

end

end OAI
