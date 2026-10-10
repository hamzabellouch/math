import OAI.Geometry.RCD.Harmonic.QuadraticSegmentCost
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

/-! # Exact envelope values along a saturated transport segment -/

namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] {S : Set X}

theorem dual_segment_envelope (f : S → ℝ) (a m : S) (b x : X) (β s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hdual : ∀ u, f u+β ≤ dist (u : X) b^2)
    (ha : f a+β=dist (a : X) b^2)
    (hxa : dist x (a : X)=s*dist (a : X) b)
    (hxb : dist x b=(1-s)*dist (a : X) b)
    (hmax : f a-dist x (a : X)^2/s ≤ f m-dist x (m : X)^2/s) :
    f m-dist x (m : X)^2/s=f a-s*dist (a : X) b^2 := by
  have htri := dist_triangle (m : X) x b
  rw [dist_comm (m : X) x,hxb] at htri
  have hq := quadratic_segment_cost dist_nonneg hs hs1 htri
  have hd := hdual m
  have he : f a-dist x (a : X)^2/s=f a-s*dist (a : X) b^2 := by
    rw [hxa]
    field_simp
  rw [he] at hmax
  linarith

end RegularPointCoordinates

end OAI
