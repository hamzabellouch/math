import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.RegularLatticeScales

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netAncestor_forced_near_center {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x z : E) (hz : (z : X) ∈ (N k).points)
    (hxz : dist (x : X) (z : X) < latticeRadius R k / 4) :
    netAncestor N k (t + 1) x = z := by
  rw [netAncestor_first_parent]
  apply Subtype.ext
  apply (N k).parent_forced _ _ hz
  have hb := netAncestor_dist_le_latticeRadius R hR N (k + 1) t x
  rw [latticeRadius_succ] at hb
  have ht := dist_triangle (netAncestor N (k + 1) t x : X) (x : X) (z : X)
  rw [dist_comm (netAncestor N (k + 1) t x : X) (x : X)] at ht
  have hp := latticeRadius_pos R hR k
  linarith

theorem netAncestor_consistent_on_net {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x : E) (hx : (x : X) ∈ (N (k + t)).points) :
    (netAncestor N k t x : X) ∈ (N k).points := by
  cases t with
  | zero => simpa only [Nat.add_zero, netAncestor_zero] using! hx
  | succ t => exact netAncestor_mem N k t x

end

end RieszRectifiability

end OAI
