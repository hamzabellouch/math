import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.StoppingCoreSeparation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem stop_core_points_radius_separation {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i j : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hj : j ∈ cellRegionStops μ R hR k z Good) (hne : i ≠ j)
    (x y : Ambient d) (hx : x ∈ closedBall i.center (i.radius / 32))
    (hy : y ∈ closedBall j.center (j.radius / 32)) :
    max i.radius j.radius ≤ 16 * dist x y := by
  have hs := cellRegionStops_centers_separated μ R hR k z Good i j hi hj hne
  have hx' : dist x i.center ≤ i.radius / 32 := hx
  have hy' : dist y j.center ≤ j.radius / 32 := hy
  have h1 := dist_triangle i.center x j.center
  have h2 := dist_triangle x y j.center
  rw [dist_comm i.center x] at h1
  have hiM := le_max_left i.radius j.radius
  have hjM := le_max_right i.radius j.radius
  linarith

theorem survivor_stop_core_point_radius_separation {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (x y : Ambient d) (hx : x ∈ closedBall i.center (i.radius / 32))
    (hy : y ∈ cellRegionLimit μ R hR k z Good) :
    i.radius ≤ 16 * dist x y := by
  have hs := cellRegionLimit_stop_center_separated μ R hR k z Good i hi y hy
  have hx' : dist x i.center ≤ i.radius / 32 := hx
  have ht := dist_triangle y x i.center
  rw [dist_comm y x] at ht
  have hd : 0 ≤ dist x y := dist_nonneg
  linarith

theorem stop_core_parameter_radii_separated {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (F : Set (SupportCellDescendant μ R hR k z)) (hF : F ⊆ cellRegionStops μ R hR k z Good)
    (x : F → Ambient d) (a : F → Ambient n) (M : ℝ≥0)
    (hx : ∀ i : F, x i ∈ closedBall i.val.center (i.val.radius / 32))
    (hcoord : ∀ i j : F, dist (x i) (x j) ≤ (M : ℝ) * dist (a i) (a j)) :
    ∀ i j : F, i ≠ j → i.val.radius + j.val.radius ≤ 32 * (M : ℝ) * dist (a i) (a j) := by
  intro i j hij
  have hs := stop_core_points_radius_separation μ R hR k z Good i.val j.val
    (hF i.property) (hF j.property) (fun heq => hij (Subtype.ext heq))
    (x i) (x j) (hx i) (hx j)
  have hc := hcoord i j
  have hiM := le_max_left i.val.radius j.val.radius
  have hjM := le_max_right i.val.radius j.val.radius
  linarith

end

end RieszRectifiability

end OAI
