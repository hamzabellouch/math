import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.StoppingCoreSeparation
import OAI.Analysis.RieszRectifiability.Flatness.AdjacentCellPlaneDirections

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_good_pair_cell_for_stop_center {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) (hpositive : 0 < i.depth)
    (y : Ambient d) (hy : y ∈ cleanSupportCell μ R hR k z)
    (hsep : i.radius ≤ 8 * dist i.center y) :
    ∃ q : SupportCellDescendant μ R hR k z, Good q ∧ i.center ∈ q.cell ∧
      q.radius ≤ 512 * dist i.center y ∧ dist i.center y ≤ 512 * q.radius ∧
      i.center ∈ ball q.center (1024 * q.radius) ∧ y ∈ ball q.center (1024 * q.radius) := by
  have hD : 0 < dist i.center y := by have h := i.radius_pos; linarith
  let t := annularLatticeDepth R k (dist i.center y) hD
  let m := min t (i.depth - 1)
  obtain ⟨q, hq, hsub, hcenter⟩ := i.exists_ancestor_at_depth m (by dsimp [m]; omega)
  have hgood : Good q := hi.2 q (by dsimp [m] at hq; omega) hsub
  have hlower : dist i.center y ≤ 512 * q.radius := by
    have htop : dist i.center y ≤ 8 * latticeRadius R k := by
      have h := cleanSupportCell_pair_distance_le μ R hR k z i.center y
        (i.cell_subset_top i.center_mem_cell) hy
      have hr := latticeRadius_pos R hR k
      linarith
    have hscale := annularLatticeDepth_radius_lower R hR k (dist i.center y) hD htop
    have hle : latticeRadius R (k + t) ≤ q.radius := by
      apply latticeRadius_antitone R hR.le
      dsimp [m] at hq
      omega
    change dist i.center y ≤ 512 * latticeRadius R (k + t) at hscale
    linarith
  have hupper : q.radius ≤ 512 * dist i.center y := by
    by_cases ht : t ≤ i.depth - 1
    · have hqt : q.depth = t := by simpa only [m, min_eq_left ht] using! hq
      have h := annularLatticeDepth_radius_upper R k (dist i.center y) hD
      change latticeRadius R (k + t) ≤ dist i.center y / 8 at h
      change latticeRadius R (k + q.depth) ≤ _
      rw [hqt]
      linarith
    · have hqi : q.depth = i.depth - 1 := by
        simpa only [m, min_eq_right (le_of_not_ge ht)] using! hq
      have hscale := i.radius_parent_eq_64 q (by omega)
      linarith
  have hxc := q.dist_center_of_mem i.center hcenter
  have htri := dist_triangle y i.center q.center
  rw [dist_comm y i.center] at htri
  have hr := q.radius_pos
  refine ⟨q, hgood, hcenter, hupper, hlower, ?_, ?_⟩
  · rw [mem_ball]
    linarith
  · rw [mem_ball]
    linarith

end

end RieszRectifiability

end OAI
