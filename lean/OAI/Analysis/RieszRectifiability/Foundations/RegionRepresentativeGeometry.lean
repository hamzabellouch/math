import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CappedStopPairScale

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellRegionRepresentatives {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) : Set (Ambient d) :=
  cellRegionLimit μ R hR k z Good ∪ range (fun i : cellRegionStops μ R hR k z Good => i.val.center)

theorem cellRegionRepresentatives_subset_top {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    cellRegionRepresentatives μ R hR k z Good ⊆ cleanSupportCell μ R hR k z := by
  rintro x (hx | ⟨i, rfl⟩)
  · exact hx.1
  · exact i.val.cell_subset_top i.val.center_mem_cell

theorem stop_radius_le_representative_distance {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (y : Ambient d) (hy : y ∈ cellRegionRepresentatives μ R hR k z Good) (hne : i.center ≠ y) :
    i.radius ≤ 8 * dist i.center y := by
  rcases hy with hy | ⟨j, rfl⟩
  · simpa only [dist_comm y i.center] using! cellRegionLimit_stop_center_separated μ R hR k z Good i hi y hy
  · have hij : i ≠ j.val := fun h => hne (congrArg SupportCellDescendant.center h)
    exact (le_max_left i.radius j.val.radius).trans
      (cellRegionStops_centers_separated μ R hR k z Good i j.val hi j.property hij)

theorem exists_good_pair_cell_for_representatives {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (x y : Ambient d) (hx : x ∈ cellRegionRepresentatives μ R hR k z Good)
    (hy : y ∈ cellRegionRepresentatives μ R hR k z Good) (hne : x ≠ y) :
    ∃ q : SupportCellDescendant μ R hR k z, Good q ∧ x ∈ q.cell ∧
      q.radius ≤ 512 * dist x y ∧ dist x y ≤ 512 * q.radius ∧
      x ∈ ball q.center (1024 * q.radius) ∧ y ∈ ball q.center (1024 * q.radius) := by
  have hytop := cellRegionRepresentatives_subset_top μ R hR k z Good hy
  rcases hx with hx | ⟨i, rfl⟩
  · obtain ⟨q, hxq, hupper, hlower, hxball, hyball⟩ :=
      exists_pair_scale_support_descendant μ R hR k z x y hx.1 hytop hne
    exact ⟨q, hx.2 q hxq, hxq, by linarith [dist_nonneg (x := x) (y := y)], hlower, hxball, hyball⟩
  · have hpositive : 0 < i.val.depth := Nat.pos_of_ne_zero (fun h => i.property.1 (hroot i.val h))
    exact exists_good_pair_cell_for_stop_center μ R hR k z Good i.val i.property hpositive y hytop
      (stop_radius_le_representative_distance μ R hR k z Good i.val i.property y hy hne)

end

end RieszRectifiability

end OAI
