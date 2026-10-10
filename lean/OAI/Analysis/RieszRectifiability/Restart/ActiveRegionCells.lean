import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.StoppingCoreSeparation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def activeRegionCell (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) : Prop :=
  ∀ q : SupportCellDescendant μ R hR k z, q.depth ≤ i.depth → i.cell ⊆ q.cell → Good q

theorem activeRegionCell_good (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i) : Good i :=
  hi i le_rfl Subset.rfl

theorem activeRegionCell_ancestor (Good : SupportCellDescendant μ R hR k z → Prop)
    (i q : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i)
    (hdepth : q.depth ≤ i.depth) (hsub : i.cell ⊆ q.cell) : activeRegionCell Good q := by
  intro j hj hqj
  exact hi j (hj.trans hdepth) (hsub.trans hqj)

theorem activeRegionCell_of_region_limit (Good : SupportCellDescendant μ R hR k z → Prop)
    (x : Ambient d) (hx : x ∈ cellRegionLimit μ R hR k z Good)
    (i : SupportCellDescendant μ R hR k z) (hxi : x ∈ i.cell) : activeRegionCell Good i := by
  intro q _ hsub
  exact hx.2 q (hsub hxi)

theorem activeRegionCell_of_strict_stop_ancestor (Good : SupportCellDescendant μ R hR k z → Prop)
    (i q : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : q.depth < i.depth) (hsub : i.cell ⊆ q.cell) : activeRegionCell Good q := by
  intro j hj hqj
  exact hi.2 j (hj.trans_lt hdepth) (hsub.trans hqj)

theorem stop_not_activeRegionCell (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) : ¬ activeRegionCell Good i :=
  fun h => hi.1 (activeRegionCell_good Good i h)

theorem activeRegionCell_stop_scale_separation (Good : SupportCellDescendant μ R hR k z → Prop)
    (i q : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) (hq : activeRegionCell Good q) :
    i.radius / 8 ≤ dist i.center q.center + q.radius := by
  by_cases hdepth : q.depth ≤ i.depth
  · have hrad : i.radius ≤ q.radius :=
      latticeRadius_antitone R hR.le (Nat.add_le_add_left hdepth k)
    have hpos := i.radius_pos
    have hd : 0 ≤ dist i.center q.center := dist_nonneg
    linarith
  · have hdepth' : i.depth ≤ q.depth := (Nat.le_of_lt (Nat.lt_of_not_ge hdepth))
    have hout : q.center ∉ i.cell := by
      intro hmem
      have hsub := q.cell_nested_of_common_point i hdepth' q.center q.center_mem_cell hmem
      exact hi.1 (hq i hdepth' hsub)
    have hdist := i.distance_lower_of_clean_outside q.center
      (q.cell_subset_top q.center_mem_cell) hout
    rw [dist_comm q.center i.center] at hdist
    have hpos := q.radius_pos
    linarith

end

end RieszRectifiability

end OAI
