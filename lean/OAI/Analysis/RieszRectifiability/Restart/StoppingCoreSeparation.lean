import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CellRegionStopping

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.mem_cell_of_mem_support_near_center {d : ℕ}
    {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
    {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (x : Ambient d)
    (hx : x ∈ μ.support) (hclean : x ∉ supportLatticeExceptional μ R hR)
    (hnear : dist x i.center < i.radius / 8) : x ∈ i.cell := by
  exact ⟨(supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).1
    ⟨hx, hnear⟩, hclean⟩

theorem SupportCellDescendant.distance_lower_of_clean_outside {d : ℕ}
    {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
    {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z) (hout : x ∉ i.cell) :
    i.radius / 8 ≤ dist x i.center := by
  by_contra hbad
  exact hout (i.mem_cell_of_mem_support_near_center x
    (supportLatticeCell_subset_support μ R hR k z hx.1) hx.2 (lt_of_not_ge hbad))

theorem cellRegionStops_centers_separated {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i j : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hj : j ∈ cellRegionStops μ R hR k z Good) (hne : i ≠ j) :
    max i.radius j.radius ≤ 8 * dist i.center j.center := by
  have hd := cellRegionStops_pairwise_disjoint μ R hR k z Good hi hj hne
  have hji : j.center ∉ i.cell := fun h => Set.disjoint_left.mp hd h j.center_mem_cell
  have hij : i.center ∉ j.cell := fun h => Set.disjoint_left.mp hd i.center_mem_cell h
  have hiD := i.distance_lower_of_clean_outside j.center (j.cell_subset_top j.center_mem_cell) hji
  have hjD := j.distance_lower_of_clean_outside i.center (i.cell_subset_top i.center_mem_cell) hij
  rw [dist_comm j.center i.center] at hiD
  exact max_le (by linarith) (by linarith)

theorem cellRegionLimit_stop_center_separated {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (x : Ambient d) (hx : x ∈ cellRegionLimit μ R hR k z Good) :
    i.radius ≤ 8 * dist x i.center := by
  have hout : x ∉ i.cell := fun h => hi.1 (hx.2 i h)
  have h := i.distance_lower_of_clean_outside x hx.1 hout
  linarith

end

end RieszRectifiability

end OAI
