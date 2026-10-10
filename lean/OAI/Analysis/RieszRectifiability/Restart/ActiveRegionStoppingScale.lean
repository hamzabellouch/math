import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionCells
import OAI.Analysis.RieszRectifiability.Restart.CappedStoppingDistance

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

def cellRegionStoppingScale : Ambient d → ℝ :=
  cappedStoppingDistance (latticeRadius R k)
    (fun i : {i // activeRegionCell Good i} => i.val.center)
    (fun i => i.val.radius)

theorem cellRegionStoppingScale_nonneg (x : Ambient d) :
    0 ≤ cellRegionStoppingScale μ R hR k z Good x :=
  cappedStoppingDistance_nonneg _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le) x

theorem cellRegionStoppingScale_le_top (x : Ambient d) :
    cellRegionStoppingScale μ R hR k z Good x ≤ latticeRadius R k :=
  cappedStoppingDistance_le_cap _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le) x

theorem cellRegionStoppingScale_le_center_radius (x : Ambient d)
    (i : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i) :
    cellRegionStoppingScale μ R hR k z Good x ≤ dist x i.center + i.radius :=
  cappedStoppingDistance_le_center_radius (latticeRadius R k)
    (fun j : {j : SupportCellDescendant μ R hR k z // activeRegionCell Good j} => j.val.center)
    (fun j => j.val.radius) (latticeRadius_pos R hR k).le
    (fun j => j.val.radius_pos.le) x ⟨i, hi⟩

theorem cellRegionStoppingScale_le_add_dist (x y : Ambient d) :
    cellRegionStoppingScale μ R hR k z Good x ≤
      cellRegionStoppingScale μ R hR k z Good y + dist x y :=
  cappedStoppingDistance_le_add_dist _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le) x y

theorem cellRegionStoppingScale_lipschitz :
    LipschitzWith 1 (cellRegionStoppingScale μ R hR k z Good) :=
  cappedStoppingDistance_lipschitz _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le)

theorem cellRegionStoppingScale_eq_zero_of_region_limit (x : Ambient d)
    (hx : x ∈ cellRegionLimit μ R hR k z Good) :
    cellRegionStoppingScale μ R hR k z Good x = 0 := by
  apply le_antisymm _ (cellRegionStoppingScale_nonneg μ R hR k z Good x)
  by_contra h
  have hpos : 0 < cellRegionStoppingScale μ R hR k z Good x := lt_of_not_ge h
  obtain ⟨t, ht⟩ := exists_annular_lattice_depth R k
    (cellRegionStoppingScale μ R hR k z Good x) hpos
  obtain ⟨i, hi, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx.1 t
  have hactive := activeRegionCell_of_region_limit Good x hx i hi.2
  have hbound := cellRegionStoppingScale_le_center_radius μ R hR k z Good x i hactive
  have hdist := i.dist_center_of_mem x hi.2
  have hrad : i.radius ≤ cellRegionStoppingScale μ R hR k z Good x / 8 := by
    simpa only [SupportCellDescendant.radius, hi.1] using! ht
  linarith

theorem cellRegionStoppingScale_lower_at_stop
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) :
    i.radius / 8 ≤ cellRegionStoppingScale μ R hR k z Good i.center := by
  unfold cellRegionStoppingScale cappedStoppingDistance
  apply le_ciInf
  intro q
  cases q with
  | none =>
    change i.radius / 8 ≤ latticeRadius R k
    have hr : i.radius ≤ latticeRadius R k :=
      latticeRadius_antitone R hR.le (Nat.le_add_right k i.depth)
    have hp := i.radius_pos
    linarith
  | some q => exact activeRegionCell_stop_scale_separation Good i q.val hi q.property

theorem cellRegionStoppingScale_upper_at_stop
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) :
    cellRegionStoppingScale μ R hR k z Good i.center ≤ 192 * i.radius := by
  by_cases hzero : i.depth = 0
  · have hr : i.radius = latticeRadius R k := by simp only [SupportCellDescendant.radius, hzero, Nat.add_zero]
    have hcap := cellRegionStoppingScale_le_top μ R hR k z Good i.center
    rw [← hr] at hcap
    have hp := i.radius_pos
    linarith
  · obtain ⟨q, hq, hsub, hcenter⟩ := i.exists_ancestor_at_depth (i.depth - 1) (Nat.sub_le _ _)
    have hdepth : i.depth = q.depth + 1 := by omega
    have hactive := activeRegionCell_of_strict_stop_ancestor Good i q hi (by omega) hsub
    have hbound := cellRegionStoppingScale_le_center_radius μ R hR k z Good i.center q hactive
    have hdist := q.dist_center_of_mem i.center hcenter
    have hr : q.radius = 64 * i.radius := by
      change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
      rw [hdepth, ← Nat.add_assoc, latticeRadius_succ]
      ring
    linarith

theorem cellRegionStoppingScale_stop_core_bounds
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) (x : Ambient d)
    (hx : dist x i.center ≤ i.radius / 16) :
    i.radius / 16 ≤ cellRegionStoppingScale μ R hR k z Good x ∧
      cellRegionStoppingScale μ R hR k z Good x ≤ 193 * i.radius := by
  have hl := cellRegionStoppingScale_lower_at_stop μ R hR k z Good i hi
  have hu := cellRegionStoppingScale_upper_at_stop μ R hR k z Good i hi
  have hxy := cellRegionStoppingScale_le_add_dist μ R hR k z Good x i.center
  have hyx := cellRegionStoppingScale_le_add_dist μ R hR k z Good i.center x
  rw [dist_comm i.center x] at hyx
  have hp := i.radius_pos
  constructor <;> linarith

end

end RieszRectifiability

end OAI
