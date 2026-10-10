import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitModel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cellRegionStoppingScale_eq_top_of_far {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (x : Ambient d) (hfar : 3 * latticeRadius R k ≤ dist x (z : Ambient d)) :
    cellRegionStoppingScale μ R hR k z Good x = latticeRadius R k := by
  apply le_antisymm (cellRegionStoppingScale_le_top μ R hR k z Good x)
  unfold cellRegionStoppingScale cappedStoppingDistance
  apply le_ciInf
  intro i
  cases i with
  | none => exact le_rfl
  | some i =>
    have hc := (supportCellRoot μ R hR k z).dist_center_of_mem i.val.center
      (i.val.cell_subset_top i.val.center_mem_cell)
    have hc' : dist i.val.center (z : Ambient d) ≤ 2 * latticeRadius R k := by
      simpa only [supportCellRoot, SupportCellDescendant.radius, Nat.add_zero] using! hc
    have ht := dist_triangle x i.val.center (z : Ambient d)
    have hr := i.val.radius_pos
    change latticeRadius R k ≤ dist x i.val.center + i.val.radius
    linarith

theorem active_region_limit_fixes_exterior_plane {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (u : S (supportCellRoot μ R hR k z))
    (hfar : 3 * latticeRadius R k ≤ dist (u : Ambient d) (z : Ambient d)) :
    f u = u := by
  have hD := cellRegionStoppingScale_eq_top_of_far μ R hR k z Good u hfar
  have hr0 := latticeRadius_pos R hR k
  have h := active_region_limit_eq_parameter_of_large_scale μ R hR k z Good S hS f
    (fun v => hmodel.2.2.1.tendsto_at v) u 0 (by
      simp only [activeRegionParameterMap, id_eq, zero_add]
      rw [hD, latticeRadius_succ]
      linarith)
  simpa only [activeRegionParameterMap, id_eq] using! h

end

end RieszRectifiability

end OAI
