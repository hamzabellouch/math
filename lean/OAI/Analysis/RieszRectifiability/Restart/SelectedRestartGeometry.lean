import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartTree

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

theorem SupportCellDescendant.compose_root (q : SupportCellDescendant μ R hR k z) :
    q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) = q := by
  refine (q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)).eq_of_common_point_same_depth
    q rfl q.center ?_ q.center_mem_cell
  rw [SupportCellDescendant.compose_cell]
  exact q.center_mem_cell

theorem relative_restart_root_active
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) :
    activeRegionCell (relativeRestartGood Bad q)
      (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) := by
  intro i hi _
  have hi0 : i.depth = 0 := Nat.eq_zero_of_le_zero hi
  rw [i.eq_root_of_zero_depth hi0]
  change ¬ Bad (q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩))
  rwa [SupportCellDescendant.compose_root]

theorem selected_restart_remainder_of_bad_root
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : Bad q) (E : Set (Ambient d)) :
    selectedRestartRemainder Bad q E = ∅ := by
  let root := supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
  have hroot : root ∈ relativeSelectedRestartStops Bad q E := by
    refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
    · change ¬ ¬ Bad (q.compose root)
      rw [SupportCellDescendant.compose_root]
      exact not_not.mpr hq
    · intro j hj _
      exact False.elim (Nat.not_lt_zero j.depth hj)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2 (Or.inr (mem_iUnion.mpr ⟨⟨root, hroot⟩, hx.1⟩))

theorem selected_restart_stops_of_good_root
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) (E : Set (Ambient d)) :
    relativeSelectedRestartStops Bad q E =
      activeCellSelectedStopSet μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
        (relativeRestartGood Bad q)
        (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) E := by
  ext i
  constructor
  · intro hi
    have hi0 : i.depth ≠ 0 := by
      intro hh
      have hgood := activeRegionCell_good (relativeRestartGood Bad q) _
        (relative_restart_root_active Bad q hq)
      exact hi.1.1 (i.eq_root_of_zero_depth hh ▸ hgood)
    exact ⟨⟨hi.1, Nat.pos_of_ne_zero hi0, i.cell_subset_top⟩,
      hi.2.resolve_left hi0⟩
  · intro hi
    exact ⟨hi.1.1, Or.inr hi.2⟩

theorem selected_restart_parent_eq
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    selectedRestartParent Bad q E =
      cellRegionLimit μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ (relativeRestartGood Bad q) ∩
        (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩).cell ∩ E := by
  ext x
  exact ⟨fun hx => ⟨⟨hx.1, hx.1.1⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩

theorem selected_restart_remainder_of_good_root
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) (E : Set (Ambient d)) :
    selectedRestartRemainder Bad q E = q.cell \
      activeCellRepresentedSet μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
        (relativeRestartGood Bad q)
        (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) E := by
  unfold selectedRestartRemainder
  rw [selected_restart_parent_eq, selected_restart_stops_of_good_root Bad q hq E]
  rfl

end

end RieszRectifiability

end OAI
