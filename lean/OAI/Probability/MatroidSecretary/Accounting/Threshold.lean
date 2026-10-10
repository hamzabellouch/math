import OAI.Probability.MatroidSecretary.Accounting.Contracts

namespace OAI

/-! Exact source interpretation of the cumulative count in `lem:all-orders`.
The implementation orders listed groups increasingly by integer weight level.
For an actual listed group, counting accepted labels by group index is exactly
counting them by the source's rounded-weight threshold. -/

namespace MatroidProphet.MainAlgorithm
open Finset
variable {n : ℕ}

lemma selected_level_mem_groups (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    {e : Fin n} (he : e ∈ selection M hE d w π) {j : ℤ}
    (hw : w e = some j) : j ∈ groups M d w := by
  have hel := layerGreedy_subset M _ _ _ _ he
  obtain ⟨k, hwk, hek, _⟩ := (assign_spec M hE d w e _ _).mp
    (assigned_some_of_eligible (assign M hE d w) w e hel)
  have hjk : j = k := Option.some.inj (hw.symm.trans hwk)
  exact hjk ▸ hek.2.2.1

/-- No selected label has an unlisted level, so the indexed and literal
weight-threshold cumulative accepted sets agree, not merely their sizes. -/
theorem indexed_selection_eq_threshold (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) :
    (selection M hE d w π).filter
      (fun e => ∃ j, w e = some j ∧ h ≤ (groups M d w).idxOf j) =
    (selection M hE d w π).filter
      (fun e => ∃ j, w e = some j ∧ i ≤ j) := by
  classical
  obtain ⟨him, hidx⟩ := groups_index_of_get M d w hi
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, j, hw, hj⟩
    have hjm := selected_level_mem_groups M hE d w π he hw
    have hlt := groups_idxOf_lt_iff M d w j i hjm him
    exact ⟨he, j, hw, by omega⟩
  · rintro ⟨he, j, hw, hj⟩
    have hjm := selected_level_mem_groups M hE d w π he hw
    have hlt := groups_idxOf_lt_iff M d w j i hjm him
    exact ⟨he, j, hw, by omega⟩

/-- Literal source weight-threshold form of the deterministic clause. -/
theorem listedLambda_le_threshold_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    {h : ℕ} {i : ℤ} (hi : (groups M d w)[h]? = some i) :
    listedLambda M hE d w h ≤
      ((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card := by
  rw [← indexed_selection_eq_threshold M hE d w π hi]
  exact (AccountingContracts.all_orders M hE d w h).1 π

end MatroidProphet.MainAlgorithm

end OAI
