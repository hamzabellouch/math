import OAI.Combinatorics.EditApproximation.Binary.BinaryGatheredValues

namespace OAI

/-! The default-zero finite buffers preserve the nonnegative bounds of
paired initial/history coordinates when the initial buffer covers them. -/

namespace EditApproximation

theorem finiteAnswerTable_eq_zero_of_not_mem {κ : Type*} [DecidableEq κ]
    (keys : List κ) (values : List ℚ) (query : κ) (hq : query ∉ keys) :
    finiteAnswerTable keys values query = 0 := by
  induction keys generalizing values with
  | nil => rfl
  | cons key keys ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      have hk : query ≠ key := fun he => hq (List.mem_cons.mpr (Or.inl he))
      have ht : query ∉ keys := fun he => hq (List.mem_cons_of_mem key he)
      simpa only [finiteAnswerTable, ite_eq_right hk] using ih values ht

theorem finiteAnswerTable_nonneg {κ : Type*} [DecidableEq κ]
    (keys : List κ) (values : List ℚ) (query : κ) (hv : ∀ value ∈ values, 0 ≤ value) :
    0 ≤ finiteAnswerTable keys values query := by
  induction keys generalizing values with
  | nil => exact le_rfl
  | cons key keys ih =>
    cases values with
    | nil => exact le_rfl
    | cons value values =>
      unfold finiteAnswerTable
      split_ifs
      · exact hv value List.mem_cons_self
      · exact ih values (fun v h => hv v (List.mem_cons_of_mem _ h))

theorem finiteAnswerTable_map_le_of_subset {κ : Type*} [DecidableEq κ]
    (keys initialKeys : List κ) (history initial : κ → ℚ)
    (hkeys : ∀ key ∈ keys, key ∈ initialKeys)
    (hi : ∀ key, 0 ≤ initial key)
    (hle : ∀ key, history key ≤ initial key) (query : κ) :
    finiteAnswerTable keys (keys.map history) query ≤
      finiteAnswerTable initialKeys (initialKeys.map initial) query := by
  by_cases hq : query ∈ keys
  · rw [finiteAnswerTable_map keys history query hq,
      finiteAnswerTable_map initialKeys initial query (hkeys query hq)]
    exact hle query
  · rw [finiteAnswerTable_eq_zero_of_not_mem keys _ query hq]
    apply finiteAnswerTable_nonneg
    intro value hv
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hv
    exact hi key

end EditApproximation

end OAI
