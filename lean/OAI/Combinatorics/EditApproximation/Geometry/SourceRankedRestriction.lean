import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Restrict only the recursive table keys of a mixed source/table query.
The source reads remain explicit. This preserves the finite cache domain
without materializing any counterfactual table. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ) (supported : κ → Prop)







 theorem restrictBody_value
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ) (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key) :
    (restrictBody tableRank supported tableBody parent).value
        (Sum.elim sourceValue (fun key => tableValue key.val.val)) =
      (tableBody parent.val).value (Sum.elim sourceValue (fun key => tableValue key.val)) := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_value]
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  rw [horacle]
  exact FiniteQuery.restrict_value _ _ _ hkeys

 theorem restrictBody_cost
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ) (sourceWeight : σ → ℕ) (tableWeight : κ → ℕ)
    (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key) :
    (restrictBody tableRank supported tableBody parent).cost
        (Sum.elim sourceValue (fun key => tableValue key.val.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) =
      (tableBody parent.val).cost (Sum.elim sourceValue (fun key => tableValue key.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val)) := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_cost]
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  have hweight :
      (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceWeight (fun key => tableWeight key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  rw [horacle, hweight]
  exact FiniteQuery.restrict_cost _ _ _ _ hkeys

 theorem restrictBody_keys_all
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (sourcePredicate : σ → Prop) (tablePredicate : κ → Prop)
    (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key)
    (hall : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      match key with | .inl source => sourcePredicate source | .inr table => tablePredicate table.val) :
    ∀ key ∈ (restrictBody tableRank supported tableBody parent).keys
        (Sum.elim sourceValue (fun key => tableValue key.val.val)),
      match key with | .inl source => sourcePredicate source | .inr table => tablePredicate table.val.val := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_keys]
  intro key hk
  obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hk
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hp⟩
    cases key <;> rfl
  rw [horacle] at hs
  have hmem : small.val ∈ ((FiniteQuery.restrict
      (supportedChild tableRank supported parent.val) (tableBody parent.val)).keys
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val)).map Subtype.val :=
    List.mem_map.mpr ⟨small, hs, rfl⟩
  rw [FiniteQuery.restrict_keys _ _ _ hkeys] at hmem
  have h := hall small.val hmem
  rcases small with ⟨small, hp⟩
  cases small <;> exact h

end EditApproximation.SourceRanked

end OAI
