import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoKeys
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedWork

namespace OAI

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

include hbody

/-- Forgetting source leaves preserves every table request, including
those which the mixed memo execution first encounters after a cache hit. -/
theorem uncachedKeys_table_mem (root item : κ)
    (hitem : Sum.inr item ∈ rankedUncachedKeys (rank tableRank)
      (body tableRank tableBody sourceValue) (.inr root)) :
    item ∈ rankedUncachedKeys tableRank (projectedBody tableRank tableBody sourceValue) root := by
  let mixed := body tableRank tableBody sourceValue
  let projected := projectedBody tableRank tableBody sourceValue
  have hvm (key : Sum σ κ) : rankedProgramValue (rank tableRank) mixed key =
      value sourceValue tableValue key := program_value tableRank tableBody sourceValue tableValue hbody key
  have hvp (key : κ) : rankedProgramValue tableRank projected key = tableValue key :=
    projectedProgram_value tableRank tableBody sourceValue tableValue hbody key
  have hall : ∀ level root, tableRank root = level → ∀ item,
      Sum.inr item ∈ rankedUncachedKeys (rank tableRank) mixed (.inr root) →
      item ∈ rankedUncachedKeys tableRank projected root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel item hm
      rw [rankedUncachedKeys] at hm ⊢
      rcases List.mem_cons.mp hm with heq | hm
      · exact List.mem_cons.mpr (.inl (Sum.inr.inj heq))
      · have hanswer :
            (fun next => rankedProgramValue (rank tableRank) mixed next.val) ∘ child tableRank root =
              Sum.elim sourceValue (fun next => tableValue next.val) := by
          funext next
          rw [Function.comp_apply, hvm]
          cases next <;> rfl
        change Sum.inr item ∈ ((mixed (.inr root)).keys _).flatMap _ at hm
        dsimp only [mixed, body] at hm
        rw [FiniteQuery.mapKeys_keys, hanswer] at hm
        obtain ⟨next, hn, hi⟩ := List.mem_flatMap.mp hm
        obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hn
        cases raw with
        | inl scalar =>
          change Sum.inr item ∈ rankedUncachedKeys (rank tableRank) mixed (.inl scalar) at hi
          rw [rankedUncachedKeys] at hi
          simp only [mixed, body, FiniteQuery.keys, List.flatMap_nil,
            List.mem_cons, Sum.inr_ne_inl, List.not_mem_nil, or_false] at hi
        | inr next =>
          have ht := (FiniteQuery.eraseSources_inr_mem_iff sourceValue
            (fun child => tableValue child.val) (tableBody root) next).mp hr
          have hi' := ih (tableRank next.val) (hlevel ▸ next.property) next.val rfl item hi
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨next, ?_, hi'⟩
          change next ∈ (FiniteQuery.eraseSources sourceValue (tableBody root)).keys
            (fun child => rankedProgramValue tableRank projected child.val)
          simpa only [hvp] using ht
  exact hall (tableRank root) root rfl item hitem

end EditApproximation.SourceRanked

end OAI
