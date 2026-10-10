import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedSpent
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorFlow

namespace OAI

namespace LowSpaceSubsetSum.BudgetedParentCollector

variable {n : ℕ}

def collect (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B C : ℕ) (P : StoredRestriction n) (budget : ℕ) :=
  let out := BudgetedPreparedParent.run D F P hF B C budget
  (out.1.map (fun (value, left) => (value.dictionary, left)), out.2)

noncomputable def bill (D : RepresentationParentData n) (B C : ℕ) (P : StoredRestriction n) : ℕ :=
  BudgetedPreparedParent.setupCharge D.input C +
    inputScale D.input ^ 7 * ({D with maskRestriction := P.semantic}.collect B).state.queries +
    B * ({D with maskRestriction := P.semantic}.collect B).state.copies + 4

theorem value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B C : ℕ) (P : StoredRestriction n) (budget : ℕ)
    (out : StoredEntry.Dictionary D.input D.capacity) (left : ℕ)
    (h : (collect D F hF B C P budget).1 = some (out, left)) :
    out = (ComputedParentExecution.run D F P hF B).1.dictionary ∧ left ≤ budget := by
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
  rcases p with ⟨result, remaining⟩
  have hv := BudgetedPreparedParent.run_value D F P hF B C budget result remaining hp
  cases he
  exact ⟨congrArg PreparedParentExecution.Result.dictionary hv.1, hv.2⟩

theorem complete (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B C : ℕ) (P : StoredRestriction n) (budget : ℕ)
    (hn : 10000 ≤ n) (hb : bill D B C P ≤ budget) :
    ∃ left, (collect D F hF B C P budget).1 =
      some ((ComputedParentExecution.run D F P hF B).1.dictionary, left) := by
  obtain ⟨left, h⟩ := BudgetedPreparedParent.run_complete D F P hF B C budget hn hb
  exact ⟨left, by simp only [collect, h, Option.map_some]⟩

theorem remaining (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B C : ℕ) (P : StoredRestriction n) (budget : ℕ)
    (hn : 10000 ≤ n) (out : StoredEntry.Dictionary D.input D.capacity) (left : ℕ)
    (h : (collect D F hF B C P budget).1 = some (out, left)) :
    budget ≤ left + bill D B C P := by
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
  rcases p with ⟨result, rest⟩
  have hr := BudgetedPreparedParent.run_remaining D F P hF B C budget hn result rest hp
  have hv := (BudgetedPreparedParent.run_value D F P hF B C budget result rest hp).1
  have hq := congrArg (fun r => r.state.queries)
    (StoredParentExecution.collect_value {D with maskRestriction := P.semantic} F hF B)
  have hc := congrArg (fun r => r.state.copies)
    (StoredParentExecution.collect_value {D with maskRestriction := P.semantic} F hF B)
  rw [ComputedParentExecution.run_value] at hv
  rw [hv] at hr
  change budget ≤ rest + BudgetedPreparedParent.setupCharge D.input C +
    inputScale D.input ^ 7 * (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.queries +
    B * (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.copies + 4 at hr
  change (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.queries = _ at hq
  change (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1.state.copies = _ at hc
  rw [hq, hc] at hr
  cases he
  simpa only [bill, Nat.add_assoc] using hr

theorem account (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B C : ℕ) (P : StoredRestriction n) (budget : ℕ)
    (hn : 10000 ≤ n) (hl : ∀ j, (D.pair j).left.occurrences.card ≤ C)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n)
    (hcopy : (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B) :
    BudgetedSeparatorFlow.Account budget (collect D F hF B C P budget) := by
  constructor
  · exact BudgetedPreparedParent.run_work D F P hF B C budget hn hl hr hC hcopy
  · intro out left h
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
    rcases p with ⟨result, rest⟩
    have hv := (BudgetedPreparedParent.run_value D F P hF B C budget result rest hp).2
    have hs := BudgetedPreparedParent.run_spent D F P hF B C budget hn hl hr hC hcopy result rest hp
    cases he
    exact ⟨hv, hs⟩

end LowSpaceSubsetSum.BudgetedParentCollector

end OAI
