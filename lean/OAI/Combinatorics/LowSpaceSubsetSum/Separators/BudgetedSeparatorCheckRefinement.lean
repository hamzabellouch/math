import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCheck
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorRefinement

namespace OAI

/-! # Completed budgeted checks retain the original acceptance test -/

namespace LowSpaceSubsetSum.BudgetedSeparatorCheck

open BudgetedSeparatorCall BudgetedSeparatorFlow StoredSeparatorCheck

variable {n g : ℕ}

theorem execute_value (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) (result : Bool) (left : ℕ)
    (h : (execute capacity target blocks xs ys nx ny budget).1 = some (result, left)) :
    result = (reference capacity target blocks xs ys).1 := by
  induction blocks generalizing xs ys nx ny budget result left with
  | nil =>
    rw [execute] at h
    obtain ⟨fits, remaining, hf, hout⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value 4 _ budget fits remaining hf
    simp only [reference, hx, hy]
    by_cases hb : nx + ny ≤ capacity
    · simp only [hb, decide_true, ↓reduceIte] at hout ⊢
      exact (BudgetedSeparatorCall.value _ _ _ _ _ hout).1
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, BudgetedSeparatorFlow.pure] at hout ⊢
      cases hout
      rfl
  | cons b rest ih =>
    rw [execute] at h
    obtain ⟨fits, remaining, hf, hout⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value 4 _ budget fits remaining hf
    simp only [reference, hx, hy]
    by_cases hb : nx + ny ≤ capacity
    · simp only [hb, decide_true, ↓reduceIte] at hout ⊢
      have hv := BudgetedSeparatorTraversal.execute_value b.queryBound b.leftQuery b.rightQuery
        (fun _ as bs na nb rem => execute capacity target rest as bs na nb rem)
        (fun _ as bs => reference capacity target rest as bs)
        (fun _ as bs na nb rem r l ha hb hr => ih as bs na nb rem ha hb r l hr)
        b.depth 0 b.familySize xs ys nx ny remaining result left hout
      exact hv
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, BudgetedSeparatorFlow.pure] at hout ⊢
      cases hout
      rfl

theorem reference_value (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (blocks : List (Block n g)) (xs ys : List (StoredEntry n)) :
    (reference capacity target blocks xs ys).1 =
      (SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
        (blocks.map Block.source) xs ys).accepted := by
  subst capacity
  induction blocks generalizing xs ys with
  | nil =>
    simp only [reference, List.map_nil, SeparatorBlocks.check, SeparatorTerminal.bounded]
    split
    · exact StoredEntryTerminal.run_value target xs ys (by omega) (by omega)
    · rfl
  | cons b rest ih =>
    simp only [reference, List.map_cons, SeparatorBlocks.check]
    split
    · rw [BudgetedSeparatorTraversal.reference_value]
      have h := MeasuredSeparatorTraversal.run_value b.leftQuery b.rightQuery b.left b.right
        b.leftQuery_value b.rightQuery_value
        (fun _ as bs => reference (2 ^ n) target rest as bs)
        (fun _ as bs => SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
          (rest.map Block.source) as bs)
        (fun _ as bs => ih as bs) b.depth 0 b.familySize xs ys
      rw [h, b.depth_eq]
      rfl
    · rfl

theorem execute_complete (capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny)
    (hb : (reference capacity target blocks xs ys).2 ≤ budget) :
    (execute capacity target blocks xs ys nx ny budget).1 =
      some ((reference capacity target blocks xs ys).1,
        budget - (reference capacity target blocks xs ys).2) := by
  induction blocks generalizing xs ys nx ny budget with
  | nil =>
    simp only [reference, hx, hy] at hb ⊢
    have hfour : 4 ≤ budget := by split at hb <;> dsimp only at hb <;> omega
    rw [execute]
    apply (bind_eq_some _ _ _ _).mpr
    refine ⟨decide (nx + ny ≤ capacity), budget - 4, ?_, ?_⟩
    · exact congrArg Prod.fst (BudgetedSeparatorCall.complete 4 _ budget hfour)
    · by_cases hs : nx + ny ≤ capacity
      · simp only [hs, decide_true, ↓reduceIte] at hb ⊢
        have hc : BudgetedSeparatorTerminal.charge n nx ny ≤ budget - 4 := by omega
        rw [BudgetedSeparatorTerminal.complete target xs ys nx ny _ hc]
        congr 2
        omega
      · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, BudgetedSeparatorFlow.pure]
  | cons b rest ih =>
    simp only [reference, hx, hy] at hb ⊢
    have hfour : 4 ≤ budget := by split at hb <;> dsimp only at hb <;> omega
    rw [execute]
    apply (bind_eq_some _ _ _ _).mpr
    refine ⟨decide (nx + ny ≤ capacity), budget - 4, ?_, ?_⟩
    · exact congrArg Prod.fst (BudgetedSeparatorCall.complete 4 _ budget hfour)
    · by_cases hs : nx + ny ≤ capacity
      · simp only [hs, decide_true, ↓reduceIte] at hb ⊢
        have ht := BudgetedSeparatorTraversal.execute_complete b.queryBound b.leftQuery b.rightQuery
          (fun _ as bs na nb rem => execute capacity target rest as bs na nb rem)
          (fun _ as bs => reference capacity target rest as bs)
          (fun _ as bs na nb rem ha hb hc => ih as bs na nb rem ha hb hc)
          b.depth 0 b.familySize xs ys nx ny (budget - 4) hx hy (by omega)
        simpa only [Nat.sub_sub] using ht
      · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte, BudgetedSeparatorFlow.pure]

end LowSpaceSubsetSum.BudgetedSeparatorCheck

end OAI
