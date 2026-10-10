import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCheckRefinement

namespace OAI

/-! # Exact allowance spending by completed separator calls -/

namespace LowSpaceSubsetSum.BudgetedSeparatorTraversal

open BudgetedSeparatorFlow

variable {α β : Type*}

theorem remaining (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → BudgetedSeparatorCall.Outcome Bool)
    (source : ℕ → List α → List β → Bool × ℕ)
    (hleaf : ∀ j as bs na nb budget result left, as.length = na → bs.length = nb →
      (leaf j as bs na nb budget).1 = some (result, left) →
      budget = left + (source j as bs).2)
    (k lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) (result : Bool) (left : ℕ)
    (h : (execute K test₁ test₂ leaf k lo hi xs ys nx ny budget).1 = some (result, left)) :
    budget = left + (reference K test₁ test₂ source k lo hi xs ys).2 := by
  induction k generalizing lo hi xs ys nx ny budget result left with
  | zero =>
    rw [execute] at h
    obtain ⟨f, rem, hf, h⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, hrem, hfee⟩ := BudgetedSeparatorNode.value K test₁ test₂ lo hi xs ys
      nx ny budget f rem hf
    simp only [reference, hx, hy]
    split at h
    · rename_i he
      simp only [he, ↓reduceIte]
      cases h
      omega
    · rename_i he
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      have hs := hleaf _ _ _ _ _ _ _ _ rfl rfl h
      omega
  | succ k ih =>
    rw [execute] at h
    obtain ⟨f, rem, hf, h⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, hrem, hfee⟩ := BudgetedSeparatorNode.value K test₁ test₂ lo hi xs ys
      nx ny budget f rem hf
    simp only [reference, hx, hy]
    split at h
    · rename_i he
      simp only [he, ↓reduceIte]
      cases h
      omega
    · rename_i he
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i hs
        simp only [hs, ↓reduceIte]
        have hleaf' := hleaf _ _ _ _ _ _ _ _ rfl rfl h
        omega
      · rename_i hs
        simp only [hs, ↓reduceIte]
        obtain ⟨first, midBudget, hfirst, hrest⟩ := (bind_eq_some _ _ _ _).mp h
        obtain ⟨second, finalBudget, hsecond, hfinal⟩ := (bind_eq_some _ _ _ _).mp hrest
        have hfirst' := ih _ _ _ _ _ _ _ rfl rfl _ _ hfirst
        have hsecond' := ih _ _ _ _ _ _ _ rfl rfl _ _ hsecond
        cases hfinal
        omega

end LowSpaceSubsetSum.BudgetedSeparatorTraversal

namespace LowSpaceSubsetSum.BudgetedSeparatorCheck

open BudgetedSeparatorFlow

variable {n g : ℕ}

theorem remaining (capacity : ℕ) (target : ℤ) (blocks : List (StoredSeparatorCheck.Block n g))
    (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) (result : Bool) (left : ℕ)
    (h : (execute capacity target blocks xs ys nx ny budget).1 = some (result, left)) :
    budget = left + (reference capacity target blocks xs ys).2 := by
  induction blocks generalizing xs ys nx ny budget result left with
  | nil =>
    rw [execute] at h
    obtain ⟨fits, rem, hf, hout⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, hrem, hfee⟩ := BudgetedSeparatorCall.value 4 _ budget fits rem hf
    simp only [reference, hx, hy]
    by_cases hs : nx + ny ≤ capacity
    · simp only [hs, decide_true, ↓reduceIte] at hout ⊢
      obtain ⟨_, hleft, hc⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hout
      omega
    · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte,
        BudgetedSeparatorFlow.pure] at hout ⊢
      cases hout
      omega
  | cons b rest ih =>
    rw [execute] at h
    obtain ⟨fits, rem, hf, hout⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, hrem, hfee⟩ := BudgetedSeparatorCall.value 4 _ budget fits rem hf
    simp only [reference, hx, hy]
    by_cases hs : nx + ny ≤ capacity
    · simp only [hs, decide_true, ↓reduceIte] at hout ⊢
      have ht := BudgetedSeparatorTraversal.remaining b.queryBound b.leftQuery b.rightQuery
        (fun _ as bs na nb rem => execute capacity target rest as bs na nb rem)
        (fun _ as bs => reference capacity target rest as bs)
        (fun _ as bs na nb rem r l ha hb hr => ih as bs na nb rem ha hb r l hr)
        b.depth 0 b.familySize xs ys nx ny rem hx hy result left hout
      omega
    · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte,
        BudgetedSeparatorFlow.pure] at hout ⊢
      cases hout
      omega

end LowSpaceSubsetSum.BudgetedSeparatorCheck

end OAI
