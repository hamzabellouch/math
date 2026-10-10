import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorTraversal

namespace OAI

/-! # Exact values of the interrupted separator traversal -/

namespace LowSpaceSubsetSum.BudgetedSeparatorTraversal

open BudgetedSeparatorCall BudgetedSeparatorFlow

variable {α β : Type*}

theorem reference_value (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (leaf : ℕ → List α → List β → Bool × ℕ)
    (k lo hi : ℕ) (xs : List α) (ys : List β) :
    (reference K test₁ test₂ leaf k lo hi xs ys).1 =
      (MeasuredSeparatorTraversal.run test₁ test₂ leaf k lo hi xs ys).1 := by
  induction k generalizing lo hi xs ys with
  | zero =>
    simp only [reference, BudgetedSeparatorNode.prepare, MeasuredSeparatorTraversal.run]
    split_ifs <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
  | succ k ih =>
    simp only [reference, BudgetedSeparatorNode.prepare, MeasuredSeparatorTraversal.run]
    by_cases he : ((MeasuredSeparatorTraversal.keep test₁ lo hi xs).1.isEmpty ||
      (MeasuredSeparatorTraversal.keep test₂ lo hi ys).1.isEmpty) = true
    · simp only [he, ↓reduceIte]
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      by_cases hs : hi ≤ lo + 1
      · simp only [hs, ↓reduceIte]
      · simp only [hs, ↓reduceIte, ih]

theorem execute_value (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Outcome Bool)
    (source : ℕ → List α → List β → Bool × ℕ)
    (hleaf : ∀ j as bs na nb budget result left, as.length = na → bs.length = nb →
      (leaf j as bs na nb budget).1 = some (result, left) → result = (source j as bs).1)
    (k lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (result : Bool) (left : ℕ)
    (h : (execute K test₁ test₂ leaf k lo hi xs ys nx ny budget).1 = some (result, left)) :
    result = (reference K test₁ test₂ source k lo hi xs ys).1 := by
  induction k generalizing lo hi xs ys nx ny budget result left with
  | zero =>
    rw [execute] at h
    obtain ⟨f, remaining, hf, h⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorNode.value K test₁ test₂ lo hi xs ys nx ny budget
      f remaining hf
    simp only [reference]
    split at h
    · rename_i he
      simp only [he, ↓reduceIte]
      cases h
      rfl
    · rename_i he
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact hleaf _ _ _ _ _ _ _ _ rfl rfl h
  | succ k ih =>
    rw [execute] at h
    obtain ⟨f, remaining, hf, h⟩ := (bind_eq_some _ _ _ _).mp h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorNode.value K test₁ test₂ lo hi xs ys nx ny budget
      f remaining hf
    simp only [reference]
    split at h
    · rename_i he
      simp only [he, ↓reduceIte]
      cases h
      rfl
    · rename_i he
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i hsmall
        simp only [hsmall, ↓reduceIte]
        exact hleaf _ _ _ _ _ _ _ _ rfl rfl h
      · rename_i hsmall
        simp only [hsmall, ↓reduceIte]
        obtain ⟨first, midBudget, hfirst, hrest⟩ := (bind_eq_some _ _ _ _).mp h
        obtain ⟨second, finalBudget, hsecond, hfinal⟩ := (bind_eq_some _ _ _ _).mp hrest
        cases hfinal
        rw [ih _ _ _ _ _ _ _ _ _ hfirst, ih _ _ _ _ _ _ _ _ _ hsecond]

theorem execute_complete (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Outcome Bool)
    (source : ℕ → List α → List β → Bool × ℕ)
    (hleaf : ∀ j as bs na nb budget, as.length = na → bs.length = nb →
      (source j as bs).2 ≤ budget →
      (leaf j as bs na nb budget).1 =
        some ((source j as bs).1, budget - (source j as bs).2))
    (k lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny)
    (hb : (reference K test₁ test₂ source k lo hi xs ys).2 ≤ budget) :
    (execute K test₁ test₂ leaf k lo hi xs ys nx ny budget).1 =
      some ((reference K test₁ test₂ source k lo hi xs ys).1,
        budget - (reference K test₁ test₂ source k lo hi xs ys).2) := by
  induction k generalizing lo hi xs ys nx ny budget with
  | zero =>
    let f := (BudgetedSeparatorNode.prepare test₁ test₂ lo hi xs ys).1
    let fee := BudgetedSeparatorNode.charge K nx ny
    have heq : BudgetedSeparatorNode.charge K xs.length ys.length = fee := by rw [hx, hy]
    simp only [reference, heq] at hb ⊢
    change (if f.left.isEmpty || f.right.isEmpty then (false, fee)
      else ((source lo f.left f.right).1, fee + (source lo f.left f.right).2)).2 ≤ budget at hb
    rw [execute]
    apply (bind_eq_some _ _ _ _).mpr
    have hf : fee ≤ budget := by split at hb <;> dsimp only at hb <;> omega
    refine ⟨f, budget - fee, BudgetedSeparatorNode.complete K test₁ test₂ lo hi xs ys
      nx ny budget hf, ?_⟩
    change _ = some ((if f.left.isEmpty || f.right.isEmpty then (false, fee)
      else ((source lo f.left f.right).1, fee + (source lo f.left f.right).2)).1,
      budget - (if f.left.isEmpty || f.right.isEmpty then (false, fee)
        else ((source lo f.left f.right).1, fee + (source lo f.left f.right).2)).2)
    split
    · rfl
    · have hs : (source lo f.left f.right).2 ≤ budget - fee := by
        simp_all only [Bool.false_eq_true, ↓reduceIte]
        omega
      rw [hleaf lo f.left f.right f.nx f.ny _ f.left_size f.right_size hs]
      congr 2
      omega
  | succ k ih =>
    let f := (BudgetedSeparatorNode.prepare test₁ test₂ lo hi xs ys).1
    let fee := BudgetedSeparatorNode.charge K nx ny
    let mid := (lo + hi) / 2
    let a := reference K test₁ test₂ source k lo mid f.left f.right
    let b := reference K test₁ test₂ source k mid hi f.left f.right
    have heq : BudgetedSeparatorNode.charge K xs.length ys.length = fee := by rw [hx, hy]
    simp only [reference, heq] at hb ⊢
    change (if f.left.isEmpty || f.right.isEmpty then (false, fee)
      else if hi ≤ lo + 1 then ((source lo f.left f.right).1, fee + (source lo f.left f.right).2)
      else (a.1 || b.1, fee + a.2 + b.2)).2 ≤ budget at hb
    have hf : fee ≤ budget := by split at hb <;> (try split at hb) <;> dsimp only at hb <;> omega
    rw [execute]
    apply (bind_eq_some _ _ _ _).mpr
    refine ⟨f, budget - fee, BudgetedSeparatorNode.complete K test₁ test₂ lo hi xs ys
      nx ny budget hf, ?_⟩
    change _ = some ((if f.left.isEmpty || f.right.isEmpty then (false, fee)
      else if hi ≤ lo + 1 then ((source lo f.left f.right).1, fee + (source lo f.left f.right).2)
      else (a.1 || b.1, fee + a.2 + b.2)).1,
      budget - (if f.left.isEmpty || f.right.isEmpty then (false, fee)
        else if hi ≤ lo + 1 then ((source lo f.left f.right).1, fee + (source lo f.left f.right).2)
        else (a.1 || b.1, fee + a.2 + b.2)).2)
    split
    · rfl
    · split
      · have hs : (source lo f.left f.right).2 ≤ budget - fee := by
          simp_all only [Bool.false_eq_true, ↓reduceIte]
          omega
        rw [hleaf lo f.left f.right f.nx f.ny _ f.left_size f.right_size hs]
        congr 2
        omega
      · have ha : a.2 ≤ budget - fee := by
          simp_all only [Bool.false_eq_true, ↓reduceIte]
          omega
        have hb' : b.2 ≤ budget - fee - a.2 := by
          simp_all only [Bool.false_eq_true, ↓reduceIte]
          omega
        apply (bind_eq_some _ _ _ _).mpr
        refine ⟨a.1, budget - fee - a.2,
          ih lo mid f.left f.right f.nx f.ny (budget - fee)
            f.left_size f.right_size ha, ?_⟩
        apply (bind_eq_some _ _ _ _).mpr
        refine ⟨b.1, budget - fee - a.2 - b.2,
          ih mid hi f.left f.right f.nx f.ny (budget - fee - a.2)
            f.left_size f.right_size hb', ?_⟩
        change some (a.1 || b.1, budget - fee - a.2 - b.2) = _
        congr 2
        omega

end LowSpaceSubsetSum.BudgetedSeparatorTraversal

end OAI
