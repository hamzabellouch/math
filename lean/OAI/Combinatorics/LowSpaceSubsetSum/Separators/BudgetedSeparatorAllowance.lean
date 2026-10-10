import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorRefinement

namespace OAI

/-! # Bounding prepaid traversal allowance by the source scan ledger -/

namespace LowSpaceSubsetSum.BudgetedSeparatorTraversal

variable {α β : Type*}

private theorem empty_allowance (K L N s : ℕ) :
    (K + 20) * (N + 1) ≤ 4 * (K + L + 40) * (N + s + 1) := by
  nlinarith only [Nat.zero_le (K * N), Nat.zero_le (L * N), Nat.zero_le (K * s),
    Nat.zero_le (L * s), Nat.zero_le N, Nat.zero_le s, Nat.zero_le K, Nat.zero_le L]

private theorem leaf_allowance (K L N s cost : ℕ) (hc : cost ≤ L * (s + N + 1)) :
    (K + 20) * (N + 1) + cost ≤ 4 * (K + L + 40) * (N + s + 1) := by
  nlinarith only [hc, Nat.zero_le (K * N), Nat.zero_le (L * N), Nat.zero_le (K * s),
    Nat.zero_le (L * s), Nat.zero_le N, Nat.zero_le s, Nat.zero_le K, Nat.zero_le L]

private theorem branch_allowance (K L N s t a b : ℕ) (hN : 2 ≤ N)
    (ha : a ≤ 4 * (K + L + 40) * (s + 1))
    (hb : b ≤ 4 * (K + L + 40) * (t + 1)) :
    (K + 20) * (N + 1) + a + b ≤ 4 * (K + L + 40) * (N + s + t + 1) := by
  have hp := Nat.mul_le_mul_left (3 * K + 4 * L + 140) hN
  nlinarith only [ha, hb, hp, Nat.zero_le K, Nat.zero_le L]

private theorem nonempty_size (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (lo hi : ℕ) (xs : List α) (ys : List β)
    (h : ((SeparatorTraversal.keep inc₁ lo hi xs).isEmpty ||
      (SeparatorTraversal.keep inc₂ lo hi ys).isEmpty) ≠ true) :
    2 ≤ xs.length + ys.length := by
  have hxl : 0 < (SeparatorTraversal.keep inc₁ lo hi xs).length := by
    apply List.length_pos_iff.mpr
    intro he
    simp only [he, List.isEmpty_nil, Bool.true_or] at h
    exact h rfl
  have hyl : 0 < (SeparatorTraversal.keep inc₂ lo hi ys).length := by
    apply List.length_pos_iff.mpr
    intro he
    simp only [he, List.isEmpty_nil, Bool.or_true] at h
    exact h rfl
  have hl := SeparatorTraversal.keep_length inc₁ lo hi xs
  have hr := SeparatorTraversal.keep_length inc₂ lo hi ys
  omega

theorem reference_work (K L : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (h₁ : ∀ x lo hi, (test₁ x lo hi).1 = SeparatorIncidenceTable.hit (inc₁ x) lo hi)
    (h₂ : ∀ y lo hi, (test₂ y lo hi).1 = SeparatorIncidenceTable.hit (inc₂ y) lo hi)
    (leaf : ℕ → List α → List β → Bool × ℕ)
    (source : ℕ → List α → List β → SeparatorTraversal.Result)
    (hleaf : ∀ j as bs, (leaf j as bs).2 ≤ L *
      ((source j as bs).scans + as.length + bs.length + 1))
    (k lo hi : ℕ) (xs : List α) (ys : List β) :
    (reference K test₁ test₂ leaf k lo hi xs ys).2 ≤ 4 * (K + L + 40) *
      ((SeparatorTraversal.run inc₁ inc₂ source k lo hi xs ys).scans + 1) := by
  induction k generalizing lo hi xs ys with
  | zero =>
    have hl := SeparatorTraversal.keep_length inc₁ lo hi xs
    have hr := SeparatorTraversal.keep_length inc₂ lo hi ys
    have hf : (leaf lo (SeparatorTraversal.keep inc₁ lo hi xs)
        (SeparatorTraversal.keep inc₂ lo hi ys)).2 ≤ L *
        ((source lo (SeparatorTraversal.keep inc₁ lo hi xs)
          (SeparatorTraversal.keep inc₂ lo hi ys)).scans + (xs.length + ys.length) + 1) :=
      (hleaf lo (SeparatorTraversal.keep inc₁ lo hi xs)
      (SeparatorTraversal.keep inc₂ lo hi ys)).trans
      (Nat.mul_le_mul_left L (by omega))
    simp only [reference, BudgetedSeparatorNode.prepare, BudgetedSeparatorNode.charge,
      MeasuredSeparatorTraversal.keep_value test₁ inc₁ h₁,
      MeasuredSeparatorTraversal.keep_value test₂ inc₂ h₂, SeparatorTraversal.run, SeparatorTraversal.finish]
    split
    · exact empty_allowance K L (xs.length + ys.length) 0
    · exact leaf_allowance K L (xs.length + ys.length) _ _ hf
  | succ k ih =>
    have hl := SeparatorTraversal.keep_length inc₁ lo hi xs
    have hr := SeparatorTraversal.keep_length inc₂ lo hi ys
    have hf : (leaf lo (SeparatorTraversal.keep inc₁ lo hi xs)
        (SeparatorTraversal.keep inc₂ lo hi ys)).2 ≤ L *
        ((source lo (SeparatorTraversal.keep inc₁ lo hi xs)
          (SeparatorTraversal.keep inc₂ lo hi ys)).scans + (xs.length + ys.length) + 1) :=
      (hleaf lo (SeparatorTraversal.keep inc₁ lo hi xs)
      (SeparatorTraversal.keep inc₂ lo hi ys)).trans
      (Nat.mul_le_mul_left L (by omega))
    have ha := ih lo ((lo + hi) / 2) (SeparatorTraversal.keep inc₁ lo hi xs)
      (SeparatorTraversal.keep inc₂ lo hi ys)
    have hb := ih ((lo + hi) / 2) hi (SeparatorTraversal.keep inc₁ lo hi xs)
      (SeparatorTraversal.keep inc₂ lo hi ys)
    simp only [reference, BudgetedSeparatorNode.prepare, BudgetedSeparatorNode.charge,
      MeasuredSeparatorTraversal.keep_value test₁ inc₁ h₁,
      MeasuredSeparatorTraversal.keep_value test₂ inc₂ h₂, SeparatorTraversal.run, SeparatorTraversal.finish]
    split
    · exact empty_allowance K L (xs.length + ys.length) 0
    · rename_i he
      split
      · exact leaf_allowance K L (xs.length + ys.length) _ _ hf
      · exact branch_allowance K L (xs.length + ys.length) _ _ _ _
          (nonempty_size inc₁ inc₂ lo hi xs ys he) ha hb

end LowSpaceSubsetSum.BudgetedSeparatorTraversal

end OAI
