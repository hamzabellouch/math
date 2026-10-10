import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPrefixFilter
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorTraversal

namespace OAI

/-! # Executed separator DFS with measured interval callbacks

Both child calls follow the source traversal exactly. Filtering is a
concrete tail-recursive loop over retained record pointers. Its callback
charge includes the stored-mask lookup and the two binary searches.
-/

namespace LowSpaceSubsetSum.MeasuredSeparatorTraversal

variable {α β : Type*}

def keep (test : α → ℕ → ℕ → Bool × ℕ) (lo hi : ℕ) (xs : List α) : List α × ℕ :=
  MeasuredFilter.runAcc (fun x => test x lo hi) xs [] 0

theorem keep_value (test : α → ℕ → ℕ → Bool × ℕ) (inc : α → Array ℕ)
    (ht : ∀ x lo hi, (test x lo hi).1 = SeparatorIncidenceTable.hit (inc x) lo hi)
    (lo hi : ℕ) (xs : List α) :
    (keep test lo hi xs).1 = SeparatorTraversal.keep inc lo hi xs := by
  simp only [keep, MeasuredFilter.runAcc_value, List.reverse_nil, List.nil_append,
    ht, SeparatorTraversal.keep]

theorem keep_work (test : α → ℕ → ℕ → Bool × ℕ) (K : ℕ)
    (ht : ∀ x lo hi, (test x lo hi).2 ≤ K) (lo hi : ℕ) (xs : List α) :
    (keep test lo hi xs).2 ≤ (K + 4) * xs.length + 1 := by
  simpa only [keep, Nat.zero_add, List.length_nil, Nat.add_zero] using
    MeasuredFilter.runAcc_work (fun x => test x lo hi) K (fun x => ht x lo hi) xs [] 0

def run (test₁ : α → ℕ → ℕ → Bool × ℕ) (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → Bool × ℕ) :
    ℕ → ℕ → ℕ → List α → List β → Bool × ℕ
  | 0, lo, hi, xs, ys =>
    let left := keep test₁ lo hi xs
    let right := keep test₂ lo hi ys
    if left.1.isEmpty || right.1.isEmpty then (false, left.2 + right.2 + 3) else
      let out := leaf lo left.1 right.1
      (out.1, left.2 + right.2 + out.2 + 4)
  | k + 1, lo, hi, xs, ys =>
    let left := keep test₁ lo hi xs
    let right := keep test₂ lo hi ys
    if left.1.isEmpty || right.1.isEmpty then (false, left.2 + right.2 + 3)
    else if hi ≤ lo + 1 then
      let out := leaf lo left.1 right.1
      (out.1, left.2 + right.2 + out.2 + 4)
    else
      let mid := (lo + hi) / 2
      let first := run test₁ test₂ leaf k lo mid left.1 right.1
      let second := run test₁ test₂ leaf k mid hi left.1 right.1
      (first.1 || second.1, left.2 + right.2 + first.2 + second.2 + 8)

theorem run_value (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (ht₁ : ∀ x lo hi, (test₁ x lo hi).1 = SeparatorIncidenceTable.hit (inc₁ x) lo hi)
    (ht₂ : ∀ y lo hi, (test₂ y lo hi).1 = SeparatorIncidenceTable.hit (inc₂ y) lo hi)
    (leaf : ℕ → List α → List β → Bool × ℕ)
    (source : ℕ → List α → List β → SeparatorTraversal.Result)
    (hleaf : ∀ j xs ys, (leaf j xs ys).1 = (source j xs ys).accepted)
    (k lo hi : ℕ) (xs : List α) (ys : List β) :
    (run test₁ test₂ leaf k lo hi xs ys).1 =
      (SeparatorTraversal.run inc₁ inc₂ source k lo hi xs ys).accepted := by
  induction k generalizing lo hi xs ys with
  | zero =>
    simp only [run, keep_value test₁ inc₁ ht₁, keep_value test₂ inc₂ ht₂,
      SeparatorTraversal.run]
    split
    · rfl
    · exact hleaf _ _ _
  | succ k ih =>
    simp only [run, keep_value test₁ inc₁ ht₁, keep_value test₂ inc₂ ht₂,
      SeparatorTraversal.run]
    split
    · rfl
    · split
      · exact hleaf _ _ _
      · simp only [ih]

private theorem empty_bound (K L N a b : ℕ)
    (ha : a ≤ (K + 4) * N + 2) :
    a + 3 ≤ (2 * K + 2 * L + 32) * (N + b + 1) := by
  nlinarith only [ha, Nat.zero_le (K * N), Nat.zero_le (L * N),
    Nat.zero_le (K * b), Nat.zero_le (L * b), Nat.zero_le N, Nat.zero_le b,
    Nat.zero_le K, Nat.zero_le L]

private theorem leaf_bound (K L N a b c : ℕ)
    (ha : a ≤ (K + 4) * N + 2) (hc : c ≤ L * (b + N + 1)) :
    a + c + 4 ≤ (2 * K + 2 * L + 32) * (N + b + 1) := by
  nlinarith only [ha, hc, Nat.zero_le (K * N), Nat.zero_le (L * N),
    Nat.zero_le (K * b), Nat.zero_le N, Nat.zero_le b, Nat.zero_le K]

private theorem branch_bound (K L N a b c r s : ℕ)
    (hN : 2 ≤ N) (ha : a ≤ (K + 4) * N + 2)
    (hr : r ≤ (2 * K + 2 * L + 32) * (b + 1))
    (hs : s ≤ (2 * K + 2 * L + 32) * (c + 1)) :
    a + r + s + 8 ≤ (2 * K + 2 * L + 32) * (N + b + c + 1) := by
  have hp := Nat.mul_le_mul_left (K + 2 * L + 28) hN
  nlinarith only [ha, hr, hs, hp]

private theorem nonempty_size (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (lo hi : ℕ) (xs : List α) (ys : List β)
    (he : ((SeparatorTraversal.keep inc₁ lo hi xs).isEmpty ||
      (SeparatorTraversal.keep inc₂ lo hi ys).isEmpty) ≠ true) :
    2 ≤ xs.length + ys.length := by
  have hl := SeparatorTraversal.keep_length inc₁ lo hi xs
  have hr := SeparatorTraversal.keep_length inc₂ lo hi ys
  have hxl : (SeparatorTraversal.keep inc₁ lo hi xs).length > 0 := by
    apply List.length_pos_iff.mpr
    intro h
    simp only [h, List.isEmpty_nil, Bool.true_or] at he
    exact he rfl
  have hyl : (SeparatorTraversal.keep inc₂ lo hi ys).length > 0 := by
    apply List.length_pos_iff.mpr
    intro h
    simp only [h, List.isEmpty_nil, Bool.or_true] at he
    exact he rfl
  omega

/-- The existing source scans absorb every measured filter and branch action. -/
theorem run_work (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (ht₁ : ∀ x lo hi, (test₁ x lo hi).1 = SeparatorIncidenceTable.hit (inc₁ x) lo hi)
    (ht₂ : ∀ y lo hi, (test₂ y lo hi).1 = SeparatorIncidenceTable.hit (inc₂ y) lo hi)
    (K L : ℕ) (hc₁ : ∀ x lo hi, (test₁ x lo hi).2 ≤ K)
    (hc₂ : ∀ y lo hi, (test₂ y lo hi).2 ≤ K)
    (leaf : ℕ → List α → List β → Bool × ℕ)
    (source : ℕ → List α → List β → SeparatorTraversal.Result)
    (hleaf : ∀ j xs ys, (leaf j xs ys).2 ≤
      L * ((source j xs ys).scans + xs.length + ys.length + 1))
    (k lo hi : ℕ) (xs : List α) (ys : List β) :
    (run test₁ test₂ leaf k lo hi xs ys).2 ≤ (2 * K + 2 * L + 32) *
      ((SeparatorTraversal.run inc₁ inc₂ source k lo hi xs ys).scans + 1) := by
  induction k generalizing lo hi xs ys with
  | zero =>
    have hl := keep_work test₁ K hc₁ lo hi xs
    have hr := keep_work test₂ K hc₂ lo hi ys
    have hxl := SeparatorTraversal.keep_length inc₁ lo hi xs
    have hyl := SeparatorTraversal.keep_length inc₂ lo hi ys
    have hf := (hleaf lo (SeparatorTraversal.keep inc₁ lo hi xs)
      (SeparatorTraversal.keep inc₂ lo hi ys)).trans (Nat.mul_le_mul_left L
        (by omega : (source lo (SeparatorTraversal.keep inc₁ lo hi xs)
          (SeparatorTraversal.keep inc₂ lo hi ys)).scans +
          (SeparatorTraversal.keep inc₁ lo hi xs).length +
          (SeparatorTraversal.keep inc₂ lo hi ys).length + 1 ≤
          (source lo (SeparatorTraversal.keep inc₁ lo hi xs)
          (SeparatorTraversal.keep inc₂ lo hi ys)).scans + (xs.length + ys.length) + 1))
    simp only [run, keep_value test₁ inc₁ ht₁, keep_value test₂ inc₂ ht₂,
      SeparatorTraversal.run]
    split
    · exact empty_bound K L (xs.length + ys.length) _ 0 (by nlinarith only [hl, hr])
    · exact leaf_bound K L (xs.length + ys.length) _ _ _
        (by nlinarith only [hl, hr]) hf
  | succ k ih =>
    have hl := keep_work test₁ K hc₁ lo hi xs
    have hr := keep_work test₂ K hc₂ lo hi ys
    have hxl := SeparatorTraversal.keep_length inc₁ lo hi xs
    have hyl := SeparatorTraversal.keep_length inc₂ lo hi ys
    have hf := (hleaf lo (SeparatorTraversal.keep inc₁ lo hi xs)
      (SeparatorTraversal.keep inc₂ lo hi ys)).trans (Nat.mul_le_mul_left L
        (by omega : (source lo (SeparatorTraversal.keep inc₁ lo hi xs)
          (SeparatorTraversal.keep inc₂ lo hi ys)).scans +
          (SeparatorTraversal.keep inc₁ lo hi xs).length +
          (SeparatorTraversal.keep inc₂ lo hi ys).length + 1 ≤
          (source lo (SeparatorTraversal.keep inc₁ lo hi xs)
          (SeparatorTraversal.keep inc₂ lo hi ys)).scans + (xs.length + ys.length) + 1))
    simp only [run, keep_value test₁ inc₁ ht₁, keep_value test₂ inc₂ ht₂,
      SeparatorTraversal.run]
    split
    · exact empty_bound K L (xs.length + ys.length) _ 0 (by nlinarith only [hl, hr])
    · rename_i he
      split
      · exact leaf_bound K L (xs.length + ys.length) _ _ _
          (by nlinarith only [hl, hr]) hf
      · have hN := nonempty_size inc₁ inc₂ lo hi xs ys he
        have hfirst := ih lo ((lo + hi) / 2)
          (SeparatorTraversal.keep inc₁ lo hi xs) (SeparatorTraversal.keep inc₂ lo hi ys)
        have hsecond := ih ((lo + hi) / 2) hi
          (SeparatorTraversal.keep inc₁ lo hi xs) (SeparatorTraversal.keep inc₂ lo hi ys)
        exact branch_bound K L (xs.length + ys.length) _ _ _ _ _ hN
          (by nlinarith only [hl, hr]) hfirst hsecond

end LowSpaceSubsetSum.MeasuredSeparatorTraversal

end OAI
