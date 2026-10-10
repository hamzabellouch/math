import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorBlocks

namespace OAI

/-! # Record-map refinement of the complete separator execution

Mapping stored records to their mathematical views preserves not only
acceptance but the original scan and workspace ledgers.
-/

namespace LowSpaceSubsetSum.SeparatorExecutionMap

variable {α β γ δ : Type*}

private def mapOut (f : α → β) (out : List α × ℕ) : List β × ℕ := (out.1.map f, out.2)

private theorem merge_map (f : α → β) (cmp : β → β → Bool) (xs ys : List α) :
    CountedSort.merge cmp (xs.map f) (ys.map f) =
      mapOut f (CountedSort.merge (fun x y => cmp (f x) (f y)) xs ys) := by
  induction xs generalizing ys with
  | nil => simp [CountedSort.merge, mapOut]
  | cons x xs ih =>
    induction ys with
    | nil => simp [CountedSort.merge, mapOut]
    | cons y ys ihy =>
      cases h : cmp (f x) (f y) with
      | false =>
        simp only [List.map_cons] at ihy
        simp only [List.map_cons, CountedSort.merge, h, Bool.false_eq_true, ↓reduceIte]
        rw [ihy]
        simp only [mapOut, List.map_cons]
      | true =>
        have hi := ih (y :: ys)
        simp only [List.map_cons] at hi
        simp only [List.map_cons, CountedSort.merge, h, ↓reduceIte]
        rw [hi]
        simp only [mapOut, List.map_cons]

private theorem sortRun_split {α : Type*} (cmp : α → α → Bool) (k : ℕ) (xs : List α)
    (h : 2 ≤ xs.length) :
    CountedSort.run cmp (k + 1) xs =
      let cut := (xs.length + 1) / 2
      let left := CountedSort.run cmp k (xs.take cut)
      let right := CountedSort.run cmp k (xs.drop cut)
      let out := CountedSort.merge cmp left.1 right.1
      (out.1, left.2 + right.2 + 3 * xs.length + out.2 + 1) := by
  cases xs with
  | nil => simp at h
  | cons x xs => cases xs with
    | nil => simp at h
    | cons y ys => rfl

private theorem sortRun_map (f : α → β) (cmp : β → β → Bool) (k : ℕ) (xs : List α) :
    CountedSort.run cmp k (xs.map f) =
      mapOut f (CountedSort.run (fun x y => cmp (f x) (f y)) k xs) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y rest =>
        have hl : 2 ≤ (x :: y :: rest).length := by simp
        rw [sortRun_split cmp k _ (by simpa only [List.length_map] using hl),
          sortRun_split _ k _ hl]
        simp only [List.length_map, ← List.map_take, ← List.map_drop, ih, mapOut, merge_map]

private theorem sort_map (f : α → β) (cmp : β → β → Bool) (xs : List α) :
    CountedSort.sort cmp (xs.map f) =
      mapOut f (CountedSort.sort (fun x y => cmp (f x) (f y)) xs) := by
  simp only [CountedSort.sort, List.length_map, sortRun_map]

private theorem find_map (f : α → β) (h : γ → δ) (wx : β → ℤ) (wy : δ → ℤ)
    (fuel : ℕ) (xs : List α) (ys : List γ) (queries : ℕ) :
    SortedFind.runAcc SeparatorTerminal.read wx SeparatorTerminal.read wy fuel
      (xs.map f) (ys.map h) queries =
      SortedFind.runAcc SeparatorTerminal.read (wx ∘ f) SeparatorTerminal.read (wy ∘ h)
        fuel xs ys queries := by
  induction fuel generalizing xs ys queries with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => rfl
      | cons y ys =>
        simp only [List.map_cons, SortedFind.runAcc, SeparatorTerminal.read, Function.comp_apply]
        split
        · simpa only [List.map_cons] using ih xs (y :: ys) (queries + 2)
        · split
          · simpa only [List.map_cons] using ih (x :: xs) ys (queries + 2)
          · rfl

theorem terminal_map (f : α → β) (h : γ → δ) (wx : β → ℤ) (wy : δ → ℤ)
    (target : ℤ) (xs : List α) (ys : List γ) :
    SeparatorTerminal.run wx wy target (xs.map f) (ys.map h) =
      SeparatorTerminal.run (wx ∘ f) (wy ∘ h) target xs ys := by
  simp only [SeparatorTerminal.run, List.isEmpty_map, List.length_map]
  split
  · rfl
  · simp only [SeparatorTerminal.sort, sort_map, mapOut, find_map, Function.comp_def]

theorem bounded_map (f : α → β) (h : γ → δ) (wx : β → ℤ) (wy : δ → ℤ)
    (n : ℕ) (target : ℤ) (xs : List α) (ys : List γ) :
    SeparatorTerminal.bounded n wx wy target (xs.map f) (ys.map h) =
      SeparatorTerminal.bounded n (wx ∘ f) (wy ∘ h) target xs ys := by
  simp only [SeparatorTerminal.bounded, List.length_map]
  split
  · exact terminal_map f h wx wy target xs ys
  · rfl

private theorem keep_map (f : α → β) (inc : β → Array ℕ)
    (lo hi : ℕ) (xs : List α) :
    SeparatorTraversal.keep inc lo hi (xs.map f) =
      (SeparatorTraversal.keep (inc ∘ f) lo hi xs).map f := by
  simp only [SeparatorTraversal.keep, List.filter_map, Function.comp_def]

theorem traversal_map (f : α → β) (h : γ → δ) (inc₁ : β → Array ℕ) (inc₂ : δ → Array ℕ)
    (leaf : ℕ → List β → List δ → SeparatorTraversal.Result)
    (k lo hi : ℕ) (xs : List α) (ys : List γ) :
    SeparatorTraversal.run inc₁ inc₂ leaf k lo hi (xs.map f) (ys.map h) =
      SeparatorTraversal.run (inc₁ ∘ f) (inc₂ ∘ h)
        (fun j as bs => leaf j (as.map f) (bs.map h)) k lo hi xs ys := by
  induction k generalizing lo hi xs ys with
  | zero =>
    simp only [SeparatorTraversal.run, keep_map, List.isEmpty_map, List.length_map,
      SeparatorTraversal.finish]
  | succ k ih =>
    simp only [SeparatorTraversal.run, keep_map, List.isEmpty_map, List.length_map,
      SeparatorTraversal.finish, ih]

def block (f : α → β) (h : γ → δ) (b : SeparatorBlocks.Block β δ) :
    SeparatorBlocks.Block α γ where
  size := b.size
  left := b.left ∘ f
  right := b.right ∘ h
  left_sorted := fun x => b.left_sorted (f x)
  right_sorted := fun y => b.right_sorted (h y)

theorem blocks_map (f : α → β) (h : γ → δ) (wx : β → ℤ) (wy : δ → ℤ)
    (n : ℕ) (target : ℤ) (blocks : List (SeparatorBlocks.Block β δ))
    (xs : List α) (ys : List γ) :
    SeparatorBlocks.check n wx wy target blocks (xs.map f) (ys.map h) =
      SeparatorBlocks.check n (wx ∘ f) (wy ∘ h) target (blocks.map (block f h)) xs ys := by
  induction blocks generalizing xs ys with
  | nil => exact bounded_map f h wx wy n target xs ys
  | cons b bs ih =>
    simp only [SeparatorBlocks.check, List.map_cons, List.length_map]
    split
    · rw [traversal_map]
      simp only [ih, block, SeparatorBlocks.depth]
    · rfl

end LowSpaceSubsetSum.SeparatorExecutionMap

end OAI
