import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorIncidenceTable

namespace OAI

/-!
# Depth-first separator interval traversal

Only the received arrays, their filtered children and a scalar result are
retained. A branch whose filtered arrays are empty ends immediately. The
binary interval queries refer to the precomputed incidence arrays. The
terminal callback is the next block, or the final exact-weight search.
-/

namespace LowSpaceSubsetSum.SeparatorTraversal

open SeparatorIncidenceTable

variable {α β : Type*}

structure Result where
  accepted : Bool
  scans : ℕ
  peak : ℕ
  deriving Repr

def keep {γ : Type*} (incidence : γ → Array ℕ) (lo hi : ℕ) (xs : List γ) : List γ :=
  xs.filter (fun x => hit (incidence x) lo hi)

def finish (leaf : ℕ → List α → List β → Result) (j : ℕ)
    (xs : List α) (ys : List β) (parent : ℕ) : Result :=
  let out := leaf j xs ys
  ⟨out.accepted, parent + out.scans, parent + xs.length + ys.length + out.peak⟩

/-- The ledger completes both children, so acceptance can only save work. -/
def run (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (leaf : ℕ → List α → List β → Result) : ℕ → ℕ → ℕ → List α → List β → Result
  | 0, lo, hi, xs, ys =>
    let left := keep inc₁ lo hi xs
    let right := keep inc₂ lo hi ys
    if left.isEmpty || right.isEmpty then ⟨false, xs.length + ys.length,
      xs.length + ys.length + left.length + right.length⟩
    else finish leaf lo left right (xs.length + ys.length)
  | k + 1, lo, hi, xs, ys =>
    let left := keep inc₁ lo hi xs
    let right := keep inc₂ lo hi ys
    if left.isEmpty || right.isEmpty then ⟨false, xs.length + ys.length,
      xs.length + ys.length + left.length + right.length⟩
    else if hi ≤ lo + 1 then finish leaf lo left right (xs.length + ys.length)
    else
      let mid := (lo + hi) / 2
      let first := run inc₁ inc₂ leaf k lo mid left right
      let second := run inc₁ inc₂ leaf k mid hi left right
      ⟨first.accepted || second.accepted,
        xs.length + ys.length + first.scans + second.scans,
        xs.length + ys.length + left.length + right.length + max first.peak second.peak⟩

theorem keep_mem {γ : Type*} (inc : γ → Array ℕ) (lo hi : ℕ) (xs : List γ) (x : γ) :
    x ∈ keep inc lo hi xs ↔ x ∈ xs ∧ hit (inc x) lo hi = true := by
  simp [keep]

theorem keep_length {γ : Type*} (inc : γ → Array ℕ) (lo hi : ℕ) (xs : List γ) :
    (keep inc lo hi xs).length ≤ xs.length := List.length_filter_le _ _

def Witness (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ) (goal : α → β → Prop)
    (lo hi : ℕ) (xs : List α) (ys : List β) : Prop :=
  ∃ j, lo ≤ j ∧ j < hi ∧ ∃ x ∈ xs, ∃ y ∈ ys,
    j ∈ (inc₁ x).toList ∧ j ∈ (inc₂ y).toList ∧ goal x y

theorem witness_empty (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ) (goal : α → β → Prop)
    (hs₁ : ∀ x, Monotone (fun i : Fin (inc₁ x).size => (inc₁ x)[i.val]))
    (hs₂ : ∀ y, Monotone (fun i : Fin (inc₂ y).size => (inc₂ y)[i.val]))
    (lo hi : ℕ) (xs : List α) (ys : List β)
    (hempty : ((keep inc₁ lo hi xs).isEmpty || (keep inc₂ lo hi ys).isEmpty) = true) :
    ¬ Witness inc₁ inc₂ goal lo hi xs ys := by
  rintro ⟨j, hjl, hjh, x, hx, y, hy, hxi, hyi, _⟩
  have hxl : x ∈ keep inc₁ lo hi xs := (keep_mem _ _ _ _ _).mpr
    ⟨hx, (hit_iff _ (hs₁ x) _ _).mpr ⟨j, hxi, hjl, hjh⟩⟩
  have hyl : y ∈ keep inc₂ lo hi ys := (keep_mem _ _ _ _ _).mpr
    ⟨hy, (hit_iff _ (hs₂ y) _ _).mpr ⟨j, hyi, hjl, hjh⟩⟩
  have hxne : (keep inc₁ lo hi xs).isEmpty = false := by
    simpa using List.ne_nil_of_mem hxl
  have hyne : (keep inc₂ lo hi ys).isEmpty = false := by
    simpa using List.ne_nil_of_mem hyl
  simp [hxne, hyne] at hempty

theorem witness_singleton (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ) (goal : α → β → Prop)
    (hs₁ : ∀ x, Monotone (fun i : Fin (inc₁ x).size => (inc₁ x)[i.val]))
    (hs₂ : ∀ y, Monotone (fun i : Fin (inc₂ y).size => (inc₂ y)[i.val]))
    (lo hi : ℕ) (xs : List α) (ys : List β) (hsmall : hi ≤ lo + 1) :
    Witness inc₁ inc₂ goal lo hi xs ys ↔
      ∃ x ∈ keep inc₁ lo hi xs, ∃ y ∈ keep inc₂ lo hi ys, goal x y := by
  constructor
  · rintro ⟨j, hjl, hjh, x, hx, y, hy, hxi, hyi, hg⟩
    exact ⟨x, (keep_mem _ _ _ _ _).mpr ⟨hx,
      (hit_iff _ (hs₁ x) _ _).mpr ⟨j, hxi, hjl, hjh⟩⟩,
      y, (keep_mem _ _ _ _ _).mpr ⟨hy,
      (hit_iff _ (hs₂ y) _ _).mpr ⟨j, hyi, hjl, hjh⟩⟩, hg⟩
  · rintro ⟨x, hx, y, hy, hg⟩
    obtain ⟨hx, hxc⟩ := (keep_mem _ _ _ _ _).mp hx
    obtain ⟨hy, hyc⟩ := (keep_mem _ _ _ _ _).mp hy
    obtain ⟨j, hj, hjl, hjh⟩ := (hit_iff _ (hs₁ x) _ _).mp hxc
    obtain ⟨j', hj', hjl', hjh'⟩ := (hit_iff _ (hs₂ y) _ _).mp hyc
    have he : j' = j := by omega
    exact ⟨j, hjl, hjh, x, hx, y, hy, hj, he ▸ hj', hg⟩

theorem witness_split (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ) (goal : α → β → Prop)
    (hs₁ : ∀ x, Monotone (fun i : Fin (inc₁ x).size => (inc₁ x)[i.val]))
    (hs₂ : ∀ y, Monotone (fun i : Fin (inc₂ y).size => (inc₂ y)[i.val]))
    (lo mid hi : ℕ) (xs : List α) (ys : List β) (hl : lo ≤ mid) (hh : mid ≤ hi) :
    Witness inc₁ inc₂ goal lo hi xs ys ↔
      Witness inc₁ inc₂ goal lo mid (keep inc₁ lo hi xs) (keep inc₂ lo hi ys) ∨
      Witness inc₁ inc₂ goal mid hi (keep inc₁ lo hi xs) (keep inc₂ lo hi ys) := by
  constructor
  · rintro ⟨j, hjl, hjh, x, hx, y, hy, hxi, hyi, hg⟩
    have hxl : x ∈ keep inc₁ lo hi xs := (keep_mem _ _ _ _ _).mpr
      ⟨hx, (hit_iff _ (hs₁ x) _ _).mpr ⟨j, hxi, hjl, hjh⟩⟩
    have hyl : y ∈ keep inc₂ lo hi ys := (keep_mem _ _ _ _ _).mpr
      ⟨hy, (hit_iff _ (hs₂ y) _ _).mpr ⟨j, hyi, hjl, hjh⟩⟩
    by_cases hm : j < mid
    · exact Or.inl ⟨j, hjl, hm, x, hxl, y, hyl, hxi, hyi, hg⟩
    · exact Or.inr ⟨j, by omega, hjh, x, hxl, y, hyl, hxi, hyi, hg⟩
  · rintro (⟨j, hjl, hjh, x, hx, y, hy, hxi, hyi, hg⟩ |
      ⟨j, hjl, hjh, x, hx, y, hy, hxi, hyi, hg⟩)
    · exact ⟨j, hjl, hjh.trans_le hh, x, ((keep_mem _ _ _ _ _).mp hx).1,
        y, ((keep_mem _ _ _ _ _).mp hy).1, hxi, hyi, hg⟩
    · exact ⟨j, hl.trans hjl, hjh, x, ((keep_mem _ _ _ _ _).mp hx).1,
        y, ((keep_mem _ _ _ _ _).mp hy).1, hxi, hyi, hg⟩

theorem correct (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (leaf : ℕ → List α → List β → Result) (goal : α → β → Prop)
    (hs₁ : ∀ x, Monotone (fun i : Fin (inc₁ x).size => (inc₁ x)[i.val]))
    (hs₂ : ∀ y, Monotone (fun i : Fin (inc₂ y).size => (inc₂ y)[i.val]))
    (C : ℕ)
    (hleaf : ∀ j xs ys, xs.length + ys.length ≤ C →
      ((leaf j xs ys).accepted = true ↔ ∃ x ∈ xs, ∃ y ∈ ys, goal x y))
    (k lo hi : ℕ) (xs : List α) (ys : List β) (hwidth : hi - lo ≤ 2 ^ k)
    (hsize : xs.length + ys.length ≤ C) :
    (run inc₁ inc₂ leaf k lo hi xs ys).accepted = true ↔
      Witness inc₁ inc₂ goal lo hi xs ys := by
  induction k generalizing lo hi xs ys with
  | zero =>
    have hsmall : hi ≤ lo + 1 := by simp only [pow_zero] at hwidth; omega
    have hchild : (keep inc₁ lo hi xs).length + (keep inc₂ lo hi ys).length ≤ C :=
      (Nat.add_le_add (keep_length _ _ _ _) (keep_length _ _ _ _)).trans hsize
    by_cases he : ((keep inc₁ lo hi xs).isEmpty || (keep inc₂ lo hi ys).isEmpty) = true
    · simp only [run, he, ↓reduceIte]
      exact ⟨by simp, fun h => False.elim (witness_empty _ _ _ hs₁ hs₂ _ _ _ _ he h)⟩
    · simp only [run, he, finish]
      exact (hleaf _ _ _ hchild).trans (witness_singleton _ _ _ hs₁ hs₂ _ _ _ _ hsmall).symm
  | succ k ih =>
    have hchild : (keep inc₁ lo hi xs).length + (keep inc₂ lo hi ys).length ≤ C :=
      (Nat.add_le_add (keep_length _ _ _ _) (keep_length _ _ _ _)).trans hsize
    by_cases he : ((keep inc₁ lo hi xs).isEmpty || (keep inc₂ lo hi ys).isEmpty) = true
    · simp only [run, he, ↓reduceIte]
      exact ⟨by simp, fun h => False.elim (witness_empty _ _ _ hs₁ hs₂ _ _ _ _ he h)⟩
    · by_cases hsmall : hi ≤ lo + 1
      · simp only [run, he, hsmall, ↓reduceIte, finish]
        exact (hleaf _ _ _ hchild).trans (witness_singleton _ _ _ hs₁ hs₂ _ _ _ _ hsmall).symm
      · have hl : lo ≤ (lo + hi) / 2 := by omega
        have hh : (lo + hi) / 2 ≤ hi := by omega
        have hw₁ : (lo + hi) / 2 - lo ≤ 2 ^ k := by rw [pow_succ] at hwidth; omega
        have hw₂ : hi - (lo + hi) / 2 ≤ 2 ^ k := by rw [pow_succ] at hwidth; omega
        simp only [run, he, hsmall, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true,
          ih _ _ _ _ hw₁ hchild, ih _ _ _ _ hw₂ hchild]
        exact (witness_split _ _ _ hs₁ hs₂ _ _ _ _ _ hl hh).symm

/-- Retaining parent buffers through both children costs only depth times
input length, plus the terminal callback's workspace. -/
theorem peak_le (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (leaf : ℕ → List α → List β → Result) (L : ℕ)
    (hleaf : ∀ j xs ys, (leaf j xs ys).peak ≤ L)
    (k lo hi : ℕ) (xs : List α) (ys : List β) :
    (run inc₁ inc₂ leaf k lo hi xs ys).peak ≤
      2 * (k + 1) * (xs.length + ys.length) + L := by
  induction k generalizing lo hi xs ys with
  | zero =>
    have hx := keep_length inc₁ lo hi xs
    have hy := keep_length inc₂ lo hi ys
    have hf := hleaf lo (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
    simp only [run]
    split_ifs <;> dsimp only [finish] <;> omega
  | succ k ih =>
    have hx := keep_length inc₁ lo hi xs
    have hy := keep_length inc₂ lo hi ys
    have hf := hleaf lo (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
    simp only [run]
    split_ifs
    · dsimp only
      nlinarith
    · dsimp only [finish]
      nlinarith
    · dsimp only
      have h₁ := ih lo ((lo + hi) / 2) (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
      have h₂ := ih ((lo + hi) / 2) hi (keep inc₁ lo hi xs) (keep inc₂ lo hi ys)
      have hm := max_le h₁ h₂
      nlinarith

/-- Retaining parent buffers through both children costs only depth times
input length, plus the terminal callback's workspace. -/
theorem peak_le_capacity (inc₁ : α → Array ℕ) (inc₂ : β → Array ℕ)
    (leaf : ℕ → List α → List β → Result) (C L : ℕ)
    (hleaf : ∀ j xs ys, xs.length + ys.length ≤ C → (leaf j xs ys).peak ≤ L)
    (k lo hi : ℕ) (xs : List α) (ys : List β) (hsize : xs.length + ys.length ≤ C) :
    (run inc₁ inc₂ leaf k lo hi xs ys).peak ≤
      2 * (k + 1) * (xs.length + ys.length) + L := by
  induction k generalizing lo hi xs ys with
  | zero =>
    have hx := keep_length inc₁ lo hi xs
    have hy := keep_length inc₂ lo hi ys
    have hchild : (keep inc₁ lo hi xs).length + (keep inc₂ lo hi ys).length ≤ C := by omega
    have hf := hleaf lo (keep inc₁ lo hi xs) (keep inc₂ lo hi ys) hchild
    simp only [run]
    split_ifs <;> dsimp only [finish] <;> omega
  | succ k ih =>
    have hx := keep_length inc₁ lo hi xs
    have hy := keep_length inc₂ lo hi ys
    have hchild : (keep inc₁ lo hi xs).length + (keep inc₂ lo hi ys).length ≤ C := by omega
    have hf := hleaf lo (keep inc₁ lo hi xs) (keep inc₂ lo hi ys) hchild
    simp only [run]
    split_ifs
    · dsimp only
      nlinarith
    · dsimp only [finish]
      nlinarith
    · dsimp only
      have h₁ := ih lo ((lo + hi) / 2) (keep inc₁ lo hi xs) (keep inc₂ lo hi ys) hchild
      have h₂ := ih ((lo + hi) / 2) hi (keep inc₁ lo hi xs) (keep inc₂ lo hi ys) hchild
      have hm := max_le h₁ h₂
      nlinarith

end LowSpaceSubsetSum.SeparatorTraversal

end OAI
