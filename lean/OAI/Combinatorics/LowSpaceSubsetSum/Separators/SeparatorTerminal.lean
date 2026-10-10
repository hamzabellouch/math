import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorTraversal
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.SortedFind
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedSort

namespace OAI

/-! # The separator's terminal sort and first exact-weight match -/

namespace LowSpaceSubsetSum.SeparatorTerminal

variable {α β : Type*}

def read {γ : Type*} : List γ → Option (γ × List γ)
  | [] => none
  | x :: xs => some (x, xs)

theorem reader {γ : Type*} : RowMerge.IsReader (read (γ := γ)) id := by
  intro xs
  cases xs <;> rfl

def sort {γ : Type*} (key : γ → ℤ) (xs : List γ) : List γ × ℕ :=
  CountedSort.sort (fun x y => decide (key x ≤ key y)) xs

theorem sort_perm {γ : Type*} (key : γ → ℤ) (xs : List γ) :
    (sort key xs).1.Perm xs := by
  rw [sort, CountedSort.sort_value]
  exact List.mergeSort_perm _ _

theorem sort_sorted {γ : Type*} (key : γ → ℤ) (xs : List γ) :
    (sort key xs).1.Pairwise (fun x y => key x ≤ key y) := by
  rw [sort, CountedSort.sort_value]
  simpa only [decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun x y => decide (key x ≤ key y))
      (fun _ _ _ h₁ h₂ => decide_eq_true ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂)))
      (fun x y => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (key x) (key y)) xs

def run (wx : α → ℤ) (wy : β → ℤ) (target : ℤ) (xs : List α) (ys : List β) :
    SeparatorTraversal.Result :=
  if xs.isEmpty || ys.isEmpty then ⟨false, 0, 0⟩ else
    let left := sort wx xs
    let right := sort (fun y => target - wy y) ys
    let out := SortedFind.runAcc read wx read (fun y => target - wy y)
      (xs.length + ys.length + 1) left.1 right.1 0
    ⟨out.1, left.2 + right.2 + out.2,
      8 * (Nat.clog 2 (xs.length + ys.length) + 1) * (xs.length + ys.length + 1)⟩

theorem correct (wx : α → ℤ) (wy : β → ℤ) (target : ℤ) (xs : List α) (ys : List β) :
    (run wx wy target xs ys).accepted = true ↔ ∃ x ∈ xs, ∃ y ∈ ys, wx x + wy y = target := by
  by_cases he : (xs.isEmpty || ys.isEmpty) = true
  · have he' : xs = [] ∨ ys = [] := by simpa using he
    rcases he' with rfl | rfl <;> simp [run]
  · simp only [run, he, Bool.false_eq_true, ↓reduceIte]
    have hleft := sort_perm wx xs
    have hright := sort_perm (fun y => target - wy y) ys
    rw [SortedFind.correct read wx read (fun y => target - wy y) id reader id reader
      (xs.length + ys.length + 1) _ _ 0 (sort_sorted wx xs) (sort_sorted (fun y => target - wy y) ys)
      (by dsimp only [id]; rw [hleft.length_eq, hright.length_eq]; omega)]
    rw [MatchPotential.positive_iff]
    simp only [id_eq, hleft.mem_iff, hright.mem_iff]
    constructor <;> rintro ⟨x, hx, y, hy, h⟩ <;> exact ⟨x, hx, y, hy, by omega⟩

theorem scans_le (wx : α → ℤ) (wy : β → ℤ) (target : ℤ) (xs : List α) (ys : List β)
    (n : ℕ) (hx : xs.length ≤ 2 ^ n) (hy : ys.length ≤ 2 ^ n) :
    (run wx wy target xs ys).scans ≤ (6 * n + 7) * (xs.length + ys.length) := by
  by_cases he : (xs.isEmpty || ys.isEmpty) = true
  · simp [run, he]
  · have hn : 1 ≤ xs.length + ys.length := by
      have he' : xs ≠ [] ∧ ys ≠ [] := by simpa using he
      have := List.length_pos_iff.mpr he'.1
      omega
    have hl := CountedSort.sort_steps_of_index_bits
      (fun x y => decide (wx x ≤ wx y)) xs n hx
    have hr := CountedSort.sort_steps_of_index_bits
      (fun x y => decide (target - wy x ≤ target - wy y)) ys n hy
    have hq := SortedFind.queries_le read wx read (fun y => target - wy y)
      (xs.length + ys.length + 1) (sort wx xs).1 (sort (fun y => target - wy y) ys).1 0
    simp only [run, he, Bool.false_eq_true, ↓reduceIte, sort]
    dsimp only [sort] at hq
    nlinarith

/-- The caller's capacity guard also bounds the terminal cost on every input. -/
def bounded (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ) (xs : List α) (ys : List β) :
    SeparatorTraversal.Result :=
  if xs.length + ys.length ≤ 2 ^ n then run wx wy target xs ys else ⟨false, 0, 0⟩

theorem bounded_correct (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (xs : List α) (ys : List β) (h : xs.length + ys.length ≤ 2 ^ n) :
    (bounded n wx wy target xs ys).accepted = true ↔ ∃ x ∈ xs, ∃ y ∈ ys, wx x + wy y = target := by
  simpa only [bounded, h, ↓reduceIte] using correct wx wy target xs ys

theorem bounded_scans (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (xs : List α) (ys : List β) :
    (bounded n wx wy target xs ys).scans ≤ (6 * n + 7) * (xs.length + ys.length) := by
  unfold bounded
  split_ifs with h
  · exact scans_le _ _ _ _ _ n (by omega) (by omega)
  · dsimp
    omega

theorem bounded_peak (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (xs : List α) (ys : List β) :
    (bounded n wx wy target xs ys).peak ≤ 8 * (n + 1) * (2 ^ n + 1) := by
  unfold bounded
  split_ifs with h
  · unfold run
    split_ifs
    · dsimp
      omega
    · dsimp
      have := Nat.clog_le_of_le_pow (b := 2) h
      gcongr
  · dsimp
    omega

theorem bounded_peak_capacity (n C : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (xs : List α) (ys : List β) (hsize : xs.length + ys.length ≤ C) (hC : C ≤ 2 ^ n) :
    (bounded n wx wy target xs ys).peak ≤ 8 * (n + 1) * (C + 1) := by
  have hfit := hsize.trans hC
  simp only [bounded, hfit, ↓reduceIte]
  unfold run
  split_ifs
  · dsimp
    omega
  · dsimp
    have hlog := Nat.clog_le_of_le_pow (b := 2) hfit
    gcongr

end LowSpaceSubsetSum.SeparatorTerminal

end OAI
