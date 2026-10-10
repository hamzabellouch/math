import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MergedReader
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-!
# Binary indexing and empty padding for the row tournament

Binary paths index a power-of-two set of leaves. Array indices occupy the
initial segment and all other leaves are empty. The reindexing proof counts
exact occurrences; its finite sums and lists are analysis views only.
-/

namespace LowSpaceSubsetSum
namespace PaddedRows

variable {α σ : Type*}

def index (d : ℕ) : RowMerge.Path d ≃ Fin (2 ^ d) :=
  (Equiv.piCongrRight (fun _ : Fin d => finTwoEquiv.symm)).trans finFunctionFinEquiv

def next (read : σ → Option (α × σ)) : Option σ → Option (α × Option σ)
  | none => none
  | some s => (read s).map (fun z => (z.1, some z.2))

def view (output : σ → List α) : Option σ → List α
  | none => []
  | some s => output s

theorem reader (read : σ → Option (α × σ)) (output : σ → List α)
    (hread : RowMerge.IsReader read output) : RowMerge.IsReader (next read) (view output) := by
  intro s
  cases s with
  | none => rfl
  | some s =>
    have h := hread s
    cases hr : read s with
    | none => simpa only [next, hr, Option.map_none, view] using h
    | some z => simpa only [next, hr, Option.map_some, view] using h

def rows (xs : Array σ) (d : ℕ) (p : RowMerge.Path d) : Option σ :=
  if h : (index d p).val < xs.size then some xs[(index d p).val] else none

theorem rows_sorted (xs : Array σ) (d : ℕ) (output : σ → List α) (key : α → ℤ)
    (hs : ∀ s ∈ xs.toList, (output s).Pairwise (fun x y => key x ≤ key y))
    (p : RowMerge.Path d) :
    (view output (rows xs d p)).Pairwise (fun x y => key x ≤ key y) := by
  unfold rows
  split_ifs with h
  · apply hs
    exact List.mem_iff_getElem.mpr ⟨(index d p).val,
      by simpa only [Array.length_toList] using h, by simp⟩
  · simp [view]

theorem sum_padding {M : Type*} [AddCommMonoid M] (n m : ℕ) (hnm : n ≤ m)
    (f : Fin n → M) :
    (∑ i : Fin m, if h : i.val < n then f ⟨i.val, h⟩ else 0) = ∑ i : Fin n, f i := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    simp
  | succ m ih =>
    by_cases hn : n ≤ m
    · rw [Fin.sum_univ_castSucc]
      have hlast : ¬ m < n := by omega
      simp only [Fin.val_castSucc, Fin.val_last, dite_eq_right hlast, add_zero]
      exact ih hn
    · have hn : n = m + 1 := by omega
      subst n
      apply Finset.sum_congr rfl
      intro i _
      exact dite_eq_left i.isLt

theorem sum_rows {M : Type*} [AddCommMonoid M] (xs : Array σ) (d : ℕ)
    (hd : xs.size ≤ 2 ^ d) (f : σ → M) :
    (∑ p : RowMerge.Path d, match rows xs d p with | none => 0 | some s => f s) =
      ∑ i : Fin xs.size, f xs[i.val] := by
  calc
    _ = ∑ i : Fin (2 ^ d), if h : i.val < xs.size then f xs[i.val] else 0 := by
      apply Fintype.sum_equiv (index d)
      intro p
      dsimp only [rows]
      split_ifs <;> rfl
    _ = _ := sum_padding xs.size (2 ^ d) hd (fun i => f xs[i.val])

theorem row_bag (xs : Array σ) (d : ℕ) (hd : xs.size ≤ 2 ^ d) (output : σ → List α) :
    (∑ p : RowMerge.Path d, (view output (rows xs d p) : Multiset α)) =
      ∑ i : Fin xs.size, (output xs[i.val] : Multiset α) := by
  calc
    _ = ∑ p : RowMerge.Path d,
        match rows xs d p with | none => 0 | some s => (output s : Multiset α) := by
      apply Finset.sum_congr rfl
      intro p _
      cases rows xs d p <;> rfl
    _ = _ := sum_rows xs d hd (fun s => (output s : Multiset α))

end PaddedRows
end LowSpaceSubsetSum

end OAI
