import OAI.Combinatorics.LowSpaceSubsetSum.Streams.SliceCursor
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BinaryPivot
import Mathlib.Data.List.TakeDrop

namespace OAI

/-!
# Binary search for the exact eligible slice

Two prefix searches find the half-open interval of occurrences with a fixed
primary key. A secondary order within equal primary keys gives the sorted
slice needed by modular row initialization. Both searches query the shared
array directly, including when the eligible slice is empty.
-/

namespace LowSpaceSubsetSum
namespace BinarySlice

variable {α : Type*}

def lower (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ) : ℕ :=
  (BinaryPivot.search (fun i : Fin xs.size => decide (key xs[i.val] < r)) k).lo

def upper (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ) : ℕ :=
  (BinaryPivot.search (fun i : Fin xs.size => decide (key xs[i.val] ≤ r)) k).lo

theorem lower_spec (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    ∀ i : Fin xs.size, key xs[i.val] < r ↔ i.val < lower xs key r k := by
  have hp : BinaryPivot.PrefixPredicate
      (fun i : Fin xs.size => decide (key xs[i.val] < r)) := by
    intro i j hij hj
    exact decide_eq_true ((hs hij).trans_lt (of_decide_eq_true hj))
  simpa only [lower, decide_eq_true_eq] using
    (BinaryPivot.search_exact _ hp k hk).2

theorem upper_spec (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    ∀ i : Fin xs.size, key xs[i.val] ≤ r ↔ i.val < upper xs key r k := by
  have hp : BinaryPivot.PrefixPredicate
      (fun i : Fin xs.size => decide (key xs[i.val] ≤ r)) := by
    intro i j hij hj
    exact decide_eq_true ((hs hij).trans (of_decide_eq_true hj))
  simpa only [upper, decide_eq_true_eq] using
    (BinaryPivot.search_exact _ hp k hk).2

theorem lower_bounded (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ) :
    lower xs key r k ≤ xs.size :=
  (BinaryPivot.search _ k).ordered.trans (BinaryPivot.search _ k).bounded

theorem upper_bounded (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ) :
    upper xs key r k ≤ xs.size :=
  (BinaryPivot.search _ k).ordered.trans (BinaryPivot.search _ k).bounded

theorem ordered (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    lower xs key r k ≤ upper xs key r k := by
  by_contra h
  have hlow := lower_bounded xs key r k
  have hin : upper xs key r k < xs.size := by omega
  have hlt := (lower_spec xs key r k hs hk ⟨_, hin⟩).mpr (by dsimp; omega)
  have hle := (upper_spec xs key r k hs hk ⟨_, hin⟩).mp hlt.le
  change upper xs key r k < upper xs key r k at hle
  omega

def range (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    SliceCursor.Range xs.size :=
  ⟨lower xs key r k, upper xs key r k - lower xs key r k, by
    have := ordered xs key r k hs hk
    have := upper_bounded xs key r k
    omega⟩

theorem index_spec (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k)
    (i : Fin xs.size) :
    key xs[i.val] = r ↔ lower xs key r k ≤ i.val ∧ i.val < upper xs key r k := by
  have hl := lower_spec xs key r k hs hk i
  have hu := upper_spec xs key r k hs hk i
  omega

theorem slice_eq_filter (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k) :
    SliceCursor.slice xs (range xs key r k hs hk) =
      xs.toList.filter (fun x => decide (key x = r)) := by
  let lo := lower xs key r k
  let hi := upper xs key r k
  have hlo : lo ≤ hi := ordered xs key r k hs hk
  have hhi : hi ≤ xs.size := upper_bounded xs key r k
  let pre := xs.toList.take lo
  let mid := (xs.toList.drop lo).take (hi - lo)
  let suf := xs.toList.drop hi
  have hdec : xs.toList = pre ++ mid ++ suf := by
    have hd : mid ++ suf = xs.toList.drop lo := by
      dsimp only [mid, suf]
      have heq : lo + (hi - lo) = hi := by omega
      simpa only [heq] using List.drop_take_append_drop xs.toList lo (hi - lo)
    rw [List.append_assoc, hd]
    exact (List.take_append_drop lo xs.toList).symm
  have hp : pre.filter (fun x => decide (key x = r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi', hix⟩ := List.mem_iff_getElem.mp hx
    have hin : i < xs.size := by
      dsimp only [pre] at hi'
      simp only [List.length_take, Array.length_toList] at hi'
      omega
    have hil : i < lo := by
      dsimp only [pre] at hi'
      simp only [List.length_take, Array.length_toList] at hi'
      omega
    have hv := (lower_spec xs key r k hs hk ⟨i, hin⟩).mpr hil
    dsimp only [pre] at hix
    rw [List.getElem_take, Array.getElem_toList] at hix
    rw [← hix]
    simpa only [decide_eq_true_eq] using ne_of_lt hv
  have hm : mid.filter (fun x => decide (key x = r)) = mid := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨i, hi', hix⟩ := List.mem_iff_getElem.mp hx
    have hin : lo + i < xs.size := by
      dsimp only [mid] at hi'
      simp only [List.length_take, List.length_drop, Array.length_toList] at hi'
      omega
    have hili : lo + i < hi := by
      dsimp only [mid] at hi'
      simp only [List.length_take, List.length_drop, Array.length_toList] at hi'
      omega
    have hv := (index_spec xs key r k hs hk ⟨lo + i, hin⟩).mpr ⟨by dsimp; omega, hili⟩
    dsimp only [mid] at hix
    rw [List.getElem_take, List.getElem_drop, Array.getElem_toList] at hix
    rw [← hix]
    exact decide_eq_true hv
  have ht : suf.filter (fun x => decide (key x = r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi', hix⟩ := List.mem_iff_getElem.mp hx
    have hin : hi + i < xs.size := by
      dsimp only [suf] at hi'
      simp only [List.length_drop, Array.length_toList] at hi'
      omega
    have hv : ¬ key xs[hi + i] ≤ r := by
      intro hle
      have := (upper_spec xs key r k hs hk ⟨hi + i, hin⟩).mp hle
      change hi + i < hi at this
      omega
    dsimp only [suf] at hix
    rw [List.getElem_drop, Array.getElem_toList] at hix
    rw [← hix]
    simpa only [decide_eq_true_eq] using
      (show ¬ key xs[hi + i] = r from fun heq => hv heq.le)
  rw [SliceCursor.slice_eq_drop_take]
  change mid = xs.toList.filter _
  rw [hdec, List.filter_append, List.filter_append, hp, hm, ht]
  simp

theorem slice_key (xs : Array α) (key : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k)
    (i : Fin (range xs key r k hs hk).length) :
    key (SliceCursor.values xs (range xs key r k hs hk) i) = r := by
  have hmem : SliceCursor.values xs (range xs key r k hs hk) i ∈
      SliceCursor.slice xs (range xs key r k hs hk) := List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [slice_eq_filter xs key r k hs hk] at hmem
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

theorem slice_sorted (xs : Array α) (key secondary : α → ℤ) (r : ℤ) (k : ℕ)
    (hs : Monotone (fun i : Fin xs.size => key xs[i.val])) (hk : xs.size < 2 ^ k)
    (htie : ∀ i j : Fin xs.size, i ≤ j → key xs[i.val] = key xs[j.val] →
      secondary xs[i.val] ≤ secondary xs[j.val]) :
    Monotone (fun i : Fin (range xs key r k hs hk).length =>
      secondary (SliceCursor.values xs (range xs key r k hs hk) i)) := by
  intro i j hij
  let rr := range xs key r k hs hk
  have hi : rr.lo + i.val < xs.size := by
    have := rr.bounded
    have : i.val < rr.length := i.isLt
    omega
  have hj : rr.lo + j.val < xs.size := by
    have := rr.bounded
    have : j.val < rr.length := j.isLt
    omega
  apply htie ⟨rr.lo + i.val, hi⟩ ⟨rr.lo + j.val, hj⟩
    (show rr.lo + i.val ≤ rr.lo + j.val from Nat.add_le_add_left hij _)
  exact (slice_key xs key r k hs hk i).trans (slice_key xs key r k hs hk j).symm

end BinarySlice
end LowSpaceSubsetSum

end OAI
