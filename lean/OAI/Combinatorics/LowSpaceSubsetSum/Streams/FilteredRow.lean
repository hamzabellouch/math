import OAI.Combinatorics.LowSpaceSubsetSum.Counting.BinarySlice
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SliceModular
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PairCursor

namespace OAI

/-!
# The actual filtered modular row

The row searches the shared array by the small residue, searches the large
residue within that slice, and stores only the first occurrence and cursor.
Its sorted output is exactly the eligible occurrences. Positivity of the
large modulus supplies normalized keys; no coprimality is used.
-/

namespace LowSpaceSubsetSum
namespace FilteredRow

variable {α β : Type*}

abbrev PrimarySorted (xs : Array β) (w : β → ℤ) (p : ℤ) : Prop :=
  Monotone (fun i : Fin xs.size => w xs[i.val] % p)

abbrev SecondarySorted (xs : Array β) (w : β → ℤ) (p P : ℤ) : Prop :=
  ∀ i j : Fin xs.size, i ≤ j → w xs[i.val] % p = w xs[j.val] % p →
    w xs[i.val] % P ≤ w xs[j.val] % P

def range (xs : Array β) (w : β → ℤ) (p c wx : ℤ) (k : ℕ)
    (hs : PrimarySorted xs w p) (hk : xs.size < 2 ^ k) : SliceCursor.Range xs.size :=
  BinarySlice.range xs (fun y => w y % p) ((c - wx) % p) k hs hk

theorem range_length (xs : Array β) (w : β → ℤ) (p c wx : ℤ) (k : ℕ)
    (hs : PrimarySorted xs w p) (hk : xs.size < 2 ^ k) :
    (range xs w p c wx k hs hk).length < 2 ^ k := by
  have := (range xs w p c wx k hs hk).bounded
  omega

theorem range_sorted (xs : Array β) (w : β → ℤ) (p P c wx : ℤ) (k : ℕ)
    (hs : PrimarySorted xs w p) (ht : SecondarySorted xs w p P) (hk : xs.size < 2 ^ k) :
    Monotone (fun i : Fin (range xs w p c wx k hs hk).length =>
      w (SliceCursor.values xs (range xs w p c wx k hs hk) i) % P) :=
  BinarySlice.slice_sorted xs (fun y => w y % p) (fun y => w y % P)
    ((c - wx) % p) k hs hk ht

def forward (xs : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (hk : xs.size < 2 ^ k) (x : α) : PairCursor.State α xs.size :=
  ⟨x, SliceModular.forward xs (range xs wr p c (wl x) k hs hk)
    (fun y => wr y % P) P (wl x % P) k⟩

def reverse (xs : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c v : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (hk : xs.size < 2 ^ k) (x : α) : PairCursor.State α xs.size :=
  ⟨x, SliceModular.reverse xs (range xs wr p c (wl x) k hs hk)
    (fun y => wr y % P) ((v - wl x) % P) k⟩

theorem eligible (p c x y : ℤ) :
    (x + y) % p = c % p ↔ y % p = (c - x) % p := by
  change Int.ModEq p (x + y) c ↔ Int.ModEq p y (c - x)
  constructor
  · intro h
    simpa only [add_sub_cancel_left] using h.sub_right x
  · intro h
    simpa only [add_sub_cancel] using h.add_left x

theorem range_slice (xs : Array β) (wr : β → ℤ) (p c wx : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (hk : xs.size < 2 ^ k) :
    SliceCursor.slice xs (range xs wr p c wx k hs hk) =
      xs.toList.filter (fun y => decide ((wx + wr y) % p = c % p)) := by
  rw [range, BinarySlice.slice_eq_filter]
  congr 1
  funext y
  simp only [← eligible p c wx (wr y)]

theorem forward_perm (xs : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (ht : SecondarySorted xs wr p P)
    (hk : xs.size < 2 ^ k) (x : α) :
    (PairCursor.output xs (forward xs wl wr p P c k hs hk x)).Perm
      ((xs.toList.filter (fun y => decide ((wl x + wr y) % p = c % p))).map (fun y => (x, y))) := by
  have h := SliceModular.forward_perm xs (range xs wr p c (wl x) k hs hk)
    (fun y => wr y % P) P (wl x % P) k (range_length xs wr p c (wl x) k hs hk)
    (range_sorted xs wr p P c (wl x) k hs ht hk)
  rw [range_slice xs wr p c (wl x) k hs hk] at h
  exact h.map (fun y => (x, y))

theorem reverse_perm (xs : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c v : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (ht : SecondarySorted xs wr p P)
    (hk : xs.size < 2 ^ k) (x : α) :
    (PairCursor.output xs (reverse xs wl wr p P c v k hs hk x)).Perm
      ((xs.toList.filter (fun y => decide ((wl x + wr y) % p = c % p))).map (fun y => (x, y))) := by
  have h := SliceModular.reverse_perm xs (range xs wr p c (wl x) k hs hk)
    (fun y => wr y % P) ((v - wl x) % P) k (range_length xs wr p c (wl x) k hs hk)
    (range_sorted xs wr p P c (wl x) k hs ht hk)
  rw [range_slice xs wr p c (wl x) k hs hk] at h
  exact h.map (fun y => (x, y))

theorem forward_sorted (xs : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (ht : SecondarySorted xs wr p P)
    (hk : xs.size < 2 ^ k) (hP : 0 < P) (x : α) :
    (PairCursor.output xs (forward xs wl wr p P c k hs hk x)).Pairwise
      (fun a b => (wl a.1 + wr a.2) % P ≤ (wl b.1 + wr b.2) % P) := by
  have h := SliceModular.forward_sorted xs (range xs wr p c (wl x) k hs hk)
    (fun y => wr y % P) P (wl x % P) k (range_length xs wr p c (wl x) k hs hk)
    (range_sorted xs wr p P c (wl x) k hs ht hk)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (fun y _ => ⟨Int.emod_nonneg _ hP.ne', Int.emod_lt_of_pos _ hP⟩)
  change ((SliceCursor.output xs _).map (fun y => (x, y))).Pairwise _
  rw [List.pairwise_map]
  simpa only [forward, Int.add_emod, Int.emod_emod] using h

theorem reverse_sorted (xs : Array β) (wl : α → ℤ) (wr : β → ℤ) (p P c v : ℤ) (k : ℕ)
    (hs : PrimarySorted xs wr p) (ht : SecondarySorted xs wr p P)
    (hk : xs.size < 2 ^ k) (hP : 0 < P) (x : α) :
    (PairCursor.output xs (reverse xs wl wr p P c v k hs hk x)).Pairwise
      (fun a b => (v - wl a.1 - wr a.2) % P ≤ (v - wl b.1 - wr b.2) % P) := by
  have h := SliceModular.reverse_sorted xs (range xs wr p c (wl x) k hs hk)
    (fun y => wr y % P) P ((v - wl x) % P) k (range_length xs wr p c (wl x) k hs hk)
    (range_sorted xs wr p P c (wl x) k hs ht hk)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (fun y _ => ⟨Int.emod_nonneg _ hP.ne', Int.emod_lt_of_pos _ hP⟩)
  change ((SliceCursor.output xs _).map (fun y => (x, y))).Pairwise _
  rw [List.pairwise_map]
  simpa only [reverse, Int.sub_emod, Int.emod_emod] using h

end FilteredRow
end LowSpaceSubsetSum

end OAI
