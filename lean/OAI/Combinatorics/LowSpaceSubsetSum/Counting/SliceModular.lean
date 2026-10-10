import OAI.Combinatorics.LowSpaceSubsetSum.Streams.SliceCursor
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ModularCursor

namespace OAI

/-!
# Modular pivot readers on shared-array slices

Binary pivot queries and subsequent cyclic reads access the same immutable
array through the slice address map. No reordered slice is stored. Empty,
direct and complementary rows all use the same constant-size cursor type.
-/

namespace LowSpaceSubsetSum
namespace SliceModular

variable {α : Type*}

def forward (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) : SliceCursor.State xs.size :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    ⟨rr, some (ModularCursor.forwardStart (SliceCursor.values xs rr) residue P r k)⟩
  else ⟨rr, none⟩

def reverse (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (K : ℤ) (k : ℕ) : SliceCursor.State xs.size :=
  if h : 0 < rr.length then
    haveI : NeZero rr.length := ⟨by omega⟩
    ⟨rr, some (ModularCursor.reverseStart (SliceCursor.values xs rr) residue K k)⟩
  else ⟨rr, none⟩

theorem forward_output (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) (hk : rr.length < 2 ^ k)
    (hs : Monotone (fun i : Fin rr.length => residue (SliceCursor.values xs rr i))) :
    SliceCursor.output xs (forward xs rr residue P r k) =
      ModularRows.direct P r residue (SliceCursor.slice xs rr) := by
  by_cases h : 0 < rr.length
  · have : NeZero rr.length := ⟨by omega⟩
    rw [forward, dite_eq_left h]
    exact ModularCursor.forward_trace (SliceCursor.values xs rr) residue P r k hk hs
  · have hz : rr.length = 0 := by omega
    rw [forward, dite_eq_right h]
    simp [SliceCursor.output, SliceCursor.slice, hz, ModularRows.direct]

theorem reverse_output (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (K : ℤ) (k : ℕ) (hk : rr.length < 2 ^ k)
    (hs : Monotone (fun i : Fin rr.length => residue (SliceCursor.values xs rr i))) :
    SliceCursor.output xs (reverse xs rr residue K k) =
      ModularRows.complementary K residue (SliceCursor.slice xs rr) := by
  by_cases h : 0 < rr.length
  · have : NeZero rr.length := ⟨by omega⟩
    rw [reverse, dite_eq_left h]
    exact ModularCursor.reverse_trace (SliceCursor.values xs rr) residue K k hk hs
  · have hz : rr.length = 0 := by omega
    rw [reverse, dite_eq_right h]
    simp [SliceCursor.output, SliceCursor.slice, hz, ModularRows.complementary]

theorem forward_perm (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) (hk : rr.length < 2 ^ k)
    (hs : Monotone (fun i : Fin rr.length => residue (SliceCursor.values xs rr i))) :
    (SliceCursor.output xs (forward xs rr residue P r k)).Perm (SliceCursor.slice xs rr) := by
  rw [forward_output xs rr residue P r k hk hs]
  exact ModularRows.direct_perm _ _ _ _

theorem reverse_perm (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (K : ℤ) (k : ℕ) (hk : rr.length < 2 ^ k)
    (hs : Monotone (fun i : Fin rr.length => residue (SliceCursor.values xs rr i))) :
    (SliceCursor.output xs (reverse xs rr residue K k)).Perm (SliceCursor.slice xs rr) := by
  rw [reverse_output xs rr residue K k hk hs]
  exact ModularRows.complementary_perm _ _ _

theorem forward_sorted (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P r : ℤ) (k : ℕ) (hk : rr.length < 2 ^ k)
    (hs : Monotone (fun i : Fin rr.length => residue (SliceCursor.values xs rr i)))
    (hr : 0 ≤ r) (hrP : r < P)
    (hbound : ∀ x ∈ SliceCursor.slice xs rr, 0 ≤ residue x ∧ residue x < P) :
    (SliceCursor.output xs (forward xs rr residue P r k)).Pairwise
      (fun x y => (r + residue x) % P ≤ (r + residue y) % P) := by
  rw [forward_output xs rr residue P r k hk hs]
  exact ModularRows.direct_sorted hr hrP residue _ hbound
    (List.pairwise_ofFn.mpr (fun _ _ h => hs h.le))

theorem reverse_sorted (xs : Array α) (rr : SliceCursor.Range xs.size)
    (residue : α → ℤ) (P K : ℤ) (k : ℕ) (hk : rr.length < 2 ^ k)
    (hs : Monotone (fun i : Fin rr.length => residue (SliceCursor.values xs rr i)))
    (hK : 0 ≤ K) (hKP : K < P)
    (hbound : ∀ x ∈ SliceCursor.slice xs rr, 0 ≤ residue x ∧ residue x < P) :
    (SliceCursor.output xs (reverse xs rr residue K k)).Pairwise
      (fun x y => (K - residue x) % P ≤ (K - residue y) % P) := by
  rw [reverse_output xs rr residue K k hk hs]
  exact ModularRows.complementary_sorted hK hKP residue _ hbound
    (List.pairwise_ofFn.mpr (fun _ _ h => hs h.le))

end SliceModular
end LowSpaceSubsetSum

end OAI
