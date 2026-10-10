import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CyclicCursor
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BinaryPivot

namespace OAI

/-!
# Executable modular row initialization

Binary search finds the first direct pivot and the position after the last
complementary pivot. The resulting constant-state cyclic cursor produces
the corresponding sorted modular row exactly. The cutoff search uses a
supplied number of steps; the theorem requires only that the array length
be smaller than `2^k`. Equal residues stay separate array occurrences.
-/

namespace LowSpaceSubsetSum
namespace ModularCursor

open scoped Fin.NatCast

variable {n : ℕ} [NeZero n] {α : Type*}

def forwardStart (a : Fin n → α) (residue : α → ℤ) (P r : ℤ) (k : ℕ) :
    CyclicCursor.State n :=
  ⟨Fin.ofNat n (BinaryPivot.search (fun i => decide (residue (a i) < P - r)) k).lo,
    n, false⟩

def reverseStart (a : Fin n → α) (residue : α → ℤ) (K : ℤ) (k : ℕ) :
    CyclicCursor.State n :=
  ⟨Fin.ofNat n (BinaryPivot.search (fun i => decide (residue (a i) ≤ K)) k).lo - 1,
    n, true⟩

theorem forward_trace (a : Fin n → α) (residue : α → ℤ) (P r : ℤ) (k : ℕ)
    (hk : n < 2 ^ k) (hsort : Monotone (fun i => residue (a i))) :
    CyclicCursor.trace a n (forwardStart a residue P r k) =
      ModularRows.direct P r residue (List.ofFn a) := by
  have hprefix : BinaryPivot.PrefixPredicate
      (fun i : Fin n => decide (residue (a i) < P - r)) := by
    intro i j hij hj
    apply decide_eq_true
    exact lt_of_le_of_lt (hsort hij) (of_decide_eq_true hj)
  have hsplit := BinaryPivot.search_split a
    (fun x => decide (residue x < P - r)) hprefix k hk
  let c := BinaryPivot.search (fun i : Fin n => decide (residue (a i) < P - r)) k
  let lo := (List.ofFn a).take c.lo
  let hi := (List.ofFn a).drop c.lo
  have hc : c.lo ≤ n := c.ordered.trans c.bounded
  have hlist : List.ofFn a = lo ++ hi := (List.take_append_drop c.lo _).symm
  apply CyclicCursor.forward_trace_eq_direct a P r residue lo hi hlist
    (Fin.ofNat n c.lo)
  · simp [lo, hc]
  · simpa only [decide_eq_true_eq] using hsplit.1
  · simpa only [decide_eq_false_iff_not, not_lt] using hsplit.2

theorem reverse_trace (a : Fin n → α) (residue : α → ℤ) (K : ℤ) (k : ℕ)
    (hk : n < 2 ^ k) (hsort : Monotone (fun i => residue (a i))) :
    CyclicCursor.trace a n (reverseStart a residue K k) =
      ModularRows.complementary K residue (List.ofFn a) := by
  have hprefix : BinaryPivot.PrefixPredicate
      (fun i : Fin n => decide (residue (a i) ≤ K)) := by
    intro i j hij hj
    apply decide_eq_true
    exact (hsort hij).trans (of_decide_eq_true hj)
  have hsplit := BinaryPivot.search_split a
    (fun x => decide (residue x ≤ K)) hprefix k hk
  let c := BinaryPivot.search (fun i : Fin n => decide (residue (a i) ≤ K)) k
  let lo := (List.ofFn a).take c.lo
  let hi := (List.ofFn a).drop c.lo
  have hc : c.lo ≤ n := c.ordered.trans c.bounded
  have hlist : List.ofFn a = lo ++ hi := (List.take_append_drop c.lo _).symm
  apply CyclicCursor.reverse_trace_eq_complementary a K residue lo hi hlist
    (Fin.ofNat n c.lo)
  · simp [lo, hc]
  · simpa only [decide_eq_true_eq] using hsplit.1
  · simpa only [decide_eq_false_iff_not, not_le] using hsplit.2

theorem forward_sorted (a : Fin n → α) (residue : α → ℤ) (P r : ℤ) (k : ℕ)
    (hk : n < 2 ^ k) (hsort : Monotone (fun i => residue (a i)))
    (hr : 0 ≤ r) (hrP : r < P) (hbound : ∀ i, 0 ≤ residue (a i) ∧ residue (a i) < P) :
    (CyclicCursor.trace a n (forwardStart a residue P r k)).Pairwise
      (fun x y => (r + residue x) % P ≤ (r + residue y) % P) := by
  rw [forward_trace a residue P r k hk hsort]
  apply ModularRows.direct_sorted hr hrP
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hbound i
  · exact List.pairwise_ofFn.mpr (fun _ _ h => hsort h.le)

theorem reverse_sorted (a : Fin n → α) (residue : α → ℤ) (P K : ℤ) (k : ℕ)
    (hk : n < 2 ^ k) (hsort : Monotone (fun i => residue (a i)))
    (hK : 0 ≤ K) (hKP : K < P) (hbound : ∀ i, 0 ≤ residue (a i) ∧ residue (a i) < P) :
    (CyclicCursor.trace a n (reverseStart a residue K k)).Pairwise
      (fun x y => (K - residue x) % P ≤ (K - residue y) % P) := by
  rw [reverse_trace a residue K k hk hsort]
  apply ModularRows.complementary_sorted hK hKP
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hbound i
  · exact List.pairwise_ofFn.mpr (fun _ _ h => hsort h.le)

end ModularCursor
end LowSpaceSubsetSum

end OAI
