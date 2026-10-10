import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace OAI

/-!
# The modular pivot order of a pair-stream row

These are the two cyclic orders in `lem:streams`. The list is an analysis view
of one sorted slice: implementation can traverse the slice by its pivot and
cursor, rather than allocating the reordered list. The permutation theorems
preserve occurrence multiplicity, including repeated residues.
-/

namespace LowSpaceSubsetSum
namespace ModularRows

variable {α : Type*}

def direct (P r : ℤ) (residue : α → ℤ) (xs : List α) : List α :=
  xs.filter (fun x => decide (P - r ≤ residue x)) ++
    xs.filter (fun x => decide (residue x < P - r))

def complementary (K : ℤ) (residue : α → ℤ) (xs : List α) : List α :=
  (xs.filter (fun x => decide (residue x ≤ K))).reverse ++
    (xs.filter (fun x => decide (K < residue x))).reverse

theorem direct_perm (P r : ℤ) (residue : α → ℤ) (xs : List α) :
    (direct P r residue xs).Perm xs := by
  simpa only [direct, ← decide_not, not_le] using
    List.filter_append_perm (fun x => decide (P - r ≤ residue x)) xs

theorem complementary_perm (K : ℤ) (residue : α → ℤ) (xs : List α) :
    (complementary K residue xs).Perm xs := by
  apply ((List.reverse_perm _).append (List.reverse_perm _)).trans
  simpa only [← decide_not, not_le] using List.filter_append_perm (fun x => decide (residue x ≤ K)) xs

theorem direct_wrapped {P r x : ℤ} (_hr : 0 ≤ r) (hrP : r < P)
    (_hx : 0 ≤ x) (hxP : x < P) (hwrap : P - r ≤ x) :
    (r + x) % P = r + x - P := by
  rw [← Int.sub_emod_right (r + x) P]
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem direct_unwrapped {P r x : ℤ} (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hwrap : x < P - r) : (r + x) % P = r + x :=
  Int.emod_eq_of_lt (by omega) (by omega)

theorem complementary_low {P K x : ℤ} (_hK : 0 ≤ K) (hKP : K < P)
    (hx : 0 ≤ x) (hsmall : x ≤ K) : (K - x) % P = K - x :=
  Int.emod_eq_of_lt (by omega) (by omega)

theorem complementary_high {P K x : ℤ} (hK : 0 ≤ K) (_hKP : K < P)
    (hxP : x < P) (hlarge : K < x) : (K - x) % P = K - x + P := by
  rw [← Int.add_emod_right (K - x) P]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Direct cyclic traversal is sorted by normalized pair residue. -/
theorem direct_sorted {P r : ℤ} (hr : 0 ≤ r) (hrP : r < P)
    (residue : α → ℤ) (xs : List α)
    (hbound : ∀ x ∈ xs, 0 ≤ residue x ∧ residue x < P)
    (hsort : xs.Pairwise (fun x y => residue x ≤ residue y)) :
    (direct P r residue xs).Pairwise
      (fun x y => (r + residue x) % P ≤ (r + residue y) % P) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (hsort.filter (fun x => decide (P - r ≤ residue x))).imp_of_mem
    intro x y hx hy hxy
    obtain ⟨hxmem, hxwrap⟩ := List.mem_filter.mp hx
    obtain ⟨hymem, hywrap⟩ := List.mem_filter.mp hy
    have hxw : P - r ≤ residue x := of_decide_eq_true hxwrap
    have hyw : P - r ≤ residue y := of_decide_eq_true hywrap
    rw [direct_wrapped hr hrP (hbound x hxmem).1 (hbound x hxmem).2 hxw,
      direct_wrapped hr hrP (hbound y hymem).1 (hbound y hymem).2 hyw]
    omega
  · apply (hsort.filter (fun x => decide (residue x < P - r))).imp_of_mem
    intro x y hx hy hxy
    obtain ⟨hxmem, hxwrap⟩ := List.mem_filter.mp hx
    obtain ⟨hymem, hywrap⟩ := List.mem_filter.mp hy
    rw [direct_unwrapped hr (hbound x hxmem).1 (of_decide_eq_true hxwrap),
      direct_unwrapped hr (hbound y hymem).1 (of_decide_eq_true hywrap)]
    omega
  · intro x hx y hy
    obtain ⟨hxmem, hxwrap⟩ := List.mem_filter.mp hx
    obtain ⟨hymem, hywrap⟩ := List.mem_filter.mp hy
    rw [direct_wrapped hr hrP (hbound x hxmem).1 (hbound x hxmem).2
        (of_decide_eq_true hxwrap),
      direct_unwrapped hr (hbound y hymem).1 (of_decide_eq_true hywrap)]
    have := (hbound x hxmem).2
    have := (hbound y hymem).1
    omega

/-- Reverse cyclic traversal is sorted by the complementary residue. -/
theorem complementary_sorted {P K : ℤ} (hK : 0 ≤ K) (hKP : K < P)
    (residue : α → ℤ) (xs : List α)
    (hbound : ∀ x ∈ xs, 0 ≤ residue x ∧ residue x < P)
    (hsort : xs.Pairwise (fun x y => residue x ≤ residue y)) :
    (complementary K residue xs).Pairwise
      (fun x y => (K - residue x) % P ≤ (K - residue y) % P) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_reverse.mpr
    apply (hsort.filter (fun x => decide (residue x ≤ K))).imp_of_mem
    intro x y hx hy hxy
    obtain ⟨hxmem, hxsmall⟩ := List.mem_filter.mp hx
    obtain ⟨hymem, hysmall⟩ := List.mem_filter.mp hy
    rw [complementary_low hK hKP (hbound x hxmem).1 (of_decide_eq_true hxsmall),
      complementary_low hK hKP (hbound y hymem).1 (of_decide_eq_true hysmall)]
    omega
  · apply List.pairwise_reverse.mpr
    apply (hsort.filter (fun x => decide (K < residue x))).imp_of_mem
    intro x y hx hy hxy
    obtain ⟨hxmem, hxlarge⟩ := List.mem_filter.mp hx
    obtain ⟨hymem, hylarge⟩ := List.mem_filter.mp hy
    rw [complementary_high hK hKP (hbound x hxmem).2 (of_decide_eq_true hxlarge),
      complementary_high hK hKP (hbound y hymem).2 (of_decide_eq_true hylarge)]
    omega
  · intro x hx y hy
    obtain ⟨hxmem, hxsmall⟩ := List.mem_filter.mp (List.mem_reverse.mp hx)
    obtain ⟨hymem, hylarge⟩ := List.mem_filter.mp (List.mem_reverse.mp hy)
    rw [complementary_low hK hKP (hbound x hxmem).1 (of_decide_eq_true hxsmall),
      complementary_high hK hKP (hbound y hymem).2 (of_decide_eq_true hylarge)]
    have := (hbound x hxmem).1
    have := (hbound y hymem).2
    omega

/-- Filtering a row by the small modulus preserves its residue ordering. -/
theorem filtered_sorted (p c : ℤ) (weight residue : α → ℤ) (xs : List α)
    (hsort : xs.Pairwise (fun x y => residue x ≤ residue y)) :
    (xs.filter (fun x => decide (weight x % p = c % p))).Pairwise
      (fun x y => residue x ≤ residue y) := hsort.filter _

end ModularRows
end LowSpaceSubsetSum

end OAI
