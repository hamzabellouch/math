import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ModularRows
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Rotate

namespace OAI

/-!
# Constant-state cyclic array traversal

The mutable cursor has only a position, remaining length, and direction.
`next` accesses the shared immutable array once and changes these fields.
`trace` is an analysis view of repeated advances; it is not retained by the
stream. A complete traversal permutes array occurrences, so equal-valued
items are never lost at a cyclic pivot.
-/

namespace LowSpaceSubsetSum
namespace CyclicCursor

open scoped Fin.NatCast

variable {n : ℕ} [NeZero n] {α : Type*}

structure State (n : ℕ) where
  position : Fin n
  remaining : ℕ
  reverse : Bool
  deriving DecidableEq

def advance (c : State n) : State n :=
  ⟨if c.reverse then c.position - 1 else c.position + 1, c.remaining - 1, c.reverse⟩

def next (xs : Array α) [NeZero xs.size] (c : State xs.size) :
    Option (α × State xs.size) :=
  if c.remaining = 0 then none else some (xs[c.position.val], advance c)

@[simp] theorem next_eq_none_iff (xs : Array α) [NeZero xs.size] (c : State xs.size) :
    next xs c = none ↔ c.remaining = 0 := by
  simp [next]

@[simp] theorem advance_remaining (c : State n) :
    (advance c).remaining = c.remaining - 1 := rfl

@[simp] theorem advance_reverse (c : State n) : (advance c).reverse = c.reverse := rfl

/-- Analysis only: the finite output of a bounded number of advances. -/
def trace (a : Fin n → α) : ℕ → State n → List α
  | 0, _ => []
  | k + 1, c => if c.remaining = 0 then [] else a c.position :: trace a k (advance c)

def order (reverse : Bool) (p : Fin n) : Equiv.Perm (Fin n) where
  toFun i := if reverse then p - i else p + i
  invFun i := if reverse then p - i else i - p
  left_inv i := by cases reverse <;> simp
  right_inv i := by cases reverse <;> simp

theorem trace_eq_ofFn (a : Fin n → α) (k : ℕ) (c : State n) (hk : k ≤ c.remaining) :
    trace a k c = List.ofFn (fun j : Fin k =>
      a (if c.reverse then c.position - (j.val : Fin n) else c.position + (j.val : Fin n))) := by
  induction k generalizing c with
  | zero => simp [trace]
  | succ k ih =>
    have hc : c.remaining ≠ 0 := by omega
    have hk' : k ≤ (advance c).remaining := by simp only [advance_remaining]; omega
    rw [trace, ite_eq_right hc, ih (advance c) hk', List.ofFn_succ]
    congr 1
    · cases c.reverse <;> simp
    · apply congrArg List.ofFn
      funext j
      cases hrev : c.reverse <;>
        simp [advance, hrev, Fin.val_succ, Nat.cast_add, sub_eq_add_neg,
          add_comm, add_left_comm]

theorem forward_trace_eq_rotate (a : Fin n → α) (p : Fin n) :
    trace a n ⟨p, n, false⟩ = (List.ofFn a).rotate p.val := by
  rw [trace_eq_ofFn a n _ le_rfl]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_rotate, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod, Nat.add_comm]

theorem reverse_trace_eq_reverse_forward (a : Fin n → α) (p : Fin n) :
    trace a n ⟨p, n, true⟩ = (trace a n ⟨p + 1, n, false⟩).reverse := by
  rw [trace_eq_ofFn a n _ le_rfl, trace_eq_ofFn a n _ le_rfl]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_ofFn]
    simp only [↓reduceIte, Bool.false_eq_true, List.length_ofFn]
    have hi' : i < n := by simpa using hi
    have hsum : n - 1 - i + (i + 1) = n := by omega
    have hcast := congrArg (fun k : ℕ => (k : Fin n)) hsum
    simp only [Nat.cast_add, Nat.cast_one, Fin.natCast_self] at hcast
    have hneg : ((n - 1 - i : ℕ) : Fin n) = -((i : Fin n) + 1) :=
      eq_neg_iff_add_eq_zero.mpr hcast
    rw [hneg]
    congr 1
    abel

theorem forward_trace_split (a : Fin n → α) (lo hi : List α)
    (hlist : List.ofFn a = lo ++ hi) (p : Fin n)
    (hp : p.val = lo.length % n) :
    trace a n ⟨p, n, false⟩ = hi ++ lo := by
  have hlen : (lo ++ hi).length = n := by rw [← hlist, List.length_ofFn]
  rw [forward_trace_eq_rotate, hlist, hp, ← hlen, List.rotate_mod,
    List.rotate_append_length_eq]

theorem reverse_trace_split (a : Fin n → α) (lo hi : List α)
    (hlist : List.ofFn a = lo ++ hi) (p : Fin n)
    (hp : p.val = lo.length % n) :
    trace a n ⟨p - 1, n, true⟩ = lo.reverse ++ hi.reverse := by
  rw [reverse_trace_eq_reverse_forward]
  simp only [sub_add_cancel]
  rw [forward_trace_split a lo hi hlist p hp, List.reverse_append]

theorem direct_of_split (P r : ℤ) (residue : α → ℤ) (lo hi : List α)
    (hlo : ∀ x ∈ lo, residue x < P - r) (hhi : ∀ x ∈ hi, P - r ≤ residue x) :
    ModularRows.direct P r residue (lo ++ hi) = hi ++ lo := by
  have h₁ : lo.filter (fun x => decide (P - r ≤ residue x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hlo
  have h₂ : hi.filter (fun x => decide (P - r ≤ residue x)) = hi := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hhi
  have h₃ : lo.filter (fun x => decide (residue x < P - r)) = lo := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hlo
  have h₄ : hi.filter (fun x => decide (residue x < P - r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hhi
  simp only [ModularRows.direct, List.filter_append, h₁, h₂, h₃, h₄, List.nil_append, List.append_nil]

theorem complementary_of_split (K : ℤ) (residue : α → ℤ) (lo hi : List α)
    (hlo : ∀ x ∈ lo, residue x ≤ K) (hhi : ∀ x ∈ hi, K < residue x) :
    ModularRows.complementary K residue (lo ++ hi) = lo.reverse ++ hi.reverse := by
  have h₁ : lo.filter (fun x => decide (residue x ≤ K)) = lo := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hlo
  have h₂ : hi.filter (fun x => decide (residue x ≤ K)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hhi
  have h₃ : lo.filter (fun x => decide (K < residue x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hlo
  have h₄ : hi.filter (fun x => decide (K < residue x)) = hi := by
    apply List.filter_eq_self.mpr
    simpa only [decide_eq_true_eq, not_le, not_lt] using hhi
  simp [ModularRows.complementary, List.filter_append, h₁, h₂, h₃, h₄]

theorem forward_trace_eq_direct (a : Fin n → α) (P r : ℤ) (residue : α → ℤ)
    (lo hi : List α) (hlist : List.ofFn a = lo ++ hi) (p : Fin n)
    (hp : p.val = lo.length % n)
    (hlo : ∀ x ∈ lo, residue x < P - r) (hhi : ∀ x ∈ hi, P - r ≤ residue x) :
    trace a n ⟨p, n, false⟩ = ModularRows.direct P r residue (List.ofFn a) := by
  rw [hlist, direct_of_split P r residue lo hi hlo hhi]
  exact forward_trace_split a lo hi hlist p hp

theorem reverse_trace_eq_complementary (a : Fin n → α) (K : ℤ) (residue : α → ℤ)
    (lo hi : List α) (hlist : List.ofFn a = lo ++ hi) (p : Fin n)
    (hp : p.val = lo.length % n)
    (hlo : ∀ x ∈ lo, residue x ≤ K) (hhi : ∀ x ∈ hi, K < residue x) :
    trace a n ⟨p - 1, n, true⟩ = ModularRows.complementary K residue (List.ofFn a) := by
  rw [hlist, complementary_of_split K residue lo hi hlo hhi]
  exact reverse_trace_split a lo hi hlist p hp

theorem full_trace_perm (a : Fin n → α) (p : Fin n) (reverse : Bool) :
    (trace a n ⟨p, n, reverse⟩).Perm (List.ofFn a) := by
  rw [trace_eq_ofFn a n _ le_rfl]
  have h := (order reverse p).ofFn_comp_perm a
  simpa [order, Function.comp_def] using h

theorem full_trace_array_perm (xs : Array α) [NeZero xs.size]
    (p : Fin xs.size) (reverse : Bool) :
    (trace (fun j : Fin xs.size => xs[j.val]) xs.size ⟨p, xs.size, reverse⟩).Perm
      xs.toList := by
  have h := full_trace_perm (fun j : Fin xs.size => xs[j.val]) p reverse
  have hxs : List.ofFn (fun j : Fin xs.size => xs[j.val]) = xs.toList := by
    rw [← Array.toList_ofFn, Array.ofFn_getElem]
  rwa [hxs] at h

/-- Every stopped traversal reports exactly the consumed number of occurrences. -/
theorem trace_length (a : Fin n → α) (k : ℕ) (c : State n) (hk : k ≤ c.remaining) :
    (trace a k c).length = k := by rw [trace_eq_ofFn a k c hk, List.length_ofFn]

theorem advance_iterate_remaining (k : ℕ) (c : State n) :
    ((advance^[k]) c).remaining = c.remaining - k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, advance_remaining]
    omega

end CyclicCursor
end LowSpaceSubsetSum

end OAI
