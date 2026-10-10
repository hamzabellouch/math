import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace OAI

/-!
# Bounded binary pivot search

A search state consists of two endpoints of a half-open interval. Each step
performs at most one indexed predicate query and halves the interval. The
predicate is true on a prefix, including the empty and full prefixes. After
`k` steps with array length less than `2^k`, the endpoints agree and identify
the exact boundary. This is the pivot rule needed by cyclic modular rows.
-/

namespace LowSpaceSubsetSum
namespace BinaryPivot

structure Cut (n : ℕ) where
  lo : ℕ
  hi : ℕ
  ordered : lo ≤ hi
  bounded : hi ≤ n
  deriving DecidableEq

def initial (n : ℕ) : Cut n := ⟨0, n, Nat.zero_le _, le_rfl⟩

def width {n : ℕ} (c : Cut n) : ℕ := c.hi - c.lo

def step {n : ℕ} (p : Fin n → Bool) (c : Cut n) : Cut n :=
  if h : c.lo < c.hi then
    let mid := (c.lo + c.hi) / 2
    have hmid : mid < n := by have := c.bounded; dsimp [mid]; omega
    if p ⟨mid, hmid⟩ then
      ⟨mid + 1, c.hi, by dsimp [mid]; omega, c.bounded⟩
    else
      ⟨c.lo, mid, by dsimp [mid]; omega, by have := c.bounded; dsimp [mid]; omega⟩
  else c

def PrefixPredicate {n : ℕ} (p : Fin n → Bool) : Prop :=
  ∀ i j, i.val ≤ j.val → p j = true → p i = true

def Separates {n : ℕ} (p : Fin n → Bool) (c : Cut n) : Prop :=
  (∀ i, i.val < c.lo → p i = true) ∧ (∀ i, c.hi ≤ i.val → p i = false)

theorem initial_separates {n : ℕ} (p : Fin n → Bool) : Separates p (initial n) := by
  constructor
  · intro i hi
    simp [initial] at hi
  · intro i hi
    have := i.isLt
    simp only [initial] at hi
    omega

theorem step_separates {n : ℕ} (p : Fin n → Bool) (hp : PrefixPredicate p)
    (c : Cut n) (hc : Separates p c) : Separates p (step p c) := by
  unfold step
  split_ifs with h
  · dsimp only
    split_ifs with hmid
    · constructor
      · intro i hi
        exact hp i _ (by dsimp at hi ⊢; omega) hmid
      · exact hc.2
    · constructor
      · exact hc.1
      · intro i hi
        by_cases hi' : p i = true
        · have hcontra := hp ⟨(c.lo + c.hi) / 2, by have := c.bounded; omega⟩ i hi hi'
          exact False.elim (hmid hcontra)
        · exact Bool.eq_false_iff.mpr hi'
  · exact hc

theorem step_width_le_half {n : ℕ} (p : Fin n → Bool) (c : Cut n) :
    width (step p c) ≤ width c / 2 := by
  have horder := c.ordered
  unfold step
  split_ifs with h
  · dsimp only
    split_ifs <;> dsimp only [width] <;> omega
  · simp only [width]
    omega

theorem iterate_separates {n : ℕ} (p : Fin n → Bool) (hp : PrefixPredicate p)
    (k : ℕ) (c : Cut n) (hc : Separates p c) : Separates p ((step p)^[k] c) := by
  induction k generalizing c with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (step_separates p hp c hc)

theorem iterate_width_zero {n : ℕ} (p : Fin n → Bool) (k : ℕ) (c : Cut n)
    (hk : width c < 2 ^ k) : width ((step p)^[k] c) = 0 := by
  induction k generalizing c with
  | zero => simpa using hk
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    have hh := step_width_le_half p c
    rw [pow_succ] at hk
    omega

def search {n : ℕ} (p : Fin n → Bool) (k : ℕ) : Cut n := (step p)^[k] (initial n)

theorem search_exact {n : ℕ} (p : Fin n → Bool) (hp : PrefixPredicate p)
    (k : ℕ) (hk : n < 2 ^ k) :
    (search p k).lo = (search p k).hi ∧
      ∀ i : Fin n, p i = true ↔ i.val < (search p k).lo := by
  have hsep := iterate_separates p hp k (initial n) (initial_separates p)
  change Separates p (search p k) at hsep
  have hzero := iterate_width_zero p k (initial n) (by simpa [width, initial] using hk)
  have horder := (search p k).ordered
  change width (search p k) = 0 at hzero
  simp only [width] at hzero
  have heq : (search p k).lo = (search p k).hi := by omega
  refine ⟨heq, fun i => ⟨?_, hsep.1 i⟩⟩
  intro hi
  by_contra h
  have hfalse := hsep.2 i (by omega)
  simp [hi] at hfalse

theorem search_split {n : ℕ} {α : Type*} (a : Fin n → α) (p : α → Bool)
    (hp : PrefixPredicate (fun i => p (a i))) (k : ℕ) (hk : n < 2 ^ k) :
    (∀ x ∈ (List.ofFn a).take (search (fun i => p (a i)) k).lo, p x = true) ∧
    (∀ x ∈ (List.ofFn a).drop (search (fun i => p (a i)) k).lo, p x = false) := by
  let c := search (fun i => p (a i)) k
  have hboundary := (search_exact (fun i => p (a i)) hp k hk).2
  have hc : c.lo ≤ n := c.ordered.trans c.bounded
  change ∀ i : Fin n, p (a i) = true ↔ i.val < c.lo at hboundary
  change (∀ x ∈ (List.ofFn a).take c.lo, p x = true) ∧
    (∀ x ∈ (List.ofFn a).drop c.lo, p x = false)
  constructor
  · intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hin : i < n := by simp only [List.length_take, List.length_ofFn] at hi; omega
    have hiq : i < c.lo := by simp only [List.length_take, List.length_ofFn] at hi; omega
    rw [List.getElem_take, List.getElem_ofFn] at hix
    rw [← hix]
    exact (hboundary ⟨i, hin⟩).mpr hiq
  · intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hin : c.lo + i < n := by
      simp only [List.length_drop, List.length_ofFn] at hi
      omega
    rw [List.getElem_drop, List.getElem_ofFn] at hix
    rw [← hix]
    apply Bool.eq_false_iff.mpr
    intro he
    have hlt := (hboundary ⟨c.lo + i, hin⟩).mp he
    change c.lo + i < c.lo at hlt
    omega

end BinaryPivot
end LowSpaceSubsetSum

end OAI
