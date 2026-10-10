import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Binary search for the attained endpoint of a monotone feasibility test

A fixed number of midpoint tests finds a known cutoff. The number of
tests is logarithmic in the binary upper bound; no values are enumerated.
-/

namespace ContingencyTables.BoundedBinarySearch

abbrev Window := ℕ×ℕ

def midpoint (p : Window) : ℕ := p.1+(p.2-p.1+1)/2

def step (test : ℕ→Bool) (p : Window) : Window :=
  if test (midpoint p) then (midpoint p,p.2) else (p.1,midpoint p-1)

def run (test : ℕ→Bool) : ℕ→Window→Window
  | 0,p => p
  | k+1,p => run test k (step test p)

lemma step_width (test : ℕ→Bool) (p : Window) :
    2*((step test p).2-(step test p).1)≤p.2-p.1 := by
  rcases p with ⟨lo,hi⟩
  unfold step midpoint
  split_ifs <;> dsimp only <;> omega

lemma run_width (test : ℕ→Bool) (k : ℕ) (p : Window) :
    ((run test k p).2-(run test k p).1)*2^k≤p.2-p.1 := by
  induction k generalizing p with
  | zero => simp [run]
  | succ k ih =>
    have h := ih (step test p)
    have hs := step_width test p
    change ((run test k (step test p)).2-(run test k (step test p)).1)*2^(k+1)≤_
    calc
      _ = (((run test k (step test p)).2-(run test k (step test p)).1)*2^k)*2 := by
        rw [pow_succ]
        ring
      _ ≤ ((step test p).2-(step test p).1)*2 := Nat.mul_le_mul_right 2 h
      _ ≤ p.2-p.1 := by simpa only [Nat.mul_comm] using hs

lemma step_contains (test : ℕ→Bool) (K : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (p : Window)
    (hlo : p.1≤K) (hhi : K≤p.2) :
    (step test p).1≤K ∧ K≤(step test p).2 := by
  unfold step
  split_ifs with h
  · exact ⟨(ht _).mp h,hhi⟩
  · have hm : K<midpoint p := by
      by_contra hn
      exact h ((ht _).mpr (by omega))
    exact ⟨hlo,by dsimp only;omega⟩

lemma run_contains (test : ℕ→Bool) (K : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (k : ℕ) (p : Window)
    (hlo : p.1≤K) (hhi : K≤p.2) :
    (run test k p).1≤K ∧ K≤(run test k p).2 := by
  induction k generalizing p with
  | zero => exact ⟨hlo,hhi⟩
  | succ k ih =>
    have hs := step_contains test K ht p hlo hhi
    exact ih (step test p) hs.1 hs.2

theorem run_eq_cutoff (test : ℕ→Bool) (K U k : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (hK : K≤U) (hk : U<2^k) :
    run test k (0,U)=(K,K) := by
  have hb := run_contains test K ht k (0,U) (Nat.zero_le _) hK
  have hw := run_width test k (0,U)
  have hz : (run test k (0,U)).2-(run test k (0,U)).1=0 := by
    simp only [Nat.sub_zero] at hw
    by_contra hn
    have hp : 1≤(run test k (0,U)).2-(run test k (0,U)).1 := by omega
    have hm := Nat.mul_le_mul_right (2^k) hp
    nlinarith
  apply Prod.ext <;> dsimp only <;> omega

def find (test : ℕ→Bool) (U : ℕ) : ℕ :=
  (run test (Nat.clog 2 (U+1)) (0,U)).1

theorem find_eq_cutoff (test : ℕ→Bool) (K U : ℕ)
    (ht : ∀ t,test t=true ↔ t≤K) (hK : K≤U) : find test U=K := by
  have hp : U<2^(Nat.clog 2 (U+1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self U) (Nat.le_pow_clog (by decide) (U+1))
  exact congrArg Prod.fst (run_eq_cutoff test K U (Nat.clog 2 (U+1)) ht hK hp)

end ContingencyTables.BoundedBinarySearch

end OAI
