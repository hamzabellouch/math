import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

def primes : Set ℕ := {n | Nat.Prime n}

abbrev sumset (A B : Set ℕ) : Set ℕ := A + B

def EventuallyEqual (S T : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n ∈ S ↔ n ∈ T)

def AsymptoticallyIndecomposable : Prop :=
  ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite ((A + B) ∆ {n : ℕ | Nat.Prime n})

def FiniteModificationIndecomposable : Prop :=
  ∀ S : Set ℕ, (S ∆ primes).Finite →
    ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial → A + B ≠ S

@[simp] theorem mem_primes {n : ℕ} : n ∈ primes ↔ Nat.Prime n := Iff.rfl

@[simp] theorem mem_sumset {A B : Set ℕ} {n : ℕ} :
    n ∈ sumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = n := Set.mem_add

noncomputable def elementsUpTo (A : Set ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (x + 1)).filter (fun n => n ∈ A)

noncomputable def countUpTo (A : Set ℕ) (x : ℕ) : ℕ := (elementsUpTo A x).card

@[simp] theorem mem_elementsUpTo {A : Set ℕ} {x n : ℕ} :
    n ∈ elementsUpTo A x ↔ n ∈ A ∧ n ≤ x := by
  classical
  simp only [elementsUpTo, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, and_comm]

end Ostmann

end OAI
