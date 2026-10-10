import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Finset.Nat
import OAI.NumberTheory.Ostmann.Defs

namespace OAI

/-!
# Sets in Ostmann's inverse Goldbach problem

We use `ℕ` for the manuscript's nonnegative integers. The threshold convention
uses `N ≤ n`; changing finitely many initial values does not affect it.
-/

namespace Ostmann

/-- Both prime coverage and exclusion of composite sums beyond one threshold. -/
def EventuallyPrimeSumset (A B : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → (n ∈ sumset A B ↔ n.Prime)

theorem sumset_comm (A B : Set ℕ) : sumset A B = sumset B A := by
  ext n
  simp only [mem_sumset]
  constructor <;> rintro ⟨a, ha, b, hb, hab⟩
  · exact ⟨b, hb, a, ha, (Nat.add_comm b a).trans hab⟩
  · exact ⟨b, hb, a, ha, (Nat.add_comm b a).trans hab⟩

theorem EventuallyPrimeSumset.symm {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) : EventuallyPrimeSumset B A := by
  simpa only [EventuallyPrimeSumset, sumset_comm B A] using h

open scoped symmDiff

/-- The manuscript's finite symmetric difference and threshold formulations agree. -/
theorem finite_symmDiff_iff (A B : Set ℕ) :
    (sumset A B ∆ primes).Finite ↔ EventuallyPrimeSumset A B := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := Set.finite_iff_bddAbove.mp h
    refine ⟨M + 1, ?_⟩
    intro n hn
    have hout : n ∉ sumset A B ∆ primes := by
      intro hin
      have := hM hin
      omega
    simp only [Set.mem_symmDiff, primes, Set.mem_ofPred_eq] at hout
    tauto
  · rintro ⟨N, hN⟩
    apply (Set.finite_Iio N).subset
    intro n hn
    by_contra hlt
    have heq := hN n (Nat.le_of_not_gt hlt)
    simp only [Set.mem_symmDiff, primes, Set.mem_ofPred_eq, heq,
      and_not_self, or_self] at hn

/-- Each sufficiently large sum of elements of the summands is prime. -/
theorem EventuallyPrimeSumset.prime_add {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ a ∈ A, ∀ b ∈ B, N ≤ a + b → (a + b).Prime := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun a ha b hb hab => (hN (a + b) hab).mp ⟨a, ha, b, hb, rfl⟩⟩

/-- The two infinite summands formulation, stated independently of its proof. -/
def TwoInfiniteSummandsImpossible : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → ¬ EventuallyPrimeSumset A B

/-- Ostmann's main statement, including all finite modifications of the primes. -/
def InverseGoldbach : Prop :=
  ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial → (sumset A B ∆ primes).Infinite

end Ostmann

end OAI
