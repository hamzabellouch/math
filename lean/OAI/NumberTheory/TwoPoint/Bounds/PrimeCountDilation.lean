import OAI.NumberTheory.TwoPoint.Bounds.FourierPrimeCutoff

namespace OAI

/-! Extracting `x=u*z` from the core-prime cutoff. Primes excluded because
they divide `u` do not reappear in the count, even at exceptional integers
where the multiplicative functions themselves cannot yet be factored. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma finitePrimeDivisorCount_mul_of_avoids (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (u n : ℕ) (hu : ∀ p ∈ P, ¬p ∣ u) :
    finitePrimeDivisorCount P (u * n) = finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  apply sum_congr rfl
  intro p hp
  simp only [(hP p hp).dvd_mul, hu p hp, false_or]

lemma finitePrimeDivisorCount_filter_mul (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (u n : ℕ) :
    finitePrimeDivisorCount (C.filter (fun p => ¬p ∣ u)) (u * n) =
      finitePrimeDivisorCount (C.filter (fun p => ¬p ∣ u)) n := by
  apply finitePrimeDivisorCount_mul_of_avoids
  · intro p hp
    exact hC p (mem_filter.mp hp).1
  · intro p hp
    exact (mem_filter.mp hp).2

/-- The expanded divisor `d` and retained divisor `u` have the same core
prime factors, so the core cutoff depends only on the reduced variable. -/
lemma finitePrimeDivisorCount_same_core_factors (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (d u n : ℕ)
    (hcore : ∀ p ∈ C, p ∣ d ↔ p ∣ u) :
    finitePrimeDivisorCount (C.filter (fun p => ¬p ∣ d)) (u * n) =
      finitePrimeDivisorCount (C.filter (fun p => ¬p ∣ u)) n := by
  have heq : C.filter (fun p => ¬p ∣ d) = C.filter (fun p => ¬p ∣ u) := by
    ext p
    by_cases hp : p ∈ C
    · simp only [mem_filter, hp, true_and, hcore p hp]
    · simp only [mem_filter, hp, false_and]
  rw [heq, finitePrimeDivisorCount_filter_mul C hC u n]

lemma primeCountCutoff_same_core_factors (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (d u n : ℕ)
    (hcore : ∀ p ∈ C, p ∣ d ↔ p ∣ u) (μ σ : ℝ) (w : ℝ → ℂ) :
    primeCountCutoff (C.filter (fun p => ¬p ∣ d)) μ σ w (u * n) =
      primeCountCutoff (C.filter (fun p => ¬p ∣ u)) μ σ w n := by
  rw [primeCountCutoff_eq_fourierInv, primeCountCutoff_eq_fourierInv,
    finitePrimeDivisorCount_same_core_factors C hC d u n hcore]

end TwoPointCorrelations

end OAI
