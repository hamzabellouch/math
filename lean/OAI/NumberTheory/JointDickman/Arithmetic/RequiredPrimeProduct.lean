import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset

namespace OAI

/-! # Availability of a prescribed coefficient at an independent endpoint -/

namespace JointDickman
open Finset

def PrimeProductAvailable (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A ⊆ S, (∏ p ∈ A, p) = n

open Classical in
/-- A prescribed integer is available with probability 1/n if it is a
squarefree product of the allowed primes, and probability zero otherwise. -/
theorem independent_site_available_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∑ S ∈ P.powerset, if PrimeProductAvailable n S then
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S else 0) ≤ 1/(n : ℝ) := by
  by_cases hav : ∃ A ⊆ P, (∏ p ∈ A, p) = n
  · obtain ⟨A,hAP,hAn⟩ := hav
    have he (S : Finset ℕ) (hS : S ⊆ P) : PrimeProductAvailable n S ↔ A ⊆ S := by
      constructor
      · rintro ⟨R,hRS,hRn⟩
        have hr : R = A := primeProduct_injective hP (hRS.trans hS) hAP (hRn.trans hAn.symm)
        simpa only [hr] using hRS
      · intro hAS
        exact ⟨A,hAS,hAn⟩
    calc
      _ = ∑ S ∈ P.powerset, if A ⊆ S then
          bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S else 0 := by
        apply sum_congr rfl
        intro S hS
        simp only [he S (mem_powerset.mp hS)]
      _ = 1/(n : ℝ) := by rw [independent_site_contains_prime_product P A hAP,hAn]
      _ ≤ _ := le_rfl
  · have he (S : Finset ℕ) (hS : S ⊆ P) : ¬PrimeProductAvailable n S := by
      rintro ⟨A,hAS,hAn⟩
      exact hav ⟨A,hAS.trans hS,hAn⟩
    have hz : (∑ S ∈ P.powerset, if PrimeProductAvailable n S then
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S else 0) = 0 := by
      apply sum_eq_zero
      intro S hS
      simp only [he S (mem_powerset.mp hS),ite_false]
    rw [hz]
    positivity

open Classical in
theorem independent_site_large_available_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} {X : ℝ} (hX : 0 < X) (hn : X ≤ (n : ℝ)) :
    (∑ S ∈ P.powerset, if PrimeProductAvailable n S then
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S else 0) ≤ 1/X :=
  (independent_site_available_le P hP n).trans (one_div_le_one_div_of_le hX hn)

end JointDickman

end OAI
