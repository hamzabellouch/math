import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallPositiveQuadratic
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetProducts

namespace OAI

/-! # Divisor sums of the actual squarefree prime-set modulus -/

namespace Ostmann

open scoped BigOperators

theorem primeSet_modulus_squarefree (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Squarefree Q.toList.prod := by
  simpa using primeSubset_product_squarefree Q hQ

theorem sum_primeSet_divisors (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (f : ℕ → ℂ) :
    (∑ d ∈ Q.toList.prod.divisors, f d) = ∑ U ∈ Q.powerset, f U.toList.prod := by
  classical
  have hQpos : 0 < Q.toList.prod := prime_list_prod_pos _ (primeSet_list_prime Q hQ)
  have hQsf := primeSet_modulus_squarefree Q hQ
  symm
  apply Finset.sum_bij (fun U _ => U.toList.prod)
  · intro U hU
    exact Nat.mem_divisors.mpr ⟨primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU), hQpos.ne'⟩
  · intro U hU V hV huv
    apply primeSubset_product_injective Q hQ (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV)
    simpa using huv
  · intro d hd
    have hdQ := (Nat.mem_divisors.mp hd).1
    have hdsf : Squarefree d := hQsf.squarefree_of_dvd hdQ
    have hsub : d.primeFactors ⊆ Q := by
      intro p hp
      rw [← primeSet_modulus_primeFactors Q hQ]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdQ, hQpos.ne'⟩
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr hsub, ?_⟩
    simpa using Nat.prod_primeFactors_of_squarefree hdsf
  · intro U _
    rfl

end Ostmann

end OAI
