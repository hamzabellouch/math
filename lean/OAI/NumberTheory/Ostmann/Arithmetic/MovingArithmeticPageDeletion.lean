import Mathlib.Algebra.BigOperators.Associated
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPageCRT

namespace OAI

/-! # The prescribed conductor deletion confines Page to the frequency block -/

namespace Ostmann
open scoped Classical BigOperators

theorem pageAtModulus_movingArithmeticFactors {I : Type*}
    (z : Option PrimitiveRealZero) (r : ℕ) (q : I → ℕ) (P : Finset ℕ) (S : Finset I)
    (cutoff : ℕ) (hP : ∀ p ∈ P, p.Prime ∧ cutoff ≤ p)
    (hS : ∀ i ∈ S, (q i).Prime ∧ cutoff ≤ q i)
    (hexcluded : ∀ e, z = some e → ∀ p,
      deletedConductorPrime e.modulus cutoff = some p →
        ¬p ∣ ∏ b, movingArithmeticModuli r q P S b) :
    pageAtModulus (∏ b, movingArithmeticModuli r q P S b) z = pageAtModulus r z := by
  let C := (∏ p ∈ P, p) ^ 2 * ∏ i ∈ S, q i
  have hprod : (∏ b, movingArithmeticModuli r q P S b) = C * r := by
    rw [movingArithmeticModuli_product]
    exact Nat.mul_comm _ _
  have hlarge : ∀ p, p.Prime → p ∣ C → cutoff ≤ p := by
    intro p hp hd
    rcases hp.dvd_mul.mp hd with hl | hr
    · obtain ⟨t, ht, hpt⟩ := (hp.prime.dvd_finsetProd_iff (fun t : ℕ => t)).mp
        (hp.dvd_of_dvd_pow hl)
      have heq := (Nat.prime_dvd_prime_iff_eq hp (hP t ht).1).mp hpt
      simpa only [heq] using (hP t ht).2
    · obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff q).mp hr
      have heq := (Nat.prime_dvd_prime_iff_eq hp (hS i hi).1).mp hpi
      simpa only [heq] using (hS i hi).2
  rw [hprod]
  apply pageAtModulus_regular_factor z C r cutoff hlarge
  intro e he p hdel hd
  exact hexcluded e he p hdel (hprod.symm ▸ hd)

end Ostmann

end OAI
