import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantSupport
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCoprime

namespace OAI

/-! # The bulk Page projection for the actual frequency model -/

namespace Ostmann
open scoped Classical BigOperators

theorem frequencyModel_bulk_page_projection {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (p : I → ℕ) (z : Option PrimitiveRealZero)
    (hp : ∀ i, (p i).Prime ∧ cutoff ≤ p i)
    (hdelete : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i) :
    pageAtModulus (∏ i, bulkResidueModuli (frequencyModelBase S n t ^ (n - 1 + 2)) p i) z =
      pageAtModulus (frequencyModelBase S n t ^ (n - 1 + 2)) z := by
  have h := frequencyModel_page_projection S n V cutoff t hS hcut ∅ p z
    (by simp) hp (by simp) hdelete
  rw [movingArithmeticModuli_product] at h
  simpa only [Fintype.prod_sum_type, bulkResidueModuli, Fintype.prod_unique,
    Finset.prod_empty, one_pow, one_mul, mul_one] using h

end Ostmann

end OAI
