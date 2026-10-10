import Mathlib.Algebra.BigOperators.Associated
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCRT
import OAI.NumberTheory.Ostmann.ZeroDensity.PageConductorProjection

namespace OAI

/-! # The deleted conductor prime removes every spectator Page factor -/

namespace Ostmann
open scoped Classical BigOperators

/-- The prescribed single prime exclusion makes the Page correction depend
only on the frequency block. Multiplicities in that block are retained. -/
theorem bulk_page_projection {I : Type*} [Fintype I]
    (z : Option PrimitiveRealZero) (r cutoff : ℕ) (p : I → ℕ)
    (hr : 0 < r) (hrcutoff : r < cutoff)
    (hp : ∀ i, (p i).Prime) (hlarge : ∀ i, cutoff ≤ p i)
    (hexcluded : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i) :
    pageAtModulus (∏ i, bulkResidueModuli r p i) z = pageAtModulus r z := by
  have hprod : (∏ i, bulkResidueModuli r p i) = r * ∏ i, p i := by
    rw [Fintype.prod_sum_type]
    simp only [bulkResidueModuli, Fintype.prod_unique]
  rw [hprod]
  apply pageAtModulus_mul_eq z r (∏ i, p i) cutoff
  · intro q hq hqr
    exact (Nat.le_of_dvd hr hqr).trans_lt hrcutoff
  · intro q hq hqp
    obtain ⟨i, _, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hqp
    have heq := (Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hqi
    simpa only [heq] using hlarge i
  · intro e he q hq hqp
    obtain ⟨i, _, hqi⟩ := ((deletedConductorPrime_spec hq).1.prime.dvd_finsetProd_iff p).mp hqp
    exact hexcluded e he q hq i
      ((Nat.prime_dvd_prime_iff_eq (deletedConductorPrime_spec hq).1 (hp i)).mp hqi)

end Ostmann

end OAI
