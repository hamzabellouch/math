import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace OAI

/-! # Formal products and the smaller period of a repeated prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def sampledPrimeSet {I : Type*} [Fintype I] (p : I → ℕ) : Finset ℕ :=
  Finset.univ.image p

noncomputable def primeSlotCount {I : Type*} [Fintype I] (p : I → ℕ) (q : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => p i = q)).card

theorem primeSlotCount_pos {I : Type*} [Fintype I] (p : I → ℕ) {q : ℕ}
    (hq : q ∈ sampledPrimeSet p) : 0 < primeSlotCount p q := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

theorem primeSlotCount_sum {I : Type*} [Fintype I] (p : I → ℕ) :
    (∑ q ∈ sampledPrimeSet p, primeSlotCount p q) = Fintype.card I := by
  simpa only [primeSlotCount, Finset.card_univ] using
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := sampledPrimeSet p)
      (f := p) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)).symm

theorem formal_prime_product {I : Type*} [Fintype I] (p : I → ℕ) :
    (∏ i, p i) = ∏ q ∈ sampledPrimeSet p, q ^ primeSlotCount p q := by
  simpa only [primeSlotCount, Finset.prod_const] using
    (Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := sampledPrimeSet p)
      (g := p) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun q => q)).symm

theorem all_multiple_prime_count {I : Type*} [Fintype I] (p : I → ℕ)
    (hm : ∀ q ∈ sampledPrimeSet p, 2 ≤ primeSlotCount p q) :
    2 * (sampledPrimeSet p).card ≤ Fintype.card I := by
  have h := Finset.sum_le_sum hm
  simpa only [Finset.sum_const, smul_eq_mul, primeSlotCount_sum, mul_comm] using h

/-- A repeated label removes at least that prime from the formal period.
This is the period saving used before bandlimited Poisson summation. -/
theorem repeated_prime_period_bound {I : Type*} [Fintype I] (p : I → ℕ)
    (hp : ∀ i, 1 ≤ p i) {q : ℕ} (hq : q ∈ sampledPrimeSet p)
    (hm : 2 ≤ primeSlotCount p q) :
    q * (∏ r ∈ sampledPrimeSet p, r) ≤ ∏ i, p i := by
  have hr1 (r : ℕ) (hr : r ∈ sampledPrimeSet p) : 1 ≤ r := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact hp i
  have hbase (r : ℕ) (hr : r ∈ (sampledPrimeSet p).erase q) :
      r ≤ r ^ primeSlotCount p r := by
    simpa only [pow_one] using Nat.pow_le_pow_right (hr1 r (Finset.mem_of_mem_erase hr))
      (primeSlotCount_pos p (Finset.mem_of_mem_erase hr))
  rw [formal_prime_product, ← Finset.mul_prod_erase (sampledPrimeSet p) (fun r => r) hq,
    ← Finset.mul_prod_erase (sampledPrimeSet p) (fun r => r ^ primeSlotCount p r) hq]
  calc
    q * (q * ∏ r ∈ (sampledPrimeSet p).erase q, r) =
        q ^ 2 * ∏ r ∈ (sampledPrimeSet p).erase q, r := by ring
    _ ≤ q ^ primeSlotCount p q * ∏ r ∈ (sampledPrimeSet p).erase q, r ^ primeSlotCount p r :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (hr1 q hq) hm) (Finset.prod_le_prod hbase)

end Ostmann

end OAI
