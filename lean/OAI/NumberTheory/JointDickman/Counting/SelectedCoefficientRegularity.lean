import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairPushforward
import OAI.NumberTheory.JointDickman.Counting.CoefficientEventBound

namespace OAI

/-! # Regularity and integer products of selected prime sets -/

namespace JointDickman

open Finset

theorem coefficientPrimeSet_at_product {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    coefficientPrimeSet B (∏ p ∈ A, p) = A := by
  have hprime : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hnonzero : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hprime p hp).ne_zero
  have hpf := Nat.primeFactors_prod hprime
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpd⟩ := mem_filter.mp hp
    have hh := Nat.mem_primeFactors.mpr ⟨auxiliaryPrimes_prime B p hpP, hpd, hnonzero⟩
    rwa [hpf] at hh
  · intro hp
    have hh : p ∈ (∏ p ∈ A, p).primeFactors := by rwa [hpf]
    exact mem_filter.mpr ⟨hA hp, (Nat.mem_primeFactors.mp hh).2.1⟩

open Classical in
theorem coefficientPairFailureMass_selected_sum (B L T : ℕ) (τ C : ℝ) :
    (∑ ac ∈ amplificationCoefficientPairs B T, coefficientPairFailureMass B L τ C ac.1 ac.2) =
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T then
          if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D then 0 else
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
              bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D
        else 0 := by
  let f : ℕ × ℕ → ℝ := fun ac =>
    if RegularPrimeSet B L τ C (coefficientPrimeSet B ac.1) ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B ac.2) then 0 else 1
  have h := primeProductPair_weighted_sum (auxiliaryPrimes B) (1 / 2)
    (amplificationCoefficientPairs B T) f
  have heq : (∑ ac ∈ amplificationCoefficientPairs B T, coefficientPairFailureMass B L τ C ac.1 ac.2) =
      ∑ ac ∈ amplificationCoefficientPairs B T,
        f ac * (primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) := by
    apply sum_congr rfl
    intro ac _
    dsimp [coefficientPairFailureMass, f]
    split_ifs <;> simp only [zero_mul, one_mul]
  rw [heq, h]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  dsimp only [f]
  rw [coefficientPrimeSet_at_product (mem_powerset.mp hA),
    coefficientPrimeSet_at_product (mem_powerset.mp hD)]
  split_ifs <;> simp only [zero_mul, one_mul]

end JointDickman

end OAI
