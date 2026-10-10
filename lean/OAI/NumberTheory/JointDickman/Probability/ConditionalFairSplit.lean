import OAI.NumberTheory.JointDickman.Arithmetic.ConditionalPrimeParameters

namespace OAI

/-! # Exact conditional law of the remaining half of a prime site -/

namespace JointDickman

open Finset

private theorem subsetMass_prod_ite {P S : Finset ℕ} (hS : S ⊆ P) (q : ℕ → ℝ) :
    bernoulliSubsetMass P q S = ∏ p ∈ P, if p ∈ S then q p else 1 - q p := by
  classical
  rw [prod_ite]
  have hyes : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : P.filter (fun p => p ∉ S) = P \ S := by ext p; simp
  rw [hyes, hno]
  rfl

private theorem subsetMass_tilt_product {P S : Finset ℕ} (hS : S ⊆ P) (q v : ℕ → ℝ) :
    bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, if p ∈ S then q p * v p else 1 - q p := by
  classical
  rw [prod_ite]
  have hyes : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : P.filter (fun p => p ∉ S) = P \ S := by ext p; simp
  rw [hyes, hno, prod_mul_distrib]
  unfold bernoulliSubsetMass
  ring

open Classical in
/-- A site is sampled at density 1/p and split by fair coins; A and R are
its selected and remaining prime sets. -/
noncomputable def fairSelectedRemainingMass (P A R : Finset ℕ) : ℝ :=
  if Disjoint A R then
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) (A ∪ R) * (1 / 2 : ℝ)^(A ∪ R).card
  else 0

/-- The exact joint mass factors into the selected marginal and the
independent remaining indicators, including the zero probabilities at A. -/
theorem fairSelectedRemainingMass_factor {P A R : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hR : R ⊆ P) :
    fairSelectedRemainingMass P A R =
      bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
      bernoulliSubsetMass P (remainingPrimeParameter A) R := by
  classical
  by_cases hd : Disjoint A R
  · rw [fairSelectedRemainingMass, ite_eq_left hd,
      show (1 / 2 : ℝ)^(A ∪ R).card = ∏ _p ∈ A ∪ R, (1 / 2 : ℝ) by simp,
      subsetMass_tilt_product (union_subset hA hR), subsetMass_prod_ite hA,
      subsetMass_prod_ite hR, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hden : 2 * (p : ℝ) - 1 ≠ 0 := by linarith only [hp2]
    have hden' : -1 + (p : ℝ) * 2 ≠ 0 := by linarith only [hp2]
    by_cases ha : p ∈ A <;> by_cases hr : p ∈ R
    · exact False.elim ((disjoint_left.mp hd) ha hr)
    · simp only [mem_union, ha, hr, true_or, ite_true, ite_false, remainingPrimeParameter]
      ring
    · simp only [mem_union, ha, hr, false_or, ite_true, ite_false, remainingPrimeParameter]
      field_simp [hp0, hden, hden']
      linear_combination - (mul_inv_cancel₀ hden')
    · simp only [mem_union, ha, hr, false_or, ite_false, remainingPrimeParameter]
      field_simp [hp0, hden, hden']
      linear_combination mul_inv_cancel₀ hden'
  · rw [fairSelectedRemainingMass, ite_eq_right hd]
    obtain ⟨p, hpA, hpR⟩ := not_disjoint_iff.mp hd
    have hzero : bernoulliSubsetMass P (remainingPrimeParameter A) R = 0 := by
      unfold bernoulliSubsetMass
      have hz : (∏ p ∈ R, remainingPrimeParameter A p) = 0 := by
        apply prod_eq_zero hpR
        simp only [remainingPrimeParameter, hpA, ite_true]
      rw [hz, zero_mul]
    rw [hzero, mul_zero]

open Classical in
/-- Summing the exact joint split mass over nonregular remainders gives the
selected marginal times the failure probability proved above. -/
theorem fairSelectedRemainingMass_bad (B L : ℕ) (τ C : ℝ) {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    (∑ R ∈ (auxiliaryPrimes B).powerset,
      if RegularPrimeSet B L τ C R then 0 else fairSelectedRemainingMass (auxiliaryPrimes B) A R) =
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
        primeRegularityFailureProbability B L τ C (remainingPrimeParameter A) := by
  classical
  unfold primeRegularityFailureProbability
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  have hP : ∀ p ∈ auxiliaryPrimes B, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  rw [fairSelectedRemainingMass_factor hP hA (mem_powerset.mp hR)]
  split_ifs <;> simp only [mul_zero]

end JointDickman

end OAI
