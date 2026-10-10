import OAI.NumberTheory.JointDickman.Arithmetic.AdditionSieveDensity

namespace OAI

/-! # Sieve majorants for the actual quarter-density product law -/

namespace JointDickman

open Finset

noncomputable def additionSieveWeight (P Z n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Z, residueWeight (additionSieveTheta P p) 0 (n : ZMod p)

theorem additionSieveWeight_nonneg (P Z n : ℕ) : 0 ≤ additionSieveWeight P Z n := by
  apply prod_nonneg
  intro p hp
  exact residueWeight_nonneg _ _ (additionSieveTheta_bounds P (Nat.mem_primesLE.mp hp).2.two_le).1

theorem quarter_primeProductMass_at_product {Q S : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (hS : S ⊆ Q) :
    primeProductMass Q (1 / 4) (∏ p ∈ S, p) =
      primeNormalizer Q (1 / 4) * (∏ p ∈ S, quarterOdds p) / (∏ p ∈ S, p : ℕ) := by
  have hden : ∀ p ∈ Q, 1 - (1 / 4 : ℝ) / p ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hh : (1 / 4 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith only [hp2])
    linarith only [hh]
  rw [primeProductMass_exact (1 / 4) hQ hS hden]
  have hfactor (p : ℕ) : ((1 / 4 : ℝ) / p) / (1 - (1 / 4 : ℝ) / p) = quarterOdds p / p := by
    unfold quarterOdds
    ring
  simp_rw [hfactor]
  rw [prod_div_distrib, ← Nat.cast_prod]
  unfold primeNormalizer
  ring

theorem quarter_product_weight_le_sieve {Q S : Finset ℕ} (P Z : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hS : S ⊆ Q) (hrough : ∀ p ∈ Q, P < p) :
    (∏ p ∈ S, quarterOdds p) ≤ additionSieveWeight P Z (∏ p ∈ S, p) := by
  classical
  let n := ∏ p ∈ S, p
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hQ p (hS hp)
  have hn : n ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hprime p hp).ne_zero
  have hpf : n.primeFactors = S := Nat.primeFactors_prod hprime
  have heq (p : ℕ) (hp : p ∈ Nat.primesLE Z) :
      residueWeight (additionSieveTheta P p) 0 (n : ZMod p) =
        if p ∈ S then quarterOdds p else 1 := by
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hdiv : p ∣ n ↔ p ∈ S := by
      rw [← hpf, Nat.mem_primeFactors]
      simp only [hpp, hn, and_true, true_and, ne_eq, not_false_eq_true]
    by_cases hpS : p ∈ S
    · have hpP : ¬p ≤ P := Nat.not_le.mpr (hrough p (hS hpS))
      simp [residueWeight, ZMod.natCast_eq_zero_iff, hdiv, hpS, additionSieveTheta, hpP]
    · simp [residueWeight, ZMod.natCast_eq_zero_iff, hdiv, hpS]
  have hsubset : (Nat.primesLE Z).filter (fun p => p ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
  have hprod := prod_le_prod_of_subset_of_le_one₀ hsubset
    (fun p hp => (quarterOdds_bounds (hprime p hp).two_le).1)
    (fun p hp _ => (quarterOdds_bounds (hprime p hp).two_le).2)
  unfold additionSieveWeight
  change _ ≤ ∏ p ∈ Nat.primesLE Z, residueWeight (additionSieveTheta P p) 0 (n : ZMod p)
  rw [prod_congr rfl heq]
  rw [← prod_filter]
  exact hprod

theorem quarter_primeProductMass_le_sieve {Q : Finset ℕ} (P Z n : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hrough : ∀ p ∈ Q, P < p) :
    primeProductMass Q (1 / 4) n ≤
      primeNormalizer Q (1 / 4) / n * additionSieveWeight P Z n := by
  classical
  by_cases hs : n ∈ Q.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hS, rfl⟩ := mem_image.mp hs
    have hSQ := mem_powerset.mp hS
    rw [quarter_primeProductMass_at_product hQ hSQ]
    have hQ0 := (primeNormalizer_bounds Q hQ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)).1
    calc
      _ = (primeNormalizer Q (1 / 4) / (∏ p ∈ S, p : ℕ)) * (∏ p ∈ S, quarterOdds p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (quarter_product_weight_le_sieve P Z hQ hSQ hrough)
        (div_nonneg hQ0 (Nat.cast_nonneg _))
  · rw [primeProductMass_eq_zero (1 / 4) n hs]
    exact mul_nonneg (div_nonneg
      (primeNormalizer_bounds Q hQ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)).1
      (Nat.cast_nonneg n)) (additionSieveWeight_nonneg P Z n)

end JointDickman

end OAI
