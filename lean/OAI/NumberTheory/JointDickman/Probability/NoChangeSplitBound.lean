import OAI.NumberTheory.JointDickman.Probability.RegularOrientedSplit

namespace OAI

/-! # The no-change part of the amplification second moment -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem highPrimePart_at_cutoff {B : ℕ} {A : Finset ℕ} (hB : 1 < B)
    (hA : A ⊆ auxiliaryPrimes B) : highPrimePart (Real.log (auxiliaryCutoff B)) A = A := by
  classical
  apply filter_eq_self.mpr
  intro p hp
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt hB) 1000
  exact Real.log_lt_log hP0 (mem_filter.mp (hA hp)).2

/-- All second assignments agree with the first assignments, retaining the
necessary lower tail restrictions on the two remaining sets. -/
noncomputable def noChangeSplitMass (B : ℕ) (A D : Finset ℕ) (C : ℝ) : ℝ :=
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C
  (1 / 2 : ℝ)^A.card * (1 / 2 : ℝ)^D.card *
    (highNoAdditionMass (auxiliaryPrimes B) (remainingPrimeParameter D) k *
      highNoAdditionMass (auxiliaryPrimes B) (remainingPrimeParameter A) k)

theorem regular_no_change_split_bound {B L : ℕ} {A D : Finset ℕ} {τ C : ℝ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hAr : RegularPrimeSet B L τ C A) (hDr : RegularPrimeSet B L τ C D) :
    noChangeSplitMass B A D C ≤ (2 : ℝ)^(4 * C) * (auxiliaryRatio B)^(-amplificationExponent) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hY0 : 0 < Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C
  have ha : k ≤ (A.card : ℝ) := by
    have hh := hAr.2 0
    simp only [primeTailEndpoint, pow_zero, one_mul] at hh
    change k ≤ (highPrimePart (Real.log (auxiliaryCutoff B)) A).card at hh
    rwa [highPrimePart_at_cutoff hB hA] at hh
  have hd : k ≤ (D.card : ℝ) := by
    have hh := hDr.2 0
    simp only [primeTailEndpoint, pow_zero, one_mul] at hh
    change k ≤ (highPrimePart (Real.log (auxiliaryCutoff B)) D).card at hh
    rwa [highPrimePart_at_cutoff hB hD] at hh
  have hparam (S : Finset ℕ) : ∀ p ∈ auxiliaryPrimes B,
      0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc S (auxiliaryPrimes_prime B p hp).two_le
  have hh := high_coin_four_factor_bound hB0 hY0 ha hd
    (highNoAdditionMass_nonneg _ _ k (hparam D))
    (highNoAdditionMass_nonneg _ _ k (hparam A))
    (remaining_high_no_addition_bound _ _ k (hparam D))
    (remaining_high_no_addition_bound _ _ k (hparam A))
  have heq : Real.log (auxiliaryCutoff B) / (B : ℝ) = (auxiliaryRatio B)⁻¹ := by
    rw [log_auxiliaryCutoff, auxiliaryRatio, inv_div]
  rw [heq, ← Real.rpow_neg_eq_inv_rpow] at hh
  exact hh

/-- Uniform vanishing after the extra factor B needed in the second moment. -/
theorem regular_no_change_vanishing (L : ℕ) (τ C : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℕ in atTop, ∀ A D : Finset ℕ,
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      (B : ℝ) * noChangeSplitMass B A D C ≤ ε := by
  intro ε hε
  have ht := amplification_no_change_tendsto.const_mul ((2 : ℝ)^(4 * C))
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (eventually_le_nhds hε), eventually_gt_atTop 1] with B hb hB
  intro A D hA hD hAr hDr
  have hh := mul_le_mul_of_nonneg_left (regular_no_change_split_bound hB hA hD hAr hDr)
    (Nat.cast_nonneg B)
  calc
    _ ≤ (2 : ℝ)^(4 * C) * ((B : ℝ) * (auxiliaryRatio B)^(-amplificationExponent)) := by
      convert hh using 1; ring
    _ ≤ ε := hb

end JointDickman

end OAI
