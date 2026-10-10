import OAI.NumberTheory.JointDickman.Counting.CoefficientPairMajorant
import OAI.NumberTheory.JointDickman.Amplification.TwoFormSubtraction
import OAI.NumberTheory.JointDickman.Counting.TiltedCoefficient
import OAI.NumberTheory.JointDickman.Amplification.IntervalRemainder

namespace OAI

/-! # Fixed-endpoint coefficient estimates for the decreasing form -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem coefficient_pair_sub_le_good_primes (B Z b j n : ℕ) :
    coefficientWeight B n * coefficientWeight B (b - j * n) ≤ coefficientScale B ^ 2 *
      ∏ p ∈ goodSievePrimes Z j b, residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 (n : ZMod p) *
        residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 ((b : ZMod p) - j * n) := by
  classical
  by_cases hn : j*n ≤ b
  ·
      let f := fun p => residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 (n : ZMod p) *
        residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 ((b : ZMod p) - j * n)
      have hf0 (p : ℕ) : 0 ≤ f p := mul_nonneg
        (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1)
        (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1)
      have hf1 (p : ℕ) : f p ≤ 1 := by
        have h := mul_le_mul (residueWeight_le_one (0 : ZMod p) n (roughSieveTheta_bounds (auxiliaryCutoff B) p).2)
          (residueWeight_le_one (0 : ZMod p) ((b : ZMod p) - j * n) (roughSieveTheta_bounds (auxiliaryCutoff B) p).2)
          (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1) zero_le_one
        simpa only [mul_one] using h
      have hprod : (∏ p ∈ sievePrimes Z, f p) ≤ ∏ p ∈ goodSievePrimes Z j b, f p :=
        prod_le_prod_of_subset_of_le_one₀ (filter_subset _ _) (fun p _ => hf0 p) (fun p _ _ => hf1 p)
      calc
        _ ≤ (coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z n) *
            (coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z (b - j * n)) :=
          mul_le_mul (coefficientWeight_le_sieved B Z n) (coefficientWeight_le_sieved B Z (b - j * n))
            (coefficientWeight_nonneg _ _) (mul_nonneg (coefficientScale_nonneg _) (sievedCoefficientWeight_nonneg _ _ _))
        _ = coefficientScale B ^ 2 * ∏ p ∈ sievePrimes Z, f p := by
          simp only [sievedCoefficientWeight, f, prod_mul_distrib, Nat.cast_sub hn, Nat.cast_mul]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
  · rw [Nat.sub_eq_zero_of_le (by omega : b ≤ j*n),coefficientWeight_zero,mul_zero]
    apply mul_nonneg (sq_nonneg _)
    exact prod_nonneg (fun p _ => mul_nonneg
      (residueWeight_nonneg _ _ (roughSieveTheta_bounds _ p).1)
      (residueWeight_nonneg _ _ (roughSieveTheta_bounds _ p).1))

theorem coefficient_two_form_sub_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ j b u v : ℕ,
      j ≠ 0 → b ≠ 0 → (b : ℝ) ≤ Real.exp (κ * B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      u ≤ v → Real.exp (δ * B) ≤ (v : ℝ) - u →
      (∑ n ∈ Ico u v, coefficientWeight B n * coefficientWeight B (b - j * n)) ≤
        C * ((v : ℝ) - u) * singularFactor 24 j := by
  classical
  obtain ⟨C, hC, hsieve⟩ := two_form_interval_sieve_sub hFord hM
  obtain ⟨M, hM0, hnorm⟩ := coefficient_sieve_density_bound hM
    (by linarith : 0 < (δ / 8) / 2)
  refine ⟨C * M ^ 2 * Real.exp 1 + 1, by positivity, ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    good_sieve_density_bound κ, coefficient_interval_remainder_small hδ,
    eventually_gt_atTop 1] with B hcut hgood herror hB
  intro j b u v hj hb hbsize hbrough huv hL
  let Z := sieveCutoff (δ / 8) B
  let P := goodSievePrimes Z j b
  let θ := roughSieveTheta (auxiliaryCutoff B)
  have hP (p : ℕ) (hp : p ∈ P) :
      p.Prime ∧ p ≤ Z ∧ 4 ≤ p ∧ ¬p ∣ j ∧ ¬p ∣ b := by
    obtain ⟨hpS, hpj, hpb⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hpS
    obtain ⟨hpZ, hpp⟩ := Nat.mem_primesLE.mp hpZ
    exact ⟨hpp, hpZ, by omega, hpj, hpb⟩
  have hs := hsieve P θ j b u v Z huv hcut.1 hP (fun p _ => roughSieveTheta_bounds _ p)
  have hg := hgood Z j b hj hb hbsize hbrough
  have hn := hnorm B Z hB hcut.2.1 hcut.2.2.1
  have hL0 : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hS0 : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  have hscaled : coefficientScale B ^ 2 * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 ≤
      M ^ 2 * singularFactor 24 j * Real.exp 1 := by
    calc
      _ ≤ coefficientScale B ^ 2 *
          (roughSieveDensity (auxiliaryCutoff B) Z ^ 2 * singularFactor 24 j * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hg (sq_nonneg _)
      _ = (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) ^ 2 *
          singularFactor 24 j * Real.exp 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (coefficientScale_nonneg B) (roughSieveDensity_nonneg _ _)) hn 2) hS0)
        (Real.exp_pos _).le
  have herr := herror ((v : ℝ) - u) hL
  calc
    _ ≤ ∑ n ∈ Ico u v, coefficientScale B ^ 2 *
        ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) *
          residueWeight (θ p) 0 ((b : ZMod p) - j * n) :=
      sum_le_sum (fun n _ => coefficient_pair_sub_le_good_primes B Z b j n)
    _ = coefficientScale B ^ 2 * (∑ n ∈ Ico u v,
        ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) *
          residueWeight (θ p) 0 ((b : ZMod p) - j * n)) := by rw [mul_sum]
    _ ≤ coefficientScale B ^ 2 *
        (C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 +
          2 * (Z + 1 : ℝ) * (Z : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ ≤ C * ((v : ℝ) - u) * (M ^ 2 * singularFactor 24 j * Real.exp 1) + ((v : ℝ) - u) := by
      rw [mul_add]
      apply add_le_add (b := C * ((v : ℝ) - u) * (M ^ 2 * singularFactor 24 j * Real.exp 1)) ?_ herr
      calc
        _ = C * ((v : ℝ) - u) * (coefficientScale B ^ 2 * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (mul_nonneg hC.le hL0)
    _ ≤ C * ((v : ℝ) - u) * (M ^ 2 * singularFactor 24 j * Real.exp 1) +
        ((v : ℝ) - u) * singularFactor 24 j :=
      add_le_add le_rfl (le_mul_of_one_le_right hL0 (singularFactor_one_le (by norm_num) j))
    _ = _ := by ring

end JointDickman

end OAI
