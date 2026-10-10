import OAI.NumberTheory.JointDickman.Probability.GraphResidueMajorant
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryOdds

namespace OAI

/-! # Uniform normalization after discarding the coefficient primes -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graph_selected_odds_bound :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (10*(B : ℝ)) →
      (∏ p ∈ S, (1-(1/2 : ℝ)/p)⁻¹) ≤ Real.exp 1 := by
  have ht : Tendsto (fun B : ℕ => (20/Real.log 2)*
      ((B : ℝ)/(auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have h := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (20/Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using h
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hS hp)
  have hcut : ∀ p ∈ S, (auxiliaryCutoff B : ℝ) ≤ p :=
    fun p hp => (mem_filter.mp (hS hp)).2.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ 10*B/Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  apply (inverseSelectedPrimeOdds_le hP (by norm_num) (by norm_num) S hprime hcut).trans
  apply Real.exp_le_exp.mpr
  calc
    2*(S.card : ℝ)/auxiliaryCutoff B ≤ 2*(10*B/Real.log 2)/auxiliaryCutoff B :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hP.le
    _ = (20/Real.log 2)*((B : ℝ)/auxiliaryCutoff B) := by ring
    _ ≤ 1 := hsmall.le

theorem three_root_product_le_half_cube (G : Finset ℕ)
    (hG : ∀ p ∈ G, p.Prime) :
    (∏ p ∈ G, (1-3/(2*(p : ℝ)))) ≤ (primeNormalizer G (1/2))^3 := by
  unfold primeNormalizer
  rw [← prod_pow]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hG p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have h : (3 : ℝ)/(2*p) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hG p hp).two_le
    have hx : 0 ≤ (1/2 : ℝ)/p := by positivity
    have hx1 : (1/2 : ℝ)/p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hh := mul_nonneg (sq_nonneg ((1/2 : ℝ)/p)) (show 0 ≤ 3-(1/2 : ℝ)/p by linarith)
    have he : (3 : ℝ)/(2*p) = 3*((1/2 : ℝ)/p) := by ring
    rw [he]
    nlinarith

theorem primeNormalizer_sdiff {P S : Finset ℕ} (hS : S ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNormalizer (P\S) (1/2) = primeNormalizer P (1/2) *
      ∏ p ∈ S, (1-(1/2 : ℝ)/p)⁻¹ := by
  have hp (p : ℕ) (hp : p ∈ S) : (1-(1/2 : ℝ)/p) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (hS hp)).two_le
    have hd : (1/2 : ℝ)/p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  unfold primeNormalizer
  rw [← prod_sdiff hS (f := fun p : ℕ => 1-(1/2 : ℝ)/p), prod_inv_distrib]
  rw [mul_assoc, mul_inv_cancel₀ (prod_ne_zero_iff.mpr hp), mul_one]

/-- This is uniform in the later regularity cutoff. Only Mertens' cited
reciprocal-prime input is used for the normalization. -/
theorem graph_three_root_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (10*(B : ℝ)) →
      (auxiliaryRatio B^(1/2 : ℝ))^3 *
        (∏ p ∈ auxiliaryPrimes B\S, (1-3/(2*(p : ℝ)))) ≤ K := by
  let C : ℝ := (4 : ℝ)^(-(1/2 : ℝ))+1
  have hC : 0 < C := by unfold C; positivity
  refine ⟨(C*Real.exp 1)^3, by positivity, ?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1/2) (by norm_num) (by norm_num)
  filter_upwards [graph_selected_odds_bound,
    ht.eventually (Iio_mem_nhds (show (4 : ℝ)^(-(1/2 : ℝ)) < C by dsimp [C]; linarith)),
    eventually_gt_atTop 1] with B hS hnorm hB
  intro S hSP hprod
  have hR := (auxiliaryRatio_pos hB).le
  have hq := (primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).1
  have hsmall : primeNormalizer (auxiliaryPrimes B\S) (1/2) *
      auxiliaryRatio B^(1/2 : ℝ) ≤ C*Real.exp 1 := by
    rw [primeNormalizer_sdiff hSP (auxiliaryPrimes_prime B), mul_right_comm]
    exact mul_le_mul hnorm.le (hS S hSP hprod)
      (prod_nonneg (fun p hp => by
        have hp0 := (primeNormalizer_bounds {p} (by simpa using auxiliaryPrimes_prime B p (hSP hp))
          (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).1
        simpa only [primeNormalizer, prod_singleton] using inv_nonneg.mpr hp0)) hC.le
  calc
    _ ≤ (auxiliaryRatio B^(1/2 : ℝ))^3 *
        (primeNormalizer (auxiliaryPrimes B\S) (1/2))^3 :=
      mul_le_mul_of_nonneg_left (three_root_product_le_half_cube _
        (fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1)) (by positivity)
    _ = (primeNormalizer (auxiliaryPrimes B\S) (1/2)*
        auxiliaryRatio B^(1/2 : ℝ))^3 := by ring
    _ ≤ (C*Real.exp 1)^3 := pow_le_pow_left₀
      (mul_nonneg (primeNormalizer_bounds _
        (fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1)
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).1
        (Real.rpow_nonneg hR _)) hsmall 3

end JointDickman

end OAI
