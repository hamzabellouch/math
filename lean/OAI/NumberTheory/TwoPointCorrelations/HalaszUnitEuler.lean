import OAI.NumberTheory.TwoPointCorrelations.HalaszUnitCorrection
import OAI.NumberTheory.TwoPointCorrelations.HalaszNearDiscrepancy
import Mathlib.NumberTheory.EulerProduct.Basic

namespace OAI

/-! Absolute Euler control of the constant-one convolution correction.
The first-order exponent is the actual prime discrepancy. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszUnitReciprocal (F : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖mrtArithmetic (halaszUnitCorrection F) n‖ / (n : ℝ)

lemma halasz_unit_reciprocal_nonneg (F : ℕ → ℂ) (n : ℕ) :
    0 ≤ halaszUnitReciprocal F n := by unfold halaszUnitReciprocal; positivity

lemma halasz_unit_reciprocal_one (F : ℕ → ℂ) : halaszUnitReciprocal F 1 = 1 := by
  simp [halaszUnitReciprocal, halaszUnitCorrection, mrtArithmetic]

lemma halasz_unit_reciprocal_mul (F : ℕ → ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    halaszUnitReciprocal F (m * n) = halaszUnitReciprocal F m * halaszUnitReciprocal F n := by
  have hh := mrtArithmetic_isMultiplicative (halaszUnitCorrection F)
    (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  unfold halaszUnitReciprocal
  rw [hh.map_mul_of_coprime hcop, norm_mul, Nat.cast_mul, mul_div_mul_comm]

lemma halasz_unit_reciprocal_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitReciprocal F (p ^ k) =
      ‖halaszUnitCorrectionLocal F p k‖ * ((p : ℝ)⁻¹) ^ k := by
  unfold halaszUnitReciprocal
  rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos k), halasz_unit_correction_prime_pow F hp,
    Nat.cast_pow, div_eq_mul_inv, inv_pow]

lemma halasz_unit_reciprocal_local_summable (F : ℕ → ℂ) (hF : OneBounded F)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => halaszUnitReciprocal F (p ^ k)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  apply Summable.of_nonneg_of_le (fun k => halasz_unit_reciprocal_nonneg F (p ^ k))
    (f := fun k => 2 * ((p : ℝ)⁻¹) ^ k)
  · intro k
    rw [halasz_unit_reciprocal_prime_pow F hp]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rcases k with _ | k
    · simp
    · exact halasz_unit_correction_local_bound F hF hp (Nat.succ_pos k)
  · exact (summable_geometric_of_lt_one (by positivity) hr).mul_left 2

lemma halasz_unit_reciprocal_local_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) ≤
      Real.exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2) := by
  let r : ℝ := (p : ℝ)⁻¹
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by simpa only [one_div] using inv_anti₀ (by norm_num) hp2
  have hr1 : r < 1 := by linarith
  have hs := halasz_unit_reciprocal_local_summable F hF hp
  have ht : (∑' k : ℕ, halaszUnitReciprocal F (p ^ (k + 2))) ≤
      2 * r ^ 2 * (1 - r)⁻¹ := by
    have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    apply (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum _ hgeom
    intro k
    change halaszUnitReciprocal F (p ^ (k + 2)) ≤ _
    rw [halasz_unit_reciprocal_prime_pow F hp]
    have hh := halasz_unit_correction_local_bound F hF hp (by omega : 0 < k + 2)
    calc
      _ ≤ 2 * r ^ (k + 2) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by rw [pow_add]; ring
  have he : (∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) =
      1 + ‖1 - F p‖ / p + ∑' k : ℕ, halaszUnitReciprocal F (p ^ (k + 2)) := by
    have hh := (hs.sum_add_tsum_nat_add 2).symm
    simpa [sum_range_succ, halasz_unit_reciprocal_prime_pow F hp,
      halaszUnitCorrectionLocal, hF1, norm_sub_rev, div_eq_mul_inv] using hh
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
    linarith
  have htail : 2 * r ^ 2 * (1 - r)⁻¹ ≤ 4 / (p : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * r ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by dsimp [r]; simp only [inv_pow, div_eq_mul_inv]; ring
  calc
    _ ≤ 1 + ‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2 := by rw [he]; linarith
    _ ≤ _ := by
      have hh := Real.add_one_le_exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2)
      linarith

lemma halasz_unit_reciprocal_prefix_le_prod (F : ℕ → ℂ) (hF : OneBounded F) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) ≤
      ∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖halaszUnitReciprocal F (p ^ k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (halasz_unit_reciprocal_nonneg F _)] using
      halasz_unit_reciprocal_local_summable F hF hp
  obtain ⟨_, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := halaszUnitReciprocal F) (halasz_unit_reciprocal_one F) (fun {_ _} h => halasz_unit_reciprocal_mul F h)
    hlocal (N + 1)
  have hi : HasSum ((Nat.smoothNumbers (N + 1)).indicator (halaszUnitReciprocal F))
      (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) :=
    (hasSum_subtype_iff_indicator (f := halaszUnitReciprocal F)
      (s := Nat.smoothNumbers (N + 1))).mp he
  have hsum : (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, (Nat.smoothNumbers (N + 1)).indicator (halaszUnitReciprocal F) n := by
    apply sum_congr rfl
    intro n hn
    have hn' := mem_Icc.mp hn
    rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hn'.1 (by omega))]
    unfold halaszUnitReciprocal
    rw [mrtArithmetic_apply_pos _ hn'.1]
  rw [hsum]
  have hfirst := hi.summable.sum_le_tsum (Icc 1 N)
    (fun n _ => Set.indicator_nonneg (fun n _ => halasz_unit_reciprocal_nonneg F n) n)
  rw [hi.tsum_eq] at hfirst
  exact hfirst

lemma halasz_unit_reciprocal_prod_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∏ p ∈ primesUpTo N, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) ≤
      Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := by
  calc
    _ ≤ ∏ p ∈ primesUpTo N, Real.exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2) := by
      apply prod_le_prod₀
      · intro p _
        exact tsum_nonneg (fun _ => halasz_unit_reciprocal_nonneg F _)
      · intro p hp
        exact halasz_unit_reciprocal_local_bound F hF hF1 (mem_filter.mp hp).2
    _ = Real.exp ((∑ p ∈ primesUpTo N, ‖1 - F p‖ / p) +
        4 * ∑ p ∈ primesUpTo N, 1 / (p : ℝ) ^ 2) := by
      rw [← Real.exp_sum, sum_add_distrib, mul_sum]
      congr 2
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, ‖1 - F p‖ / p) + 8) := by
      apply Real.exp_le_exp.mpr
      linarith [mrt_prime_inverse_square_sum N]
    _ = _ := by simp [halaszPrimeDiscrepancy, mrtArchimedeanTwist]

/-- Absolute reciprocal mass of the exact constant-one correction. -/
theorem halasz_unit_correction_reciprocal (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) ≤
      Real.exp (halaszPrimeDiscrepancy F 0 N + 8) :=
  (halasz_unit_reciprocal_prefix_le_prod F hF N).trans
    (halasz_unit_reciprocal_prod_bound F hF hF1 N)

lemma halasz_twisted_prime_discrepancy (F : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    halaszPrimeDiscrepancy (halaszTwistedFunction F t) 0 N =
      halaszPrimeDiscrepancy F t N := by
  simp [halaszPrimeDiscrepancy, halaszTwistedFunction, mrtArchimedeanTwist]

theorem halasz_twisted_unit_reciprocal (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection (halaszTwistedFunction F t) n‖ / (n : ℝ)) ≤
      Real.exp (halaszPrimeDiscrepancy F t N + 8) := by
  simpa only [halasz_twisted_prime_discrepancy] using
    halasz_unit_correction_reciprocal (halaszTwistedFunction F t)
      (halasz_twisted_oneBounded F hF t) (halasz_twisted_one F hF1 t) N

/-- Uniform reciprocal correction bound for every permitted near-twist
missing-prime mask. -/
theorem halasz_near_correction_reciprocal :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      (∑ n ∈ Icc 1 N,
        ‖halaszUnitCorrection (halaszTwistedFunction (mrtMissingCoefficient F Q) t) n‖ / (n : ℝ)) ≤
          Real.exp 8 * (Real.log N) ^ (7 / (8 : ℝ)) := by
  filter_upwards [halasz_near_masked_discrepancy, Filter.eventually_ge_atTop 2]
    with N hN hN2
  intro F hF1 hF Q hQ hcut t hD
  have hrec := halasz_twisted_unit_reciprocal (mrtMissingCoefficient F Q)
    (mrtMissingCoefficient_oneBounded F hF Q) (mrtMissingCoefficient_one F hF1 Q hQ) t N
  have hdis := hN F hF Q hQ hcut t hD
  apply hrec.trans
  calc
    _ ≤ Real.exp (7 / 8 * Real.log (Real.log N) + 8) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      rw [Real.rpow_def_of_pos hl, ← Real.exp_add]
      congr 1
      ring

end TwoPointCorrelations

end OAI
