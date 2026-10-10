import OAI.NumberTheory.TwoPointCorrelations.HalaszLogBands
import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimePolynomial

namespace OAI

/-! On one logarithmic band the two prime mean-square masses cancel:
the adaptive denominator contributes v⁻² and the two prime masses O(v²). -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_prime_set_mass_le {Y : ℝ} (hY : 1 ≤ Y) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Y) :
    (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ Real.log Y + halaszMertensConstant := by
  have hsub : Q ⊆ sievePrimesUpTo Y := by
    intro q hq
    exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by linarith)).mpr (hQ q hq).2),
      (hQ q hq).1⟩
  exact (sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => Real.log (q : ℝ) / q)
    hsub (fun q hq _ => div_nonneg
      (Real.log_nonneg (by exact_mod_cast (sievePrimesUpTo_prime Y q hq).one_le))
      (Nat.cast_nonneg _))).trans (halasz_prime_prefix_mass_le hY)

theorem halasz_band_mean_square_weights : ∃ K : ℝ, 0 < K ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (X v : ℝ), 0 < X → Real.log 2 ≤ v →
    ∀ (P Q : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) →
      (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Real.exp (2 * v)) →
      Real.sqrt (∑ p ∈ P, ‖f p / (Real.log (X / p) : ℂ)‖ ^ 2 *
        (Real.log (p : ℝ) / p)) *
        Real.sqrt (∑ q ∈ Q, ‖f q‖ ^ 2 * (Real.log (q : ℝ) / q)) ≤ K := by
  let C₁ := 1 + 2 * halaszMertensConstant / Real.log 2
  let C₂ := 2 + halaszMertensConstant / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_pos.mpr (mul_pos hC₁ hC₂), ?_⟩
  intro f hf X v hX hv P Q hP hQ
  have hv0 : 0 < v := htwo.trans_le hv
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hQl : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1
  have hpMass : (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ C₁ * v :=
    halasz_log_band_mass_linear hX hv P hP
  have hqMass : (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ C₂ * v := by
    have hm := halasz_prime_set_mass_le (Y := Real.exp (2 * v))
      (Real.one_le_exp_iff.mpr (by linarith)) Q hQ
    rw [Real.log_exp] at hm
    have hh := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ halaszMertensConstant / Real.log 2 from div_nonneg hM htwo.le)
    rw [div_mul_cancel₀ _ htwo.ne'] at hh
    dsimp [C₂]
    linarith
  let A := ∑ p ∈ P, ‖f p / (Real.log (X / p) : ℂ)‖ ^ 2 * (Real.log (p : ℝ) / p)
  let B := ∑ q ∈ Q, ‖f q‖ ^ 2 * (Real.log (q : ℝ) / q)
  have hA0 : 0 ≤ A := sum_nonneg (fun p hp => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _)))
  have hB0 : 0 ≤ B := sum_nonneg (fun q hq => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hQl q hq).one_le)) (Nat.cast_nonneg _)))
  have hA : A ≤ C₁ / v := by
    calc
      _ ≤ (v⁻¹) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / p :=
        halasz_prime_coefficient_square_mass P _ hPl
          (fun p hp => halasz_adaptive_coefficient_bound f hf hv0 (hPl p hp).pos (hP p hp).2.1)
      _ ≤ (v⁻¹) ^ 2 * (C₁ * v) := mul_le_mul_of_nonneg_left hpMass (sq_nonneg _)
      _ = _ := by field_simp
  have hB : B ≤ C₂ * v := by
    have hb := halasz_prime_coefficient_square_mass Q f hQl (fun q hq => hf q (hQl q hq).pos)
    simpa only [one_pow, one_mul] using hb.trans (by simpa only [one_pow, one_mul] using hqMass)
  have hAB : A * B ≤ C₁ * C₂ := by
    calc
      _ ≤ (C₁ / v) * (C₂ * v) := mul_le_mul hA hB hB0 (by positivity)
      _ = _ := by field_simp
  have hs := Real.sqrt_le_sqrt hAB
  rw [Real.sqrt_mul hA0] at hs
  exact hs

end TwoPointCorrelations

end OAI
