import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterThermal

namespace OAI

/-! A weak effective polynomial lower bound at one for every nonprincipal
quadratic character, obtained from nonnegative convolution coefficients. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

lemma mrt_character_thermal_nat {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    mrtCharacterThermal χ t = ∑' n : ℕ, χ.zetaMul n * (Real.exp (-t * n) : ℂ) := by
  have hh := tsum_zero_pnat_eq_tsum_nat (mrt_character_thermal_summable χ ht)
  simpa only [ArithmeticFunction.map_zero, zero_mul, zero_add, mrtCharacterThermal] using hh

lemma mrt_exp_neg_one_ge_quarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (by linarith [Real.exp_one_lt_three])

theorem mrt_quadratic_thermal_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) {t : ℝ} (ht : 0 < t) (K : ℕ)
    (hK : t * (K : ℝ) ^ 2 ≤ 1) :
    (K : ℝ) / 4 ≤ (mrtCharacterThermal χ t).re := by
  let F : ℕ → ℝ := fun n => (χ.zetaMul n).re * Real.exp (-t * n)
  have hF (n : ℕ) : 0 ≤ F n := mul_nonneg
    (mrt_quadratic_coefficient_re_nonneg χ hχ n) (Real.exp_nonneg _)
  have hs : Summable F := by
    simpa only [F, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using (Complex.hasSum_re
        (mrt_character_thermal_summable χ ht).hasSum).summable
  have heq : (mrtCharacterThermal χ t).re = ∑' n, F n := by
    rw [mrt_character_thermal_nat χ ht,
      Complex.re_tsum (mrt_character_thermal_summable χ ht)]
    simp only [F, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [heq]
  calc
    _ = ∑ _n ∈ Icc 1 K, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ n ∈ Icc 1 K, F (n ^ 2) := by
      apply sum_le_sum
      intro n hn
      have hnK : (n : ℝ) ≤ K := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      have hsquare : t * (n : ℝ) ^ 2 ≤ 1 :=
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnK 2) ht.le).trans hK
      have hexp : 1 / 4 ≤ Real.exp (-t * (n ^ 2 : ℕ)) := by
        apply mrt_exp_neg_one_ge_quarter.trans
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
      exact hexp.trans (le_mul_of_one_le_left (Real.exp_nonneg _)
        (mrt_quadratic_square_coefficient_re χ hχ n hn0))
    _ = ∑ n ∈ (Icc 1 K).image (fun n : ℕ => n ^ 2), F n := by
      apply (sum_image ?_).symm
      intro a _ b _ hab
      nlinarith
    _ ≤ ∑' n, F n := hs.sum_le_tsum _ (fun n _ => hF n)

theorem mrt_quadratic_LFunction_one_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) :
    1 / (64 * (q : ℝ)) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  let t : ℝ := 1 / (64 * (q : ℝ) ^ 2)
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have ht : 0 < t := by dsimp only [t]; positivity
  have hscale : t * ((8 * q : ℕ) : ℝ) ^ 2 ≤ 1 := by
    dsimp only [t]
    push_cast
    field_simp
    norm_num
  have hlower := mrt_quadratic_thermal_lower χ hsq ht (8 * q) hscale
  have herr := mrt_character_thermal_error χ hχ ht
  have hnorm : (2 * q : ℝ) ≤ ‖mrtCharacterThermal χ t‖ := by
    have hre := (Complex.abs_re_le_norm (mrtCharacterThermal χ t))
    push_cast at hlower
    have hle := (le_abs_self (mrtCharacterThermal χ t).re).trans hre
    linarith
  have htri := norm_sub_le (DirichletCharacter.LFunction χ 1 / (t : ℂ))
    (DirichletCharacter.LFunction χ 1 / (t : ℂ) - mrtCharacterThermal χ t)
  have hid : DirichletCharacter.LFunction χ 1 / (t : ℂ) -
      (DirichletCharacter.LFunction χ 1 / (t : ℂ) - mrtCharacterThermal χ t) =
      mrtCharacterThermal χ t := by ring
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at htri
  have hdiv : (q : ℝ) ≤ ‖DirichletCharacter.LFunction χ 1‖ / t := by linarith
  have hh := (le_div_iff₀ ht).mp hdiv
  have heq : (q : ℝ) * t = 1 / (64 * (q : ℝ)) := by
    dsimp only [t]
    field_simp
  rwa [heq] at hh

end TwoPointCorrelations

end OAI
