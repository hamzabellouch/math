import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimeOscillation

namespace OAI

/-! A uniform tail form of the fixed-modulus prime-number estimate. Its exponentially decreasing constant pays for the growing
frequency factor in the moderate-frequency partial summation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimeLogWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

lemma halasz_prime_log_weight_split (n : ℕ) :
    halaszPrimeLogWeight n = modFiveLogWeight true n + modFiveLogWeight false n := by
  by_cases hn : n.Prime <;> by_cases hr : n % 5 = 1 <;>
    simp [halaszPrimeLogWeight, modFiveLogWeight, ModFivePrime, hn, hr]

lemma halasz_prime_theta_split (x : ℝ) :
    partialCoefficientSum halaszPrimeLogWeight x = modFiveTheta true x + modFiveTheta false x := by
  unfold partialCoefficientSum modFiveTheta
  simp_rw [halasz_prime_log_weight_split, sum_add_distrib]

theorem ModFiveThetaInput.halasz_prime_tail_error (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a x : ℝ, 2 ≤ a → a ≤ x →
      |partialCoefficientSum halaszPrimeLogWeight x - x| ≤
        (K * Real.exp (-c * Real.sqrt (Real.log a))) * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, htheta⟩ := hP
  refine ⟨c / 2, 48 * C / (c / 2) ^ 4, by positivity, by positivity, ?_⟩
  intro a x ha hax
  have hx : 2 ≤ x := ha.trans hax
  have hxp : 0 < x := by linarith
  have hap : 0 < a := by linarith
  have hx1 : 1 < x := by linarith
  have hsum : |partialCoefficientSum halaszPrimeLogWeight x - x| ≤
      2 * C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [halasz_prime_theta_split]
    have he : modFiveTheta true x + modFiveTheta false x - x =
        (modFiveTheta true x - modFiveDensity true * x) +
          (modFiveTheta false x - modFiveDensity false * x) := by
      norm_num [modFiveDensity]
      ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add (htheta true x hx)
      (htheta false x hx)).trans_eq (by ring))
  have hhalf : 0 < c / 2 := by positivity
  have hpoly := exp_neg_sqrt_log_le (c / 2) x hhalf hx1
  have hmono : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log a)) := by
    apply Real.exp_le_exp.mpr
    have hs := Real.sqrt_le_sqrt (Real.log_le_log hap hax)
    nlinarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log x)) =
      Real.exp (-(c / 2) * Real.sqrt (Real.log x)) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply hsum.trans
  rw [hexp]
  have hb := mul_le_mul hpoly hmono (Real.exp_pos _).le (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * C * x by positivity)
  convert hh using 1
  ring

end TwoPointCorrelations

end OAI
