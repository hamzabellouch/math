import OAI.NumberTheory.TwoPointCorrelations.HalaszWindowPerron
import OAI.NumberTheory.TwoPointCorrelations.HalaszWindowTail
import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimePolynomial
import OAI.NumberTheory.TwoPointCorrelations.HalaszCoefficientBound
import OAI.NumberTheory.TwoPointCorrelations.HalaszTriplePrefix

namespace OAI

/-! A complete finite estimate for each grouped triple convolution.
The main term, contour tail, and unsmoothing error are all explicit. -/

namespace TwoPointCorrelations

open Finset Complex MeasureTheory
open _root_.Erdos970 (VerticalIntegral VerticalIntegral')
open scoped Classical LSeries.notation

lemma halasz_vertical_integral_norm (G : ℂ → ℂ) :
    ‖VerticalIntegral' G 1‖ ≤ ‖∫ t : ℝ, G (1 + (t : ℂ) * I)‖ := by
  have hnorm : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    simp only [norm_div, norm_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
    exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr hp
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, norm_mul, norm_I,
    one_mul, Complex.ofReal_one]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

theorem halasz_prime_triple_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
    ∀ (N : ℕ) (x T A W R : ℝ) (m : ℕ), 0 < x → 0 < m → (m : ℝ) ≤ x →
      (∀ n : ℕ, x ≠ (n : ℝ)) → B ≤ T → 0 ≤ A → 0 ≤ W → 0 ≤ R →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ a b : ℕ → ℂ,
      (∀ p ∈ P, ‖a p‖ ≤ R) → (∀ q ∈ Q, ‖b q‖ ≤ 1) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
    ‖∑ n ∈ Icc 1 ⌊x⌋₊,
      (halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟
          halaszSmoothFunction f N)) n‖ ≤
      (C * x * A) *
        (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) +
      40 * x * (R * ∑ p ∈ P, Real.log (p : ℝ) / p) *
        (∑ q ∈ Q, Real.log (q : ℝ) / q) * W / ((m / x) * T) +
      R * Real.log (x + m) ^ 2 * m := by
  obtain ⟨C, B, hC, hB, hmid⟩ := halasz_prime_window_middle
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N x T A W R m hx hm hmx hxnat hBT hA hW hR P Q hP hQ a b ha hb hFA hFW
  let c : ℕ → ℂ := halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
    (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟ halaszSmoothFunction f N)
  let D := halaszPrimePolynomial P a
  let E := halaszPrimePolynomial Q b
  let F := fun t : ℝ => LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hsum (t : ℝ) : LSeriesSummable c (1 + (t : ℂ) * I) :=
    (halasz_finite_LSeries_summable P _ _).convolution
      ((halasz_finite_LSeries_summable Q _ _).convolution
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t))
  have hc : LSeriesSummable c 1 := by simpa using hsum 0
  have hline (t : ℝ) : LSeries c (1 + (t : ℂ) * I) = D t * E t * F t := by
    dsimp only [c]
    rw [LSeries_convolution' (halasz_finite_LSeries_summable P _ _)
      ((halasz_finite_LSeries_summable Q _ _).convolution
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t)),
      LSeries_convolution' (halasz_finite_LSeries_summable Q _ _)
        (halasz_smooth_LSeries_summable f hf1 hf hbound N t),
      halasz_finite_LSeries, halasz_finite_LSeries,
      halasz_prime_polynomial_series P a hPl t, halasz_prime_polynomial_series Q b hQ t]
    dsimp [D, E, F]
    ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < (m : ℝ) / x := div_pos hmR hx
  have hδ1 : (m : ℝ) / x ≤ 1 := (div_le_one hx).mpr hmx
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hpMass : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := sum_nonneg (fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _))
  have hqMass : 0 ≤ ∑ q ∈ Q, Real.log (q : ℝ) / q := sum_nonneg (fun q hq =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hQ q hq).one_le)) (Nat.cast_nonneg _))
  have hint : Integrable (fun t : ℝ => D t * E t * F t *
      halaszPerronWindowKernel x (m / x) (1 + (t : ℂ) * I)) := by
    simpa only [hline] using halasz_LSeries_window_integrable c hc hx hδ
  have htail := halasz_window_integral_truncate D E F hx hδ hδ1 hT
    (mul_nonneg hR hpMass) hqMass hW
    (halasz_prime_polynomial_bounded P a hPl ha)
    (fun t => by simpa only [one_mul] using halasz_prime_polynomial_bounded Q b hQ hb t)
    hFW hint
  have hmiddle := hmid x (m / x) T A hx hδ hδ1 hBT hA P Q hP hQ a b F hFA
  have hcoeff (n : ℕ) : ‖c n‖ ≤ R * Real.log (n : ℝ) ^ 2 :=
    halasz_triple_coefficient_bound _ _ _ hR
      (halasz_finite_prime_mangoldt_bound P a hPl hR ha)
      (fun n : ℕ => by simpa only [one_mul] using
        halasz_finite_prime_mangoldt_bound Q b hQ (R := 1) (by norm_num) hb n)
      (halasz_smooth_oneBounded f hbound N) n
  have hboundary (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖c n‖ ≤ R * Real.log (x + m) ^ 2 := by
    have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnle : (n : ℝ) ≤ x + m := by
      have hh : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast (mem_Icc.mp hn).2
      linarith [Nat.floor_le hx.le]
    exact (hcoeff n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg hn1)
        (Real.log_le_log (by positivity) hnle) 2) hR)
  have hunsmooth := halasz_window_unsmoothing c hc hx m hm hxnat hboundary
  have hnorm := halasz_vertical_integral_norm
    (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s)
  simp_rw [hline] at hnorm
  have hcompare := norm_add_le
    (VerticalIntegral' (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s) 1)
    ((∑ n ∈ Icc 1 ⌊x⌋₊, c n) -
      VerticalIntegral' (fun s => LSeries c s * halaszPerronWindowKernel x (m / x) s) 1)
  rw [add_sub_cancel, norm_sub_rev] at hcompare
  change ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ _
  dsimp only [D, E, halaszPrimePolynomial] at htail hnorm
  linarith

end TwoPointCorrelations

end OAI
