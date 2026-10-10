import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaDiskQuotient

namespace OAI

/-! # A logarithmic error for the zeta pole throughout the right-hand strip -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zetaAtHeight_zero_left (t : ℝ) (z : ℂ) (hz : zetaAtHeight t z = 0) : z.re < -1 := by
  have hn : ¬ 1 ≤ (z + characterZeroCenter t).re := by
    intro h
    exact regularizedZeta_ne_zero_right _ h hz
  simp only [Complex.add_re, characterZeroCenter_re] at hn
  linarith

theorem zetaAtHeight_logDeriv_lower (t σ : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    -(logDeriv (zetaAtHeight t) ((σ - 2 : ℝ) : ℂ)).re ≤
      48 * (Real.log (96 * (|t| + 2) ^ 2) +
        (Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 + 1) := by
  obtain ⟨g, hg, he, hne⟩ := zeta_disk_quotient_exists t
  let M := 32 * (|t| + 2) ^ 2
  let N := ∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)
  let A := Real.log (3 * M) + N * Real.log 6 + 1
  let w : ℂ := ((σ - 2 : ℝ) : ℂ)
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t| + 2)]
  have hA : 0 < A := by
    have hl : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
    have hl6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
    have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    dsimp [A]
    positivity
  have hw : ‖w‖ ≤ 1 := by
    change ‖((σ - 2 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hgb := logDeriv_norm_le_small_disk g A hA (fun z _ => hg z)
    (fun z hz => hne z (ball_subset_closedBall hz)) (fun z hz => ?_) w hw
  · have hwball : w ∈ closedBall 0 (3 / 2 : ℝ) := by
      simpa using hw.trans (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hfne : zetaAtHeight t w ≠ 0 := by
      apply regularizedZeta_ne_zero_right
      simp only [w, Complex.add_re, Complex.ofReal_re, characterZeroCenter_re]
      linarith
    have hwS : w ∉ zetaDiskZeros t := fun hh => hfne ((mem_zetaDiskZeros t w).mp hh).2
    have hsplit : logDeriv (zetaAtHeight t) w =
        (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)) +
          logDeriv g w := by
      have hfun := funext he
      conv_lhs => rw [hfun]
      rw [logDeriv_fun_mul w (finiteZeroPolynomial_ne_zero _ _ w hwS) (hne w hwball)
        (finiteZeroPolynomial_analytic _ _ w).differentiableAt (hg w).differentiableAt,
        finiteZeroPolynomial_logDeriv _ _ w hwS]
    have hsum : 0 ≤ (∑ z ∈ zetaDiskZeros t,
        (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_nonneg
      intro z hz
      have hzleft := zetaAtHeight_zero_left t z ((mem_zetaDiskZeros t z).mp hz).2
      have hd : 0 ≤ (w - z).re := by
        simp only [Complex.sub_re, w, Complex.ofReal_re]
        linarith
      rw [div_eq_mul_inv, Complex.mul_re]
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (by
        rw [Complex.inv_re]
        exact div_nonneg hd (Complex.normSq_nonneg _))
    have hre := Complex.re_le_norm (-logDeriv g w)
    rw [Complex.neg_re, norm_neg] at hre
    have hmass := zetaDiskZeros_mass_bound t
    have hprod := mul_le_mul_of_nonneg_right hmass (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6))
    have hlog : Real.log (3 * M) = Real.log (96 * (|t| + 2) ^ 2) := by
      congr 1
      dsimp [M]
      ring
    rw [hsplit, Complex.add_re]
    dsimp only [A, N] at hgb
    rw [hlog] at hgb
    linarith
  · exact (zeta_disk_quotient_log_bound t M le_rfl g hg he hne z
      (by simpa using (mem_ball_iff_norm.mp hz).le)).trans (by dsimp [A, N]; linarith)

end Ostmann

end OAI
