import OAI.Probability.StrongRayleigh.StableUnivariate

namespace OAI

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace Problem336AdditiveD139

theorem polynomial_ratio_im_nonneg_of_affine_stable (p q : ℝ[X])
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (aeval z p / aeval z q).im := by
  by_cases hq : aeval z q = 0
  · simp [hq]
  · by_contra! hneg
    have hw : 0 < (-(aeval z p / aeval z q)).im := by
      simpa using neg_pos.mpr hneg
    apply hstable z (-(aeval z p / aeval z q)) hz hw
    rw [neg_mul, div_mul_cancel₀ _ hq]
    ring

theorem polynomial_ratio_conj (p q : ℝ[X]) (z : ℂ) :
    aeval (conj z) p / aeval (conj z) q =
      conj (aeval z p / aeval z q) := by
  rw [Polynomial.aeval_conj, Polynomial.aeval_conj, map_div₀]

theorem polynomial_ratio_im_nonpos_of_affine_stable (p q : ℝ[X])
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0)
    {z : ℂ} (hz : z.im < 0) :
    (aeval z p / aeval z q).im ≤ 0 := by
  have h := polynomial_ratio_im_nonneg_of_affine_stable p q hstable
    (z := conj z) (by simpa using neg_pos.mpr hz)
  rw [polynomial_ratio_conj] at h
  change 0 ≤ -(aeval z p / aeval z q).im at h
  linarith

theorem polynomial_ratio_analyticOnNhd_slitPlane (p q : ℝ[X])
    (hstable : ∀ z : ℂ, 0 < z.im → aeval z q ≠ 0)
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) :
    AnalyticOnNhd ℂ (fun z : ℂ => aeval z p / aeval z q) Complex.slitPlane := by
  intro z hz
  exact (analyticAt_id.aeval_polynomial p).div
    (analyticAt_id.aeval_polynomial q)
    (aeval_ne_zero_on_slitPlane_of_stable q hstable hcoeff hz)

theorem polynomial_ratio_ofReal_pos (p q : ℝ[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (hqcoeff : ∀ n : ℕ, 0 ≤ q.coeff n)
    {t : ℝ} (ht : 0 < t) :
    0 < (aeval (t : ℂ) p / aeval (t : ℂ) q).re := by
  have hpos := div_pos
    (eval_pos_of_nonnegative_coefficients p hp hpcoeff ht)
    (eval_pos_of_nonnegative_coefficients q hq hqcoeff ht)
  have heq : aeval (t : ℂ) p / aeval (t : ℂ) q =
      ((p.eval t / q.eval t : ℝ) : ℂ) := by
    calc
      _ = ((p.eval t : ℝ) : ℂ) / ((q.eval t : ℝ) : ℂ) :=
        congrArg₂ (· / ·) (Polynomial.aeval_ofReal (K := ℂ) p t)
          (Polynomial.aeval_ofReal (K := ℂ) q t)
      _ = _ := by simp
  simpa [heq] using hpos

end Problem336AdditiveD139

end

end OAI
