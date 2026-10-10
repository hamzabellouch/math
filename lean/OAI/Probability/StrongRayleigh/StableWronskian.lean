import OAI.Probability.StrongRayleigh.AffineSlopeStability
import OAI.Probability.StrongRayleigh.PolynomialPick
import OAI.Probability.StrongRayleigh.PickSquareRoot

namespace OAI

noncomputable section

open Polynomial Set
open scoped ComplexConjugate

namespace Problem336AdditiveD139

theorem stable_wronskian_of_denominator_stable (p q : ℝ[X])
    (hpcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (hqcoeff : ∀ n : ℕ, 0 ≤ q.coeff n)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0)
    (hqstable : ∀ z : ℂ, 0 < z.im → aeval z q ≠ 0) :
    q.eval 1 * p.derivative.eval 1 - p.eval 1 * q.derivative.eval 1 ≤
      p.eval 1 * q.eval 1 := by
  by_cases hp : p = 0
  · simp [hp]
  have hq : q ≠ 0 := by
    intro hq
    simpa [hq] using hqstable Complex.I (by simp)
  have hqpos : 0 < q.eval 1 :=
    eval_pos_of_nonnegative_coefficients q hq hqcoeff (by norm_num)
  have heval (P : ℝ[X]) : aeval (1 : ℂ) P = ((P.eval 1 : ℝ) : ℂ) := by
    simpa using Polynomial.aeval_ofReal (K := ℂ) P (1 : ℝ)
  have hqne : aeval (1 : ℂ) q ≠ 0 := by
    rw [heval]
    exact_mod_cast ne_of_gt hqpos
  have hderiv := (p.hasDerivAt_aeval (1 : ℂ)).div
    (q.hasDerivAt_aeval (1 : ℂ)) hqne
  have hbound := reflectedPick_derivative_re_le
    (fun z : ℂ => aeval z p / aeval z q) _
    (polynomial_ratio_analyticOnNhd_slitPlane p q hqstable hqcoeff).differentiableOn
    (fun z hz => polynomial_ratio_im_nonneg_of_affine_stable p q hstable hz)
    (fun z => polynomial_ratio_conj p q z)
    (fun t ht => (polynomial_ratio_ofReal_pos p q hp hq hpcoeff hqcoeff ht).le)
    hderiv
  simp only [heval, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re] at hbound
  have hmul := (div_le_iff₀ (sq_pos_of_pos hqpos)).mp hbound
  have hsimp : p.eval 1 / q.eval 1 * q.eval 1 ^ 2 = p.eval 1 * q.eval 1 := by
    field_simp
  rw [hsimp] at hmul
  nlinarith

theorem stable_affine_wronskian_bound (p q : ℝ[X])
    (hpcoeff : ∀ n : ℕ, 0 ≤ p.coeff n)
    (hqcoeff : ∀ n : ℕ, 0 ≤ q.coeff n)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0) :
    q.eval 1 * p.derivative.eval 1 - p.eval 1 * q.derivative.eval 1 ≤
      p.eval 1 * q.eval 1 := by
  by_cases hq : q = 0
  · simp [hq]
  exact stable_wronskian_of_denominator_stable p q hpcoeff hqcoeff hstable
    (polynomial_slope_stable_of_affine_stable p q hq hstable)

end Problem336AdditiveD139

end

end OAI
