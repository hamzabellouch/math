import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreTail
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialProjection

namespace OAI

/-! # The Laguerre recurrence for the actual regularized slow solution -/

open Filter Topology MeasureTheory Set Polynomial

namespace DefocusingNLS

theorem shiftedSlowDerivative_equation (q : ℂ) (M : ℕ) (s : ℂ) (t : ℝ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) (ht : 0 ≤ t) :
    (t : ℂ) * shiftedSlowDerivative 2 q (M + 1) s t +
      (1 - (t : ℂ)) * shiftedSlowDerivative 1 q (M + 1) s t +
      (M : ℂ) * shiftedSlowDerivative 1 q (M + 1) s t -
      s * (shiftedSlowDerivative 2 q (M + 1) s t -
        shiftedSlowDerivative 1 q (M + 1) s t) -
      q * shiftedSlowDerivative 0 q (M + 1) s t = 0 := by
  have hx : 0 ≤ ((t : ℂ) - s).re := by simpa [hsre] using ht
  have hx0 := Complex.slitPlane_ne_zero (shifted_argument_mem_slitPlane s hsim t)
  have h := regularizedSlowSolution_kummer_equation_closed q (M + 1) ((t : ℂ) - s) hq hx hx0
  simp only [shiftedSlowDerivative, iteratedDeriv_succ, iteratedDeriv_zero]
  push_cast at h
  linear_combination h

theorem integrableOn_weightedPolynomial_shiftedSlowDerivative
    (n : ℕ) (q : ℂ) (m : ℕ) (s : ℂ) (p : ℂ[X])
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    IntegrableOn (weightedPolynomialIntegrand (shiftedSlowDerivative n q m s) p) (Ioi 0) :=
  integrableOn_exp_neg_mul_polynomial_of_growth _ _ _
    (continuous_shiftedSlowDerivative n q m s hq hsim).continuousOn
    (shiftedSlowDerivative_isBigO_rpow n q m s hq hsre)

theorem shiftedSlowDerivative_projected_equation (q : ℂ) (M : ℕ) (s : ℂ) (p : ℂ[X])
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    weightedPolynomialIntegral (shiftedSlowDerivative 2 q (M + 1) s) (X * p) +
      weightedPolynomialIntegral (shiftedSlowDerivative 1 q (M + 1) s) ((1 - X) * p) +
      (M : ℂ) * weightedPolynomialIntegral (shiftedSlowDerivative 1 q (M + 1) s) p -
      s * (weightedPolynomialIntegral (shiftedSlowDerivative 2 q (M + 1) s) p -
        weightedPolynomialIntegral (shiftedSlowDerivative 1 q (M + 1) s) p) -
      q * weightedPolynomialIntegral (shiftedSlowDerivative 0 q (M + 1) s) p = 0 := by
  let f := fun n => shiftedSlowDerivative n q (M + 1) s
  let A := weightedPolynomialIntegrand (f 2) (X * p)
  let B := weightedPolynomialIntegrand (f 1) ((1 - X) * p)
  let C := weightedPolynomialIntegrand (f 1) p
  let D := weightedPolynomialIntegrand (f 2) p
  let E := weightedPolynomialIntegrand (f 0) p
  have hi (n : ℕ) (r : ℂ[X]) :
      IntegrableOn (weightedPolynomialIntegrand (f n) r) (Ioi 0) :=
    integrableOn_weightedPolynomial_shiftedSlowDerivative n q (M + 1) s r hq hsre hsim
  have hAB : IntegrableOn (fun t => A t + B t) (Ioi 0) := (hi 2 _).add (hi 1 _)
  have hABC : IntegrableOn (fun t => A t + B t + (M : ℂ) * C t) (Ioi 0) :=
    hAB.add ((hi 1 p).const_mul (M : ℂ))
  have hDC : IntegrableOn (fun t => D t - C t) (Ioi 0) := (hi 2 p).sub (hi 1 p)
  have hsDC : IntegrableOn (fun t => s * (D t - C t)) (Ioi 0) := hDC.const_mul s
  have hqE : IntegrableOn (fun t => q * E t) (Ioi 0) := (hi 0 p).const_mul q
  have hz : (∫ t in Ioi (0 : ℝ), A t + B t + (M : ℂ) * C t -
      s * (D t - C t) - q * E t) = 0 := by
    calc
      _ = ∫ _t in Ioi (0 : ℝ), (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have h := shiftedSlowDerivative_equation q M s t hq hsre hsim ht.le
        simp only [shiftedSlowDerivative_zero] at h
        dsimp [A, B, C, D, E, f, weightedPolynomialIntegrand]
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
          Polynomial.eval_X]
        linear_combination (Real.exp (-t) : ℂ) * p.eval (t : ℂ) * h
      _ = 0 := by simp
  have hABCD : IntegrableOn (fun t => A t + B t + (M : ℂ) * C t -
      s * (D t - C t)) (Ioi 0) := hABC.sub hsDC
  rw [integral_sub hABCD hqE, integral_sub hABC hsDC,
    integral_add hAB ((hi 1 p).const_mul (M : ℂ)), integral_add (hi 2 _) (hi 1 _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub (hi 2 p) (hi 1 p)] at hz
  exact hz

/-- The recurrence in Lemma `free:laguerre` now holds for the integral-defined
coefficients of `H`, with no spectral or sequence hypothesis. -/
theorem slowLaguerre_recurrence (q : ℂ) (M : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    (q + n) * slowLaguerreCoefficient q (M + 1) s n =
      -(M : ℂ) * slowLaguerreB q (M + 1) s (n + 1) -
        s * slowLaguerreC q (M + 1) s n := by
  let f := fun k => shiftedSlowDerivative k q (M + 1) s
  have hi (k : ℕ) (p : ℂ[X]) :
      IntegrableOn (weightedPolynomialIntegrand (f k) p) (Ioi 0) :=
    integrableOn_weightedPolynomial_shiftedSlowDerivative k q (M + 1) s p hq hsre hsim
  have hg := weightedPolynomialIntegral_laguerre_operator (f 0) (f 1) (f 2)
    (laguerrePolynomial n)
    (fun t _ => hasDerivAt_shiftedSlowDerivative 0 q (M + 1) s hq hsim t)
    (fun t _ => hasDerivAt_shiftedSlowDerivative 1 q (M + 1) s hq hsim t)
    (continuous_shiftedSlowDerivative 0 q (M + 1) s hq hsim).continuousWithinAt
    (continuous_shiftedSlowDerivative 1 q (M + 1) s hq hsim).continuousWithinAt
    (hi 0) (hi 1) (hi 2)
  rw [laguerreOperator_laguerrePolynomial] at hg
  have he : weightedPolynomialIntegral (f 0) (-C (n : ℂ) * laguerrePolynomial n) =
      -(n : ℂ) * weightedPolynomialIntegral (f 0) (laguerrePolynomial n) := by
    change weightedPolynomialFunctional (f 0) (hi 0) _ = _
    rw [neg_mul, map_neg, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [weightedPolynomialFunctional_apply, neg_mul]
  rw [he] at hg
  have hp := shiftedSlowDerivative_projected_equation q M s (laguerrePolynomial n) hq hsre hsim
  have hb := slowLaguerreB_eq_derivative_coefficient q (M + 1) s n hq hsre hsim
  have hc := slowLaguerreC_eq_derivative_coefficients q (M + 1) s n hq hsre hsim
  change slowLaguerreB q (M + 1) s (n + 1) =
    -weightedPolynomialIntegral (f 1) (laguerrePolynomial n) at hb
  change slowLaguerreC q (M + 1) s n =
    weightedPolynomialIntegral (f 2) (laguerrePolynomial n) -
      weightedPolynomialIntegral (f 1) (laguerrePolynomial n) at hc
  change (q + n) * weightedPolynomialIntegral (f 0) (laguerrePolynomial n) = _
  linear_combination -hp + hg + (M : ℂ) * hb + s * hc

end DefocusingNLS

end OAI
