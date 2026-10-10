import OAI.MathematicalPhysics.DefocusingNLS.Profile.NormalizedSlowCone

namespace OAI

/-! # Identification of the nonsingular tail with division by `q` -/

open MeasureTheory Set Polynomial

namespace DefocusingNLS

theorem shiftedSlowDerivative_parameter_step (q : ℂ) (m : ℕ) (s : ℂ) (t : ℝ)
    (hq : -1 < q.re) (hsre : s.re = 0) (ht : 0 < t) :
    shiftedSlowDerivative 1 q m s t = -q * shiftedSlowDerivative 0 (q + 1) (m + 1) s t := by
  have hx : 0 < ((t : ℂ) - s).re := by simpa [hsre] using ht
  simpa only [shiftedSlowDerivative, iteratedDeriv_succ, iteratedDeriv_zero] using
    (hasDerivAt_regularizedSlowSolution_shift q m ((t : ℂ) - s) hq hx).deriv

theorem shiftedSlowSecondDerivative_parameter_step (q : ℂ) (m : ℕ) (s : ℂ) (t : ℝ)
    (hq : -1 < q.re) (hsre : s.re = 0) (ht : 0 < t) :
    shiftedSlowDerivative 2 q m s t = -q * shiftedSlowDerivative 1 (q + 1) (m + 1) s t := by
  have hx : 0 < ((t : ℂ) - s).re := by simpa [hsre] using ht
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  have h1 := (hasDerivAt_regularizedSlowSolution_shift (q + 1) (m + 1)
    ((t : ℂ) - s) hq' hx).deriv
  have h2 := (hasDerivAt_deriv_regularizedSlowSolution q m ((t : ℂ) - s) hq hx).deriv
  simp only [shiftedSlowDerivative, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, h2]
  have he : q + 1 + 1 = q + 2 := by ring
  rw [he, Nat.add_assoc]
  ring

theorem slowDerivative_coefficient_parameter_step (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) :
    laguerreCoefficientIntegral (shiftedSlowDerivative 1 q m s) n =
      -q * slowLaguerreCoefficient (q + 1) (m + 1) s n := by
  unfold slowLaguerreCoefficient laguerreCoefficientIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [laguerreIntegrand,
    shiftedSlowDerivative_parameter_step q m s t hq hsre ht]
  ring

theorem slowSecondDerivative_coefficient_parameter_step (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) :
    laguerreCoefficientIntegral (shiftedSlowDerivative 2 q m s) n =
      -q * laguerreCoefficientIntegral (shiftedSlowDerivative 1 (q + 1) (m + 1) s) n := by
  unfold laguerreCoefficientIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [laguerreIntegrand,
    shiftedSlowSecondDerivative_parameter_step q m s t hq hsre ht]
  ring

theorem q_mul_normalizedSlowB (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    q * normalizedSlowB q m s (n + 1) = slowLaguerreB q m s (n + 1) := by
  rw [slowLaguerreB_eq_derivative_coefficient q m s n hq hsre hsim,
    slowDerivative_coefficient_parameter_step q m s n hq hsre]
  simp only [normalizedSlowB, Nat.add_sub_cancel]
  ring

theorem q_mul_normalizedSlowC (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    q * normalizedSlowC q m s n = slowLaguerreC q m s n := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  rw [slowLaguerreC_eq_derivative_coefficients q m s n hq hsre hsim,
    slowSecondDerivative_coefficient_parameter_step q m s n hq hsre,
    slowDerivative_coefficient_parameter_step q m s n hq hsre]
  have hb := slowLaguerreB_succ (q + 1) (m + 1) s n
  rw [slowLaguerreB_eq_derivative_coefficient (q + 1) (m + 1) s n hq' hsre hsim] at hb
  unfold normalizedSlowC
  linear_combination -q * hb

theorem q_mul_normalizedSlowCoefficient (q : ℂ) (m : ℕ) (s : ℂ) (n : ℕ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    q * normalizedSlowCoefficient q m s (n + 1) = slowLaguerreCoefficient q m s (n + 1) := by
  have h := slowLaguerreB_succ q m s (n + 1)
  rw [← q_mul_normalizedSlowB q m s (n + 1) hq hsre hsim,
    ← q_mul_normalizedSlowB q m s n hq hsre hsim] at h
  simp only [normalizedSlowB, normalizedSlowCoefficient, Nat.add_sub_cancel] at h ⊢
  linear_combination -h

end DefocusingNLS

end OAI
