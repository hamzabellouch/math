import OAI.Analysis.CircleDomains.Modulus.LinePayment

namespace OAI

/-!
# Mean derivative of a randomly shifted staircase

A smooth degree-one lift has average derivative one over a full period.
For a uniform shift of the level grid this gives the derivative expectation.
Iterated integration gives the corresponding product identity for two
independent shifts.
-/

open MeasureTheory

namespace CircleDomainRigidity.FiniteTransfer

/-- FTC computes the integral of the shifted derivative over one period. -/
theorem integral_shifted_deriv_eq_period {P : ℝ → ℝ} {h : ℝ}
    (hP : ContDiff ℝ 1 P) (hperiod : ∀ x, P (x + h) = P x + h) (x : ℝ) :
    (∫ θ in (0 : ℝ)..h, deriv P (x - θ)) = h := by
  rw [intervalIntegral.integral_comp_sub_left, sub_zero,
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc hP.contDiffOn]
  have heq := hperiod (x - h)
  have hx : x - h + h = x := by ring
  rw [hx] at heq
  linarith

/-- The normalized uniform-shift mean is exactly one. -/
theorem average_shifted_deriv_eq_one {P : ℝ → ℝ} {h : ℝ}
    (hh : 0 < h) (hP : ContDiff ℝ 1 P)
    (hperiod : ∀ x, P (x + h) = P x + h) (x : ℝ) :
    (∫ θ in (0 : ℝ)..h, deriv P (x - θ)) / h = 1 := by
  rw [integral_shifted_deriv_eq_period hP hperiod, div_self hh.ne']

/-- Joining the original coordinate to a shifted staircase by a cutoff
preserves the mean derivative multiplier. -/
theorem integral_cutoff_multiplier {P : ℝ → ℝ} {h : ℝ}
    (hP : ContDiff ℝ 1 P) (hperiod : ∀ x, P (x + h) = P x + h)
    (x χ : ℝ) :
    (∫ θ in (0 : ℝ)..h, (1 - χ) + χ * deriv P (x - θ)) = h := by
  have hi : IntervalIntegrable (fun θ => deriv P (x - θ)) volume 0 h :=
    (hP.continuous_deriv_one.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 h
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul χ),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_shifted_deriv_eq_period hP hperiod]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- Two independent shifts have product mean one, by iterated integration. -/
theorem integral_independent_cutoff_multipliers
    {P Q : ℝ → ℝ} {h : ℝ}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hperiodP : ∀ x, P (x + h) = P x + h)
    (hperiodQ : ∀ x, Q (x + h) = Q x + h) (x y χ ψ : ℝ) :
    (∫ θ in (0 : ℝ)..h, ∫ φ in (0 : ℝ)..h,
      ((1 - χ) + χ * deriv P (x - θ)) *
        ((1 - ψ) + ψ * deriv Q (y - φ))) = h ^ 2 := by
  simp_rw [intervalIntegral.integral_const_mul,
    integral_cutoff_multiplier hQ hperiodQ]
  rw [intervalIntegral.integral_mul_const,
    integral_cutoff_multiplier hP hperiodP]
  ring

end CircleDomainRigidity.FiniteTransfer

end OAI
