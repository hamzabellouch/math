import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrincipalPNTBridge
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedProgressionInputs

namespace OAI

/-! # The conductor-one consequence of the progression input

The principal smooth PNT is not an independent input: the conductor-one
theta estimate, elementary prime-power removal and partial summation suffice.
-/

namespace Ostmann

open Filter
open scoped Classical BigOperators

theorem primeProgressionTheta_one (x : ℝ) :
    primeProgressionTheta 1 0 x = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp [primeProgressionTheta, primeProgressionLog, Finset.sum_filter, Nat.ModEq, Nat.mod_one]

theorem PublishedProgressionInput.principal_theta_bound (P : PublishedProgressionInput)
    (x : ℝ) (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤
      P.errorConstant * x * Real.exp (-P.decay * Real.sqrt (Real.log x)) := by
  have h := P.theta 1 le_rfl 0 (by norm_num) x hx
  simpa only [primeProgressionTheta_one, P.localZero_one, pageCoefficient, pageBeta,
    Nat.totient_one, Nat.cast_one, thetaMainTerm, zero_mul, zero_div, sub_zero, div_one]
    using h

private theorem prime_power_error_log_scale (d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop,
      2 * Real.sqrt (Real.exp y) * y ≤ Real.exp y * Real.exp (-d * Real.sqrt y) := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 1
    (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left (2 : ℝ)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hpoly, eventually_ge_atTop ((4 * d) ^ 2),
    eventually_ge_atTop (0 : ℝ)] with y hy hlarge hy0
  have hpoly' : 2 * y ≤ Real.exp (y / 4) := by
    apply (le_abs_self (2 * y)).trans
    simpa only [pow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul,
      show (1 / 4 : ℝ) * y = y / 4 by ring] using hy
  have hroot : 4 * d ≤ Real.sqrt y := by
    have hs := Real.sqrt_le_sqrt hlarge
    rwa [Real.sqrt_sq (by positivity)] at hs
  have hcost : d * Real.sqrt y ≤ y / 4 := by
    nlinarith [Real.sq_sqrt hy0]
  calc
    _ = Real.exp (y / 2) * (2 * y) := by rw [← Real.exp_half]; ring
    _ ≤ Real.exp (y / 2) * Real.exp (y / 4) :=
      mul_le_mul_of_nonneg_left hpoly' (Real.exp_nonneg _)
    _ = Real.exp (3 * y / 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (y - d * Real.sqrt y) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem PublishedProgressionInput.principal_chebyshev_pnt (P : PublishedProgressionInput) :
    ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))) := by
  refine ⟨P.decay, P.decay_pos, ?_⟩
  apply Asymptotics.IsBigO.of_bound (P.errorConstant + 1)
  have hsmall := Real.tendsto_log_atTop.eventually
    (prime_power_error_log_scale P.decay P.decay_pos)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hsmall hx
  have hx0 : 0 < x := by linarith
  have hpow : |Chebyshev.psi x - Chebyshev.theta x| ≤
      x * Real.exp (-P.decay * Real.sqrt (Real.log x)) := by
    refine (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)).trans ?_
    simpa only [Real.exp_log hx0] using hsmall
  have htheta := P.principal_theta_bound x hx
  have hh := abs_sub_le (Chebyshev.psi x) (Chebyshev.theta x) x
  have hsum : |Chebyshev.psi x - x| ≤
      (P.errorConstant + 1) * (x * Real.exp (-P.decay * Real.sqrt (Real.log x))) := by
    nlinarith
  simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.sqrt_eq_rpow,
    abs_of_pos (mul_pos hx0 (Real.exp_pos _))] using hsum

theorem PublishedProgressionInput.smoothPrincipalPNT (P : PublishedProgressionInput) :
    PublishedSmoothPrincipalPNT :=
  publishedSmoothPrincipalPNT_of_chebyshev P.principal_chebyshev_pnt

end Ostmann

end OAI
