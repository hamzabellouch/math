import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexFlux
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! A nonsingular average form of the complex radial derivative. -/

open Set MeasureTheory intervalIntegral
namespace DefocusingNLS

noncomputable def radialComplexAverage (k : ℕ) (a b : ℝ) (Q : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ)^11*
    Complex.exp (Complex.I*(r^2*(t^2-1)/4 : ℝ))*radialComplexSource k a b (Q (r*t))

theorem radialComplexAverage_continuous (k : ℕ) (a b : ℝ) (Q : ℝ → ℂ)
    (hQ : Continuous Q) : Continuous (radialComplexAverage k a b Q) := by
  have hN := (contDiff_oddPowerNonlinearity k).continuous
  apply continuous_parametric_intervalIntegral_of_continuous' _ 0 1
  unfold Function.uncurry radialComplexSource
  fun_prop

theorem radialComplexAverage_zero (k : ℕ) (a b : ℝ) (Q : ℝ → ℂ) :
    radialComplexAverage k a b Q 0=radialComplexSource k a b (Q 0)/12 := by
  simp only [radialComplexAverage,zero_pow (by norm_num : 2 ≠ 0),zero_mul,zero_div,
    Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
  rw [intervalIntegral.integral_mul_const]
  have hi : (∫ t in (0 : ℝ)..1, (t : ℂ)^11)=(1/12 : ℂ) := by
    simp_rw [← Complex.ofReal_pow]
    rw [intervalIntegral.integral_ofReal]
    norm_num [integral_pow]
  rw [hi]
  ring

theorem radialComplexAverage_scaling (k : ℕ) (a b r : ℝ) (Q : ℝ → ℂ) :
    (r : ℂ)^12*Complex.exp (Complex.I*(r^2/4 : ℝ))*radialComplexAverage k a b Q r=
      ∫ t in (0 : ℝ)..r, (t : ℂ)^11*Complex.exp (Complex.I*(t^2/4 : ℝ))*
        radialComplexSource k a b (Q t) := by
  let F : ℝ → ℂ := fun t => (t : ℂ)^11*Complex.exp (Complex.I*(t^2/4 : ℝ))*
    radialComplexSource k a b (Q t)
  have hs := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) F r
  simp only [mul_zero,mul_one,Complex.real_smul] at hs
  have hfun : (fun t => F (r*t))=fun t : ℝ =>
      ((r : ℂ)^11*Complex.exp (Complex.I*(r^2/4 : ℝ)))*
        ((t : ℂ)^11*Complex.exp (Complex.I*(r^2*(t^2-1)/4 : ℝ))*
          radialComplexSource k a b (Q (r*t))) := by
    funext t
    have he : Complex.exp (Complex.I*((r*t)^2/4 : ℝ))=
        Complex.exp (Complex.I*(r^2/4 : ℝ))*
          Complex.exp (Complex.I*(r^2*(t^2-1)/4 : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [F]
    rw [he]
    push_cast
    ring
  rw [hfun,intervalIntegral.integral_const_mul] at hs
  rw [← hs]
  dsimp only [radialComplexAverage]
  ring

theorem radialComplexDerivative_average (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : ContinuousOn Q (Icc 0 R))
    (hD : ContinuousOn (deriv Q) (Icc 0 R))
    (hDD : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv Q) r)
    (hEq : ∀ r ∈ Ioo 0 R,
      deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
        Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=
          oddPowerNonlinearity k (Q r)) :
    deriv Q R=(R : ℂ)*radialComplexAverage k a b Q R := by
  have hh := (radialComplexFlux_integral k a b R hR Q hQ hD hDD hEq).trans
    (radialComplexAverage_scaling k a b R Q).symm
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hn : (R : ℂ)^11*Complex.exp (Complex.I*(R^2/4 : ℝ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hR0) (Complex.exp_ne_zero _)
  apply mul_left_cancel₀ hn
  change radialComplexFlux Q R=_
  rw [hh]
  ring

end DefocusingNLS

end OAI
