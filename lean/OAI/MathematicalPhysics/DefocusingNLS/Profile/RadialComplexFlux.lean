import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStationaryField
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! The regular complex radial flux identity, including its vanishing endpoint at zero. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def radialComplexSource (k : ℕ) (a b : ℝ) (z : ℂ) : ℂ :=
  oddPowerNonlinearity k z-((b : ℂ)+Complex.I*(a : ℂ))*z

noncomputable def radialComplexFlux (Q : ℝ → ℂ) (r : ℝ) : ℂ :=
  (r : ℂ)^11*Complex.exp (Complex.I*(r^2/4 : ℝ))*deriv Q r

theorem radialComplexFlux_hasDerivAt (k : ℕ) (a b r : ℝ) (hr : 0 < r)
    (Q : ℝ → ℂ) (hD : DifferentiableAt ℝ (deriv Q) r)
    (hEq : deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
      Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=
        oddPowerNonlinearity k (Q r)) :
    HasDerivAt (radialComplexFlux Q)
      ((r : ℂ)^11*Complex.exp (Complex.I*(r^2/4 : ℝ))*radialComplexSource k a b (Q r)) r := by
  have hs : HasDerivAt (fun t : ℝ => t^2/4) (r/2) r := by
    convert ((hasDerivAt_id r).pow 2).div_const 4 using 1
    · rfl
    · dsimp only [id_eq]
      ring
  have he := (hs.ofReal_comp.const_mul Complex.I).cexp
  have hh := (((hasDerivAt_id r).ofReal_comp.pow 11).mul he).mul hD.hasDerivAt
  change HasDerivAt (radialComplexFlux Q) _ r at hh
  apply hh.congr_deriv
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hEq' : deriv (deriv Q) r=radialComplexSource k a b (Q r)-
      (11/r : ℝ)*deriv Q r-Complex.I*(r/2 : ℝ)*deriv Q r := by
    unfold radialComplexSource
    linear_combination hEq
  rw [hEq']
  dsimp only [Pi.pow_apply,Pi.mul_apply,id_eq]
  push_cast
  field_simp
  ring

theorem radialComplexFlux_integral (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : ContinuousOn Q (Icc 0 R))
    (hD : ContinuousOn (deriv Q) (Icc 0 R))
    (hDD : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv Q) r)
    (hEq : ∀ r ∈ Ioo 0 R,
      deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
        Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=
          oddPowerNonlinearity k (Q r)) :
    radialComplexFlux Q R=
      ∫ r in 0..R, (r : ℂ)^11*Complex.exp (Complex.I*(r^2/4 : ℝ))*
        radialComplexSource k a b (Q r) := by
  have hF : ContinuousOn (radialComplexFlux Q) (Icc 0 R) := by
    unfold radialComplexFlux
    fun_prop
  have hS : ContinuousOn (fun r : ℝ => (r : ℂ)^11*Complex.exp (Complex.I*(r^2/4 : ℝ))*
      radialComplexSource k a b (Q r)) (Icc 0 R) := by
    have hN := (contDiff_oddPowerNonlinearity k).continuous.comp_continuousOn hQ
    unfold radialComplexSource
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hF
    (fun r hr => radialComplexFlux_hasDerivAt k a b r hr.1 Q (hDD r hr) (hEq r hr))
    (ContinuousOn.intervalIntegrable_of_Icc hR.le hS)
  simpa only [radialComplexFlux,Complex.ofReal_zero,zero_pow (by norm_num : 11 ≠ 0),zero_mul,sub_zero] using hh.symm

end DefocusingNLS

end OAI
