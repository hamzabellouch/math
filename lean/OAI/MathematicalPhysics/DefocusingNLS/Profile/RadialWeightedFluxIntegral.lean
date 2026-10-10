import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedFlux
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityEquation

namespace OAI

/-! The weighted radial velocity is the exact positive mass average. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialWeightedFlux_average (m : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : ContinuousOn Q (Icc 0 R))
    (hD : ContinuousOn (deriv Q) (Icc 0 R))
    (hQd : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ Q r)
    (hDD : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv Q) r)
    (hEq : ∀ r ∈ Ioo 0 R,
      deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
        Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=
          oddPowerNonlinearity m (Q r)) :
    radialWeightedFlux Q R=(6-2*a)*R*radialAverage (fun t => Complex.normSq (Q t)) R := by
  let F := fun r : ℝ => r^11*radialWeightedFlux Q r
  have hμ : ContinuousOn (fun t => Complex.normSq (Q t)) (Icc 0 R) :=
    Complex.continuous_normSq.comp_continuousOn hQ
  have hc : ContinuousOn F (Icc 0 R) := by
    dsimp only [F,radialWeightedFlux]
    fun_prop
  have hd (r : ℝ) (hr : r ∈ Ioo 0 R) :
      HasDerivAt F ((6-2*a)*(Complex.normSq (Q r)*r^11)) r := by
    have hh := ((hasDerivAt_id r).pow 11).mul
      (radialWeightedFlux_hasDerivAt m a b r hr.1.ne' Q (hQd r hr) (hDD r hr) (hEq r hr))
    apply hh.congr_deriv
    dsimp only [id_eq,Pi.pow_apply]
    field_simp [hr.1.ne']
    ring
  have hsrc : ContinuousOn (fun r : ℝ => (6-2*a)*(Complex.normSq (Q r)*r^11))
      (Icc 0 R) := continuousOn_const.mul (hμ.mul (continuous_id.pow 11).continuousOn)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hc hd
    (hsrc.intervalIntegrable_of_Icc hR.le)
  have he : R^11*radialWeightedFlux Q R=
      (6-2*a)*(R^12*radialAverage (fun t => Complex.normSq (Q t)) R) := by
    rw [radialAverage_scaling,← intervalIntegral.integral_const_mul]
    simpa only [F,zero_pow (by norm_num : 11 ≠ 0),zero_mul,sub_zero] using hi.symm
  apply mul_left_cancel₀ (pow_ne_zero 11 hR.ne')
  rw [he]
  ring

theorem radialWeightedFlux_velocity (m : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : ContinuousOn Q (Icc 0 R))
    (hD : ContinuousOn (deriv Q) (Icc 0 R))
    (hQd : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ Q r)
    (hDD : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv Q) r)
    (hEq : ∀ r ∈ Ioo 0 R,
      deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
        Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=
          oddPowerNonlinearity m (Q r)) :
    radialWeightedFlux Q R/Complex.normSq (Q R)=
      radialVelocity (6-2*a) (fun r => ‖Q r‖) R := by
  rw [radialWeightedFlux_average m a b R hR Q hQ hD hQd hDD hEq]
  simp only [radialVelocity,radialVelocityRatio,Complex.sq_norm]
  ring

end DefocusingNLS

end OAI
