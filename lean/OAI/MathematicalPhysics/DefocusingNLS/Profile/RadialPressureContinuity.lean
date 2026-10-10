import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureSmallness

namespace OAI

/-! Continuity of the pressure and its transport, including the regular origin. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

theorem radialComplexNormSq_hasDerivAt (Q : ℝ → ℂ) (r : ℝ)
    (hQ : DifferentiableAt ℝ Q r) :
    HasDerivAt (fun t => Complex.normSq (Q t)) (2*(star (Q r)*deriv Q r).re) r := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r
    (hQ.hasDerivAt.star.mul hQ.hasDerivAt)
  convert h using 1
  · funext t
    simp [Complex.normSq_apply,Complex.mul_re]
  · simp only [Complex.reCLM_apply,Complex.add_re,Complex.mul_re,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring

theorem radialPressure_hasDerivAt (m : ℕ) (a : ℝ) (Q : ℝ → ℂ) (r : ℝ)
    (hQ : DifferentiableAt ℝ Q r) :
    HasDerivAt (fun t => ‖Q t‖^(2*m)/a)
      ((2*(m : ℝ)*Complex.normSq (Q r)^(m-1)*(star (Q r)*deriv Q r).re)/a) r := by
  have h := ((radialComplexNormSq_hasDerivAt Q r hQ).pow m).div_const a
  convert h using 1
  · funext t
    simp only [Pi.pow_apply,pow_mul,Complex.sq_norm]
  · ring

theorem radialPressure_deriv_continuousOn (m : ℕ) (a R : ℝ) (Q : ℝ → ℂ)
    (hQ : ContinuousOn Q (Icc 0 R)) (hD : ContinuousOn (deriv Q) (Icc 0 R))
    (hd : ∀ r ∈ Icc 0 R, DifferentiableAt ℝ Q r) :
    ContinuousOn (deriv (fun t => ‖Q t‖^(2*m)/a)) (Icc 0 R) := by
  have hN : ContinuousOn (fun r => Complex.normSq (Q r)) (Icc 0 R) :=
    Complex.continuous_normSq.comp_continuousOn hQ
  have hP : ContinuousOn (fun r => (star (Q r)*deriv Q r).re) (Icc 0 R) :=
    Complex.continuous_re.comp_continuousOn (hQ.star.mul hD)
  have hc := (((hN.pow (m-1)).const_mul (2*(m : ℝ))).mul hP).div_const a
  apply hc.congr
  intro r hr
  exact (radialPressure_hasDerivAt m a Q r (hd r hr)).deriv

theorem radialMatchedPressureTransport_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (fun r => radialVelocity (6-2*radialShootingA n)
      (fun t => ‖radialMatchedProfile n z t‖) r*
      deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n) r) (Icc 0 R) := by
  let Q := radialMatchedProfile n z
  have hQ : Continuous Q := (radialMatchedProfile_differentiable n z hX hz).continuous
  have hW : ContinuousOn (radialVelocity (6-2*radialShootingA n) (fun t => ‖Q t‖))
      (Icc 0 R) := by
    have hn : ∀ r ∈ Icc 0 R, (‖Q r‖^2 : ℝ)≠0 := fun r hr =>
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.1))
    have hA := continuous_radialAverage (fun r => ‖Q r‖^2) (hQ.norm.pow 2)
    exact continuous_id.continuousOn.mul
      ((continuous_const.mul hA).continuousOn.div (hQ.norm.pow 2).continuousOn hn)
  exact hW.mul (radialPressure_deriv_continuousOn _ _ R Q hQ.continuousOn
    (radialMatchedProfile_derivative_continuousOn n z hX hz R)
    (fun r _ => radialMatchedProfile_differentiable n z hX hz r))

end DefocusingNLS

end OAI
