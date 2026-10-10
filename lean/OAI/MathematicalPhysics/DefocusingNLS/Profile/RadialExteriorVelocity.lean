import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAmplitudeEquation

namespace OAI

/-! Exterior velocity and deformation depend only on the canonical logarithmic jet. -/

namespace DefocusingNLS
open ProfileCertificate

theorem complex_logDerivative_re (q d : ℂ) :
    (d/q).re=(star q*d).re/Complex.normSq q := by
  simp only [Complex.div_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem complex_logDerivative_im (q d : ℂ) :
    (d/q).im=(star q*d).im/Complex.normSq q := by
  simp only [Complex.div_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem radialPhysicalExterior_logDerivative (ν : ℂ) (Z : ℝ → ℂ × ℂ)
    (r : ℝ) (hr : r ≠ 0) (hZ : (Z (Real.log r)).1 ≠ 0) :
    radialPhysicalExteriorSlope ν Z r/radialPhysicalExterior ν Z r=
      (ν+(Z (Real.log r)).2/(Z (Real.log r)).1)/(r : ℂ) := by
  unfold radialPhysicalExteriorSlope radialPhysicalExterior
  have hrC := Complex.ofReal_ne_zero.mpr hr
  field_simp [Complex.exp_ne_zero,hZ,hrC]

theorem radialMatchedProfile_logDerivative (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : innerBoundaryRadius < r) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
      (radialShootingM z) (Real.log innerBoundaryRadius)
    deriv (radialMatchedProfile n z) r/radialMatchedProfile n z r=
      (ν+(Z (Real.log r)).2/(Z (Real.log r)).1)/(r : ℂ) := by
  dsimp only
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  rw [(radialMatchedProfile_hasDerivAt n z hX hz r hrp).deriv]
  simp only [radialMatchedJet,radialMatchedProfile,ite_eq_right hr.not_ge,
    radialShootingPhysicalJet,radialPhysicalJet,radialShootingExteriorProfile]
  exact radialPhysicalExterior_logDerivative _ _ r hrp.ne'
    (((radialExteriorCanonical_spec hX).2.2 (Real.log r)
      (Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr.le)).1)

theorem radialMatchedAmplitude_logDerivative (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    deriv (fun t => ‖radialMatchedProfile n z t‖) r/‖radialMatchedProfile n z r‖=
      (deriv (radialMatchedProfile n z) r/radialMatchedProfile n z r).re := by
  have hn := norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.le)
  rw [complex_logDerivative_re,← Complex.sq_norm]
  have hh := complexAmplitude_first_derivative _ r
    (radialMatchedProfile_differentiable n z hX hz r)
    (radialMatchedProfile_ne_zero n z hX r hr.le)
  rw [← hh]
  field_simp [hn]

theorem radialMatchedVelocity_logarithmic (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : innerBoundaryRadius < r) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
      (radialShootingM z) (Real.log innerBoundaryRadius)
    let ξ := (Z (Real.log r)).2/(Z (Real.log r)).1
    let w := radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖)
    w r/r=1/2+2/r^2*(ν.im+ξ.im) := by
  dsimp only
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hw := radialMatchedVelocity_formula n z hX hz r hrp
  rw [mul_div_assoc] at hw
  rw [← complex_logDerivative_im,radialMatchedProfile_logDerivative n z hX hz r hr] at hw
  simp only [Complex.div_ofReal_im,Complex.add_im] at hw
  rw [← hw]
  field_simp [hrp.ne']

theorem radialMatchedDeformation_logarithmic (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : innerBoundaryRadius < r) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
      (radialShootingM z) (Real.log innerBoundaryRadius)
    let ξ := (Z (Real.log r)).2/(Z (Real.log r)).1
    let w := radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖)
    deriv w r=1/2-ξ.re-2/r^2*(ν.im+ξ.im)*(11+2*ν.re+2*ξ.re) := by
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold)
    (radialShootingM z) (Real.log innerBoundaryRadius)
  let ξ := (Z (Real.log r)).2/(Z (Real.log r)).1
  let A := fun t => ‖radialMatchedProfile n z t‖
  let c := 6-2*radialShootingA n
  let w := radialVelocity c A
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hwr : w r/r=1/2+2/r^2*(ν.im+ξ.im) :=
    radialMatchedVelocity_logarithmic n z hX hz r hr
  have hAr := radialMatchedAmplitude_logDerivative n z hX hz r hrp
  rw [radialMatchedProfile_logDerivative n z hX hz r hr] at hAr
  simp only [Complex.div_ofReal_re,Complex.add_re] at hAr
  have hwval : w r=(1/2+2/r^2*(ν.im+ξ.im))*r := (div_eq_iff hrp.ne').1 hwr
  have hc : c=6+ν.re := by
    have hν := congrArg Complex.re (radialShootingNu_physical n z)
    norm_num [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im] at hν
    dsimp only [c,ν]
    linarith
  have hd := radialMatchedVelocity_hasDerivAt n z hX hz r hrp
  change deriv w r=_
  calc
    deriv w r=c-11*(w r/r)-2*w r*(deriv A r/A r) := by rw [hd.deriv]; ring
    _ = _ := by
      rw [hwr,hAr,hwval,hc]
      change 6+ν.re-11*(1/2+2/r^2*(ν.im+ξ.im))-
        2*((1/2+2/r^2*(ν.im+ξ.im))*r)*((ν.re+ξ.re)/r)=_
      field_simp [hrp.ne']
      ring

end DefocusingNLS

end OAI
