import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenmode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEvenProfile

namespace OAI

/-! The phase symmetry is an actual solution of the two circular mode
equations for the constructed profile. -/

namespace DefocusingNLS
open ProfileCertificate

theorem oddPower_circular_phase (m : ℕ) (q : ℂ) :
    (((m+1 : ℕ) : ℂ)*q^m*star q^m)*(Complex.I*q)+
      ((m : ℂ)*q^(m+1)*star q^(m-1))*(-Complex.I*star q) =
      Complex.I*oddPowerNonlinearity m q := by
  cases m with
  | zero => simp [oddPowerNonlinearity]
  | succ m =>
    simp only [Nat.add_sub_cancel,oddPowerNonlinearity,
      Nat.cast_add,Nat.cast_one,pow_succ]
    ring

theorem harmonicRadialEigenpair_phase (a b : ℝ) (m : ℕ) (Q : ℝ → ℂ)
    (hQ : ∀ r, 0<r →
      Complex.I*(deriv (deriv Q) r+(11/r : ℝ)*deriv Q r)-
        (r/2 : ℝ)*deriv Q r+(-(a : ℂ)+Complex.I*(b : ℂ))*Q r-
        Complex.I*oddPowerNonlinearity m (Q r)=0) :
    IsHarmonicRadialEigenpair a b m Q 0 0
      (fun r => Complex.I*Q r) (fun r => -Complex.I*star (Q r)) := by
  intro r hr
  have hs := hQ r hr
  have hn := oddPower_circular_phase m (Q r)
  have hsc := congrArg star hs
  simp only [star_add,star_sub,star_mul,star_neg,star_zero,
    Complex.star_def,Complex.conj_I,Complex.conj_ofReal] at hsc
  simp only [starRingEnd_apply] at hsc
  constructor
  · simp only [deriv_const_mul_field',zero_mul,zero_div,sub_zero]
    rw [hn]
    linear_combination (norm := ring_nf) -Complex.I*hs
  · simp only [deriv_const_mul_field',deriv.star',zero_mul,zero_div,sub_zero]
    have he : star (((m+1 : ℕ) : ℂ)*Q r^m*star (Q r)^m)*(-Complex.I*star (Q r))+
        star ((m : ℂ)*Q r^(m+1)*star (Q r)^(m-1))*(Complex.I*Q r) =
        -Complex.I*star (oddPowerNonlinearity m (Q r)) := by
      have hnc := congrArg star hn
      simp only [star_add,star_mul,star_neg,star_star,
        show star Complex.I = -Complex.I from Complex.conj_I,neg_neg] at hnc
      simp only [star_mul]
      linear_combination hnc
    rw [he]
    linear_combination (norm := ring_nf) Complex.I*hsc

theorem radialMatched_phase_eigenpair (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) 0 0
      (fun r => Complex.I*radialMatchedEvenProfile n z r)
      (fun r => -Complex.I*star (radialMatchedEvenProfile n z r)) := by
  have hp := harmonicRadialEigenpair_phase (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
    (radialMatchedEvenProfile n z) (fun r hr => by
      have h := radialMatchedEvenProfile_stationary n z hX hz r hr
      rw [oddPowerNonlinearity_eq]
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,mul_assoc] using h)
  intro r hr
  simpa only [radialMatchedEvenProfile_nonneg n z r hr.le] using hp r hr

end DefocusingNLS

end OAI
