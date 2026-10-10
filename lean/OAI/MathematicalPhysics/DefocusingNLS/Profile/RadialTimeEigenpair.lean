import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeCalculus

namespace OAI

/-! The time-translation symmetry in the actual two-channel radial system. -/

open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_time_eigenpair (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) 0 1
      (radialAffineEuler ((radialShootingA n : ℂ)-
        Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))
        (radialMatchedEvenProfile n z))
      (fun r => star (radialAffineEuler ((radialShootingA n : ℂ)-
        Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))
        (radialMatchedEvenProfile n z) r)) := by
  have heta : ((0 : ℝ) : ℂ)=(0 : ℂ) := rfl
  have hlam : ((1 : ℝ) : ℂ)=(1 : ℂ) := by norm_num
  rw [← heta,← hlam]
  apply harmonicRadialEigenpair_of_real_first (eta := 0) (lam := 1)
  intro r hr
  let Q := radialMatchedEvenProfile n z
  let m := n+radialInnerShootingThreshold
  let a := radialShootingA n
  let b := radialShootingB (profileMatchingParameter z)
  let c : ℂ := (a : ℂ)-Complex.I*(b : ℂ)
  have hQ : ContDiff ℝ ∞ Q := radialMatchedEvenProfile_contDiff n z hX hz
  have hQr : Q r=radialMatchedProfile n z r := radialMatchedEvenProfile_nonneg n z r hr.le
  have hm : 2*(m : ℝ)*a=1 := by
    have h := radialShootingA_power n (profileMatchingParameter z)
    dsimp only [m,a]
    nlinarith
  have hs : Complex.I*(deriv (deriv Q) r+(11/r : ℝ)*deriv Q r)-
      (r/2 : ℝ)*deriv Q r-c*Q r-Complex.I*oddPowerNonlinearity m (Q r)=0 := by
    have h := radialMatchedEvenProfile_stationary n z hX hz r hr
    rw [oddPowerNonlinearity_eq]
    dsimp only [c,a,b,m,Q]
    push_cast at h ⊢
    linear_combination h
  have ht := (radialMatched_translation_eigenpair n z hX hz r hr).1
  rw [← hQr] at ht
  have hn : oddPowerDerivative m (Q r) (radialAffineEuler c Q r)=
      c*oddPowerNonlinearity m (Q r)+oddPowerNonlinearity m (Q r)+
        ((r : ℂ)/2)*oddPowerDerivative m (Q r) (deriv Q r) := by
    have hsm : (r : ℂ)/2*deriv Q r=(r/2 : ℝ) • deriv Q r := by
      simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_ofNat]
    rw [radialAffineEuler,map_add,hsm,map_smul,
      oddPower_time_cancellation a b m hm (Q r)]
    dsimp only [c]
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_ofNat]
  change (1 : ℂ)*radialAffineEuler c Q r = _
  rw [radialAffineEuler_second c Q hQ,radialAffineEuler_deriv c Q hQ,← hQr]
  simp only [oddPowerDerivative,add_apply,smul_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe,starL'_apply,smul_eq_mul] at hn
  dsimp only [radialAffineEuler,Q,c,a,b,m] at hs ht hn ⊢
  simp only [star_add,star_sub,star_mul,star_div₀,Complex.star_def,
    Complex.conj_ofReal,Complex.conj_I,map_ofNat] at hn ⊢
  simp only [starRingEnd_apply] at hn ⊢
  push_cast at hs ht hn ⊢
  have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  linear_combination (norm := (field_simp [hrC]; ring))
    -((radialShootingA n : ℂ)-Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)+1)*hs+
      ((r : ℂ)/2)*ht+Complex.I*hn

end DefocusingNLS

end OAI
