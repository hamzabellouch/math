import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeMatchedIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedFlux
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCoreBoundary

namespace OAI

/-! The limiting mass average is the physical current of the matched free profile. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingFreeCurrent_hasDerivAt (z : ProfileMatchingBall)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialWeightedFlux (radialShootingFreeExterior z))
      (6*Complex.normSq (radialShootingFreeExterior z r)-
        11/r*radialWeightedFlux (radialShootingFreeExterior z) r) r := by
  have hQ := radialShootingFreeExterior_hasDerivAt z r hr
  have hD := radialShootingFreeExterior_hasDerivAt_deriv z r hr
  have he : deriv (deriv (radialShootingFreeExterior z)) r+
      (11/r : ℝ)*deriv (radialShootingFreeExterior z) r+
      Complex.I*((r/2 : ℝ)*deriv (radialShootingFreeExterior z) r+
        (0 : ℂ)*radialShootingFreeExterior z r)+
      ((radialShootingB (profileMatchingParameter z)+1 : ℝ) : ℂ)*
        radialShootingFreeExterior z r=
      oddPowerNonlinearity 0 (radialShootingFreeExterior z r) := by
    rw [hD.deriv]
    simp only [oddPowerNonlinearity,pow_zero,mul_one,zero_mul,add_zero,
      Complex.ofReal_add,Complex.ofReal_one,radialFreeCoefficient]
    push_cast
    ring
  simpa only [mul_zero,sub_zero] using radialWeightedFlux_hasDerivAt 0 0
    (radialShootingB (profileMatchingParameter z)+1) r hr.ne'
    (radialShootingFreeExterior z) hQ.differentiableAt hD.differentiableAt he

theorem radialMatchedFreeTransport_hasDerivAt (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radialMatchedFreeTransportFunction z)
      (6*radialMatchedFreeMassFunction z r-11/r*radialMatchedFreeTransportFunction z r) r := by
  have hd := ((hasDerivAt_id r).mul
    (hasDerivAt_radialAverage (radialMatchedFreeMassFunction z) hc r hr)).const_mul 6
  apply hd.congr_deriv
  dsimp only [radialMatchedFreeTransportFunction,id_eq]
  field_simp [hr]
  ring

theorem radialMatchedFreeTransport_core (z : ProfileMatchingBall) :
    radialMatchedFreeTransportFunction z (radialShootingR (profileMatchingParameter z))=
      radialShootingR (profileMatchingParameter z)/2 := by
  have hL : 0 ≤ radialShootingR (profileMatchingParameter z) :=
    le_trans (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1
  unfold radialMatchedFreeTransportFunction
  rw [radialAverage_congr _ (fun _ => (1 : ℝ)) _ hL
    (fun r hr => radialMatchedFreeMass_core z r hr.2),radialAverage_const]
  ring

theorem radialMatchedFreeTransport_eq_current (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hR : radialShootingR (profileMatchingParameter z) ≤ R) :
    radialMatchedFreeTransportFunction z R=
      radialWeightedFlux (radialShootingFreeExterior z) R := by
  let L := radialShootingR (profileMatchingParameter z)
  let Q := radialShootingFreeExterior z
  let A := radialMatchedFreeTransportFunction z
  let F := fun r : ℝ => r^11*(A r-radialWeightedFlux Q r)
  have hL : 0 < L := by dsimp only [L]; linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]
  have hQc : ContinuousOn Q (Icc L R) :=
    (radialShootingFreeExterior_contDiffOn z).continuousOn.mono
      (fun r hr => hL.trans_le hr.1)
  have hDc : ContinuousOn (deriv Q) (Icc L R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt_deriv z r (hL.trans_le hr.1)).continuousAt.continuousWithinAt
  have hAc : Continuous A := continuous_const.mul
    (continuous_id.mul (continuous_radialAverage _ hc))
  have hFc : ContinuousOn F (Icc L R) := by
    dsimp only [F,radialWeightedFlux]
    fun_prop
  have hFd (r : ℝ) (hr : r ∈ Ioo L R) : HasDerivAt F 0 r := by
    have hr0 := hL.trans hr.1
    have hμ : radialMatchedFreeMassFunction z r=Complex.normSq (Q r) := by
      rw [radialMatchedFreeMassFunction,radialMatchedFreeProfile_eq_physical z hz₁ hz r hr.1.le]
      exact Complex.sq_norm _
    have hd := ((hasDerivAt_id r).pow 11).mul
      ((radialMatchedFreeTransport_hasDerivAt z hc r hr0.ne').sub
        (radialShootingFreeCurrent_hasDerivAt z r hr0))
    apply hd.congr_deriv
    dsimp only [id_eq,Pi.pow_apply]
    rw [hμ]
    change _*(A r-radialWeightedFlux Q r)+r^11*
      ((6*Complex.normSq (Q r)-11/r*A r)-
        (6*Complex.normSq (Q r)-11/r*radialWeightedFlux Q r))=0
    field_simp [hr0.ne']
    ring
  have hInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume L R :=
    intervalIntegrable_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR hFc hFd hInt
  have hFL : F L=0 := by
    dsimp only [F,A,Q,radialWeightedFlux,L]
    rw [radialMatchedFreeTransport_core,radialShootingFreeExterior_core_value z hz₁ hz,
      radialShootingFreeExterior_neumann z hz]
    simp
  have he' : (0 : ℝ)=F R-F L := by
    simpa only [intervalIntegral.integral_zero] using he
  have hFR : F R=0 := by linarith
  have hRp : 0 < R := hL.trans_le hR
  have hd : A R-radialWeightedFlux Q R=0 :=
    (mul_eq_zero.mp hFR).resolve_left (pow_ne_zero 11 hRp.ne')
  exact sub_eq_zero.mp hd

end DefocusingNLS

end OAI
