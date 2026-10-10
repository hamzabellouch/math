import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeCurrent

namespace OAI

/-! The exact first-order coefficient cancelled by the free profile gauge. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedFreeMass_eq_normSq (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (r : ℝ) (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    radialMatchedFreeMassFunction z r=Complex.normSq (radialShootingFreeExterior z r) := by
  rw [radialMatchedFreeMassFunction,radialMatchedFreeProfile_eq_physical z hz₁ hz r hr]
  exact Complex.sq_norm _

theorem radialMatchedFreeMass_hasDerivAt (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (r : ℝ) (hr : radialShootingR (profileMatchingParameter z) < r) :
    HasDerivAt (radialMatchedFreeMassFunction z)
      (2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re) r := by
  have hr0 : 0 < r := lt_trans
    (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hr
  have hQ := (radialShootingFreeExterior_hasDerivAt z r hr0).differentiableAt.hasDerivAt
  have he : radialMatchedFreeMassFunction z =ᶠ[nhds r]
      fun t => Complex.normSq (radialShootingFreeExterior z t) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact radialMatchedFreeMass_eq_normSq z hz₁ hz t (le_of_lt ht)
  have hμ : HasDerivAt (fun t => Complex.normSq (radialShootingFreeExterior z t))
      (2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re) r := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hQ.star.mul hQ)
    convert hh using 1
    · funext t
      simp [Complex.normSq_apply,Complex.mul_re]
    · simp [Complex.mul_re]
      ring
  exact hμ.congr_of_eventuallyEq he

theorem radialFreeGaugeCoefficient_algebra (q dq : ℂ) (r : ℝ) :
    (((2*(star q*dq).re : ℝ) : ℂ)+
        Complex.I*((r/2*Complex.normSq q+2*(star q*dq).im : ℝ) : ℂ))*q=
      (Complex.normSq q : ℂ)*(2*dq+Complex.I*(r/2 : ℝ)*q) := by
  apply Complex.ext <;>
    simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem radialMatchedFreeGaugeCoefficient (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (r : ℝ)
    (hr : radialShootingR (profileMatchingParameter z) ≤ r) :
    (((2*(star (radialShootingFreeExterior z r)*deriv (radialShootingFreeExterior z) r).re : ℝ) : ℂ)+
        Complex.I*(radialMatchedFreeTransportFunction z r : ℂ))*radialShootingFreeExterior z r=
      (radialMatchedFreeMassFunction z r : ℂ)*
        (2*deriv (radialShootingFreeExterior z) r+
          Complex.I*(r/2 : ℝ)*radialShootingFreeExterior z r) := by
  rw [radialMatchedFreeTransport_eq_current z hz₁ hz hc r hr,
    radialMatchedFreeMass_eq_normSq z hz₁ hz r hr]
  exact radialFreeGaugeCoefficient_algebra _ _ r

end DefocusingNLS

end OAI
