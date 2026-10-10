import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalPhysicalParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalSourceCombination
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingTail

namespace OAI

/-! The actual canonical parameter columns solve the physical inhomogeneous equation. -/

namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialCanonicalParameter_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta lam : ℂ) (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) c Y)
    (r : ℝ) (hr : innerBoundaryRadius<r) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    let V := fun la => spectralPhysicalPair (ν-2*la) (star ν-2*la) (Y la)
    HasDerivAt (fun s => deriv (fun la => V la s) lam)
      (spectralPhysicalCircularField (ν-2*lam) (star ν-2*lam) eta
        (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r
        (deriv (fun la => V la r) lam)+spectralPhysicalJordanSource (V lam r)) r := by
  intro ν V
  have hm := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hr₁ : 1<r := lt_of_le_of_lt innerBoundaryRadius_bounds.1 hr
  have hν : ν = -1/((n+radialInnerShootingThreshold : ℕ) : ℂ)+
      2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
    dsimp only [ν]
    unfold radialShootingNu radialShootingQ
    ring
  have hs : (Complex.exp (ν*(Real.log r : ℂ))*star (Complex.exp (ν*(Real.log r : ℂ))))^
      (n+radialInnerShootingThreshold)=1/(r : ℂ)^2 := by
    rw [hν]
    exact spectralPhysicalFactor_scale _ hm _ r (lt_trans zero_lt_one hr₁)
  have hh := canonical_physical_parameter_equation ν eta (radialShootingM z)
    (n+radialInnerShootingThreshold) (by omega) (Real.log innerBoundaryRadius)
    hX (radialShootingM_ne_zero z) c Y hY lam r hr₁ hs
  simpa only [V,spectralPhysicalJordanSource,radialMatchedProfile,ite_eq_right hr.not_ge,
    radialShootingExteriorProfile,radialPhysicalExterior] using hh

end DefocusingNLS

end OAI
