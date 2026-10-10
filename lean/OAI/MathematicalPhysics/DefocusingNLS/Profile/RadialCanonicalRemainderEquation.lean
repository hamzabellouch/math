import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalParameterCombination
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalParameterEquation

namespace OAI

/-! Subtracting the canonical parameter correction removes the physical Jordan source. -/

namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialCanonicalParameter_combination_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta lam : ℂ) (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (c : ℂ × ℂ) (r : ℝ) (hr : innerBoundaryRadius<r) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    HasDerivAt (canonicalParameterStateCombination ν Y Z lam c)
      (spectralPhysicalCircularField (ν-2*lam) (star ν-2*lam) eta
        (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r
        (canonicalParameterStateCombination ν Y Z lam c r)+spectralPhysicalJordanSource
          (c.1 • spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Y lam) r+
           c.2 • spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Z lam) r)) r := by
  intro ν
  have hDp := radialCanonicalParameter_hasDerivAt n z hX eta lam (1,0) Y hY r hr
  have hDm := radialCanonicalParameter_hasDerivAt n z hX eta lam (0,1) Z hZ r hr
  exact spectralPhysicalSource_combination (ν-2*lam) (star ν-2*lam) eta
    (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) _ _ _ _ c.1 c.2 r hDp hDm

theorem radialCanonicalParameter_remainder_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (eta lam : ℂ) (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (c : ℂ × ℂ) (V : ℝ → E₄) (U : E₄) (r : ℝ) (hr : innerBoundaryRadius<r)
    (hU : U=c.1 • spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Y lam) r+
      c.2 • spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) r)
    (hV : HasDerivAt V (spectralPhysicalCircularField
      (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
      (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) eta
      (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r (V r)+
        spectralPhysicalJordanSource U) r) :
    let ν := radialShootingNu (n+radialInnerShootingThreshold) z
    HasDerivAt (fun s => V s-canonicalParameterStateCombination ν Y Z lam c s)
      (spectralPhysicalCircularField (ν-2*lam) (star ν-2*lam) eta
        (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r
        (V r-canonicalParameterStateCombination ν Y Z lam c r)) r := by
  intro ν
  have hD := radialCanonicalParameter_combination_hasDerivAt n z hX eta lam Y Z hY hZ c r hr
  dsimp only at hD
  rw [← hU] at hD
  exact spectralPhysicalSource_subtraction (ν-2*lam) (star ν-2*lam) eta
    (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) V
    (canonicalParameterStateCombination ν Y Z lam c) (spectralPhysicalJordanSource U) r hV hD

end DefocusingNLS

end OAI
