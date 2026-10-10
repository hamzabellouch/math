import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteActualCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSmooth

namespace OAI

/-! The matched profile supplies the individual nonlinear coefficient
symbols required for the qualitative part of remote reduction. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_profile_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) :
    HasLogJetBound (radialShootingNu (n+radialInnerShootingThreshold) z).re
      (fun t => radialMatchedProfile n z (Real.exp t)) := by
  have hh := homogeneousPhysicalProfile_logJetBound
    (radialShootingNu (n+radialInnerShootingThreshold) z) _
    (radialExteriorCanonical_logJetBound _ _ _ _ hX (radialShootingM_ne_zero z))
  apply hh.eventually_congr
  filter_upwards [eventually_gt_atTop (Real.log innerBoundaryRadius)] with t ht
  have hr : innerBoundaryRadius < Real.exp t := by
    have hpos : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
    simpa only [Real.exp_log hpos] using Real.exp_lt_exp.mpr ht
  simp only [radialMatchedProfile,ite_eq_right hr.not_ge,
    radialShootingExteriorProfile,radialPhysicalExterior,Real.log_exp]

theorem spectralRemote_matched_bounded_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (sigma : ℝ) :
    HasLogJetBound 0 (fun t => spectralRemotePhysicalBounded (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) sigma
      (spectralDiagonalCoefficient (n+radialInnerShootingThreshold) (radialMatchedProfile n z (Real.exp t)))
      (spectralCrossCoefficient (n+radialInnerShootingThreshold) (radialMatchedProfile n z (Real.exp t)))) := by
  let m := n+radialInnerShootingThreshold
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hnu : (radialShootingNu m z).re = -2*radialShootingA n := by
    rw [radialShootingNu_physical n z]
    simp [Complex.mul_re,Complex.mul_im]
  have hscale : 2*(m : ℝ)*(radialShootingNu m z).re = -2 := by
    rw [hnu]
    have ha := radialShootingA_power n (profileMatchingParameter z)
    change 2*radialShootingA n*(m : ℝ) = 1 at ha
    nlinarith
  exact spectralRemote_oddPower_individual _ _ sigma _ m hm hscale _
    (spectralRemote_matched_profile_symbol n z hX)

end DefocusingNLS

end OAI
