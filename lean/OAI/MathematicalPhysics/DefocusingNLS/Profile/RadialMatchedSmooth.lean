import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEJoin
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingPhysicalJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialProfileSplice

namespace OAI

/-! The matched radial profile is smooth and stationary at every positive radius. -/

open scoped ContDiff
open Set Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchedJet (n : ℕ) (z : ProfileMatchingBall) (r : ℝ) : ℂ × ℂ :=
  if r ≤ innerBoundaryRadius then radialShootingInnerJet n (profileMatchingParameter z) r
  else radialShootingPhysicalJet n z r

theorem radialMatchedJet_fst (n : ℕ) (z : ProfileMatchingBall) :
    (fun r => (radialMatchedJet n z r).1)=radialMatchedProfile n z := by
  funext r
  dsimp only [radialMatchedJet,radialMatchedProfile]
  split_ifs <;> rfl

theorem radialMatchedJet_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialMatchedJet n z)
      (radialStationaryField (n+radialInnerShootingThreshold) (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) r (radialMatchedJet n z r)) r := by
  apply radial_ode_join _ _ _ innerBoundaryRadius
    (by linarith [innerBoundaryRadius_bounds.1])
    (radialShootingInnerJet_continuousOn n (profileMatchingParameter z))
    (radialShootingInnerJet_hasDerivAt n (profileMatchingParameter z))
    (radialShootingPhysicalJet_hasDerivAt n z hX)
    (radialShootingJet_match n z hX hz) _ r hr
  exact (radialStationaryField_contDiffAt _ _ _ _
    (by linarith [innerBoundaryRadius_bounds.1])).continuousAt

theorem radialMatchedJet_contDiffOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ContDiffOn ℝ ∞ (radialMatchedJet n z) (Ioi 0) :=
  radialStationarySolution_contDiffOn _ _ _ _ (radialMatchedJet_hasDerivAt n z hX hz)

theorem radialMatchedProfile_contDiffOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ContDiffOn ℝ ∞ (radialMatchedProfile n z) (Ioi 0) := by
  have hh := (radialMatchedJet_contDiffOn n z hX hz).fst
  rwa [radialMatchedJet_fst] at hh

theorem radialMatchedProfile_hasDerivAt (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialMatchedProfile n z) (radialMatchedJet n z r).2 r := by
  have hh := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r
    (radialMatchedJet_hasDerivAt n z hX hz r hr)
  change HasDerivAt (fun t => (radialMatchedJet n z t).1) (radialMatchedJet n z r).2 r at hh
  rwa [radialMatchedJet_fst] at hh

theorem radialMatchedProfile_stationary (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (radialMatchedProfile n z)) r+
      (11/r : ℝ)*deriv (radialMatchedProfile n z) r+
      Complex.I*((r/2 : ℝ)*deriv (radialMatchedProfile n z) r+
        (radialShootingA n : ℂ)*radialMatchedProfile n z r)+
      (radialShootingB (profileMatchingParameter z) : ℂ)*radialMatchedProfile n z r=
        oddPowerNonlinearity (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) := by
  have hh := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r
    (radialMatchedJet_hasDerivAt n z hX hz r hr)
  change HasDerivAt (fun t => (radialMatchedJet n z t).2) _ r at hh
  have he : deriv (radialMatchedProfile n z) =ᶠ[nhds r]
      (fun t => (radialMatchedJet n z t).2) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    exact (radialMatchedProfile_hasDerivAt n z hX hz t ht).deriv
  have hD := (hh.congr_of_eventuallyEq he).deriv
  have hQ := congrFun (radialMatchedJet_fst n z) r
  have hQ' := (radialMatchedProfile_hasDerivAt n z hX hz r hr).deriv
  dsimp only [radialStationaryField] at hD
  rw [hQ,← hQ'] at hD
  change deriv (deriv (radialMatchedProfile n z)) r=
    -(11/r : ℝ)*deriv (radialMatchedProfile n z) r-
      Complex.I*((r/2 : ℝ)*deriv (radialMatchedProfile n z) r+
        (radialShootingA n : ℂ)*radialMatchedProfile n z r)-
      (radialShootingB (profileMatchingParameter z) : ℂ)*radialMatchedProfile n z r+
      oddPowerNonlinearity (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) at hD
  linear_combination hD

end DefocusingNLS

end OAI
