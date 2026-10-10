import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolarRegularity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStationaryField
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerSlopeContinuity

namespace OAI

/-! The actual inner value/derivative pair satisfies the first-order stationary ODE. -/

open Set
namespace DefocusingNLS

noncomputable def radialShootingInnerJet (n : ℕ) (w : RadialShootingDisk) (r : ℝ) : ℂ × ℂ :=
  (radialShootingInnerComplex n w r,deriv (radialShootingInnerComplex n w) r)

theorem radialShootingInnerJet_continuousOn (n : ℕ) (w : RadialShootingDisk) :
    ContinuousOn (radialShootingInnerJet n w) (Icc 0 innerBoundaryRadius) :=
  (radialShootingInner_differentiable n w).continuous.continuousOn.prodMk
    (radialShootingInner_derivative_continuousOn n w)

theorem radialShootingInnerJet_hasDerivAt (n : ℕ) (w : RadialShootingDisk) (r : ℝ)
    (hr : r ∈ Ioo 0 innerBoundaryRadius) :
    HasDerivAt (radialShootingInnerJet n w)
      (radialStationaryField (n+radialInnerShootingThreshold) (radialShootingA n)
        (radialShootingB w) r (radialShootingInnerJet n w r)) r := by
  have hH := radialShootingInnerAmplitude_spec n w
  have hDA := hH.2.1 r (by simpa only [radialShootingInnerData_R] using hr)
  have hD := radialInnerComplex_deriv_differentiableAt innerBoundaryRadius
    (radialShootingA n) (by linarith [innerBoundaryRadius_bounds.1])
    (radialShootingInnerAmplitude n w) hH.1 (radialShootingInner_positive n w) r hr hDA
  rw [← radialShootingInnerComplex_eq] at hD
  have hh := ((radialShootingInner_differentiable n w r).hasDerivAt).prodMk hD.hasDerivAt
  apply hh.congr_deriv
  apply Prod.ext
  · rfl
  · have he := radialShootingInner_stationary n w r hr
    rw [← oddPowerNonlinearity_eq] at he
    dsimp only [radialStationaryField,radialShootingInnerJet]
    linear_combination he

end DefocusingNLS

end OAI
