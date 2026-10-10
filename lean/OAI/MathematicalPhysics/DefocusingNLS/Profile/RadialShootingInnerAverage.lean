import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexAverage
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerJet

namespace OAI

/-! The actual inner profile obeys the regular complex derivative integral. -/

open Set
namespace DefocusingNLS

theorem radialShootingInner_derivative_average (n : ℕ) (w : RadialShootingDisk)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ innerBoundaryRadius) :
    deriv (radialShootingInnerComplex n w) r=(r : ℂ)*
      radialComplexAverage (n+radialInnerShootingThreshold) (radialShootingA n)
        (radialShootingB w) (radialShootingInnerComplex n w) r := by
  apply radialComplexDerivative_average _ _ _ r hr
  · exact (radialShootingInner_differentiable n w).continuous.continuousOn
  · exact (radialShootingInner_derivative_continuousOn n w).mono
      (fun _ ht => ⟨ht.1,ht.2.trans hrR⟩)
  · intro t ht
    exact (radialShootingInnerJet_hasDerivAt n w t ⟨ht.1,lt_of_lt_of_le ht.2 hrR⟩).differentiableAt.snd
  · intro t ht
    simpa only [oddPowerNonlinearity_eq] using
      radialShootingInner_stationary n w t ⟨ht.1,lt_of_lt_of_le ht.2 hrR⟩

theorem radialShootingInner_derivative_zero (n : ℕ) (w : RadialShootingDisk) :
    deriv (radialShootingInnerComplex n w) 0=0 := by
  have hH := radialShootingInnerAmplitude_spec n w
  have hh := radial_coupled_polar_deriv (radialShootingInnerData n w)
    (radialShootingInnerAmplitude n w) hH 0
    ⟨le_rfl,by rw [radialShootingInnerData_R]; linarith [innerBoundaryRadius_bounds.1]⟩
  rw [radialShootingInnerData_R] at hh
  change deriv (radialShootingInnerComplex n w) 0=_ at hh
  rw [hh]
  simp [radialPolarSlope,hH.2.2.2.1.deriv,radialPhaseSpeed,radialVelocity]

end DefocusingNLS

end OAI
