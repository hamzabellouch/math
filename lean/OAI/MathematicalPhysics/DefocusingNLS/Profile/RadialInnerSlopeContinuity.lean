import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingInnerEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledComplexParameter

namespace OAI

/-! Continuity of the actual inner radial derivative up to the matching boundary. -/

open Set
namespace DefocusingNLS

theorem radialShootingInner_derivative_continuousOn (n : ℕ) (w : RadialShootingDisk) :
    ContinuousOn (deriv (radialShootingInnerComplex n w)) (Icc 0 innerBoundaryRadius) := by
  let P := radialShootingInnerData n w
  let H := radialShootingInnerAmplitude n w
  have hH := radialShootingInnerAmplitude_spec n w
  have hD := (radial_inner_integral_and_continuity P H hH).2
  rw [radialShootingInnerData_R] at hD
  have hR : 0 ≤ innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  have hn (r : ℝ) (hr : r ∈ Icc 0 innerBoundaryRadius) : H r ≠ 0 :=
    (radialShootingInner_positive n w r hr).ne'
  have hHC : Continuous H := hH.1.continuous
  have hB := radialClampedAmplitude_continuous innerBoundaryRadius H hHC
  have hBn (r : ℝ) : radialClampedAmplitude innerBoundaryRadius H r ≠ 0 :=
    hn _ (radialClamp_mem innerBoundaryRadius r hR)
  have hφ := (radialPhase_differentiable P.c _ hB hBn).continuous
  have hv := radial_phase_speed_continuousOn P.c innerBoundaryRadius H hR hHC hn
  have hc : ContinuousOn (radialPolarSlope H (deriv H) (radialPhaseSpeed P.c H)
      (radialPhase P.c (radialClampedAmplitude innerBoundaryRadius H))) (Icc 0 innerBoundaryRadius) := by
    unfold radialPolarSlope
    fun_prop
  apply hc.congr
  intro r hr
  have hh := radial_coupled_polar_deriv P H hH r (by
    simpa only [P,radialShootingInnerData_R] using hr)
  simpa only [P,H,radialShootingInnerData_R,radialShootingInnerComplex] using hh

end DefocusingNLS

end OAI
