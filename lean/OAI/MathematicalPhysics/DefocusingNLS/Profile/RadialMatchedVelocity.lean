import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedFluxIntegral

namespace OAI

/-! The mass-average velocity formula for the actual matched profile. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedProfile_deriv_eq_inner (n : ℕ) (z : ProfileMatchingBall)
    (r : ℝ) (hr : r < innerBoundaryRadius) :
    deriv (radialMatchedProfile n z) r=
      deriv (radialShootingInnerComplex n (profileMatchingParameter z)) r := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Iio_mem_nhds hr] with t ht
  exact ite_eq_left ht.le

theorem radialMatchedProfile_derivative_continuousOn (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) :
    ContinuousOn (deriv (radialMatchedProfile n z)) (Icc 0 R) := by
  intro r hr
  rcases hr.1.eq_or_lt with he | hp
  · subst r
    have hB : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
    have hI := radialShootingInner_derivative_continuousOn n (profileMatchingParameter z)
      0 (show (0 : ℝ) ∈ Icc 0 innerBoundaryRadius from ⟨le_rfl,hB.le⟩)
    have hN : Icc (0 : ℝ) innerBoundaryRadius ∈ nhdsWithin 0 (Icc 0 R) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hB)] with t ht htB
      exact ⟨ht.1,htB.le⟩
    apply (hI.mono_of_mem_nhdsWithin hN).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hB)] with t ht
      exact radialMatchedProfile_deriv_eq_inner n z t ht
    · exact radialMatchedProfile_deriv_eq_inner n z 0 hB
  · have hs := ((radialMatchedProfile_contDiffOn n z hX hz) r hp).contDiffAt
      (Ioi_mem_nhds hp)
    exact (hs.derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt

theorem radialMatchedWeightedFlux_average (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R) :
    radialWeightedFlux (radialMatchedProfile n z) R=
      (6-2*radialShootingA n)*R*
        radialAverage (fun t => Complex.normSq (radialMatchedProfile n z t)) R := by
  apply radialWeightedFlux_average (n+radialInnerShootingThreshold)
    (radialShootingA n) (radialShootingB (profileMatchingParameter z)) R hR
  · exact (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
  · exact radialMatchedProfile_derivative_continuousOn n z hX hz R
  · intro r hr
    exact radialMatchedProfile_differentiable n z hX hz r
  · intro r hr
    have hs := ((radialMatchedProfile_contDiffOn n z hX hz) r hr.1).contDiffAt
      (Ioi_mem_nhds hr.1)
    exact (hs.derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  · intro r hr
    exact radialMatchedProfile_stationary n z hX hz r hr.1

theorem radialMatchedVelocity_formula (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R) :
    R/2+2*(star (radialMatchedProfile n z R)*deriv (radialMatchedProfile n z) R).im /
      Complex.normSq (radialMatchedProfile n z R)=
      radialVelocity (6-2*radialShootingA n) (fun r => ‖radialMatchedProfile n z r‖) R := by
  have hN : Complex.normSq (radialMatchedProfile n z R) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (radialMatchedProfile_ne_zero n z hX R hR.le)).ne'
  have hF := radialMatchedWeightedFlux_average n z hX hz R hR
  unfold radialVelocity radialVelocityRatio
  simp only [Complex.sq_norm]
  dsimp only [radialWeightedFlux] at hF
  field_simp [hN]
  nlinarith [hF]

end DefocusingNLS

end OAI
