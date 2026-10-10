import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSquareSmooth
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianFirstRegularity

namespace OAI

/-! Full smoothness of the actual matched Cartesian profile, including its origin. -/

open scoped ContDiff
open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialShootingSquare_contDiffOn (n : ℕ) (w : RadialShootingDisk) :
    ContDiffOn ℝ ∞ (radialSquareProfile (radialShootingInnerComplex n w))
      (Icc 0 (innerBoundaryRadius^2)) :=
  radialSquareProfile_contDiffOn _ _ _ innerBoundaryRadius
    (by linarith [innerBoundaryRadius_bounds.1]) _ (radialShootingInner_differentiable n w)
    (fun r hr => radialShootingInner_derivative_average n w r hr.1 hr.2)

theorem radialMatchedCartesian_contDiff (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : ContDiff ℝ ∞ (radialMatchedCartesian n z) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y=0
  · subst y
    have hR : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
    have hq := radialShootingSquare_contDiffOn n (profileMatchingParameter z)
    have h0 : (0 : ℝ) ∈ Icc 0 (innerBoundaryRadius^2) := ⟨le_rfl,sq_nonneg _⟩
    have hn : ContDiffWithinAt ℝ ∞ (fun y : E => ‖y‖^2)
        (Metric.ball 0 innerBoundaryRadius) 0 := (contDiff_norm_sq ℝ).contDiffWithinAt
    have hm : MapsTo (fun y : E => ‖y‖^2) (Metric.ball 0 innerBoundaryRadius)
        (Icc 0 (innerBoundaryRadius^2)) := by
      intro y hy
      have hyl : ‖y‖ < innerBoundaryRadius := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      exact ⟨sq_nonneg _,by nlinarith [norm_nonneg y]⟩
    have hq0 : ContDiffWithinAt ℝ ∞
        (radialSquareProfile (radialShootingInnerComplex n (profileMatchingParameter z)))
        (Icc 0 (innerBoundaryRadius^2)) (‖(0 : E)‖^2) := by simpa using hq 0 h0
    have hqc := hq0.comp 0 hn hm
    have he : (fun y : E => radialSquareProfile (radialShootingInnerComplex n (profileMatchingParameter z))
        (‖y‖^2)) =ᶠ[nhds (0 : E)] radialMatchedCartesian n z := by
      filter_upwards [Metric.ball_mem_nhds (0 : E) hR] with y hy
      have hyl : ‖y‖ ≤ innerBoundaryRadius :=
        (by simpa only [Metric.mem_ball,dist_zero_right] using hy : ‖y‖ < innerBoundaryRadius).le
      simp only [radialSquareProfile,Real.sqrt_sq (norm_nonneg y),radialMatchedCartesian,
        radialMatchedProfile,ite_eq_left hyl]
    exact (hqc.contDiffAt (Metric.ball_mem_nhds (0 : E) hR)).congr_of_eventuallyEq he.symm
  · have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hc := ((radialMatchedProfile_contDiffOn n z hX hz) ‖y‖ hnorm).contDiffAt
      (Ioi_mem_nhds hnorm)
    exact hc.comp y (contDiffAt_norm ℝ hy)

theorem exists_smooth_radialMatchedProfile :
    ∀ᶠ n in atTop, ∃ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) ∧
      radialMatchingMap n z=0 ∧
      ContDiff ℝ ∞ (radialMatchedCartesian n z) ∧
      (∀ y : E, radialMatchedCartesian n z y ≠ 0) ∧
      0 < (radialMatchedCartesian n z 0).re ∧ (radialMatchedCartesian n z 0).im=0 := by
  have hs : Tendsto (fun n : ℕ => n+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  filter_upwards [exists_radialMatchingMap_zero,hs.eventually radialShootingExterior_exists] with n hn hX
  obtain ⟨z,hz⟩ := hn
  refine ⟨z,hX z,hz,radialMatchedCartesian_contDiff n z (hX z) hz,?_,?_⟩
  · intro y
    exact radialMatchedProfile_ne_zero n z (hX z) ‖y‖ (norm_nonneg y)
  · simpa only [radialMatchedCartesian,norm_zero] using radialMatchedProfile_origin n z

end DefocusingNLS

end OAI
