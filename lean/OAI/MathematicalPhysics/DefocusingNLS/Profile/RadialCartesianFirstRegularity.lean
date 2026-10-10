import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingSquare
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSmooth
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! First Cartesian regularity of the actual matched profile, including the origin. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def radialMatchedCartesian (n : ℕ) (z : ProfileMatchingBall) (y : E) : ℂ :=
  radialMatchedProfile n z ‖y‖

theorem radialMatchedCartesian_contDiff_one (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) : ContDiff ℝ 1 (radialMatchedCartesian n z) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y=0
  · subst y
    have hR : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
    have hq := radialShootingSquare_contDiffOn_one n (profileMatchingParameter z)
    have h0 : (0 : ℝ) ∈ Icc 0 (innerBoundaryRadius^2) := ⟨le_rfl,sq_nonneg _⟩
    have hn : ContDiffWithinAt ℝ 1 (fun y : E => ‖y‖^2)
        (Metric.ball 0 innerBoundaryRadius) 0 := (contDiff_norm_sq ℝ).contDiffWithinAt
    have hm : MapsTo (fun y : E => ‖y‖^2) (Metric.ball 0 innerBoundaryRadius)
        (Icc 0 (innerBoundaryRadius^2)) := by
      intro y hy
      have hyl : ‖y‖ < innerBoundaryRadius := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      exact ⟨sq_nonneg _,by nlinarith [norm_nonneg y]⟩
    have hqc : ContDiffWithinAt ℝ 1
        (fun y : E => radialSquareProfile (radialShootingInnerComplex n (profileMatchingParameter z))
          (‖y‖^2)) (Metric.ball 0 innerBoundaryRadius) 0 := by
      have hq0 : ContDiffWithinAt ℝ 1
          (radialSquareProfile (radialShootingInnerComplex n (profileMatchingParameter z)))
          (Icc 0 (innerBoundaryRadius^2)) (‖(0 : E)‖^2) := by simpa using hq 0 h0
      simpa only [Function.comp_def] using hq0.comp 0 hn hm
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
    exact (hc.of_le (by norm_num)).comp y (contDiffAt_norm ℝ hy)

end DefocusingNLS

end OAI
