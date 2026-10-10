import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerDeformation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorDeformation

namespace OAI

/-! Uniform positive radial deformation for the actual matched profiles. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_uniform_deformation :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ r : ℝ, 0 ≤ r →
        c ≤ deriv (radialMatchedVelocity n z) r ∧
        c ≤ radialVelocityRatio (6-2*radialShootingA n)
          (fun t => ‖radialMatchedProfile n z t‖) r := by
  obtain ⟨c,hc,hext⟩ := radialMatched_uniform_exterior_deformation
  refine ⟨min c (3/10),lt_min hc (by norm_num),?_⟩
  filter_upwards [hext] with n hn z hX hz r hr
  by_cases hi : r ≤ innerBoundaryRadius
  · have hh := radialMatched_inner_deformation n z hX hz r ⟨hr,hi⟩
    exact ⟨(min_le_right _ _).trans hh.1,(min_le_right _ _).trans hh.2⟩
  · have hrb : innerBoundaryRadius < r := lt_of_not_ge hi
    have hp : 0 < r := lt_of_lt_of_le (by linarith [innerBoundaryRadius_bounds.1]) hrb.le
    have hh := hn z hX hz r hrb
    have hw : radialMatchedVelocity n z r/r=
        radialVelocityRatio (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖) r := by
      dsimp [radialMatchedVelocity,radialVelocity]
      exact mul_div_cancel_left₀ _ hp.ne'
    rw [hw] at hh
    exact ⟨(min_le_left _ _).trans hh.2,(min_le_left _ _).trans hh.1⟩

end DefocusingNLS

end OAI
