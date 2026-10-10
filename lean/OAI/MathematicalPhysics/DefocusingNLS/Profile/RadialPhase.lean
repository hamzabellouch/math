import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityLocal

namespace OAI

/-! Integration of the nonsingular radial phase velocity. -/

open MeasureTheory
namespace DefocusingNLS

theorem continuous_radialVelocity (c : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r, A r ≠ 0) : Continuous (radialVelocity c A) := by
  exact continuous_id.mul
    ((continuous_const.mul (continuous_radialAverage (fun r => (A r)^2) (hA.pow 2))).div
      (hA.pow 2) (fun r => pow_ne_zero 2 (hAz r)))

noncomputable def radialPhase (c : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, (radialVelocity c A t-t/2)/2

theorem radialPhase_origin (c : ℝ) (A : ℝ → ℝ) : radialPhase c A 0=0 := by
  simp only [radialPhase,intervalIntegral.integral_same]

theorem radialPhase_hasDerivAt (c : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r, A r ≠ 0) (r : ℝ) :
    HasDerivAt (radialPhase c A) ((radialVelocity c A r-r/2)/2) r := by
  have hc : Continuous (fun t => (radialVelocity c A t-t/2)/2) :=
    ((continuous_radialVelocity c A hA hAz).sub (continuous_id.div_const 2)).div_const 2
  exact (hc.integral_hasStrictDerivAt 0 r).hasDerivAt

theorem radialPhase_differentiable (c : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r, A r ≠ 0) : Differentiable ℝ (radialPhase c A) :=
  fun r => (radialPhase_hasDerivAt c A hA hAz r).differentiableAt

theorem radialPhase_deriv_hasDerivAt (c d : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r, A r ≠ 0) (r : ℝ) (hr : r ≠ 0) (hdA : HasDerivAt A d r) :
    HasDerivAt (deriv (radialPhase c A))
      ((c-11*radialVelocityRatio c A r-2*radialVelocity c A r*d/A r-1/2)/2) r := by
  have he : deriv (radialPhase c A)=fun t => (radialVelocity c A t-t/2)/2 :=
    funext (fun t => (radialPhase_hasDerivAt c A hA hAz t).deriv)
  rw [he]
  exact ((radialVelocity_hasDerivAt_local c d A hA r hr (hAz r) hdA).sub
    ((hasDerivAt_id r).div_const 2)).div_const 2

end DefocusingNLS

end OAI
