import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialContinuity

namespace OAI

/-! Continuity of the actual potential only needs positivity on the inner interval. -/

open Set
namespace DefocusingNLS

theorem continuousOn_radialAmplitudePotential (c b R : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r ∈ Icc 0 R, A r ≠ 0) :
    ContinuousOn (radialAmplitudePotential c b A) (Icc 0 R) := by
  have hρ : ContinuousOn (radialVelocityRatio c A) (Icc 0 R) :=
    (continuous_const.mul (continuous_radialAverage (fun t => (A t)^2) (hA.pow 2))).continuousOn.div
      (hA.pow 2).continuousOn (fun r hr => pow_ne_zero 2 (hAz r hr))
  exact (continuous_const.add ((continuous_id.pow 2).div_const 16)).continuousOn.sub
    (((continuous_id.pow 2).continuousOn.mul (hρ.pow 2)).div_const 4)

end DefocusingNLS

end OAI
