import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityBounds

namespace OAI

/-! Continuity of the actual nonsingular potential on positive amplitudes. -/

namespace DefocusingNLS

theorem continuous_radialVelocityRatio (c : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r, A r ≠ 0) : Continuous (radialVelocityRatio c A) :=
  (continuous_const.mul (continuous_radialAverage (fun t => (A t)^2) (hA.pow 2))).div
    (hA.pow 2) (fun r => pow_ne_zero 2 (hAz r))

theorem continuous_radialAmplitudePotential (c b : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAz : ∀ r, A r ≠ 0) : Continuous (radialAmplitudePotential c b A) := by
  unfold radialAmplitudePotential
  exact (continuous_const.add ((continuous_id.pow 2).div_const 16)).sub
    (((continuous_id.pow 2).mul ((continuous_radialVelocityRatio c A hA hAz).pow 2)).div_const 4)

end DefocusingNLS

end OAI
