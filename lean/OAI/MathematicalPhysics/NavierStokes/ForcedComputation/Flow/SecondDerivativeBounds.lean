import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveInterface

namespace OAI

/-! A computable operator bound for the second derivative of a finite
velocity expression. This is the coefficient needed in the planar second
variational equation. -/

noncomputable section
namespace ShearFlows.VelocityExpr
open scoped BigOperators NNReal

def secondModulusBound (c : VelocityExpr) : ℕ :=
  ∑ j : Fin 4, c.modulusBound [j]

theorem fderiv_lipschitz_bound {c : VelocityExpr} (hc : c.Valid)
    (x y : SpaceTime) :
    ‖fderiv ℝ c.val x - fderiv ℝ c.val y‖ ≤
      (c.secondModulusBound : ℝ) * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  conv_lhs => rw [← spaceTimeDirections_sum v]
  rw [map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j : Fin 4, ‖(fderiv ℝ c.val x - fderiv ℝ c.val y)
        (timeSpaceCoord j v • spaceTimeDirection j)‖) ≤
        ∑ j : Fin 4, ‖v‖ * ((c.modulusBound [j] : ℝ) * ‖x - y‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul]
      exact mul_le_mul (timeSpaceCoord_norm j v) (lipschitz_bound hc [j] x y)
        (norm_nonneg _) (norm_nonneg _)
    _ = ((c.secondModulusBound : ℝ) * ‖x - y‖) * ‖v‖ := by
      simp only [secondModulusBound, Nat.cast_sum]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem fderiv_lipschitz {c : VelocityExpr} (hc : c.Valid) :
    LipschitzWith (c.secondModulusBound : ℝ≥0) (fderiv ℝ c.val) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_natCast] using fderiv_lipschitz_bound hc x y

theorem second_fderiv_bound {c : VelocityExpr} (hc : c.Valid) (x : SpaceTime) :
    ‖fderiv ℝ (fderiv ℝ c.val) x‖ ≤ (c.secondModulusBound : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ (fderiv_lipschitz hc)

end ShearFlows.VelocityExpr

end

end OAI
