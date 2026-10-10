import OAI.Geometry.ProjectionBody.GraphJacobian
import OAI.Geometry.ProjectionBody.HyperplaneJacobian
import OAI.Geometry.ProjectionBody.Definitions
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- Projection of a graph chart cancels the length of its unnormalized normal. -/
theorem graphProjection_normDet {n : ℕ} (i : Fin (n + 1)) (a : E n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (graphLinear i a)).normDet =
      |⟪graphNormal i a, u⟫| := by
  let w := graphNormal i a
  have hw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr (graphNormal_ne_zero i a)
  let v := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hw]
  have hmem (x : E n) : ⟪v, graphLinear i a x⟫ = 0 := by
    rw [show v = ‖w‖⁻¹ • graphNormal i a from rfl, real_inner_smul_left,
      graphNormal_inner_graphLinear, mul_zero]
  change ((perpendicularTo u).starProjection.toLinearMap.comp (graphLinear i a)).normDet = _
  rw [normDet_project_comp (graphLinear i a) hv hu hmem (by simp),
    graphLinear_normDet]
  change |⟪‖w‖⁻¹ • w, u⟫| * ‖w‖ = |⟪w, u⟫|
  rw [real_inner_smul_left, abs_mul, abs_inv, abs_of_nonneg (norm_nonneg w)]
  field_simp [hw]

theorem coordinateProjection_normDet {n : ℕ} (i : Fin (n + 1))
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (insertZero i).toLinearMap).normDet = |u i| := by
  have hL : graphLinear i 0 = (insertZero i).toLinearMap := by
    ext x j
    simp [graphLinear]
  have h := graphProjection_normDet i 0 hu
  simpa [hL, graphNormal, EuclideanSpace.inner_single_left] using h

end ProjectionCounterexample

end

end OAI
