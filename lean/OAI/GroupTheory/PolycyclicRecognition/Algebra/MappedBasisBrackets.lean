import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateLieBrackets

namespace OAI

/-! # Coordinate bracket preservation under a Lie-algebra identification -/

namespace PolycyclicRecognition

open Module

/-- Mapping both the vectors and their basis leaves the coordinate Lie
bracket unchanged. -/
theorem basisBracket_map_lieEquiv
    {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']
    {n : ℕ} (b : Basis (Fin n) ℝ L) (e : L ≃ₗ⁅ℝ⁆ L') :
    basisBracket (b.map e.toLinearEquiv) = basisBracket b := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [basisBracket_apply, Basis.map_equivFun]
  change b.equivFun (e.symm ⁅e (b.equivFun.symm x), e (b.equivFun.symm y)⁆) = _
  rw [← e.map_lie, e.symm_apply_apply]

end PolycyclicRecognition

end OAI
