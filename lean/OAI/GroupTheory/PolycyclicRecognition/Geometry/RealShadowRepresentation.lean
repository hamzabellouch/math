import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowSplit
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveSizeTriangularRepresentation

namespace OAI

/-! # A faithful triangular representation of the real shadow -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The nilpotent weight kernel acts by nilpotent matrices in a faithful
real triangular representation of the modified algebra. -/
theorem exists_realShadow_triangularRepresentation :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : CartanRealShadow T H →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
        Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
        ∀ x ∈ realShadowKernel T H, IsNilpotent (j x) := by
  let := cartanRealShadow_solvable T H
  let := realShadowKernel_nilpotent T H
  obtain ⟨n, ⟨A⟩⟩ := nonempty_cartanRealShadow_triangularAdjoint T H
  obtain ⟨m, hm, j, hj, hu, hn⟩ := exists_positive_faithful_triangular_representation A
  refine ⟨m, hm, j, hj, hu, fun x hx => hn x ?_⟩
  exact A.nilpotent_ideal_le_kernelIdeal (realShadowKernel T H) hx

end PolycyclicRecognition

end

end OAI
