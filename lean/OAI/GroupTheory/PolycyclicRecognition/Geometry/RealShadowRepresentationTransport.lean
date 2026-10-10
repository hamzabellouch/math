import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowRepresentation

namespace OAI

/-! # Transporting the faithful shadow representation to its geometric realization -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L K : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [LieRing K] [LieAlgebra ℝ K]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Only the target real-shadow algebra needs a finite-dimensionality instance. -/
theorem realShadow_triangularRepresentation_pullback (e : K ≃ₗ⁅ℝ⁆ CartanRealShadow T H) :
    ∃ m : ℕ, 0 < m ∧ ∃ j : K →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      ∀ x, e x ∈ realShadowKernel T H → IsNilpotent (j x) := by
  obtain ⟨m, hm, j, hj, hu, hn⟩ := exists_realShadow_triangularRepresentation T H
  exact ⟨m, hm, j.comp e.toLieHom, hj.comp e.injective,
    fun x => hu (e x), fun x hx => hn (e x) hx⟩

end PolycyclicRecognition

end

end OAI
