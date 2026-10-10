import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnconditionalNilpotentCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialUnipotentModel

namespace OAI

/-! # A faithful nilpotent matrix representation of a real nilpotent algebra

The coordinate model and its regular representation have both been constructed
without a published-input hypothesis. Engel gives a uniform product bound.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exists_faithful_nilpotent_representation (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) :
    ∃ (m c : ℕ) (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective j ∧ (∀ x, IsNilpotent (j x)) ∧
      ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hnil
  let := P
  obtain ⟨m, j, hj, hn⟩ := exists_faithful_nilpotent_matrixLieRepresentation (Module.finBasis ℝ L)
  obtain ⟨c, hc⟩ := exists_vanishing_matrix_products_of_pointwise_nilpotent j hn
  exact ⟨m, c, j, hj, hn, hc⟩

end PolycyclicRecognition

end

end OAI
