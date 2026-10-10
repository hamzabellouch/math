import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealNilpotentSpanningOperators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentMatrixProducts

namespace OAI

/-! # Nilpotence of a matrix representation from spanning generators -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing.IsNilpotent L] {m : ℕ}

theorem matrix_nilpotent_of_spanning_set
    (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (S : Set L)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ x ∈ S, IsNilpotent (j x)) (x : L) :
    IsNilpotent (j x) := by
  let E : Matrix (Fin m) (Fin m) ℝ ≃ₐ[ℝ] Module.End ℝ (Fin m → ℝ) := Matrix.toLinAlgEquiv'
  let k : L →ₗ⁅ℝ⁆ Module.End ℝ (Fin m → ℝ) := E.toLieEquiv.toLieHom.comp j
  let := LieRingModule.compLieHom (Fin m → ℝ) k
  let := LieModule.compLieHom (Fin m → ℝ) k
  have hk (y : L) (hy : y ∈ S) : IsNilpotent (LieModule.toEnd ℝ L (Fin m → ℝ) y) :=
    (h y hy).map E.toRingHom
  obtain ⟨c, hc⟩ := real_nilpotent_operators_of_spanning_set S hS hk x
  refine ⟨c, E.injective ?_⟩
  rw [map_pow, map_zero]
  exact hc

theorem matrix_products_vanish_of_spanning_nilpotents
    (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (S : Set L)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ x ∈ S, IsNilpotent (j x)) :
    ∃ c : ℕ, ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 :=
  exists_vanishing_matrix_products_of_pointwise_nilpotent j
    (matrix_nilpotent_of_spanning_set j S hS h)

end PolycyclicRecognition

end

end OAI
