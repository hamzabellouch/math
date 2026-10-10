import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentRepresentationProducts
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! # Uniformly vanishing products in a nilpotent matrix representation -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {m : ℕ}

theorem exists_vanishing_matrix_products_of_pointwise_nilpotent
    (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) (hj : ∀ x, IsNilpotent (j x)) :
    ∃ c : ℕ, ∀ l : List L, c ≤ l.length → (l.map j).prod = 0 := by
  let E : Matrix (Fin m) (Fin m) ℝ ≃ₐ[ℝ] Module.End ℝ (Fin m → ℝ) :=
    Matrix.toLinAlgEquiv'
  let k : L →ₗ⁅ℝ⁆ Module.End ℝ (Fin m → ℝ) := E.toLieEquiv.toLieHom.comp j
  have hk (x : L) : IsNilpotent (k x) := (hj x).map E.toRingHom
  obtain ⟨c, hc⟩ := exists_vanishing_products_of_pointwise_nilpotent k hk
  refine ⟨c, fun l hl => ?_⟩
  apply E.injective
  rw [map_zero, map_list_prod]
  have heq : (l.map j).map E = l.map k := by
    rw [List.map_map]
    rfl
  rw [heq]
  exact hc l hl

end PolycyclicRecognition

end

end OAI
