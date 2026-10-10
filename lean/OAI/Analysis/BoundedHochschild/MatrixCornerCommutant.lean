import OAI.Analysis.BoundedHochschild.PartialIsoCornerEquivalence
import OAI.Analysis.BoundedHochschild.TracialDecomposition

namespace OAI

/-! Explicit identification of a matrix diagonal corner with its commutant. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixSystems HochschildComparison HochschildCorners

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (E : MatrixSystem M n) (i : Fin n)

/-- The matrix coefficient map identifies a diagonal corner with the full
matrix commutant. Its inverse is multiplication by that diagonal projection. -/
def matrixCornerCommutantEquiv :
    PopaCorner.algebra (E.diagonal_proj i) ≃⋆ₐ[ℂ] E.commutant where
  toFun a := ⟨E.coefficient i i a, E.coefficient_mem i i a⟩
  invFun b := ⟨E.entry i i * (b : M), by
    constructor
    · rw [← mul_assoc, (E.diagonal_proj i).isIdempotentElem.eq]
    · rw [mul_assoc, (b.property i i).eq, ← mul_assoc,
        (E.diagonal_proj i).isIdempotentElem.eq]⟩
  left_inv a := by
    apply Subtype.ext
    change E.entry i i * E.coefficient i i (a : M) = (a : M)
    have hc := E.coefficient_corner i (a : M)
    rw [a.property.1, a.property.2] at hc
    calc
      _ = E.entry i i * E.coefficient i i (a : M) * E.entry i i := by
        rw [mul_assoc, (E.coefficient_mem i i (a : M) i i).eq,
          ← mul_assoc, (E.diagonal_proj i).isIdempotentElem.eq]
      _ = (a : M) := hc
  right_inv b := Subtype.ext (E.coefficient_of_commutant i b.property)
  map_mul' a b := by
    apply Subtype.ext
    change E.coefficient i i ((a : M) * (b : M)) =
      E.coefficient i i (a : M) * E.coefficient i i (b : M)
    rw [E.coefficient_mul, a.property.2]
  map_add' a b := by
    apply Subtype.ext
    change E.coefficient i i ((a : M) + (b : M)) =
      E.coefficient i i (a : M) + E.coefficient i i (b : M)
    simp only [MatrixSystem.coefficient, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' z a := by
    apply Subtype.ext
    change E.coefficient i i (z • (a : M)) = z • E.coefficient i i (a : M)
    simp only [MatrixSystem.coefficient, mul_smul_comm, smul_mul_assoc, Finset.smul_sum]
  map_star' a := Subtype.ext (E.coefficient_star i i (a : M)).symm

/-- An isometry identifies the whole algebra with its range corner. -/
def isometryCornerEquiv (v : PartialIso M) (hi : v.initial = 1) :
    M ≃⋆ₐ[ℂ] PopaCorner.algebra v.final_proj := by
  let hunit : M ≃⋆ₐ[ℂ] PopaCorner.algebra v.initial_proj :=
    { toFun := fun a => ⟨a, by
        change v.initial * a = a ∧ a * v.initial = a
        rw [hi, one_mul, mul_one]
        exact ⟨rfl, rfl⟩⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_star' := fun _ => rfl }
  exact hunit.trans (partialIsoCornerEquiv v)

end BoundedHochschild.KadisonRingrose

end

end OAI
