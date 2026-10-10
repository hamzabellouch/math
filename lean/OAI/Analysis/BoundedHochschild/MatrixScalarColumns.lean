import OAI.Analysis.BoundedHochschild.NestedMatrixAmplification

namespace OAI

/-! Diagonal copies of the proved isometry columns inside finite matrix
algebras. These supply the row estimates at every matrix level. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

/-- The unital diagonal embedding into a finite matrix algebra. -/
def matrixScalarHom (k : ℕ) : M →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) M where
  toFun a := CStarMatrix.ofMatrix (Matrix.scalar (Fin k) a)
  map_zero' := (Matrix.scalar (Fin k)).map_zero
  map_one' := (Matrix.scalar (Fin k)).map_one
  map_add' a b := (Matrix.scalar (Fin k)).map_add a b
  map_mul' a b := (Matrix.scalar (Fin k)).map_mul a b
  commutes' _ := rfl
  map_star' a := by
    ext i j
    change (if i = j then star a else 0) = star (if j = i then a else 0)
    by_cases h : i = j
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false, star_zero]

@[simp] lemma matrixScalarHom_apply (k : ℕ) (a : M) (i j : Fin k) :
    matrixScalarHom k a i j = if i = j then a else 0 := rfl

variable [PartialOrder M] [StarOrderedRing M]

def matrixScalarPartialIso (k : ℕ) (v : PartialIso M) :
    PartialIso (CStarMatrix (Fin k) (Fin k) M) where
  val := matrixScalarHom k (v : M)
  mul_star_mul := by
    simpa only [map_mul, map_star] using congrArg (matrixScalarHom k) v.mul_star_mul

@[simp] lemma matrixScalarPartialIso_initial (k : ℕ) (v : PartialIso M) :
    (matrixScalarPartialIso k v).initial = matrixScalarHom k v.initial := by
  simp only [PartialIso.initial, matrixScalarPartialIso, map_mul, map_star]

@[simp] lemma matrixScalarPartialIso_final (k : ℕ) (v : PartialIso M) :
    (matrixScalarPartialIso k v).final = matrixScalarHom k v.final := by
  simp only [PartialIso.final, matrixScalarPartialIso, map_mul, map_star]

lemma matrixScalar_columns {n : ℕ} (k : ℕ) (c : Fin n → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) :
    (∀ i, (matrixScalarPartialIso k (c i)).initial = 1) ∧
      (∀ i j, i ≠ j → (matrixScalarPartialIso k (c i)).final *
        (matrixScalarPartialIso k (c j)).final = 0) ∧
      ∑ i, (matrixScalarPartialIso k (c i)).final = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [matrixScalarPartialIso_initial, hi, map_one]
  · intro i j hij
    rw [matrixScalarPartialIso_final, matrixScalarPartialIso_final, ← map_mul,
      ho i j hij, map_zero]
  · simp only [matrixScalarPartialIso_final, ← map_sum, hs, map_one]

end BoundedHochschild.KadisonRingrose

end

end OAI
