import OAI.Analysis.Pureness.States.ScalarMatrixQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarCoefficientMatrixHom : CStarMatrix ι ι ℂ →⋆ₐ[ℂ] CStarMatrix ι ι A where
  toFun := CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ A).toNonUnitalStarAlgHom
  map_zero' := map_zero _
  map_one' := by
    ext i j
    change algebraMap ℂ A (if i=j then 1 else 0) = if i=j then 1 else 0
    split_ifs <;> simp
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  commutes' z := by
    ext i j
    change algebraMap ℂ A (if i=j then z else 0) = if i=j then algebraMap ℂ A z else 0
    split_ifs <;> simp

lemma scalarCoefficientMatrixHom_apply (z : CStarMatrix ι ι ℂ) (i j : ι) :
    scalarCoefficientMatrixHom (A := A) z i j = algebraMap ℂ A (z i j) := rfl

lemma scalarCoefficientMatrixHom_commute (x : A) (z : CStarMatrix ι ι ℂ) :
    Commute (scalarMatrixHom x) (scalarCoefficientMatrixHom z) := by
  change CStarMatrix.ofMatrix ((Matrix.diagonal (fun _ => x)) *
    (CStarMatrix.ofMatrix.symm z).map (algebraMap ℂ A)) =
    CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm z).map (algebraMap ℂ A) *
      Matrix.diagonal (fun _ => x))
  apply congrArg CStarMatrix.ofMatrix
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
  exact (Algebra.commutes (z i j) x).symm

lemma positiveQuasitrace_scalarMatrix_normalized
    (T : PositiveQuasitrace (CStarMatrix ι ι ℂ)) (i : ι)
    (hunit : T ⟨1,zero_le_one⟩ = 1) (z : CStarMatrix ι ι ℂ) :
    T.complexValue z = (Fintype.card ι : ℂ)⁻¹ * Matrix.trace (CStarMatrix.ofMatrix.symm z) := by
  have hu := positiveQuasitrace_scalarMatrix T i (⟨1,zero_le_one⟩ : Positive ℂ)
  have he : Positive.map scalarMatrixHom.toNonUnitalStarAlgHom (⟨1,zero_le_one⟩ : Positive ℂ) =
      (⟨1,zero_le_one⟩ : Positive (CStarMatrix ι ι ℂ)) := Subtype.ext (map_one scalarMatrixHom)
  rw [he,hunit] at hu
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    have : Nonempty ι := ⟨i⟩
    exact_mod_cast Fintype.card_ne_zero
  have hv : T (Positive.map (matrixCorner i) ⟨1,zero_le_one⟩) = (Fintype.card ι : ℝ)⁻¹ := by
    apply mul_left_cancel₀ hn
    rw [← hu,mul_inv_cancel₀ hn]
  rw [positiveQuasitrace_scalarMatrix_complex T i z,hv]
  push_cast
  ring

theorem positiveQuasitrace_scalarCoefficientMatrix
    (T : PositiveQuasitrace (CStarMatrix ι ι A)) (i : ι)
    (hunit : T ⟨1,zero_le_one⟩ = 1) (z : CStarMatrix ι ι ℂ) :
    T.complexValue (scalarCoefficientMatrixHom z) =
      (Fintype.card ι : ℂ)⁻¹ * Matrix.trace (CStarMatrix.ofMatrix.symm z) := by
  let P := T.comap (scalarCoefficientMatrixHom (A := A) (ι := ι)).toNonUnitalStarAlgHom
  have hp : P ⟨1,zero_le_one⟩ = 1 := by
    change T (Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom ⟨1,zero_le_one⟩) = 1
    have he : Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom (⟨1,zero_le_one⟩ : Positive (CStarMatrix ι ι ℂ)) =
        (⟨1,zero_le_one⟩ : Positive (CStarMatrix ι ι A)) := Subtype.ext (map_one scalarCoefficientMatrixHom)
    rw [he,hunit]
  exact (T.comap_complexValue (scalarCoefficientMatrixHom (A := A) (ι := ι)).toNonUnitalStarAlgHom z).symm.trans
    (positiveQuasitrace_scalarMatrix_normalized P i hp z)
end CuntzPureness

end

end OAI
