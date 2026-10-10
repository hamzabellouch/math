import OAI.Analysis.Pureness.States.QuotientMatrixCornerLift
import OAI.Analysis.Pureness.Stabilization.MatrixEntries

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma matrixInclusion_single {n m : ℕ} (h : n ≤ m) (i j : Fin n) (a : A) :
    matrixInclusion h (singleMatrix i j a)=singleMatrix (Fin.castLE h i) (Fin.castLE h j) a := by
  apply CStarMatrix.ext
  intro p q
  rw [matrixInclusion_entry]
  change (if hp : p.val<n then if hq : q.val<n then
    (if i=⟨p.val,hp⟩ ∧ j=⟨q.val,hq⟩ then a else 0) else 0 else 0) =
      if Fin.castLE h i=p ∧ Fin.castLE h j=q then a else 0
  simp only [Fin.ext_iff,Fin.val_castLE]
  split_ifs <;> simp_all <;> omega

variable {D E K : Type*} [CStarAlgebra D]
  [CStarAlgebra E] [CStarAlgebra K]

theorem matrixCornerLift_inclusion_natural {n m : ℕ} (h : n ≤ m)
    (φ : D →⋆ₙₐ[ℂ] E) (ψ : D →⋆ₙₐ[ℂ] K) (χ : E →⋆ₙₐ[ℂ] K)
    (v : Fin n → E) (w : Fin m → K)
    (hv : ∀ i j, star (v i)*v j=if i=j then φ 1 else 0)
    (hw : ∀ i j, star (w i)*w j=if i=j then ψ 1 else 0)
    (hc : ∀ x, χ (φ x)=ψ x) (hl : ∀ i, χ (v i)=w (Fin.castLE h i))
    (M : FinMatrix D n) :
    χ (matrixCornerLift φ v hv M)=matrixCornerLift ψ w hw (matrixInclusion h M) := by
  nth_rw 1 [matrix_eq_sum_single M]
  nth_rw 2 [matrix_eq_sum_single M]
  simp only [map_sum,matrixInclusion_single]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change χ (matrixCornerLift φ v hv (singleMatrix i j (M i j))) =
    matrixCornerLift ψ w hw (singleMatrix (Fin.castLE h i) (Fin.castLE h j) (M i j))
  simp only [singleMatrix,matrixCornerLift_single]
  simp only [matrixCornerTerm,map_mul,map_star,hc,hl]
end CuntzPureness

end

end OAI
