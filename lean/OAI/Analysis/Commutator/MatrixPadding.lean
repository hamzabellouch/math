import Mathlib
import OAI.Analysis.Commutator.HilbertPadding

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification CyclicColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixPaddingSourceDecidableEq : DecidableEq ι := Classical.decEq ι

local instance matrixPaddingComplementDecidableEq : DecidableEq κ := Classical.decEq κ

lemma leftCopies_adjoint_apply (v : SumSpace (H:=H) (ι⊕κ)) :
    (leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint v=
      WithLp.toLp 2 (fun i => v (Sum.inl i)) := by
  apply ext_inner_left ℂ
  intro w
  rw [adjoint_inner_right]
  simp [PiLp.inner_apply,Fintype.sum_sum_type]

def padMatrix : CStarMatrix ι ι A →⋆ₙₐ[ℂ] CStarMatrix (ι⊕κ) (ι⊕κ) A where
  toFun X := CStarMatrix.ofMatrix (Matrix.fromBlocks (fun i j => X i j) 0 0 0)
  map_zero' := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_add' X Y := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_smul' z X := by ext i j; cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_mul' X Y := by
    ext i j
    cases i <;> cases j <;>
      simp [CStarMatrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks]
  map_star' X := by
    ext i j
    cases i <;> cases j <;> simp [CStarMatrix.star_apply,Matrix.fromBlocks]

lemma norm_padMatrix_le (X : CStarMatrix ι ι A) : ‖padMatrix ι κ X‖ ≤ ‖X‖ :=
  NonUnitalStarAlgHom.norm_apply_le (padMatrix ι κ) X

lemma representation_padMatrix (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : CStarMatrix ι ι A) :
    matrixRepresentation ρ (padMatrix ι κ X)=
      extend (leftCopies (H:=H) ι κ) (matrixRepresentation ρ X) := by
  ext v i
  change matrixAction (fun i j => ρ (padMatrix ι κ X i j)) v i=
    leftCopies (H:=H) ι κ
      (matrixRepresentation ρ X ((leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint v)) i
  rw [leftCopies_adjoint_apply]
  cases i <;> simp [padMatrix,Fintype.sum_sum_type,matrixRepresentation,matrixAction_apply,Matrix.fromBlocks]

lemma diagonal_commutator_extend (Y : H →L[ℂ] H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    diagonal (H:=H) (ι⊕κ) Y*extend (leftCopies ι κ) T-
      extend (leftCopies ι κ) T*diagonal (H:=H) (ι⊕κ) Y=
        extend (leftCopies ι κ) (diagonal (H:=H) ι Y*T-T*diagonal (H:=H) ι Y) := by
  have h := extend_commutator (leftCopies (H:=H) ι κ) T (diagonal (H:=H) ι Y)
    (diagonal (H:=H) (ι⊕κ) Y) (leftCopies_diagonal ι κ Y) (adjoint_leftCopies_diagonal ι κ Y)
  have hn := congrArg Neg.neg h
  simpa only [neg_sub,extend,comp_sub,sub_comp] using hn

theorem matrix_padding_commutator_norm (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix ι ι A) :
    ‖diagonal (H:=H) (ι⊕κ) Y*matrixRepresentation ρ (padMatrix ι κ X)-
        matrixRepresentation ρ (padMatrix ι κ X)*diagonal (H:=H) (ι⊕κ) Y‖=
      ‖diagonal (H:=H) ι Y*matrixRepresentation ρ X-
        matrixRepresentation ρ X*diagonal (H:=H) ι Y‖ := by
  rw [representation_padMatrix,diagonal_commutator_extend,norm_extend]

end Kadison.HilbertPadding

end

end
end

end OAI
