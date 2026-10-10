import Mathlib
import OAI.Analysis.Commutator.MatrixFlatten
import OAI.Analysis.Commutator.BlockDilationBound

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixGNS

open OperatorAmplification CyclicColumns

lemma norm_conjugation {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (U : K ≃ₗᵢ[ℂ] L) (T : K →L[ℂ] K) : ‖U.conjStarAlgEquiv T‖=‖T‖ :=
  StarAlgEquiv.norm_map U.conjStarAlgEquiv T

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixFlattenRepresentationIndexDecidableEq : DecidableEq ι := Classical.decEq ι

local instance matrixFlattenRepresentationCopiesDecidableEq : DecidableEq κ := Classical.decEq κ

def flattenCopies : SumSpace (H:=SumSpace (H:=H) ι) κ ≃ₗᵢ[ℂ] SumSpace (H:=H) (κ×ι) where
  toFun v := WithLp.toLp 2 (fun p => v p.1 p.2)
  invFun v := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => v (i,j)))
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := by ext p; rfl
  map_smul' z v := by ext p; rfl
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]

omit [CompleteSpace H] in
@[simp] lemma flattenCopies_apply (v : SumSpace (H:=SumSpace (H:=H) ι) κ) (p : κ×ι) :
    flattenCopies ι κ v p=v p.1 p.2 := rfl

omit [CompleteSpace H] in
@[simp] lemma flattenCopies_symm_apply (v : SumSpace (H:=H) (κ×ι)) (i : κ) (j : ι) :
    (flattenCopies (H:=H) ι κ).symm v i j=v (i,j) := rfl

lemma flattenCopies_diagonal (Y : H →L[ℂ] H) :
    (flattenCopies (H:=H) ι κ).conjStarAlgEquiv
      (diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y))=diagonal (H:=H) (κ×ι) Y := by
  ext v p
  rfl

lemma flattenCopies_matrix (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    (flattenCopies (H:=H) ι κ).conjStarAlgEquiv
      (matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X)=matrixRepresentation ρ (flatten ι κ X) := by
  ext v p
  change matrixAction (fun i j => matrixRepresentation ρ (X i j))
    ((flattenCopies (H:=H) ι κ).symm v) p.1 p.2=
      matrixAction (fun i j => ρ (flatten ι κ X i j)) v p
  simp only [matrixAction_apply,WithLp.ofLp_sum,Finset.sum_apply,
    Fintype.sum_prod_type,flatten_apply]
  apply Finset.sum_congr rfl
  intro j _
  change matrixAction (fun i k => ρ (X p.1 j i k))
    ((flattenCopies (H:=H) ι κ).symm v j) p.2=_
  simp only [matrixAction_apply,flattenCopies_symm_apply]

lemma flattenCopies_commutator_norm (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    ‖diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)*
        matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X-
      matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X*
        diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)‖=
    ‖diagonal (H:=H) (κ×ι) Y*matrixRepresentation ρ (flatten ι κ X)-
        matrixRepresentation ρ (flatten ι κ X)*diagonal (H:=H) (κ×ι) Y‖ := by
  have hn := norm_conjugation (flattenCopies (H:=H) ι κ)
    (diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)*
        matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X-
      matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X*
        diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y))
  simpa only [map_sub,map_mul,flattenCopies_diagonal,flattenCopies_matrix] using hn.symm

theorem flatBalanced_commutator_dominates (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    ‖diagonal (H:=H) ι Y*matrixRepresentation ρ X-
      matrixRepresentation ρ X*diagonal (H:=H) ι Y‖ ≤
    ‖diagonal (H:=H) ((Fin 2)×ι) Y*
        matrixRepresentation ρ (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)-
      matrixRepresentation ρ (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)*
        diagonal (H:=H) ((Fin 2)×ι) Y‖ := by
  have h := balanced_symmetry_commutator_dominates (matrixRepresentation ρ) (diagonal (H:=H) ι Y) X
  rw [flattenCopies_commutator_norm] at h
  exact h

end Kadison.MatrixGNS

end

end
end

end OAI
