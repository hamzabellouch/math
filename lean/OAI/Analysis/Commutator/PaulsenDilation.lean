import Mathlib
import OAI.Analysis.Commutator.HilbertMatrixCorner
import OAI.Analysis.Commutator.PaulsenExtension

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.Paulsen

open OperatorAmplification

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

variable [Nontrivial A] (f : A →ₗ[ℂ] (H →L[ℂ] H)) (hf : IsCompletelyContractive f)

def extension := Classical.choose (exists_unital_extension f hf)

lemma extension_one : extension f hf 1=1 := (Classical.choose_spec (exists_unital_extension f hf)).1

lemma extension_corner (a : A) :
    (single (Fin 2) 0).adjoint.comp ((extension f hf (ChoiGNS.entry 0 1 a)).comp (single (Fin 2) 1))=f a :=
  (Classical.choose_spec (exists_unital_extension f hf)).2 a

abbrev DilationSpace := Stinespring.Space (extension f hf)

def dilationRepresentation : A →⋆ₐ[ℂ] (DilationSpace f hf →L[ℂ] DilationSpace f hf) :=
  (Stinespring.representation (extension f hf)).comp ChoiGNS.diagonal

def leftOperator : H →L[ℂ] DilationSpace f hf :=
  (Stinespring.embedding (extension f hf)).comp (single (Fin 2) 0)

def rightOperator : H →L[ℂ] DilationSpace f hf :=
  (Stinespring.representation (extension f hf) (ChoiGNS.entry (0 : Fin 2) 1 (1 : A))).comp
    ((Stinespring.embedding (extension f hf)).comp (single (Fin 2) 1))

lemma representation_upper (a : A) :
    (Stinespring.representation (extension f hf) (ChoiGNS.diagonal a)).comp
      (Stinespring.representation (extension f hf) (ChoiGNS.entry (0 : Fin 2) 1 (1 : A)))=
      Stinespring.representation (extension f hf) (ChoiGNS.entry (0 : Fin 2) 1 a) := by
  change Stinespring.representation (extension f hf) (ChoiGNS.diagonal a) *
    Stinespring.representation (extension f hf) (ChoiGNS.entry (0 : Fin 2) 1 (1 : A)) = _
  rw [←map_mul,ChoiGNS.diagonal_entry,mul_one]

theorem dilation_factorization (a : A) :
    f a=(leftOperator f hf).adjoint.comp
      ((dilationRepresentation f hf a).comp (rightOperator f hf)) := by
  rw [←extension_corner f hf a,Stinespring.factorization]
  dsimp only [leftOperator,rightOperator,dilationRepresentation,StarAlgHom.comp_apply]
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_assoc]
  rw [←ContinuousLinearMap.comp_assoc
    (Stinespring.representation (extension f hf) (ChoiGNS.diagonal a))
    (Stinespring.representation (extension f hf) (ChoiGNS.entry (0 : Fin 2) 1 (1 : A))),
    representation_upper]

lemma embedding_norm_le_one : ‖Stinespring.embedding (extension f hf)‖≤1 := by
  have h := Stinespring.embedding_norm_sq (extension f hf)
  rw [extension_one] at h
  have hn : ‖(1 : SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2))‖≤1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (Stinespring.embedding (extension f hf))]

lemma leftOperator_norm_le_one : ‖leftOperator f hf‖≤1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (embedding_norm_le_one f hf) (norm_single_le_one 0)
      (norm_nonneg (single (H:=H) (Fin 2) 0)) zero_le_one).trans_eq (mul_one 1))

lemma rightOperator_norm_le_one : ‖rightOperator f hf‖≤1 := by
  have hr : ‖Stinespring.representation (extension f hf) (ChoiGNS.entry (0 : Fin 2) 1 (1 : A))‖≤1 :=
    (NonUnitalStarAlgHom.norm_apply_le _ _).trans (ChoiGNS.norm_entry_one_le_one 0 1)
  have he : ‖(Stinespring.embedding (extension f hf)).comp (single (Fin 2) 1)‖≤1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (embedding_norm_le_one f hf) (norm_single_le_one 1)
        (norm_nonneg (single (H:=H) (Fin 2) 1)) zero_le_one).trans_eq (mul_one 1))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hr he (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (mul_one 1))

end Kadison.Paulsen

end

end
end

end OAI
