import Mathlib
import OAI.Analysis.Commutator.ChoiGNS
import OAI.Analysis.Commutator.MatrixEntryWOT

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace CStarAlgebra

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type} [Fintype ι]

local instance hilbertMatrixCornerDecidableEq : DecidableEq ι := Classical.decEq ι

lemma single_adjoint (i : ι) : (single (H:=H) ι i).adjoint=PiLp.proj 2 (fun _ : ι => H) i := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [PiLp.inner_apply,apply_ite]

omit [CompleteSpace H] in
lemma norm_single_le_one (i : ι) : ‖single (H:=H) ι i‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [norm_single_eq]

lemma representation_corner (X : CStarMatrix ι ι (H →L[ℂ] H)) (i j : ι) :
    (single ι i).adjoint.comp
      ((CyclicColumns.matrixRepresentation (StarAlgHom.id ℂ (H →L[ℂ] H)) X).comp
        (single ι j))=X i j := by
  rw [single_adjoint]
  ext x
  simp [CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,apply_ite]

end Kadison.OperatorAmplification

namespace Kadison.ChoiGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type} [Fintype ι]

local instance choiMatrixCornerDecidableEq : DecidableEq ι := Classical.decEq ι

omit [PartialOrder A] [StarOrderedRing A] in
lemma entry_one_projection (i : ι) : IsStarProjection (entry i i (1 : A)) := by
  refine ⟨?_,?_⟩
  · exact by simp [IsIdempotentElem,entry_mul]
  · exact by simp [IsSelfAdjoint]

lemma norm_entry_one_le_one (i j : ι) : ‖entry i j (1 : A)‖≤1 := by
  have hn := (entry_one_projection (A:=A) j).norm_le
  have he : star (entry i j (1:A))*entry i j 1=entry j j 1 := by simp [entry_mul]
  rw [←he,CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (entry i j (1:A))]

end Kadison.ChoiGNS

end

end
end

end OAI
