import Mathlib
import OAI.Analysis.Commutator.MatrixInclusion
import OAI.Analysis.Commutator.MatrixNormalTrace
import OAI.Analysis.Commutator.MatrixRowCorner
import OAI.Analysis.Commutator.NormalSubalgebra

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance matrixCornerInclusionDecidableEq : DecidableEq ι := Classical.decEq ι

def matrixInclusion : matrixVonNeumann ι i₀ Q →⋆ₐ[ℂ] CStarMatrix ι ι M :=
  (matrixEquiv ι i₀ M).symm.toStarAlgHom.comp
    (NormalSubalgebra.inclusion (matrixVonNeumann ι i₀ M) (matrixVonNeumann ι i₀ Q)
      (matrixVonNeumann_mono ι i₀ hQM))

lemma matrixInclusion_entry (X : matrixVonNeumann ι i₀ Q) (i j : ι) :
    (matrixInclusion ι i₀ M Q hQM X i j:H →L[ℂ] H)=
      entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j := by
  exact matrixEquiv_symm_entry ι i₀ M _ i j

lemma matrixInclusion_row (i : ι) :
    matrixInclusion ι i₀ M Q hQM (matrixEquiv ι i₀ Q (MatrixGNS.rowMatrix i (1:Q)))=
      MatrixGNS.rowMatrix i (1:M) := by
  apply CStarMatrix.ext
  intro j k
  apply Subtype.ext
  rw [matrixInclusion_entry]
  change entry ι (CyclicColumns.matrixRepresentation (A:=Q) (H:=H) Q.toStarSubalgebra.subtype
    (MatrixGNS.rowMatrix i (1:Q))) j k=_
  rw [entry_matrixRepresentation]
  simp only [MatrixGNS.rowMatrix_apply]
  split_ifs <;> rfl

lemma matrixTrace_restrict (τ : M →ₚ[ℂ] ℂ) (X : matrixVonNeumann ι i₀ Q) :
    MatrixGNS.trace (ι:=ι) τ (matrixInclusion ι i₀ M Q hQM X)=
      matrixTrace ι i₀ Q (NormalSubalgebra.trace M Q hQM τ) X := by
  rw [MatrixGNS.trace_apply,matrixTrace_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [NormalSubalgebra.trace_apply]
  congr 1
  apply Subtype.ext
  exact matrixInclusion_entry ι i₀ M Q hQM X i i

end Kadison.OperatorAmplification

end

end
end

end OAI
