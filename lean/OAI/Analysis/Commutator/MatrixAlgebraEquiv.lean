import Mathlib
import OAI.Analysis.Commutator.MatrixVonNeumann

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rangeRestriction {B : Type*} [CStarAlgebra B]
    (P : VonNeumannAlgebra H) (φ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : ∀ b,φ b∈P) : B →⋆ₐ[ℂ] P :=
  φ.codRestrict P.toStarSubalgebra hφ

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance : DecidableEq ι := Classical.decEq ι

lemma entry_matrixRepresentation (X : CStarMatrix ι ι M) (i j : ι) :
    entry ι (CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X) i j=
      (X i j:H →L[ℂ] H) := by
  ext x
  simp only [entry_apply,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
    StarAlgHom.coe_mk]
  simp [apply_ite]
  rfl

def matrixHom : CStarMatrix ι ι M →⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  rangeRestriction (matrixVonNeumann ι i₀ M)
    (CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype)
    (matrix_representation_mem ι i₀ M)

lemma coe_matrixHom (X : CStarMatrix ι ι M) :
    (matrixHom ι i₀ M X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      CyclicColumns.matrixRepresentation (A:=M) (H:=H) M.toStarSubalgebra.subtype X := rfl

lemma matrixHom_bijective : Function.Bijective (matrixHom ι i₀ M) := by
  constructor
  · intro X Y h
    apply CStarMatrix.ext
    intro i j
    apply Subtype.ext
    have he := congrArg (fun T : matrixVonNeumann ι i₀ M =>
      entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j) h
    simpa only [coe_matrixHom,entry_matrixRepresentation] using he
  · intro T
    obtain ⟨X,hX⟩ := matrixVonNeumann_is_range ι i₀ M T T.property
    exact ⟨X,Subtype.ext hX⟩

def matrixEquiv : CStarMatrix ι ι M ≃⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  StarAlgEquiv.ofBijective (matrixHom ι i₀ M) (matrixHom_bijective ι i₀ M)

lemma matrixEquiv_apply (X : CStarMatrix ι ι M) :
    matrixEquiv ι i₀ M X=matrixHom ι i₀ M X := rfl

lemma matrixEquiv_symm_entry (T : matrixVonNeumann ι i₀ M) (i j : ι) :
    ((matrixEquiv ι i₀ M).symm T i j:H →L[ℂ] H)=
      entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j := by
  rw [←entry_matrixRepresentation]
  have h := congrArg (fun X : matrixVonNeumann ι i₀ M =>
    entry ι (X:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i j)
    ((matrixEquiv ι i₀ M).apply_symm_apply T)
  exact h

end Kadison.OperatorAmplification

end

end
end

end OAI
