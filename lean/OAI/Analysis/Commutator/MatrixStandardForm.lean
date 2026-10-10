import Mathlib
import OAI.Analysis.Commutator.MatrixGNSUnitary
import OAI.Analysis.Commutator.MatrixNormalTrace

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance matrixStandardFormDecidableEq : DecidableEq ι := Classical.decEq ι

variable (τ : M →ₚ[ℂ] ℂ)

def standardMatrixRepresentation : matrixVonNeumann ι i₀ M →⋆ₐ[ℂ]
    (MatrixGNS.ArraySpace (ι:=ι) τ →L[ℂ] MatrixGNS.ArraySpace (ι:=ι) τ) :=
  (MatrixGNS.representation (ι:=ι) τ).comp (matrixEquiv ι i₀ M).symm.toStarAlgHom

lemma standardMatrixRepresentation_equiv (X : CStarMatrix ι ι M) :
    standardMatrixRepresentation ι i₀ M τ (matrixEquiv ι i₀ M X)=
      MatrixGNS.representation (ι:=ι) τ X := by
  change MatrixGNS.representation (ι:=ι) τ
    ((matrixEquiv ι i₀ M).symm (matrixEquiv ι i₀ M X))=_
  exact congrArg (MatrixGNS.representation (ι:=ι) τ) ((matrixEquiv ι i₀ M).symm_apply_apply X)

lemma standardMatrixTrace_vector (X : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ X=inner ℂ (MatrixGNS.vacuum (ι:=ι) τ)
      (standardMatrixRepresentation ι i₀ M τ X (MatrixGNS.vacuum (ι:=ι) τ)) := rfl

lemma standardMatrix_vacuum_cyclic : DenseRange (fun X : matrixVonNeumann ι i₀ M =>
    standardMatrixRepresentation ι i₀ M τ X (MatrixGNS.vacuum (ι:=ι) τ)) := by
  let : Nonempty ι := ⟨i₀⟩
  apply (MatrixGNS.dense_vacuumOrbit (ι:=ι) τ).mono
  rintro y ⟨X,rfl⟩
  exact ⟨matrixEquiv ι i₀ M X,congrArg (fun T => T (MatrixGNS.vacuum (ι:=ι) τ))
    (standardMatrixRepresentation_equiv ι i₀ M τ X)⟩

def standardMatrixUnitary :=
  VectorGNS.equivalence (matrixTrace ι i₀ M τ) (standardMatrixRepresentation ι i₀ M τ)
    (MatrixGNS.vacuum (ι:=ι) τ) (standardMatrixTrace_vector ι i₀ M τ)
    (standardMatrix_vacuum_cyclic ι i₀ M τ)

lemma standardMatrixUnitary_intertwines (X : matrixVonNeumann ι i₀ M)
    (v : (matrixTrace ι i₀ M τ).GNS) :
    standardMatrixUnitary ι i₀ M τ ((matrixTrace ι i₀ M τ).gnsStarAlgHom X v)=
      standardMatrixRepresentation ι i₀ M τ X (standardMatrixUnitary ι i₀ M τ v) :=
  VectorGNS.equivalence_intertwines _ _ _ _ _ _ _

lemma standardMatrixUnitary_algebraVector (X : CStarMatrix ι ι M) :
    standardMatrixUnitary ι i₀ M τ
      (TracialGNS.algebraVector (matrixTrace ι i₀ M τ) (matrixEquiv ι i₀ M X))=
    MatrixGNS.scale ι • MatrixGNS.algebraArray τ X := by
  rw [standardMatrixUnitary,VectorGNS.equivalence_algebraVector,
    standardMatrixRepresentation_equiv,MatrixGNS.representation_vacuum]

end Kadison.OperatorAmplification

end

end
end

end OAI
