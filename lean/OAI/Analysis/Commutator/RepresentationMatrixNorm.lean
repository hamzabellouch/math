import Mathlib
import OAI.Analysis.Commutator.CyclicMatrix
import OAI.Analysis.Commutator.CyclicSpatialImplementation
import OAI.Analysis.Commutator.Definitions
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixOperator_representation (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) :
    matrixOperator h (fun i j => φ (X i j))=
      CyclicColumns.matrixRepresentation φ (CStarMatrix.ofMatrix X) := rfl

lemma matrixOperator_representation_norm_le (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) :
    ‖matrixOperator h (fun i j => ψ (X i j))‖≤‖matrixOperator h (fun i j => φ (X i j))‖ := by
  rw [matrixOperator_representation,matrixOperator_representation,
    CyclicSpatial.matrixRepresentation_norm_eq φ hφ]
  exact CyclicColumns.matrixRepresentation_norm_le ψ _

lemma matrixOperator_subtype_norm_le (M : VonNeumannAlgebra H)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖matrixOperator h (fun i j => ψ ⟨X i j,hX i j⟩)‖≤‖matrixOperator h X‖ :=
  matrixOperator_representation_norm_le (A:=M) (H:=H) (G:=G)
    M.toStarSubalgebra.subtype Subtype.val_injective ψ h (fun i j => ⟨X i j,hX i j⟩)

end Kadison

end

end
end

end OAI
