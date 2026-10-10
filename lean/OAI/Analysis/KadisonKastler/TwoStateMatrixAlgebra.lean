import OAI.Analysis.KadisonKastler.TwoStateMatrixCyclicity
import OAI.Analysis.KadisonKastler.DiagonalPairAlgebra

namespace OAI

/-! # A von Neumann algebra carrying two diagonal vector states -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoStateMatrixAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (TwoStateMatrixHilbert H H) :=
  diagonalPairAlgebra (matrixVonNeumann (ι := Fin 2) M)

def twoStateMatrixEquiv (M : VonNeumannAlgebra H) :
    CStarMatrix (Fin 2) (Fin 2) (Algebra M) ≃⋆ₐ[ℂ] Algebra (twoStateMatrixAlgebra M) :=
  (matrixAlgebraEquiv M).trans (diagonalPairEquiv (matrixVonNeumann M))

theorem twoStateMatrixEquiv_coe (M : VonNeumannAlgebra H)
    (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
    (twoStateMatrixEquiv M a).val =
      twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M)) a := by
  change hilbertPairOperator (matrixOperatorHom M a) (matrixOperatorHom M a) =
    hilbertPairOperator (matrixOperatorHom M a)
      (matrixOperatorHom M (coefficientMatrixMap (StarAlgEquiv.refl ℂ (Algebra M)).toStarAlgHom a))
  congr 2

theorem twoStateMatrixAlgebra_cyclic (M : VonNeumannAlgebra H) (Ω ξ : H)
    (hΩ : DenseRange (algebraVectorMap M Ω)) (hξ : DenseRange (algebraVectorMap M ξ)) :
    DenseRange (algebraVectorMap (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ)) := by
  have h := twoStateMatrixRepresentation_cyclic (StarAlgEquiv.refl ℂ (Algebra M)) Ω ξ hΩ hξ
  apply Dense.mono ?_ h
  rintro _ ⟨a, rfl⟩
  refine ⟨twoStateMatrixEquiv M a, ?_⟩
  change (twoStateMatrixEquiv M a).val (twoStateMatrixVector Ω ξ) = _
  rw [twoStateMatrixEquiv_coe]

theorem twoStateMatrixAlgebra_separating (M : VonNeumannAlgebra H) (Ω ξ : H)
    (hΩ : Function.Injective (algebraVectorMap M Ω))
    (hξ : Function.Injective (algebraVectorMap M ξ)) :
    Function.Injective (algebraVectorMap (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ)) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (twoStateMatrixEquiv M).surjective a
  obtain ⟨b, rfl⟩ := (twoStateMatrixEquiv M).surjective b
  apply congrArg (twoStateMatrixEquiv M)
  apply twoStateMatrixRepresentation_separating (StarAlgEquiv.refl ℂ (Algebra M)) Ω ξ hΩ hξ
  change (twoStateMatrixEquiv M a).val (twoStateMatrixVector Ω ξ) =
    (twoStateMatrixEquiv M b).val (twoStateMatrixVector Ω ξ) at hab
  simpa only [twoStateMatrixEquiv_coe] using hab

end

end KadisonKastler

end OAI
