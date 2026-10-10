import OAI.Analysis.KadisonKastler.NormalMatrixRepresentation
import OAI.Analysis.KadisonKastler.TwoStateMatrixCyclicity

namespace OAI

/-! # The two-state matrix algebra for a specified normal representation change -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)

def normalTwoStateAlgebra : VonNeumannAlgebra (TwoStateMatrixHilbert H K) :=
  normalPairAlgebra (matrixVonNeumann (ι := Fin 2) M) (normalMatrixRepresentation θ)

variable (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))

def normalTwoStateEquiv : CStarMatrix (Fin 2) (Fin 2) (Algebra M) ≃⋆ₐ[ℂ]
    Algebra (normalTwoStateAlgebra θ) :=
  (matrixAlgebraEquiv M).trans (normalPairEquiv (matrixVonNeumann (ι := Fin 2) M)
    (normalMatrixRepresentation θ) (normalMatrixRepresentation_boundedWeakNormal θ hθ))

theorem normalTwoStateEquiv_coe (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
    (normalTwoStateEquiv θ hθ a).val = twoStateMatrixRepresentation θ a := by
  change hilbertPairOperator (matrixOperatorHom M a)
    (normalMatrixRepresentation θ (matrixAlgebraEquiv M a)) = _
  change hilbertPairOperator (matrixOperatorHom M a)
    (matrixOperatorHom N (coefficientMatrixMap θ.toStarAlgHom
      ((matrixAlgebraEquiv M).symm (matrixAlgebraEquiv M a)))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl

include hθ in
theorem normalTwoStateAlgebra_cyclic (Ω : H) (ξ : K)
    (hΩ : DenseRange (algebraVectorMap M Ω)) (hξ : DenseRange (algebraVectorMap N ξ)) :
    DenseRange (algebraVectorMap (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ)) := by
  have h := twoStateMatrixRepresentation_cyclic θ Ω ξ hΩ hξ
  apply Dense.mono ?_ h
  rintro _ ⟨a, rfl⟩
  refine ⟨normalTwoStateEquiv θ hθ a, ?_⟩
  change (normalTwoStateEquiv θ hθ a).val (twoStateMatrixVector Ω ξ) = _
  rw [normalTwoStateEquiv_coe]

include hθ in
theorem normalTwoStateAlgebra_separating (Ω : H) (ξ : K)
    (hΩ : Function.Injective (algebraVectorMap M Ω))
    (hξ : Function.Injective (algebraVectorMap N ξ)) :
    Function.Injective (algebraVectorMap (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ)) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (normalTwoStateEquiv θ hθ).surjective a
  obtain ⟨b, rfl⟩ := (normalTwoStateEquiv θ hθ).surjective b
  apply congrArg (normalTwoStateEquiv θ hθ)
  apply twoStateMatrixRepresentation_separating θ Ω ξ hΩ hξ
  change (normalTwoStateEquiv θ hθ a).val (twoStateMatrixVector Ω ξ) =
    (normalTwoStateEquiv θ hθ b).val (twoStateMatrixVector Ω ξ) at hab
  simpa only [normalTwoStateEquiv_coe] using hab

end

end KadisonKastler

end OAI
