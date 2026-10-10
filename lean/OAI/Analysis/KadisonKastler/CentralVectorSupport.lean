import OAI.Analysis.KadisonKastler.VectorSupportProjection
import OAI.Analysis.KadisonKastler.CentralVectorMatrixLimit

namespace OAI

/-! # The support of a central vector commutes with the matrix stages -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralVector_support_commutes (M N : VonNeumannAlgebra H)
    (hNM : N ≤ M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra N, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ centralVectorSpace N J) (a : Algebra N) :
    (vectorSupportProjection M ξ).val.val * a.val =
      a.val * (vectorSupportProjection M ξ).val.val := by
  apply vectorSupport_commutes_of_right_vectors M N hNM ξ _ a
  intro b
  exact ⟨⟨conjugationOperator J (star b).val,hright (star b)⟩,hξ b⟩

theorem matrixCentralVector_support_commutes {M : VonNeumannAlgebra H}
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ matrixCentralVectorSpace A J) (n : ℕ) (i j : Fin (A n).size) :
    (vectorSupportProjection M ξ).val.val * ((A n).units.entry i j).val =
      ((A n).units.entry i j).val * (vectorSupportProjection M ξ).val.val := by
  exact centralVector_support_commutes M (matrixUnitConcreteAlgebra (A n).units)
    (matrixUnitConcreteAlgebra_le (A n).units) J
    (fun a => hright (coordinateInclusion (matrixUnitConcreteAlgebra_le (A n).units) a))
    ξ (matrixCentralVectorSpace_le A J n hξ) ((concreteMatrixUnits (A n).units).entry i j)

end

end KadisonKastler

end OAI
