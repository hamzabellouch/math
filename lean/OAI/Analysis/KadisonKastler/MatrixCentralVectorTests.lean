import OAI.Analysis.KadisonKastler.CentralVectorSpace
import OAI.Analysis.KadisonKastler.ConjugateMatrixStages
import OAI.Analysis.KadisonKastler.FiniteMatrixInjectivity

namespace OAI

/-! # Matrix-unit tests for central vectors -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Right evaluation is linear in the algebra element, despite the two conjugations. -/
def rightVectorLinear (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) : (H →L[ℂ] H) →ₗ[ℂ] H where
  toFun a := conjugationOperator J (star a) ξ
  map_add' a b := by
    change J (star (a + b) (J ξ)) = J (star a (J ξ)) + J (star b (J ξ))
    rw [star_add, add_apply, map_add]
  map_smul' c a := by
    change J (star (c • a) (J ξ)) = c • J (star a (J ξ))
    rw [star_smul, smul_apply, J.map_smulₛₗ]
    simp

@[simp] theorem rightVectorLinear_apply (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : H →L[ℂ] H) :
    rightVectorLinear J ξ a = conjugationOperator J (star a) ξ := rfl

theorem mem_centralVectorSpace_matrix_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (Algebra M)) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ↔
      ∀ i j, (E.entry i j).val ξ = conjugationOperator J (star (E.entry i j).val) ξ := by
  constructor
  · intro h i j
    exact h ((concreteMatrixUnits E).entry i j)
  · intro h a
    obtain ⟨b,hb⟩ := a.property
    have hentry (i j : ι) : (E.entry i j).val ξ = rightVectorLinear J ξ (E.entry i j).val :=
      h i j
    change a.val ξ = rightVectorLinear J ξ a.val
    rw [← hb]
    change (E.concreteHom b) ξ = rightVectorLinear J ξ (E.concreteHom b)
    rw [show E.concreteHom b = ∑ i, ∑ j, b i j • (E.entry i j).val by
      change M.toStarSubalgebra.subtype (E.hom b) = _
      simp only [MatrixUnitSystem.hom_apply, map_sum, map_smul]
      rfl]
    simp only [map_sum, map_smul, sum_apply, smul_apply]
    simp_rw [hentry]

end

end KadisonKastler

end OAI
