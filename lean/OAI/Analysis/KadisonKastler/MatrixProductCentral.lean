import OAI.Analysis.KadisonKastler.RelativeMatrixExtension
import OAI.Analysis.KadisonKastler.MatrixCentralVectorTests

namespace OAI

/-! # Central vectors of two commuting finite matrix algebras -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem central_vector_mul (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M)
    (ha : a.val ξ = conjugationOperator J (star a).val ξ)
    (hb : b.val ξ = conjugationOperator J (star b).val ξ) :
    (a*b).val ξ = conjugationOperator J (star (a*b)).val ξ := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star b)) a.val a.property
  change (a.val*b.val) ξ = conjugationOperator J (star (a.val*b.val)) ξ
  rw [mul_apply_eq_comp,hb]
  calc
    a.val (conjugationOperator J (star b).val ξ) =
        conjugationOperator J (star b).val (a.val ξ) :=
      congrArg (fun T : H →L[ℂ] H => T ξ) hc
    _ = conjugationOperator J (star b).val (conjugationOperator J (star a).val ξ) := by rw [ha]
    _ = conjugationOperator J (star (a.val*b.val)) ξ := by
      rw [star_mul,conjugationOperator_mul J hJ,mul_apply_eq_comp]
      rfl

theorem matrix_product_centralVectorSpace
    (E : MatrixUnitSystem ι (Algebra M)) (F : MatrixUnitSystem κ (Algebra M))
    (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant) :
    centralVectorSpace (matrixUnitConcreteAlgebra (E.product F hc)) J =
      centralVectorSpace (matrixUnitConcreteAlgebra E) J ⊓
        centralVectorSpace (matrixUnitConcreteAlgebra F) J := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · apply centralVectorSpace_antitone
      exact matrix_concrete_mono E _ (E.algebra_le_product_left F hc)
    · apply centralVectorSpace_antitone
      exact matrix_concrete_mono F _ (E.algebra_le_product_right F hc)
  · intro ξ hξ
    apply (mem_centralVectorSpace_matrix_iff _ J ξ).mpr
    intro i j
    exact central_vector_mul J hJ hright ξ (E.entry i.1 j.1) (F.entry i.2 j.2)
      ((mem_centralVectorSpace_matrix_iff E J ξ).mp hξ.1 _ _)
      ((mem_centralVectorSpace_matrix_iff F J ξ).mp hξ.2 _ _)

end

end KadisonKastler

end OAI
