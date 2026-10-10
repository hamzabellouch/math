import OAI.Analysis.KadisonKastler.TwoStateCornerEmbedding

namespace OAI

/-! # The matrix coefficient recovered by compressing a diagonal state space -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] theorem twoStateCornerEmbedding_adjoint (i : Fin 2) (v : TwoStateMatrixHilbert H H) :
    (twoStateCornerEmbedding i).toContinuousLinearMap.adjoint v =
      if i = 0 then v.fst 0 else v.snd 1 := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  fin_cases i <;>
    simp [twoStateCornerEmbedding, WithLp.prod_inner_apply, PiLp.inner_apply,
      tupleSingle_apply, Fin.sum_univ_two]

theorem twoStateCornerEmbedding_compress_vector (M : VonNeumannAlgebra H) (Ω ξ : H)
    (i : Fin 2) (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
    (twoStateCornerEmbedding i).toContinuousLinearMap.adjoint
      ((twoStateMatrixEquiv M a).val (twoStateMatrixVector Ω ξ)) =
        (a i i).val (twoStateVectorAt Ω ξ i) := by
  fin_cases i
  · change (twoStateCornerEmbedding 0).toContinuousLinearMap.adjoint
      ((twoStateMatrixEquiv M a).val (twoStateMatrixVector Ω ξ)) = (a 0 0).val Ω
    rw [twoStateMatrixEquiv_coe, twoStateCornerEmbedding_adjoint, ite_eq_left rfl,
      twoStateMatrixRepresentation_vector_fst]
  · change (twoStateCornerEmbedding 1).toContinuousLinearMap.adjoint
      ((twoStateMatrixEquiv M a).val (twoStateMatrixVector Ω ξ)) = (a 1 1).val ξ
    rw [twoStateMatrixEquiv_coe, twoStateCornerEmbedding_adjoint,
      ite_eq_right (by decide : (1 : Fin 2) ≠ 0), twoStateMatrixRepresentation_vector_snd]
    rfl

end

end KadisonKastler

end OAI
