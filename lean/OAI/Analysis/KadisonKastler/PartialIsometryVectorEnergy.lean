import OAI.Analysis.KadisonKastler.CornerStateWeights
import OAI.Analysis.KadisonKastler.SmallVectorSubprojection
import OAI.Analysis.KadisonKastler.CentralDefectSelfAdjoint

namespace OAI

/-! # Vector energy of a partial isometry and its central defect -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem partialIsometry_vector_norm_sq (v : PartialIsometry M) (ξ : H) :
    ‖v.val.val ξ‖^2=‖v.support.val.val ξ‖^2 := by
  have he := congrArg Complex.re (vectorFunctional_projection v.support ξ)
  rw [← v.initial] at he
  change (inner ℂ ξ (v.val.val.adjoint (v.val.val ξ))).re=‖v.support.val.val ξ‖^2 at he
  rw [ContinuousLinearMap.adjoint_inner_right] at he
  change RCLike.re (inner ℂ (v.val.val ξ) (v.val.val ξ))=_ at he
  rwa [inner_self_eq_norm_sq] at he

theorem partialIsometry_right_vector_norm_sq (J : H ≃ₗᵢ⋆[ℂ] H)
    (v : PartialIsometry M) (ξ : H) (hξ : J ξ=ξ) :
    ‖conjugationOperator J (star v.val.val) ξ‖^2=‖v.target.val.val ξ‖^2 := by
  rw [conjugationOperator_apply,hξ,J.norm_map]
  exact partialIsometry_vector_norm_sq v.adjoint ξ

theorem partialIsometry_central_defect_upper (J : H ≃ₗᵢ⋆[ℂ] H)
    (v : PartialIsometry M) (ξ : H) (hξ : J ξ=ξ) :
    ‖centralVectorDefect J ξ v.val.val‖^2 ≤
      2*(‖v.support.val.val ξ‖^2+‖v.target.val.val ξ‖^2) := by
  have hn := norm_sub_le (v.val.val ξ) (conjugationOperator J (star v.val.val) ξ)
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  have hp := partialIsometry_vector_norm_sq v ξ
  have hq := partialIsometry_right_vector_norm_sq J v ξ hξ
  change ‖centralVectorDefect J ξ v.val.val‖ ≤ _ at hn
  change ‖centralVectorDefect J ξ v.val.val‖^2 ≤ _ at hs
  nlinarith [sq_nonneg (‖v.val.val ξ‖-‖conjugationOperator J (star v.val.val) ξ‖)]

theorem partialIsometry_central_defect_lower (J : H ≃ₗᵢ⋆[ℂ] H)
    (v : PartialIsometry M) (p q : AlgebraProjection M)
    (hsupport : v.support.val=p.val-q.val) (htarget : v.target=q)
    (hqp : q ≤ p) (η : H) (hη : J η=η)
    (hsmall : ‖q.val.val η‖^2 < ‖p.val.val η‖^2/16) :
    ‖p.val.val η‖^2/4 < ‖centralVectorDefect J η v.val.val‖^2 := by
  let A := ‖v.val.val η‖
  let B := ‖conjugationOperator J (star v.val.val) η‖
  let D := ‖centralVectorDefect J η v.val.val‖
  have ha : A^2=‖(p.val-q.val).val η‖^2 := by
    exact (partialIsometry_vector_norm_sq v η).trans (congrArg (fun a : Algebra M => ‖a.val η‖^2) hsupport)
  have hb : B^2=‖q.val.val η‖^2 := by
    exact (partialIsometry_right_vector_norm_sq J v η hη).trans (congrArg (fun r : AlgebraProjection M => ‖r.val.val η‖^2) htarget)
  have htotal : A^2+B^2=‖p.val.val η‖^2 := by
    rw [ha,hb,add_comm]
    exact vector_projection_sub_weight p q hqp η
  have hn : A ≤ D+B := by
    calc
      _ = ‖(v.val.val η-conjugationOperator J (star v.val.val) η)+
          conjugationOperator J (star v.val.val) η‖ := by
        dsimp only [A]
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
  have hs := (sq_le_sq₀ (show 0 ≤ A from norm_nonneg _) (show 0 ≤ D+B by positivity)).mpr hn
  change ‖p.val.val η‖^2/4 < D^2
  nlinarith [sq_nonneg (D-B),sq_nonneg ‖p.val.val η‖]

end

end KadisonKastler

end OAI
