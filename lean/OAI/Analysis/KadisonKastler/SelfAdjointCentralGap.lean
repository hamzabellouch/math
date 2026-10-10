import OAI.Analysis.KadisonKastler.CentralDefectSelfAdjoint
import OAI.Analysis.KadisonKastler.SelfAdjointApproximation

namespace OAI

/-! # A self-adjoint witness for a central-vector gap

One real or imaginary part retains at least half the test-vector defect.
At a conjugation-fixed reference vector both parts have no larger defect
than the original operator.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_central_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (hξ : J ξ = ξ) (a : Algebra M) :
    ∃ b : Algebra M, IsSelfAdjoint b ∧ ‖b‖ ≤ ‖a‖ ∧
      ‖centralVectorDefect J ξ b.val‖ ≤ ‖centralVectorDefect J ξ a.val‖ ∧
      ‖centralVectorDefect J η a.val‖ / 2 ≤ ‖centralVectorDefect J η b.val‖ := by
  rcases centralVectorDefect_re_im_gap J η a.val with hr | hi
  · let b : Algebra M := ⟨(realPart a.val : H →L[ℂ] H),realPart_mem_vonNeumann M a.property⟩
    refine ⟨b,?_,?_,centralVectorDefect_realPart_le J hJ ξ hξ a.val,hr⟩
    · exact Subtype.ext (realPart a.val).property.star_eq
    · exact realPart.norm_le a.val
  · have hb : (imaginaryPart a.val : H →L[ℂ] H) ∈ M := by
      rw [imaginaryPart_apply_coe,← Complex.coe_smul (2 : ℝ)⁻¹]
      exact M.smul_mem (M.smul_mem (M.sub_mem a.property (M.star_mem' a.property)) _) _
    let b : Algebra M := ⟨(imaginaryPart a.val : H →L[ℂ] H),hb⟩
    refine ⟨b,?_,?_,centralVectorDefect_imaginaryPart_le J hJ ξ hξ a.val,hi⟩
    · exact Subtype.ext (imaginaryPart a.val).property.star_eq
    · exact imaginaryPart.norm_le a.val

end

end KadisonKastler

end OAI
