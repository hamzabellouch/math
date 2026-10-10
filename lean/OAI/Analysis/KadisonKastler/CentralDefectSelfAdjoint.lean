import OAI.Analysis.KadisonKastler.MatrixCentralVectorTests
import OAI.Analysis.KadisonKastler.SelfAdjointProjectionCut

namespace OAI

/-! # Reducing a central-vector defect to a self-adjoint contraction -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def centralVectorDefect (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) : (H →L[ℂ] H) →ₗ[ℂ] H where
  toFun a := a ξ - rightVectorLinear J ξ a
  map_add' a b := by
    simp only [add_apply,map_add]
    abel
  map_smul' c a := by
    simp only [smul_apply,map_smul,smul_sub,RingHom.id_apply]

@[simp] theorem centralVectorDefect_apply (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : H →L[ℂ] H) :
    centralVectorDefect J ξ a = a ξ - conjugationOperator J (star a) ξ := rfl

theorem centralVectorDefect_star_norm (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ = ξ) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ (star a)‖ = ‖centralVectorDefect J ξ a‖ := by
  have he : J (centralVectorDefect J ξ a) = -centralVectorDefect J ξ (star a) := by
    change J (a ξ - J (star a (J ξ))) = -(star a ξ - J (star (star a) (J ξ)))
    rw [map_sub,hξ,hJ,star_star]
    abel
  have hn := congrArg norm he
  simpa only [J.norm_map,norm_neg] using hn.symm

theorem centralVectorDefect_realPart_le (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ = ξ) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ (realPart a : H →L[ℂ] H)‖ ≤ ‖centralVectorDefect J ξ a‖ := by
  let D := centralVectorDefect J ξ
  change ‖D (realPart a : H →L[ℂ] H)‖ ≤ ‖D a‖
  rw [realPart_apply_coe,D.map_smul_of_tower,map_add,norm_smul]
  rw [show ‖(2 : ℝ)⁻¹‖ = (1 / 2 : ℝ) by norm_num]
  have hstar := centralVectorDefect_star_norm J hJ ξ hξ a
  change ‖D (star a)‖ = ‖D a‖ at hstar
  have hn := norm_add_le (D a) (D (star a))
  nlinarith

theorem centralVectorDefect_imaginaryPart_le (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ = ξ) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ (imaginaryPart a : H →L[ℂ] H)‖ ≤ ‖centralVectorDefect J ξ a‖ := by
  let D := centralVectorDefect J ξ
  change ‖D (imaginaryPart a : H →L[ℂ] H)‖ ≤ ‖D a‖
  rw [imaginaryPart_apply_coe,map_smul,D.map_smul_of_tower,map_sub,norm_smul,norm_smul]
  rw [norm_neg,Complex.norm_I,one_mul,
    show ‖(2 : ℝ)⁻¹‖ = (1 / 2 : ℝ) by norm_num]
  have hstar := centralVectorDefect_star_norm J hJ ξ hξ a
  change ‖D (star a)‖ = ‖D a‖ at hstar
  have hn := norm_sub_le (D a) (D (star a))
  nlinarith

theorem centralVectorDefect_re_im_gap (J : H ≃ₗᵢ⋆[ℂ] H) (η : H) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J η a‖ / 2 ≤
        ‖centralVectorDefect J η (realPart a : H →L[ℂ] H)‖ ∨
      ‖centralVectorDefect J η a‖ / 2 ≤
        ‖centralVectorDefect J η (imaginaryPart a : H →L[ℂ] H)‖ := by
  let D := centralVectorDefect J η
  have he : D a = D (realPart a : H →L[ℂ] H) +
      Complex.I • D (imaginaryPart a : H →L[ℂ] H) := by
    rw [← map_smul,← map_add,realPart_add_I_smul_imaginaryPart]
  have hn := norm_add_le (D (realPart a : H →L[ℂ] H))
    (Complex.I • D (imaginaryPart a : H →L[ℂ] H))
  rw [← he,norm_smul,Complex.norm_I,one_mul] at hn
  change ‖D a‖ / 2 ≤ ‖D (realPart a : H →L[ℂ] H)‖ ∨
    ‖D a‖ / 2 ≤ ‖D (imaginaryPart a : H →L[ℂ] H)‖
  by_contra h
  push Not at h
  linarith [h.1,h.2]

end

end KadisonKastler

end OAI
