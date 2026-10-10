import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierCharacter

namespace OAI

/-! Two integral completions of a primitive bottom row differ by the
actual level-three unipotent stabilizer. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaBottomRow_equal_translation (g h : cubicThetaPrincipalGroup)
    (he : cubicThetaBottomRow g=cubicThetaBottomRow h) :
    ∃ w : Eisenstein,g=cubicThetaPrincipalTranslation w*h := by
  have hc : g.val 1 0=h.val 1 0 := congrArg CubicThetaBottomRow.c he
  have hd : g.val 1 1=h.val 1 1 := congrArg CubicThetaBottomRow.d he
  let d := g*h⁻¹
  have h10 : d.val 1 0=0 := by
    change (g.val*h.val⁻¹) 1 0=0
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    change g.val 1 0*h.val 1 1+g.val 1 1*(-h.val 1 0)=0
    rw [hc,hd]
    ring
  have h11 : d.val 1 1=1 := by
    change (g.val*h.val⁻¹) 1 1=1
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    change g.val 1 0*(-h.val 0 1)+g.val 1 1*h.val 0 0=1
    rw [hc,hd]
    linear_combination cubicThetaPrincipalGroup_det h
  have h00 : d.val 0 0=1 := by
    have H := cubicThetaPrincipalGroup_det d
    rw [h10,h11,mul_one,mul_zero,sub_zero] at H
    exact H
  obtain ⟨w,hw⟩ := (cubicThetaPrincipalGroup_offDiagonal d).1
  have hT : d=cubicThetaPrincipalTranslation w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact hw
    · exact h10
    · exact h11
  refine ⟨w,?_⟩
  rw [←hT]
  dsimp only [d]
  rw [mul_assoc,inv_mul_cancel,mul_one]

lemma CubicThetaBottomRow.completion_rightMul_translation (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) :
    ∃ w : Eisenstein,r.completion*g=cubicThetaPrincipalTranslation w*(r.rightMul g).completion := by
  apply cubicThetaBottomRow_equal_translation
  rw [(r.rightMul g).completion_row]
  rfl

lemma cubicThetaHorizontalCharacter_completion (h : Eisenstein)
    (g k : cubicThetaPrincipalGroup) (he : cubicThetaBottomRow g=cubicThetaBottomRow k)
    (p : CubicThetaPoint) :
    cubicThetaHorizontalCharacter h (g • p).val.1=
      cubicThetaHorizontalCharacter h (k • p).val.1 := by
  obtain ⟨w,rfl⟩ := cubicThetaBottomRow_equal_translation g k he
  rw [mul_smul]
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) (k • p).val).1=_
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
  have hw : ((3*w:Eisenstein):ℂ)=3*(w:ℂ) := by
    rw [Subalgebra.coe_mul]
    congr 1
  rw [hw]
  exact cubicThetaHorizontalCharacter_periodic h w (k • p).val.1

end CubicFirstMoment

end

end OAI
