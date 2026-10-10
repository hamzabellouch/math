import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramRowKernel

namespace OAI

/-! The off-diagonal row phase descends to the actual level-three
translation classes of primitive rows. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompletion_top_character (h : Eisenstein)
    (g k : cubicThetaPrincipalGroup) (he : cubicThetaBottomRow g=cubicThetaBottomRow k)
    (hc : k.val 1 0≠0) :
    cubicThetaHorizontalCharacter h (((g.val 0 0:Eisenstein):ℂ)/((g.val 1 0:Eisenstein):ℂ))=
      cubicThetaHorizontalCharacter h (((k.val 0 0:Eisenstein):ℂ)/((k.val 1 0:Eisenstein):ℂ)) := by
  obtain ⟨w,hw⟩ := cubicThetaBottomRow_equal_translation g k he
  have hgc : g.val 1 0=k.val 1 0 := congrArg CubicThetaBottomRow.c he
  have hga : g.val 0 0=k.val 0 0+3*w*k.val 1 0 := by
    rw [hw]
    change ((cubicThetaPrincipalTranslation w).val.val*k.val.val) 0 0=_
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change 1*k.val 0 0+(3*w)*k.val 1 0=_
    ring
  have hcC : ((k.val 1 0:Eisenstein):ℂ)≠0 := fun hz => hc (Subtype.ext hz)
  have hfrac : (((g.val 0 0:Eisenstein):ℂ)/((g.val 1 0:Eisenstein):ℂ))=
      (((k.val 0 0:Eisenstein):ℂ)/((k.val 1 0:Eisenstein):ℂ))+3*(w:ℂ) := by
    rw [hgc,hga]
    push_cast
    field_simp
    rw [show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
    ring
  rw [hfrac,cubicThetaHorizontalCharacter_periodic]

lemma cubicThetaRow_right_translation_c (r : CubicThetaBottomRow) (w : Eisenstein) :
    (r.rightMul (cubicThetaPrincipalTranslation w)).c=r.c := by
  rw [CubicThetaBottomRow.rightMul_c]
  change r.c*1+r.d*0=r.c
  ring

lemma cubicThetaRow_right_translation_d (r : CubicThetaBottomRow) (w : Eisenstein) :
    (r.rightMul (cubicThetaPrincipalTranslation w)).d=r.d+3*r.c*w := by
  rw [CubicThetaBottomRow.rightMul_d]
  change r.c*(3*w)+r.d*1=r.d+3*r.c*w
  ring

theorem cubicThetaGramRowPhase_translation (h k : Eisenstein)
    (r : CubicThetaBottomRow) (hr : r.c≠0) (w : Eisenstein) :
    cubicThetaGramRowPhase h k (r.rightMul (cubicThetaPrincipalTranslation w))=
      cubicThetaGramRowPhase h k r := by
  let t := r.rightMul (cubicThetaPrincipalTranslation w)
  let g := r.completion*cubicThetaPrincipalTranslation w
  have hg : cubicThetaBottomRow t.completion=cubicThetaBottomRow g := by
    rw [t.completion_row]
    rfl
  have hgc : g.val 1 0=r.c := by
    change (r.rightMul (cubicThetaPrincipalTranslation w)).c=r.c
    exact cubicThetaRow_right_translation_c r w
  have hga : g.val 0 0=r.completion.val 0 0 := by
    change (r.completion.val.val*(cubicThetaPrincipalTranslation w).val.val) 0 0=_
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change r.completion.val 0 0*1+r.completion.val 0 1*0=_
    ring
  have htop := cubicThetaCompletion_top_character k t.completion g hg (hgc ▸ hr)
  have htc : t.completion.val 1 0=t.c := congrArg CubicThetaBottomRow.c t.completion_row
  rw [htc] at htop
  rw [hgc,hga] at htop
  have hbot : cubicThetaHorizontalCharacter h ((t.d:ℂ)/(t.c:ℂ))=
      cubicThetaHorizontalCharacter h ((r.d:ℂ)/(r.c:ℂ)) := by
    have hfrac : (t.d:ℂ)/(t.c:ℂ)=(r.d:ℂ)/(r.c:ℂ)+3*(w:ℂ) := by
      dsimp only [t]
      rw [cubicThetaRow_right_translation_c,cubicThetaRow_right_translation_d]
      push_cast
      have hcC : (r.c:ℂ)≠0 := fun hz => hr (Subtype.ext hz)
      field_simp
      rw [show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
      ring
    rw [hfrac,cubicThetaHorizontalCharacter_periodic]
  change cubicThetaGramRowPhase h k t=_
  unfold cubicThetaGramRowPhase
  rw [htop,hbot]
  have hp : t.phase=r.phase := by
    dsimp only [t]
    rw [CubicThetaBottomRow.phase_rightMul,cubicThetaPrincipalTranslation_value,mul_one]
  rw [hp]

end CubicFirstMoment

end

end OAI
