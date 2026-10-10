import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowCompletionTranslation

namespace OAI

/-! Exact decomposition of the principal arithmetic group into the
level-three translation stabilizer and primitive bottom rows. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBottomRow_left_translation (w : Eisenstein) (g : cubicThetaPrincipalGroup) :
    cubicThetaBottomRow (cubicThetaPrincipalTranslation w*g)=cubicThetaBottomRow g := by
  apply CubicThetaBottomRow.ext
  · change ((cubicThetaPrincipalTranslation w).val.val*g.val.val) 1 0=g.val 1 0
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change 0*g.val 0 0+1*g.val 1 0=g.val 1 0
    ring
  · change ((cubicThetaPrincipalTranslation w).val.val*g.val.val) 1 1=g.val 1 1
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    change 0*g.val 0 1+1*g.val 1 1=g.val 1 1
    ring

lemma cubicThetaPrincipalTranslation_injective : Function.Injective cubicThetaPrincipalTranslation := by
  intro w z h
  have he : (3:Eisenstein)*w=3*z := congrArg (fun g : cubicThetaPrincipalGroup => g.val 0 1) h
  exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) he

def cubicThetaRowTranslationMap (wr : Eisenstein × CubicThetaBottomRow) : cubicThetaPrincipalGroup :=
  cubicThetaPrincipalTranslation wr.1*wr.2.completion

lemma cubicThetaRowTranslationMap_injective : Function.Injective cubicThetaRowTranslationMap := by
  rintro ⟨w,r⟩ ⟨z,s⟩ h
  have hrs : r=s := by
    have he := congrArg cubicThetaBottomRow h
    simpa only [cubicThetaRowTranslationMap,cubicThetaBottomRow_left_translation,
      CubicThetaBottomRow.completion_row] using he
  subst s
  have ht : cubicThetaPrincipalTranslation w=cubicThetaPrincipalTranslation z := mul_right_cancel h
  exact Prod.ext (cubicThetaPrincipalTranslation_injective ht) rfl

lemma cubicThetaRowTranslationMap_surjective : Function.Surjective cubicThetaRowTranslationMap := by
  intro g
  obtain ⟨w,hw⟩ := cubicThetaBottomRow_equal_translation g (cubicThetaBottomRow g).completion
    (CubicThetaBottomRow.completion_row _).symm
  exact ⟨(w,cubicThetaBottomRow g),hw.symm⟩

def cubicThetaRowTranslationEquiv : (Eisenstein × CubicThetaBottomRow) ≃ cubicThetaPrincipalGroup :=
  Equiv.ofBijective cubicThetaRowTranslationMap
    ⟨cubicThetaRowTranslationMap_injective,cubicThetaRowTranslationMap_surjective⟩

@[simp] lemma cubicThetaRowTranslationEquiv_apply (w : Eisenstein) (r : CubicThetaBottomRow) :
    cubicThetaRowTranslationEquiv (w,r)=cubicThetaPrincipalTranslation w*r.completion := rfl

end CubicFirstMoment

end

end OAI
