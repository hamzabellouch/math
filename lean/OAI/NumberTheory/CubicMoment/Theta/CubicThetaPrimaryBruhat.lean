import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedCoefficient

namespace OAI

/-! Rational-cusp geometry for the actual primary projector. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimaryBruhat_identity (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    cubicThetaFullComplex g=
      cubicThetaTranslationMatrix ((g 0 0:ℂ)/(g 1 0:ℂ))*
        cubicThetaInversionMatrix (g 1 0:ℂ)
          (fun he => primary_ne_zero hc (Subtype.ext he))*
        cubicThetaTranslationMatrix ((g 1 1:ℂ)/(g 1 0:ℂ)) := by
  have hq : (g 1 0:ℂ)≠0 := fun he => primary_ne_zero hc (Subtype.ext he)
  have hg : (g 0 0:ℂ)*(g 1 1:ℂ)-(g 0 1:ℂ)*(g 1 0:ℂ)=1 := by
    have he : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      simpa only [Matrix.det_fin_two] using g.property
    exact_mod_cast he
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change (g i j:ℂ)=
    (((!![1,(g 0 0:ℂ)/(g 1 0:ℂ);0,1] : Matrix (Fin 2) (Fin 2) ℂ)*
      !![0,-(g 1 0:ℂ)⁻¹;(g 1 0:ℂ),0])*!![1,(g 1 1:ℂ)/(g 1 0:ℂ);0,1]) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hq]
  all_goals first | (solve | ring) | linear_combination -hg

lemma cubicThetaPrimaryBruhat_point (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (p : CubicThetaPoint) :
    (g • p).val=
      ((cubicThetaInversion (g 1 0:ℂ) (p.val.1+(g 1 1:ℂ)/(g 1 0:ℂ),p.val.2)).1+
          (g 0 0:ℂ)/(g 1 0:ℂ),
        (cubicThetaInversion (g 1 0:ℂ) (p.val.1+(g 1 1:ℂ)/(g 1 0:ℂ),p.val.2)).2) := by
  have hq : (g 1 0:ℂ)≠0 := fun he => primary_ne_zero hc (Subtype.ext he)
  rw [cubicThetaFullPointAction_apply,cubicThetaPrimaryBruhat_identity g hc,
    ←cubicThetaMobius_comp _ _ p.property]
  rw [←cubicThetaMobius_comp _ _ (cubicThetaMobius_height_pos _ p.property),
    cubicThetaMobius_translation]
  rw [cubicThetaMobius_translation ((g 1 1:ℂ)/(g 1 0:ℂ)) p.val,
    cubicThetaMobius_inversion (p := (p.val.1+(g 1 1:ℂ)/(g 1 0:ℂ),p.val.2)) hq p.property]

theorem cubicThetaSelected_primary_cusp (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient
      ((cubicThetaInversion (g 1 0:ℂ) (z,v)).1+(g 0 0:ℂ)/(g 1 0:ℂ),
        (cubicThetaInversion (g 1 0:ℂ) (z,v)).2)=
      cubicThetaProjectedConstant g hc*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
          (z-(g 1 1:ℂ)/(g 1 0:ℂ)+(g 1 1:ℂ),v) := by
  let p : CubicThetaPoint := ⟨(z-(g 1 1:ℂ)/(g 1 0:ℂ),v),hv⟩
  have hp := cubicThetaPrimaryBruhat_point g hc p
  dsimp only [p,Prod.fst,Prod.snd] at hp
  rw [sub_add_cancel] at hp
  have he := cubicThetaNormalizedPrimaryProjection_expansion g hc p
  rw [hp] at he
  exact he

end CubicFirstMoment

end

end OAI
