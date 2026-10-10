import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeZeroMode

namespace OAI

/-! The second character branch is an integral horizontal dilation.
Its constant mode can therefore be reduced by the actual cell integral. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSecondBranch_point {p : Eisenstein} (hp : primaryPrime p)
    (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3) b (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPoint (‖(p:ℂ)‖*v)
        (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)
        ((p:ℂ)*z+3*(b:ℂ)/(p:ℂ)) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  apply Subtype.ext
  change ((p:ℂ)^2/(p:ℂ)^1*z+((3*b:Eisenstein):ℂ)/(p:ℂ)^1,
    (‖(p:ℂ)‖^2/‖(p:ℂ)‖^1)*v)=((p:ℂ)*z+3*(b:ℂ)/(p:ℂ),‖(p:ℂ)‖*v)
  apply Prod.ext
  · push_cast
    rw [show ((3:Eisenstein):ℂ)=3 from
      map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
    field_simp [hpC]
  · field_simp [hn]

lemma cubicThetaPrimeCubeSecondBranch_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    F.val (cubicThetaPrimeCubeBranchPoint hp (⟨2,by decide⟩:Fin 3) b
      (cubicThetaHorizontalPoint v hv z))=
    cubicThetaSectionHorizontal F (‖(p:ℂ)‖*v)
      (mul_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) hv)
      ((p:ℂ)*z+3*(b:ℂ)/(p:ℂ)) := by
  rw [cubicThetaPrimeCubeSecondBranch_point]
  rfl

end CubicFirstMoment

end

end OAI
