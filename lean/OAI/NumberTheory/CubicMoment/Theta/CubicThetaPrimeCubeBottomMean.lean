import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalPeriodMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFirstBranchMean

namespace OAI

/-! The bottom Hecke branch has the literal cubic residue degree as its
horizontal mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeBottomBranch_point {p : Eisenstein} (hp : primaryPrime p)
    (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBranchPoint hp 0 b (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPoint (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))
        ((z+3*(b:ℂ))/(p^3:Eisenstein)) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  apply Subtype.ext
  change ((p:ℂ)^0/(p:ℂ)^3*z+((3*b:Eisenstein):ℂ)/(p:ℂ)^3,
    (‖(p:ℂ)‖^0/‖(p:ℂ)‖^3)*v)=((z+3*(b:ℂ))/(p^3:Eisenstein),v/‖(p:ℂ)‖^3)
  apply Prod.ext
  · push_cast
    rw [show ((3:Eisenstein):ℂ)=3 from
      map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
    field_simp [hpC]
  · field_simp [hn]

lemma cubicThetaPrimeCubeBottom_periodization {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPeriodization (p^3)
        (cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
          (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))) z := by
  unfold cubicThetaPrimeCubeBottomFunctionSum cubicThetaHorizontalPeriodization
  apply tsum_congr
  intro r
  rw [cubicThetaPrimeCubeBottomBranch_point]
  rfl

theorem cubicThetaPrimeCubeBottom_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,
      cubicThetaPrimeCubeBottomFunctionSum hp F.val (cubicThetaHorizontalPoint v hv z))=
    (norm (p^3):ℂ)*∫ z in cubicThetaHorizontalCell,
      cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) z := by
  simp_rw [cubicThetaPrimeCubeBottom_periodization]
  exact cubicThetaHorizontalPeriodization_mean (pow_ne_zero _ hp.2.ne_zero) _
    (cubicThetaSectionHorizontal_periodic F _ _)

end CubicFirstMoment

end

end OAI
