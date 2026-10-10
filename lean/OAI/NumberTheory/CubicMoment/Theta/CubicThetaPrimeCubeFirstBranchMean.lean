import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFirstPeriodMean
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSecondBranchCoordinates

namespace OAI

/-! The actual first character branch, in the horizontal cell used for
arithmetic cusp coefficients. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstBranch_point {p : Eisenstein} (hp : primaryPrime p)
    (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeBranchPoint hp 1 b (cubicThetaHorizontalPoint v hv z)=
      cubicThetaHorizontalPoint (v/‖(p:ℂ)‖)
        (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))
        (z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hn : ‖(p:ℂ)‖≠0 := norm_ne_zero_iff.mpr hpC
  apply Subtype.ext
  change ((p:ℂ)^1/(p:ℂ)^2*z+((3*b:Eisenstein):ℂ)/(p:ℂ)^2,
    (‖(p:ℂ)‖^1/‖(p:ℂ)‖^2)*v)=(z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2,v/‖(p:ℂ)‖)
  apply Prod.ext
  · push_cast
    rw [show ((3:Eisenstein):ℂ)=3 from
      map_ofNat (eisensteinRing.subtype : Eisenstein →+* ℂ) 3]
    field_simp [hpC]
  · field_simp [hn]

lemma cubicThetaPrimeCubeFirstBranch_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (b : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    F.val (cubicThetaPrimeCubeBranchPoint hp 1 b (cubicThetaHorizontalPoint v hv z))=
    cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖)
      (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))
      (z/(p:ℂ)+3*(b:ℂ)/(p:ℂ)^2) := by
  rw [cubicThetaPrimeCubeFirstBranch_point]
  rfl

lemma cubicThetaPrimeCubeFirstBranch_periodization {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z)=
      cubicThetaPrimeCubeFirstPeriodization p
        (cubicThetaSectionHorizontal F (v/‖(p:ℂ)‖)
          (div_pos hv (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))) z := by
  rw [cubicThetaPrimeCubeFirstPeriodization_units hp]
  unfold cubicThetaPrimeCubeUnitFunctionSum
  apply tsum_congr
  intro u
  simp only [Fin.val_one,pow_one,cubicThetaPrimeCubeFirstTerm]
  rw [cubicThetaPrimeCubeFirstBranch_section]

theorem cubicThetaPrimeCubeFirstBranch_mean {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,
      cubicThetaPrimeCubeUnitFunctionSum hp 1 F.val (cubicThetaHorizontalPoint v hv z))=0 := by
  simp_rw [cubicThetaPrimeCubeFirstBranch_periodization hp]
  exact cubicThetaPrimeCubeFirstPeriodization_mean hp _ (cubicThetaSectionHorizontal_periodic F _ _)

end CubicFirstMoment

end

end OAI
