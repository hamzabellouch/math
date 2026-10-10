import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHorizontalMean

namespace OAI

/-! A proof-independent scalar horizontal mean for actual sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_coordinates (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionFunction F p.val=F.val p := by
  change F.val (cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p))=F.val p
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  exact congrArg F.val h

def cubicThetaSectionMean (F : CubicThetaSection) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,cubicThetaSectionFunction F (z,v)

lemma cubicThetaSectionMean_eq (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    cubicThetaSectionMean F v=
      ∫ z in cubicThetaHorizontalCell,cubicThetaSectionHorizontal F v hv z := by
  unfold cubicThetaSectionMean
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  exact cubicThetaSectionFunction_apply F hv

theorem cubicThetaSectionMean_hecke {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    cubicThetaSectionMean (cubicThetaPrimeCubeHecke hp F) v=
      cubicThetaSectionMean F (‖(p:ℂ)‖^3*v)+
        (norm (p^3):ℂ)*cubicThetaSectionMean F (v/‖(p:ℂ)‖^3) := by
  have hn : 0<‖(p:ℂ)‖^3 := pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3
  rw [cubicThetaSectionMean_eq _ _ hv,cubicThetaSectionMean_eq _ _ (mul_pos hn hv),
    cubicThetaSectionMean_eq _ _ (div_pos hv hn)]
  exact cubicThetaPrimeCubeHecke_horizontal_mean hp F v hv

end CubicFirstMoment

end

end OAI
