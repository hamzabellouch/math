import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveResidueObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedResidueObservation

namespace OAI

/-! Scaling of the actual pole kernel for arbitrary positive-cutoff tests. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaFullPoleWeightIntegral (h : Eisenstein) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
    cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)

lemma cubicThetaPositivePoleRadialTest_weight {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    cubicThetaPositiveRadialTest h W ε (4/3)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        cubicThetaFullPoleWeightIntegral h W := by
  unfold cubicThetaFullPoleWeightIntegral
  rw [←cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW]
  rw [cubicThetaPositiveRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hv0 : 0<v := hε.trans hv
  rw [show star (W v)*(v:ℂ)^(4/3:ℂ)*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t)/(v:ℂ)^3=
      star (W v)*((v:ℂ)^(4/3:ℂ)*
        (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t))/(v:ℂ)^3 by ring,
    cubicThetaPoleHeat_whittaker hh hv0]
  ring

lemma cubicThetaFullPoleWeightIntegral_scale {a : Eisenstein} (ha : a≠0)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    cubicThetaFullPoleWeightIntegral (a*h)
        (cubicThetaRadialWeightScale ‖(a:ℂ)‖
          (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)=
      (‖(a:ℂ)‖:ℂ)^2*cubicThetaFullPoleWeightIntegral h W := by
  let r := ‖(a:ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  let V := cubicThetaRadialWeightScale r hr W
  unfold cubicThetaFullPoleWeightIntegral
  rw [cubicThetaRowFrequency_norm_mul]
  have he (v : ℝ) : cubicThetaWhittaker ((‖(a:ℂ)‖*‖cubicThetaRowFrequency h‖)*v)=
      cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*(r*v)) := by
    congr 1
    dsimp only [r]
    ring
  simp_rw [he]
  rw [cubicThetaRadialIntegral_dilate r hr V
    (fun v => cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  change star (W (r*(v/r)))/(v:ℂ)^3*_=star (W v)/(v:ℂ)^3*_
  rw [mul_div_cancel₀ v hr.ne']

theorem cubicThetaPositivePoleRadialTest_scale {a h : Eisenstein} (ha : a≠0) (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    cubicThetaPositiveRadialTest (a*h)
        (cubicThetaRadialWeightScale ‖(a:ℂ)‖
          (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W) (ε/‖(a:ℂ)‖) (4/3)=
      ((‖(a:ℂ)‖:ℂ)^(4/3:ℂ))*cubicThetaPositiveRadialTest h W ε (4/3) := by
  have hr : 0<‖(a:ℂ)‖ := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hp : ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖^2=‖(a:ℂ)‖^(4/3:ℝ) := by
    rw [←Real.rpow_natCast ‖(a:ℂ)‖ 2,←Real.rpow_add hr]
    norm_num
  rw [cubicThetaPositivePoleRadialTest_weight (mul_ne_zero ha hh) _ (div_pos hε hr)
      (cubicThetaRadialWeightScale_positive_low hr W hW),
    cubicThetaPositivePoleRadialTest_weight hh W hε hW,cubicThetaPoleFactor_mul ha hh,
    cubicThetaFullPoleWeightIntegral_scale ha h W]
  rw [show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hr.le]
  push_cast
  have hpC := congrArg (fun x : ℝ => (x:ℂ)) hp
  push_cast at hpC
  linear_combination
    ((2:ℂ)*(((cubicThetaRowHeatScale h)^(1/6:ℝ):ℝ):ℂ)/
      (‖cubicThetaRowFrequency h‖:ℂ)*cubicThetaFullPoleWeightIntegral h W)*hpC

end CubicFirstMoment

end

end OAI
