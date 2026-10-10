import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFrequencyScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierRadialScaling

namespace OAI

/-! Simultaneous scaling of the frequency and radial test at the cubic pole. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPoleRadialWeightIntegral (h : Eisenstein) (W : C_c(ℝ,ℂ)) : ℂ :=
  ∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
    cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)

lemma cubicThetaPoleRadialTest_weight {h : Eisenstein} (hh : h≠0) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierRadialTest h W (4/3)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        cubicThetaPoleRadialWeightIntegral h W := by
  rw [cubicThetaPoleRadialTest_whittaker hh]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  ring

lemma cubicThetaPoleRadialWeightIntegral_scale {a : Eisenstein} (ha : a≠0)
    (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(a:ℂ)‖,W v=0) :
    cubicThetaPoleRadialWeightIntegral (a*h)
        (cubicThetaRadialWeightScale ‖(a:ℂ)‖
          (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)=
      (‖(a:ℂ)‖:ℂ)^2*cubicThetaPoleRadialWeightIntegral h W := by
  let r := ‖(a:ℂ)‖
  have hr0 : 0<r := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hr : 1≤r := by
    have hq := one_le_norm ha
    change 1≤Complex.normSq (a:ℂ) at hq
    rw [Complex.normSq_eq_norm_sq] at hq
    nlinarith
  let V := cubicThetaRadialWeightScale r hr0 W
  have hV : ∀ v≤(2:ℝ),V v=0 := by
    intro v hv
    change W (r*v)=0
    exact hW _ (by nlinarith)
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    exact hW _ (by linarith)
  unfold cubicThetaPoleRadialWeightIntegral
  rw [cubicThetaRadialIntegral_zero_extension V hV,
    cubicThetaRadialIntegral_zero_extension W hW2,cubicThetaRowFrequency_norm_mul]
  have he (v : ℝ) : cubicThetaWhittaker ((‖(a:ℂ)‖*‖cubicThetaRowFrequency h‖)*v)=
      cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*(r*v)) := by
    congr 1
    dsimp only [r]
    ring
  simp_rw [he]
  rw [cubicThetaRadialIntegral_dilate r hr0 V
    (fun v => cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  change star (W (r*(v/r)))/(v:ℂ)^3*_=star (W v)/(v:ℂ)^3*_
  rw [mul_div_cancel₀ v hr0.ne']

theorem cubicThetaPoleRadialTest_scale {a h : Eisenstein} (ha : a≠0) (hh : h≠0)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(a:ℂ)‖,W v=0) :
    cubicThetaFourierRadialTest (a*h)
        (cubicThetaRadialWeightScale ‖(a:ℂ)‖
          (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W) (4/3)=
      ((‖(a:ℂ)‖:ℂ)^(4/3:ℂ))*cubicThetaFourierRadialTest h W (4/3) := by
  have hr : 0<‖(a:ℂ)‖ := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hp : ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖^2=‖(a:ℂ)‖^(4/3:ℝ) := by
    rw [←Real.rpow_natCast ‖(a:ℂ)‖ 2,←Real.rpow_add hr]
    norm_num
  rw [cubicThetaPoleRadialTest_weight (mul_ne_zero ha hh),
    cubicThetaPoleRadialTest_weight hh,cubicThetaPoleFactor_mul ha hh,
    cubicThetaPoleRadialWeightIntegral_scale ha h W hW]
  rw [show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hr.le]
  push_cast
  have hpC := congrArg (fun x : ℝ => (x:ℂ)) hp
  push_cast at hpC
  linear_combination
    ((2:ℂ)*(((cubicThetaRowHeatScale h)^(1/6:ℝ) :ℝ):ℂ)/
      (‖cubicThetaRowFrequency h‖:ℂ)*cubicThetaPoleRadialWeightIntegral h W)*hpC

end CubicFirstMoment

end

end OAI
