import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCompact

namespace OAI

/-! The actual height-two cusp strip has finite hyperbolic volume.
The proof keeps the horizontal cell and v^-3 density explicit. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCuspStrip_constant_integrable :
    IntegrableOn (fun _ : CubicThetaPoint => (1:ℝ)) (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hh : IntegrableOn (fun _ : ℂ => (1:ℝ)) cubicThetaHorizontalCell :=
    integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(-3:ℝ)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  have hd : IntegrableOn (fun y : ℂ × ℝ => (1:ℝ)/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
    have he (v : ℝ) : v^(-3:ℝ)=(v^3)⁻¹ := by
      rw [show (-3:ℝ)=((-3:ℤ):ℝ) by norm_num,Real.rpow_intCast]
      simp only [zpow_neg]
      rfl
    change Integrable (fun y : ℂ × ℝ => (1:ℝ)/y.2^3)
      (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _)
    simpa only [one_mul,he,one_div] using hm
  apply (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)
    (fun _ => (1:ℝ))).mpr
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)]
  exact hd

instance cubicThetaStrip_finiteMeasure :
    IsFiniteMeasure (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ)≠0)).mp
    cubicThetaCuspStrip_constant_integrable

end CubicFirstMoment

end

end OAI
