import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRemainderBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCompact
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticSection
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! The literal arithmetic remainder is square integrable in every
integral cusp in its initial half-plane. The bound keeps the exact
hyperbolic density rather than replacing the cusp by a finite region. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticRemainder_cusp_mass_bound
    (δ : SL(2,Eisenstein)) (z : ℂ) {v R : ℝ} (hv : 2≤v)
    (hz : Complex.normSq z≤R) {s : ℂ} (hs : 3<s.re) :
    ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖^2/v^3≤
      (cubicThetaCuspRemainderConstant s R)^2*v^(5-2*s.re) := by
  have hv0 : 0<v := by linarith
  have hb := cubicThetaArithmeticRemainder_cusp_bound δ z hv hz hs
  have hsq := mul_self_le_mul_self (_root_.norm_nonneg _) hb
  have he : (v^(4-s.re))^2/v^3=v^(5-2*s.re) := by
    rw [← Real.rpow_mul_natCast hv0.le,← Real.rpow_sub_natCast hv0.ne']
    congr 1
    norm_num
    ring
  calc
    _ ≤ (cubicThetaCuspRemainderConstant s R*v^(4-s.re))^2/v^3 :=
      div_le_div_of_nonneg_right (by simpa only [pow_two] using hsq) (pow_nonneg hv0.le 3)
    _ = _ := by rw [mul_pow,mul_div_assoc,he]

lemma cubicThetaArithmeticRemainder_cusp_mass_continuousOn
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 2<s.re) :
    ContinuousOn (fun y : ℂ × ℝ =>
      ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) y) s‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  intro y hy
  have hv : 0<y.2 := lt_trans (by norm_num : (0:ℝ)<2) hy.2
  have hR := (cubicThetaArithmeticRemainder_continuousAt hs
    (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) hv)).comp
    (cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ) hv).continuousAt
  exact ((hR.norm.pow 2).div (continuousAt_snd.pow 3) (pow_ne_zero 3 hv.ne')).continuousWithinAt

theorem cubicThetaArithmeticRemainder_cusp_mass_integrable
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (fun y : ℂ × ℝ =>
      ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) y) s‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  obtain ⟨R,_,hR⟩ := cubicThetaHorizontalCell_normSq_bound
  have hh : IntegrableOn (fun _ : ℂ => (cubicThetaCuspRemainderConstant s R)^2)
      cubicThetaHorizontalCell := integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(5-2*s.re)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  apply hm.mono'
  · exact (cubicThetaArithmeticRemainder_cusp_mass_continuousOn δ (by linarith)).aestronglyMeasurable
      (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hy0 : 0<y.2 := lt_trans (by norm_num : (0:ℝ)<2) hy.2
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hy0.le 3))]
    exact cubicThetaArithmeticRemainder_cusp_mass_bound δ y.1 hy.2.le (hR y.1 hy.1) hs

end CubicFirstMoment

end

end OAI
