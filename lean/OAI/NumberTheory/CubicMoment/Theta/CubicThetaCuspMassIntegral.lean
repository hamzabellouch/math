import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspDerivativeIntegral

namespace OAI

/-! Integrability of the actual cutoff cusp mass, with the exact v^-3
density, including the zero extension below height one. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_mass_bound (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    ‖cubicThetaCuspCutoffSection δ F z v‖^2/v^3≤cubicThetaCuspCoordinateEnergy δ F (z,v)/v^3 := by
  apply div_le_div_of_nonneg_right _ (pow_nonneg hv.le 3)
  rw [cubicThetaCuspCoordinateEnergy_norm δ F z hv,cubicThetaCuspCutoffSection,norm_mul,mul_pow]
  have hunit : ‖cubicThetaCuspCutoff v‖^2≤1 := by
    nlinarith [cubicThetaCuspCutoff_norm v,_root_.norm_nonneg (cubicThetaCuspCutoff v)]
  calc
    _ ≤ 1*‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2 :=
      mul_le_mul_of_nonneg_right hunit (sq_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact le_add_of_nonneg_right (cubicThetaSectionEnergy_nonneg F _)

lemma cubicThetaCuspCutoff_mass_integrable_high (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) := by
  apply (cubicThetaCuspCoordinateEnergy_integrable δ F (le_refl 1)).mono'
  · exact (((cubicThetaCuspCutoffSection_continuous δ F).measurable.norm.pow_const 2).div
      (measurable_snd.pow_const 3)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hv : 0<y.2 := lt_trans zero_lt_one hy.2
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hv.le 3))]
    exact cubicThetaCuspCutoff_mass_bound δ F y.1 hv

theorem cubicThetaCuspCutoff_mass_integrable (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)) := by
  apply cubicThetaCuspCell_integrable_extend (cubicThetaCuspCutoff_mass_integrable_high δ F)
  intro z v hv
  simp only [cubicThetaCuspCutoffSection,cubicThetaCuspCutoff_zero hv,zero_mul,
    norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

end CubicFirstMoment

end

end OAI
