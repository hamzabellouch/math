import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspFourierNormalization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatScaling

namespace OAI

/-! An integrable scalar majorant for the fixed radial testing weights. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialWeight_bounded (W : C_c(ℝ,ℂ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ v, ‖W v‖≤C := by
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun v => ?_⟩
  by_cases hv : v∈tsupport W
  · exact (hC v hv).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hv,norm_zero]
    exact le_max_right _ _

lemma cubicThetaRadialWeight_integrable (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun v : ℝ => ‖W v‖/v^2) (Ioi (2:ℝ)) := by
  obtain ⟨C,hC,hW⟩ := cubicThetaRadialWeight_bounded W
  have hp : IntegrableOn (fun v : ℝ => v^(-2:ℝ)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  apply (hp.const_mul C).mono'
    ((W.continuous.measurable.norm.div (measurable_id.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change 2<v at hv
  change ‖‖W v‖/v^2‖≤C*v^(-2:ℝ)
  rw [Real.norm_of_nonneg (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))]
  have he : v^(-2:ℝ)=(v^2)⁻¹ := by
    rw [Real.rpow_neg (by linarith : 0≤v),Real.rpow_two]
  rw [he,← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hW v) (sq_nonneg _)

def cubicThetaRadialWeightMass (W : C_c(ℝ,ℂ)) : ℝ :=
  ∫ v in Ioi (2:ℝ), ‖W v‖/v^2

lemma cubicThetaRadialWeightMass_nonneg (W : C_c(ℝ,ℂ)) :
    0≤cubicThetaRadialWeightMass W :=
  integral_nonneg (fun v => div_nonneg (_root_.norm_nonneg (W v)) (sq_nonneg v))

end CubicFirstMoment

end

end OAI
