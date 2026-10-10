import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def gaussianBandConstant : ℝ := 2*(Real.sqrt (2*Real.pi))⁻¹

theorem gaussianBandConstant_pos : 0 < gaussianBandConstant := by
  unfold gaussianBandConstant
  positivity

theorem standard_gaussian_density_bound :
    gaussianReal 0 1 ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem standard_gaussian_band {r : ℝ} (_hr : 0 ≤ r) :
    gaussianReal 0 1 (Icc (-r) r) ≤ ENNReal.ofReal (gaussianBandConstant*r) := by
  calc
    _ ≤ (ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • (volume : Measure ℝ)) (Icc (-r) r) :=
      standard_gaussian_density_bound _
    _ = _ := by
      rw [Measure.smul_apply,smul_eq_mul,Real.volume_Icc,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold gaussianBandConstant
      ring

theorem gaussian_unit_inner_law {w : Space d} (hw : ‖w‖ = 1) :
    (stdGaussian (Space d)).map (innerSL ℝ w) = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,hw]
  norm_num

theorem gaussian_unit_inner_band {w : Space d} (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | |inner ℝ w x| ≤ r} ≤ ENNReal.ofReal (gaussianBandConstant*r) := by
  have he : {x : Space d | |inner ℝ w x| ≤ r} = (innerSL ℝ w) ⁻¹' Icc (-r) r := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,mem_Icc,innerSL_apply_apply,abs_le]
  rw [he,← Measure.map_apply (innerSL ℝ w).continuous.measurable measurableSet_Icc,
    gaussian_unit_inner_law hw]
  exact standard_gaussian_band hr

end Falconer

end OAI
