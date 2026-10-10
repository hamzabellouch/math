import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOneAtom

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def scalarGaussianOverlap (v : ℝ) : ℝ :=
  ∫ y, (scalarMagnetization (v*y))^2 ∂gaussianReal 0 1

theorem scalarGaussianOverlap_integrable (v : ℝ) :
    Integrable (fun y => (scalarMagnetization (v*y))^2) (gaussianReal 0 1) := by
  apply (integrable_const (1:ℝ)).mono'
    ((scalarMagnetization_lipschitz.continuous.comp (continuous_const.mul continuous_id)).pow 2).aestronglyMeasurable
  filter_upwards [] with y
  change ‖(scalarMagnetization (v*y))^2‖ ≤ 1
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (_:ℝ))] using scalarMagnetization_sq_le_one (v*y)

theorem scalarGaussianValue_derivative (v : ℝ) :
    HasDerivAt scalarGaussianValue (v*(1-scalarGaussianOverlap v)) v := by
  have HC := scalarMagnetization_lipschitz.continuous
  have iu : Integrable (fun y => scalarMagnetization (v*y)) (gaussianReal 0 1) := by
    apply (integrable_const (1:ℝ)).mono' (HC.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    filter_upwards [] with y
    exact scalarMagnetization_abs_le_one (v*y)
  have idu : Integrable (fun y => v*(1-(scalarMagnetization (v*y))^2)) (gaussianReal 0 1) :=
    ((integrable_const (1:ℝ)).sub (scalarGaussianOverlap_integrable v)).const_mul v
  have iyu : Integrable (fun y => y*scalarMagnetization (v*y)) (gaussianReal 0 1) := by
    apply (((memLp_id_gaussianReal 1).integrable (by norm_num)).norm).mono'
      (continuous_id.mul (HC.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    filter_upwards [] with y
    change ‖y*scalarMagnetization (v*y)‖ ≤ ‖y‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (scalarMagnetization_abs_le_one _)
  have hd (y : ℝ) : HasDerivAt (fun y => scalarMagnetization (v*y))
      (v*(1-(scalarMagnetization (v*y))^2)) y := by
    have H := (scalarMagnetization_hasDerivAt (v*y)).comp y ((hasDerivAt_id y).const_mul v)
    rw [scalarMagnetization_derivative_identity] at H
    simpa only [Function.comp_def,mul_one,mul_comm] using H
  have HI := gaussian_integral_mul_eq_integral_deriv _ _ hd iu idu iyu
  rw [integral_const_mul,integral_sub (integrable_const _) (scalarGaussianOverlap_integrable v)] at HI
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at HI
  simpa only [HI,scalarGaussianOverlap] using scalarGaussianValue_hasDerivAt v

theorem gaussian_square_integral : (∫ y : ℝ, y^2 ∂gaussianReal 0 1) = 1 := by
  have H := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at H
  simpa only [integral_id_gaussianReal,sub_zero,NNReal.coe_one] using H

theorem scalarGaussianOverlap_normalized_tendsto :
    Tendsto (fun v : ℝ => scalarGaussianOverlap v/v^2) (𝓝[>] 0) (𝓝 1) := by
  have HB : ∀ᶠ v : ℝ in 𝓝[>] 0, ∀ᵐ y ∂gaussianReal 0 1,
      ‖(scalarMagnetization (v*y)/v)^2‖ ≤ y^2 := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv : 0 < v := hv
    filter_upwards [] with y
    have h : |scalarMagnetization (v*y)/v| ≤ |y| := by
      rw [abs_div,abs_of_pos hv,div_le_iff₀ hv]
      simpa only [abs_mul,abs_of_pos hv,mul_comm] using scalarMagnetization_abs_le (v*y)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq.mpr h
  have HL : ∀ᵐ y ∂gaussianReal 0 1,
      Tendsto (fun v : ℝ => (scalarMagnetization (v*y)/v)^2) (𝓝[>] 0) (𝓝 (y^2)) := by
    filter_upwards [] with y
    have H : HasDerivAt (fun v : ℝ => scalarMagnetization (v*y)) y 0 := by
      have H := (scalarMagnetization_hasDerivAt (0*y)).comp 0 ((hasDerivAt_id (0:ℝ)).mul_const y)
      simpa only [Function.comp_def,id_eq,zero_mul,Real.cosh_zero,one_pow,div_one,one_mul] using H
    have HT := H.tendsto_slope_zero_right
    simp only [zero_add,zero_mul,scalarMagnetization_zero,sub_zero,smul_eq_mul] at HT
    simpa only [div_eq_mul_inv,mul_comm] using HT.pow 2
  have HI := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1) (F := fun v y : ℝ => (scalarMagnetization (v*y)/v)^2) (fun y : ℝ => y^2)
    (Filter.Eventually.of_forall (fun v =>
      (((scalarMagnetization_lipschitz.continuous.comp (continuous_const.mul continuous_id)).div_const v).pow 2).aestronglyMeasurable))
    HB (memLp_id_gaussianReal 2).integrable_sq HL
  simp only [div_pow,integral_div,gaussian_square_integral] at HI
  exact HI
end SK.Analytic

end
end

end

end OAI
