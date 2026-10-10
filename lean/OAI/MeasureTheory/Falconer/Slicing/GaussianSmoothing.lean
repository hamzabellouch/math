import OAI.MeasureTheory.Falconer.Slicing.GaussianDamping

namespace OAI

/-! # Weighted Cauchy--Schwarz for Gaussian Fourier smoothing -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_fourier_power_integrable (β : Measure (Space d)) [IsFiniteMeasure β]
    (v : Space d) (k : ℕ) :
    Integrable (fun u : Space d => Real.exp (-2*‖u-v‖^2)*
      ‖PlanarFalconer.sourceFourier β u‖^k) := by
  have hG := (PlanarFalconer.gaussian_lebesgue_integrable (V := Space d)
    (by norm_num : (0:ℝ) < 2)).comp_sub_right v
  apply (hG.mul_const ((β.real univ)^k)).mono (by unfold PlanarFalconer.sourceFourier; fun_prop)
  filter_upwards with u
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact norm_charFun_le _

theorem gaussian_translate_integral (v : Space d) :
    (∫ u : Space d, Real.exp (-2*‖u-v‖^2)) = (Real.pi/2)^((d:ℝ)/2) := by
  rw [integral_sub_right_eq_self (fun u : Space d => Real.exp (-2*‖u‖^2)) v]
  simpa only [Space,finrank_euclideanSpace_fin] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space d) (by norm_num : (0:ℝ) < 2)

theorem gaussian_smoothing_square (β : Measure (Space d)) [IsFiniteMeasure β] (v : Space d) :
    ‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2 ≤
      ((Real.pi/2)^((d:ℝ)/2))⁻¹ *
        ∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2 := by
  let C : ℝ := (Real.pi/2)^((d:ℝ)/2)
  have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  have hG := (PlanarFalconer.gaussian_lebesgue_integrable (V := Space d)
    (by norm_num : (0:ℝ) < 2)).comp_sub_right v
  have h1 : Integrable (fun u : Space d =>
      ‖(Real.exp (-2*‖u-v‖^2):ℂ)‖*‖PlanarFalconer.sourceFourier β u‖) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),pow_one] using
      gaussian_fourier_power_integrable β v 1
  have h2 : Integrable (fun u : Space d =>
      ‖(Real.exp (-2*‖u-v‖^2):ℂ)‖*‖PlanarFalconer.sourceFourier β u‖^2) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      gaussian_fourier_power_integrable β v 2
  have h := PlanarFalconer.norm_integral_coeff_square volume
    (fun u : Space d => (Real.exp (-2*‖u-v‖^2):ℂ)) (PlanarFalconer.sourceFourier β)
    hG.ofReal h1 h2
  rw [gaussian_convolution_damped] at h
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < (Real.pi/2)^((d:ℝ)/2) from hC),
    abs_of_pos (Real.exp_pos _),mul_pow] at h
  rw [gaussian_translate_integral] at h
  change C^2*‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2 ≤
    C*(∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2) at h
  have h' : C*‖PlanarFalconer.sourceFourier (gaussianDampedMeasure β) v‖^2 ≤
      ∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2 := by
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [h]
  calc
    _ ≤ (∫ u : Space d, Real.exp (-2*‖u-v‖^2)*‖PlanarFalconer.sourceFourier β u‖^2)/C :=
      (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using h')
    _ = _ := by dsimp [C]; ring

end Falconer

end OAI
