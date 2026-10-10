import OAI.MeasureTheory.Falconer.Slicing.GaussianFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Removing Gaussian damping while retaining the ambient-dimensional phase. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

theorem gaussianFourierKernel_continuous_damping {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (ξ : Space n) :
    ContinuousAt (fun ε : ℝ =>
      gaussianFourierKernel n ((ε : ℂ) + (b : ℂ)*Complex.I) ξ) 0 := by
  have hne : (b : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') Complex.I_ne_zero
  unfold gaussianFourierKernel
  apply ContinuousAt.mul
  · have ht : ContinuousAt (fun ε : ℝ =>
        (Real.pi : ℂ) / ((ε : ℂ) + (b : ℂ)*Complex.I)) 0 :=
      continuousAt_const.div (by fun_prop) (by simpa using hne)
    have hp : ContinuousAt (fun z : ℂ => z^((n : ℂ)/2))
        ((Real.pi : ℂ) / ((0 : ℂ) + (b : ℂ)*Complex.I)) :=
      Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (by simp [Complex.div_re])) (by simpa using (show 0 < (n : ℝ)/2 by positivity))
    exact hp.comp (f := fun ε : ℝ =>
      (Real.pi : ℂ) / ((ε : ℂ) + (b : ℂ)*Complex.I)) (x := 0) ht
  · apply Complex.continuous_exp.continuousAt.comp
    exact continuousAt_const.div (by fun_prop) (by simpa using hne)

theorem gaussianFourierKernel_integral_limit {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (φ : 𝓢(Space n, ℂ)) :
    Tendsto (fun c : ℝ => ∫ ξ : Space n,
      gaussianFourierKernel n (((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) ξ * φ ξ) atTop
      (𝓝 (∫ ξ : Space n, gaussianFourierKernel n ((b : ℂ)*Complex.I) ξ * φ ξ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (Real.pi/b)^((n : ℝ)/2) * ‖φ ξ‖) _ _ (φ.integrable.norm.const_mul _) _
  · filter_upwards with c
    exact (show Continuous (fun ξ : Space n =>
      gaussianFourierKernel n (((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) ξ * φ ξ) by
        unfold gaussianFourierKernel; fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c hc
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (gaussianFourierKernel_damped_bound hb (inv_nonneg.mpr hc) ξ) (norm_nonneg _)
  · filter_upwards with ξ
    have hh := (gaussianFourierKernel_continuous_damping hn hb ξ).tendsto.comp
      tendsto_inv_atTop_zero
    simpa using hh.mul_const (φ ξ)

theorem gaussian_integral_damping_limit {n : ℕ} {b : ℝ} (φ : 𝓢(Space n, ℂ)) :
    Tendsto (fun c : ℝ => ∫ x : Space n,
      Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x)
      atTop (𝓝 (∫ x : Space n,
        Complex.exp (-((b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖𝓕 φ x‖) _ _ (𝓕 φ).integrable.norm _
  · filter_upwards with c
    exact (show Continuous (fun x : Space n =>
      Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) *
        𝓕 φ x) by fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c hc
    filter_upwards with x
    rw [norm_mul]
    have hh : ‖Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) *
        (‖x‖^2 : ℝ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp only [mul_zero, add_zero, zero_add, sub_zero, mul_one]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (inv_nonneg.mpr hc)) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    have hh := ((tendsto_inv_atTop_zero.ofReal.add_const ((b : ℂ)*Complex.I)).neg.mul_const
      ((‖x‖^2 : ℝ) : ℂ)).cexp
    simpa using hh.mul_const (𝓕 φ x)

theorem gaussian_oscillatory_pairing {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (φ : 𝓢(Space n, ℂ)) :
    (∫ x : Space n, Complex.exp (-((b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x) =
      ∫ ξ : Space n, gaussianFourierKernel n ((b : ℂ)*Complex.I) ξ * φ ξ := by
  have he : (fun c : ℝ => ∫ x : Space n,
      Complex.exp (-(((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * 𝓕 φ x)
      =ᶠ[atTop] (fun c : ℝ => ∫ ξ : Space n,
        gaussianFourierKernel n (((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I) ξ * φ ξ) := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact gaussian_fourier_pairing (a := ((c⁻¹ : ℝ) : ℂ) + (b : ℂ)*Complex.I)
      (by simpa using inv_pos.mpr (show 0 < c from hc)) φ
  exact tendsto_nhds_unique (gaussian_integral_damping_limit φ)
    ((gaussianFourierKernel_integral_limit hn hb φ).congr' he.symm)

theorem gaussian_fresnel_coefficient (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ((Real.pi : ℂ) / ((b : ℂ)*Complex.I))^((n : ℂ)/2) =
      ((Real.pi/b)^((n : ℝ)/2) : ℝ) *
        Complex.exp (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I) := by
  have hr : 0 < Real.pi/b := div_pos Real.pi_pos hb
  have hi : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have he : (Real.pi : ℂ) / ((b : ℂ)*Complex.I) =
      ((Real.pi/b : ℝ) : ℂ)*(-Complex.I) := by
    push_cast
    field_simp
    simp [Complex.I_sq, div_eq_mul_inv]
  rw [he, Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hi),
    Complex.log_ofReal_mul hr hi, Complex.log_neg_I]
  have hex : (((Real.log (Real.pi/b) : ℝ) : ℂ) + (-((Real.pi : ℂ)/2)*Complex.I)) *
        ((n : ℂ)/2) =
      ((Real.log (Real.pi/b) : ℝ) : ℂ)*((n : ℂ)/2) +
        (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I) := by ring
  rw [hex, Complex.exp_add]
  congr 1
  rw [Real.rpow_def_of_pos hr]
  push_cast
  rfl

theorem gaussian_stationary_identity {n : ℕ} (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) (φ : 𝓢(Space n, ℂ)) :
    (∫ x : Space n, Complex.exp (-((b : ℂ)*Complex.I) * (‖x‖^2 : ℝ)) * φ x) =
      (((Real.pi/b)^((n : ℝ)/2) : ℝ) *
        Complex.exp (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I)) *
      ∫ ξ : Space n, Complex.exp
        (Complex.I*((Real.pi : ℂ)^2*(‖ξ‖^2 : ℝ)/(b : ℂ))) * 𝓕⁻ φ ξ := by
  have hh := gaussian_oscillatory_pairing hn hb (𝓕⁻ φ)
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  rw [hh]
  simp only [gaussianFourierKernel, gaussian_fresnel_coefficient n hb]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  have he : -(Real.pi : ℂ)^2*(‖ξ‖^2 : ℝ)/((b : ℂ)*Complex.I) =
      Complex.I*((Real.pi : ℂ)^2*(‖ξ‖^2 : ℝ)/(b : ℂ)) := by
    field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
    simp [Complex.I_sq]
  rw [he]
  ring

end Falconer

end OAI
