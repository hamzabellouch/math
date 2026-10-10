import OAI.MeasureTheory.Falconer.Fourier.QuadraticKernelBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

 theorem quadraticFourierKernel_continuous_damping {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    ContinuousAt (fun ε : ℝ => quadraticFourierKernel ((ε:ℂ)+(b:ℂ)*Complex.I) ξ) 0 := by
  have hn : (b:ℂ)*Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') Complex.I_ne_zero
  unfold quadraticFourierKernel
  apply ContinuousAt.mul
  · have ht : ContinuousAt (fun ε : ℝ => (Real.pi:ℂ)/((ε:ℂ)+(b:ℂ)*Complex.I)) 0 :=
      continuousAt_const.div (by fun_prop) (by simpa using hn)
    have hp : ContinuousAt (fun z : ℂ => z^(1/2:ℂ))
        ((Real.pi:ℂ)/((0:ℂ)+(b:ℂ)*Complex.I)) :=
      Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (show 0 ≤ ((Real.pi:ℂ)/((0:ℂ)+(b:ℂ)*Complex.I)).re by simp [Complex.div_re]))
        (show 0 < (1/2:ℂ).re by norm_num)
    exact hp.comp (f := fun ε : ℝ => (Real.pi:ℂ)/((ε:ℂ)+(b:ℂ)*Complex.I)) (x := 0) ht
  · apply Complex.continuous_exp.continuousAt.comp
    exact continuousAt_const.div (by fun_prop) (by simpa using mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) hn)

 theorem quadraticFourierKernel_integral_limit {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) :
    Tendsto (fun c : ℝ => ∫ ξ : ℝ,
      quadraticFourierKernel (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) atTop
      (𝓝 (∫ ξ : ℝ, quadraticFourierKernel ((b:ℂ)*Complex.I) ξ * φ ξ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (Real.pi/b)^(1/2:ℝ)*‖φ ξ‖) _ _ (φ.integrable.norm.const_mul _) _
  · filter_upwards with c
    exact (show Continuous (fun ξ : ℝ =>
      quadraticFourierKernel (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) by
        unfold quadraticFourierKernel; fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with c hc
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (quadraticFourierKernel_damped_bound hb (inv_nonneg.mpr hc) ξ) (norm_nonneg _)
  · filter_upwards with ξ
    have hh := (quadraticFourierKernel_continuous_damping hb ξ).tendsto.comp tendsto_inv_atTop_zero
    simpa using hh.mul_const (φ ξ)

 theorem quadraticGaussian_integral_limit {b : ℝ} (φ : 𝓢(ℝ,ℂ)) :
    Tendsto (fun c : ℝ => ∫ x : ℝ,
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖𝓕 φ x‖) _ _ (𝓕 φ).integrable.norm _
  · filter_upwards with c
    exact (show Continuous (fun x : ℝ =>
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) by fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with c hc
    filter_upwards with x
    rw [norm_mul]
    have hh : ‖Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,← Complex.ofReal_pow]
      simp only [mul_zero,add_zero,zero_add,sub_zero,mul_one]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hc)) (sq_nonneg x)
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    have hh := ((tendsto_inv_atTop_zero.ofReal.add_const ((b:ℂ)*Complex.I)).neg.mul_const ((x:ℂ)^2)).cexp
    simpa using hh.mul_const (𝓕 φ x)

 theorem quadratic_oscillatory_pairing {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : ℝ, quadraticFourierKernel ((b:ℂ)*Complex.I) ξ * φ ξ := by
  have he : (fun c : ℝ => ∫ x : ℝ,
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) =ᶠ[atTop]
      (fun c : ℝ => ∫ ξ : ℝ,
      quadraticFourierKernel (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) := by
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with c hc
    exact quadraticGaussian_pairing (a := ((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)
      (by simpa using inv_pos.mpr (show 0 < c from hc)) φ
  exact tendsto_nhds_unique (quadraticGaussian_integral_limit φ)
    ((quadraticFourierKernel_integral_limit hb φ).congr' he.symm)

end PlanarFalconer

end OAI
