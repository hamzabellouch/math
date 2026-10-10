import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveKernel
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialTraceEvaluation

namespace OAI

/-! Bounded positive-radius evaluation and the weighted Volterra reconstruction. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralPrimitiveKernel_integral (R r : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (f : ℝ → ℂ) :
    (∫ s, star (spectralPrimitiveKernelValue R r s)*f s ∂radialPressureMeasure R)=
      ∫ s in r..R, f s := by
  rw [spectral_radial_complex_integral R (hr.le.trans hrR),
    intervalIntegral.integral_of_le (hr.le.trans hrR),← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ s in Icc (0 : ℝ) R, (Icc r R).indicator f s := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      by_cases hs : s ∈ Icc r R
      · have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (hr.trans_le hs.1).ne'
        simp only [spectralPrimitiveKernelValue,indicator_of_mem hs,map_inv₀,map_pow,
          Complex.star_def,Complex.conj_ofReal]
        field_simp
      · simp [spectralPrimitiveKernelValue,hs]
    _ = ∫ s in Icc r R, f s := by
      rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
      have hi : Icc r R ∩ Icc (0 : ℝ) R=Icc r R :=
        inter_eq_left.mpr (fun _ hs => ⟨hr.le.trans hs.1,hs.2⟩)
      rw [hi]
    _ = _ := by
      rw [intervalIntegral.integral_of_le hrR]
      exact integral_Icc_eq_integral_Ioc

theorem spectralPrimitiveKernel_inner_smooth (R r : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (f : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralPrimitiveKernel R r hr) (spectralRadialSmoothValue R f)=
      ∫ s in r..R, f s := by
  rw [L2.inner_def]
  calc
    _ = ∫ s, star (spectralPrimitiveKernelValue R r s)*f s ∂radialPressureMeasure R := by
      apply integral_congr_ae
      filter_upwards [spectralPrimitiveKernel_ae R r hr,spectralRadialSmoothValue_ae R f] with s hk hf
      rw [hk,hf,RCLike.inner_apply']
      rfl
    _ = _ := spectralPrimitiveKernel_integral R r hr hrR f

noncomputable def spectralRadialPointValue (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 < r) :
    SpectralRadialEnergy R →L[ℂ] ℂ :=
  spectralRadialTrace R hR-
    (innerSL ℂ (spectralPrimitiveKernel R r hr)).comp (spectralRadialDerivative R)

theorem spectralRadialPointValue_smooth (R : ℝ) (hR : 0 < R) (r : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (f : 𝓢(ℝ,ℂ)) :
    spectralRadialPointValue R hR r hr (spectralRadialSmoothEmbedding R f)=f r := by
  change spectralRadialTrace R hR (spectralRadialSmoothEmbedding R f)-
    inner ℂ (spectralPrimitiveKernel R r hr)
      (spectralRadialDerivative R (spectralRadialSmoothEmbedding R f))=f r
  rw [spectralRadialTrace_smooth,spectralRadialSmoothEmbedding_derivative,
    spectralPrimitiveKernel_inner_smooth R r hr hrR]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrR
    f.continuous.continuousOn (fun s _ => f.hasDerivAt s)
    ((SchwartzMap.derivCLM ℂ ℂ f).continuous.intervalIntegrable r R)
  change (∫ s in r..R, (SchwartzMap.derivCLM ℂ ℂ f) s)=f R-f r at h
  rw [h]
  abel

theorem spectralRadialPointValue_difference_bound (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) (u : SpectralRadialEnergy R) :
    ‖spectralRadialPointValue R hR r hr u-spectralRadialTrace R hR u‖^2 ≤
      ((r^10)⁻¹/10)*‖spectralRadialDerivative R u‖^2 := by
  have hn := norm_inner_le_norm (𝕜 := ℂ) (spectralPrimitiveKernel R r hr) (spectralRadialDerivative R u)
  have hk := spectralPrimitiveKernel_norm_sq_bound R r hr hrR
  change ‖(spectralRadialTrace R hR u-
    inner ℂ (spectralPrimitiveKernel R r hr) (spectralRadialDerivative R u))-
      spectralRadialTrace R hR u‖^2 ≤ _
  rw [sub_sub_cancel_left,norm_neg]
  calc
    _ ≤ (‖spectralPrimitiveKernel R r hr‖*‖spectralRadialDerivative R u‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = ‖spectralPrimitiveKernel R r hr‖^2*‖spectralRadialDerivative R u‖^2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (sq_nonneg _)

end DefocusingNLS

end OAI
