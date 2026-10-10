import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialTraceKernel
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialTraceIdentity

namespace OAI

/-! The bounded trace agrees with evaluation on the dense smooth radial core. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralTraceKernel_integral (R : ℝ) (hR : 0 < R) (j : Fin 2) (f : ℝ → ℂ) :
    (∫ r, star (spectralTraceKernelValue R j r)*f r ∂radialPressureMeasure R)=
      ∫ r in (R/2)..R, ((r-R/2 : ℝ) : ℂ)^j.val*f r := by
  rw [spectral_radial_complex_integral R hR.le,intervalIntegral.integral_of_le hR.le]
  rw [← integral_Icc_eq_integral_Ioc]
  have hsub : Icc (R/2) R ⊆ Icc (0 : ℝ) R := by
    intro r hr
    exact ⟨(by linarith [hr.1]),hr.2⟩
  calc
    _ = ∫ r in Icc (0 : ℝ) R,
        (Icc (R/2) R).indicator (fun t => ((t-R/2 : ℝ) : ℂ)^j.val*f t) r := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r _
      by_cases hr : r ∈ Icc (R/2) R
      · have hr0 : (r : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (show 0 < r by linarith [hr.1]))
        simp only [spectralTraceKernelValue,indicator_of_mem hr,map_div₀,map_pow,
          Complex.star_def,Complex.conj_ofReal]
        field_simp
      · simp [spectralTraceKernelValue,hr]
    _ = ∫ r in Icc (R/2) R, ((r-R/2 : ℝ) : ℂ)^j.val*f r := by
      rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr hsub]
    _ = _ := by
      rw [intervalIntegral.integral_of_le (by linarith : R/2 ≤ R)]
      exact integral_Icc_eq_integral_Ioc

theorem spectralRadialSmoothValue_ae (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralRadialSmoothValue R f =ᵐ[radialPressureMeasure R] f :=
  BoundedContinuousFunction.coeFn_toLp 2 (radialPressureMeasure R) ℂ
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ f)

theorem spectralTraceKernel_inner_smooth (R : ℝ) (hR : 0 < R) (j : Fin 2)
    (f : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralTraceKernel R hR j) (spectralRadialSmoothValue R f)=
      ∫ r in (R/2)..R, ((r-R/2 : ℝ) : ℂ)^j.val*f r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, star (spectralTraceKernelValue R j r)*f r ∂radialPressureMeasure R := by
      apply integral_congr_ae
      filter_upwards [spectralTraceKernel_ae R hR j,spectralRadialSmoothValue_ae R f] with r hk hf
      rw [hk,hf,RCLike.inner_apply']
      rfl
    _ = _ := spectralTraceKernel_integral R hR j f

theorem spectralRadialTrace_smooth (R : ℝ) (hR : 0 < R) (f : 𝓢(ℝ,ℂ)) :
    spectralRadialTrace R hR (spectralRadialSmoothEmbedding R f)=f R := by
  change ((2/R : ℝ) : ℂ)*
    (inner ℂ (spectralTraceKernel R hR 0) (spectralRadialValue R (spectralRadialSmoothEmbedding R f))+
     inner ℂ (spectralTraceKernel R hR 1) (spectralRadialDerivative R (spectralRadialSmoothEmbedding R f)))=f R
  rw [spectralRadialSmoothEmbedding_value,spectralRadialSmoothEmbedding_derivative,
    spectralTraceKernel_inner_smooth,spectralTraceKernel_inner_smooth]
  simp only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,one_mul,SchwartzMap.derivCLM_apply]
  have h := spectral_radial_trace_identity R hR f (deriv f) f.continuous
    (SchwartzMap.derivCLM ℂ ℂ f).continuous (fun r _ => f.hasDerivAt r)
  have hg : Continuous (fun r : ℝ => (r-R/2 : ℝ) • deriv f r) :=
    (continuous_id.sub continuous_const).fun_smul (SchwartzMap.derivCLM ℂ ℂ f).continuous
  rw [intervalIntegral.integral_add (f.continuous.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)] at h
  simp only [Complex.real_smul] at h
  rw [← h,← mul_assoc]
  have hc : ((2/R : ℝ) : ℂ)*(R/2 : ℝ)=1 := by
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    field_simp [hR0]
  rw [hc,one_mul]

end DefocusingNLS

end OAI
