import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialEnergySpace
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialWeightedIntegral

namespace OAI

/-! Bounded dual kernels representing the outer radial trace from an annulus. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralTraceKernelValue (R : ℝ) (j : Fin 2) (r : ℝ) : ℂ :=
  (Icc (R/2) R).indicator (fun t : ℝ => ((t-R/2 : ℝ) : ℂ)^j.val/(t : ℂ)^11) r

theorem spectralTraceKernelValue_bound (R : ℝ) (hR : 0 < R) (j : Fin 2) (r : ℝ) :
    ‖spectralTraceKernelValue R j r‖ ≤ (1+R)/(R/2)^11 := by
  have ha : 0 < R/2 := by linarith
  have hM : 0 ≤ (1+R)/(R/2)^11 := div_nonneg (by linarith) (pow_nonneg ha.le _)
  by_cases hr : r ∈ Icc (R/2) R
  · have hr0 : 0 < r := ha.trans_le hr.1
    rw [spectralTraceKernelValue,indicator_of_mem hr,norm_div]
    simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0]
    have hpow : (R/2)^11 ≤ r^11 := pow_le_pow_left₀ ha.le hr.1 _
    have hnum : ‖((r-R/2 : ℝ) : ℂ)^j.val‖ ≤ 1+R := by
      fin_cases j
      · simp only [pow_zero,norm_one]
        linarith
      · simp only [pow_one,Complex.norm_real,Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [hr.1])]
        linarith [hr.2]
    have hn : |r-R/2|^j.val ≤ 1+R := by
      simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs] using hnum
    exact div_le_div₀ (by linarith) hn (pow_pos ha _) hpow
  · simpa only [spectralTraceKernelValue,indicator_of_notMem hr,norm_zero] using hM

theorem spectralTraceKernelValue_measurable (R : ℝ) (j : Fin 2) :
    Measurable (spectralTraceKernelValue R j) := by
  apply Measurable.indicator _ measurableSet_Icc
  fun_prop

noncomputable def spectralTraceKernel (R : ℝ) (hR : 0 < R) (j : Fin 2) : SpectralRadialL2 R :=
  (MemLp.of_bound (spectralTraceKernelValue_measurable R j).aestronglyMeasurable
    ((1+R)/(R/2)^11) (Filter.Eventually.of_forall (spectralTraceKernelValue_bound R hR j))).toLp
      (spectralTraceKernelValue R j)

theorem spectralTraceKernel_ae (R : ℝ) (hR : 0 < R) (j : Fin 2) :
    spectralTraceKernel R hR j =ᵐ[radialPressureMeasure R] spectralTraceKernelValue R j :=
  MemLp.coeFn_toLp _

noncomputable def spectralRadialTrace (R : ℝ) (hR : 0 < R) : SpectralRadialEnergy R →L[ℂ] ℂ :=
  ((2/R : ℝ) : ℂ) •
    ((innerSL ℂ (spectralTraceKernel R hR 0)).comp (spectralRadialValue R)+
     (innerSL ℂ (spectralTraceKernel R hR 1)).comp (spectralRadialDerivative R))

end DefocusingNLS

end OAI
