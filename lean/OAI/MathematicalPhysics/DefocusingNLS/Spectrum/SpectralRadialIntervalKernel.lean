import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveEvaluation

namespace OAI

/-! Local Volterra kernels and their interval-length bound away from the origin. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralRadialMeasure_singleton (R r : ℝ) : radialPressureMeasure R {r}=0 := by
  exact (withDensity_absolutelyContinuous (volume.restrict (Icc (0 : ℝ) R))
    (fun s : ℝ => ENNReal.ofReal ((max s 0)^11))) (by simp)

noncomputable def spectralRadialIntervalKernel (R l r : ℝ) (hl : 0 < l) : SpectralRadialL2 R :=
  (MemLp.of_bound (spectralPrimitiveKernelValue_measurable r l).aestronglyMeasurable
    ((l^11)⁻¹) (Filter.Eventually.of_forall (spectralPrimitiveKernelValue_bound r l hl))).toLp
      (spectralPrimitiveKernelValue r l)

theorem spectralRadialIntervalKernel_ae (R l r : ℝ) (hl : 0 < l) :
    spectralRadialIntervalKernel R l r hl =ᵐ[radialPressureMeasure R] spectralPrimitiveKernelValue r l :=
  MemLp.coeFn_toLp _

theorem spectralRadialIntervalKernel_norm_sq (R l r : ℝ) (hl : 0 < l)
    (hlr : l ≤ r) (hrR : r ≤ R) :
    ‖spectralRadialIntervalKernel R l r hl‖^2=∫ s in l..r, (s^11)⁻¹ := by
  calc
    _ = ∫ s, ‖spectralPrimitiveKernelValue r l s‖^2 ∂radialPressureMeasure R := by
      rw [← real_inner_self_eq_norm_sq]
      change (∫ s, inner ℝ (spectralRadialIntervalKernel R l r hl s)
        (spectralRadialIntervalKernel R l r hl s) ∂radialPressureMeasure R)=_
      apply integral_congr_ae
      filter_upwards [spectralRadialIntervalKernel_ae R l r hl] with s hs
      rw [hs,real_inner_self_eq_norm_sq]
    _ = ∫ s in Icc (0 : ℝ) R, ‖spectralPrimitiveKernelValue r l s‖^2*s^11 := by
      rw [radialPressureMeasure_integral R (hl.le.trans (hlr.trans hrR)),
        intervalIntegral.integral_of_le (hl.le.trans (hlr.trans hrR)),integral_Icc_eq_integral_Ioc]
    _ = ∫ s in Icc (0 : ℝ) R, (Icc l r).indicator (fun s => (s^11)⁻¹) s := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s _
      by_cases hs : s ∈ Icc l r
      · have hs0 := hl.trans_le hs.1
        simp only [spectralPrimitiveKernelValue,indicator_of_mem hs,norm_inv,norm_pow,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs0]
        field_simp
      · simp [spectralPrimitiveKernelValue,hs]
    _ = ∫ s in Icc l r, (s^11)⁻¹ := by
      rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
      have hset : Icc l r ∩ Icc (0 : ℝ) R=Icc l r :=
        inter_eq_left.mpr (fun _ hs => ⟨hl.le.trans hs.1,hs.2.trans hrR⟩)
      rw [hset]
    _ = _ := by rw [intervalIntegral.integral_of_le hlr,integral_Icc_eq_integral_Ioc]

theorem spectralRadialIntervalKernel_bound (R l r : ℝ) (hl : 0 < l)
    (hlr : l ≤ r) (hrR : r ≤ R) :
    ‖spectralRadialIntervalKernel R l r hl‖^2 ≤ (r-l)*(l^11)⁻¹ := by
  rw [spectralRadialIntervalKernel_norm_sq R l r hl hlr hrR]
  have hi : IntervalIntegrable (fun s : ℝ => (s^11)⁻¹) volume l r := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlr
    exact (continuous_id.pow 11).continuousOn.inv₀
      (fun s hs => (pow_pos (hl.trans_le hs.1) 11).ne')
  have h := intervalIntegral.integral_mono_on hlr hi (intervalIntegrable_const)
    (fun s (hs : s ∈ Icc l r) => inv_anti₀ (pow_pos hl 11) (pow_le_pow_left₀ hl.le hs.1 11))
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using h

theorem spectralRadialIntervalKernel_eq_sub (R l r : ℝ) (hl : 0 < l)
    (hlr : l ≤ r) (hrR : r ≤ R) :
    spectralRadialIntervalKernel R l r hl=
      spectralPrimitiveKernel R l hl-spectralPrimitiveKernel R r (hl.trans_le hlr) := by
  apply Lp.ext
  have hn : ∀ᵐ s ∂radialPressureMeasure R, s ≠ r := by
    simp only [ae_iff]
    simpa using spectralRadialMeasure_singleton R r
  filter_upwards [spectralRadialIntervalKernel_ae R l r hl,
    spectralPrimitiveKernel_ae R l hl,spectralPrimitiveKernel_ae R r (hl.trans_le hlr),
    Lp.coeFn_sub (spectralPrimitiveKernel R l hl) (spectralPrimitiveKernel R r (hl.trans_le hlr)),hn]
    with s hi hlv hrv hsub hne
  rw [hi,hsub,Pi.sub_apply,hlv,hrv]
  by_cases hls : l ≤ s
  · by_cases hsr : s < r
    · have hsR : s ≤ R := hsr.le.trans hrR
      simp [spectralPrimitiveKernelValue,mem_Icc,hls,hsr.le,hsR,not_le.mpr hsr]
    · have hrs : r < s := lt_of_le_of_ne (not_lt.mp hsr) (Ne.symm hne)
      by_cases hsR : s ≤ R <;>
        simp [spectralPrimitiveKernelValue,mem_Icc,hls,hrs.le,hsR,not_le.mpr hrs]
  · have hrs : ¬r ≤ s := fun h => hls (hlr.trans h)
    simp [spectralPrimitiveKernelValue,mem_Icc,hls,hrs]

theorem spectralRadialPointValue_increment (R l r : ℝ) (hR : 0 < R) (hl : 0 < l)
    (hlr : l ≤ r) (hrR : r ≤ R) (u : SpectralRadialEnergy R) :
    spectralRadialPointValue R hR r (hl.trans_le hlr) u-spectralRadialPointValue R hR l hl u=
      inner ℂ (spectralRadialIntervalKernel R l r hl) (spectralRadialDerivative R u) := by
  rw [spectralRadialIntervalKernel_eq_sub R l r hl hlr hrR,inner_sub_left]
  change (_-inner ℂ (spectralPrimitiveKernel R r (hl.trans_le hlr)) (spectralRadialDerivative R u))-
    (_-inner ℂ (spectralPrimitiveKernel R l hl) (spectralRadialDerivative R u))=_
  abel

end DefocusingNLS

end OAI
