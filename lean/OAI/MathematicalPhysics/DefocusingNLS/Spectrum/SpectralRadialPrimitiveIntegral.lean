import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialIntervalKernel
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace OAI

/-! Local unweighted integrability and the fundamental theorem for radial energy vectors. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

private theorem intervalKernel_cancel (l U r : ℝ) (hl : 0 < l) (hr : 0 ≤ r)
    (f : ℝ → ℂ) :
    (ENNReal.ofReal ((max r 0)^11)).toReal •
      (star (spectralPrimitiveKernelValue U l r)*f r)=(Icc l U).indicator f r := by
  rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr]
  by_cases hm : r ∈ Icc l U
  · have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (hl.trans_le hm.1).ne'
    simp only [spectralPrimitiveKernelValue,indicator_of_mem hm,map_inv₀,map_pow,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul,Complex.ofReal_pow]
    field_simp
  · simp [spectralPrimitiveKernelValue,hm]

theorem spectralRadialL2_intervalIntegrable (R l U : ℝ) (hl : 0 < l)
    (hlU : l ≤ U) (hUR : U ≤ R) (u : SpectralRadialL2 R) :
    IntervalIntegrable (fun r => u r) volume l U := by
  have hi : Integrable (fun r => star (spectralPrimitiveKernelValue U l r)*u r)
      (radialPressureMeasure R) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (spectralRadialIntervalKernel R l U hl) u).congr
    filter_upwards [spectralRadialIntervalKernel_ae R l U hl] with r hr
    rw [hr,RCLike.inner_apply']
    rfl
  have hw : Integrable (fun r => (ENNReal.ofReal ((max r 0)^11)).toReal •
      (star (spectralPrimitiveKernelValue U l r)*u r)) (volume.restrict (Icc (0 : ℝ) R)) :=
    (integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  have hi' : Integrable ((Icc l U).indicator (fun r => u r))
      (volume.restrict (Icc (0 : ℝ) R)) := by
    apply hw.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact intervalKernel_cancel l U r hl hr.1 _
  have hz := (integrable_indicator_iff measurableSet_Icc).mp hi'
  have hsub : Icc l U ∩ Icc (0 : ℝ) R=Icc l U :=
    inter_eq_left.mpr (fun _ hr => ⟨hl.le.trans hr.1,hr.2.trans hUR⟩)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hlU).mpr
  simpa only [IntegrableOn,Measure.restrict_restrict measurableSet_Icc,hsub] using hz

theorem spectralRadialIntervalKernel_inner (R l U : ℝ) (hl : 0 < l)
    (hlU : l ≤ U) (hUR : U ≤ R) (u : SpectralRadialL2 R) :
    inner ℂ (spectralRadialIntervalKernel R l U hl) u=∫ r in l..U, u r := by
  rw [L2.inner_def]
  calc
    _ = ∫ r, star (spectralPrimitiveKernelValue U l r)*u r ∂radialPressureMeasure R := by
      apply integral_congr_ae
      filter_upwards [spectralRadialIntervalKernel_ae R l U hl] with r hr
      rw [hr,RCLike.inner_apply']
      rfl
    _ = ∫ r in Icc (0 : ℝ) R, (Icc l U).indicator (fun r => u r) r := by
      unfold radialPressureMeasure
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      exact intervalKernel_cancel l U r hl hr.1 _
    _ = ∫ r in Icc l U, u r := by
      have hset : Icc l U ∩ Icc (0 : ℝ) R=Icc l U :=
        inter_eq_left.mpr (fun _ hr => ⟨hl.le.trans hr.1,hr.2.trans hUR⟩)
      rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,hset]
    _ = _ := by rw [intervalIntegral.integral_of_le hlU,integral_Icc_eq_integral_Ioc]

theorem spectralRadialPointValue_integral (R l r : ℝ) (hR : 0 < R) (hl : 0 < l)
    (hlr : l ≤ r) (hrR : r ≤ R) (u : SpectralRadialEnergy R) :
    spectralRadialPointValue R hR r (hl.trans_le hlr) u-spectralRadialPointValue R hR l hl u=
      ∫ s in l..r, spectralRadialDerivative R u s := by
  rw [spectralRadialPointValue_increment R l r hR hl hlr hrR,
    spectralRadialIntervalKernel_inner R l r hl hlr hrR]

end DefocusingNLS

end OAI
