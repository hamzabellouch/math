import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCollarDecay

namespace OAI

/-! The radial volume of a collar is bounded by its width times the outer density. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralRadialMeasure_integral_Icc (R l U : ℝ) (hl : 0 ≤ l)
    (hlU : l ≤ U) (hUR : U ≤ R) (f : ℝ → ℝ) :
    (∫ r in Icc l U, f r ∂radialPressureMeasure R)=∫ r in l..U, f r*r^11 := by
  rw [← integral_indicator measurableSet_Icc,
    radialPressureMeasure_integral R (hl.trans (hlU.trans hUR)),
    intervalIntegral.integral_of_le (hl.trans (hlU.trans hUR))]
  rw [← integral_Icc_eq_integral_Ioc]
  have he : (fun r => (Icc l U).indicator f r*r^11)=
      (Icc l U).indicator (fun r => f r*r^11) := by
    funext r
    by_cases hr : r ∈ Icc l U <;> simp [hr]
  rw [he,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc l U ∩ Icc (0 : ℝ) R=Icc l U :=
    inter_eq_left.mpr (fun _ hr => ⟨hl.trans hr.1,hr.2.trans hUR⟩)
  rw [hset,intervalIntegral.integral_of_le hlU,integral_Icc_eq_integral_Ioc]

theorem spectralRadialMeasure_collar_bound (R l U : ℝ) (hl : 0 ≤ l)
    (hlU : l ≤ U) (hUR : U ≤ R) :
    (∫ _ in Icc l U, (1 : ℝ) ∂radialPressureMeasure R) ≤ (U-l)*R^11 := by
  rw [spectralRadialMeasure_integral_Icc R l U hl hlU hUR]
  simp only [one_mul]
  have hi : IntervalIntegrable (fun r : ℝ => r^11) volume l U :=
    (continuous_id.pow 11).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hlU hi intervalIntegrable_const
    (fun r (hr : r ∈ Icc l U) => pow_le_pow_left₀ (hl.trans hr.1) (hr.2.trans hUR) 11)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using h

end DefocusingNLS

end OAI
