import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeakTesting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! The dimension-twelve radial volume on the fixed inner interval. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

noncomputable def radialPressureMeasure (R : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 R)).withDensity (fun r : ℝ => ENNReal.ofReal ((max r 0)^11))

instance radialPressureMeasure_finite (R : ℝ) : IsFiniteMeasure (radialPressureMeasure R) := by
  have hc : Continuous (fun r : ℝ => (max r 0)^11) := by fun_prop
  have hi := hc.continuousOn.integrableOn_compact (μ := volume) (K := Icc 0 R) isCompact_Icc
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Eventually.of_forall (fun r => by positivity))).2 hi

theorem radialPressureMeasure_integral (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ) :
    (∫ r, f r ∂radialPressureMeasure R)=∫ r in (0 : ℝ)..R, f r*r^11 := by
  unfold radialPressureMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),intervalIntegral.integral_of_le hR]
  calc
    _ = ∫ r in Icc (0 : ℝ) R, f r*r^11 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      change (ENNReal.ofReal ((max r 0)^11)).toReal • f r=f r*r^11
      rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
      simp only [smul_eq_mul]
      ring
    _ = _ := integral_Icc_eq_integral_Ioc

theorem radialPressureMeasure_restrict (R l : ℝ) (hlR : l ≤ R) :
    (radialPressureMeasure R).restrict (Iic l)=radialPressureMeasure l := by
  unfold radialPressureMeasure
  rw [restrict_withDensity measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  congr 2
  ext r
  simp only [mem_inter_iff,mem_Iic,mem_Icc]
  constructor
  · rintro ⟨hrl,hr0,hrR⟩
    exact ⟨hr0,hrl⟩
  · rintro ⟨hr0,hrl⟩
    exact ⟨hrl,hr0,hrl.trans hlR⟩

theorem radialPressureMeasure_bound (R M : ℝ) (q : ℝ → ℝ)
    (hq : ∀ r ∈ Icc 0 R, ‖q r‖ ≤ M) :
    ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ M := by
  apply (ae_withDensity_iff (by fun_prop)).2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
  exact hq r hr

theorem radialPressureMeasure_step_integral (R l b : ℝ) (hl : 0 ≤ l) (hlR : l ≤ R)
    (f : ℝ → ℝ) :
    (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*f r ∂radialPressureMeasure R)=
      b*∫ r in (0 : ℝ)..l, f r*r^11 := by
  have he : (fun r => (Iic l).indicator (fun _ : ℝ => b) r*f r)=
      (Iic l).indicator (fun r => b*f r) := by
    funext r
    by_cases hr : r ∈ Iic l <;> simp [hr]
  rw [he,integral_indicator measurableSet_Iic,radialPressureMeasure_restrict R l hlR,
    radialPressureMeasure_integral l hl]
  calc
    _ = ∫ r in (0 : ℝ)..l, b*(f r*r^11) := by
      apply intervalIntegral.integral_congr
      intro r _
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end DefocusingNLS

end OAI
