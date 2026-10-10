import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureMeasure
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureLocalTesting
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! The bounded inner pressures converge against all integrable radial tests. -/

open scoped ContDiff
open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_pressure_weakstar_of_C1_testing (R l b : ℝ) (hl : 0 ≤ l) (hlR : l ≤ R)
    (hb : |b| ≤ 1) (q : ℕ → ℝ → ℝ) (hq : ∀ n, Continuous (q n))
    (hqb : ∀ n r, r ∈ Icc 0 R → ‖q n r‖ ≤ 1)
    (hTest : ∀ φ φ₁ : ℝ → ℝ, Continuous φ → Continuous φ₁ →
      (∀ r ∈ Ioo 0 R, HasDerivAt φ (φ₁ r) r) →
      Tendsto (fun n => ∫ r in (0 : ℝ)..R, q n r*φ r*r^11) atTop
        (𝓝 (b*∫ r in (0 : ℝ)..l, φ r*r^11)))
    (φ : ℝ → ℝ) (hφ : Integrable φ (radialPressureMeasure R)) :
    Tendsto (fun n => ∫ r, q n r*φ r ∂radialPressureMeasure R) atTop
      (𝓝 (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*φ r ∂radialPressureMeasure R)) := by
  apply radial_bounded_testing_L1 (radialPressureMeasure R) q
    ((Iic l).indicator (fun _ : ℝ => b)) 1 (by norm_num)
    (fun n => (hq n).aestronglyMeasurable)
    (measurable_const.indicator measurableSet_Iic).aestronglyMeasurable
    (fun n => radialPressureMeasure_bound R 1 (q n) (hqb n)) _ _ φ hφ
  · apply radialPressureMeasure_bound
    intro r _
    by_cases hr : r ∈ Iic l
    · simpa only [indicator_of_mem hr,Real.norm_eq_abs] using hb
    · simp only [indicator_of_notMem hr,norm_zero,zero_le_one]
  · intro g _ hg
    have ht := hTest g (deriv g) hg.continuous (hg.continuous_deriv (by simp))
      (fun r _ => (hg.differentiable (by simp) r).hasDerivAt)
    rw [radialPressureMeasure_step_integral R l b hl hlR]
    simpa only [radialPressureMeasure_integral R (hl.trans hlR)] using ht

end DefocusingNLS

end OAI
