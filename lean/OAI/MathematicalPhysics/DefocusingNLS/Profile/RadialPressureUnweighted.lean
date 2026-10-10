import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureMeasure

namespace OAI

/-! The radial weight is positive away from a null singleton, so weighted weak-star testing is full weak-star testing. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radialPressureMeasure_div_integrable (R : ℝ) (φ : ℝ → ℝ)
    (hφ : Integrable φ (volume.restrict (Icc 0 R))) :
    Integrable (fun r => φ r/r^11) (radialPressureMeasure R) := by
  unfold radialPressureMeasure
  apply (integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  apply hφ.congr
  have hn0 : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    rw [ae_iff]
    simp
  have hn : ∀ᵐ r : ℝ ∂volume.restrict (Icc (0 : ℝ) R), r ≠ 0 := ae_restrict_of_ae hn0
  filter_upwards [ae_restrict_mem measurableSet_Icc,hn] with r hr hr0
  rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
  exact (div_mul_cancel₀ (φ r) (pow_ne_zero 11 hr0)).symm

theorem radialPressureMeasure_div_integral (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ) :
    (∫ r, (f r/r^11) ∂radialPressureMeasure R)=∫ r in (0 : ℝ)..R, f r := by
  rw [radialPressureMeasure_integral R hR]
  apply intervalIntegral.integral_congr_ae
  have hn : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hn] with r hr _
  exact div_mul_cancel₀ (f r) (pow_ne_zero 11 hr)

theorem radial_weighted_weakstar_unweighted (R : ℝ) (hR : 0 ≤ R)
    (q : ℕ → ℝ → ℝ) (q₀ : ℝ → ℝ)
    (hT : ∀ φ : ℝ → ℝ, Integrable φ (radialPressureMeasure R) →
      Tendsto (fun n => ∫ r, q n r*φ r ∂radialPressureMeasure R) atTop
        (𝓝 (∫ r, q₀ r*φ r ∂radialPressureMeasure R)))
    (φ : ℝ → ℝ) (hφ : Integrable φ (volume.restrict (Icc 0 R))) :
    Tendsto (fun n => ∫ r in (0 : ℝ)..R, q n r*φ r) atTop
      (𝓝 (∫ r in (0 : ℝ)..R, q₀ r*φ r)) := by
  have h := hT (fun r => φ r/r^11) (radialPressureMeasure_div_integrable R φ hφ)
  simp_rw [← mul_div_assoc,radialPressureMeasure_div_integral R hR] at h
  exact h

end DefocusingNLS

end OAI
