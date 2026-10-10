import OAI.MeasureTheory.Falconer.Fourier.EuclideanPolar
import OAI.MeasureTheory.Falconer.Radial.HyperplaneFiber
import OAI.MeasureTheory.Falconer.Estimates.Availability

namespace OAI

/-! Radial densities and their comparison with full-line fibers. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def euclideanRadialDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (x : Space (n+1)) (w : Sphere (n+1)) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^n) * a (x+r • (w : Space (n+1)))

theorem euclideanRadialDensity_joint_measurable {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) :
    Measurable (fun p : Space (n+1) × Sphere (n+1) => euclideanRadialDensity a p.1 p.2) := by
  have h : Measurable (fun p : (Space (n+1) × Sphere (n+1)) × ℝ =>
      ENNReal.ofReal (p.2^n) * a (p.1.1+p.2 • (p.1.2 : Space (n+1)))) := by fun_prop
  exact h.lintegral_prod_right'

theorem radialDirection_ray {n : ℕ} (x : Space (n+1)) (w : Sphere (n+1))
    {r : ℝ} (hr : 0 < r) : radialDirection x (x+r • (w : Space (n+1))) = w := by
  simp [radialDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    smul_smul, hr.ne']

theorem radialDirection_withDensity {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (ha : Measurable a) (x : Space (n+1)) :
    (volume.withDensity a).map (radialDirection x) =
      ((sphereMeasure (n+1)).withDensity (euclideanRadialDensity a x)).map
        (Subtype.val : Sphere (n+1) → Space (n+1)) := by
  have hrad : Measurable (radialDirection x) := by unfold radialDirection; fun_prop
  ext S hS
  rw [Measure.map_apply hrad hS, Measure.map_apply measurable_subtype_coe hS,
    withDensity_apply _ (hS.preimage hrad),
    withDensity_apply _ (hS.preimage measurable_subtype_coe)]
  let F := (radialDirection x ⁻¹' S).indicator a
  have hF : Measurable F := ha.indicator (hS.preimage hrad)
  rw [← lintegral_indicator (hS.preimage hrad),
    ← translated_euclidean_polar_lintegral F hF x,
    ← lintegral_indicator (hS.preimage measurable_subtype_coe)]
  apply lintegral_congr
  intro w
  by_cases hw : (w : Space (n+1)) ∈ S
  · rw [indicator_of_mem (show w ∈ Subtype.val ⁻¹' S from hw)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hy : x+r • (w : Space (n+1)) ∈ radialDirection x ⁻¹' S := by
      simpa only [mem_preimage, radialDirection_ray x w hr] using hw
    exact congrArg (ENNReal.ofReal (r^n) * ·) (indicator_of_mem hy a)
  · rw [indicator_of_notMem (show w ∉ Subtype.val ⁻¹' S from hw)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hy : x+r • (w : Space (n+1)) ∉ radialDirection x ⁻¹' S := by
      simpa only [mem_preimage, radialDirection_ray x w hr] using hw
    simp only [F, indicator_of_notMem hy, mul_zero, Pi.zero_apply]

theorem euclideanRadialDensity_le_fiber {n : ℕ} (a : Space (n+1) → ℝ≥0∞)
    (x : Space (n+1)) {D : ℝ}
    (hbound : ∀ y, a y ≠ 0 → dist y x ≤ D) (w : Sphere (n+1)) :
    euclideanRadialDensity a x w ≤ ENNReal.ofReal (D^n) *
      hyperplaneFiberDensity a w (hyperplaneProjection w x) := by
  rw [hyperplaneFiberDensity_line]
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D^n) * a (x+r • (w : Space (n+1))) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      change 0 < r at hr
      by_cases hz : a (x+r • (w : Space (n+1))) = 0
      · simp [hz]
      · apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        have h := hbound (x+r • (w : Space (n+1))) hz
        have hrD : r ≤ D := by
          simpa [dist_eq_norm, norm_smul, sphere_norm, Real.norm_eq_abs, abs_of_pos hr] using h
        exact pow_le_pow_left₀ hr.le hrD n
    _ = ENNReal.ofReal (D^n) * ∫⁻ r in Ioi (0 : ℝ), a (x+r • (w : Space (n+1))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_mono' Measure.restrict_le_self (le_refl _)) _

end Falconer

end OAI
