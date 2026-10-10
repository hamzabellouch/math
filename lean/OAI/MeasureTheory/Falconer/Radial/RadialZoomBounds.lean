import OAI.MeasureTheory.Falconer.Radial.RadialZoomLaw

namespace OAI

/-! # Bounded supports and Frostman bounds survive the fixed cell normalization -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_norm {a : ℝ} (ha : 0 < a) (c x : Space d) :
    ‖radialZoom a ha.ne' c x‖ = a*‖x-c‖ := by
  rw [radialZoom_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_ae_bound (μ : Measure (Space d)) {a D : ℝ} (ha : 0 < a)
    (c : Space d) (h : ∀ᵐ x ∂μ, ‖x-c‖ ≤ D) :
    ∀ᵐ x ∂Measure.map (radialZoom a ha.ne' c) μ, ‖x‖ ≤ a*D := by
  rw [ae_map_iff (radialZoom a ha.ne' c).measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [h] with x hx
  rw [radialZoom_norm ha]
  exact mul_le_mul_of_nonneg_left hx ha.le

theorem radialZoom_frostman_bound (μ : Measure (Space d))
    {a δ K s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hmass : μ univ ≤ 1) (c : Space d)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → δ ≤ r →
      Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) ≤
        ENNReal.ofReal (K*a^(-s)*r^s) := by
  intro x r hr hδ
  rw [radialZoom_ball_apply μ ha]
  have hratio : 0 < r/a := div_pos hr ha
  have hrra : r ≤ r/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hr.le ha1)
  have he : K*(r/a)^s = K*a^(-s)*r^s := by
    rw [Real.div_rpow hr.le ha.le,div_eq_mul_inv,← Real.rpow_neg ha.le]
    ring
  rw [← he]
  by_cases hr1 : r/a ≤ 1
  · exact hball _ _ (hδ.trans hrra) hr1
  · have hp : 1 ≤ (r/a)^s := Real.one_le_rpow (le_of_not_ge hr1) hs
    have hcoeff : 1 ≤ K*(r/a)^s := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoeff)

end Falconer

end OAI
