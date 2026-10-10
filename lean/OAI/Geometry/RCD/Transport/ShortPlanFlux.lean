import OAI.Geometry.RCD.Coordinates.UniformPlanPullback

namespace OAI

/-! # Uniform flux bounds for short compressed transport plans -/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
attribute [local instance] pathBorel pathBorelSpace

omit [ProperSpace X] [μ.Regular] in
theorem testPlan_flux_eq_inner (π : Measure C(Time, X))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    (G : Lp ℝ 2 μ) (t : Time) :
    (∫ γ, dist (γ 0) (γ 1) * G (γ t) ∂π) =
      inner ℝ (hD.toLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)))
        (testPlanPullback μ π hC hc t G) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hD.coeFn_toLp, compressionPullback_ae μ π _
    (measurable_path_eval t) hC (hc t) G] with γ hd hg
  change testPlanPullback μ π hC hc t G γ = G (γ t) at hg
  simp only [Real.inner_apply, hd, hg]

omit [ProperSpace X] [μ.Regular] in
theorem short_plan_flux_le (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    (G : Lp ℝ 2 μ) {d η : ℝ} (hd : 0 ≤ d) (_hη : 0 ≤ η)
    (hlen : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ d)
    (hclose : ∀ t : Time,
      ‖testPlanPullback μ π hC hc t G - testPlanPullback μ π hC hc 0 G‖ ≤ η)
    (t : Time) :
    (∫ γ, dist (γ 0) (γ 1) * G (γ t) ∂π) ≤
      (∫ γ, dist (γ 0) (γ 1) * G (γ 0) ∂π) + d * η := by
  let D := hD.toLp (fun γ : C(Time, X) => dist (γ 0) (γ 1))
  have hDn : ‖D‖ ≤ d := by
    have hh := Lp.norm_le_of_ae_bound hd (show ∀ᵐ γ ∂π, ‖D γ‖ ≤ d from by
      filter_upwards [hD.coeFn_toLp, hlen] with γ hγ hs
      simpa only [D, hγ, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hs)
    simpa [measureUnivNNReal] using hh
  rw [testPlan_flux_eq_inner μ π hC hc hD G t, testPlan_flux_eq_inner μ π hC hc hD G 0]
  suffices hh : inner ℝ D (testPlanPullback μ π hC hc t G) -
      inner ℝ D (testPlanPullback μ π hC hc 0 G) ≤ d * η by linarith
  rw [← inner_sub_right]
  exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul hDn (hclose t) (norm_nonneg _) hd))

theorem short_plan_absolute_increment_le (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    {d η : ℝ} (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hlen : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ d)
    (hclose : ∀ t : Time,
      ‖testPlanPullback μ π hC hc t G - testPlanPullback μ π hC hc 0 G‖ ≤ η) :
    (∫ γ, |u (γ 1) - u (γ 0)| ∂π) ≤
      (∫ γ, dist (γ 0) (γ 1) * G (γ 0) ∂π) + d * η := by
  have hbase := hG.testPlan_integrated_subinterval μ π hg hC hc hD (1 : Time)
  have hcont := testPlan_flux_continuous μ π hg hC hc hD G
  have hb : (∫ s : ℝ in 0..1, ∫ γ, dist (γ 0) (γ 1) * G (geodesicExtension γ s) ∂π) ≤
      ∫ _s : ℝ in 0..1, (∫ γ, dist (γ 0) (γ 1) * G (γ 0) ∂π) + d * η := by
    apply intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)
    intro s hs
    have h := short_plan_flux_le μ π hC hc hD G hd hη hlen hclose ⟨s, hs⟩
    have he (γ : C(Time, X)) : geodesicExtension γ s = γ ⟨s, hs⟩ :=
      geodesicExtension_eq γ ⟨s, hs⟩
    simpa only [he] using h
  change (∫ γ, |u (γ 1) - u (γ 0)| ∂π) ≤
    ∫ s : ℝ in 0..1, ∫ γ, dist (γ 0) (γ 1) * G (geodesicExtension γ s) ∂π at hbase
  exact hbase.trans (by simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hb)

end RegularPointCoordinates

end OAI
