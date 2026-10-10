import OAI.Geometry.RCD.Metric.EuclideanFiniteMeasureCompactness

namespace OAI

/-! # Closed-set mass bounds for general metric probability laws -/

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem metric_finite_measure_closed_eventual_bound {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {νs : ℕ → FiniteMeasure Y} {ν : FiniteMeasure Y}
    (hlim : Tendsto νs atTop (𝓝 ν)) {A : Set Y} (hA : IsClosed A)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop, (νs k : Measure Y).real A≤(ν : Measure Y).real A+η := by
  let B := (ν : Measure Y).real A+η
  have hB : 0≤B := add_nonneg measureReal_nonneg hη.le
  have hlt : (ν : Measure Y) A<ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (ν : Measure Y) A)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
    change (ν : Measure Y).real A<B
    dsimp [B]
    linarith
  have he := eventually_lt_of_limsup_lt
    ((FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hA).trans_lt hlt)
  filter_upwards [he] with k hk
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hk.le).trans_eq (ENNReal.toReal_ofReal hB)


theorem metric_probability_open_eventual_lower {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {P : ℕ → ProbabilityMeasure Y} {Q : ProbabilityMeasure Y}
    (hlim : Tendsto P atTop (𝓝 Q)) {A : Set Y} (hA : IsOpen A)
    {c : ℝ} (hc : c < (Q : Measure Y).real A) :
    ∀ᶠ k in atTop, c ≤ (P k : Measure Y).real A := by
  by_cases hc0 : c < 0
  · exact Eventually.of_forall (fun _ => hc0.le.trans measureReal_nonneg)
  have hc0' : 0 ≤ c := le_of_not_gt hc0
  have he : ENNReal.ofReal c < (Q : Measure Y) A := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (Q : Measure Y) A)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0').mpr hc
  have ht := eventually_lt_of_lt_liminf
    (he.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA))
  filter_upwards [ht] with k hk
  have hr := ENNReal.toReal_mono (measure_ne_top (P k : Measure Y) A) hk.le
  simpa only [Measure.real,ENNReal.toReal_ofReal hc0'] using hr

theorem metric_probability_closed_mass_lower {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {P : ℕ → ProbabilityMeasure Y} {Q : ProbabilityMeasure Y}
    (hlim : Tendsto P atTop (𝓝 Q)) {A : Set Y} (hA : IsClosed A)
    {c : ℝ} (hc : ∀ᶠ k in atTop, c ≤ (P k : Measure Y).real A) :
    c ≤ (Q : Measure Y).real A := by
  have hfinite : Tendsto (fun k => (P k).toFiniteMeasure) atTop (𝓝 Q.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto Q).comp hlim
  by_contra hnot
  have hgap : 0 < (c-(Q : Measure Y).real A)/2 := by linarith
  obtain ⟨k,hk,hk'⟩ := (hc.and (metric_finite_measure_closed_eventual_bound hfinite hA hgap)).exists
  change (P k : Measure Y).real A ≤
    (Q : Measure Y).real A+(c-(Q : Measure Y).real A)/2 at hk'
  linarith

theorem metric_probability_ball_pos_of_closed_mass {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {P : ℕ → ProbabilityMeasure Y} {Q : ProbabilityMeasure Y}
    (hlim : Tendsto P atTop (𝓝 Q)) {z : Y} {a b c : ℝ}
    (hab : a < b) (hc : 0 < c)
    (hbound : ∀ᶠ k in atTop, c ≤ (P k : Measure Y).real (closedBall z a)) :
    0 < (Q : Measure Y).real (ball z b) := by
  have hh := metric_probability_closed_mass_lower hlim isClosed_closedBall hbound
  exact hc.trans_le (hh.trans (measureReal_mono (closedBall_subset_ball hab) (measure_ne_top _ _)))

end RegularPointCoordinates

end

end OAI
