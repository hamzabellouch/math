import OAI.Geometry.RCD.Metric.FiniteMeasureClosedBound

namespace OAI

/-! # Positive local mass survives weak convergence on closed balls -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem probability_open_eventual_lower {n : ℕ}
    {P : ℕ → ProbabilityMeasure (Euclidean n)} {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto P atTop (𝓝 Q)) {A : Set (Euclidean n)} (hA : IsOpen A)
    {c : ℝ} (hc : c < (Q : Measure (Euclidean n)).real A) :
    ∀ᶠ k in atTop, c ≤ (P k : Measure (Euclidean n)).real A := by
  by_cases hc0 : c < 0
  · exact Eventually.of_forall (fun _ => hc0.le.trans measureReal_nonneg)
  have hc0' : 0 ≤ c := le_of_not_gt hc0
  have he : ENNReal.ofReal c < (Q : Measure (Euclidean n)) A := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (Q : Measure (Euclidean n)) A)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0').mpr hc
  have ht := eventually_lt_of_lt_liminf
    (he.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA))
  filter_upwards [ht] with k hk
  have hr := ENNReal.toReal_mono (measure_ne_top (P k : Measure (Euclidean n)) A) hk.le
  simpa only [Measure.real,ENNReal.toReal_ofReal hc0'] using hr

theorem probability_closed_mass_lower {n : ℕ}
    {P : ℕ → ProbabilityMeasure (Euclidean n)} {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto P atTop (𝓝 Q)) {A : Set (Euclidean n)} (hA : IsClosed A)
    {c : ℝ} (hc : ∀ᶠ k in atTop, c ≤ (P k : Measure (Euclidean n)).real A) :
    c ≤ (Q : Measure (Euclidean n)).real A := by
  have hfinite : Tendsto (fun k => (P k).toFiniteMeasure) atTop (𝓝 Q.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto Q).comp hlim
  by_contra hnot
  have hgap : 0 < (c-(Q : Measure (Euclidean n)).real A)/2 := by linarith
  obtain ⟨k,hk,hk'⟩ := (hc.and (finite_measure_closed_eventual_bound hfinite hA hgap)).exists
  change (P k : Measure (Euclidean n)).real A ≤
    (Q : Measure (Euclidean n)).real A+(c-(Q : Measure (Euclidean n)).real A)/2 at hk'
  linarith

theorem probability_ball_pos_of_closed_mass {n : ℕ}
    {P : ℕ → ProbabilityMeasure (Euclidean n)} {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto P atTop (𝓝 Q)) {z : Euclidean n} {a b c : ℝ}
    (hab : a < b) (hc : 0 < c)
    (hbound : ∀ᶠ k in atTop, c ≤ (P k : Measure (Euclidean n)).real (closedBall z a)) :
    0 < (Q : Measure (Euclidean n)).real (ball z b) := by
  have hh := probability_closed_mass_lower hlim isClosed_closedBall hbound
  exact hc.trans_le (hh.trans (measureReal_mono (closedBall_subset_ball hab) (measure_ne_top _ _)))

end RegularPointCoordinates

end

end OAI
