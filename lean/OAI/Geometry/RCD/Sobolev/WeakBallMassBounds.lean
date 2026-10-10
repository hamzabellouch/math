import OAI.Geometry.RCD.Metric.MetricProbabilityClosedMass

namespace OAI

/-! # Passing quantitative ball bounds to a weak probability limit -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem weak_closed_mass_ge_of_tendsto {P : ℕ → ProbabilityMeasure Y}
    {Q : ProbabilityMeasure Y} (hlim : Tendsto P atTop (𝓝 Q))
    {A : Set Y} (hA : IsClosed A) {a : ℕ → ℝ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 c))
    (hbound : ∀ᶠ k in atTop, a k ≤ (P k : Measure Y).real A) :
    c ≤ (Q : Measure Y).real A := by
  by_contra hnot
  have hgap : (Q : Measure Y).real A < c := lt_of_not_ge hnot
  let b := (c+(Q : Measure Y).real A)/2
  have hb : b < c := by dsimp only [b]; linarith
  have he := ha.eventually (lt_mem_nhds hb)
  have hh := metric_probability_closed_mass_lower hlim hA
    (hbound.and he |>.mono (fun k hk => hk.2.le.trans hk.1))
  change b ≤ (Q : Measure Y).real A at hh
  dsimp only [b] at hh
  linarith

theorem weak_open_mass_le_of_tendsto {P : ℕ → ProbabilityMeasure Y}
    {Q : ProbabilityMeasure Y} (hlim : Tendsto P atTop (𝓝 Q))
    {A : Set Y} (hA : IsOpen A) {a : ℕ → ℝ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 c))
    (hbound : ∀ᶠ k in atTop, (P k : Measure Y).real A ≤ a k) :
    (Q : Measure Y).real A ≤ c := by
  by_contra hnot
  have hgap : c < (Q : Measure Y).real A := lt_of_not_ge hnot
  let b := (c+(Q : Measure Y).real A)/2
  have hb : c < b := by dsimp only [b]; linarith
  have hb' : b < (Q : Measure Y).real A := by dsimp only [b]; linarith
  obtain ⟨k,⟨hk,hk'⟩,hk''⟩ :=
    ((ha.eventually (gt_mem_nhds hb)).and hbound |>.and
      (metric_probability_open_eventual_lower hlim hA hb')).exists
  exact (not_le_of_gt hk) (hk''.trans hk')

end RegularPointCoordinates

end

end OAI
