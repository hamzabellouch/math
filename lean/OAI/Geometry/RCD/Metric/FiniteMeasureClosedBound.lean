import OAI.Geometry.RCD.Metric.EuclideanFiniteMeasureCompactness

namespace OAI

/-! # Real local-mass upper bounds from weak finite-measure convergence -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem finite_measure_closed_eventual_bound {n : ℕ}
    {νs : ℕ → FiniteMeasure (Euclidean n)} {ν : FiniteMeasure (Euclidean n)}
    (hlim : Tendsto νs atTop (𝓝 ν)) {A : Set (Euclidean n)} (hA : IsClosed A)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop, (νs k : Measure (Euclidean n)).real A≤(ν : Measure (Euclidean n)).real A+η := by
  let B := (ν : Measure (Euclidean n)).real A+η
  have hB : 0≤B := add_nonneg measureReal_nonneg hη.le
  have hlt : (ν : Measure (Euclidean n)) A<ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (ν : Measure (Euclidean n)) A)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
    change (ν : Measure (Euclidean n)).real A<B
    dsimp [B]
    linarith
  have he := eventually_lt_of_limsup_lt
    ((FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hA).trans_lt hlt)
  filter_upwards [he] with k hk
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hk.le).trans_eq (ENNReal.toReal_ofReal hB)

end RegularPointCoordinates

end

end OAI
