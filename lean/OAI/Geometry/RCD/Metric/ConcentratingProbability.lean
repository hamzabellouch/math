import OAI.Analysis.RCDHeat.GeodesicMarginalCompact

namespace OAI

/-! # Weak convergence when a probability concentrates at a point

Used for the second endpoint of radial transport. The estimate uses only
continuity at the pole and probability mass one, and retains the original
measures throughout the limit.
-/

open Set Filter Metric MeasureTheory
open scoped Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem probability_tendsto_dirac_of_radius {ν : ℕ → ProbabilityMeasure X}
    {p : X} {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (hs : ∀ k, ∀ᵐ x ∂(ν k : Measure X), dist x p ≤ r k) :
    Tendsto ν atTop (𝓝 (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure X)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun i => ∫ x, f x ∂(ν i : Measure X)) atTop
    (𝓝 (∫ x, f x ∂Measure.dirac p))
  rw [integral_dirac]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt (ε / 2) (by positivity)
  filter_upwards [hr.eventually (gt_mem_nhds hδ)] with k hk
  have hb : ∀ᵐ x ∂(ν k : Measure X), ‖f x - f p‖ ≤ ε / 2 := by
    filter_upwards [hs k] with x hx
    exact (show dist (f x) (f p) < ε / 2 from hfδ (hx.trans_lt hk)).le
  have hi := norm_integral_le_of_norm_le_const hb
  have hfi : Integrable f (ν k : Measure X) := f.integrable (μ := (ν k : Measure X))
  have hci : Integrable (fun _ : X => f p) (ν k : Measure X) := integrable_const _
  rw [integral_sub hfi hci, integral_const] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hi
  exact lt_of_le_of_lt (show dist (∫ x, f x ∂(ν k : Measure X)) (f p) ≤ ε / 2 from hi)
    (by linarith)

end RegularPointCoordinates

end OAI
