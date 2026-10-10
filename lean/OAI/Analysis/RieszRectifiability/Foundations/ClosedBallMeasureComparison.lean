import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem measure_le_of_closedBall_le {d : ℕ} (ρ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ρ] [IsFiniteMeasureOnCompacts ν]
    (hball : ∀ x : Ambient d, ∀ r : ℝ, 0 < r → ρ (closedBall x r) ≤ ν (closedBall x r)) :
    ρ ≤ ν := by
  apply Measure.le_iff'.mpr
  intro s
  let v := Besicovitch.vitaliFamily ρ
  apply v.measure_le_of_frequently_le ν Measure.AbsolutelyContinuous.rfl s
  intro x _hx
  apply Filter.Eventually.frequently
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with a ha
  obtain ⟨r, hr, rfl⟩ := ha
  exact hball x r hr

end

end RieszRectifiability

end OAI
