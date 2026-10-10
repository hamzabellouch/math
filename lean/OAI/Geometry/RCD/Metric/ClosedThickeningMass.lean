import OAI.Geometry.RCD.Metric.ProbabilityClosedMass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

namespace OAI

/-! # Removing a vanishing closed thickening under a finite measure -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem finite_measure_closed_of_thickenings {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    {A : Set E} (hA : IsClosed A) {c : ℝ}
    (h : ∀ κ : ℝ, 0 < κ → c ≤ μ.real (cthickening κ A)) : c ≤ μ.real A := by
  have hm := tendsto_measure_cthickening_of_isClosed
    (μ := μ) (s := A) ⟨1,zero_lt_one,measure_ne_top _ _⟩ hA
  have ht := (ENNReal.tendsto_toReal (measure_ne_top μ A)).comp
    (hm.comp tendsto_one_div_add_atTop_nhds_zero_nat)
  exact ge_of_tendsto ht (Eventually.of_forall fun j => h (1/((j:ℝ)+1)) (by positivity))

end RegularPointCoordinates

end

end OAI
