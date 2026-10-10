import OAI.Geometry.RCD.Transport.WeakLengthCompression

namespace OAI

/-! # A fixed density bound passes to weak probability limits -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem weak_probability_domination (μ : Measure X) [μ.OuterRegular]
    (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hP : ∀ k, (P k : Measure X) ≤ C • μ) : (Q : Measure X) ≤ C • μ := by
  let : (C • μ).OuterRegular := Measure.OuterRegular.smul μ hC
  apply measure_le_of_open_sets
  intro U hU
  calc
    (Q : Measure X) U ≤ liminf (fun k => (P k : Measure X) U) atTop :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hU
    _ ≤ liminf (fun _ : ℕ => (C • μ) U) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall fun k => hP k U)
    _ = _ := by simp

end RegularPointCoordinates

end

end OAI
