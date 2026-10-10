import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace OAI

/-! # Joint measurability from monotone time and continuous space sections -/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem continuous_sections_measurable {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (g : ℝ → Y → ℝ) (hc : ∀ t, Continuous (g t))
    (ht : ∀ x, Continuous (fun t => g t x)) :
    Measurable (Function.uncurry g) := by
  have h : Measurable (fun q : Y × ℝ => g q.2 q.1) :=
    measurable_uncurry_of_continuous_of_measurable hc (fun x => (ht x).measurable)
  exact h.comp measurable_swap

theorem monotone_spatial_measurable {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (g : ℝ → Y → ℝ) (hc : ∀ t, Continuous (g t))
    (hm : ∀ x, Monotone (fun t => g t x)) :
    Measurable (Function.uncurry g) := by
  have h : Measurable (fun q : Y × ℝ => g q.2 q.1) :=
    measurable_uncurry_of_continuous_of_measurable hc (fun x => (hm x).measurable)
  exact h.comp measurable_swap

end RegularPointCoordinates

end

end OAI
