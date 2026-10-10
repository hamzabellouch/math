import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.ThresholdField

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BitReindex
open Classical MeasureTheory

noncomputable def bitReindex {ι : Type*} (e : ι ≃ ι) (b : ι → Bool) : ι → Bool :=
  fun z => b (e.symm z)

theorem bitReindex_measurable {ι : Type*} (e : ι ≃ ι) : Measurable (bitReindex e) :=
  Measurable.of_eval (fun z => measurable_pi_apply (e.symm z))

theorem thresholdField_transport {ι : Type*} (μ : Measure (ι → ℝ)) (e : ι ≃ ι) :
    (μ.map (fieldReindex e)).map thresholdField=
      (μ.map thresholdField).map (bitReindex e) := by
  rw [Measure.map_map thresholdField_measurable (fieldReindex_measurable e),
    Measure.map_map (bitReindex_measurable e) thresholdField_measurable]
  rfl

theorem ObservableClose.threshold_transport {ι : Type*} (μ : Measure (ι → ℝ))
    (e : ι ≃ ι) {ε : ℝ} (h : ObservableClose μ (μ.map (fieldReindex e)) ε) :
    ObservableClose (μ.map thresholdField) ((μ.map thresholdField).map (bitReindex e)) ε := by
  have hh := h.map thresholdField_measurable
  rw [thresholdField_transport] at hh
  exact hh

end BitReindex

end SimpleAmenable
end
end

end OAI
