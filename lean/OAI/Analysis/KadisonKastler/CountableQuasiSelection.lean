import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! Countable measurable selection of nonsingular maps is nonsingular. -/

namespace KadisonKastler

open MeasureTheory

variable {I X Y : Type*} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

theorem quasiMeasurePreserving_countable_selection {T : I → X → Y}
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν)
    {c : X → I} (hc : Measurable c) :
    Measure.QuasiMeasurePreserving (fun x => T (c x) x) μ ν := by
  have hm : Measurable (fun p : I × X => T p.1 p.2) :=
    measurable_from_prod_countable_right (fun i => (hT i).measurable)
  have hsel : Measurable (fun x => T (c x) x) := hm.comp (hc.prodMk measurable_id)
  refine ⟨hsel, ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply hsel hA]
  have havoid : ∀ᵐ y ∂ν, y ∉ A := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hzero
  have hall : ∀ᵐ x ∂μ, ∀ i, T i x ∉ A :=
    ae_all_iff.mpr (fun i => (hT i).ae havoid)
  change μ {x | T (c x) x ∈ A} = 0
  simpa only [not_not] using (ae_iff.mp (hall.mono (fun x hx => hx (c x))))

end KadisonKastler

end OAI
