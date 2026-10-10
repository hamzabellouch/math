import OAI.Probability.DilutedSpin.UpperDatum

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
lemma measurePreserving_rootMap {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (k : ℕ) :
    MeasurePreserving (rootMap f k) (rootLaw k (fun _ => μ)) (rootLaw k (fun _ => ν)) := by
  induction k with
  | zero => exact MeasurePreserving.id _
  | succ k ih => exact hf.prod ih

lemma integral_rootMap {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (k : ℕ) (F : RootPath Y k → ℝ)
    (hF : Measurable F) :
    (∫ z,F (rootMap f k z) ∂rootLaw k (fun _ => μ))=∫ w,F w ∂rootLaw k (fun _ => ν) :=
by
  rw [← (measurePreserving_rootMap hf k).map_eq,
    integral_map (measurable_rootMap f hf.measurable k).aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
