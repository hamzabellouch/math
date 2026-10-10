import OAI.Probability.DilutedSpin.PhysicalReservoirIncrement
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma rootMap_comp {X Y Z : Type} (f : X → Y) (g : Y → Z) (k : ℕ) (z : RootPath X k) :
    rootMap g k (rootMap f k z)=rootMap (g ∘ f) k z := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext rfl (ih z.2)

lemma measurePreserving_rootSplit {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (fun z : RootPath (X×Y) k => (rootMap Prod.fst k z,rootMap Prod.snd k z))
      (rootLaw k (fun _ => μ.prod ν)) ((rootLaw k (fun _ => μ)).prod (rootLaw k (fun _ => ν))) := by
  have h := ((MeasurePreserving.symm (rootArrayEquiv k) (measurePreserving_rootArray μ k)).prod
    (MeasurePreserving.symm (rootArrayEquiv k) (measurePreserving_rootArray ν k))).comp
    ((measurePreserving_arrowProdEquivProdArrow X Y (Fin k) (fun _ => μ) (fun _ => ν)).comp
      (measurePreserving_rootArray (μ.prod ν) k))
  convert h using 1
  funext z
  apply Prod.ext
  · apply (rootArrayEquiv (X := X) k).injective
    dsimp only [Function.comp_apply,Prod.map,Prod.fst]
    rw [MeasurableEquiv.apply_symm_apply]
    funext i
    simp only [rootArrayEquiv_apply,rootArray_rootMap]
    rfl
  · apply (rootArrayEquiv (X := Y) k).injective
    dsimp only [Function.comp_apply,Prod.map,Prod.snd]
    rw [MeasurableEquiv.apply_symm_apply]
    funext i
    simp only [rootArrayEquiv_apply,rootArray_rootMap]
    rfl

lemma integral_rootSplit {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (k : ℕ) (F : RootPath X k × RootPath Y k → ℝ) (hF : Measurable F)
    (hi : Integrable F ((rootLaw k (fun _ => μ)).prod (rootLaw k (fun _ => ν)))) :
    (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => μ.prod ν))=
      ∫ x,∫ y,F (x,y) ∂rootLaw k (fun _ => ν) ∂rootLaw k (fun _ => μ) := by
  have hp := measurePreserving_rootSplit μ ν k
  rw [← integral_prod F hi,←hp.map_eq,
    integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
