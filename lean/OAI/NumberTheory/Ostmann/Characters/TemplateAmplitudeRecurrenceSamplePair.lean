import OAI.NumberTheory.Ostmann.Characters.TemplateActualPhasePair
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSamplePairCore
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSourceFactorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem sampledPivotSurviving_pair (k j:ℕ) (hj:j<k) (width:Role→ℕ) {Q:ℕ}
    (χ:PrimeCharacterData (schedule k j) width Q) (hχ:∀i p,χ i p≠1)
    (a:PrimeTranslationData (schedule k j) width Q)
    (hL hR:CopiedConstituent (schedule k j) j width→PrimeUpTo Q)
    (y:OutsideConstituent (schedule k j) j width→PrimeUpTo Q)
    (P:ℕ+) (s:ℤ) (t:HistoryReconstruction.Tree (j+1))
    (hc:samplePrimeSupport (schedule k (j+1)) width
      (nextSample (schedule k j) j width hL hR y))
    (ht:∀i,HistoryFrequencyUnits (nextSample (schedule k j) j width hL hR y i).val (j+1) s t)
    (he:s*(P:ℤ)=t.1.1*((∏i,(hR i).val:ℕ):ℤ)-t.1.2*((∏i,(hL i).val:ℕ):ℤ))
    (hP:∀i,(P:ZMod (nextSample (schedule k j) j width hL hR y i).val)≠0) :
    sampledPivotSurviving k j hj width χ a hL y P t.1.1 t.2.1 *
      conj (sampledPivotSurviving k j hj width χ a hR y P t.1.2 t.2.2) =
    sampledHistoryPhase k (j+1) width
      (fun i => χ (previousConstituent (schedule k j) j width i))
      (fun i => a (previousConstituent (schedule k j) j width i))
      (nextSample (schedule k j) j width hL hR y) s t := by
  exact sampledPivotSurviving_pair_core k j hj width χ hχ a hL hR y P s t hc ht he hP

end Ostmann.Characters.Template

end

end OAI
