import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSourceFactorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def sampledRetainedPhase (k j : ℕ) (hj:j<k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  if copiedWithinAtomPrimeSupport (schedule k j) j width h ∧
    outsideWithinAtomPrimeSupport (schedule k j) j width y then
    sampledPivotSurviving k j hj width χ a h y P s t
  else 0

end Ostmann.Characters.Template

end

end OAI
