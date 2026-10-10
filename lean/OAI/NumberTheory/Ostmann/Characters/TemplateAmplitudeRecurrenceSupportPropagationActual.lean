import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSize
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem currentAtomSupport_nextSample_of_reversal (k j : ℕ) (hj:j<k)
    (width : Role → ℕ) {Q V : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (hV : ∀i p,p∈E i → V<p.val)
    (hL hR : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hLmass : (copiedPrimePrior (schedule k j) j width E hE).mass hL≠0)
    (hRmass : (copiedPrimePrior (schedule k j) j width E hE).mass hR≠0)
    (hymass : (outsidePrimePrior (schedule k j) j width E hE).mass y≠0)
    (P s v w : ℤ) (hs : s≠0) (hsV : s.natAbs≤V)
    (hl : CurrentAtomSupport k j v (sourceState k j P
      (copiedSampleState (schedule k j) j width hL) (outsideSampleState (schedule k j) j width y)))
    (hr : CurrentAtomSupport k j w (sourceState k j P
      (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y)))
    (he : v*(∏i,copiedSampleState (schedule k j) j width hR i)-
      w*(∏i,copiedSampleState (schedule k j) j width hL i)=s*P) :
    CurrentAtomSupport k (j+1) s
      (constituentSampleState (schedule k (j+1)) width
        (nextSample (schedule k j) j width hL hR y)) := by
  rw [constituentSampleState_nextSample]
  exact hl.paired_of_reversal_prime_factors hj hr hs he
    (pairedSampleState_prime_factor_gt k j width E hE hV hL hR y
      hLmass hRmass hymass s hsV)

end Ostmann.Characters.Template

end

end OAI
