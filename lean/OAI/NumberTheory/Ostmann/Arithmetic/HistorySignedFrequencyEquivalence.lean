import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyForward

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySupportReduction HistorySignedDecode HistorySignedNumerators
open HistoryPairPattern HistoryPairRows

theorem pair_integralGuard_iff_event_lines
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (hsame : frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h')
    (hx : ∀i : Occurrences h h', AncestorUnits h h'
      (fun j => (pairSample h h' j:ZMod (slot h h' i).value)) i)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (Xp Xm : ℤ) (hgu : CurrentGiantUnits (rebuild h Xp Xm))
    (hgu' : CurrentGiantUnits (rebuild h' Xp Xm)) :
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard) ↔
      pairedSignedLeafAdmissible K h h' Xp Xm ∧ OwnPrimeLines h h' hs hs' Xp Xm := by
  constructor
  · rintro ⟨hi,hi'⟩
    refine ⟨?_,ownPrimeLines_of_integralGuard h h' hs hs' hroot Xp Xm hi hi'⟩
    have hR := pairedFrequencyProduct_ne_zero hs hs'
    let : NeZero (pairedFrequencyProduct h h') := ⟨hR⟩
    refine ⟨hR,?_⟩
    exact signed_pair_leafAdmissible_of_integralGuard K (frequencySchedule h h')
      (fixedFactorSchedule h h') h h' hs hs' hlarge hlarge' hu hu' hle []
      (canonical_scheduleMatches h h') _ _ Xp Xm Xp Xm
      (signedInitialGiants_matches _ _ _ _) (signedInitialGiants_matches _ _ _ _)
      hgu hgu' hi hi' hsame
  · rintro ⟨hevent,hlines⟩
    exact pair_integralGuard_of_canonical_event_lines K h h' hs hs' hroot hlarge hlarge'
      hu hu' hle hsame hx hV Xp Xm hgu hgu' hevent hlines

theorem pair_integralGuard_iff_event_lines_of_arithmeticGuards
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (hsame : frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h')
    (hx : ∀i : Occurrences h h', AncestorUnits h h'
      (fun j => (pairSample h h' j:ZMod (slot h h' i).value)) i)
    (hV : ∀i : Occurrences h h',∀j≤l,V j<(slot h h' i).value)
    (Xp Xm : ℤ)
    (ha : HistorySignedSupportReduction.ArithmeticGuards V outside (rebuild h Xp Xm))
    (ha' : HistorySignedSupportReduction.ArithmeticGuards V outside (rebuild h' Xp Xm)) :
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard) ↔
      pairedSignedLeafAdmissible K h h' Xp Xm ∧ OwnPrimeLines h h' hs hs' Xp Xm :=
  pair_integralGuard_iff_event_lines K h h' hs hs' hroot hlarge hlarge' hu hu' hle
    hsame hx hV Xp Xm (currentGiantUnits_of_arithmeticGuards V outside _ ha)
    (currentGiantUnits_of_arithmeticGuards V outside _ ha')

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
