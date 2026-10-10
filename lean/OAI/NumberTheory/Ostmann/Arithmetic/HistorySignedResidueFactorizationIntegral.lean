import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyEquivalence
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationSquares

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open HistoryPairPattern HistoryPairRows HistoryFrequencyResidues

theorem integral_squares_iff_event_lines
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
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard ∧
      PairNumeratorSquares h h' Xp Xm) ↔
    (pairedSignedLeafAdmissible K h h' Xp Xm ∧ OwnPrimeLines h h' hs hs' Xp Xm ∧
      OwnPrimeSquareLines h h' hs hs' Xp Xm) := by
  have hi := pair_integralGuard_iff_event_lines K h h' hs hs' hroot hlarge hlarge'
    hu hu' hle hsame hx hV Xp Xm hgu hgu'
  constructor
  · rintro ⟨hh,hh',hsq⟩
    obtain ⟨he,hl⟩ := hi.mp ⟨hh,hh'⟩
    exact ⟨he,hl,(pairNumeratorSquares_iff_ownPrimeSquareLines h h' hs hs'
      hroot Xp Xm hh hh' hx hV).mp hsq⟩
  · rintro ⟨he,hl,hsq⟩
    obtain ⟨hh,hh'⟩ := hi.mpr ⟨he,hl⟩
    exact ⟨hh,hh',(pairNumeratorSquares_iff_ownPrimeSquareLines h h' hs hs'
      hroot Xp Xm hh hh' hx hV).mpr hsq⟩

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
