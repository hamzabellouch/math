import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyForward
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextBridge
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextConverse

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySupportReduction HistorySignedDecode HistorySignedNumerators
open HistorySignedResidueFactorization HistoryPairPattern HistoryPairRows
open Characters FrequencyExposure BinaryExposure

def pairedFiniteLeafAdmissible (K : ℕ) {l : ℕ} (h h' : History l)
    (z : ZMod ((pairedFrequencyProduct h h')^(K+2)) ×
      ZMod ((pairedFrequencyProduct h h')^(K+2))) : Prop :=
  leafAdmissible (exposureConstraint K (pairedFrequencyProduct h h')
      (frequencySchedule h h') (fixedFactorSchedule h h'))
    (update false (exposureStep K (pairedFrequencyProduct h h')
      (frequencySchedule h h') (fixedFactorSchedule h h') false))
    (update true (exposureStep K (pairedFrequencyProduct h h')
      (frequencySchedule h h') (fixedFactorSchedule h h') true))
    l ([],(l,initialResidueGiants K (pairedFrequencyProduct h h') z,
      initialResidueGiants K (pairedFrequencyProduct h h') z))
    (frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h)

theorem integral_frequency_iff_finite_event_lines
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
    (Xp Xm : ℤ) :
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard ∧
      FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild h' Xp Xm)) ↔
    (pairedFiniteFrequencyUnits K h h' (Xp,Xm) ∧ pairedFiniteLeafAdmissible K h h' (Xp,Xm) ∧
      OwnPrimeLines h h' hs hs' Xp Xm) := by
  let R := pairedFrequencyProduct h h'
  have hR : R≠0 := pairedFrequencyProduct_ne_zero hs hs'
  let : NeZero R := ⟨hR⟩
  let g := initialResidueGiants K R (Xp,Xm)
  have hg : SignedGiantsMatch R l g Xp Xm := initialResidueGiants_matches K R l hle Xp Xm
  have hF : ∀s∈h.frequencies,s.natAbs∣R :=
    fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs)
  have hF' : ∀s∈h'.frequencies,s.natAbs∣R :=
    fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs)
  constructor
  · rintro ⟨hi,hi',hf,hf'⟩
    have hknown := (frequencyGiantCoprime_pair_iff_known K (frequencySchedule h h')
      (fixedFactorSchedule h h') h h' hs hs' hF hF' hu hu' hle []
      (canonical_scheduleMatches h h') g g Xp Xm Xp Xm hg hg hi hi' hsame).mp ⟨hf,hf'⟩
    refine ⟨hknown,?_,ownPrimeLines_of_integralGuard h h' hs hs' hroot Xp Xm hi hi'⟩
    exact signed_pair_leafAdmissible_of_integralGuard K (frequencySchedule h h')
      (fixedFactorSchedule h h') h h' hs hs' hlarge hlarge' hu hu' hle []
      (canonical_scheduleMatches h h') g g Xp Xm Xp Xm hg hg
      (currentGiantUnits_of_frequencyGiantCoprime _ hf)
      (currentGiantUnits_of_frequencyGiantCoprime _ hf') hi hi' hsame
  · rintro ⟨hknown,hevent,hlines⟩
    have hown := pair_guardedOwnDivisibility_of_lines h h' hs hs' hroot Xp Xm hx hV hlines
    have hi := pair_integralGuard_of_leafAdmissible_knownUnits K (frequencySchedule h h')
      (fixedFactorSchedule h h') h h' hs hs' hlarge hlarge' hu hu' hle []
      (canonical_scheduleMatches h h') g g Xp Xm Xp Xm hg hg hknown hown.1 hown.2 hsame hevent
    have hf := (frequencyGiantCoprime_pair_iff_known K (frequencySchedule h h')
      (fixedFactorSchedule h h') h h' hs hs' hF hF' hu hu' hle []
      (canonical_scheduleMatches h h') g g Xp Xm Xp Xm hg hg hi.1 hi.2 hsame).mpr hknown
    exact ⟨hi.1,hi.2,hf⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
