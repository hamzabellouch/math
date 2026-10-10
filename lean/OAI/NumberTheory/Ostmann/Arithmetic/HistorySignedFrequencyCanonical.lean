import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyConverse
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsDivisibility

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySupportReduction HistorySignedDecode HistorySignedNumerators
open HistoryPairPattern HistoryPairRows MvPolynomial Characters FrequencyExposure BinaryExposure

def pairedSignedLeafAdmissible (K : ℕ) {l : ℕ} (h h' : History l) (Xp Xm : ℤ) : Prop :=
  ∃ hR : pairedFrequencyProduct h h'≠0,
    let : NeZero (pairedFrequencyProduct h h') := ⟨hR⟩
    leafAdmissible (exposureConstraint K (pairedFrequencyProduct h h')
        (frequencySchedule h h') (fixedFactorSchedule h h'))
      (update false (exposureStep K (pairedFrequencyProduct h h')
        (frequencySchedule h h') (fixedFactorSchedule h h') false))
      (update true (exposureStep K (pairedFrequencyProduct h h')
        (frequencySchedule h h') (fixedFactorSchedule h h') true))
      l ([],(l,signedInitialGiants (pairedFrequencyProduct h h') Xp Xm,
        signedInitialGiants (pairedFrequencyProduct h h') Xp Xm))
      (frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h)

def OwnPrimeLines {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h h' : History l) (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (Xp Xm : ℤ) : Prop :=
  ∀i : Occurrences h h', ((slot h h' i).value:ℤ) ∣
    eval (pairSample h h') (leftFlag h h' hs hs' i)*Xp+
      eval (pairSample h h') (rightFlag h h' hs hs' i)*Xm

theorem ownPrimeLines_of_integralGuard {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h h' : History l) (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hroot : RootGiantsAgree h h') (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (hi' : (rebuild h' Xp Xm).IntegralGuard) :
    OwnPrimeLines h h' hs hs' Xp Xm := by
  intro i
  rw [← pairActual_integer_linear_cleared h h' hs hs' hroot Xp Xm hi hi' i]
  exact dvd_mul_of_dvd_right (pairActual_divisible h h' Xp Xm hi hi' i) _

theorem pair_integralGuard_of_canonical_event_lines
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
    (hgu' : CurrentGiantUnits (rebuild h' Xp Xm))
    (hevent : pairedSignedLeafAdmissible K h h' Xp Xm)
    (hlines : OwnPrimeLines h h' hs hs' Xp Xm) :
    (rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard := by
  obtain ⟨hR,hevent⟩ := hevent
  let : NeZero (pairedFrequencyProduct h h') := ⟨hR⟩
  have hown := pair_guardedOwnDivisibility_of_lines h h' hs hs' hroot Xp Xm hx hV hlines
  exact pair_integralGuard_of_leafAdmissible K (frequencySchedule h h') (fixedFactorSchedule h h')
    h h' hs hs' hlarge hlarge' hu hu' hle [] (canonical_scheduleMatches h h')
    _ _ Xp Xm Xp Xm (signedInitialGiants_matches _ _ _ _) (signedInitialGiants_matches _ _ _ _)
    hgu hgu' hown.1 hown.2 hsame hevent

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
