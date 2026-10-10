import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyForward
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextBridge
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextConverse
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsDivisibility

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySignedDecode HistorySignedResidueFactorization
open HistorySignedNumerators HistorySupportReduction
open Characters FrequencyExposure BinaryExposure

def singleFiniteFrequencyUnits (K R : ℕ) {l : ℕ} (h : History l)
    (hF : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (z : ZMod (R^(K+2)) × ZMod (R^(K+2))) : Prop :=
  knownPairFrequencyUnits K R (frequencyScheduleAux R h h hF hF)
    (fixedFactorSchedule h h) h h []
    (l, initialResidueGiants K R z, initialResidueGiants K R z)
    (frequencyLeaves (R^(K+2)) h)

def singleFiniteLeafAdmissible (K R : ℕ) {l : ℕ} (h : History l)
    (hF : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (z : ZMod (R^(K+2)) × ZMod (R^(K+2))) : Prop :=
  leafAdmissible (exposureConstraint K R (frequencyScheduleAux R h h hF hF)
      (fixedFactorSchedule h h))
    (update false (exposureStep K R (frequencyScheduleAux R h h hF hF)
      (fixedFactorSchedule h h) false))
    (update true (exposureStep K R (frequencyScheduleAux R h h hF hF)
      (fixedFactorSchedule h h) true)) l
    ([], (l, initialResidueGiants K R z, initialResidueGiants K R z))
    (frequencyLeaves (R^(K+2)) h)

theorem single_integral_frequency_iff_finite (K R : ℕ) [NeZero R]
    {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hlarge : LargePrimes V h)
    (hu : FrequencyUnits R h) (hF : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (hle : l ≤ K) (Xp Xm : ℤ) :
    ((rebuild h Xp Xm).IntegralGuard ∧ FrequencyGiantCoprime (rebuild h Xp Xm)) ↔
      singleFiniteFrequencyUnits K R h hF (Xp, Xm) ∧
      singleFiniteLeafAdmissible K R h hF (Xp, Xm) ∧
      GuardedOwnDivisibility h Xp Xm := by
  let d := frequencyScheduleAux R h h hF hF
  let f := fixedFactorSchedule h h
  let g := initialResidueGiants K R ((Xp : ZMod (R^(K+2))), (Xm : ZMod (R^(K+2))))
  have hm : ScheduleMatches d f [] h h := frequencyScheduleAux_matches R h h hF hF
  have hg : SignedGiantsMatch R l g Xp Xm := initialResidueGiants_matches K R l hle Xp Xm
  have hb (hi : (rebuild h Xp Xm).IntegralGuard) :=
    frequencyGiantCoprime_pair_iff_known K d f h h hs hs hF hF hu hu hle [] hm
      g g Xp Xm Xp Xm hg hg hi hi rfl
  constructor
  · rintro ⟨hi, hf⟩
    have hgu := currentGiantUnits_of_frequencyGiantCoprime _ hf
    refine ⟨(hb hi).mp ⟨hf, hf⟩, ?_, ?_⟩
    · exact signed_pair_leafAdmissible_of_integralGuard K d f h h hs hs hlarge hlarge
        hu hu hle [] hm g g Xp Xm Xp Xm hg hg hgu hgu hi hi rfl
    · exact fun i _ => actual_divisible h Xp Xm hi i
  · rintro ⟨hf, he, ho⟩
    have hi := (pair_integralGuard_of_leafAdmissible_knownUnits K d f h h hs hs
      hlarge hlarge hu hu hle [] hm g g Xp Xm Xp Xm hg hg hf ho ho rfl he).1
    exact ⟨hi, ((hb hi).mpr hf).1⟩

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
