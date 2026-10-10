import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyIndependentPair

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues
open HistorySignedResidueFactorization

theorem single_integral_and_frequency_of_event_static (K R : ℕ) [NeZero R]
    {l : ℕ} (h : History l) {V : ℕ → ℕ}
    (hs : StaticSkeleton V h) (hlarge : LargePrimes V h)
    (hu : FrequencyUnits R h) (hF : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (hle : l ≤ K) (Xp Xm : ℤ) (hown : GuardedOwnDivisibility h Xp Xm)
    (hf : singleFiniteFrequencyUnits K R h hF (Xp, Xm))
    (he : singleFiniteLeafAdmissible K R h hF (Xp, Xm)) :
    (rebuild h Xp Xm).IntegralGuard ∧ FrequencyGiantCoprime (rebuild h Xp Xm) := by
  let d := frequencyScheduleAux R h h hF hF
  let f := fixedFactorSchedule h h
  let g := initialResidueGiants K R ((Xp : ZMod (R^(K+2))), (Xm : ZMod (R^(K+2))))
  have hm : ScheduleMatches d f [] h h := frequencyScheduleAux_matches R h h hF hF
  have hg : SignedGiantsMatch R l g Xp Xm := initialResidueGiants_matches K R l hle Xp Xm
  have hi := (pair_integralGuard_of_leafAdmissible_static K d f h h hs hs
    hlarge hlarge hu hu hle [] hm g g Xp Xm Xp Xm hg hg hf hown hown rfl he).1
  refine ⟨hi, ?_⟩
  exact ((frequencyGiantCoprime_pair_iff_known_static K d f h h hs hs hF hF
    hu hu hle [] hm g g Xp Xm Xp Xm hg hg hi hi rfl).mpr hf).1

theorem pair_integral_and_frequency_of_independent_event
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ}
    (hs : StaticSkeleton V h) (hs' : StaticSkeleton V h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l ≤ K)
    (Xp Xm : ℤ) (hown : GuardedOwnDivisibility h Xp Xm)
    (hown' : GuardedOwnDivisibility h' Xp Xm)
    (hf : independentFiniteFrequencyUnits K h h' (Xp, Xm))
    (he : independentFiniteLeafAdmissible K h h' (Xp, Xm)) :
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard) ∧
      FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild h' Xp Xm) := by
  let R := pairedFrequencyProduct h h'
  let : NeZero R := ⟨pairedFrequencyProduct_ne_zero_static hs hs'⟩
  have hi := single_integral_and_frequency_of_event_static K R h hs hlarge hu
    (fun _ ht => FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ ht))
    hle Xp Xm hown hf.1 he.1
  have hi' := single_integral_and_frequency_of_event_static K R h' hs' hlarge' hu'
    (fun _ ht => FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ ht))
    hle Xp Xm hown' hf.2 he.2
  exact ⟨⟨hi.1, hi'.1⟩, hi.2, hi'.2⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
