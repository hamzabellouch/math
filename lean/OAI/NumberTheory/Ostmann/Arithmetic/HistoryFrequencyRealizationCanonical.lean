import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealization

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistorySupportReduction Characters FrequencyExposure BinaryExposure

theorem pairedFrequencyProduct_ne_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h h' : History l} (hs : h.Supported V outside) (hs' : h'.Supported V outside) :
    pairedFrequencyProduct h h'≠0 := by
  apply List.prod_ne_zero
  intro hn
  obtain ⟨s,hsn,heq⟩ := List.mem_map.mp hn
  have hz : s=0 := Int.natAbs_eq_zero.mp heq
  rcases List.mem_append.mp hsn with hsn | hsn
  · exact (History.supported_frequency_bounds hs s hsn).1 hz
  · exact (History.supported_frequency_bounds hs' s hsn).1 hz

def pairedLeafAdmissible (K : ℕ) {l : ℕ} (h h' : History l) : Prop :=
  ∃ hR : pairedFrequencyProduct h h'≠0,
    let : NeZero (pairedFrequencyProduct h h') := ⟨hR⟩
    leafAdmissible (exposureConstraint K (pairedFrequencyProduct h h')
        (frequencySchedule h h') (fixedFactorSchedule h h'))
      (update false (exposureStep K (pairedFrequencyProduct h h')
        (frequencySchedule h h') (fixedFactorSchedule h h') false))
      (update true (exposureStep K (pairedFrequencyProduct h h')
        (frequencySchedule h h') (fixedFactorSchedule h h') true))
      l ([],(l,initialGiants (pairedFrequencyProduct h h') h.root,
        initialGiants (pairedFrequencyProduct h h') h'.root))
      (frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h)

theorem supported_pair_canonical_leafAdmissible
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (hs' : h'.Supported V outside)
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (hsame : frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h=
      frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h') :
    pairedLeafAdmissible K h h' := by
  have hR := pairedFrequencyProduct_ne_zero hs hs'
  let : NeZero (pairedFrequencyProduct h h') := ⟨hR⟩
  refine ⟨hR,?_⟩
  exact supported_pair_leafAdmissible K (frequencySchedule h h') (fixedFactorSchedule h h')
    h h' hs hs' hlarge hlarge' hu hu' hle [] (canonical_scheduleMatches h h')
    _ _ (initialGiants_matches _ _ _) (initialGiants_matches _ _ _) hsame

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
