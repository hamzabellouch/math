import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseArithmetic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistorySignedDecode HistorySignedNumerators HistorySupportReduction
open Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryPairedFrequencyAverage

theorem StaticSkeleton.frequency_ne_zero {V : ℕ→ℕ} {l : ℕ} {h : History l}
    (hs : StaticSkeleton V h) (s : ℤ) (hm : s∈h.frequencies) : s≠0 := by
  induction h with
  | leaf a =>
    have he : s=a.frequency := by simpa only [History.frequencies,List.mem_singleton] using hm
    exact he.symm ▸ hs.root.frequency_ne_zero
  | node a p u hp hm0 left right ihl ihr =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hs.1.frequency_ne_zero
    · rcases List.mem_append.mp hm with hm | hm
      · exact ihl hs.2.2.1 hm
      · exact ihr hs.2.2.2 hm

theorem pairedFrequencyProduct_ne_zero_static {l : ℕ} {V : ℕ→ℕ}
    {h h' : History l} (hs : StaticSkeleton V h) (hs' : StaticSkeleton V h') :
    pairedFrequencyProduct h h'≠0 := by
  apply List.prod_ne_zero
  intro hn
  obtain ⟨s,hsn,heq⟩ := List.mem_map.mp hn
  have hz : s=0 := Int.natAbs_eq_zero.mp heq
  rcases List.mem_append.mp hsn with hsn | hsn
  · exact hs.frequency_ne_zero s hsn hz
  · exact hs'.frequency_ne_zero s hsn hz

theorem pair_integral_and_frequency_of_indicator
    (K : ℕ) {l : ℕ} (h h' : History l) {V : ℕ→ℕ}
    (hs : StaticSkeleton V h) (hs' : StaticSkeleton V h')
    (hlarge : LargePrimes V h) (hlarge' : LargePrimes V h')
    (hu : FrequencyUnits (pairedFrequencyProduct h h') h)
    (hu' : FrequencyUnits (pairedFrequencyProduct h h') h') (hle : l≤K)
    (Xp Xm : ℤ) (hown : GuardedOwnDivisibility h Xp Xm)
    (hown' : GuardedOwnDivisibility h' Xp Xm)
    (hsame : frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h =
      frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h')
    (he : pairedFrequencyResidueIndicator K h h' (Xp,Xm)≠0) :
    ((rebuild h Xp Xm).IntegralGuard ∧ (rebuild h' Xp Xm).IntegralGuard) ∧
      FrequencyGiantCoprime (rebuild h Xp Xm) ∧ FrequencyGiantCoprime (rebuild h' Xp Xm) := by
  classical
  let R := pairedFrequencyProduct h h'
  let : NeZero R := ⟨pairedFrequencyProduct_ne_zero_static hs hs'⟩
  have hevent : (knownPairFrequencyUnits K R (frequencySchedule h h')
      (fixedFactorSchedule h h') h h' []
      (l,initialResidueGiants K R (Xp,Xm),initialResidueGiants K R (Xp,Xm))
      (frequencyLeaves (R^(K+2)) h)) ∧
      leafAdmissible (exposureConstraint K R (frequencySchedule h h') (fixedFactorSchedule h h'))
        (update false (exposureStep K R (frequencySchedule h h') (fixedFactorSchedule h h') false))
        (update true (exposureStep K R (frequencySchedule h h') (fixedFactorSchedule h h') true))
        l ([],(l,initialResidueGiants K R (Xp,Xm),initialResidueGiants K R (Xp,Xm)))
        (frequencyLeaves (R^(K+2)) h) := by
    by_contra hbad
    apply he
    unfold pairedFrequencyResidueIndicator guardIndicator
    split_ifs with htrue
    · exact False.elim (hbad htrue)
    · rfl
  have hg := initialResidueGiants_matches K R l hle Xp Xm
  have hi := pair_integralGuard_of_leafAdmissible_static K (frequencySchedule h h')
    (fixedFactorSchedule h h') h h' hs hs' hlarge hlarge' hu hu' hle []
    (canonical_scheduleMatches h h') _ _ Xp Xm Xp Xm hg hg hevent.1 hown hown' hsame hevent.2
  refine ⟨hi,?_⟩
  exact (frequencyGiantCoprime_pair_iff_known_static K (frequencySchedule h h')
    (fixedFactorSchedule h h') h h' hs hs'
    (fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs))
    (fun _ hs=>FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs))
    hu hu' hle [] (canonical_scheduleMatches h h') _ _ Xp Xm Xp Xm hg hg hi.1 hi.2 hsame).mpr hevent.1

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
