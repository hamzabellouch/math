import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeletonDecode
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationUnitsPair
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistorySupportReduction HistoryFrequencyResidues
open Construction.CanonicalOccurrenceTransport HistoryOccurrenceVariables

theorem StaticSkeleton.frequency_bounds {V : ℕ→ℕ} {l : ℕ} {h : History l}
    (hs : StaticSkeleton V h) : ∀s∈h.frequencies,s≠0 ∧ ∃j≤l,s.natAbs≤V j := by
  induction h with
  | leaf a =>
    intro s hm
    have he : s=a.frequency := by simpa only [History.frequencies,List.mem_singleton] using hm
    subst s
    exact ⟨hs.root.frequency_ne_zero,0,le_rfl,hs.root.frequency_bound⟩
  | @node l a p u hp hm left right ihl ihr =>
    intro s hs'
    simp only [History.frequencies,List.mem_cons,List.mem_append] at hs'
    rcases hs' with rfl | hs' | hs'
    · exact ⟨hs.1.frequency_ne_zero,l+1,le_rfl,hs.1.frequency_bound⟩
    · obtain ⟨hne,j,hjl,hj⟩ := ihl hs.2.2.1 s hs'
      exact ⟨hne,j,by omega,hj⟩
    · obtain ⟨hne,j,hjl,hj⟩ := ihr hs.2.2.2 s hs'
      exact ⟨hne,j,by omega,hj⟩

theorem sourceMass_coprime_paired_frequency_static {sources : SourceFamily}
    {l : ℕ} {V : ℕ→ℕ} (h k : History l)
    (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (q : SmallSlot) (hq : sourceMass sources q≠0) :
    Nat.Coprime q.value (pairedFrequencyProduct h k) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro z hz
  obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hz
  have hf : s≠0 ∧ ∃j≤l,s.natAbs≤V j := by
    rcases List.mem_append.mp hs' with hs' | hs'
    · exact hs.frequency_bounds s hs'
    · exact ks.frequency_bounds s hs'
  obtain ⟨hzero,j,hjl,hbound⟩ := hf
  exact History.prime_coprime_small_frequency (sourceMass_value_prime hq) hzero
    (hbound.trans_lt (sourceMass_value_gt (hfreq j hjl) hq))

theorem decoded_frequencyUnits_static (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (h k : History l)
    (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hroot : ∀q∈a.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j)) :
    FrequencyUnits (pairedFrequencyProduct h k) (decodeHistory sources seed V l a c) :=
  decoded_frequencyUnits_of_source sources seed V _
    (sourceMass_coprime_paired_frequency_static h k hs ks hfreq) l a c ha hroot hc

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
