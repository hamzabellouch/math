import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairKernelReplacement HistoryCompensationRepresentativePatterns
open CompensationEqualityPatterns HistorySymbolicEncoding
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {l : ℕ}

theorem smallSourceSamples_of_roots_occurrences (sources : SourceFamily)
    (h k : History l) (hperm : h.root.small.Perm k.root.small) (y : PairKey h k → ℤ)
    (hr : ∀ i : Fin h.root.small.length,
      PositiveSourceValue (sources (h.root.small.get i).origin) (y (HistoryPairBulkCoordinates.rootKey h k i)))
    (hi : ∀ i : Occurrences h k,
      PositiveSourceValue (sources (slot h k i).origin)
        (y (representativeMap h k (HistoryPairRepresentatives.label h k i)))) :
    SmallSourceSamples sources h k y := by
  constructor
  · intro i
    rcases i with i | i
    · exact (hr i).sourceMass
    · exact (hi (.inl i)).sourceMass
  · intro i
    rcases i with i | i
    · have hm := hperm.mem_iff.mpr (List.get_mem k.root.small i)
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
      have he : HistoryPairBulkCoordinates.rootKey h k j = rightMap h k (.inr (.inl i)) := by
        apply Subtype.ext
        change Sum.inr (l+1,((h.root.small.get j).value : ℤ)) =
          (Sum.inr (l+1,((k.root.small.get i).value : ℤ)) : Bool ⊕ (ℕ × ℤ))
        rw [hj]
      have hp := hr j
      rw [hj,he] at hp
      exact hp.sourceMass
    · exact (hi (.inr i)).sourceMass

theorem pairedInternalEquiv_origin (seed : List SourceSlot) (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (i : Internal seed l ⊕ Internal seed l) :
    (slot h k (pairedInternalEquiv seed h k hh hk i)).origin = pairedInternalOrigin seed l i := by
  cases i with
  | inl i => exact congrArg SourceSlot.origin (internalEquiv_source seed h hh i)
  | inr i => exact congrArg SourceSlot.origin (internalEquiv_source seed k hk i)

theorem pattern_source_occurrence_key {V : ℕ → ℕ} {outside : List ℕ}
    (seed : List SourceSlot) (h k : History l) (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (p : Pattern (pairedHistoryType seed l)) (b : BlockDraw p ℕ)
    (hv : ∀ i, (slot h k (pairedInternalEquiv seed h k hh hk i)).value = expand p b i)
    (hs : h.Supported V outside) (hperm : h.root.small.Perm k.root.small)
    (i : Internal seed l ⊕ Internal seed l) :
    blockSourceEquiv h k hs hperm (representativeBlockEquiv seed h k hh hk p b hv)
        (.inr (.inr (CompensationEqualityPatterns.label p i))) =
      representativeMap h k (HistoryPairRepresentatives.label h k (pairedInternalEquiv seed h k hh hk i)) := by
  rw [blockSourceEquiv_block]
  rw [← representativeBlockEquiv_label seed h k hh hk p b hv i,
    Equiv.symm_apply_apply]
  rfl

theorem smallSourceSamples_of_pattern_values {V : ℕ → ℕ} {outside : List ℕ}
    (sources : SourceFamily) (seed : List SourceSlot) (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (p : Pattern (pairedHistoryType seed l)) (b : BlockDraw p ℕ)
    (hv : ∀ i, (slot h k (pairedInternalEquiv seed h k hh hk i)).value = expand p b i)
    (hs : h.Supported V outside) (hperm : h.root.small.Perm k.root.small)
    (y : PairKey h k → ℤ)
    (hr : ∀ j, PositiveSourceValue (sources (h.root.small.get j).origin)
      (y (blockSourceEquiv h k hs hperm (representativeBlockEquiv seed h k hh hk p b hv) (.inr (.inl j)))))
    (hi : ∀ i, PositiveSourceValue (sources (pairedInternalOrigin seed l i))
      (y (blockSourceEquiv h k hs hperm (representativeBlockEquiv seed h k hh hk p b hv)
        (.inr (.inr (CompensationEqualityPatterns.label p i)))))) :
    SmallSourceSamples sources h k y := by
  apply smallSourceSamples_of_roots_occurrences sources h k hperm y
  · exact hr
  · intro o
    obtain ⟨i,rfl⟩ := (pairedInternalEquiv seed h k hh hk).surjective o
    rw [pairedInternalEquiv_origin]
    have hz := hi i
    rw [pattern_source_occurrence_key] at hz
    exact hz

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
