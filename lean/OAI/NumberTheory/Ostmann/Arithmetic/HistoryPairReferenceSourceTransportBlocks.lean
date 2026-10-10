import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesDecoded

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns
local instance sourceTransportBlocksInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
  (p : Pattern (pairedHistoryType seed l)) (b b' : BlockDraw p ℕ)
  (hv : ∀ i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value=expand p b i)
  (hv' : ∀ i, (slot D'.history E'.history (pairedOccurrenceEquiv D' E' i)).value=expand p b' i)

def typedBlockEquiv : Representative D.history E.history ≃ Block p :=
  representativeBlockEquiv seed D.history E.history D.labels E.labels p b hv

@[simp] theorem typedBlockEquiv_label (i : Internal seed l ⊕ Internal seed l) :
    typedBlockEquiv D E p b hv (HistoryPairRepresentatives.label D.history E.history
      (pairedOccurrenceEquiv D E i))=CompensationEqualityPatterns.label p i :=
  representativeBlockEquiv_label seed D.history E.history D.labels E.labels p b hv i

theorem typedBlockEquiv_transport (r : Representative D.history E.history) :
    typedBlockEquiv D' E' p b' hv' (representativeEquiv D E D' E' hp r)=
      typedBlockEquiv D E p b hv r := by
  obtain ⟨i,rfl⟩ := (HistoryPairRepresentatives.label_surjective D.history E.history).comp
    (pairedOccurrenceEquiv D E).surjective r
  simp only [Function.comp_apply]
  rw [representativeEquiv_label,occurrenceEquiv_apply,typedBlockEquiv_label,typedBlockEquiv_label]

abbrev TypedSourceIndex := Bool ⊕ (Fin (Template.current seed l).length ⊕ Block p)

def typedSourceEquiv (hperm : D.history.root.small.Perm E.history.root.small) :
    TypedSourceIndex p ≃ PairKey D.history E.history :=
  (Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.sumCongr (rootPosition D) (typedBlockEquiv D E p b hv).symm)).trans
      (sourceEquiv D.history E.history D.supported hperm)

@[simp] theorem typedSourceEquiv_giant (hperm : D.history.root.small.Perm E.history.root.small) (t : Bool) :
    typedSourceEquiv D E p b hv hperm (.inl t)=leftMap D.history E.history (.inl t) := rfl

@[simp] theorem typedSourceEquiv_root (hperm : D.history.root.small.Perm E.history.root.small)
    (i : Fin (Template.current seed l).length) :
    typedSourceEquiv D E p b hv hperm (.inr (.inl i))=rootKey D.history E.history (rootPosition D i) := rfl

@[simp] theorem typedSourceEquiv_block (hperm : D.history.root.small.Perm E.history.root.small) (q : Block p) :
    typedSourceEquiv D E p b hv hperm (.inr (.inr q))=
      representativeMap D.history E.history ((typedBlockEquiv D E p b hv).symm q) := rfl

theorem typedSourceEquiv_transport
    (hperm : D.history.root.small.Perm E.history.root.small)
    (hperm' : D'.history.root.small.Perm E'.history.root.small) (i : TypedSourceIndex p) :
    pairedBlockEquiv D E D' E' hp (typedSourceEquiv D E p b hv hperm i)=
      typedSourceEquiv D' E' p b' hv' hperm' i := by
  rcases i with t | i | q
  · exact pairedBlockEquiv_giant D E D' E' hp t
  · exact pairedBlockEquiv_ordered_root D E D' E' hp i
  · rw [typedSourceEquiv_block,typedSourceEquiv_block,← representativeEquiv_variable]
    congr 1
    apply (typedBlockEquiv D' E' p b' hv').injective
    rw [typedBlockEquiv_transport D E D' E' hp p b b' hv hv',Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem typedSourceEquiv_pullSample
    (hperm : D.history.root.small.Perm E.history.root.small)
    (hperm' : D'.history.root.small.Perm E'.history.root.small)
    (x : TypedSourceIndex p → ℤ) :
    (x ∘ (typedSourceEquiv D E p b hv hperm).symm) ∘ (pairedBlockEquiv D E D' E' hp).symm=
      x ∘ (typedSourceEquiv D' E' p b' hv' hperm').symm := by
  funext j
  obtain ⟨i,rfl⟩ := (typedSourceEquiv D' E' p b' hv' hperm').surjective j
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rw [← typedSourceEquiv_transport D E D' E' hp p b b' hv hv' hperm hperm']
  simp only [Equiv.symm_apply_apply]

end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
