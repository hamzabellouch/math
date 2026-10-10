import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesMatched

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
  (p : Pattern (pairedHistoryType seed l)) (b b' : BlockDraw p ℕ)
  (hv : ∀i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value = expand p b i)
  (hv' : ∀i, (slot D'.history E'.history (pairedOccurrenceEquiv D' E' i)).value = expand p b' i)

def typedSourceEquivMatched (e : RootMatching D.history E.history) :
    TypedSourceIndex p ≃ PairKey D.history E.history :=
  (Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.sumCongr (rootPosition D) (typedBlockEquiv D E p b hv).symm)).trans
      (sourceEquivMatched D.history E.history D.supported e)

@[simp] theorem typedSourceEquivMatched_giant (e : RootMatching D.history E.history) (t : Bool) :
    typedSourceEquivMatched D E p b hv e (.inl t) = leftMap D.history E.history (.inl t) := rfl

@[simp] theorem typedSourceEquivMatched_root (e : RootMatching D.history E.history)
    (i : Fin (Template.current seed l).length) :
    typedSourceEquivMatched D E p b hv e (.inr (.inl i)) =
      rootKey D.history E.history (rootPosition D i) := rfl

@[simp] theorem typedSourceEquivMatched_block (e : RootMatching D.history E.history) (q : Block p) :
    typedSourceEquivMatched D E p b hv e (.inr (.inr q)) =
      representativeMap D.history E.history ((typedBlockEquiv D E p b hv).symm q) := rfl

theorem typedSourceEquivMatched_transport
    (e : RootMatching D.history E.history) (e' : RootMatching D'.history E'.history)
    (i : TypedSourceIndex p) :
    pairedBlockEquiv D E D' E' hp (typedSourceEquivMatched D E p b hv e i) =
      typedSourceEquivMatched D' E' p b' hv' e' i := by
  rcases i with t | i | q
  · exact pairedBlockEquiv_giant D E D' E' hp t
  · exact pairedBlockEquiv_ordered_root D E D' E' hp i
  · rw [typedSourceEquivMatched_block,typedSourceEquivMatched_block,
      ←representativeEquiv_variable]
    congr 1
    apply (typedBlockEquiv D' E' p b' hv').injective
    rw [typedBlockEquiv_transport D E D' E' hp p b b' hv hv',
      Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem typedSourceEquivMatched_pullSample
    (e : RootMatching D.history E.history) (e' : RootMatching D'.history E'.history)
    (x : TypedSourceIndex p → ℤ) :
    (x ∘ (typedSourceEquivMatched D E p b hv e).symm) ∘ (pairedBlockEquiv D E D' E' hp).symm =
      x ∘ (typedSourceEquivMatched D' E' p b' hv' e').symm := by
  funext j
  obtain ⟨i,rfl⟩ := (typedSourceEquivMatched D' E' p b' hv' e').surjective j
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  rw [←typedSourceEquivMatched_transport D E D' E' hp p b b' hv hv' e e']
  simp only [Equiv.symm_apply_apply]

theorem typedSourceEquivMatched_eq (e e' : RootMatching D.history E.history) :
    typedSourceEquivMatched D E p b hv e = typedSourceEquivMatched D E p b hv e' := by
  ext i
  rfl

end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
