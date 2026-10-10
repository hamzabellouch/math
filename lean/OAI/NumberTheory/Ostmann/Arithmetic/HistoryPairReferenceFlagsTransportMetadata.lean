import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransportBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)

theorem occurrenceEquiv_source (i : Occurrences D.history E.history) :
    sourceOfSlot (slot D'.history E'.history (occurrenceEquiv D E D' E' i))=
      sourceOfSlot (slot D.history E.history i) := by
  obtain ⟨i,rfl⟩ := (pairedOccurrenceEquiv D E).surjective i
  rw [occurrenceEquiv_apply]
  rcases i with i | i
  · exact (internalEquiv_source seed D'.history D'.labels i).trans
      (internalEquiv_source seed D.history D.labels i).symm
  · exact (internalEquiv_source seed E'.history E'.labels i).trans
      (internalEquiv_source seed E.history E.labels i).symm

theorem representativeEquiv_level
    (hp : SamePairPattern seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels) (r : Representative D.history E.history) :
    (representativeEquiv D E D' E' hp r).val.1=r.val.1 := by
  calc
    _ = pairLevel D'.history E'.history
        (representativeMap D'.history E'.history (representativeEquiv D E D' E' hp r)) := rfl
    _ = pairLevel D'.history E'.history
        (pairedBlockEquiv D E D' E' hp (representativeMap D.history E.history r)) :=
      congrArg (pairLevel D'.history E'.history) (representativeEquiv_variable D E D' E' hp r)
    _ = pairLevel D.history E.history (representativeMap D.history E.history r) :=
      pairKeyEquiv_level seed D.history E.history D'.history E'.history
        D.labels E.labels D'.labels E'.labels hp _
    _ = _ := rfl

end Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

end

end OAI
