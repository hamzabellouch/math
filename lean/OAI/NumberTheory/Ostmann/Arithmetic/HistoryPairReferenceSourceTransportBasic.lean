import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesOrder
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagsTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesBasic
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportSources

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)

def rootPosition (D : DecodedDraw sources seed V outside l) :
    Fin (Template.current seed l).length ≃ Fin D.history.root.small.length :=
  matchedRootPosition (root_matches D.labels)

def rootPositionEquiv : Fin D.history.root.small.length ≃ Fin D'.history.root.small.length :=
  (rootPosition D).symm.trans (rootPosition D')

@[simp] theorem rootPositionEquiv_apply (i : Fin (Template.current seed l).length) :
    rootPositionEquiv D D' (rootPosition D i)=rootPosition D' i := by
  simp [rootPositionEquiv]

@[simp] theorem pairedBlockEquiv_giant (b : Bool) :
    pairedBlockEquiv D E D' E' hp (leftMap D.history E.history (.inl b))=
      leftMap D'.history E'.history (.inl b) :=
  pairKeyEquiv_left seed _ _ _ _ D.labels E.labels D'.labels E'.labels hp (.inl b)

@[simp] theorem pairedBlockEquiv_ordered_root (i : Fin (Template.current seed l).length) :
    pairedBlockEquiv D E D' E' hp (rootKey D.history E.history (rootPosition D i))=
      rootKey D'.history E'.history (rootPosition D' i) :=
  pairKeyEquiv_left seed _ _ _ _ D.labels E.labels D'.labels E'.labels hp (.inr (.inl i))

@[simp] theorem pairedBlockEquiv_root (i : Fin D.history.root.small.length) :
    pairedBlockEquiv D E D' E' hp (rootKey D.history E.history i)=
      rootKey D'.history E'.history (rootPositionEquiv D D' i) := by
  obtain ⟨i,rfl⟩ := (rootPosition D).surjective i
  rw [rootPositionEquiv_apply,pairedBlockEquiv_ordered_root]

theorem rootPosition_source (i : Fin (Template.current seed l).length) :
    sources ((D.history.root.small.get (rootPosition D i)).origin)=
      sources (((Template.current seed l).get i).origin) := by
  exact congrArg (fun z : SourceSlot => sources z.origin)
    (matches_get_source (root_matches D.labels) i)

theorem rootPositionEquiv_source (i : Fin D.history.root.small.length) :
    sources ((D'.history.root.small.get (rootPositionEquiv D D' i)).origin)=
      sources ((D.history.root.small.get i).origin) := by
  obtain ⟨i,rfl⟩ := (rootPosition D).surjective i
  rw [rootPositionEquiv_apply,rootPosition_source D',rootPosition_source D]

def sourceCoordinateEquiv : Coordinates D.history E.history ≃ Coordinates D'.history E'.history :=
  Equiv.sumCongr (Equiv.refl Bool)
    (Equiv.sumCongr (rootPositionEquiv D D') (representativeEquiv D E D' E' hp))

@[simp] theorem sourceMap_transport (i : Coordinates D.history E.history) :
    pairedBlockEquiv D E D' E' hp (sourceMap D.history E.history i)=
      sourceMap D'.history E'.history (sourceCoordinateEquiv D E D' E' hp i) := by
  rcases i with b | i | r
  · exact pairedBlockEquiv_giant D E D' E' hp b
  · exact pairedBlockEquiv_root D E D' E' hp i
  · exact (representativeEquiv_variable D E D' E' hp r).symm

@[simp] theorem sourceEquiv_transport
    (hperm : D.history.root.small.Perm E.history.root.small)
    (hperm' : D'.history.root.small.Perm E'.history.root.small)
    (i : Coordinates D.history E.history) :
    pairedBlockEquiv D E D' E' hp (sourceEquiv _ _ D.supported hperm i)=
      sourceEquiv _ _ D'.supported hperm' (sourceCoordinateEquiv D E D' E' hp i) :=
  sourceMap_transport D E D' E' hp i

theorem pullSample_sourceMap (x : PairKey D.history E.history → ℤ)
    (i : Coordinates D.history E.history) :
    (x ∘ (pairedBlockEquiv D E D' E' hp).symm)
      (sourceMap D'.history E'.history (sourceCoordinateEquiv D E D' E' hp i))=
      x (sourceMap D.history E.history i) := by
  rw [← sourceMap_transport]
  simp only [Function.comp_apply,Equiv.symm_apply_apply]

end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
