import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentativeVariables
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPairRows

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryPairRepresentativeVariables HistoryPairFlags

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)

def occurrenceEquiv : Occurrences D.history E.history ≃ Occurrences D'.history E'.history :=
  (pairedOccurrenceEquiv D E).symm.trans (pairedOccurrenceEquiv D' E')

@[simp] theorem occurrenceEquiv_apply (i : Internal seed l ⊕ Internal seed l) :
    occurrenceEquiv D E D' E' (pairedOccurrenceEquiv D E i)=pairedOccurrenceEquiv D' E' i := by
  simp [occurrenceEquiv]

theorem representativeMap_label_transport (i : Occurrences D.history E.history) :
    pairedBlockEquiv D E D' E' hp (representativeMap D.history E.history (label D.history E.history i))=
      representativeMap D'.history E'.history (label D'.history E'.history (occurrenceEquiv D E D' E' i)) := by
  obtain ⟨i,rfl⟩ := (pairedOccurrenceEquiv D E).surjective i
  rw [occurrenceEquiv_apply]
  rcases i with i | i
  · exact pairKeyEquiv_left seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels hp (.inr (.inr i))
  · exact pairKeyEquiv_right seed D.history E.history D'.history E'.history
      D.labels E.labels D'.labels E'.labels hp (.inr (.inr i))

include hp in
theorem label_eq_iff (i j : Occurrences D.history E.history) :
    label D.history E.history i=label D.history E.history j ↔
      label D'.history E'.history (occurrenceEquiv D E D' E' i)=
        label D'.history E'.history (occurrenceEquiv D E D' E' j) := by
  rw [← (representativeMap_injective D.history E.history).eq_iff,
    ← (pairedBlockEquiv D E D' E' hp).injective.eq_iff,
    representativeMap_label_transport,representativeMap_label_transport,
    (representativeMap_injective D'.history E'.history).eq_iff]

def representativeEquiv : Representative D.history E.history ≃ Representative D'.history E'.history :=
  sameFibersEquiv (label D.history E.history)
    (label D'.history E'.history ∘ occurrenceEquiv D E D' E')
    (label_surjective D.history E.history)
    ((label_surjective D'.history E'.history).comp (occurrenceEquiv D E D' E').surjective)
    (label_eq_iff D E D' E' hp)

@[simp] theorem representativeEquiv_label (i : Occurrences D.history E.history) :
    representativeEquiv D E D' E' hp (label D.history E.history i)=
      label D'.history E'.history (occurrenceEquiv D E D' E' i) :=
  sameFibersEquiv_apply _ _ _ _ _ i

@[simp] theorem representativeEquiv_variable (r : Representative D.history E.history) :
    representativeMap D'.history E'.history (representativeEquiv D E D' E' hp r)=
      pairedBlockEquiv D E D' E' hp (representativeMap D.history E.history r) := by
  obtain ⟨i,rfl⟩ := label_surjective D.history E.history r
  rw [representativeEquiv_label]
  exact (representativeMap_label_transport D E D' E' hp i).symm

def fiberEquiv (r : Representative D.history E.history) :
    Fiber D.history E.history r ≃ Fiber D'.history E'.history (representativeEquiv D E D' E' hp r) where
  toFun i := ⟨occurrenceEquiv D E D' E' i.val, by
    rw [← representativeEquiv_label,i.property]⟩
  invFun i := ⟨(occurrenceEquiv D E D' E').symm i.val, by
    apply (representativeEquiv D E D' E' hp).injective
    simpa only [representativeEquiv_label,Equiv.apply_symm_apply] using i.property⟩
  left_inv i := Subtype.ext ((occurrenceEquiv D E D' E').symm_apply_apply i.val)
  right_inv i := Subtype.ext ((occurrenceEquiv D E D' E').apply_symm_apply i.val)

@[simp] theorem fiberEquiv_val (r : Representative D.history E.history) (i : Fiber D.history E.history r) :
    (fiberEquiv D E D' E' hp r i).val=occurrenceEquiv D E D' E' i.val := rfl

theorem fiber_card (r : Representative D.history E.history) :
    Fintype.card (Fiber D.history E.history r)=
      Fintype.card (Fiber D'.history E'.history (representativeEquiv D E D' E' hp r)) :=
  Fintype.card_congr (fiberEquiv D E D' E' hp r)

def indexEquiv (r : Representative D.history E.history) :
    Index D.history E.history r ≃ Index D'.history E'.history (representativeEquiv D E D' E' hp r) :=
  Equiv.sumCongr ((fiberEquiv D E D' E' hp r).prodCongr (Equiv.refl Bool))
    ((fiberEquiv D E D' E' hp r).prodCongr (fiberEquiv D E D' E' hp r))

end Ostmann.Arithmetic.HistoryPairReferenceFlagsTransport

end

end OAI
