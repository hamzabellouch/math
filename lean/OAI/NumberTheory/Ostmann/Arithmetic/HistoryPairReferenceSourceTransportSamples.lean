import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBlocks

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns HistoryOccurrenceVariables
local instance sourceTransportSamplesInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
  (p : Pattern (pairedHistoryType seed l)) (b b' : BlockDraw p ℕ)
  (hv : ∀ i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value=expand p b i)
  (hv' : ∀ i, (slot D'.history E'.history (pairedOccurrenceEquiv D' E' i)).value=expand p b' i)
  (hperm : D.history.root.small.Perm E.history.root.small)
  (hperm' : D'.history.root.small.Perm E'.history.root.small)

def typedSample : TypedSourceIndex p → ℤ :=
  Sum.elim (fun t=>if t then (D.root.giantMinus : ℤ) else (D.root.giantPlus : ℤ))
    (Sum.elim (fun i=>(D.history.root.small.get (rootPosition D i)).value) (fun q=>b.val q))

theorem typedSourceEquiv_sample (i : TypedSourceIndex p) :
    pairSample D.history E.history (typedSourceEquiv D E p b hv hperm i)=typedSample D p b i := by
  rcases i with t | i | q
  · rw [typedSourceEquiv_giant,leftMap_sample]
    cases t <;> simp only [integerSample,DecodedDraw.history,decodeHistory_root,typedSample,Sum.elim_inl,Bool.false_eq_true,↓reduceIte]
  · rfl
  · change (prime D.history E.history ((typedBlockEquiv D E p b hv).symm q) : ℤ)=(b.val q : ℤ)
    exact congrArg (fun n : ℕ => (n : ℤ))
      ((representativeBlockEquiv_prime seed D.history E.history D.labels E.labels p b hv _).trans
        (congrArg b.val ((typedBlockEquiv D E p b hv).apply_symm_apply q)))

theorem pairSample_eq_typed :
    pairSample D.history E.history=typedSample D p b ∘ (typedSourceEquiv D E p b hv hperm).symm := by
  funext j
  obtain ⟨i,rfl⟩ := (typedSourceEquiv D E p b hv hperm).surjective j
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using
    typedSourceEquiv_sample D E p b hv hperm i

include hv hperm in

theorem actual_pullSample_eq :
    pairSample D.history E.history ∘ (pairedBlockEquiv D E D' E' hp).symm=
      typedSample D p b ∘ (typedSourceEquiv D' E' p b' hv' hperm').symm := by
  rw [pairSample_eq_typed D E p b hv hperm]
  exact typedSourceEquiv_pullSample D E D' E' hp p b b' hv hv' hperm hperm' _

theorem typedSample_root_assignment (x : SourceAssignment sources (Template.current seed l))
    (hx : D.root.small=assignedSlots sources (Template.current seed l) x)
    (i : Fin (Template.current seed l).length) :
    typedSample D p b (.inr (.inl i))=(x i).val := by
  exact congrArg (fun n : ℕ => (n : ℤ))
    (matchedRootPosition_value (root_matches D.labels) x
      (by simpa only [DecodedDraw.history,decodeHistory_root] using hx) i)

end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
