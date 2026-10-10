import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportMatched

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceSourceTransport
open Construction CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairReferenceFlagsTransport
open HistoryCompensationRepresentativePatterns CompensationEqualityPatterns HistoryPairSourceLaws
local instance sourceTransportMatchedLawsInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
attribute [local instance] Classical.propDecidable

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}
variable (D E D' E' : DecodedDraw sources seed V outside l)
  (hp : SamePairPattern seed D.history E.history D'.history E'.history
    D.labels E.labels D'.labels E'.labels)
  (p : Pattern (pairedHistoryType seed l)) (b b' : BlockDraw p ℕ)
  (hv : ∀ i, (slot D.history E.history (pairedOccurrenceEquiv D E i)).value=expand p b i)
  (hv' : ∀ i, (slot D'.history E'.history (pairedOccurrenceEquiv D' E' i)).value=expand p b' i)
  (e : RootMatching D.history E.history)
  (e' : RootMatching D'.history E'.history)

def canonicalSourceMeanMatched (giants : Bool → PrimeSource)
    (F : (PairKey D.history E.history → ℤ) → ℝ) : ℝ :=
  ∑ x : ∀i,mixedCarrier giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i,
    (∏i,mixedWeight giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i (x i))*
      F ((fun i=>mixedValue giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i (x i)) ∘
        (typedSourceEquivMatched D E p b hv e).symm)

theorem canonicalSourceMeanMatched_transport (giants : Bool → PrimeSource)
    (F : (PairKey D'.history E'.history → ℤ) → ℝ) :
    canonicalSourceMeanMatched D E p b hv e giants
      (fun x=>F (x ∘ (pairedBlockEquiv D E D' E' hp).symm))=
    canonicalSourceMeanMatched D' E' p b' hv' e' giants F := by
  unfold canonicalSourceMeanMatched
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact congrArg F (typedSourceEquivMatched_pullSample D E D' E' hp p b b' hv hv' e e' _)

theorem actual_source_mean_eq_canonical_matched (giants : Bool → PrimeSource)
    (F : (PairKey D.history E.history → ℤ) → ℝ) :
    let coord := blockSourceEquivMatched D.history E.history D.supported e (typedBlockEquiv D E p b hv)
    (∑ x : ∀i,mixedCarrier giants (actualRootSources D) sources (pairedInternalOrigin seed l) p i,
      (∏i,mixedWeight giants (actualRootSources D) sources (pairedInternalOrigin seed l) p i (x i))*
        F (fun j=>mixedValue giants (actualRootSources D) sources (pairedInternalOrigin seed l) p (coord.symm j) (x (coord.symm j))))=
      canonicalSourceMeanMatched D E p b hv e giants F := by
  dsimp only
  rw [mixed_product_sum_reindex]
  unfold canonicalSourceMeanMatched
  simp only [Function.comp_def]
  rw [mixed_product_sum_reindex]
  have hidx (j : PairKey D.history E.history) :
      (blockSourceEquivMatched D.history E.history D.supported e (typedBlockEquiv D E p b hv)).symm j=
      (Equiv.sumCongr (Equiv.refl Bool) (Equiv.sumCongr (rootPosition D) (Equiv.refl (Block p))))
        ((typedSourceEquivMatched D E p b hv e).symm j) := by
    obtain ⟨i,rfl⟩ := (typedSourceEquivMatched D E p b hv e).surjective j
    simp only [Equiv.symm_apply_apply]
    apply (blockSourceEquivMatched D.history E.history D.supported e (typedBlockEquiv D E p b hv)).injective
    rw [Equiv.apply_symm_apply]
    rcases i with t | i | q <;> rfl
  have hS : (fun j=>mixedSupport giants (actualRootSources D) sources (pairedInternalOrigin seed l) p
      ((blockSourceEquivMatched D.history E.history D.supported e (typedBlockEquiv D E p b hv)).symm j))=
      (fun j=>mixedSupport giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p
        ((typedSourceEquivMatched D E p b hv e).symm j)) := by
    funext j
    rw [hidx]
    exact (root_law_eq D p giants _).1
  rw [hS]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [hidx]
  exact congrFun (root_law_eq D p giants _).2 (x j)

end Ostmann.Arithmetic.HistoryPairReferenceSourceTransport

end

end OAI
