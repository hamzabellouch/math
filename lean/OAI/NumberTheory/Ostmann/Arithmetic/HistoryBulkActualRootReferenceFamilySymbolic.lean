import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsDecoded

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryCompensationRepresentativePatterns HistoryPairRepresentatives
open HistoryBulkUniversalPatternAggregation HistoryBulkSelectedUniversalOperator
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hvalid : ∀ j, (expand p b j).val ∈ (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)
variable (J : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → SelectedBulkSample C l → ℤ → ℤ → ℂ)
variable {α : Type} [Fintype α] (w : α → ℝ) (P Q : α → ℤ)
variable {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l ≤ k) (ha : 0 < (selectedNonbulkPrior C l).mass a)
  (hc : ∀ i, choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l (leftChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) i) ≠ 0)
  (he : ∀ i, choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l (rightChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) i) ≠ 0)
  (houtside : ∀ q∈outside, ∃ v : spectator.Sample, (v:ℕ)=q)
  (hw : ∀ r, 0 ≤ w r) (hpos : ∀ r, w r ≠ 0 → 0 < P r ∧ 0 < Q r)

def representativeEquiv
    (i : RootPresent (referenceFamily C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J w P Q
      hactual hl ha hc he houtside hw hpos)) :
    Block p ≃ Representative
      (rootLeftHistory (referenceFamily C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J w P Q
        hactual hl ha hc he houtside hw hpos) i)
      (rootRightHistory (referenceFamily C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J w P Q
        hactual hl ha hc he houtside hw hpos) i) :=
  (decodedRepresentativeBlockEquiv C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l p b hvalid
    (rootSelected _ i).left (rootSelected _ i).right i.val.2.1 i.val.2.2
    (rootSelected _ i).left_matches (rootSelected _ i).right_matches).symm

def symbolicPatternFamily
    (hcell : ∀ v, w v ≠ 0 → 0 < P v ∧ 0 < Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)| ≤ 1 ∧
      |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)| ≤ 1) :
    SymbolicPatternFamily C outside l p where
  permutation := σ
  left := (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j))
  right := (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j))
  refs := referenceFamily C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J w P Q hactual hl ha hc he houtside hw hpos
  data := actualData C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J w P Q hactual hl ha hc he houtside hw hpos hcell
  representative := representativeEquiv C outside σ a p b hvalid J w P Q
    hactual hl ha hc he houtside hw hpos
  mask := fun _ => 1
  mask_mem := fun _ => ⟨zero_le_one,le_rfl⟩

end Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily

end

end OAI
