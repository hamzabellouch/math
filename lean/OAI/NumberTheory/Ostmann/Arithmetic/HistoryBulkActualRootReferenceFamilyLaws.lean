import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilySymbolic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryCompensationRepresentativePatterns HistoryPairRepresentatives
open HistoryBulkUniversalPatternAggregation HistoryBulkSelectedUniversalOperator
open HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference HistoryBulkFibreOriginalReference
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hvalid : ∀ j, (expand p b j).val ∈ (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)
variable (J : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → SelectedBulkSample C l → ℤ → ℤ → ℂ)
variable {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l ≤ k) (ha : 0 < (selectedNonbulkPrior C l).mass a)
  (hc : ∀ i, choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l (leftChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) i) ≠ 0)
  (he : ∀ i, choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l (rightChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) i) ≠ 0)
  (houtside : ∀ q∈outside, ∃ v : spectator.Sample, (v:ℕ)=q)

def primePatternFamily : SymbolicPatternFamily C outside l p :=
  symbolicPatternFamily C outside σ a p b hvalid J
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
    hactual hl ha hc he houtside (primeWeight_nonneg C.giant)
    (fun r _ => primeDraw_positive C.giant r)
    (fun r hr => prime_draw_cells C r
      (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))

theorem primePatternFamily_none_iff (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    (primePatternFamily C outside σ a p b hvalid J hactual hl ha hc he houtside).refs i = none ↔
      weightedPrimeFibreMean C outside σ a i.1.val i.1.val
        (leftChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) i) (rightChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) i) (J i) = 0 := by
  simpa only [primePatternFamily,symbolicPatternFamily,weightedPrimeFibreMean_eq_weighted,wholeMean] using
    referenceFamily_none_iff C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl ha hc he houtside (primeWeight_nonneg C.giant)
      (fun r _ => primeDraw_positive C.giant r) i

def mixedPatternFamily : SymbolicPatternFamily C outside l p :=
  symbolicPatternFamily C outside σ a p b hvalid J
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
    hactual hl ha hc he houtside (mixedWeight_nonneg C.giantCenter C.giant)
    (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
    (fun r hr => mixed_draw_cells C r
      (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))

theorem mixedPatternFamily_none_iff (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    (mixedPatternFamily C outside σ a p b hvalid J hactual hl ha hc he houtside).refs i = none ↔
      weightedMixedFibreMean C outside σ a i.1.val i.1.val
        (leftChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) i) (rightChoices C (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) i) (J i) = 0 := by
  simpa only [mixedPatternFamily,symbolicPatternFamily,weightedMixedFibreMean_eq_weighted,wholeMean] using
    referenceFamily_none_iff C outside σ a (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inl j)) (fun j => blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hvalid (Sum.inr j)) J
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
      hactual hl ha hc he houtside (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _ => mixedDraw_positive C.giantCenter C.giant r) i

end Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily

end

end OAI
