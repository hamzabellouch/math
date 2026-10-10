import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexBackground

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualPrincipalBlockFamily HistoryBulkUniversalPatternAggregation
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkReferenceFrequencyFamily HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)

theorem background_pattern_root_congr {β : Type*} [Fintype β]
    (F G : Background C l → β →
      ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → ℂ)
    (h : ∀bg i p b,outerMass C l p (restoreOuterBackground C l p bg b)≠0 →
      Function.Injective (fun q=>(blockType p q,b q)) → F bg i p b=G bg i p b) :
    (backgroundPrior C l).cmean (fun bg=>patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>∑i:β,F bg i p b))=
    (backgroundPrior C l).cmean (fun bg=>patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>∑i:β,G bg i p b)) :=
  background_pattern_congr C _ _
    (fun bg p b ho ht=>Finset.sum_congr rfl (fun i _=>h bg i p b ho ht))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
