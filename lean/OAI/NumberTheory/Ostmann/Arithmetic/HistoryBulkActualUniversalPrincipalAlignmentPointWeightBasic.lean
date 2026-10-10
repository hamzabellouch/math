import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryBulkUniversalPatternAggregation HistoryBulkSelectedUniversalOperator
open HistoryPairKernelReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

theorem replacementReference_weight_eq_kernels
    (F : SymbolicPatternFamily C outside l p) (hp : ∀q∈outside,q.Prime)
    (i : RootPresent F.refs)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) :
    (replacementReference F hp i).weight b mixed =
      ((∏q : Block p,symbolicKernel mixed (rootLeftHistory F.refs i) (rootRightHistory F.refs i)
        (rootLeftHistory_supported F.refs i) (rootRightHistory_supported F.refs i)
        (F.representative i q) (b q).val : ℝ):ℂ) :=
  transportReference_weight _ _ _ _ _ _ _ _ _ _ _ _

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
