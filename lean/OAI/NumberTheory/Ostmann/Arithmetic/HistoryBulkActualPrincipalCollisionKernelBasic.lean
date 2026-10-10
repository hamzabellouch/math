import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedReference

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryPairRepresentatives HistoryPairKernelReplacement
open HistoryPairReferenceSourceTransport HistoryCompensationRepresentativePatterns
attribute [local instance] Classical.propDecidable HistoryPairReferenceFlagExpectation.matchedReferenceInternalDecidable

theorem symbolic_product_eq_blocks {b : Type} [Fintype b]
    {V : ℕ→ℕ} {outside : List ℕ} {l : ℕ} (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (e : b ≃ Representative h g) (x : b→ℕ)
    (hp : ∀q,prime h g (e q)=x q) (mixed : Bool) :
    (∏r : Representative h g,symbolicKernel mixed h g hs gs r (prime h g r)) =
    ∏q : b,symbolicKernel mixed h g hs gs (e q) (x q) := by
  calc
    _ = ∏q : b,symbolicKernel mixed h g hs gs (e q) (prime h g (e q)) := (e.prod_comp (fun r : Representative h g=>symbolicKernel mixed h g hs gs r (prime h g r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro q _
      rw [hp q]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
