import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalCollision
open HistoryBulkSourceDisintegration HistoryBulkUniversalPatternAggregation
open scoped BigOperators Classical
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  (C : InitialSourceChoice d Bs BD Bz k L E) (origin τ : ι → ℕ)
  (outside : List ℕ) (a : SelectedNonbulkSample C l)
  (refs : κ → ∀p:Pattern τ,(Block p → CommonSample C.sources origin) →
    Option (PrincipalCollisionReference C outside a p))
  (mask : κ → SelectedBulkSample C l → ∀p:Pattern τ,
    (Block p → CommonSample C.sources origin) → ℝ)
  (corrected mixed guarded : Bool)

def indexCollisionMean : ℂ :=
  ∑i,collisionPrincipalMean C origin τ outside a (refs i) (mask i) corrected mixed guarded

def indexCollisionBlockValue (p : Pattern τ) (b : Block p → CommonSample C.sources origin) : ℂ :=
  ∑i,(refs i p b).elim 0 (fun r=>referenceKernel C origin τ outside a r b mixed *
    (selectedBulkPrior C l).cmean (fun u=>(mask i u p b:ℂ)*
      (if guarded ∧ ¬fibreSmallOutsideGuard C outside a u then 0 else
        r.value corrected mixed u)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
