import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSumDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexPatterns

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalCollision
open HistoryBulkSourceDisintegration HistoryBulkUniversalPatternAggregation
open HistoryBulkPrincipalSourceReindex
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

theorem indexCollisionMean_eq_pattern :
    indexCollisionMean C origin τ outside a refs mask corrected mixed guarded =
    patternComplexSum C.sources origin τ
      (indexCollisionBlockValue C origin τ outside a refs mask corrected mixed guarded) := by
  unfold indexCollisionMean
  simp only [collisionPrincipalMean_eq_pattern]
  rw [←patternComplexSum_sum]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
