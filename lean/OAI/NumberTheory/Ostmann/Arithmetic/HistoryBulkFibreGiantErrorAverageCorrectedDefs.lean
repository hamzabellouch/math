import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationFibreIdentities
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCompensation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximation HistoryBulkReferencePeriodicMeanSource
open HistoryBulkFibreOriginalReference
open HistoryBulkIndependentFibreReference HistoryDiagonalRemainingRootMatching
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l)
variable (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

def correctedWitnessPrincipal
    (r : HistoryBulkActualCorrectedReferenceFamily.Witness C outside a e s t c₁ c₂)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ _ l c₁ ≠ 0)
    (hc₂ : choicesMass C.sources _ _ l c₂ ≠ 0)
    (hp : ∀q∈outside,q.Prime) : ℂ :=
  let f := HistoryBulkActualCorrectedReferenceFamily.witnessFrame
    C outside a e s t c₁ c₂ he ha hc₁ hc₂ hp r
  oldCompensation f.left f.right * (selectedBulkPrior C l).cmean (fun u =>
    let y := rightAssignment C a e u
      (reference_compatible_all C outside a e he s t c₁ c₂ r u)
    staticPairMask (f.newLeft (fibreAssignment C a u)) (f.newRight y) outside *
      f.principalCorrectedMixed (bulkPermutation e he) (fibreAssignment C a u) y)

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
