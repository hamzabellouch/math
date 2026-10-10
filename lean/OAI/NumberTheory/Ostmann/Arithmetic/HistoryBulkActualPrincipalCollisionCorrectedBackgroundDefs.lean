import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundScalarDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalCollision
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selectedBackgroundMean_eq (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) (guarded : Bool) :
    selectedBackgroundMean C outside e he hlen hp hV guarded=
      backgroundCollisionMean C outside
        (selectedCollisionReferences C outside e he hlen hp hV)
        (fun bg i=>selectedCollisionMask C outside e he hp bg i true) true true guarded := by
  exact Eq.trans (Eq.refl _) (Eq.refl _)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
