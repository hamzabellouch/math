import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalCollision
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selectedBackgroundMean_error_le
    (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) {ε θ : ℝ}
    (h : ‖backgroundCollisionMean C outside
        (selectedCollisionReferences C outside e he hlen hp hV)
        (fun bg i=>selectedCollisionMask C outside e he hp bg i true) true true true-
      backgroundCollisionMean C outside
        (selectedCollisionReferences C outside e he hlen hp hV)
        (fun bg i=>selectedCollisionMask C outside e he hp bg i true) true true false‖≤ε ∧
      ‖backgroundCollisionMean C outside
        (selectedCollisionReferences C outside e he hlen hp hV)
        (fun bg i=>selectedCollisionMask C outside e he hp bg i true) true true true-
      backgroundCollisionMean C outside
        (selectedCollisionReferences C outside e he hlen hp hV)
        (fun bg i=>selectedCollisionMask C outside e he hp bg i true) true true false‖≤θ) :
    ‖selectedBackgroundMean C outside e he hlen hp hV true-
      selectedBackgroundMean C outside e he hlen hp hV false‖≤ε ∧
    ‖selectedBackgroundMean C outside e he hlen hp hV true-
      selectedBackgroundMean C outside e he hlen hp hV false‖≤θ :=
  error_bounds_of_eq
    (selectedBackgroundMean_eq C outside e he hlen hp hV true)
    (selectedBackgroundMean_eq C outside e he hlen hp hV false) h

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
