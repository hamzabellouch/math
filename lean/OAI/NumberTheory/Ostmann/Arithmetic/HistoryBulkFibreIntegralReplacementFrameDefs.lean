import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootPrincipals
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrameDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryBulkFibreGiantApproximation HistoryBulkGoodPatternPrincipalFrame
open HistoryBulkGiantCorrectedBounds HistoryBulkCorrectedXiBounds
open HistoryPairGiantCoordinates HistoryBulkReferenceScalarCoordinates
open HistoryPrincipalIntegralAverage HistoryGiantPriorGrid HistoryBulkIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def giantValue (r : Frame (l:=l) C outside) (corrected mixed : Bool)
    (x : Frame.Source (C:=C) (l:=l)) : ℂ :=
  if mixed then r.mixedIntegralValue x corrected else
    primeIntegral (fun _ : Bool=>C.giantCenter-1) (fun _=>C.giantCenter+1)
      (fun _=>logCellMass C.giantCenter ∅)
      (primeCutoff C.giantCenter (fun u=>
        (if corrected then
          jointCorrectedScalar C (bulkSize k L/2) r.left r.right r.left_supported
            r.right_supported (boolEquiv r.left r.right) (orderedBulkEquiv r)
        else
          jointScalar C (bulkSize k L/2) r.left r.right r.left_supported
            r.right_supported (boolEquiv r.left r.right) (orderedBulkEquiv r))
          u (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)))

def bulkMean (r : Frame (l:=l) C outside) (corrected mixed : Bool)
    (a : SelectedNonbulkSample C l)
    (σ : Equiv.Perm (Frame.Slots (depth:=k) (L:=L) (l:=l)))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  (selectedBulkPrior C l).cmean (fun u=>
    r.rootValue mixed hV σ (fibreAssignment C a u)*
      giantValue r corrected mixed (fibreAssignment C a u))

end Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrame

end

end OAI
