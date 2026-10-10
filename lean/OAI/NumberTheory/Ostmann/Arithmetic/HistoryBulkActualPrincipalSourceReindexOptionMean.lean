import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatchedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionFrames

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryBulkReferencePeriodicMeanSource
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (a : SelectedNonbulkSample C l)

def frameRawMean (f : Frame (l:=l) C outside) (mixed : Bool) : ℂ :=
  (selectedBulkPrior C l).cmean (fun u=>
    let x := fibreAssignment C a u
    let y := permuteAssignment C σ x
    staticPairMask (f.newLeft x) (f.newRight y) outside *
      (if mixed then f.principalMixed σ x y else f.principal σ x y))

theorem frameRawMean_congr {f g : Frame (l:=l) C outside} (mixed : Bool) (h : f=g) :
    frameRawMean C outside σ a f mixed=frameRawMean C outside σ a g mixed :=
  congrArg (fun f=>frameRawMean C outside σ a f mixed) h

 theorem quotient_frameRawMean {f g : Frame (l:=l) C outside}
    (mixed : Bool) (x c : ℂ)
    (hq : x/c=frameRawMean C outside σ a f mixed) (h : g=f) :
    x/c=frameRawMean C outside σ a g mixed :=
  hq.trans (frameRawMean_congr C outside σ a mixed h).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
