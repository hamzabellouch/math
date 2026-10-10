import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementStageData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalKernelStageCorrected
attribute [local instance] Classical.propDecidable
local instance totalCorrectedKernelInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def correctedKernelValue (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (_hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (symbolic : Bool)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) : ℂ :=
  ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
    selectedKernelMean C p (spectatorList spectator ds) e he List.length_ofFn
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      (D.residues ds) i.1 i.2.1 i.2.2 symbolic

def correctedKernelAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (symbolic : Bool) : ℂ :=
  if he : PreservesRemainingBands _ e then
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (correctedKernelValue C spectator D hl e he symbolic)
  else 0

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
