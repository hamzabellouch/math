import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementStageData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def correctedSquareValue (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (_hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (probability : Bool)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) : ℂ :=
  correctedSourceMean C (spectatorList spectator ds) e he
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
    (D.admissible ds) List.length_ofFn (D.residues ds) probability

def correctedSquareAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (probability : Bool) : ℂ :=
  if he : PreservesRemainingBands _ e then
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (correctedSquareValue C spectator D hl e he probability)
  else 0

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
