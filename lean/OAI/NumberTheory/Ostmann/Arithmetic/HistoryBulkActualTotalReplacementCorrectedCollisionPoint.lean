import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundScalarDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalCollisionCorrected
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

private theorem correctedKernelPointProof
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) :
    correctedKernelValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator D hl e he true ds =
      selectedBackgroundMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he List.length_ofFn
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        (D.residues ds) true :=
  (correctedKernelValue_eq (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
    (k:=k) (l:=l) (E:=E) C spectator D hl e he ds
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
    (D.residues ds) true).trans
  (HistoryBulkActualPrincipalKernelStageCorrected.sum_selectedKernelMean_eq_collisionMean
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he List.length_ofFn
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) (D.residues ds))

public theorem correctedKernelValue_eq_collisionMean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) :
    correctedKernelValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator D hl e he true ds =
      selectedBackgroundMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C (spectatorList spectator ds) e he List.length_ofFn
        (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        (D.residues ds) true :=
  correctedKernelPointProof C spectator D hl e he ds

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end
end

end OAI
