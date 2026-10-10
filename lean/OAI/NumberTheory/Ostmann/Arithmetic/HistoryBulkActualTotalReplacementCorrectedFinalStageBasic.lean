import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrectedDefsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedBulkDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualIntegralReplacement HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem corrected_final_stage_average_bound
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hl : l < k) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (hV : SpectatorResidueBounds C spectator l) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (h : ∀ he : PreservesRemainingBands _ e, ∀ ds,
      ‖correctedBulkPrincipal C spectator ds hl e he (hV ds)-
        correctedPrincipal C spectator ds hl e he (hV ds)‖ ≤ B ∧
      ‖correctedBulkPrincipal C spectator ds hl e he (hV ds)-
        correctedPrincipal C spectator ds hl e he (hV ds)‖ ≤ D) :
    ‖correctedBulkAverage C spectator hl e hV-
      correctedFinalAverage C spectator hl e hV‖ ≤ B ∧
    ‖correctedBulkAverage C spectator hl e hV-
      correctedFinalAverage C spectator hl e hV‖ ≤ D :=
  @norm_guarded_cmean_sub_le_both
    (Fin (2*(bulkSize k L/2)) → spectator.Sample) inferInstance
    (spectatorPrior spectator (2*(bulkSize k L/2)))
    (PreservesRemainingBands _ e) (Classical.propDecidable _)
    (fun he ds => correctedBulkPrincipal (l:=l) C spectator ds hl e he (hV ds))
    (fun he ds => correctedPrincipal (l:=l) C spectator ds hl e he (hV ds))
    B D hB hD (fun he ds _ => h he ds)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
