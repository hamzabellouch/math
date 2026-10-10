import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquareDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementInitialGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedScalarDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage HistoryBulkActualPrincipalSourceReindex
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem correctedGuardedPrincipalAverage_eq_correctedSquareAverage
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l < k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) :
    correctedGuardedPrincipalAverage C spectator e =
      correctedSquareAverage C spectator D hl e false :=
  @same_guard_congr (PreservesRemainingBands _ e) (Classical.propDecidable _)
    (fun he => originalSourceAverage C spectator (correctedSelectedPrincipal C spectator e he))
    (fun he => (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (correctedSquareValue C spectator D hl e he false))
    (fun he => @original_corrected_principal_eq_B_sourceMean d Bs BD Bz L k l E
      C spectator e he D.admissible D.residues D.frequencies)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
