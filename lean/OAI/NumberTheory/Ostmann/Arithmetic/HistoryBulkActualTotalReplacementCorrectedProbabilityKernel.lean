import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedProbabilityKernelPoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquareDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementInitialGuard

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalSourceReindexFamilyCorrected
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (D : PlainStageData C spectator l) (hl : l<k)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))

theorem correctedSquareAverage_probability_eq_kernel :
    correctedSquareAverage C spectator D hl e true =
      correctedKernelAverage C spectator D hl e false :=
  @same_guard_congr
    (PreservesRemainingBands (Template.remainder (l+1)
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
    (Classical.propDecidable _)
    (fun he => (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (correctedSquareValue C spectator D hl e he true))
    (fun he => (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (correctedKernelValue C spectator D hl e he false))
    (fun he => congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
      (funext (fun ds => correctedSquareValue_probability_eq_kernel C spectator D hl e he ds)))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
