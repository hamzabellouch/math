import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedAggregate
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquareDefs

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

theorem correctedSquareValue_probability_eq_kernel
    (he : PreservesRemainingBands (Template.remainder (l+1)
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) :
    correctedSquareValue C spectator D hl e he true ds =
      correctedKernelValue C spectator D hl e he false ds :=
  background_probability_rootExpression_eq_kernel_sum C (spectatorList spectator ds) e he
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
    (D.admissible ds) List.length_ofFn (D.residues ds)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
