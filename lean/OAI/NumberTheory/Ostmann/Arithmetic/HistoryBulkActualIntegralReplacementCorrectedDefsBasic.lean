import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBackground

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualIntegralReplacement
open Construction Conclusion Filter
open HistoryBulkSourceDisintegration HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualGoodPrincipal HistoryBulkPatternIntegralReplacement
open HistoryBulkIndependentFibreReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def correctedBulkPrincipal (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) (_hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (hV : ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  backgroundValue false (fun bg p b=>correctedFamily C p (restoreOuterBackground C l p bg b)
    (spectatorList spectator ds) e he
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) true true hV

end Ostmann.Arithmetic.HistoryBulkActualIntegralReplacement

end

end OAI
