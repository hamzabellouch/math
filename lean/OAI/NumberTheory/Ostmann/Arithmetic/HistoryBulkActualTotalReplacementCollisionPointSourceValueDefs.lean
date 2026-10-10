import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkActualIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainCollisionSourceBulkValue (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l ≤ k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  plainBulkPrincipal C spectator ds hactual hl σ mixed hV

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
