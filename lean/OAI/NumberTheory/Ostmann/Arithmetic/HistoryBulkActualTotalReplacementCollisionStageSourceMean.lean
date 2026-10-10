import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceValueDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainBulkDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plainBulkAverage_eq_sourceValue_mean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (mixed : Bool) (hV : SpectatorResidueBounds C spectator l) :
    plainBulkAverage C spectator hactual hl σ mixed hV =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
        (fun ds=>plainCollisionSourceBulkValue C spectator ds hactual hl σ mixed (hV ds)) := by
  unfold plainBulkAverage plainCollisionSourceBulkValue
  rfl

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
