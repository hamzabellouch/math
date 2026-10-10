import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundScalarDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalCollision
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def correctedCollisionPrincipal
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (guarded : Bool) : ℂ :=
  selectedBackgroundMean (l:=l) C (spectatorList spectator ds) e he List.length_ofFn
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hV guarded

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
