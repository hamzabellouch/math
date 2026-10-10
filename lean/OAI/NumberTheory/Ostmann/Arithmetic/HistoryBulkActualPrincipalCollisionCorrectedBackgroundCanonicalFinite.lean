import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrectedDefsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackgroundIdentity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSpectatorDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalCollision
open HistoryBulkActualIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem correctedCollisionPrincipal_error_le
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    {ε θ : ℝ}
    (h : ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds e he hV true-
      correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds e he hV false‖≤ε ∧
      ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds e he hV true-
      correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds e he hV false‖≤θ) :
    ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds e he hV true-
      correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds hl e he hV‖≤ε ∧
    ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds e he hV true-
      correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator ds hl e he hV‖≤θ :=
  error_bounds_of_eq rfl
    (selectedBackgroundMean_false_eq_correctedBulkPrincipal
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C spectator ds hl e he hV).symm h

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
