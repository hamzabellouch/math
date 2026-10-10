import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrectedDefsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSpectatorDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionPoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalCollisionCorrected
open HistoryBulkActualIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

private theorem transfer {x y z : ℂ} {a b : ℝ}
    (hxy : x=y) (h : ‖y-z‖≤a ∧ ‖y-z‖≤b) : ‖x-z‖≤a ∧ ‖x-z‖≤b :=
  hxy.symm ▸ h

public theorem correctedKernelValue_error_le
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) (r₁ r₂ : ℝ)
    (h : ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds e he (D.residues ds) true-
        correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds)‖≤r₁ ∧
      ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds e he (D.residues ds) true-
        correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds)‖≤r₂) :
    ‖correctedKernelValue C spectator D hl e he true ds -
        correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
          (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds)‖≤r₁ ∧
      ‖correctedKernelValue C spectator D hl e he true ds -
        correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
          (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds)‖≤r₂ :=
  transfer (z := correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds))
    (a:=r₁) (b:=r₂)
    (correctedKernelValue_eq_collisionMean
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C spectator D hl e he ds) h

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end
end

end OAI
