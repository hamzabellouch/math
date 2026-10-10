import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrectedDefsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSpectatorDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedBulkDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionBulkAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionKernelAverage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionPointError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalCollisionCorrected
open HistoryBulkActualIntegralReplacement
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

private theorem transport_two_errors {x x' y y' : ℂ} {a b : ℝ}
    (hx : x=x') (hy : y=y') (h : ‖x'-y'‖≤a ∧ ‖x'-y'‖≤b) :
    ‖x-y‖≤a ∧ ‖x-y‖≤b := hx.symm ▸ hy.symm ▸ h

public theorem corrected_collision_stage_average_from_collision_bound
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (r₁ r₂ : ℝ) (hr₁ : 0≤r₁) (hr₂ : 0≤r₂)
    (h : ∀he : PreservesRemainingBands (Template.remainder (l+1)
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e,∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      (spectatorPrior spectator (2*(bulkSize k L/2))).mass ds≠0 →
      ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds e he (D.residues ds) true-
        correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds)‖≤r₁ ∧
      ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds e he (D.residues ds) true-
        correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
        (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds)‖≤r₂) :
    ‖correctedKernelAverage (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator D hl e true-
      correctedBulkAverage (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator hl e D.residues‖≤r₁ ∧
    ‖correctedKernelAverage (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator D hl e true-
      correctedBulkAverage (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator hl e D.residues‖≤r₂ :=
  transport_two_errors
    (correctedKernelAverage_eq_guarded (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator D hl e true)
    (correctedBulkAverage_eq_guarded (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator hl e D.residues)
    (norm_guarded_cmean_sub_le_both
    (α := Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (spectatorPrior spectator (2*(bulkSize k L/2))) (PreservesRemainingBands (Template.remainder (l+1)
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
    (fun he => correctedKernelValue (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator D hl e he true)
    (fun he ds => correctedBulkPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L)
      (k:=k) (l:=l) (E:=E) C spectator ds hl e he (D.residues ds))
    r₁ r₂ hr₁ hr₂
    (fun he ds hds => correctedKernelValue_error_le
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C spectator D hl e he ds r₁ r₂ (h he ds hds)))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end
end

end OAI
