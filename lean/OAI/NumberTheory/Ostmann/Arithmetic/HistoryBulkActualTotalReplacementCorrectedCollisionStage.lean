import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionStageError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionStageProperty
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalCollisionCorrected

private theorem correctedCollisionStageProof
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ scale : ℝ in atTop, correctedCollisionStageProperty d Bs BD Bz H k scale :=
  @Filter.Eventually.mono ℝ
    (correctedCollisionErrorProperty d Bs BD Bz H k)
    (correctedCollisionStageProperty d Bs BD Bz H k) atTop
    (selected_corrected_collision_error_eventually d Bs BD Bz H (k:=k) hBs hH hk)
    (fun L hL E C hG hGu hcl hcu hb hd spectator hspec l hl D e =>
      corrected_collision_stage_average_from_collision_bound
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C spectator D hl e
        (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
        (Real.exp (-H*(bulkSize k L:ℝ)))
        (Real.exp_pos _).le (Real.exp_pos _).le
        (fun he ds hds => hL E C hG hGu hcl hcu hb hd spectator hspec ds
          (HistoryBulkFibreGiantErrorAverage.spectator_mass_ne_zero
            (k:=k) (L:=L) spectator ds hds)
          l hl e he (D.residues ds)))

public theorem selected_corrected_collision_stage_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ scale : ℝ in atTop, correctedCollisionStageProperty d Bs BD Bz H k scale :=
  correctedCollisionStageProof d Bs BD Bz H hBs hH hk

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end
end

end OAI
