import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualComparisonDecayArithmeticSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionStageProperty
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedFinalStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedJoin
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquareStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedStatementExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedCovariance

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage HistoryActualComparisonDecayArithmetic

private theorem corrected_total_of_collision_stage (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k)
    (hcollisionSource : ∀ᶠ L : ℝ in atTop, correctedCollisionStageProperty d Bs BD Bz (H+5) k L) :
    CorrectedTotalEstimate d Bs BD Bz H k := by
  rw [correctedTotalEstimate_eq]
  have hk0 : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ 1) hk
  have hreserve : 0 ≤ H+5 := add_nonneg hH (Nat.cast_nonneg 5)
  filter_upwards [selected_plain_stage_data_eventually d Bs BD Bz hk0,
    selectedDiagonalCovariance_guarded_error_eventually d Bs BD Bz (H+5) hBs hreserve hk0,
    selected_corrected_square_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    selected_corrected_kernel_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk0,
    hcollisionSource,
    selected_corrected_final_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    (bulkSize_tendsto_atTop hk0).eventually_ge_atTop 1]
    with L hdata hgiant hsquare hkernel hcollision hfinal hm
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl
  let D := hdata E C hG hcl hcu hb hd spectator hspec l hl.le
  refine ⟨D.residues,fun e => ?_⟩
  have h01 := hgiant E C hG hGu hcl hcu hb hd spectator hspec l hl e
  have hB := hsquare E C hG hGu hcl hcu hb hd spectator hspec l hl D e
  have hK := hkernel E C hG hGu hcl hcu hb hd spectator hspec l hl D e
  have h34 := hcollision E C hG hGu hcl hcu hb hd spectator hspec l hl D e
  have h45 := hfinal E C hG hGu hcl hcu hb hd spectator hspec l hl D.residues e
  exact corrected_total_of_stage_bounds C spectator D hl e H hm h01 hB hK h34 h45

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
