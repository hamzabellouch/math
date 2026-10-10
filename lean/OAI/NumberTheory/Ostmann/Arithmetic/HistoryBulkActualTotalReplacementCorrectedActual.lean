import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedCollisionStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedComposition
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage HistoryActualComparisonDecayArithmetic

private theorem correctedActualProof (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    CorrectedTotalEstimate d Bs BD Bz H k := by
  rw [correctedTotalEstimate_eq]
  have hk0 : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ 1) hk
  have hreserve : 0 ≤ H+5 := add_nonneg hH (Nat.cast_nonneg 5)
  filter_upwards [selected_plain_stage_data_eventually d Bs BD Bz hk0,
    selectedDiagonalCovariance_guarded_error_eventually d Bs BD Bz (H+5) hBs hreserve hk0,
    selected_corrected_square_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    selected_corrected_kernel_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk0,
    selected_corrected_collision_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    selected_corrected_final_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    (bulkSize_tendsto_atTop hk0).eventually_ge_atTop 1]
    with scale hdata hgiant hsquare hkernel hcollision hfinal hm
  intro indices choice hG hGu hcl hcu hb hd spectator hspec level hl
  let stageData := hdata indices choice hG hcl hcu hb hd spectator hspec level hl.le
  refine ⟨stageData.residues,fun permutation => ?_⟩
  have h01 := hgiant indices choice hG hGu hcl hcu hb hd spectator hspec level hl permutation
  have hB := hsquare indices choice hG hGu hcl hcu hb hd spectator hspec level hl stageData permutation
  have hK := hkernel indices choice hG hGu hcl hcu hb hd spectator hspec level hl stageData permutation
  have h34 := hcollision indices choice hG hGu hcl hcu hb hd spectator hspec level hl stageData permutation
  have h45 := hfinal indices choice hG hGu hcl hcu hb hd spectator hspec level hl stageData.residues permutation
  exact corrected_total_of_stage_bounds choice spectator stageData hl permutation H hm h01 hB hK h34 h45

public theorem selected_corrected_total_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    CorrectedTotalEstimate d Bs BD Bz H k :=
  correctedActualProof d Bs BD Bz H hBs hH hk

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end
end

end OAI
