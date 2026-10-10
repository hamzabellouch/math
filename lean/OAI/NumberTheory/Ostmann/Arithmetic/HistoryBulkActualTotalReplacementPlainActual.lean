import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualComparisonDecayArithmeticSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainFinalStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainGiant
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainJoin
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementSquareStage

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryActualComparisonDecayArithmetic

theorem selected_plain_total_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    PlainTotalEstimate d Bs BD Bz H k := by
  have hk0 : 0 < k := lt_of_lt_of_le (Nat.zero_lt_succ 1) hk
  have hreserve : 0 ≤ H+5 := add_nonneg hH (Nat.cast_nonneg 5)
  filter_upwards [selected_plain_stage_data_eventually d Bs BD Bz hk0,
    selected_plain_giant_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    selected_plain_square_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    selected_plain_kernel_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk0,
    selected_plain_collision_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    selected_plain_final_stage_eventually d Bs BD Bz (H+5) hBs hreserve hk,
    (bulkSize_tendsto_atTop hk0).eventually_ge_atTop 1]
    with L hdata hgiant hsquare hkernel hcollision hfinal hm
  intro E C hG hGu hcl hcu hb hd spectator hspec
  obtain ⟨hactual,hgiant⟩ := hgiant E C hG hGu hcl hcu hb hd spectator hspec
  refine ⟨hactual,fun l hl => ?_⟩
  let D := hdata E C hG hcl hcu hb hd spectator hspec l hl
  refine ⟨D.residues,fun σ mixed => ?_⟩
  have h01 := hgiant l hl σ mixed
  have hB := hsquare E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed
  have hK := hkernel E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed
  have h34 := hcollision E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed
  have h45 := hfinal E C hG hGu hcl hcu hb hd spectator hspec hactual l hl D.residues σ mixed
  exact plain_total_of_stage_bounds C spectator D hl σ mixed H hm h01 hB hK h34 h45

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
