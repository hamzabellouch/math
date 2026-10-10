import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementErrorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementError
open Construction Conclusion HistoryBulkPriorGrid PrimeCellReplacement PrimeProgression
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition Filter

theorem eventually_bulk_cell_bounds (k : ℕ) {K d : ℝ} (hK : 0 ≤ K) (hd : 0 < d) :
    ∀ᶠ L : ℝ in atTop, ∀E:Finset ℕ,E.card ≤ 2 →
      0 < bulkNormalizer L E ∧ 0 < meshWidth bulk L ∧ meshWidth bulk L ≤ 1 ∧
      0 ≤ primeEnvelope bulk k 1 K d L ∧
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι], ∀M:ℕ,0 < M →
      ∀(j:GridBoxIndex (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => meshWidth bulk L))(i:ι),
      correctedPrimeError K d
        (boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) (fun _ => meshWidth bulk L) j i)
        (bulkNormalizer L E) ≤ primeEnvelope bulk k 1 K d L ∧
      |harmonicIntegral M
        (boxLower (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) (fun _ => meshWidth bulk L) j i)
        (boxUpper (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) (fun _ => meshWidth bulk L) j i)/
        bulkNormalizer L E|+primeEnvelope bulk k 1 K d L ≤ 2 := by
  filter_upwards [eventually_actual_primeCell_bounds bulk k (C:=1) (by norm_num) hK hd,
    bulkNormalizer_bounds_eventually,eventually_ge_atTop (0:ℝ)] with L hcell hnorm hL
  intro E hE
  have hz := hnorm E hE
  refine ⟨hz.1,Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _)),
    ?_,?_⟩
  · unfold primeEnvelope
    positivity
  intro ι _ _ M hM j i
  have horder : ∀i:ι,bulkLogLower L ≤ bulkLogUpper L := fun _ =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by norm_num) hL)
  have hlo : Real.exp (bulk.a₀*L) ≤ bulkLogLower L :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by norm_num [bulk]) hL)
  exact hcell M _ _ _ hM (hlo.trans (boxLower_ge _ _ _ horder j i))
    (box_order _ _ _ horder j i) (box_width_le _ _ _ horder (fun _ => Real.exp_pos _) j i)
    hz.1 (hz.2.2.trans (Real.one_le_exp (by positivity)))

end Ostmann.Arithmetic.HistoryBulkReplacementError

end

end OAI
