import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementError
open Construction Conclusion HistoryBulkPriorGrid PrimeCellReplacement PrimeProgression PrimeCellFreezing
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget LogCellPartition Filter
open scoped BigOperators

theorem sourceBulkMean_replacement_eventually (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(M:ℕ) [NeZero M], ∀(a:ℕ)(E:Finset ℕ),
      Fintype.card ι ≤ 2^k*bulkSize k L → a ≤ residueCostExponent k →
      Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) → E.card ≤ 2 →
      ∀(hZ:0 < harmonicPrimeMass (bulkPrimeBand L E))
        (hsize:(M:ℝ) < Real.exp (bulkLogLower L))
        (F:(ι → (ZMod M)ˣ) → ℂ)(f:(ι → ℝ) → ℂ),
      (∑u:ι → (ZMod M)ˣ,‖F u‖) ≤ (M:ℝ)^(Fintype.card ι+a) →
      (∀z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
        DifferentiableAt ℝ (fun y => f (fun i => Real.exp (y i))) z) →
      (∀z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),∀i,
        ‖deriv (fun t => f (Characters.RationalHistory.Expr.logCurve (fun q => Real.exp (z q)) i t)) 0‖ ≤
          Real.exp (C*((bulkSize k L:ℝ)+1))) →
      (∀z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
        ‖f (fun i => Real.exp (z i))‖ ≤ Real.exp (C*((bulkSize k L:ℝ)+1))) →
      ‖sourceBulkMean L E hZ M hsize F f-
        principalIntegral M (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
          (fun _ => bulkNormalizer L E) f*∑u:ι → (ZMod M)ˣ,F u‖ ≤
        3*Real.exp (-Real.exp (bulk.target*L)) := by
  obtain ⟨d,K,L₀,hd,hK,_hL₀,hreplace⟩ := exists_sourceBulkMean_replacement_constants
  filter_upwards [eventually_bulk_replacement_error_budget k C hK.le hd,
    eventually_bulk_cell_bounds k hK.le hd,
    HistoryBulkReplacementGeometry.eventually_geometryBounds hd L₀,
    eventually_ge_atTop (0:ℝ)] with L hbudget hcell hgeometry hL
  intro ι _ _ M _ a E hn ha hmod hE hZ hsize F f hF hdif hderiv hf
  have hM := NeZero.pos M
  have hg := hgeometry M hM hmod
  have hi := bulkGeometry_inputs hg
  have hc := hcell E hE
  let A : ℝ := Real.exp (C*((bulkSize k L:ℝ)+1))
  let R : ℝ := ∑u:ι → (ZMod M)ˣ,‖F u‖
  have hA : 0 ≤ A := Real.exp_nonneg _
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hnorm : ∀p:BulkPrimeTuple ι L,
      ‖F (bulkTupleUnits L M hsize p)*f (fun i => ((p i).val:ℝ))‖ ≤ A*R :=
    bulkTuple_test_norm_le L M hsize F f hf
  have hmain := hreplace ι L E hZ M hsize (fun _ : ι => meshWidth bulk L)
    hL hi.1 (fun _ => ⟨hc.2.1,hc.2.2.1⟩) hi.2.2
    (primeEnvelope bulk k 1 K d L) 2 hc.2.2.2.1 (by norm_num)
    (fun j i => (hc.2.2.2.2 ι M hM j i).1)
    (fun j i => (add_le_add le_rfl (hc.2.2.2.2 ι M hM j i).1).trans
      (hc.2.2.2.2 ι M hM j i).2)
    F f A (meshWidth bulk L) A (A*R) hA hc.2.1.le (mul_nonneg hA hR)
    (fun _ => le_rfl) hdif hderiv hf hnorm
  apply hmain.trans
  exact hbudget ι M a E A A (A*R) R hn ha hM hmod hE hA hA (mul_nonneg hA hR) hR
    le_rfl le_rfl (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hF hA) hF

end Ostmann.Arithmetic.HistoryBulkReplacementError

end

end OAI
