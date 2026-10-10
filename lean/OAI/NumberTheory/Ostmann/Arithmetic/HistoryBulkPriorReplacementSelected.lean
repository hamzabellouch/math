import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementGeometryBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourceBulkMean_selected_eq
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) :
    sourceBulkMean L E C.bulkPositive M hsize F f =
      (dependentProductPrior (fun _ : ι => C.bulk.law)).cmean (fun p =>
        F (fun i => bulkPrimeUnit L M hsize (p i).val
          (bulkPrimeBand_subset_closed L E (p i).property))*f (fun i => ((p i).val : ℝ))) := rfl

theorem bulkTuple_test_norm_le (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L))
    (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) {A : ℝ}
    (hf : ∀ z∈logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
      ‖f (fun i => Real.exp (z i))‖ ≤ A) (p : BulkPrimeTuple ι L) :
    ‖F (bulkTupleUnits L M hsize p)*f (fun i => ((p i).val : ℝ))‖ ≤
      A*∑ u : ι → (ZMod M)ˣ, ‖F u‖ := by
  classical
  have ha := hf (tupleLog (fun _ => bulkPrimeCutoff L)
    (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) p)
    (tupleLog_mem (fun _ => bulkPrimeCutoff L) (fun _ => bulkLogLower L) (fun _ => bulkLogUpper L) p)
  rw [exp_tupleLog] at ha
  have hb : ‖F (bulkTupleUnits L M hsize p)‖ ≤ ∑ u : ι → (ZMod M)ˣ, ‖F u‖ :=
    Finset.single_le_sum (fun u _ => norm_nonneg (F u)) (Finset.mem_univ _)
  rw [norm_mul, mul_comm A]
  exact mul_le_mul hb ha (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem bulkGeometry_inputs {dAP L₀ L : ℝ} {M : ℕ}
    (hg : HistoryBulkReplacementGeometry.GeometryBounds dAP L₀ M L) :
    L₀ ≤ bulkLogLower L ∧ (M : ℝ) < Real.exp (bulkLogLower L) ∧
      (M : ℝ) ≤ Real.exp (dAP*(bulkLogLower L)^(1/3 : ℝ)) :=
  (hg.at_lower (bulkLogLower L) le_rfl).2

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
