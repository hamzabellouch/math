import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductGapBudget
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationGapList

namespace OAI

/-! # The prescribed cutoff is the exact-target instance of the product schedule -/
namespace Ostmann
open scoped BigOperators

private theorem headD_drop_ofFn {k : ℕ} (f : Fin k → ℝ) (n : ℕ) (hn : n < k) :
    ((List.ofFn f).drop n).headD 0 = f ⟨n, hn⟩ := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [List.ofFn_succ]
    cases n with
    | zero => simp
    | succ n =>
      rw [List.drop_succ_cons]
      exact (ih (fun i => f i.succ) n (by omega)).trans (congrArg f (Fin.ext (by rfl)))

theorem movingProductExponent_sum_gaps (T : ℕ → ℝ) (W : ℝ) (n : ℕ) :
    movingProductExponent T W n = W +
      ∑ j ∈ Finset.range n, (movingProductExponent T W j - 2 * T j) := by
  induction n with
  | zero => simp [movingProductExponent]
  | succ n ih =>
    rw [Finset.sum_range_succ, movingProductExponent]
    linarith

theorem movingProductFrequency_prescribed (G J Y Bs BD Bz L : ℝ) (k n : ℕ)
    (hn : n ≤ k)
    (hbase : 2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)) :
    let ws := movingCompensationTargets J (movingCompensationGaps k BD Bz L)
    movingProductFrequencyExponent (movingTargetPivotExponent G ws)
      (2 * G + J + ws.sum) Y (spectatorBulkCount k L) n =
      movingCutoffExponent Bs BD Bz ((k : ℝ) ^ 4) (spectatorBulkCount k L) n := by
  intro ws
  unfold movingProductFrequencyExponent movingCutoffExponent
  rw [movingProductExponent_sum_gaps]
  have hsum : (∑ j ∈ Finset.range n,
      (movingProductExponent (movingTargetPivotExponent G ws) (2 * G + J + ws.sum) j -
        2 * movingTargetPivotExponent G ws j)) =
      ∑ j ∈ Finset.range n, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ j) (spectatorBulkCount k L) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j < k := (Finset.mem_range.mp hj).trans_le hn
    rw [movingProductExponent_target_gap G J _ j (by simpa using hjk)]
    unfold movingCompensationGaps
    rw [headD_drop_ofFn _ j hjk]
    dsimp only
    exact mul_div_cancel₀ _ (by positivity)
  rw [hsum]
  dsimp only [ws] at *
  linarith

/-- Consequently this construction retains the original floor cutoffs when
there is no cell-center error. -/
theorem movingProductNaturalCutoff_prescribed (G J Y Bs BD Bz L : ℝ) (k n : ℕ)
    (hn : n ≤ k)
    (hbase : 2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)) :
    let ws := movingCompensationTargets J (movingCompensationGaps k BD Bz L)
    movingProductNaturalCutoff (movingTargetPivotExponent G ws)
      (2 * G + J + ws.sum) Y (spectatorBulkCount k L) n =
      movingNaturalCutoff Bs BD Bz ((k : ℝ) ^ 4) (spectatorBulkCount k L) n := by
  intro ws
  unfold movingProductNaturalCutoff movingNaturalCutoff
  rw [movingProductFrequency_prescribed G J Y Bs BD Bz L k n hn hbase]

end Ostmann

end OAI
