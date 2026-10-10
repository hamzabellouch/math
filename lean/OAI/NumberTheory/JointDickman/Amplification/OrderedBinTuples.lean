import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeTupleLimit
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBinPartition

namespace OAI

/-! # Limits of ordered prime tuples with prescribed bin indices -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def orderedBinTupleMass (J h : ℕ) (A x : ℝ)
    (r : Fin h → Fin (J-1)) : ℝ := by
  classical
  exact ∑ v ∈ orderedPrimeTuples (largePrimeSet x (x^((1 : ℝ)/J))) h,
    if (∀ i, v i ∈ primeBin x J ((r i).val+1)) ∧ (∏ i, v i) ≤ ⌊A*x⌋₊
      then ∏ i, 1/(v i : ℝ) else 0

noncomputable def orderedBinTupleLimit (J h : ℕ) (r : Fin h → Fin (J-1)) : ℝ :=
  (FiniteMeasure.pi (fun _ : Fin h => logarithmicPrimeMeasure ((1 : ℝ)/J)))
    (orderedPrimeBox h (fun i => ((r i).val+1 : ℝ)/J)
      (fun i => ((r i).val+2 : ℝ)/J) 1)

theorem orderedBinTupleMass_tendsto {J : ℕ} (hJ : 2 ≤ J) {A : ℝ} (hA : 0 < A)
    (n : ℕ) (r : Fin (n+1) → Fin (J-1)) :
    Tendsto (fun x => orderedBinTupleMass J (n+1) A x r) atTop (𝓝 (orderedBinTupleLimit J (n+1) r)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hc : 0 < (1 : ℝ)/J := div_pos zero_lt_one hJ0
  have hc1 : (1 : ℝ)/J < 1 := (div_lt_one hJ0).mpr (by exact_mod_cast (show 1 < J by omega))
  have ht := orderedReciprocalPrimeTuple_scaled_box_tendsto hc hc1 hA n
    (fun i => ((r i).val+1 : ℝ)/J) (fun i => ((r i).val+2 : ℝ)/J)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  unfold orderedBinTupleMass
  apply sum_congr rfl
  intro v hv
  have hp (i : Fin (n+1)) : (v i).Prime :=
    (Nat.mem_primesLE.mp (mem_filter.mp ((orderedPrimeTuples_mem.mp hv).1 i)).1).2
  have he : (∀ i, v i ∈ primeBin x J ((r i).val+1)) ↔
      ∀ i, x^(((r i).val+1 : ℝ)/J) < v i ∧ (v i : ℝ) ≤ x^(((r i).val+2 : ℝ)/J) := by
    apply forall_congr'
    intro i
    have hu : ((r i).val : ℝ)+1+1 = ((r i).val : ℝ)+2 := by ring
    simpa only [hp i, true_and, Nat.cast_add, Nat.cast_one, hu] using
      (mem_primeBin_iff (zero_le_one.trans hx) J ((r i).val+1) (v i))
  have hf : (∏ i, v i) ≤ ⌊A*x⌋₊ ↔ (∏ i, (v i : ℝ)) ≤ A*x := by
    rw [Nat.le_floor_iff (mul_nonneg hA.le (zero_le_one.trans hx))]
    norm_cast
  simp only [← he, ← hf]

end JointDickman

end OAI
