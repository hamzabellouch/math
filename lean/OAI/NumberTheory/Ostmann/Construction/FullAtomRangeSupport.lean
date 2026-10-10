import OAI.NumberTheory.Ostmann.Construction.FullAtomWeightSupport
import OAI.NumberTheory.Ostmann.Construction.InsertedAtomAssignment

namespace OAI

/-! # The original pivot interval remains present in full coefficient support -/

namespace Ostmann

open scoped Classical

theorem fullAtomTransferWeight_top_range {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n x t ≠ 0)
    (r : ScheduleAtomRange role n) (hr : r ∈ ranges n) : r.Holds x := by
  have hg := (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n x t hw).1.2.2
  cases n with
  | zero => exact hg r hr
  | succ n => exact hg.1 r hr

noncomputable def pivotIntervalTest {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (p : CurrentPivotConstituent role n) (lo hi : ℕ) : ScheduleAtomRange role n where
  atoms := [scheduledPartitionEquiv role n (.inl p)]
  lower := lo
  upper := hi

theorem fullAtomTransferWeight_pivot_interval {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ) (t : FrequencyTree ℤ n)
    (p : CurrentPivotConstituent role n) (lo hi M : ℕ)
    (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (hr : pivotIntervalTest role n p lo hi ∈ ranges n)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M l u) t ≠ 0) : M ∈ Finset.Icc lo hi := by
  have hg := fullAtomTransferWeight_top_range role childBound pivotBound ranges leaf n _ t hw _ hr
  have hh : (M : ℝ) ∈ Set.Icc (lo : ℝ) (hi : ℝ) := by
    simpa only [pivotIntervalTest, ScheduleAtomRange.Holds, List.map_singleton,
      List.prod_singleton, scheduledInsertedAtoms_pivot] using hg
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩

end Ostmann

end OAI
