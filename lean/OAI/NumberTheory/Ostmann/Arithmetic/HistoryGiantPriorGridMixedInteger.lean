import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellTests
import OAI.NumberTheory.Ostmann.Construction.DiagonalExternalMeasure

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction
open scoped BigOperators

theorem closedIntegerCell_subset (G : ℝ) :
    IntegerCell.cellSupport ⌈Real.exp (G+1)⌉₊ (G-1) (G+1) ⊆ integerPivotCell G := by
  intro n hn
  obtain ⟨hn, hp, _, _⟩ := Finset.mem_filter.mp hn
  have hn' := Finset.mem_range.mp hn
  exact Finset.mem_Ioc.mpr ⟨hp,by omega⟩

theorem externalPivotWeight_ne_zero_mem_closedInteger (G : ℝ) {n : ℕ}
    (hn : n ∈ integerPivotCell G) (hw : externalPivotWeight G n ≠ 0) :
    n ∈ IntegerCell.cellSupport ⌈Real.exp (G+1)⌉₊ (G-1) (G+1) := by
  have hφ : smoothPartition (Real.log n-G) ≠ 0 := by
    intro hz
    exact hw (by simp only [externalPivotWeight,hz,mul_zero])
  have hs := smoothPartition_support_subset hφ
  obtain ⟨hp,hn⟩ := Finset.mem_Ioc.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,
    by linarith [hs.1],by linarith [hs.2]⟩

theorem integerPivot_weighted_sum_eq_closed (G : ℝ) (H : ℕ → ℂ) :
    (∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*H n) =
      ∑ n ∈ IntegerCell.cellSupport ⌈Real.exp (G+1)⌉₊ (G-1) (G+1),
        (externalPivotWeight G n:ℂ)*H n := by
  classical
  symm
  apply Finset.sum_subset (closedIntegerCell_subset G)
  intro n hn hnot
  have hz : externalPivotWeight G n = 0 := by
    by_contra hz
    exact hnot (externalPivotWeight_ne_zero_mem_closedInteger G hn hz)
  simp only [hz,Complex.ofReal_zero,zero_mul]

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
