import OAI.Probability.ContinuumTransition.QuadraticBlocks

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gridIndex_mem_of_mem_union {u : ℝ} (hu : 0 < u) {s : Finset Lattice} {x : Space}
    (hx : x ∈ ⋃ k ∈ s, gridBox u k) : gridIndex u x ∈ s := by
  obtain ⟨k, hk, hx⟩ := mem_iUnion₂.mp hx
  rwa [(mem_gridBox_iff hu k x).1 hx]

theorem cube_subset_gridBlocks {u : ℝ} (hu : 0 < u) (m : ℕ) :
    cube (2*(m : ℝ)*u) ⊆ ⋃ k ∈ gridIndices m 1, gridBox u k := by
  intro x hx
  apply mem_iUnion₂.mpr
  refine ⟨gridIndex u x, ?_, mem_gridBox hu x⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hxi := hx i
  change -(m : ℤ)*1 ≤ ⌊x i/u⌋ ∧ ⌊x i/u⌋ ≤ (m : ℤ)*1
  simp only [mul_one]
  constructor
  · apply Int.le_floor.mpr
    rw [le_div_iff₀ hu]
    push_cast
    exact (by linarith [hxi.1])
  · apply Int.floor_le_iff.mpr
    rw [div_lt_iff₀ hu]
    push_cast
    nlinarith [hxi.2]

end ContinuumTemperature
end

end OAI
