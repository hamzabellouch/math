import OAI.NumberTheory.DukePrimeDegree.Arithmetic.Arithmetic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-!
# Summing the separated-zero comparison

The rescaled zero coordinates in the manuscript are
`Xρ = L (1 - Re ρ)` and `Yρ = L Im ρ`. A uniform zero-free disk gives
`c² ≤ Xρ² + Yρ²`. Summing the elementary pointwise comparison controls
the real Hadamard sum throughout the discriminant-scaled interval.
-/

namespace DukePrimeDegree

/-- Control the whole zero sum at every `0 < U ≤ 4` by its value at
`U = 1`. Convergence at `U = 1` implies convergence throughout this range. -/
theorem zero_sum_comparison {ι : Type*}
    (X Y : ι → ℝ) (c U : ℝ) (hc : 0 < c) (hU : 0 < U) (hU4 : U ≤ 4)
    (hX : ∀ i, 0 ≤ X i) (hgap : ∀ i, c ^ 2 ≤ X i ^ 2 + Y i ^ 2)
    (hsum : Summable (fun i => (X i + 1) / ((X i + 1) ^ 2 + Y i ^ 2))) :
    Summable (fun i => (X i + U) / ((X i + U) ^ 2 + Y i ^ 2)) ∧
      (∑' i, (X i + U) / ((X i + U) ^ 2 + Y i ^ 2)) ≤
        (8 + 8 / c ^ 2) * ∑' i, (X i + 1) / ((X i + 1) ^ 2 + Y i ^ 2) := by
  have hnonneg : ∀ i, 0 ≤ (X i + U) / ((X i + U) ^ 2 + Y i ^ 2) := by
    intro i
    exact div_nonneg (add_nonneg (hX i) hU.le) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hbound : ∀ i, (X i + U) / ((X i + U) ^ 2 + Y i ^ 2) ≤
      (8 + 8 / c ^ 2) * ((X i + 1) / ((X i + 1) ^ 2 + Y i ^ 2)) :=
    fun i => zero_contribution_comparison (hX i) hU hU4 hc (hgap i)
  have hsum' := Summable.of_nonneg_of_le hnonneg hbound (hsum.mul_left (8 + 8 / c ^ 2))
  refine ⟨hsum', ?_⟩
  calc
    _ ≤ ∑' i, (8 + 8 / c ^ 2) * ((X i + 1) / ((X i + 1) ^ 2 + Y i ^ 2)) :=
      hsum'.tsum_le_tsum hbound (hsum.mul_left _)
    _ = _ := tsum_mul_left

end DukePrimeDegree

end OAI
