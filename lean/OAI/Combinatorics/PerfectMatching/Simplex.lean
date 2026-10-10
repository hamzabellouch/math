import Mathlib

namespace OAI

/-!
Probability vectors on finite types, with their convexity and compactness properties.
The function-space simplex is the range of the weights of `Convexity.StdSimplex`.
-/

noncomputable section

open scoped BigOperators

namespace MatchingEntropy

/-- Nonnegative real weights with total mass one. -/
def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem probabilitySimplex_eq_range (Index : Type*) [Fintype Index] :
    probabilitySimplex Index =
      Set.range (fun simplex : Convexity.StdSimplex ℝ Index ↦ ⇑simplex.weights) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  ext weights
  simp [probabilitySimplex]

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

theorem single_mem_probabilitySimplex {Index : Type*} [Fintype Index]
    [DecidableEq Index] (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index := by
  constructor
  · intro other
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

theorem probabilitySimplex_le_one {Index : Type*} [Fintype Index] {weights : Index → ℝ}
    (mem : weights ∈ probabilitySimplex Index) (index : Index) : weights index ≤ 1 := by
  rw [← mem.2]
  exact Finset.single_le_sum (fun other _ ↦ mem.1 other) (Finset.mem_univ index)

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  rw [probabilitySimplex_eq_range]
  exact isCompact_range
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).continuous

end MatchingEntropy

end

end OAI
