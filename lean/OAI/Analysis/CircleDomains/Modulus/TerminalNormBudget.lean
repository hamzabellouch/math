import OAI.Analysis.CircleDomains.Topology.ParallelDiskTolls

namespace OAI

/-!
# From terminal excess to the full oscillation norm

The finite transfer bounds the square-sum of the positive excess above
the original band widths. The elementary Euclidean triangle inequality
then gives the full oscillation norm needed in parallel-line payment.
-/

open Set

namespace CircleDomainRigidity

theorem sqrt_sum_sq_add_le {I : Type*} [Fintype I] (a b : I → ℝ) :
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤
      Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have ha := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i)))
  have hb := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (b i)))
  have hab := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hsum : (∑ i, (a i + b i) ^ 2) =
      (∑ i, a i ^ 2) + 2 * (∑ i, a i * b i) + ∑ i, b i ^ 2 := by
    simp_rw [add_sq]
    simp only [Finset.sum_add_distrib]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  nlinarith

theorem sqrt_sum_sq_le_band_add_excess {I : Type*} [Fintype I]
    (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ Real.sqrt (∑ i, b i ^ 2) +
      Real.sqrt (∑ i, max (a i - b i) 0 ^ 2) := by
  calc
    _ ≤ Real.sqrt (∑ i, (b i + max (a i - b i) 0) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (ha i) (add_nonneg (hb i) (le_max_right _ _))).mpr
      linarith [le_max_left (a i - b i) 0]
    _ ≤ _ := sqrt_sum_sq_add_le b (fun i => max (a i - b i) 0)

theorem sqrt_sum_sq_le_of_excess_budget {I : Type*} [Fintype I]
    (a b : I → ℝ) {B ε : ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hband : Real.sqrt (∑ i, b i ^ 2) ≤ B)
    (hexcess : Real.sqrt (∑ i, max (a i - b i) 0 ^ 2) ≤ ε) :
    Real.sqrt (∑ i, a i ^ 2) ≤ B + ε :=
  (sqrt_sum_sq_le_band_add_excess a b ha hb).trans (add_le_add hband hexcess)

end CircleDomainRigidity

end OAI
