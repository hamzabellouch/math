import OAI.NumberTheory.JointDickman.Counting.CountingParameterVariation
import OAI.NumberTheory.JointDickman.Counting.CountingPeriodicModel
import OAI.NumberTheory.JointDickman.Probability.CutNormParameter

namespace OAI

/-! # Parameter continuity of the actual counting-model entries -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem countingSiteWithSeries_entry_variation (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {σ σ' K : ℝ} (hK : 0 ≤ K)
    (hkernel : ∀ j : ℕ, H < j → j < T → ∀ x y,
      |countingPrimeKernel P m B j c D T σ x y-countingPrimeKernel P m B j c D T σ' x y| ≤ K*|σ-σ'|)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteWithSeries F P m B L T H M τ C c D σ i k a b-
      countingSiteWithSeries F P m B L T H M τ C c D σ' i k a b| ≤
      (∑ j ∈ range (T+1), |independentRootMean B L τ C*(F j/(j : ℝ))| *K)*|σ-σ'| := by
  let V := ∑ j ∈ range (T+1), |independentRootMean B L τ C*(F j/(j : ℝ))| *K
  have hV : 0 ≤ V := sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hK)
  have hj (j : ℕ) (hH : H < j) (hT : j < T) (a b : Finset ℕ) :
      |countingCandidateWithSeries F P m B L j τ C c D T σ a b-
        countingCandidateWithSeries F P m B L j τ C c D T σ' a b| ≤ V*|σ-σ'| := by
    unfold countingCandidateWithSeries subsetPrimeModel
    rw [← mul_sub,abs_mul]
    apply (mul_le_mul_of_nonneg_left (hkernel j hH hT _ _) (abs_nonneg _)).trans
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact single_le_sum (s := range (T+1))
      (f := fun l => |independentRootMean B L τ C*(F l/(l : ℝ))| *K)
      (fun l _ => mul_nonneg (abs_nonneg _) hK) (mem_range.mpr (by omega))
  change _ ≤ V*|σ-σ'|
  unfold countingSiteWithSeries
  split_ifs with hik hh hki hh
  · exact hj _ hh.1 hh.2 _ _
  · simp only [sub_self,abs_zero]; positivity
  · exact hj _ hh.1 hh.2 _ _
  · simp only [sub_self,abs_zero]; positivity
  · simp only [sub_self,abs_zero]; positivity

end JointDickman

end OAI
