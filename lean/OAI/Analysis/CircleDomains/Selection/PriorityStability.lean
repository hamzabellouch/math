import OAI.Analysis.CircleDomains.Modulus.PriorityWeights

namespace OAI

/-! Stability of the countable interpolation under changes in its
active scalar values. Cutoffs equal to zero need no coefficient bound. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityInfiniteValue_stability
    {χ c d : ℕ → ℝ} (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1)
    {B C ε x y : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (hd : ∀ n, ‖d n‖ ≤ C)
    (hxy : ‖x-y‖ ≤ ε) (hcd : ∀ n, χ n = 0 ∨ ‖c n-d n‖ ≤ ε) :
    ‖priorityInfiniteValue χ c x-priorityInfiniteValue χ d y‖ ≤ ε := by
  have hw := priorityWeight_tsum_mem_unit hχ
  have hrem : 0 ≤ 1-∑' n, priorityWeight χ n := by linarith [hw.2]
  have hcs := priorityWeighted_summable hχ hc
  have hds := priorityWeighted_summable hχ hd
  have hdiff : (∑' n, priorityWeight χ n*(c n-d n)) =
      (∑' n, priorityWeight χ n*c n)-(∑' n, priorityWeight χ n*d n) := by
    simp_rw [mul_sub]
    exact hcs.tsum_sub hds
  have hterm (n : ℕ) : ‖priorityWeight χ n*(c n-d n)‖ ≤ priorityWeight χ n*ε := by
    rcases hcd n with hn | hn
    · simp [priorityWeight, hn]
    · rw [norm_mul, Real.norm_eq_abs (priorityWeight χ n), abs_of_nonneg (priorityWeight_nonneg hχ n)]
      exact mul_le_mul_of_nonneg_left hn (priorityWeight_nonneg hχ n)
  have hsum : ‖∑' n, priorityWeight χ n*(c n-d n)‖ ≤ (∑' n, priorityWeight χ n)*ε := by
    have h := tsum_of_norm_bounded (f := fun n => priorityWeight χ n*(c n-d n))
      ((priorityWeight_summable hχ).mul_right ε).hasSum hterm
    simpa only [(priorityWeight_summable hχ).tsum_mul_right] using h
  have heq : priorityInfiniteValue χ c x-priorityInfiniteValue χ d y =
      (1-∑' n, priorityWeight χ n)*(x-y)+∑' n, priorityWeight χ n*(c n-d n) := by
    rw [priorityInfiniteValue, priorityInfiniteValue, hdiff]
    ring
  rw [heq]
  calc
    _ ≤ ‖(1-∑' n, priorityWeight χ n)*(x-y)‖+‖∑' n, priorityWeight χ n*(c n-d n)‖ := norm_add_le _ _
    _ ≤ (1-∑' n, priorityWeight χ n)*ε+(∑' n, priorityWeight χ n)*ε := by
      rw [norm_mul, Real.norm_eq_abs (1-∑' n, priorityWeight χ n), abs_of_nonneg hrem]
      exact add_le_add (mul_le_mul_of_nonneg_left hxy hrem) hsum
    _ = ε := by ring

end CircleDomainRigidity

end

end OAI
