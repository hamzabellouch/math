import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) where
  weight z := μ.weight z.1*(κ z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) ((κ z.1).nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, total, mul_one]

theorem expect_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (joint μ κ).expect f=μ.expect (fun ω => (κ ω).expect (fun ξ => f (ω, ξ))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem support_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (z : Ω × Ξ)
    (h : 0 < (joint μ κ).weight z) : 0 < μ.weight z.1 ∧ 0 < (κ z.1).weight z.2 := by
  exact ⟨pos_of_mul_pos_left h ((κ z.1).nonneg z.2), pos_of_mul_pos_right h (μ.nonneg z.1)⟩

end MetricKMedian.FiniteLaw
end
end

end OAI
