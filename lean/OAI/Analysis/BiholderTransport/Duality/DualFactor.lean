import Mathlib

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport
section DualFactor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma dual_factor_norm_comparison (Q : E →L[ℝ] E) (L A : E →L[ℝ] F)
    {s c C : ℝ} (hs : 0 < s) (hc : 0 < c) (hC : 0 < C)
    (hL : Function.Surjective L)
    (hLn : ∀ k, c * ‖k‖ ≤ ‖L k‖ ∧ ‖L k‖ ≤ C * ‖k‖)
    (h : ∀ a k, s * inner ℝ (Q a) k = inner ℝ (L k) (A a)) (a : E) :
    c * ‖A a‖ ≤ s * ‖Q a‖ ∧ s * ‖Q a‖ ≤ C * ‖A a‖ := by
  constructor
  · obtain ⟨k,hk⟩ := hL (A a)
    have H := h a k
    rw [hk,real_inner_self_eq_norm_sq] at H
    have H1 := real_inner_le_norm (Q a) k
    have H2 := (hLn k).1
    rw [hk] at H2
    by_cases hz : ‖A a‖ = 0
    · rw [hz,mul_zero]; positivity
    · have hp : 0 < ‖A a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have H3 := mul_le_mul_of_nonneg_left H1 hs.le
      have H4 := mul_le_mul_of_nonneg_left H2 (mul_nonneg hs.le (norm_nonneg (Q a)))
      have H5 := mul_le_mul_of_nonneg_left H3 hc.le
      nlinarith
  · have H := h a (Q a)
    rw [real_inner_self_eq_norm_sq] at H
    have H1 := real_inner_le_norm (L (Q a)) (A a)
    have H2 := mul_le_mul_of_nonneg_right (hLn (Q a)).2 (norm_nonneg (A a))
    by_cases hz : ‖Q a‖ = 0
    · rw [hz,mul_zero]; positivity
    · have hp : 0 < ‖Q a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith

end DualFactor
end WeakMTWTransport

end

end

end

end OAI
