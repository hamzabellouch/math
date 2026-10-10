import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

namespace OAI

namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

theorem weighted_error_mono (a B H b₀ b₁ S₀ S₁ : ℝ)
    (hB : 0 ≤ B) (hb₀ : 0 ≤ b₀) (hb : b₀ ≤ b₁) (hS₁ : 0 ≤ S₁)
    (hS : S₀ ≤ B*S₁) :
    a*(B*H)+b₀*S₀ ≤ B*(a*H+b₁*S₁) := by
  calc
    _ ≤ a*(B*H)+b₀*(B*S₁) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hS hb₀)
    _ ≤ a*(B*H)+b₁*(B*S₁) := add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (mul_nonneg hB hS₁))
    _ = _ := by ring

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end OAI
