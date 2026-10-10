import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OrderedSpanConditioning

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem spanConditionConstant_rescale (M τ R : ℝ) (hτ : τ ≠ 0) (hR : R ≠ 0) (n : ℕ) :
    spanConditionConstant (M * R) (τ * R) n = spanConditionConstant M τ n / R := by
  induction n with
  | zero => simp only [spanConditionConstant, zero_div]
  | succ n ih =>
    simp only [spanConditionConstant, ih]
    field_simp

end

end RieszRectifiability

end OAI
