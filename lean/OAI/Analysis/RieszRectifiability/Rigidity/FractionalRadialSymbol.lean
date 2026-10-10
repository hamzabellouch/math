import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSymbolPositivity
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSymbolInvariance

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem fractionalSymbol_eq_positive_constant_mul_norm (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Ambient (p + 1), fractionalSymbol p ξ = c * ‖ξ‖ := by
  obtain ⟨v, hv⟩ := exists_norm_eq (E := Ambient (p + 1)) (show (0 : ℝ) ≤ 1 from zero_le_one)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    norm_num at hv
  exact ⟨fractionalSymbol p v, fractionalSymbol_pos p v hv0,
    fractionalSymbol_eq_unit_mul_norm p v hv⟩

end

end RieszRectifiability

end OAI
