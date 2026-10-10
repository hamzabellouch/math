import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Choosing the comparison loss before the compactness contact margin -/

namespace Falconer

theorem one_scale_loss_choice (d : ℕ) {ε gain : ℝ} (hε : 0 < ε) (hgain : 0 < gain) :
    ∃ τ : ℝ, 0 < τ ∧ (2*(d:ℝ)+4)*τ ≤ ε/2 ∧
      (20*(2*(d:ℝ)+4)+4)*τ ≤ gain/8 ∧ 2*τ ≤ gain := by
  let L : ℝ := 2*(d:ℝ)+4
  have hL : 0 < L := by dsimp [L]; positivity
  have hS : 0 < 20*L+4 := by positivity
  let τ := min (min (ε/(2*L)) (gain/(8*(20*L+4)))) (gain/2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ ≤ ε/(2*L) := (min_le_left _ _).trans (min_le_left _ _)
  have hτgain : τ ≤ gain/(8*(20*L+4)) := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,?_,?_,?_⟩
  · change L*τ ≤ ε/2
    calc
      _ ≤ L*(ε/(2*L)) := mul_le_mul_of_nonneg_left hτε hL.le
      _ = _ := by field_simp
  · change (20*L+4)*τ ≤ gain/8
    calc
      _ ≤ (20*L+4)*(gain/(8*(20*L+4))) := mul_le_mul_of_nonneg_left hτgain hS.le
      _ = _ := by field_simp
  · have hh : τ ≤ gain/2 := min_le_right _ _
    linarith

end Falconer

end OAI
