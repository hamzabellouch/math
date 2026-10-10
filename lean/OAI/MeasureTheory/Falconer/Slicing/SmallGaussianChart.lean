import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # A fixed direction-chart radius for the controlled Gaussian slice geometry -/

namespace Falconer

theorem exists_small_gaussian_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 ∧
      4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
  let A : ℝ := 4*(h:ℝ)+1+8*(h:ℝ)*(h+2:ℝ)
  let ρ : ℝ := 1/(8*(A+1))
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 8*(A+1)*ρ = 1 := by dsimp [ρ]; field_simp
  have hp : A*ρ ≤ 1/8 := by nlinarith
  have hcoef : (h:ℝ)*((h+2:ℝ)*2) ≤ A := by dsimp [A]; nlinarith
  refine ⟨ρ,hρ,?_,?_,?_⟩
  · nlinarith [mul_nonneg hA hρ.le]
  · have hb := mul_le_mul_of_nonneg_right hcoef hρ.le
    nlinarith
  · calc
      _ = A*ρ := by dsimp [A]; ring
      _ ≤ 1/8 := hp
      _ ≤ 1/4 := by norm_num

end Falconer

end OAI
