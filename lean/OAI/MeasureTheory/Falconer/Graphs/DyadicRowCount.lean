import OAI.MeasureTheory.Falconer.Estimates.DyadicTree

namespace OAI

/-! # Counting the original dyadic rows at the terminal scale -/

namespace Falconer
open MeasureTheory

theorem dyadic_row_count_le {d j : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) {R : ℝ} (hR : 0 ≤ R) (hj : (2 : ℝ)^j ≤ R) :
    ((Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j).card : ℝ) ≤ R^(2*d) := by
  have hc (Q : DyadicCube d) (ρ : Measure (Space d)) :
      ((Q.occupiedPaths ρ j).card : ℝ) ≤ R^d := by
    calc
      _ ≤ (2 : ℝ)^(d*j) := by exact_mod_cast Q.card_occupiedPaths_le ρ j
      _ = ((2 : ℝ)^j)^d := by rw [← pow_mul,Nat.mul_comm]
      _ ≤ R^d := pow_le_pow_left₀ (by positivity) hj d
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ R^d*R^d := mul_le_mul (hc Q₁ μ) (hc Q₂ ν) (by positivity) (pow_nonneg hR d)
    _ = R^(2*d) := by rw [← pow_add]; congr 1; omega

theorem dyadic_row_count_at_terminal_depth {d j N : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (hj : j ≤ N) :
    ((Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j).card : ℝ) ≤ ((2 : ℝ)^N)^(2*d) :=
  dyadic_row_count_le Q₁ Q₂ μ ν (by positivity) (pow_le_pow_right₀ (by norm_num) hj)

end Falconer

end OAI
