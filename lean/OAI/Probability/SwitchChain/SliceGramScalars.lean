import Mathlib

namespace OAI

namespace Problem315.SliceGram

theorem eigenvalue_relation (N b d mu₁ mu₂ : ℝ)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) :
    N * (N - 3) * mu₂ = (N - 1) * (N - 2 * mu₁) := by
  rw [hmu₁, hmu₂]
  nlinarith [hconstant]

theorem degree_two_eigenvalue_le (N b d mu₁ mu₂ : ℝ) (hN : 4 ≤ N)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) (hpos : 0 ≤ mu₁) :
    mu₂ ≤ (N - 1) / (N - 3) := by
  have hrel := eigenvalue_relation N b d mu₁ mu₂ hconstant hmu₁ hmu₂
  have hfactor : 0 < N * (N - 3) := mul_pos (by linarith) (by linarith)
  apply (mul_le_mul_iff_right₀ hfactor).mp
  have hden : N - 3 ≠ 0 := by linarith
  calc
    N * (N - 3) * mu₂ = (N - 1) * (N - 2 * mu₁) := hrel
    _ ≤ (N - 1) * N := by nlinarith
    _ = N * (N - 3) * ((N - 1) / (N - 3)) := by field_simp

theorem degree_two_eigenvalue_le_johnson (N b d mu₁ mu₂ : ℝ) (hN : 4 ≤ N)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) (hpos : 0 ≤ mu₁) :
    mu₂ ≤ N - 1 := by
  apply (degree_two_eigenvalue_le N b d mu₁ mu₂ hN hconstant hmu₁ hmu₂ hpos).trans
  apply (div_le_iff₀ (by linarith : 0 < N - 3)).mpr
  nlinarith

end Problem315.SliceGram

end OAI
