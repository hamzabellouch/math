import OAI.Combinatorics.ContingencyTables.Parameters
import Mathlib.Data.Nat.Cast.Order.Field

namespace OAI

/-!
# Integer bin widths for dense blocks

The free-cell width is the actual integer quotient `floor(s/B)`, where
`s=min(Rᵢ,Pⱼ)`. Large margins give the two-sided scale comparison used in
the dense rejection sampler.
-/

namespace ContingencyTables.DenseAffine

theorem integer_width_bounds (s B : ℕ) (hB : 0 < B) (hs : 2 * B ≤ s) :
    (s : ℝ) / (2 * B) ≤ (s / B : ℕ) ∧ (s / B : ℕ) ≤ (s : ℝ) / B := by
  have hq : 0 < s / B := Nat.div_pos (by omega) hB
  have hmod := Nat.mod_lt s hB
  have hid := Nat.mod_add_div s B
  have hscale : s ≤ 2 * B * (s / B) := by nlinarith
  constructor
  · apply (div_le_iff₀ (show (0 : ℝ) < 2 * B by positivity)).mpr
    have hscale' : (s : ℝ) ≤ 2 * (B : ℝ) * (s / B : ℕ) := by exact_mod_cast hscale
    nlinarith
  · exact Nat.cast_div_le

theorem dense_width_positive (d s : ℕ) (hd : 14 ≤ d) (hs : d ^ 12 ≤ s) :
    0 < s / d ^ 8 := by
  have hd₀ : 0 < d := by omega
  have hpow : d ^ 8 ≤ d ^ 12 := by
    apply Nat.pow_le_pow_right (by omega : 1 ≤ d)
    decide
  exact Nat.div_pos (hpow.trans hs) (pow_pos hd₀ _)

theorem dense_width_bounds (d s : ℕ) (hd : 14 ≤ d) (hs : d ^ 12 ≤ s) :
    (s : ℝ) / (2 * (d : ℝ) ^ 8) ≤ (s / d ^ 8 : ℕ) ∧
      (s / d ^ 8 : ℕ) ≤ (s : ℝ) / (d : ℝ) ^ 8 := by
  have hd₀ : 0 < d := by omega
  have hfour : 2 ≤ d ^ 4 := by
    have h := Nat.le_self_pow (show 4 ≠ 0 by decide) d
    omega
  have hscale : 2 * d ^ 8 ≤ d ^ 12 := by
    calc
      2 * d ^ 8 ≤ d ^ 4 * d ^ 8 := Nat.mul_le_mul_right _ hfour
      _ = d ^ 12 := by ring
  simpa only [Nat.cast_pow] using
    integer_width_bounds s (d ^ 8) (pow_pos hd₀ _) (hscale.trans hs)

/-- The product `A*d/B=d⁻³` is at most one with the actual integer
parameter choices. This controls the density within each unit bin. -/
theorem dense_exponent_change_scale (d : ℕ) (hd : 14 ≤ d) :
    (d : ℝ) ^ 4 * d / (d : ℝ) ^ 8 ≤ 1 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  apply (div_le_one (pow_pos hd₀ _)).mpr
  calc
    (d : ℝ) ^ 4 * d = (d : ℝ) ^ 5 := by ring
    _ ≤ (d : ℝ) ^ 8 := pow_le_pow_right₀ hd₁ (by decide)

end ContingencyTables.DenseAffine

end OAI
