import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableAmplification
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace OAI

/-!
# Binary charge amplification and integer rounding

An integer within a constant factor of `exp D` has binary length linear in
`D`. Rational Taylor sums compute this scale with explicit positive-integer
charge rounding bounds.
-/

namespace ContinuumCoulomb

def binaryAmplification (D : ℕ) : ℕ := taylorAmplification D

theorem binaryAmplification_pos (D : ℕ) : 0 < binaryAmplification D := by
  exact taylorAmplification_pos D

theorem binaryAmplification_ge_scale (D : ℕ) : D + 1 ≤ binaryAmplification D :=
  taylorAmplification_ge_scale D

theorem binaryAmplification_bounds (D : ℕ) :
    Real.exp (D : ℝ) / 2 ≤ (binaryAmplification D : ℝ) ∧
      (binaryAmplification D : ℝ) ≤ 2 * Real.exp (D : ℝ) := by
  exact taylorAmplification_bounds D

/-- Exponentially large charges still have only linearly many binary digits. -/
theorem binaryAmplification_bit_length (D : ℕ) :
    Nat.size (binaryAmplification D) ≤ 2 * D + 2 := by
  apply Nat.size_le.mpr
  have hexp : Real.exp (D : ℝ) ≤ (4 : ℝ) ^ D := by
    have h : Real.exp (D : ℝ) = Real.exp 1 ^ D := by
      simpa only [mul_one] using Real.exp_nat_mul 1 D
    rw [h]
    exact pow_le_pow_left₀ (Real.exp_pos _).le
      (Real.exp_one_lt_three.le.trans (by norm_num)) D
  have hscale := (binaryAmplification_bounds D).2
  have hpow : (0 : ℝ) < (4 : ℝ) ^ D := by positivity
  have heq : (2 : ℝ) ^ (2 * D + 2) = 4 * (4 : ℝ) ^ D := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  have hbound : (binaryAmplification D : ℝ) < (2 : ℝ) ^ (2 * D + 2) := by
    rw [heq]
    linarith
  exact_mod_cast hbound

/-- Rational rounding used by the charge-output algorithm. -/
def rationalRoundedScaledCharge (Z : ℕ) (q : ℚ) : ℕ := (round ((Z : ℚ) * q)).toNat

noncomputable def roundedScaledCharge (Z : ℕ) (q : ℝ) : ℕ :=
  (round ((Z : ℝ) * q)).toNat

theorem rationalRoundedScaledCharge_eq (Z : ℕ) (q : ℚ) :
    rationalRoundedScaledCharge Z q = roundedScaledCharge Z (q : ℝ) := by
  simp only [rationalRoundedScaledCharge, roundedScaledCharge,
    ← Rat.cast_natCast (α := ℝ) Z, ← Rat.cast_mul, Rat.round_cast]

theorem roundedScaledCharge_pos {Z : ℕ} {q : ℝ} (hscale : 1 ≤ (Z : ℝ) * q) :
    0 < roundedScaledCharge Z q := by
  have h := (abs_le.mp (abs_sub_round ((Z : ℝ) * q))).2
  have hr : (0 : ℝ) < (round ((Z : ℝ) * q) : ℝ) := by linarith
  have hrInt : (0 : ℤ) < round ((Z : ℝ) * q) := by exact_mod_cast hr
  exact Int.pos_iff_toNat_pos.mp hrInt

/-- Rounding the physical charge first incurs only inverse-amplification
error in the dilated one-particle potential. -/
theorem roundedScaledCharge_error {Z : ℕ} (hZ : 0 < Z) {q : ℝ}
    (hscale : 1 ≤ (Z : ℝ) * q) :
    |(roundedScaledCharge Z q : ℝ) / (Z : ℝ) - q| ≤ 1 / (2 * (Z : ℝ)) := by
  have hz : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hr : (0 : ℤ) ≤ round ((Z : ℝ) * q) := by
    have h := (abs_le.mp (abs_sub_round ((Z : ℝ) * q))).2
    have hreal : (0 : ℝ) ≤ (round ((Z : ℝ) * q) : ℝ) := by linarith
    exact_mod_cast hreal
  have hcast : (roundedScaledCharge Z q : ℝ) = (round ((Z : ℝ) * q) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  have heq : (roundedScaledCharge Z q : ℝ) / (Z : ℝ) - q =
      ((round ((Z : ℝ) * q) : ℝ) - (Z : ℝ) * q) / (Z : ℝ) := by
    rw [hcast]
    field_simp
  rw [heq, abs_div, abs_of_pos hz]
  have h : |(round ((Z : ℝ) * q) : ℝ) - (Z : ℝ) * q| ≤ (1 / 2 : ℝ) := by
    simpa only [abs_sub_comm] using abs_sub_round ((Z : ℝ) * q)
  have hdiv := div_le_div_of_nonneg_right h hz.le
  convert hdiv using 1
  ring

end ContinuumCoulomb

end OAI
