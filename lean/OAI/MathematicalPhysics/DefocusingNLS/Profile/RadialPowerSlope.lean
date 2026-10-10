import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! The positive polynomial divided difference in the scalar comparison equation. -/

open Finset
namespace DefocusingNLS

def radialPowerSlope (p : ℕ) (x y : ℝ) : ℝ :=
  ∑ i ∈ range p, x^i*y^(p-1-i)

theorem radialPowerSlope_identity (p : ℕ) (x y : ℝ) :
    radialPowerSlope p x y*(x-y)=x^p-y^p := geom_sum₂_mul x y p

theorem radialPowerSlope_nonneg (p : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ radialPowerSlope p x y := by
  apply sum_nonneg
  intro i _
  exact mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)

theorem radialPowerSlope_lower (p : ℕ) (b x y : ℝ)
    (hb : 0 ≤ b) (hx : b ≤ x) (hy : b ≤ y) :
    (p : ℝ)*b^(p-1) ≤ radialPowerSlope p x y := by
  have he : (p : ℝ)*b^(p-1)=∑ _i ∈ range p, b^(p-1) := by simp
  rw [he]
  apply sum_le_sum
  intro i hi
  have hi' : i ≤ p-1 := by have := mem_range.1 hi; omega
  calc
    b^(p-1)=b^i*b^(p-1-i) := by rw [← pow_add]; congr 1; omega
    _ ≤ x^i*y^(p-1-i) := mul_le_mul (pow_le_pow_left₀ hb hx _) (pow_le_pow_left₀ hb hy _)
      (pow_nonneg hb _) (pow_nonneg (hb.trans hx) _)

end DefocusingNLS

end OAI
