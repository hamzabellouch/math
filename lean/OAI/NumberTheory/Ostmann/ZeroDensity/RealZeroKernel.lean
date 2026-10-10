import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Comparing the real parts of zero contributions at two real points -/

namespace Ostmann

noncomputable def realZeroKernel (a y : ℝ) : ℝ := a / (a ^ 2 + y ^ 2)

theorem realZeroKernel_nonneg {a y : ℝ} (ha : 0 ≤ a) : 0 ≤ realZeroKernel a y :=
  div_nonneg ha (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem realZeroKernel_complex (s : ℝ) (ρ : ℂ) :
    ((s : ℂ) - ρ)⁻¹.re = realZeroKernel (s - ρ.re) ρ.im := by
  rw [Complex.inv_re]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.normSq_apply,
    Complex.sub_im, Complex.ofReal_im, zero_sub, neg_mul_neg, realZeroKernel, pow_two]

/-- The universal ratio bound used for zeros near the real axis. -/
theorem realZeroKernel_ratio {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    realZeroKernel a y ≤ (b / a) * realZeroKernel b y := by
  have hb : 0 < b := ha.trans_le hab
  have hda : 0 < a ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg y)
  have hdb : 0 < b ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg y)
  have hs : 0 ≤ (b ^ 2 - a ^ 2) * y ^ 2 := by
    apply mul_nonneg _ (sq_nonneg y)
    nlinarith
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_div_iff₀ hda hdb]
  apply (mul_le_mul_iff_left₀ ha).mp
  field_simp
  nlinarith

/-- At imaginary height at least one, bounded real parts give an absolute
constant independent of the zero-free region. -/
theorem realZeroKernel_high {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 2) (hy : 1 ≤ y ^ 2) :
    realZeroKernel a y ≤ 5 * realZeroKernel b y := by
  have hb0 : 0 < b := ha.trans_le hab
  have hda : 0 < a ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg y)
  have hdb : 0 < b ^ 2 + y ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb0) (sq_nonneg y)
  have hd : b ^ 2 + y ^ 2 ≤ 5 * (a ^ 2 + y ^ 2) := by nlinarith [sq_nonneg a]
  have h1 := mul_le_mul_of_nonneg_right hab hdb.le
  have h2 := mul_le_mul_of_nonneg_left hd hb0.le
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_div_iff₀ hda hdb]
  nlinarith

theorem realZeroKernel_gap {a b y c δ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hgap : b - a ≤ δ) (hregion : c * δ ≤ a) :
    realZeroKernel a y ≤ (1 + c⁻¹) * realZeroKernel b y := by
  have hδ : δ / a ≤ 1 / c := by
    apply (div_le_div_iff₀ ha hc).mpr
    nlinarith
  have hratio : b / a ≤ 1 + c⁻¹ := by
    have hg := div_le_div_of_nonneg_right (show b ≤ a + δ by linarith) ha.le
    rw [add_div, div_self ha.ne'] at hg
    exact hg.trans (by simpa only [one_div] using add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hδ)
  exact (realZeroKernel_ratio ha hab).trans
    (mul_le_mul_of_nonneg_right hratio (realZeroKernel_nonneg (ha.le.trans hab)))

end Ostmann

end OAI
