import OAI.MeasureTheory.Falconer.Incidence.RadialBlockDepths
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! # Concrete near-pin radii for the reserved-block dyadic geometry -/

namespace Falconer

theorem reserved_block_freezing {d A q s : ℝ} (hd : 1 ≤ d) (hA : 0 < A)
    (hq : 0 < q) (hq1 : q ≤ 1) (hs : 0 < s) (hscale : s ≤ A*q^2) :
    Real.sqrt d*s < 8*d*A*q ∧
      8*(Real.sqrt d*s)^2/(8*d*A*q) ≤ s*q := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hr : 0 < 8*d*A*q := by positivity
  have hsq : q^2 ≤ q := by nlinarith
  have hb : s ≤ A*q := hscale.trans (mul_le_mul_of_nonneg_left hsq hA.le)
  constructor
  · have hroot : Real.sqrt d ≤ d := by
      nlinarith [Real.sq_sqrt hd0.le,Real.sqrt_nonneg d]
    have he : Real.sqrt d*s ≤ d*A*q := by
      calc
        _ ≤ d*s := mul_le_mul_of_nonneg_right hroot hs.le
        _ ≤ d*(A*q) := mul_le_mul_of_nonneg_left hb hd0.le
        _ = _ := by ring
    have hh : 0 < d*A*q := by positivity
    linarith
  · apply (div_le_iff₀ hr).mpr
    calc
      8*(Real.sqrt d*s)^2 = (8*d*s)*s := by
        rw [mul_pow,Real.sq_sqrt hd0.le]
        ring
      _ ≤ (8*d*s)*(A*q^2) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (s*q)*(8*d*A*q) := by ring

theorem dyadic_reserved_block_freezing {d : ℕ} (hd : 0 < d)
    {A : ℝ} (hA : 0 < A) {a b : ℕ} (hab : 2*b ≤ a) :
    Real.sqrt d*(A/(2:ℝ)^a) < 8*(d:ℝ)*A/(2:ℝ)^b ∧
      8*(Real.sqrt d*(A/(2:ℝ)^a))^2/(8*(d:ℝ)*A/(2:ℝ)^b) ≤ A/(2:ℝ)^(a+b) := by
  let q : ℝ := ((2:ℝ)^b)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hscale : A/(2:ℝ)^a ≤ A*q^2 := by
    have hh : A/(2:ℝ)^a ≤ A/(2:ℝ)^(2*b) :=
      div_le_div_of_nonneg_left hA.le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hab)
    have he : (2:ℝ)^(2*b) = ((2:ℝ)^b)^2 := by rw [Nat.mul_comm 2 b,pow_mul]
    simpa only [q,he,div_eq_mul_inv,inv_pow] using hh
  have hh := reserved_block_freezing (by exact_mod_cast hd : (1:ℝ) ≤ d)
    hA hq hq1 (show 0 < A/(2:ℝ)^a by positivity) hscale
  have he : (A/(2:ℝ)^a)*q = A/(2:ℝ)^(a+b) := by
    simp only [q,pow_add,div_eq_mul_inv,mul_inv_rev]
    ring
  simpa only [q,← div_eq_mul_inv,he] using hh

end Falconer

end OAI
