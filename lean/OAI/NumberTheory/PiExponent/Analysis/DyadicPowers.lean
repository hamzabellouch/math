import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace PiExponent

 theorem dyadic_block_bound_algebra {c K nu : ℝ} (hc : 0 < c) (hK : 0 < K) :
    4 / (K ^ 3 * (c * (2 * K) ^ (1 - nu)) ^ 2) =
      (4 / (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu)))) * K ^ (2 * nu - 5) := by
  have hsq (x : ℝ) (hx : 0 ≤ x) :
      (x ^ (1 - nu)) ^ (2 : ℕ) = x ^ (2 * (1 - nu)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  have hprod : K ^ (3 : ℕ) * K ^ (2 * (1 - nu)) = K ^ (5 - 2 * nu) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hK]
    congr 1
    ring
  have hden : K ^ 3 * (c * (2 * K) ^ (1 - nu)) ^ 2 =
      (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu))) * K ^ (5 - 2 * nu) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hK.le, mul_pow, mul_pow,
      hsq 2 (by norm_num), hsq K hK.le]
    calc
      _ = (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu))) *
          (K ^ 3 * K ^ (2 * (1 - nu))) := by ring
      _ = _ := by rw [hprod]
  have hcoeff : c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu)) ≠ 0 :=
    (mul_pos (pow_pos hc 2) (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hKpow : K ^ (5 - 2 * nu) ≠ 0 := (Real.rpow_pos_of_pos hK _).ne'
  rw [hden]
  apply (div_eq_iff (mul_ne_zero hcoeff hKpow)).2
  rw [mul_mul_mul_comm, div_mul_cancel₀ _ hcoeff, ← Real.rpow_add hK]
  have hexponent : 2 * nu - 5 + (5 - 2 * nu) = 0 := by ring
  rw [hexponent, Real.rpow_zero, mul_one]

 theorem dyadic_rpow_eq_geometric (nu : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (2 * nu - 5) = ((2 : ℝ) ^ (2 * nu - 5)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

 theorem dyadic_geometric_ratio_pos (nu : ℝ) :
    0 < (2 : ℝ) ^ (2 * nu - 5) := Real.rpow_pos_of_pos (by norm_num) _

 theorem dyadic_geometric_ratio_lt_one {nu : ℝ} (hnu : nu < 5 / 2) :
    (2 : ℝ) ^ (2 * nu - 5) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · norm_num
  · linarith

 theorem summable_dyadic_block_bound {c nu : ℝ} (hc : 0 < c) (hnu : nu < 5 / 2) :
    Summable (fun k : ℕ =>
      4 / (((2 : ℝ) ^ k) ^ (3 : ℕ) *
        (c * (2 * (2 : ℝ) ^ k) ^ (1 - nu)) ^ (2 : ℕ))) := by
  have hg := summable_geometric_of_lt_one (dyadic_geometric_ratio_pos nu).le
    (dyadic_geometric_ratio_lt_one hnu)
  have hm := hg.mul_left (4 / (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu))))
  apply hm.congr
  intro k
  rw [dyadic_block_bound_algebra hc (pow_pos (by norm_num) k),
    dyadic_rpow_eq_geometric]

end PiExponent

end OAI
