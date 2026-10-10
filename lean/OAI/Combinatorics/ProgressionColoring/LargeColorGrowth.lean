import OAI.Combinatorics.ProgressionColoring.LargeColor
import OAI.Combinatorics.ProgressionColoring.UpperBound
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI

namespace QuantitativeVanDerWaerden
namespace LargeColor

/-- The ambient color count is bounded by a convenient quartic expression. -/
theorem color_count_le_quartic {b s : ℕ} (hb : 1 ≤ b) :
    2 ^ s * (s * (b - 1) ^ 2 + 1) ≤ (2 ^ s) ^ 2 * b ^ 2 := by
  have hp : (b - 1) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (Nat.sub_le b 1) 2
  have hsq : 1 ≤ b ^ 2 := by simpa using Nat.pow_le_pow_left hb 2
  have hs : s + 1 ≤ 2 ^ s := Nat.succ_le_of_lt (Nat.lt_two_pow_self : s < 2 ^ s)
  calc
    _ ≤ 2 ^ s * ((s + 1) * b ^ 2) := by
      apply Nat.mul_le_mul_left
      have hmul := Nat.mul_le_mul_left s hp
      nlinarith
    _ ≤ 2 ^ s * (2 ^ s * b ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs)
    _ = _ := by ring

noncomputable def base (r : ℕ) : ℕ := ⌊Real.exp (Real.log (r : ℝ) / 4)⌋₊

noncomputable def dimension (r : ℕ) : ℕ := ⌊Real.log (r : ℝ) / (4 * Real.log 2)⌋₊

theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hn' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hn
  have hlt := Nat.lt_floor_add_one x
  linarith

theorem log_large {r : ℕ} (hr : 256 ≤ r) :
    8 * Real.log 2 ≤ Real.log (r : ℝ) := by
  calc
    _ = Real.log ((2 : ℝ) ^ 8) := by rw [Real.log_pow]; norm_num
    _ ≤ Real.log (r : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hr)

theorem base_le_exp (r : ℕ) :
    (base r : ℝ) ≤ Real.exp (Real.log (r : ℝ) / 4) :=
  Nat.floor_le (Real.exp_pos _).le

theorem base_ge_two {r : ℕ} (hr : 256 ≤ r) : 2 ≤ base r := by
  apply Nat.le_floor
  apply (Real.log_le_iff_le_exp (by norm_num : 0 < (2 : ℝ))).mp
  have hlog := log_large hr
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem dimension_argument_ge_one {r : ℕ} (hr : 256 ≤ r) :
    1 ≤ Real.log (r : ℝ) / (4 * Real.log 2) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log 2)).mpr
  have hlog := log_large hr
  linarith

theorem two_pow_dimension_le {r : ℕ} (hr : 256 ≤ r) :
    (2 : ℝ) ^ dimension r ≤ Real.exp (Real.log (r : ℝ) / 4) := by
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_pow]
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (dimension r : ℝ) ≤ Real.log (r : ℝ) / (4 * Real.log 2) :=
    Nat.floor_le (by linarith [dimension_argument_ge_one hr])
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * Real.log 2)).mp hs
  nlinarith

theorem parameter_color_count {r : ℕ} (hr : 256 ≤ r) :
    2 ^ dimension r * (dimension r * (base r - 1) ^ 2 + 1) ≤ r := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hfour : Real.exp (Real.log (r : ℝ) / 4) ^ 4 = (r : ℝ) := by
    rw [← Real.exp_nat_mul]
    convert Real.exp_log hrpos using 1
    congr 1
    ring
  have hquart : ((2 : ℝ) ^ dimension r) ^ 2 * (base r : ℝ) ^ 2 ≤ (r : ℝ) := by
    calc
      _ ≤ Real.exp (Real.log (r : ℝ) / 4) ^ 2 *
          Real.exp (Real.log (r : ℝ) / 4) ^ 2 := by
        gcongr
        · exact two_pow_dimension_le hr
        · exact base_le_exp r
      _ = Real.exp (Real.log (r : ℝ) / 4) ^ 4 := by ring
      _ = (r : ℝ) := hfour
  have hnat : (2 ^ dimension r) ^ 2 * base r ^ 2 ≤ r := by exact_mod_cast hquart
  exact (color_count_le_quartic (b := base r) (s := dimension r)
    (by have := base_ge_two hr; omega)).trans hnat

theorem dimension_lower {r : ℕ} (hr : 256 ≤ r) :
    Real.log (r : ℝ) / (8 * Real.log 2) ≤ (dimension r : ℝ) := by
  have htwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  calc
    _ = (Real.log (r : ℝ) / (4 * Real.log 2)) / 2 := by
      field_simp [htwo]
      ring
    _ ≤ (dimension r : ℝ) := half_le_floor (dimension_argument_ge_one hr)

theorem log_base_lower {r : ℕ} (hr : 256 ≤ r) :
    Real.log (r : ℝ) / 8 ≤ Real.log (base r : ℝ) := by
  have hb : (2 : ℝ) ≤ (base r : ℝ) := by exact_mod_cast base_ge_two hr
  have ht : 1 ≤ Real.exp (Real.log (r : ℝ) / 4) := by linarith [base_le_exp r]
  have hhalf : Real.exp (Real.log (r : ℝ) / 4) / 2 ≤ (base r : ℝ) :=
    half_le_floor ht
  have hlog := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  linarith [log_large hr]

theorem parameter_size {r : ℕ} (hr : 256 ≤ r) :
    Real.exp ((Real.log (r : ℝ)) ^ 2 / (64 * Real.log 2)) ≤
      ((base r ^ dimension r : ℕ) : ℝ) := by
  have hb : 0 < (base r : ℝ) := by exact_mod_cast (by have := base_ge_two hr; omega : 0 < base r)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  rw [Nat.cast_pow]
  apply (Real.le_log_iff_exp_le (pow_pos hb _)).mp
  rw [Real.log_pow]
  calc
    _ = (Real.log (r : ℝ) / (8 * Real.log 2)) * (Real.log (r : ℝ) / 8) := by
      field_simp
      ring
    _ ≤ (dimension r : ℝ) * Real.log (base r : ℝ) :=
      mul_le_mul (dimension_lower hr) (log_base_lower hr) (by positivity) (by positivity)

theorem exp_bound {r k : ℕ} (hr : 256 ≤ r) (hk : 3 ≤ k) :
    Real.exp ((Real.log (r : ℝ)) ^ 2 / (64 * Real.log 2)) < (W r k : ℝ) := by
  have hnat : base r ^ dimension r < W r k :=
    pow_lt_W (base_ge_two hr) hk (parameter_color_count hr)
      (finite_ramsey (by omega) (by omega))
  exact (parameter_size hr).trans_lt (by exact_mod_cast hnat)

end LargeColor
end QuantitativeVanDerWaerden

end OAI
