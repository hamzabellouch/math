import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

def c : ℝ := 1 / 100000
def dimension (k : ℕ) : ℕ := ⌈(k : ℝ) ^ (1 / 10 : ℝ)⌉₊
def cutoff (k : ℕ) : ℕ := ⌈(k : ℝ) ^ (1 / 2 : ℝ)⌉₊
def flipProbability (k : ℕ) : ℝ := (k : ℝ) ^ (-1 / 20 : ℝ)
def meshScale (k : ℕ) : ℝ := 1 / (k : ℝ) ^ 2
def cutScale (k : ℕ) : ℝ := 1 / (1000 * (dimension k : ℝ))

theorem c_pos : 0 < c := by norm_num [c]

theorem rich_coefficient :
    2 * c - (1 / 100 : ℝ) / 80 = -(21 / 200000 : ℝ) := by
  norm_num [c]

theorem dimension_lower (k : ℕ) :
    (k : ℝ) ^ (1 / 10 : ℝ) ≤ (dimension k : ℝ) := Nat.le_ceil _

theorem cutoff_lower (k : ℕ) :
    (k : ℝ) ^ (1 / 2 : ℝ) ≤ (cutoff k : ℝ) := Nat.le_ceil _

theorem dimension_upper {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 10 : ℝ) := by
  have hceil : (dimension k : ℝ) < (k : ℝ) ^ (1 / 10 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have : 1 ≤ (k : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  linarith

theorem cutoff_upper {k : ℕ} (hk : 1 ≤ k) :
    (cutoff k : ℝ) ≤ 2 * (k : ℝ) ^ (1 / 2 : ℝ) := by
  have hceil : (cutoff k : ℝ) < (k : ℝ) ^ (1 / 2 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have : 1 ≤ (k : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  linarith

theorem dimension_pos {k : ℕ} (hk : 1 ≤ k) : 0 < dimension k := by
  have h : 1 ≤ (k : ℝ) ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have := dimension_lower k
  exact_mod_cast (show (0 : ℝ) < dimension k by linarith)

theorem cutoff_pos {k : ℕ} (hk : 1 ≤ k) : 0 < cutoff k := by
  have h : 1 ≤ (k : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have := cutoff_lower k
  exact_mod_cast (show (0 : ℝ) < cutoff k by linarith)

theorem dimension_sq_lower (k : ℕ) :
    (k : ℝ) ^ (1 / 5 : ℝ) ≤ (dimension k : ℝ) ^ 2 := by
  have hp := Real.rpow_nonneg (Nat.cast_nonneg k) (1 / 10 : ℝ)
  have hh := dimension_lower k
  have he : ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 2 = (k : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  nlinarith

theorem dimension_sq_upper {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ (1 / 5 : ℝ) := by
  have hp := Real.rpow_nonneg (Nat.cast_nonneg k) (1 / 10 : ℝ)
  have hh := dimension_upper hk
  have he : ((k : ℝ) ^ (1 / 10 : ℝ)) ^ 2 = (k : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
    norm_num
  have hd : (0 : ℝ) ≤ dimension k := Nat.cast_nonneg _
  nlinarith

theorem dimension_cutoff_upper {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) * cutoff k ≤ 4 * (k : ℝ) ^ (3 / 5 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    (dimension k : ℝ) * cutoff k ≤
        (2 * (k : ℝ) ^ (1 / 10 : ℝ)) * (2 * (k : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul (dimension_upper hk) (cutoff_upper hk)
        (Nat.cast_nonneg _) (by positivity)
    _ = 4 * ((k : ℝ) ^ (1 / 10 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ = 4 * (k : ℝ) ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_add hk0]
      norm_num

theorem flipProbability_pos {k : ℕ} (hk : 0 < k) : 0 < flipProbability k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hk) _

theorem flip_mass {k : ℕ} (hk : 0 < k) :
    flipProbability k * k = (k : ℝ) ^ (19 / 20 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  change (k : ℝ) ^ (-1 / 20 : ℝ) * k = _
  nth_rw 2 [← Real.rpow_one (k : ℝ)]
  rw [← Real.rpow_add hk0]
  norm_num

theorem meshScale_pos {k : ℕ} (hk : 0 < k) : 0 < meshScale k := by
  unfold meshScale
  positivity

theorem cutScale_pos {k : ℕ} (hk : 1 ≤ k) : 0 < cutScale k := by
  have := dimension_pos hk
  unfold cutScale
  positivity

end QuantitativeVanDerWaerden.Parameters

end

end OAI
