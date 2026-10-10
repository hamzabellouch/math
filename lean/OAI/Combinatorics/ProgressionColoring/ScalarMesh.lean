import OAI.Combinatorics.ProgressionColoring.Parameters
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem scalar_log_prime_slack {k : ℕ} (hk : 2 ≤ k) :
    Real.log (2 * (k : ℝ) ^ 2) ≤ 3 * Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hl : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hk0.ne'), Real.log_pow]
  norm_num
  linarith

theorem scalar_dimension_le_two_mul {k : ℕ} (hk : 1 ≤ k) :
    (dimension k : ℝ) ≤ 2 * k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (k : ℝ) ^ (1 / 10 : ℝ) ≤ k := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hkR (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have := dimension_upper hk
  linarith

/-- The dimension cancels nine tenths of a power of the progression length. -/
theorem scalar_nat_le_dimension_rpow {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ≤ dimension k * (k : ℝ) ^ (9 / 10 : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  calc
    (k : ℝ) = (k : ℝ) ^ (1 / 10 : ℝ) * (k : ℝ) ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hk0]
      norm_num
    _ ≤ dimension k * (k : ℝ) ^ (9 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right (dimension_lower k) (Real.rpow_nonneg hk0.le _)

/-- A bound uniform over every prime power permitted by the construction. -/
theorem scalar_log_q_le {k q : ℕ} (hk : 2 ≤ k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    Real.log q ≤ 4 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hDpos : (0 : ℝ) < dimension k := Nat.cast_pos.mpr (dimension_pos hk1)
  have hL : 0 ≤ Real.log k := Real.log_nonneg hkR
  have hP : 1 ≤ (k : ℝ) ^ (9 / 10 : ℝ) :=
    Real.one_le_rpow hkR (by norm_num)
  have hDP := scalar_nat_le_dimension_rpow hk1
  have hDPlow : (dimension k : ℝ) ≤ dimension k * (k : ℝ) ^ (9 / 10 : ℝ) :=
    le_mul_of_one_le_right hDpos.le hP
  have hc : c ≤ 1 := by norm_num [c]
  have hfirst : c * k * Real.log k ≤
      (dimension k * (k : ℝ) ^ (9 / 10 : ℝ)) * Real.log k := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact (mul_le_of_le_one_left (Nat.cast_nonneg k) hc).trans hDP
  have hsecond : (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
      3 * (dimension k * (k : ℝ) ^ (9 / 10 : ℝ)) * Real.log k := by
    calc
      (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
          dimension k * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_left (scalar_log_prime_slack hk) hDpos.le
      _ ≤ (dimension k * (k : ℝ) ^ (9 / 10 : ℝ)) * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_right hDPlow (by positivity)
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hDpos).mp
  nlinarith

/-- The logarithmic size of the inverse small-cell offset. -/
theorem scalar_dimension_log_q_le {k q : ℕ} (hk : 2 ≤ k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    ((dimension k : ℝ) + 1) * Real.log q ≤ 13 * k * Real.log k := by
  have hk1 : 1 ≤ k := by omega
  have hD1 : (1 : ℝ) ≤ dimension k := by
    exact_mod_cast (show 1 ≤ dimension k by have := dimension_pos hk1; omega)
  have hD0 : (0 : ℝ) ≤ dimension k := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hqL : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hslack : (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
      6 * k * Real.log k := by
    calc
      (dimension k : ℝ) * Real.log (2 * (k : ℝ) ^ 2) ≤
          dimension k * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_left (scalar_log_prime_slack hk) hD0
      _ ≤ (2 * k) * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_right (scalar_dimension_le_two_mul hk1) (by positivity)
      _ = _ := by ring
  have hc : c ≤ (1 / 2 : ℝ) := by norm_num [c]
  have hck : c * k * Real.log k ≤ (1 / 2 : ℝ) * k * Real.log k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg k)) hL
  have hdup : ((dimension k : ℝ) + 1) * Real.log q ≤
      (2 * dimension k) * Real.log q :=
    mul_le_mul_of_nonneg_right (by linarith) hqL
  nlinarith

/-- The actual offset `q^(-(D+1))`, written using a natural power. -/
def scalarAlpha (k q : ℕ) : ℝ := 1 / (q : ℝ) ^ (dimension k + 1)

/-- The logarithmic radius of the exponential mesh. -/
def scalarRadius (k q : ℕ) : ℝ := Real.log (1 + 1 / (2 * scalarAlpha k q))

/-- The actual number of positive radial mesh intervals. -/
def scalarMeshSize (k q : ℕ) : ℕ := ⌈(k : ℝ) ^ 2 * scalarRadius k q⌉₊

theorem scalar_q_power_ge_four {k q : ℕ} (hk : 1 ≤ k) (hq : 2 ≤ q) :
    (4 : ℝ) ≤ (q : ℝ) ^ (dimension k + 1) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hD := dimension_pos hk
  calc
    (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    _ ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hq2 2
    _ ≤ (q : ℝ) ^ (dimension k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)

theorem scalarAlpha_pos {k q : ℕ} (hq : 2 ≤ q) : 0 < scalarAlpha k q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  unfold scalarAlpha
  positivity

theorem scalarAlpha_le_quarter {k q : ℕ} (hk : 1 ≤ k) (hq : 2 ≤ q) :
    scalarAlpha k q ≤ (1 / 4 : ℝ) :=
  one_div_le_one_div_of_le (by norm_num) (scalar_q_power_ge_four hk hq)

theorem scalarRadius_pos {k q : ℕ} (hq : 2 ≤ q) : 0 < scalarRadius k q := by
  have ha := scalarAlpha_pos (k := k) hq
  apply Real.log_pos
  have : 0 < (1 : ℝ) / (2 * scalarAlpha k q) := by positivity
  linarith

/-- The mesh logarithmic radius is at most the logarithm of its denominator. -/
theorem scalarRadius_le_dimension_log_q {k q : ℕ}
    (hk : 1 ≤ k) (hq : 2 ≤ q) :
    scalarRadius k q ≤ ((dimension k : ℝ) + 1) * Real.log q := by
  have hp4 := scalar_q_power_ge_four hk hq
  have he : (1 : ℝ) / (2 * scalarAlpha k q) =
      (q : ℝ) ^ (dimension k + 1) / 2 := by
    simp [scalarAlpha, div_eq_mul_inv, mul_inv_rev]
  unfold scalarRadius
  rw [he]
  calc
    Real.log (1 + (q : ℝ) ^ (dimension k + 1) / 2) ≤
        Real.log ((q : ℝ) ^ (dimension k + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    _ = ((dimension k : ℝ) + 1) * Real.log q := by
      simp only [Real.log_pow, Nat.cast_add, Nat.cast_one]

/-- Explicit logarithmic radius bound for every admissible prime-power choice. -/
theorem scalarRadius_le {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    scalarRadius k q ≤ 13 * k * Real.log k :=
  (scalarRadius_le_dimension_log_q (by omega) hq).trans
    (scalar_dimension_log_q_le hk hqlog)

/-- An explicit bound on the number of labels in the signed radial mesh. -/
theorem scalarMeshSize_upper {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q)
    (hlog : 1 ≤ Real.log k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    2 * (scalarMeshSize k q : ℝ) ≤ 28 * (k : ℝ) ^ 3 * Real.log k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hRpos := scalarRadius_pos (k := k) hq
  have hceil : (scalarMeshSize k q : ℝ) <
      (k : ℝ) ^ 2 * scalarRadius k q + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg _) hRpos.le)
  have hR := scalarRadius_le hk hq hqlog
  have hradial : (k : ℝ) ^ 2 * scalarRadius k q ≤
      13 * (k : ℝ) ^ 3 * Real.log k := by
    calc
      (k : ℝ) ^ 2 * scalarRadius k q ≤ (k : ℝ) ^ 2 * (13 * k * Real.log k) :=
        mul_le_mul_of_nonneg_left hR (sq_nonneg _)
      _ = _ := by ring
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkR
  have hmass : (1 : ℝ) ≤ (k : ℝ) ^ 3 * Real.log k :=
    one_le_mul_of_one_le_of_one_le hk3 hlog
  nlinarith

end QuantitativeVanDerWaerden.Parameters

end

end OAI
