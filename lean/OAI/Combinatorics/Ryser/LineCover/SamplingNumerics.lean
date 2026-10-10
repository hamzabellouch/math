import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace RyserCoveringCounterexample.LineCover

theorem half_pow_le_descFactorial (n k : ℕ) (h : 2 * k ≤ n) :
    ((n : ℝ) / 2) ^ k ≤ (n.descFactorial k : ℝ) := by
  have hk : k ≤ n := (Nat.le_mul_of_pos_left k (by decide : 0 < 2)).trans h
  have hkn : k ≤ n + 1 := hk.trans (Nat.le_succ n)
  have hr : (2 : ℝ) * k ≤ n := by exact_mod_cast h
  have hbase : (n : ℝ) / 2 ≤ ((n + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
    linarith
  calc
    ((n : ℝ) / 2) ^ k ≤ (((n + 1 - k : ℕ) : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ (n.descFactorial k : ℝ) := by
      exact_mod_cast Nat.pow_sub_le_descFactorial n k

theorem descFactorial_cast_pos (n k : ℕ) (h : k ≤ n) :
    0 < (n.descFactorial k : ℝ) := by
  exact_mod_cast (Nat.descFactorial_pos.mpr h)

theorem low_occupancy_quotient_le (m D R t h : ℕ)
    (hm : 0 < m) (hlarge : 4 * h ≤ m) :
    (t : ℝ) ^ (2 * h) * ((m : ℝ) * D * R) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤
      (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : ((m : ℝ) / 2) ^ (2 * h) ≤ (m.descFactorial (2 * h) : ℝ) :=
    half_pow_le_descFactorial m (2 * h) (by simpa only [← Nat.mul_assoc] using hlarge)
  have hpos : 0 < ((m : ℝ) / 2) ^ (2 * h) := by positivity
  calc
    _ ≤ (t : ℝ) ^ (2 * h) * ((m : ℝ) * D * R) ^ h /
        (((m : ℝ) / 2) ^ (2 * h)) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = ((t : ℝ) ^ 2 * ((m : ℝ) * D * R) / ((m : ℝ) / 2) ^ 2) ^ h := by
      simp only [div_pow, mul_pow, pow_mul]
    _ = _ := by
      congr 1
      field_simp
      ring

theorem high_occupancy_quotient_le (R N D t h : ℕ)
    (hR : 0 < R) (hN : 0 < N) (hRlarge : 2 * h ≤ R) (hNlarge : 2 * h ≤ N) :
    (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : ((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h ≤
      (R.descFactorial h : ℝ) * (N.descFactorial h : ℝ) :=
    mul_le_mul (half_pow_le_descFactorial R h hRlarge)
      (half_pow_le_descFactorial N h hNlarge) (by positivity) (by positivity)
  have hpos : 0 < ((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h := by positivity
  calc
    _ ≤ (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h /
        (((R : ℝ) / 2) ^ h * ((N : ℝ) / 2) ^ h) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = ((t : ℝ) ^ 2 * ((D : ℝ) * N) / (((R : ℝ) / 2) * ((N : ℝ) / 2))) ^ h := by
      simp only [div_pow, mul_pow, pow_mul]
    _ = _ := by
      congr 1
      field_simp
      ring

theorem low_occupancy_exponent_neg (D : ℕ) (κ : ℝ) (hκ : κ < 1 / 10) :
    (D : ℝ) - 10 * ((D : ℝ) + 1) * (1 / 2 - κ / 4) < 0 := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_pos (by linarith : 0 < (D : ℝ) + 1)
    (sub_pos.mpr hκ)
  nlinarith

theorem high_occupancy_exponent_neg (D : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    (D : ℝ) - 10 * ((D : ℝ) + 1) * (1 / 2 + κ / 4) < 0 := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_pos (by linarith : 0 < (D : ℝ) + 1) hκ
  nlinarith

end RyserCoveringCounterexample.LineCover

end OAI
