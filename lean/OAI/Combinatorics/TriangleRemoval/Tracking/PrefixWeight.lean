import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

def prefixWeight (w : ℕ → ℝ) (t : ℕ) : ℝ := ∑ i ∈ Finset.range t, w i

def orderedWeight (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, t => ∑ i ∈ Finset.range t, w i * orderedWeight w j i

@[simp] theorem prefixWeight_zero (w : ℕ → ℝ) : prefixWeight w 0 = 0 := by
  simp [prefixWeight]

@[simp] theorem prefixWeight_succ (w : ℕ → ℝ) (t : ℕ) :
    prefixWeight w (t + 1) = prefixWeight w t + w t := Finset.sum_range_succ _ _

theorem prefixWeight_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (t : ℕ) :
    0 ≤ prefixWeight w t := Finset.sum_nonneg (fun i _ => hw i)

theorem orderedWeight_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j t : ℕ) :
    0 ≤ orderedWeight w j t := by
  induction j generalizing t with
  | zero => exact zero_le_one
  | succ j ih => exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (ih i))

theorem power_increment_lower (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) * y * x ^ j ≤ (x + y) ^ (j + 1) - x ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hx
    have hpow := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx (le_add_of_nonneg_right hy) (j + 1)) hy
    simp only [Nat.cast_add, Nat.cast_one] at ih hmul ⊢
    rw [pow_succ (x + y) (j + 1), pow_succ x (j + 1)]
    rw [pow_succ x j] at hpow hmul ⊢
    nlinarith

theorem orderedWeight_factorial {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j t : ℕ) :
    (j.factorial : ℝ) * orderedWeight w j t ≤ prefixWeight w t ^ j := by
  induction j generalizing t with
  | zero => simp [orderedWeight]
  | succ j ih =>
    rw [orderedWeight, Nat.factorial_succ, Nat.cast_mul, Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ Finset.range t,
          ((j + 1 : ℕ) : ℝ) * w i * prefixWeight w i ^ j := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_le_mul_of_nonneg_left (ih i)
          (mul_nonneg (Nat.cast_nonneg (j + 1)) (hw i))
        convert hh using 1; ring
      _ ≤ ∑ i ∈ Finset.range t,
          (prefixWeight w (i + 1) ^ (j + 1) - prefixWeight w i ^ (j + 1)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [prefixWeight_succ]
        exact power_increment_lower _ _ (prefixWeight_nonneg hw i) (hw i) j
      _ = prefixWeight w t ^ (j + 1) := by
        rw [Finset.sum_range_sub (fun i => prefixWeight w i ^ (j + 1))]
        simp

theorem orderedWeight_le {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j t : ℕ) :
    orderedWeight w j t ≤ prefixWeight w t ^ j / (j.factorial : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos j))).mpr
  simpa only [mul_comm] using orderedWeight_factorial hw j t

theorem three_segment_weight_le {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h a b t : ℕ) :
    orderedWeight w h t * orderedWeight w a t * orderedWeight w b t ≤
      prefixWeight w t ^ (h + a + b) /
        ((h.factorial : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ)) := by
  have hh := orderedWeight_le hw h t
  have ha := orderedWeight_le hw a t
  have hb := orderedWeight_le hw b t
  have hp := mul_le_mul hh ha (orderedWeight_nonneg hw a t)
    (div_nonneg (pow_nonneg (prefixWeight_nonneg hw t) _) (Nat.cast_nonneg _))
  have hp' := mul_le_mul hp hb (orderedWeight_nonneg hw b t)
    (mul_nonneg
      (div_nonneg (pow_nonneg (prefixWeight_nonneg hw t) _) (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg (prefixWeight_nonneg hw t) _) (Nat.cast_nonneg _)))
  calc
    _ ≤ _ := hp'
    _ = _ := by rw [pow_add, pow_add, div_mul_div_comm, div_mul_div_comm]

end SharpTerminalLeave

end

end OAI
