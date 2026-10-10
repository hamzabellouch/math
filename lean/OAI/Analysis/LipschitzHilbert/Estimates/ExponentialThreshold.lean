import OAI.Analysis.LipschitzHilbert.Estimates.MomentSuperlevel
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! Select the moment order explicitly to absorb a positive global
prefactor into the prescribed exponential exceptional-area budget. -/

noncomputable section

namespace LipschitzHilbert

theorem quarter_ceil_bound (x : ℝ) :
    (1/4:ℝ)^⌈x / Real.log 4⌉₊ ≤ Real.exp (-x) := by
  rw [quarter_pow_exp]
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc := (div_le_iff₀ hlog).mp (Nat.le_ceil (x / Real.log 4))
  nlinarith

theorem prefactor_quarter_ceil_bound (M x : ℝ) (hM : 0 < M) :
    M * (1/4:ℝ)^⌈(x+Real.log M) / Real.log 4⌉₊ ≤ Real.exp (-x) := by
  calc
    _ ≤ M * Real.exp (-(x+Real.log M)) :=
      mul_le_mul_of_nonneg_left (quarter_ceil_bound (x+Real.log M)) hM.le
    _ = Real.exp (Real.log M) * Real.exp (-(x+Real.log M)) := by
      rw [Real.exp_log hM]
    _ = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The extra successor guarantees a positive moment order and retains
the requested exponential bound. -/
theorem prefactor_quarter_successor_bound (M x : ℝ) (hM : 0 < M) :
    M * (1/4:ℝ)^(⌈(x+Real.log M) / Real.log 4⌉₊+1) ≤ Real.exp (-x) := by
  calc
    _ ≤ M * (1/4:ℝ)^⌈(x+Real.log M) / Real.log 4⌉₊ := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4)
        ⌈(x+Real.log M) / Real.log 4⌉₊]
    _ ≤ _ := prefactor_quarter_ceil_bound M x hM

theorem exponential_moment_order_le (J c L M : ℝ)
    (hJ : 0 ≤ J) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlog : Real.log M ≤ c*L) :
    ((⌈(J*L+Real.log M) / Real.log 4⌉₊+1:ℕ):ℝ) ≤
      ((J+c)/Real.log 4+2)*L := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnum : 0 ≤ J*L+Real.log M :=
    add_nonneg (mul_nonneg hJ (by linarith)) (Real.log_nonneg hM)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hnum h4.le)
  have hdiv : (J*L+Real.log M)/Real.log 4 ≤ ((J+c)/Real.log 4)*L := by
    calc
      _ ≤ (J*L+c*L)/Real.log 4 := div_le_div_of_nonneg_right (by linarith) h4.le
      _ = _ := by ring
  push_cast
  nlinarith

theorem polynomial_prefactor_log_le (C L : ℝ) (q : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L) :
    Real.log (C*L^q) ≤ (Real.log C+(q:ℝ))*L := by
  have hC0 : 0 < C := by linarith
  have hL0 : 0 < L := by linarith
  rw [Real.log_mul hC0.ne' (pow_pos hL0 _).ne', Real.log_pow]
  have h1 := mul_le_mul_of_nonneg_right (Real.log_le_self hL0.le) (Nat.cast_nonneg q)
  have h2 := mul_le_mul_of_nonneg_left hL (Real.log_nonneg hC)
  nlinarith

end LipschitzHilbert

end

end OAI
