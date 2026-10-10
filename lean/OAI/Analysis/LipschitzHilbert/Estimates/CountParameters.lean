import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Numerical parameters for the simultaneous direction count

The final steps in §6: a fixed polynomial times a Gaussian tail is below
any prescribed exponential budget, and the chosen direction bound has
the required factor-one-hundred margin.
-/

noncomputable section

open Filter

namespace LipschitzHilbert

/-- An explicit sufficient lower bound for the count-exception budget. -/
theorem polynomial_gaussian_le_exponential {C c J a L : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hL : 1 ≤ L)
    (hlarge : (|Real.log C| + |a| + J) / c ≤ L) :
    C * L ^ a * Real.exp (-c * L ^ 2) ≤ Real.exp (-J * L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogL : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hL0]
  have hlogC : Real.log C ≤ |Real.log C| * L := by
    calc
      Real.log C ≤ |Real.log C| := le_abs_self _
      _ ≤ |Real.log C| * L := le_mul_of_one_le_right (abs_nonneg _) hL
  have haL : Real.log L * a ≤ |a| * L := by
    calc
      Real.log L * a ≤ Real.log L * |a| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hlog0
      _ ≤ L * |a| := mul_le_mul_of_nonneg_right hlogL (abs_nonneg _)
      _ = |a| * L := mul_comm _ _
  have hlinear : |Real.log C| + |a| + J ≤ c * L := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hlarge
  have hquadratic := mul_le_mul_of_nonneg_right hlinear hL0.le
  have hexponent : Real.log C + Real.log L * a + (-c * L ^ 2) ≤ -J * L := by
    nlinarith
  calc
    C * L ^ a * Real.exp (-c * L ^ 2) =
        Real.exp (Real.log C + Real.log L * a + (-c * L ^ 2)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hC, Real.rpow_def_of_pos hL0]
    _ ≤ Real.exp (-J * L) := Real.exp_le_exp.mpr hexponent

/-- The exceptional budget holds for all sufficiently large `L`, with no
dependence on the number of tops or scales. -/
theorem eventually_polynomial_gaussian_le_exponential (C a J : ℝ) {c : ℝ}
    (hC : 0 < C) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, C * L ^ a * Real.exp (-c * L ^ 2) ≤ Real.exp (-J * L) := by
  filter_upwards [eventually_ge_atTop (max 1 ((|Real.log C| + |a| + J) / c))] with L hL
  exact polynomial_gaussian_le_exponential hC hc
    ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)

/-- `theta=L^(-a)` and `Lambda=L^(a+2)` give the exact quadratic tail. -/
theorem count_threshold_product {L : ℝ} (hL : 0 < L) (a : ℝ) :
    L ^ (-a) * L ^ (a + 2) = L ^ 2 := by
  rw [← Real.rpow_add hL]
  have heq : -a + (a + 2) = (2 : ℝ) := by ring
  rw [heq, Real.rpow_two]

/-- The manuscript's `D=L^(a+4)` absorbs the count threshold and the
reference direction with the stated factor-one-hundred margin. -/
theorem count_direction_margin {L a : ℝ} (hL : 15 ≤ L) (ha : 0 ≤ a) :
    1 + L ^ (a + 2) ≤ L ^ (a + 4) / 100 := by
  have hL0 : 0 < L := by linarith
  have hbase : 1 ≤ L ^ (a + 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hpow0 : 0 ≤ L ^ (a + 2) := Real.rpow_nonneg hL0.le _
  have hsq : 200 ≤ L ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hpow0
  have hexponent : a + 4 = (a + 2) + 2 := by ring
  have heq : L ^ (a + 4) = L ^ (a + 2) * L ^ 2 := by
    calc
      L ^ (a + 4) = L ^ ((a + 2) + 2) := by rw [hexponent]
      _ = _ := by rw [Real.rpow_add hL0, Real.rpow_two]
  rw [heq]
  nlinarith

/-- With `K=L^k`, `P=L^p`, `p≥k`, `theta=L^(-a)` and
`lambda=L^(a+2)`, the complete reference-family prefactor is absorbed
by the exact Gaussian rate supplied by angular counting. -/
theorem count_power_budget {L k p a c J : ℝ} (hL : 1 ≤ L) (hkp : k ≤ p)
    (hc : 0 ≤ c)
    (hlarge : 240 * (1 + c) * (|Real.log 768| + |2 * p| + J) ≤ L) :
    384 * L ^ k * (L ^ k + L ^ p) *
        Real.exp (-(L ^ (-a) * L ^ (a + 2)) / (240 * (1 + c))) ≤
      Real.exp (-J * L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hK : 0 ≤ L ^ k := Real.rpow_nonneg hL0.le _
  have hP : 0 ≤ L ^ p := Real.rpow_nonneg hL0.le _
  have hKP : L ^ k ≤ L ^ p := Real.rpow_le_rpow_of_exponent_le hL hkp
  have hprod : L ^ k * (L ^ k + L ^ p) ≤ 2 * (L ^ p * L ^ p) := by
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add_right hKP (L ^ p)) hK
    have h₂ := mul_le_mul_of_nonneg_right hKP (add_nonneg hP hP)
    nlinarith
  have hpower : L ^ (2 * p) = L ^ p * L ^ p := by
    rw [show 2 * p = p + p by ring, Real.rpow_add hL0]
  have hpref : 384 * L ^ k * (L ^ k + L ^ p) ≤ 768 * L ^ (2 * p) := by
    rw [hpower]
    nlinarith
  have hrate : 0 < 1 / (240 * (1 + c)) := by positivity
  have hthreshold : (|Real.log 768| + |2 * p| + J) / (1 / (240 * (1 + c))) ≤ L := by
    calc
      _ = 240 * (1 + c) * (|Real.log 768| + |2 * p| + J) := by
        rw [one_div, div_inv_eq_mul]
        ring
      _ ≤ L := hlarge
  have hbudget := polynomial_gaussian_le_exponential (C := 768) (a := 2 * p)
    (by norm_num) hrate hL hthreshold
  have hexp : -(L ^ (-a) * L ^ (a + 2)) / (240 * (1 + c)) =
      -(1 / (240 * (1 + c))) * L ^ 2 := by
    rw [count_threshold_product hL0]
    ring
  rw [hexp]
  exact (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le).trans hbudget

theorem eventually_count_power_budget (k p a c J : ℝ) (hkp : k ≤ p) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop,
      384 * L ^ k * (L ^ k + L ^ p) *
          Real.exp (-(L ^ (-a) * L ^ (a + 2)) / (240 * (1 + c))) ≤
        Real.exp (-J * L) := by
  filter_upwards [eventually_ge_atTop
    (max 1 (240 * (1 + c) * (|Real.log 768| + |2 * p| + J)))] with L hL
  exact count_power_budget ((le_max_left _ _).trans hL) hkp hc ((le_max_right _ _).trans hL)

end LipschitzHilbert

end

end OAI
