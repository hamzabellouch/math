import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticFrequencyTree
import OAI.NumberTheory.Ostmann.QuadraticCenter.UniformDivisorBound

namespace OAI

/-! # The frequency-tree cost is subexponential at fixed depth -/

namespace Ostmann

open Filter

theorem cubic_log_budget (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
      8 * (1 + Real.log N) ^ 3 ≤ Real.exp (ε * m) := by
  have he := ((isLittleO_pow_exp_pos_mul_atTop 3 hε).const_mul_left
    (8 * (1 + C) ^ 3)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with m hm hm1 N hN
  have hm0 : 0 ≤ m := by linarith
  have hlog : Real.log N ≤ C * m := by
    by_cases hn : N = 0
    · subst N
      simpa using mul_nonneg hC hm0
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hN
  have hlog0 := Real.log_natCast_nonneg N
  have hlin : 1 + Real.log N ≤ (1 + C) * m := by nlinarith
  have hpoly : 8 * (1 + C) ^ 3 * m ^ 3 ≤ Real.exp (ε * m) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 8 * (1 + C) ^ 3 * m ^ 3), abs_of_pos (Real.exp_pos _), one_mul] using hm
  calc
    _ ≤ 8 * ((1 + C) * m) ^ 3 := by gcongr
    _ = 8 * (1 + C) ^ 3 * m ^ 3 := by ring
    _ ≤ _ := hpoly

/-- One value of `D` controls every frequency divisor and every joint
square modulus up to `exp(2*C*m)`, with the total cost at most `exp(epsilon*m)`. -/
theorem frequency_budget_subexponential (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (2 * C * m) →
        (n.divisors.card : ℝ) ≤ D) ∧
      (∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
        8 * D ^ 4 * (1 + Real.log N) ^ 3 ≤ Real.exp (ε * m)) := by
  obtain ⟨M, hM⟩ := divisors_subexponential_uniform (2 * C) (ε / 8)
    (by positivity) (by positivity)
  filter_upwards [eventually_ge_atTop M, cubic_log_budget C (ε / 2) hC (by positivity)]
    with m hm hpoly
  refine ⟨Real.exp ((ε / 8) * m), (Real.exp_pos _).le, hM m hm, fun N hN => ?_⟩
  have hexp : Real.exp ((ε / 8) * m) ^ 4 = Real.exp ((ε / 2) * m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ = Real.exp ((ε / 2) * m) * (8 * (1 + Real.log N) ^ 3) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((ε / 2) * m) :=
      mul_le_mul_of_nonneg_left (hpoly N hN) (Real.exp_pos _).le
    _ = Real.exp (ε * m) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
