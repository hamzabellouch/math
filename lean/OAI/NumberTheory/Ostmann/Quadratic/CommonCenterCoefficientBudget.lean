import OAI.NumberTheory.Ostmann.Construction.OriginalMomentBudget
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticKernelCount

namespace OAI

/-! # The original common-center set controls the amplification energy -/

namespace Ostmann

open Filter

theorem eventual_commonCenter_coefficient_budget (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (r : ℕ) (J J₀ Z : ℝ),
      2 ≤ r → (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      0 < J → 0 < J₀ → 0 ≤ Z →
      Real.exp T ≤ Cpop * T * J → J * Real.exp (-T / (r - 1 : ℕ)) ≤ J₀ →
      Z ≤ Real.exp (T + 1) →
      Z ^ r * (r.factorial : ℝ) / J₀ ^ r ≤ Real.exp (3 * T) := by
  let C := Cpop * Real.exp 1
  have hC : 1 ≤ C := by
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ Cpop by linarith)
    dsimp [C]
    linarith
  filter_upwards [eventual_repeat_power_budget C 1 hC zero_lt_one,
    eventually_ge_atTop (1 : ℝ)] with T hbudget hT r J J₀ Z hr hrU hJ hJ₀ hZ hpop hcenter hZU
  have hTpos : 0 < T := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hprev : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ r by omega)]; norm_num
  have hprevpos : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (show 0 < r - 1 by omega)
  have hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ T := by
    have hp : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
        (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
    linarith [Real.rpow_nonneg hTpos.le (9999999 / 10000000 : ℝ)]
  have hrep := hbudget r T hrU hK
  have hbase : C * T * (r : ℝ) ≤ 16 * C * T * (r : ℝ) ^ 3 := by
    have hr3 : (r : ℝ) ≤ (r : ℝ) ^ 3 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
    calc
      _ ≤ C * T * (r : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hr3 (by positivity)
      _ ≤ 16 * (C * T * (r : ℝ) ^ 3) := le_mul_of_one_le_left (by positivity) (by norm_num)
      _ = _ := by ring
  have hsmall : (C * T * (r : ℝ)) ^ r ≤ Real.exp T := by
    have hp := pow_le_pow_left₀ (by positivity) hbase r
    have hc2 : 1 ≤ C ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hc2 (pow_nonneg (show 0 ≤ 16 * C * T * (r : ℝ) ^ 3 by positivity) r)
    norm_num only [one_mul] at hrep
    nlinarith only [hp, hh, hrep]
  let u := T / (r - 1 : ℕ)
  have hZJ : Z ≤ (C * T * Real.exp u) * J₀ := by
    have he : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hcen : J * Real.exp (-u) ≤ J₀ := by simpa only [u, neg_div] using hcenter
    calc
      Z ≤ Real.exp (T + 1) := hZU
      _ = Real.exp 1 * Real.exp T := by rw [Real.exp_add]; ring
      _ ≤ Real.exp 1 * (Cpop * T * J) := mul_le_mul_of_nonneg_left hpop (Real.exp_nonneg _)
      _ = (Real.exp 1 * (Cpop * T * J)) * (Real.exp u * Real.exp (-u)) := by rw [he, mul_one]
      _ = (C * T * Real.exp u) * (J * Real.exp (-u)) := by dsimp [C]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcen (by positivity)
  have hfac : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  have hu : (r : ℝ) * u ≤ 2 * T := by
    dsimp [u]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hprevpos).mpr
    rw [hprev]
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  calc
    Z ^ r * (r.factorial : ℝ) / J₀ ^ r ≤
        ((C * T * Real.exp u) * J₀) ^ r * (r : ℝ) ^ r / J₀ ^ r := by gcongr
    _ = (C * T * (r : ℝ)) ^ r * Real.exp ((r : ℝ) * u) := by
      rw [Real.exp_nat_mul, ← mul_pow]
      field_simp
      ring
    _ ≤ Real.exp T * Real.exp (2 * T) := by gcongr
    _ = Real.exp (3 * T) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
