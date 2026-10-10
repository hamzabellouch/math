import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterProbability

namespace OAI

/-! # Numerical cost of discarding small common centers -/

namespace Ostmann

open Filter

/-- The original interval length and prime lower bound control the lower
factorial moment, with only an exponential-in-the-tuple-length loss. -/
theorem liftMomentUpper_le_scaled (T : ℝ) (J r H Z : ℕ)
    (hT : 0 ≤ T)
    (hZ : Real.exp T / 2 ≤ (Z : ℝ))
    (hH : (H : ℝ) ≤ 2 * Real.exp ((r - 10 : ℕ) * T + T / 5)) :
    liftMomentUpper J (r - 10) H Z ≤
      6 * (2 : ℝ) ^ r * Real.exp (T / 5) * (J : ℝ) ^ (r - 10) := by
  have hZpos : (0 : ℝ) < Z := lt_of_lt_of_le (by positivity) hZ
  have hZpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp T / 2) hZ (r - 10)
  have heq : (Real.exp T / 2) ^ (r - 10) *
      ((2 : ℝ) ^ (r - 10) * Real.exp (T / 5)) =
      Real.exp ((r - 10 : ℕ) * T + T / 5) := by
    rw [div_pow, ← mul_assoc, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ (r - 10) ≠ 0),
      ← Real.exp_nat_mul, ← Real.exp_add]
  have hexp : 1 ≤ Real.exp ((r - 10 : ℕ) * T + T / 5) :=
    Real.one_le_exp (by positivity)
  have hratio : (2 * (H : ℝ) + 1) / (Z : ℝ) ^ (r - 10) ≤
      5 * (2 : ℝ) ^ (r - 10) * Real.exp (T / 5) := by
    apply (div_le_iff₀ (pow_pos hZpos _)).mpr
    have hh := mul_le_mul_of_nonneg_right hZpow
      (show 0 ≤ (2 : ℝ) ^ (r - 10) * Real.exp (T / 5) by positivity)
    rw [heq] at hh
    nlinarith only [hH, hexp, hh]
  have hpow : (2 : ℝ) ^ (r - 10) ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ r * Real.exp (T / 5) := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    have he : (1 : ℝ) ≤ Real.exp (T / 5) := Real.one_le_exp (by positivity)
    nlinarith
  have hterm : (2 * (H : ℝ) + 1) / (Z : ℝ) ^ (r - 10) + 1 ≤
      6 * (2 : ℝ) ^ r * Real.exp (T / 5) := by
    have hh := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (T / 5))
    nlinarith only [hratio, hone, hh]
  have hd : (J.descFactorial (r - 10) : ℝ) ≤ (J : ℝ) ^ (r - 10) := by
    exact_mod_cast Nat.descFactorial_le_pow J (r - 10)
  unfold liftMomentUpper
  exact (mul_le_mul hd hterm (by positivity) (by positivity)).trans_eq (by ring)

/-- The cost of ten missing prime factors dominates the tuple and logarithmic
losses at the manuscript's population scale. -/
theorem eventual_commonCenter_population_budget (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (J r : ℕ),
      Real.exp T ≤ Cpop * T * J → (2 : ℝ) ^ r ≤ Real.exp (T / 10) →
      48 * (2 : ℝ) ^ r * Real.exp (33 * T / 5) ≤ (J : ℝ) ^ 10 := by
  have hCpop0 : 0 < Cpop := by linarith
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 10 (show (0 : ℝ) < 1 by norm_num)).const_mul_left
    (48 * Cpop ^ 10)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpoly hT J r hJ hr
  have hTpos : 0 < T := by linarith
  have hp' : 48 * (Cpop * T) ^ 10 ≤ Real.exp T := by
    have hh : (48 * Cpop ^ 10) * T ^ 10 ≤ Real.exp T := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (48 * Cpop ^ 10) * T ^ 10), abs_of_pos (Real.exp_pos _),
        one_mul] using hpoly
    nlinarith only [hh]
  have hten := pow_le_pow_left₀ (Real.exp_nonneg T) hJ 10
  have hc : (48 * (2 : ℝ) ^ r * Real.exp (33 * T / 5)) * (Cpop * T) ^ 10 ≤
      (J : ℝ) ^ 10 * (Cpop * T) ^ 10 := by
    calc
      _ = (48 * (Cpop * T) ^ 10) * (2 : ℝ) ^ r * Real.exp (33 * T / 5) := by ring
      _ ≤ Real.exp T * Real.exp (T / 10) * Real.exp (33 * T / 5) := by gcongr
      _ = Real.exp (77 * T / 10) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (10 * T) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [← Real.exp_nat_mul, show (Cpop * T * J) ^ 10 =
          (J : ℝ) ^ 10 * (Cpop * T) ^ 10 by ring] at hten
        exact hten
  exact (mul_le_mul_iff_left₀ (show 0 < (Cpop * T) ^ 10 by positivity)).mp hc

theorem eventual_commonCenter_discard_budget (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (J r H Z Amax : ℕ) (K : ℝ),
      10 ≤ r → K ≤ T → 0 < Amax →
      Real.exp T ≤ Cpop * T * J → (2 : ℝ) ^ r ≤ Real.exp (T / 10) →
      Real.exp T / 2 ≤ (Z : ℝ) →
      (H : ℝ) ≤ 2 * Real.exp ((r - 10 : ℕ) * T + T / 5) →
      (Amax : ℝ) ≤ 2 * Real.exp (T / 5) →
      Real.exp (3 * T / 5) ^ 10 * liftMomentUpper J (r - 10) H Z ≤
        Real.exp (-K / 5) * (J : ℝ) ^ r / (4 * Amax) := by
  filter_upwards [eventual_commonCenter_population_budget Cpop hCpop, eventually_ge_atTop (0 : ℝ)]
    with T hpop hT J r H Z Amax K hr hK hA hJ hpow hZ hH hAU
  have hAr : (0 : ℝ) < Amax := by exact_mod_cast hA
  have hnum := hpop J r hJ hpow
  have hlift := liftMomentUpper_le_scaled T J r H Z hT hZ hH
  have he : Real.exp (32 * T / 5) ≤ Real.exp (-K / 5) * Real.exp (33 * T / 5) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnum' : 48 * (2 : ℝ) ^ r * Real.exp (32 * T / 5) ≤
      Real.exp (-K / 5) * (J : ℝ) ^ 10 := by
    calc
      _ ≤ 48 * (2 : ℝ) ^ r * (Real.exp (-K / 5) * Real.exp (33 * T / 5)) := by gcongr
      _ = Real.exp (-K / 5) * (48 * (2 : ℝ) ^ r * Real.exp (33 * T / 5)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnum (Real.exp_nonneg _)
  apply (le_div_iff₀ (show (0 : ℝ) < 4 * Amax by positivity)).mpr
  calc
    _ ≤ Real.exp (3 * T / 5) ^ 10 *
        (6 * (2 : ℝ) ^ r * Real.exp (T / 5) * (J : ℝ) ^ (r - 10)) *
        (4 * (2 * Real.exp (T / 5))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlift (by positivity)
      · exact mul_le_mul_of_nonneg_left hAU (by norm_num)
      · positivity
      · positivity
    _ = (48 * (2 : ℝ) ^ r * Real.exp (32 * T / 5)) * (J : ℝ) ^ (r - 10) := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      have hex : Real.exp ((10 : ℝ) * (3 * T / 5)) * Real.exp (T / 5) * Real.exp (T / 5) =
          Real.exp (32 * T / 5) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc
        _ = 48 * (2 : ℝ) ^ r *
            (Real.exp ((10 : ℝ) * (3 * T / 5)) * Real.exp (T / 5) * Real.exp (T / 5)) *
              (J : ℝ) ^ (r - 10) := by ring
        _ = _ := by rw [hex]
    _ ≤ (Real.exp (-K / 5) * (J : ℝ) ^ 10) * (J : ℝ) ^ (r - 10) := by gcongr
    _ = Real.exp (-K / 5) * (J : ℝ) ^ r := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hr]

end Ostmann

end OAI
