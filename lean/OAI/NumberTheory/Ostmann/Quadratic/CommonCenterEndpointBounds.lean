import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterCutoffs
import OAI.NumberTheory.Ostmann.Quadratic.KernelCountFromCenter

namespace OAI

/-! # The extracted rational center fits the original endpoint cutoffs -/

namespace Ostmann

open Filter

theorem eventual_commonCenter_denominator (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, T ^ (3 / 2 : ℝ) ≤ L →
      (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ Real.exp (η * L) := by
  filter_upwards [eventual_kernel_count_prefactor 1 η (by norm_num) hη,
    eventually_ge_atTop (1 : ℝ)] with T hbound hT L hL
  have he : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
  have hcmp : Real.exp (13 * T / 100) ≤ Real.exp (4 * T) := Real.exp_le_exp.mpr (by linarith)
  have hh := hbound L hL
  nlinarith only [hc, he, hcmp, hh]

theorem commonCenter_endpoint_power_bound (T X : ℝ) (k Z m : ℕ) (h x : ℤ)
    (hT : 3 ≤ T) (hX : 1 ≤ X) (hk : 10 ≤ k)
    (hXU : X ≤ Real.exp ((k - 10 : ℕ) * T))
    (hm : m ≤ ⌈Real.exp (13 * T / 100)⌉₊)
    (hh : |h| ≤ ⌈X * Real.exp (13 * T / 100)⌉₊)
    (hx : |(x : ℝ)| ≤ X) (hZ : Real.exp T ≤ (Z : ℝ)) :
    |(m : ℤ) * x - h| ≤ (Z ^ k : ℕ) := by
  have hT0 : 0 ≤ T := by linarith
  have hE : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hEcmp : Real.exp (13 * T / 100) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
  have hmR : (m : ℝ) ≤ 2 * Real.exp T := by
    have hc := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
    have hm' : (m : ℝ) ≤ ⌈Real.exp (13 * T / 100)⌉₊ := by exact_mod_cast hm
    linarith
  have hhR : |(h : ℝ)| ≤ 2 * X * Real.exp T := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ X * Real.exp (13 * T / 100) by positivity)
    have hh' : |(h : ℝ)| ≤ ⌈X * Real.exp (13 * T / 100)⌉₊ := by exact_mod_cast hh
    have heX : 1 ≤ X * Real.exp (13 * T / 100) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hEcmp (show 0 ≤ X by linarith)
    nlinarith only [hc, hh', heX, hmul]
  have hfour : (4 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hbound : |(((m : ℤ) * x - h : ℤ) : ℝ)| ≤ (Z : ℝ) ^ k := by
    push_cast
    calc
      |(m : ℝ) * x - h| ≤ |(m : ℝ) * x| + |(h : ℝ)| := abs_sub _ _
      _ = (m : ℝ) * |(x : ℝ)| + |(h : ℝ)| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      _ ≤ (2 * Real.exp T) * X + 2 * X * Real.exp T :=
        add_le_add (mul_le_mul hmR hx (abs_nonneg _) (by positivity)) hhR
      _ = 4 * X * Real.exp T := by ring
      _ ≤ Real.exp T * Real.exp ((k - 10 : ℕ) * T) * Real.exp T := by gcongr
      _ = Real.exp (((k - 10 : ℕ) : ℝ) * T + 2 * T) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((k : ℝ) * T) := by
        apply Real.exp_le_exp.mpr
        rw [Nat.cast_sub hk, Nat.cast_ofNat]
        nlinarith
      _ = (Real.exp T) ^ k := Real.exp_nat_mul T k
      _ ≤ (Z : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_nonneg _) hZ k
  exact_mod_cast hbound

end Ostmann

end OAI
