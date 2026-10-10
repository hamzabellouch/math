import OAI.NumberTheory.Ostmann.Construction.PrimeProductNormTransfer
import OAI.NumberTheory.Ostmann.Construction.PrimeProductParameterBudget

namespace OAI

/-! # Elementary transfer factors for sampling distinct prime products -/

namespace Ostmann

theorem prime_moment_factorial_bound (J k : ℕ) (a : ℝ) (hJ : 0 < J)
    (hk : (k : ℝ) ≤ Real.exp a * J) :
    2 * (k.factorial : ℝ) / (J : ℝ) ^ k ≤ 2 * Real.exp ((k : ℝ) * a) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hk k
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  apply (div_le_iff₀ (pow_pos hJ0 _)).mpr
  nlinarith only [hfac, hp]

theorem prime_moment_square_factor_bound (J Z k l I : ℕ) (a t C : ℝ)
    (hJ : 0 < J) (hk : (k : ℝ) ≤ Real.exp (a - t) * J)
    (hZ : (Z : ℝ) ≤ Real.exp t) (hZ1 : 1 ≤ Z)
    (hI : (I : ℝ) ≤ Real.exp C) :
    (2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
      ((I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤
      Real.exp (2 + C + 2 * l + (k : ℝ) * a) := by
  have hfac := prime_moment_factorial_bound J k (a - t) hJ hk
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow2 : (2 : ℝ) ^ (2 * l) ≤ Real.exp (2 * l) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 (2 * l)
  have hZpow : ((Z ^ k + 1 : ℕ) : ℝ) ≤ 2 * Real.exp ((k : ℝ) * t) := by
    have h1 : (1 : ℝ) ≤ (Z : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hZ1)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Z : (0 : ℝ) ≤ Z) hZ k
    rw [← Real.exp_nat_mul] at hp
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    linarith
  calc
    _ ≤ (2 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) * (2 * Real.exp ((k : ℝ) * t)) := by
      gcongr
    _ ≤ (Real.exp 1 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) * (Real.exp 1 * Real.exp ((k : ℝ) * t)) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem prime_moment_nonsquare_factor_bound (J k l I U : ℕ) (a t C A B : ℝ)
    (hJ : 0 < J) (hk : (k : ℝ) ≤ Real.exp (a - t) * J)
    (hI : (I : ℝ) ≤ Real.exp C) (hU : (U : ℝ) ≤ Real.exp B)
    (hA : 0 ≤ A) (hmass : A ≤ Real.exp B) :
    (2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
      ((I : ℝ) * (2 : ℝ) ^ (2 * l)) *
      ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤
      Real.exp (4 + C + 2 * l + 4 * l * B + (k : ℝ) * (a - t)) := by
  have hfac := prime_moment_factorial_bound J k (a - t) hJ hk
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one,
      show (2 : ℝ) ^ 3 = 8 by norm_num] using hh
  have hfac' : 2 * (k.factorial : ℝ) / (J : ℝ) ^ k ≤
      Real.exp 1 * Real.exp ((k : ℝ) * (a - t)) :=
    hfac.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _))
  have hpow2 : (2 : ℝ) ^ (2 * l) ≤ Real.exp (2 * l) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 (2 * l)
  have hUp := pow_le_pow_left₀ (Nat.cast_nonneg U : (0 : ℝ) ≤ U) hU (2 * l)
  have hAp := pow_le_pow_left₀ hA hmass (2 * l)
  rw [← Real.exp_nat_mul] at hUp hAp
  calc
    _ ≤ (Real.exp 1 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) *
        ((Real.exp 3 * Real.exp ((2 * l : ℕ) * B)) * Real.exp ((2 * l : ℕ) * B)) := by
      gcongr
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem prime_moment_sampling_ratio (C T : ℝ) (J k : ℕ)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hJ : Real.exp T ≤ C * T * J)
    (hk : (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ)) :
    (k : ℝ) ≤ Real.exp (2 * C + 3 * Real.log T - T) * J := by
  have hT0 : 0 < T := by linarith
  have hkT : (k : ℝ) ≤ 2 * T := by
    apply hk.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hconst : 2 * C ≤ Real.exp (2 * C) := by linarith [Real.add_one_le_exp (2 * C)]
  have hpower : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT (by omega)
  have hbound : 2 * C * T ^ 2 ≤ Real.exp (2 * C + 3 * Real.log T) := by
    calc
      _ ≤ Real.exp (2 * C) * T ^ 3 := mul_le_mul hconst hpower (by positivity) (Real.exp_nonneg _)
      _ = _ := by
        have hx : Real.exp (3 * Real.log T) = T ^ 3 := by
          calc
            _ = Real.exp ((3 : ℕ) * Real.log T) := by norm_num
            _ = (Real.exp (Real.log T)) ^ 3 := Real.exp_nat_mul _ _
            _ = _ := by rw [Real.exp_log hT0]
        rw [Real.exp_add, hx]
  have hscaled : (k : ℝ) * Real.exp T ≤ Real.exp (2 * C + 3 * Real.log T) * J := by
    calc
      _ ≤ (k : ℝ) * (C * T * J) := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _)
      _ ≤ (2 * T) * (C * T * J) := mul_le_mul_of_nonneg_right hkT (by positivity)
      _ = (2 * C * T ^ 2) * J := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)
  have heq : (Real.exp (2 * C + 3 * Real.log T - T) * J) * Real.exp T =
      Real.exp (2 * C + 3 * Real.log T) * J := by
    calc
      _ = (Real.exp (2 * C + 3 * Real.log T - T) * Real.exp T) * J := by ring
      _ = _ := by rw [← Real.exp_add, sub_add_cancel]
  exact (mul_le_mul_iff_left₀ (Real.exp_pos T)).mp (hscaled.trans_eq heq.symm)

end Ostmann

end OAI
