import OAI.NumberTheory.Ostmann.Characters.PrimeMomentFactors

namespace OAI

/-! # The actual square and nonsquare transfer factors at manuscript scales -/

namespace Ostmann

open Filter

theorem eventual_prime_moment_factors (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ J Z k l I U : ℕ, ∀ A : ℝ,
      0 < J → 1 ≤ Z → Real.exp T ≤ C * T * J →
      (Z : ℝ) ≤ Real.exp (T + 1) →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (I : ℝ) ≤ Real.exp (C * T) → (U : ℝ) ≤ Real.exp (C * T) →
      0 ≤ A → A ≤ Real.exp (C * T) →
      ((2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
        ((I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤
        (Real.exp (ε * T ^ (9999999 / 10000000 : ℝ))) ^ (2 * l)) ∧
      ((2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
        ((I : ℝ) * (2 : ℝ) ^ (2 * l)) *
        ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤
        (Real.exp (-10 * T)) ^ (2 * l)) := by
  let D := 4 * C + 10
  have hC0 : 0 ≤ C := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [eventual_prime_product_parameter_budget D (2 * ε) hD (by positivity),
    eventual_prime_product_error_budget D hD, eventually_ge_atTop (1 : ℝ)] with T hs he hT
  intro J Z k l I U A hJ hZ1 hpop hZ hkL hkU hl1 hlL hlU hI hU hA hmass
  have hT0 : 0 ≤ T := by linarith
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hl1
  have hratio := prime_moment_sampling_ratio C T J k hC0 hT hpop hkU
  have hratio' : (k : ℝ) ≤ Real.exp ((2 * C + 1 + 3 * Real.log T) - (T + 1)) * J := by
    have heq : (2 * C + 1 + 3 * Real.log T) - (T + 1) = 2 * C + 3 * Real.log T - T := by ring
    simpa only [heq] using hratio
  constructor
  · apply (prime_moment_square_factor_bound J Z k l I (2 * C + 1 + 3 * Real.log T)
      (T + 1) (C * T) hJ hratio' hZ hZ1 hI).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hb := hs k l hk0 hkU hlL hlU
    have hconst : 2 + C * T ≤ D * T := by dsimp [D]; nlinarith
    have hlconst : 2 * (l : ℝ) ≤ D * l := by dsimp [D]; nlinarith
    have hkconst : (k : ℝ) * (2 * C + 1 + 3 * Real.log T) ≤
        k * (D + 3 * Real.log T) := by dsimp [D]; nlinarith
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hb, hconst, hlconst, hkconst]
  · apply (prime_moment_nonsquare_factor_bound J k l I U (2 * C + 3 * Real.log T)
      T (C * T) A (C * T) hJ hratio hI hU hA hmass).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hb := he k l hkL hl1' hlU
    have hconst : 4 + C * T ≤ D * T := by dsimp [D]; nlinarith
    have hlconst : 2 * (l : ℝ) ≤ D * l := by dsimp [D]; nlinarith
    have hlT : 4 * (l : ℝ) * (C * T) ≤ 2 * D * l * T := by
      have hh : 4 * C ≤ 2 * D := by dsimp [D]; linarith
      have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hl0) hT0
      nlinarith only [hmul]
    have hkconst : (k : ℝ) * (2 * C + 3 * Real.log T - T) ≤
        k * (D + 3 * Real.log T - T) := by dsimp [D]; nlinarith
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hb, hconst, hlconst, hlT, hkconst]

end Ostmann

end OAI
