import OAI.NumberTheory.Ostmann.ZeroDensity.ResidueCountingBound
import OAI.NumberTheory.Ostmann.ZeroDensity.CanonicalThetaSize
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszExponentialParameters

namespace OAI

/-! # Elementary control of the complementary large-modulus range -/

namespace Ostmann

open Filter

theorem residuePsi_large_modulus_bound_log : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, 0 < q → Real.exp (y / 2) ≤ (q : ℝ) →
      ∀ a : ℕ,
        |residuePsi q a (Real.exp (y ^ 2)) - thetaMainTerm q.totient
          (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q))
            (Real.exp (y ^ 2))| ≤
          C * Real.exp (y ^ 2) * Real.exp (-(1 / 4 : ℝ) * y) := by
  obtain ⟨D, hD, hmain⟩ := canonical_theta_sqrt_bound
  refine ⟨D + 2, by positivity, ?_⟩
  filter_upwards [riesz_polynomial_absorption 1 (1 / 4) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with y hp hy
  intro q hq hqy a
  let X := Real.exp (y ^ 2)
  have hX : 1 ≤ X := Real.one_le_exp (sq_nonneg y)
  have hXp : 0 < X := Real.exp_pos _
  have hpoly : y ^ 2 ≤ Real.exp (y / 4) := by
    rw [show (1 / 4 : ℝ) * y = y / 4 by ring] at hp
    linarith
  have hquot : y ^ 2 / q ≤ Real.exp (-y / 4) := by
    calc
      _ ≤ Real.exp (y / 4) / Real.exp (y / 2) :=
        div_le_div₀ (Real.exp_nonneg _) hpoly (Real.exp_pos _) hqy
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hpoly' : y ^ 2 ≤ X * Real.exp (-y / 4) := by
    calc
      _ ≤ Real.exp (y / 4) := hpoly
      _ ≤ Real.exp (y ^ 2 - y / 4) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by
        dsimp [X]
        rw [Real.exp_sub, show -y / 4 = -(y / 4) by ring, Real.exp_neg]
        rfl
  have hcount := residuePsi_counting_bound q a X hq hX
  have hlog : Real.log X = y ^ 2 := Real.log_exp _
  rw [hlog] at hcount
  have hcount' : residuePsi q a X ≤ 2 * X * Real.exp (-y / 4) := by
    have hm := mul_le_mul_of_nonneg_left hquot hXp.le
    have hid : (X / (q : ℝ) + 1) * y ^ 2 = X * (y ^ 2 / q) + y ^ 2 := by ring
    rw [hid] at hcount
    linarith
  have hsqrt : Real.exp (y / 4) ≤ Real.sqrt q := by
    have hh := Real.sqrt_le_sqrt hqy
    rw [← Real.exp_half] at hh
    convert hh using 1; congr 1; ring
  have hm := hmain q a X hq hX
  have hmain' : |thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X| ≤ D * X * Real.exp (-y / 4) := by
    calc
      _ ≤ D * X / Real.sqrt q := hm
      _ ≤ D * X / Real.exp (y / 4) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hsqrt
      _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
  have htri := abs_sub (residuePsi q a X)
    (thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X)
  rw [abs_of_nonneg (residuePsi_nonneg q a X)] at htri
  have he : -(1 / 4 : ℝ) * y = -y / 4 := by ring
  rw [he]
  change |residuePsi q a X - thetaMainTerm q.totient
    (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤ _
  nlinarith

theorem residuePsi_large_modulus_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 0 < q →
      Real.exp (Real.sqrt (Real.log X) / 2) ≤ (q : ℝ) → ∀ a : ℕ,
        |residuePsi q a X - thetaMainTerm q.totient
          (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          C * X * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log X)) := by
  obtain ⟨C, hC, hbound⟩ := residuePsi_large_modulus_bound_log
  refine ⟨C, hC, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually hbound, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have he : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log (by linarith)]
  dsimp only [Function.comp_apply] at hX
  simpa only [he] using hX

end Ostmann

end OAI
