import OAI.NumberTheory.Ostmann.Supply.CollisionLogImbalance
import OAI.NumberTheory.Ostmann.Construction.TailBudgetNegligible

namespace OAI

/-! # Numerical specialization of the subset-sieve budgets -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem rpow_three_quarters_sq {L : ℝ} (hL : 0 < L) :
    (L ^ (3 / 4 : ℝ)) ^ 2 = L * Real.sqrt L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  norm_num only [Nat.cast_ofNat, mul_div_cancel_right₀]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hL, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem eventual_square_budget_le_three_quarters (K : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, W ^ 2 ≤ K * L →
      W ≤ L ^ (3 / 4 : ℝ) / 16 := by
  have hlarge := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop
    (256 * max K 0)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℝ)] with L hlarge hL W hW
  have hLp : 0 < L := by linarith
  rw [← Real.sqrt_eq_rpow] at hlarge
  have hs : K * L ≤ (L ^ (3 / 4 : ℝ) / 16) ^ 2 := by
    rw [div_pow, rpow_three_quarters_sq hLp]
    norm_num only [show (16 : ℝ) ^ 2 = 256 by norm_num]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlarge hLp.le, le_max_left K 0]
  exact le_of_sq_le_sq (hW.trans hs) (by positivity)

theorem finite_prime_reciprocal_mass_le (P : Finset ℕ) (L a : ℝ)
    (hP : ∀ p ∈ P, 0 < p ∧ a * L ≤ Real.log (p : ℝ)) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (P.card : ℝ) * Real.exp (-a * L) := by
  calc
    _ ≤ ∑ _p ∈ P, Real.exp (-a * L) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1
      have he : (p : ℝ)⁻¹ = Real.exp (-Real.log (p : ℝ)) := by
        rw [Real.exp_neg, Real.exp_log hp0]
      rw [he]
      apply Real.exp_le_exp.mpr
      linarith [(hP p hp).2]
    _ = _ := by simp

theorem eventual_small_subset_reciprocal (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ,
      (P.card : ℝ) ≤ c * L →
      (∀ p ∈ P, 0 < p ∧ a * L ≤ Real.log (p : ℝ)) →
      (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 / 16 := by
  have hsmall := ((isLittleO_pow_exp_pos_mul_atTop 1 ha).const_mul_left c).bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with L hsmall hL P hcard hP
  have hLp : 0 < L := by linarith
  have hbound : c * L ≤ (1 / 16 : ℝ) * Real.exp (a * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hLp.le),
      abs_of_pos (Real.exp_pos _)] using hsmall
  calc
    _ ≤ (P.card : ℝ) * Real.exp (-a * L) := finite_prime_reciprocal_mass_le P L a hP
    _ ≤ (c * L) * Real.exp (-a * L) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ ≤ ((1 / 16 : ℝ) * Real.exp (a * L)) * Real.exp (-a * L) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    _ = 1 / 16 := by
      rw [mul_assoc, ← Real.exp_add]
      simp

end Ostmann

end OAI
