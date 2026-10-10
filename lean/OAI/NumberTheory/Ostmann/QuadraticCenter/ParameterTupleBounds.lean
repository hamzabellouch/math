import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterMomentBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

lemma tuple_prime_band_product_bounds {k Z : ℕ} (q : Fin k → ℕ)
    (hq : ∀ i, Z ≤ q i ∧ q i ≤ 2 * Z) :
    Z ^ k ≤ ∏ i, q i ∧ (∏ i, q i) ≤ (2 * Z) ^ k := by
  constructor
  · simpa using Finset.pow_card_le_prod (Finset.univ : Finset (Fin k)) q Z (fun i _ => (hq i).1)
  · simpa using Finset.prod_le_pow_card (Finset.univ : Finset (Fin k)) q (2 * Z) (fun i _ => (hq i).2)

lemma tuple_scale_of_log_bounds (X Z M k : ℕ) (hX : 0 < X) (hZ : 0 < Z)
    (hlogZ : 0 < Real.log Z)
    (hkl : Real.log X / Real.log Z + 10 ≤ (k : ℝ))
    (hku : (k : ℝ) ≤ Real.log X / Real.log Z + 12)
    (hks : (k : ℝ) * Real.log 2 ≤ Real.log Z)
    (hMl : Z ^ k ≤ M) (hMu : M ≤ (2 * Z) ^ k) :
    (Z : ℝ) ^ 10 ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ (Z : ℝ) ^ 13 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hZr : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hklo : Real.log X + 10 * Real.log Z ≤ (k : ℝ) * Real.log Z := by
    have hm := mul_le_mul_of_nonneg_right hkl hlogZ.le
    have hid : Real.log X / Real.log Z * Real.log Z = Real.log X :=
      div_mul_cancel₀ _ hlogZ.ne'
    nlinarith
  have hkup : (k : ℝ) * Real.log Z ≤ Real.log X + 12 * Real.log Z := by
    have hm := mul_le_mul_of_nonneg_right hku hlogZ.le
    have hid : Real.log X / Real.log Z * Real.log Z = Real.log X :=
      div_mul_cancel₀ _ hlogZ.ne'
    nlinarith
  have hp (n : ℕ) : Real.exp ((n : ℝ) * Real.log Z) = (Z : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log hZr]
  have hp10 := hp 10
  have hp13 := hp 13
  norm_num only [Nat.cast_ofNat] at hp10 hp13
  have helo : (X : ℝ) * (Z : ℝ) ^ 10 ≤ (Z : ℝ) ^ k := by
    have h := Real.exp_le_exp.mpr hklo
    simpa only [Real.exp_add, Real.exp_log hXr, hp10, hp] using h
  have hkhi : (k : ℝ) * Real.log (2 * (Z : ℝ)) ≤ Real.log X + 13 * Real.log Z := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZr.ne']
    nlinarith
  have hehi : (2 * (Z : ℝ)) ^ k ≤ (X : ℝ) * (Z : ℝ) ^ 13 := by
    have h := Real.exp_le_exp.mpr hkhi
    simpa only [Real.exp_add, Real.exp_log hXr, hp13, hp, Real.exp_nat_mul,
      Real.exp_log (mul_pos (by norm_num : (0 : ℝ) < 2) hZr)] using h
  have hmlo : (Z : ℝ) ^ k ≤ M := by exact_mod_cast hMl
  have hmhi : (M : ℝ) ≤ (2 * (Z : ℝ)) ^ k := by exact_mod_cast hMu
  constructor
  · apply (le_div_iff₀ hXr).mpr
    nlinarith
  · apply (div_le_iff₀ hXr).mpr
    nlinarith

theorem eventually_tuple_product_scale :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T / 2 ≤ Real.log Z →
      ∀ q : Fin (evenMomentParameter (parameterX T) Z) → ℕ,
        (∀ i, Z ≤ q i ∧ q i ≤ 2 * Z) →
        (Z : ℝ) ^ 10 ≤ ((∏ i, q i : ℕ) : ℝ) / parameterX T ∧
          ((∏ i, q i : ℕ) : ℝ) / parameterX T ≤ (Z : ℝ) ^ 13 := by
  filter_upwards [eventually_parameterX_log_bounds, eventually_evenMomentParameter_bound,
    parameterX_tendsto.eventually_gt_atTop 0,
    eventually_mul_rpow_le_rpow (28 * Real.log 2) (a := 3 / 5) (b := 1) (by norm_num)]
    with T hX hk hXpos hg
  intro Z hZ q hq
  have hT : 0 < T := by linarith [hX.1]
  have hlogZ : 0 < Real.log Z := by linarith
  have hZr : (0 : ℝ) < Z := lt_trans (by norm_num) ((Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ)
  have hZn : 0 < Z := by exact_mod_cast hZr
  have hkspan := evenMomentParameter_bounds (parameterX T) Z
    (show 0 ≤ Real.log (parameterX T : ℝ) / Real.log Z + 10 by
      have : 0 ≤ Real.log (parameterX T : ℝ) := by linarith [hX.2.1]
      positivity)
  have hsmall : (evenMomentParameter (parameterX T) Z : ℝ) * Real.log 2 ≤ Real.log Z := by
    have hm := mul_le_mul_of_nonneg_right (hk Z hZ) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    rw [Real.rpow_one] at hg
    nlinarith
  have hprod := tuple_prime_band_product_bounds q hq
  exact tuple_scale_of_log_bounds (parameterX T) Z _ _ hXpos hZn hlogZ
    hkspan.1 hkspan.2.le hsmall hprod.1 hprod.2

end Ostmann.QuadraticCenter

end

end OAI
