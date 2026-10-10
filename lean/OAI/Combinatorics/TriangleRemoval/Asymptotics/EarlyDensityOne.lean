import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.EarlyDensity

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma earlyDensity_le_one (n i : ℕ) : earlyDensity n i ≤ 1 := by
  unfold earlyDensity
  have h₁ : 0 ≤ 1/(n : ℝ) := by positivity
  have h₂ : 0 ≤ 6*(i : ℝ)/(n : ℝ)^2 := by positivity
  linarith

theorem earlyTemplateScale_balanced_lower (a b : ℕ) (hb : b ≤ 2*a) :
    ∀ᶠ n : ℕ in atTop, ∀ i ≤ prefixTime n,
      (n : ℝ)^((a : ℝ)/1000) ≤ earlyTemplateScale a b n i := by
  filter_upwards [prefixD_eventual_envelope, prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hD hp hn
  intro i hi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hp
  have hpi : prefixDensity n ≤ earlyDensity n i := earlyDensity_antitone n hi
  have hp0 : 0 ≤ earlyDensity n i := (hpp.trans_le hpi).le
  have hDi : prefixD n ≤ (n : ℝ)*earlyDensity n i^2 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpp.le hpi 2) hn0.le
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hn0.le (1/1000 : ℝ))
    (hD.1.trans hDi) a
  have he : ((n : ℝ)^(1/1000 : ℝ))^a = (n : ℝ)^((a : ℝ)/1000) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  rw [he,mul_pow] at hh
  apply hh.trans
  unfold earlyTemplateScale
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← pow_mul]
  exact pow_le_pow_of_le_one hp0 (earlyDensity_le_one n i) hb

theorem earlyTemplateScale_balanced_uniform_lower : ∀ᶠ n : ℕ in atTop,
    ∀ a b : ℕ, 1 ≤ a → b ≤ 2*a → ∀ i ≤ prefixTime n,
      (n : ℝ)^(1/1000 : ℝ) ≤ earlyTemplateScale a b n i := by
  filter_upwards [prefixD_eventual_envelope, prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hD hp hn
  intro a b ha hb i hi
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hpp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hp
  have hpi : prefixDensity n ≤ earlyDensity n i := earlyDensity_antitone n hi
  have hp0 : 0 ≤ earlyDensity n i := (hpp.trans_le hpi).le
  have hx : (n : ℝ)^(1/1000 : ℝ) ≤ (n : ℝ)*earlyDensity n i^2 :=
    hD.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpp.le hpi 2) hn0.le)
  have hx1 : 1 ≤ (n : ℝ)*earlyDensity n i^2 :=
    (Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hx
  apply hx.trans
  calc
    _ ≤ ((n : ℝ)*earlyDensity n i^2)^a := by
      simpa only [pow_one] using (pow_le_pow_right₀ hx1 ha)
    _ ≤ earlyTemplateScale a b n i := by
      rw [mul_pow,← pow_mul]
      unfold earlyTemplateScale
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hp0 (earlyDensity_le_one n i) hb) (by positivity)

end SharpTerminalLeave

end

end OAI
