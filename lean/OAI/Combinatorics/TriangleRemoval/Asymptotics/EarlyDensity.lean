import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.OneAddLogRpow
import OAI.Combinatorics.TriangleRemoval.Asymptotics.RelativeScaleBudgetLog

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

noncomputable def earlyDensity (n i : ℕ) : ℝ :=
  1-1/(n : ℝ)-6*(i : ℝ)/(n : ℝ)^2

@[simp] lemma earlyDensity_prefix (n : ℕ) :
    earlyDensity n (prefixTime n) = prefixDensity n := rfl

lemma earlyDensity_antitone (n : ℕ) : Antitone (earlyDensity n) := by
  intro i j hij
  unfold earlyDensity
  have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact sub_le_sub_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by norm_num)) (sq_nonneg (n : ℝ))) _

lemma earlyDensity_succ (n i : ℕ) :
    earlyDensity n i = earlyDensity n (i+1)+6/(n : ℝ)^2 := by
  unfold earlyDensity
  push_cast
  ring

lemma prefixDensity_eventually_inverse_lower : ∀ᶠ n : ℕ in atTop,
    1/(n : ℝ) ≤ prefixDensity n := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  apply le_trans _ hn.1
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)

noncomputable def earlyTemplateScale (a b n i : ℕ) : ℝ :=
  (n : ℝ)^a * earlyDensity n i ^ b

theorem earlyTemplateScale_regular (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
    (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) := by
  have hi : Tendsto (fun n : ℕ => 6/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (1+6/(n : ℝ))^b) atTop (𝓝 1) := by
    simpa only [add_zero,one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).add hi).pow b
  filter_upwards [prefixDensity_eventually_inverse_lower,
    hlim.eventually_le_const (by norm_num : (1 : ℝ) < 2),
    eventually_ge_atTop (1 : ℕ)] with n hp hratio hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow : ∀ i ≤ prefixTime n, 1/(n : ℝ) ≤ earlyDensity n i := by
    intro i hi
    exact hp.trans (earlyDensity_antitone n hi)
  have hpos : ∀ i ≤ prefixTime n, 0 < earlyDensity n i := by
    intro i hi
    exact lt_of_lt_of_le (by positivity) (hlow i hi)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact mul_pos (pow_pos hn0 _) (pow_pos (hpos i hi) _)
  · intro i hi
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos (i+1) (by omega)).le
      (earlyDensity_antitone n (Nat.le_succ i)) b) (by positivity)
  · intro i hi
    have hp1 : 0 < earlyDensity n (i+1) := hpos (i+1) (by omega)
    have hstep : earlyDensity n i ≤ earlyDensity n (i+1)*(1+6/(n : ℝ)) := by
      rw [earlyDensity_succ n i]
      have hh := hlow (i+1) (by omega)
      have hhmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 6/(n : ℝ) by positivity)
      have he : (6/(n : ℝ))*(1/(n : ℝ)) = 6/(n : ℝ)^2 := by ring
      rw [he] at hhmul
      nlinarith only [hhmul]
    have hpw := pow_le_pow_left₀ (hpos i (by omega)).le hstep b
    rw [mul_pow] at hpw
    unfold earlyTemplateScale
    calc
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*(1+6/(n : ℝ))^b) :=
        mul_le_mul_of_nonneg_left hpw (by positivity)
      _ ≤ (n : ℝ)^a * (earlyDensity n (i+1)^b*2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio (by positivity))
          (by positivity)
      _ = _ := by ring

theorem earlyTemplateScale_log_budget (a b : ℕ) : ∀ᶠ n : ℕ in atTop,
    relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤
      2*(b : ℝ)*Real.log n := by
  filter_upwards [earlyTemplateScale_regular a b,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hreg hlow hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hlow
  have hscale : earlyTemplateScale a b n 0/earlyTemplateScale a b n (prefixTime n) ≤
      (n : ℝ)^b := by
    unfold earlyTemplateScale
    rw [earlyDensity_prefix,mul_div_mul_left _ _ (ne_of_gt (pow_pos hn0 a)),← div_pow]
    apply pow_le_pow_left₀ (div_nonneg (by
      have hh := (earlyDensity_antitone n (Nat.zero_le (prefixTime n)))
      change prefixDensity n ≤ earlyDensity n 0 at hh
      linarith) hp.le)
    apply (div_le_iff₀ hp).mpr
    have hp' := (div_le_iff₀ hn0).mp hlow
    have hzero : earlyDensity n 0 ≤ 1 := by unfold earlyDensity; simp
    nlinarith only [hp',hzero]
  have hlog := Real.log_le_log
    (div_pos (hreg.1 0 (Nat.zero_le _)) (hreg.1 (prefixTime n) le_rfl)) hscale
  rw [Real.log_pow] at hlog
  exact (relativeScaleBudget_le_log (earlyTemplateScale a b n) (prefixTime n)
    hreg.1 hreg.2.1 hreg.2.2).trans (by nlinarith only [hlog])

end SharpTerminalLeave

end

end OAI
