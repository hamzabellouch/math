import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedCompletionMax
import OAI.Combinatorics.TriangleRemoval.Tracking.BalancedJump
import OAI.Combinatorics.TriangleRemoval.Process.TriangleIndex

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma triangle_noise_jump_budget : ∀ᶠ n : ℕ in atTop,
    ∀ i < prefixTime n, 3*triangleNoiseLoad n i/earlyTriangleScale n (i+1) ≤ balancedJump n := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ)^(1999/2000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1999/2000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [earlyTriangleScale_regular,prefixDensity_eventually_inverse_lower,
    hg.eventually_ge_atTop 72,eventually_ge_atTop (1 : ℕ)] with n hr hp hg hn
  intro i hi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp0 := early_density_positive (by omega) hp hi.le
  have hmin : 1/(n : ℝ) ≤ earlyDensity n i := hp.trans (earlyDensity_antitone n hi.le)
  have hratio := hr.2.2.1 i hi
  have hS := hr.1 i hi.le
  have hS' := hr.1 (i+1) (by omega)
  have hD : 0 ≤ earlyTemplateScale 1 2 n i := by unfold earlyTemplateScale; positivity
  have h₁ : 3*triangleNoiseLoad n i/earlyTriangleScale n (i+1) ≤
      12*earlyTemplateScale 1 2 n i/earlyTriangleScale n i := by
    apply (div_le_div_iff₀ hS' hS).mpr
    have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 6*earlyTemplateScale 1 2 n i by positivity)
    dsimp only [triangleNoiseLoad]
    nlinarith only [hh]
  have he : 12*earlyTemplateScale 1 2 n i/earlyTriangleScale n i =
      72/(n : ℝ)^2/earlyDensity n i := by
    unfold earlyTemplateScale earlyTriangleScale earlyTemplateScale
    field_simp
    ring
  rw [he] at h₁
  have h₂ : 72/(n : ℝ)^2/earlyDensity n i ≤ 72/(n : ℝ) := by
    apply (div_le_iff₀ hp0).mpr
    have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 72/(n : ℝ) by positivity)
    convert hh using 1
    field_simp
  have h₃ : 72/(n : ℝ) ≤ balancedJump n := by
    have hh := div_le_div_of_nonneg_right hg hn0.le
    apply hh.trans_eq
    unfold balancedJump
    calc
      (n : ℝ)^(1999/2000 : ℝ)/(n : ℝ) = (n : ℝ)^(1999/2000 : ℝ)/(n : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ)^(-1/2000 : ℝ) := by rw [← Real.rpow_sub hn0]; norm_num
  exact h₁.trans (h₂.trans h₃)

theorem prefix_triangle_noise_single : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixTriangleNoise n ω then 0 else 1) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
  filter_upwards [earlyTriangleScale_regular,triangle_noise_jump_budget,
    balanced_noise_exponent_budget 3,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (2 : ℕ)] with n hr hj hexp hp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hc : 0 < balancedJump n := Real.rpow_pos_of_pos hn0 _
  have hnoise : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hL : ∀ i < prefixTime n, 0 ≤ triangleNoiseLoad n i := by
    intro i hi
    unfold triangleNoiseLoad earlyTemplateScale
    positivity
  have ht := triangle_relative_template_self_bounded_tail (triangleRequired (n := n))
    (completeGraph n) (prefixTime n) (triangleNoiseLoad n) (earlyTriangleScale n)
    (balancedJump n) 2 hc (by norm_num) hr.1 hr.2.1 hL hj (codegreeNoiseRadius n) hnoise
  have ht' : pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixTriangleNoise n ω then 0 else 1) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp
      (-codegreeNoiseRadius n^2/(4*(balancedJump n*(copyCount (triangleRequired (n := n))
        (completeGraph n)/earlyTriangleScale n 0+2*relativeScaleBudget (earlyTriangleScale n) (prefixTime n)+
          codegreeNoiseRadius n+balancedJump n)+balancedJump n*codegreeNoiseRadius n))) := by
    convert ht using 1
    apply congrArg (pmfMean _)
    funext ω
    unfold PrefixTriangleNoise RelativeNoiseExit
    split_ifs <;> simp_all
  apply ht'.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  apply hexp.trans
  apply div_le_div_of_nonneg_left (sq_nonneg _)
  · have hscale : 0 ≤ copyCount (triangleRequired (n := n)) (completeGraph n)/earlyTriangleScale n 0 :=
      div_nonneg (copyCount_nonneg _ _) (hr.1 0 (Nat.zero_le _)).le
    have hbudget := relativeScaleBudget_nonneg (earlyTriangleScale n) (prefixTime n) hr.1 hr.2.1
    positivity
  · have hi := initial_triangle_ratio_le_two hn
    have hbgt := hr.2.2.2
    have hh := mul_le_mul_of_nonneg_left (show copyCount (triangleRequired (n := n)) (completeGraph n)/earlyTriangleScale n 0+
        2*relativeScaleBudget (earlyTriangleScale n) (prefixTime n)+codegreeNoiseRadius n+balancedJump n ≤
        2+4*(3 : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n by
          nlinarith only [hi,hbgt,Real.log_nonneg hn1]) hc.le
    norm_num only [Nat.cast_ofNat] at hexp ⊢
    linarith only [hh]

theorem prefix_triangle_noise_failure : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixTriangleNoise n ω then 0 else 1) ≤
      Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_triangle_noise_single,polynomial_logsquare_le_prefix_margin 4 2,
    eventually_ge_atTop (1 : ℕ)] with n ht hb hn
  apply ht.trans
  have htime : 2*(prefixTime n+1 : ℝ) ≤ 4*(n : ℝ)^2 := by
    have ht : (prefixTime n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast prefixTime_le_square n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [ht,hn1]
  apply (mul_le_mul_of_nonneg_right htime (Real.exp_pos _).le).trans
  simpa only [Real.rpow_two] using hb

end SharpTerminalLeave
end
end

end OAI
