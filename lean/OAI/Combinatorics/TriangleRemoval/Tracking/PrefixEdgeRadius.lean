import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.EarlyDensityOne
import OAI.Combinatorics.TriangleRemoval.Asymptotics.DensityEdgeSafe

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter
open Classical

namespace SharpTerminalLeave

noncomputable def prefixEdgeRadius (n : ℕ) : ℝ := (n : ℝ)^(-1/40000 : ℝ)

lemma early_density_positive {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) {i : ℕ} (hi : i ≤ prefixTime n) :
    0 < earlyDensity n i := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (hp.trans (earlyDensity_antitone n hi))

lemma early_density_log_bound {n i : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i ≤ prefixTime n) :
    -Real.log (earlyDensity n i) ≤ Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : Real.log (1/(n : ℝ)) ≤ Real.log (earlyDensity n i) :=
    Real.log_le_log (by positivity) (hp.trans (earlyDensity_antitone n hi))
  rw [one_div,Real.log_inv] at hh
  linarith

lemma early_density_survival_budget {n i : ℕ} (hn : 2 ≤ n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hi : i ≤ prefixTime n)
    {b η : ℝ} (hb : 0 ≤ b) (hη : 0 ≤ η) :
    b*(1-earlyDensity n 0)/earlyDensity n 0+b*(6/(n : ℝ)^2)/earlyDensity n i+
      2*b*η*(-Real.log (earlyDensity n i))+b^2/(n*earlyDensity n i^2) ≤
        8*b/(n : ℝ)+2*b*η*Real.log n+b^2/prefixD n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hp0 : 0 < earlyDensity n 0 := early_density_positive (by omega) hp (Nat.zero_le _)
  have hpi := early_density_positive (by omega) hp hi
  have hpT : 0 < prefixDensity n := early_density_positive (by omega) hp le_rfl
  have hlow : 1/(n : ℝ) ≤ earlyDensity n i := hp.trans (earlyDensity_antitone n hi)
  have hab : b*(1-earlyDensity n 0)/earlyDensity n 0 ≤ 2*b/(n : ℝ) := by
    have hz : earlyDensity n 0 = 1-1/(n : ℝ) := by simp [earlyDensity]
    have hhalf : (1 : ℝ)/2 ≤ earlyDensity n 0 := by
      rw [hz]
      have hinv : 1/(n : ℝ) ≤ 1/2 := (div_le_div_iff₀ hn0 (by norm_num)).mpr (by linarith)
      linarith
    apply (div_le_iff₀ hp0).mpr
    rw [hz]
    have hm := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*b/(n : ℝ) by positivity)
    rw [hz] at hm
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm]
  have hdisc : b*(6/(n : ℝ)^2)/earlyDensity n i ≤ 6*b/(n : ℝ) := by
    calc
      _ ≤ b*(6/(n : ℝ)^2)/(1/(n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
      _ = _ := by field_simp
  have hlog : 2*b*η*(-Real.log (earlyDensity n i)) ≤ 2*b*η*Real.log n :=
    mul_le_mul_of_nonneg_left (early_density_log_bound (by omega) hp hi) (by positivity)
  have hlast : b^2/(n*earlyDensity n i^2) ≤ b^2/prefixD n := by
    apply div_le_div_of_nonneg_left (sq_nonneg b) (by unfold prefixD; positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hpT.le (earlyDensity_antitone n hi) 2) hn0.le
  simp only [div_eq_mul_inv] at hab hdisc hlog hlast ⊢
  linarith only [hab,hdisc,hlog,hlast]

lemma prefix_survival_budget_small : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    ∀ b : ℝ, 0 ≤ b → b ≤ (n : ℝ)^(1/200000 : ℝ) →
      8*b/(n : ℝ)+2*b*prefixEdgeRadius n*Real.log n+b^2/prefixD n ≤ 1 := by
  have hlim : Tendsto (fun n : ℕ =>
      8*(n : ℝ)^(-1/2 : ℝ)+2*(n : ℝ)^(-1/100000 : ℝ)+(n : ℝ)^(-1/2000 : ℝ))
      atTop (nhds 0) := by
    have ha := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
    have hb := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100000)).comp tendsto_natCast_atTop_atTop
    have hc := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2000)).comp tendsto_natCast_atTop_atTop
    convert ((ha.const_mul 8).add (hb.const_mul 2)).add hc using 1 <;> norm_num
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/40000)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/200000) zero_lt_one,
    prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hlim hrad hlog hD hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlog' : Real.log (n : ℝ) ≤ (n : ℝ)^(1/200000 : ℝ) := by
    simp only [prefixTemplateFactor,Real.rpow_one,one_mul] at hlog
    linarith
  refine ⟨Real.rpow_nonneg hn0.le _,hrad,?_⟩
  intro b hb hbhigh
  have hfirst : b/(n : ℝ) ≤ (n : ℝ)^(-1/2 : ℝ) := by
    calc
      _ ≤ (n : ℝ)^(1/200000 : ℝ)/(n : ℝ) := div_le_div_of_nonneg_right hbhigh hn0.le
      _ = (n : ℝ)^((1/200000 : ℝ)-1) := by rw [Real.rpow_sub hn0,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hmiddle : b*prefixEdgeRadius n*Real.log n ≤ (n : ℝ)^(-1/100000 : ℝ) := by
    calc
      _ ≤ ((n : ℝ)^(1/200000 : ℝ)*(n : ℝ)^(-1/40000 : ℝ))*(n : ℝ)^(1/200000 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbhigh (Real.rpow_nonneg hn0.le _))
          hlog' hlog0 (by positivity)
      _ = (n : ℝ)^((1/200000 : ℝ)-1/40000+1/200000) := by
        rw [← Real.rpow_add hn0,← Real.rpow_add hn0]; congr 1; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hlast : b^2/prefixD n ≤ (n : ℝ)^(-1/2000 : ℝ) := by
    calc
      _ ≤ ((n : ℝ)^(1/200000 : ℝ))^2/(n : ℝ)^(1/1000 : ℝ) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ hb hbhigh 2) (by positivity) hD.1
      _ = (n : ℝ)^((1/200000 : ℝ)*2-1/1000) := by
        rw [← Real.rpow_mul_natCast hn0.le,Real.rpow_sub hn0]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  simp only [div_eq_mul_inv] at hfirst hlast ⊢
  nlinarith only [hlim,hfirst,hmiddle,hlast]

theorem prefix_killed_survival : ∀ᶠ n : ℕ in atTop,
    ∀ j ≤ prefixTime n, ∀ F : Graph n, (F.card : ℝ) ≤ (n : ℝ)^(1/200000 : ℝ) →
      pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) j)
        (fun ω => if historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
          (prefixTime n) j ω then intact F (ω (historyIndex (prefixTime n) j)) else 0) ≤
      Real.exp 1 * earlyDensity n j^F.card := by
  filter_upwards [prefix_survival_budget_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (2 : ℕ)] with n hbudget hp hn
  intro j hj F hF
  have hk := density_killed_survival (PMF.pure (completeGraph n)) (earlyDensity n)
    (prefixEdgeRadius n) (prefixTime n) j hj (by omega)
    (fun i hi => early_density_positive (by omega) hp hi)
    (fun i _ => earlyDensity_succ n i) (earlyDensity_le_one n 0) hbudget.1 hbudget.2.1 F
  apply hk.trans
  rw [mul_comm (Real.exp 1)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (early_density_positive (by omega) hp hj).le _)
  apply Real.exp_le_exp.mpr
  exact (early_density_survival_budget hn hp hj (Nat.cast_nonneg _) hbudget.1).trans
    (hbudget.2.2 F.card (Nat.cast_nonneg _) hF)

end SharpTerminalLeave
end
end

end OAI
