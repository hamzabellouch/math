import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedTemplateEdgesCard
import OAI.Combinatorics.TriangleRemoval.Process.RelativeNoiseExit
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeVertexCount
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeNoiseRadius
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEdgeRadius

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma earlyTemplateScale_uniform_regular (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ a ≤ H, ∀ b ≤ H^2,
      (∀ i ≤ prefixTime n, 0 < earlyTemplateScale a b n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale a b n (i+1) ≤ earlyTemplateScale a b n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale a b n i ≤ 2*earlyTemplateScale a b n (i+1)) ∧
      relativeScaleBudget (earlyTemplateScale a b n) (prefixTime n) ≤ 2*(b : ℝ)*Real.log n := by
  have hh : ∀ z : Fin (H+1) × Fin (H^2+1), ∀ᶠ n : ℕ in atTop,
      (∀ i ≤ prefixTime n, 0 < earlyTemplateScale z.1.val z.2.val n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale z.1.val z.2.val n (i+1) ≤ earlyTemplateScale z.1.val z.2.val n i) ∧
      (∀ i < prefixTime n, earlyTemplateScale z.1.val z.2.val n i ≤ 2*earlyTemplateScale z.1.val z.2.val n (i+1)) ∧
      relativeScaleBudget (earlyTemplateScale z.1.val z.2.val n) (prefixTime n) ≤ 2*(z.2.val : ℝ)*Real.log n := by
    intro z
    filter_upwards [earlyTemplateScale_regular z.1.val z.2.val,
      earlyTemplateScale_log_budget z.1.val z.2.val] with n hr hb
    exact ⟨hr.1,hr.2.1,hr.2.2,hb⟩
  filter_upwards [Filter.eventually_all.mpr hh] with n hn
  intro a ha b hb
  exact hn (⟨a,by omega⟩,⟨b,by omega⟩)

noncomputable def balancedJump (n : ℕ) : ℝ := (n : ℝ)^(-1/2000 : ℝ)
noncomputable def balancedLoad (H : ℕ) {k : ℕ} (T : RootedTemplate k) (n i : ℕ) : ℝ :=
  4*(T.edges.card : ℝ)*(1+Real.log (n : ℝ))^(3*H+2)*
    rootedScaling T n (earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)

lemma balanced_jump_budget (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    24*(H : ℝ)^2*(1+Real.log (n : ℝ))^(3*H+2)/prefixD n ≤ balancedJump n := by
  have hc : 0 < 1/(24*(H : ℝ)^2+1) := by positivity
  filter_upwards [prefixTemplateFactor_subpower ((3*H+2 : ℕ) : ℝ) (by norm_num : (0 : ℝ) < 1/2000) hc,
    prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hb hd hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ 1+Real.log (n : ℝ) := by have := Real.log_nonneg hn1; linarith
  have hb' : (1+Real.log (n : ℝ))^(3*H+2 : ℕ) ≤
      1/(24*(H : ℝ)^2+1)*(n : ℝ)^(1/2000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_natCast] using hb
  have hcoef : 24*(H : ℝ)^2/(24*(H : ℝ)^2+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr; linarith
  have hnum : 24*(H : ℝ)^2*(1+Real.log (n : ℝ))^(3*H+2) ≤ (n : ℝ)^(1/2000 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 24*(H : ℝ)^2 by positivity)
    have he := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn0.le (1/2000 : ℝ))
    ring_nf at hh he ⊢
    exact hh.trans he
  calc
    _ ≤ (n : ℝ)^(1/2000 : ℝ)/(n : ℝ)^(1/1000 : ℝ) :=
      div_le_div₀ (by positivity) hnum (by positivity) hd.1
    _ = _ := by unfold balancedJump; rw [← Real.rpow_sub hn0]; norm_num

lemma rooted_initial_ratio_le_two (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      rootedCount T ψ (completeGraph n)/rootedScaling T n (earlyDensity n 0) ≤ 2 := by
  let C : ℝ := (2 : ℝ)^(H^2)*(2*(H : ℝ)^2)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop C,
    eventually_ge_atTop H,eventually_ge_atTop (2 : ℕ)] with n hC hn hn2
  intro k hk T ψ
  have hh := rootedCount_initial_uniform_error H hk hn hn2 T ψ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdiv : C/(n : ℝ) ≤ 1 := (div_le_one hnR).mpr hC
  have he : earlyDensity n 0 = 1-1/(n : ℝ) := by simp [earlyDensity]
  rw [he]
  have hp := (abs_le.mp hh).2
  change _ ≤ C/(n : ℝ) at hp
  linarith only [hp,hdiv]

lemma balanced_noise_exponent_budget (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    (Real.log (n : ℝ))^2/4 ≤ codegreeNoiseRadius n^2/
      (4*(balancedJump n*(2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n)+
        balancedJump n*codegreeNoiseRadius n)) := by
  let C : ℝ := 20+16*(H : ℝ)^2
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/10000) (one_div_pos.mpr hC),
    prefixTemplateFactor_subpower 2 (by norm_num : (0 : ℝ) < 1/5000) (by norm_num : (0 : ℝ) < 4),
    eventually_ge_atTop (1 : ℕ)] with n hp hl hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hr : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hc : 0 < balancedJump n := Real.rpow_pos_of_pos hn0 _
  have hr1 : codegreeNoiseRadius n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hc1 : balancedJump n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  let d := 4*(balancedJump n*(2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n)+
    balancedJump n*codegreeNoiseRadius n)
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hd : d ≤ (n : ℝ)^(-1/2500 : ℝ) := by
    have hp' : 1+Real.log (n : ℝ) ≤ (1/C)*(n : ℝ)^(1/10000 : ℝ) := by
      simpa only [prefixTemplateFactor,Real.rpow_one] using hp
    have hh := mul_le_mul_of_nonneg_left hp' hC.le
    simp only [← mul_assoc,mul_one_div_cancel hC.ne',one_mul] at hh
    have hbracket : 4*(2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n+codegreeNoiseRadius n) ≤
        C*(1+Real.log (n : ℝ)) := by dsimp [C]; nlinarith only [hr1,hc1,hlog,sq_nonneg (H : ℝ)]
    have hm := mul_le_mul_of_nonneg_left (hbracket.trans hh) hc.le
    have he : balancedJump n*(n : ℝ)^(1/10000 : ℝ) = (n : ℝ)^(-1/2500 : ℝ) := by
      unfold balancedJump; rw [← Real.rpow_add hn0]; norm_num
    rw [he] at hm
    dsimp only [d]
    nlinarith only [hm]
  have hr2 : codegreeNoiseRadius n^2 = (n : ℝ)^(-1/5000 : ℝ) := by
    unfold codegreeNoiseRadius
    rw [← Real.rpow_mul_natCast hn0.le]; norm_num
  have hratio : (n : ℝ)^(1/5000 : ℝ) ≤ codegreeNoiseRadius n^2/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hn0.le (1/5000 : ℝ))
    rw [← Real.rpow_add hn0] at hh
    rw [hr2]
    convert hh using 1
    norm_num
  have hl' : (1+Real.log (n : ℝ))^2 ≤ 4*(n : ℝ)^(1/5000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_two] using hl
  exact (show (Real.log (n : ℝ))^2/4 ≤ (n : ℝ)^(1/5000 : ℝ) by nlinarith only [hl',hlog]).trans hratio

theorem prefix_balanced_noise_single (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if RelativeNoiseExit (fun φ : RootedInjection T ψ => imageEdges T φ.val)
        (balancedLoad H T n) (earlyTemplateScale (k-T.roots.card) T.edges.card n) 2
        (codegreeNoiseRadius n) (prefixTime n) ω then 1 else 0) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
  filter_upwards [earlyTemplateScale_uniform_regular H,balanced_jump_budget H,
    rooted_initial_ratio_le_two H,balanced_noise_exponent_budget H,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (1 : ℕ)] with n hreg hjump hinit hexp hp hn
  intro k hk T ψ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hln : 0 ≤ 1+Real.log (n : ℝ) := by have := Real.log_nonneg hn1; linarith
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans (Nat.pow_le_pow_left hk 2)
  have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
  have hr := hreg (k-T.roots.card) ((Nat.sub_le _ _).trans hk) T.edges.card hb
  let s := earlyTemplateScale (k-T.roots.card) T.edges.card n
  have hD : 0 < prefixD n := by unfold prefixD; have hh : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hp; positivity
  have hc : 0 < balancedJump n := Real.rpow_pos_of_pos hn0 _
  have hnoise : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hL : ∀ i < prefixTime n, 0 ≤ balancedLoad H T n i := by
    intro i hi
    have hpi := early_density_positive (by omega) hp hi.le
    unfold balancedLoad rootedScaling
    positivity
  have hJ : ∀ i < prefixTime n, 3*balancedLoad H T n i/s (i+1) ≤ balancedJump n := by
    intro i hi
    have hsi := hr.1 (i+1) (by omega)
    have hpi := early_density_positive (by omega) hp hi.le
    have hDi : prefixD n ≤ (n : ℝ)*earlyDensity n i^2 := by
      simpa only [earlyTemplateScale,pow_one] using earlyCodegreeScale_ge_prefixD n i hi.le (le_trans (by positivity) hp)
    have hratio := hr.2.2.1 i hi
    have hcoeff : 0 ≤ 12*(T.edges.card : ℝ)*(1+Real.log (n : ℝ))^(3*H+2)/((n : ℝ)*earlyDensity n i^2) := by positivity
    have hm := mul_le_mul_of_nonneg_left hratio hcoeff
    have hstep : 3*balancedLoad H T n i/s (i+1) ≤
        24*(T.edges.card : ℝ)*(1+Real.log (n : ℝ))^(3*H+2)/((n : ℝ)*earlyDensity n i^2) := by
      apply (div_le_iff₀ hsi).mpr
      dsimp only [balancedLoad,rootedScaling,s,earlyTemplateScale] at hm ⊢
      convert hm using 1 <;> ring
    apply hstep.trans (_root_.le_trans _ hjump)
    apply div_le_div₀ (by positivity) _ hD hDi
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbR (by norm_num)) (by positivity)
  have ht := triangle_relative_template_self_bounded_tail
    (fun φ : RootedInjection T ψ => imageEdges T φ.val) (completeGraph n) (prefixTime n)
    (balancedLoad H T n) s (balancedJump n) 2 hc (by norm_num) hr.1 hr.2.1 hL hJ
    (codegreeNoiseRadius n) hnoise
  refine (show _ ≤ 2*(prefixTime n+1 : ℝ)*Real.exp
    (-codegreeNoiseRadius n^2/(4*(balancedJump n*(copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (completeGraph n)/s 0+2*relativeScaleBudget s (prefixTime n)+codegreeNoiseRadius n+balancedJump n)+
      balancedJump n*codegreeNoiseRadius n))) from ?_).trans ?_
  · convert ht using 1
    apply congrArg (pmfMean _)
    funext ω
    unfold RelativeNoiseExit
    split_ifs <;> rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  apply hexp.trans
  apply div_le_div_of_nonneg_left (sq_nonneg _)
  · have hscale : 0 ≤ copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) (completeGraph n)/s 0 :=
      div_nonneg (copyCount_nonneg _ _) (hr.1 0 (Nat.zero_le _)).le
    have hbudget := relativeScaleBudget_nonneg s (prefixTime n) hr.1 hr.2.1
    positivity
  · have hi := hinit k hk T ψ
    change copyCount _ (completeGraph n)/s 0 ≤ 2 at hi
    have hbgt : relativeScaleBudget s (prefixTime n) ≤ 2*(H : ℝ)^2*Real.log n :=
      hr.2.2.2.trans (by nlinarith only [mul_le_mul_of_nonneg_right hbR (Real.log_nonneg hn1)])
    have hh := mul_le_mul_of_nonneg_left (show copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) (completeGraph n)/s 0+
        2*relativeScaleBudget s (prefixTime n)+codegreeNoiseRadius n+balancedJump n ≤
        2+4*(H : ℝ)^2*Real.log n+codegreeNoiseRadius n+balancedJump n by linarith only [hi,hbgt]) hc.le
    linarith only [hh]

end SharpTerminalLeave
end
end

end OAI
