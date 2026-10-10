import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleNoiseJumpBudget
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixPairClosureBudget

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Filter Classical

namespace SharpTerminalLeave

lemma normalized_tracking_absolute {X s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (h : |X/s-1| ≤ r/2) : |X-s| ≤ r*s := by
  rw [show X/s-1 = (X-s)/s by rw [sub_div,div_self hs.ne'],abs_div,abs_of_pos hs] at h
  exact ((div_le_iff₀ hs).mp h).trans (mul_le_mul_of_nonneg_right (by linarith only [hr]) hs.le)

theorem prefix_good_history : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    GoodPrefixGraph n (1/80000) (3*(8001 : ℕ)+2 : ℕ) (ω (historyIndex (prefixTime n) (prefixTime n))) := by
  filter_upwards [prefix_present_edge_closure,prefix_all_pair_closure,prefix_degree_wheel_tracking,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (1 : ℕ)] with n hedge hpair hwheel hp hn
  intro ω hω hroot hbalanced htri hnoise
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hedges := hedge ω hω hroot hbalanced htri hnoise
  have halive : historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
      (prefixTime n) (prefixTime n) ω := fun i hi => hedges i hi.le
  have he := hedges (prefixTime n) le_rfl
  have hw := hwheel ω hω hroot hbalanced (prefixTime n) le_rfl halive
  have hc := hpair ω hω hroot hbalanced htri hnoise (prefixTime n) le_rfl
  have hpp : 0 < prefixDensity n := (div_pos zero_lt_one hnR).trans_le hp
  have hr : 0 ≤ prefixWheelRadius n := Real.rpow_nonneg hnR.le _
  have hdeg := mul_pos hnR hpp
  have hD : 0 < prefixD n := mul_pos hnR (sq_pos_of_pos hpp)
  refine ⟨he.1,?_,?_,?_,?_,?_⟩
  · simpa only [earlyDensity_prefix,prefixM] using he.2.1
  · intro u
    have hh := hw.1 u
    rw [earlyDensity_prefix] at hh
    simpa only [prefixWheelRadius,neg_div] using normalized_tracking_absolute hdeg hr hh
  · intro u v huv
    have hh := hc u v huv
    simp only [prefixNormalizedCodegree,earlyTemplateScale,pow_one,earlyDensity_prefix] at hh
    simpa only [prefixD,prefixWheelRadius,neg_div] using normalized_tracking_absolute hD hr hh
  · intro j hj hj' u
    have hh := hw.2 j hj hj' u
    rw [earlyDensity_prefix] at hh
    simpa only [prefixD,prefixWheelRadius,neg_div] using normalized_tracking_absolute (pow_pos hD j) hr hh
  · intro k hk T ψ
    have hh := (hroot (prefixTime n) le_rfl halive k hk T ψ).le
    rw [earlyDensity_prefix] at hh
    have hfac : (1+Real.log (n : ℝ))^(3*8001+2) = prefixTemplateFactor n (3*(8001 : ℕ)+2 : ℕ) := by
      simp only [prefixTemplateFactor,Real.rpow_natCast]
    rw [hfac] at hh
    have hfac0 : 0 ≤ prefixTemplateFactor n (3*(8001 : ℕ)+2 : ℕ) := Real.rpow_nonneg (by have := Real.log_nonneg hn1; linarith) _
    constructor
    · intro hlarge
      exact hh.trans (mul_le_mul_of_nonneg_left (rootedCompletionMax_large T hpp.le hlarge) hfac0)
    · intro hsmall
      exact hh.trans ((mul_le_mul_of_nonneg_left (rootedCompletionMax_small T hsmall) hfac0).trans_eq (mul_one _))

lemma four_prefix_margins : ∀ᶠ n : ℕ in atTop,
    4*Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) ≤
      Real.exp (-(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^(4/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually (eventually_ge_atTop (Real.log 4))] with n hn
  have hh : (4 : ℝ) ≤ Real.exp ((Real.log (n : ℝ))^(4/3 : ℝ)) := by
    calc
      (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hn
  calc
    _ ≤ Real.exp ((Real.log (n : ℝ))^(4/3 : ℝ))*Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem uniform_prefix_obligation : UniformPrefixObligation := by
  refine ⟨1/80000,by norm_num,(3*(8001 : ℕ)+2 : ℕ),?_⟩
  filter_upwards [prefix_good_history,prefix_rooted_upper_failure 8001,
    prefix_balanced_noise_failure 8001,prefix_triangle_noise_failure,
    prefix_codegree_noise_failure,four_prefix_margins] with n hgood hr hb ht hc hmargin
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  have hm : μ.map (fun ω => ω (historyIndex (prefixTime n) (prefixTime n))) = prefixLaw n := by
    rw [historyLaw_marginal _ _ _ _ le_rfl,markovLaw_triangle_step]
    rfl
  unfold prefixFailure
  rw [← hm,pmfMean_map]
  have hpoint : ∀ ω ∈ μ.support,
      (if GoodPrefixGraph n (1/80000) (3*(8001 : ℕ)+2 : ℕ) (ω (historyIndex (prefixTime n) (prefixTime n))) then (0 : ℝ) else 1) ≤
      (if PrefixRootedUpper 8001 n ω then 0 else 1)+
      (if PrefixBalancedNoise 8001 n ω then 0 else 1)+
      (if PrefixTriangleNoise n ω then 0 else 1)+
      (if PrefixCodegreeNoiseGood n ω then 0 else 1) := by
    intro ω hω
    by_cases h₁ : PrefixRootedUpper 8001 n ω <;>
      by_cases h₂ : PrefixBalancedNoise 8001 n ω <;>
      by_cases h₃ : PrefixTriangleNoise n ω <;>
      by_cases h₄ : PrefixCodegreeNoiseGood n ω
    all_goals simp only [h₁,h₂,h₃,h₄,ite_true,ite_false]
    · rw [ite_eq_left (hgood ω hω h₁ h₂ h₃ h₄)]; norm_num
    all_goals split_ifs <;> norm_num
  have hs := pmfMean_mono μ hpoint
  simp only [pmfMean_add] at hs
  apply hs.trans
  have hs' := add_le_add (add_le_add (add_le_add hr hb) ht) hc
  calc
    _ ≤ ((Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ))+
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)))+
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)))+
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := hs'
    _ = 4*Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by ring
    _ ≤ _ := hmargin

end SharpTerminalLeave
end
end

end OAI
