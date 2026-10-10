import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RerootTemplate
import OAI.Combinatorics.TriangleRemoval.Process.PowerEulerError
import OAI.Combinatorics.TriangleRemoval.Tracking.BalancedJump

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def PrefixBalancedNoise (H n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
    ¬ RelativeNoiseExit (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (balancedLoad H T n) (earlyTemplateScale (k-T.roots.card) T.edges.card n) 2
      (codegreeNoiseRadius n) (prefixTime n) ω

theorem prefix_balanced_noise_failure (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if PrefixBalancedNoise H n ω then 0 else 1) ≤
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_balanced_noise_single H,
    polynomial_logsquare_le_prefix_margin ((rootedFamilySize H : ℝ)*2^(H+2)) (H+2),
    eventually_ge_atTop (1 : ℕ)] with n htail hb hn
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  let P (i : RootedCountIndex H n) (ω : History (Graph n) (prefixTime n)) :=
    RelativeNoiseExit (fun φ : RootedInjection i.2.1 i.2.2 => imageEdges i.2.1 φ.val)
      (balancedLoad H i.2.1 n) (earlyTemplateScale (i.1.val-i.2.1.roots.card) i.2.1.edges.card n)
      2 (codegreeNoiseRadius n) (prefixTime n) ω
  have he (ω : History (Graph n) (prefixTime n)) :
      ¬ PrefixBalancedNoise H n ω ↔ ∃ i ∈ Finset.univ, P i ω := by
    simp only [PrefixBalancedNoise,not_forall,not_not]
    constructor
    · rintro ⟨k,hk,T,ψ,h⟩
      exact ⟨⟨⟨k,by omega⟩,T,ψ⟩,Finset.mem_univ _,h⟩
    · rintro ⟨i,_,h⟩
      exact ⟨i.1.val,by omega,i.2.1,i.2.2,h⟩
  have hu := pmfMean_event_union μ Finset.univ P
  have hs : (∑ i, pmfMean μ (fun ω => if P i ω then 1 else 0)) ≤
      (Fintype.card (RootedCountIndex H n) : ℝ)*2*(prefixTime n+1)*
        Real.exp (-(Real.log (n : ℝ))^2/4) := by
    calc
      _ ≤ ∑ _i : RootedCountIndex H n,
          2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
        apply Finset.sum_le_sum
        intro i _
        exact htail i.1.val (by omega) i.2.1 i.2.2
      _ = _ := by simp; ring
  have hc : (Fintype.card (RootedCountIndex H n) : ℝ)*2*(prefixTime n+1) ≤
      (rootedFamilySize H : ℝ)*2^(H+2)*(n : ℝ)^(H+2 : ℕ) := by
    exact_mod_cast rooted_noise_chances_le H n hn
  have hev : (n : ℝ)^((H : ℝ)+2) = (n : ℝ)^(H+2 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_cast
  rw [hev] at hb
  have hs' := hs.trans ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans hb)
  have hf := hu.trans hs'
  convert hf using 1
  try rfl
  apply congrArg (pmfMean μ)
  funext ω
  simp only [← he]
  split_ifs <;> rfl

noncomputable def prefixWheelRadius (n : ℕ) : ℝ := (n : ℝ)^(-1/80000 : ℝ)

lemma balanced_closure_budget (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    prefixWheelRadius n ≤ 1 ∧
    (2 : ℝ)^(H^2)*(2*(H : ℝ)^2)/(n : ℝ)+codegreeNoiseRadius n+
      (16*(H : ℝ)^2*prefixEdgeRadius n*Real.log n+4*((H : ℝ)^2)^2/prefixD n+
        24*((H : ℝ)^2)^2*Real.log n/(n : ℝ)) ≤ prefixWheelRadius n/2 := by
  let C : ℝ := 2^(H^2)*(2*(H : ℝ)^2)+1+16*(H : ℝ)^2+28*((H : ℝ)^2)^2
  have hC : 0 < C := by dsimp [C]; positivity
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,prefixEdgeRadius,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/40000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by positivity : 0 < 1/(2*C)),prefixD_eventual_envelope,
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1 : ℕ)] with n hlog hD hrad hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hη : 0 ≤ prefixEdgeRadius n := Real.rpow_nonneg hn0.le _
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hηlog : C*(1+Real.log (n : ℝ))*prefixEdgeRadius n ≤ prefixWheelRadius n/2 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show 1+Real.log (n : ℝ) ≤ 1/(2*C)*(n : ℝ)^(1/80000 : ℝ) by
        simpa only [prefixTemplateFactor,Real.rpow_one] using hlog) hC.le) hη
    have he : C*(1/(2*C)*(n : ℝ)^(1/80000 : ℝ))*prefixEdgeRadius n = prefixWheelRadius n/2 := by
      unfold prefixEdgeRadius prefixWheelRadius
      calc
        _ = (C/(2*C))*((n : ℝ)^(1/80000 : ℝ)*(n : ℝ)^(-1/40000 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hn0]; norm_num; field_simp
    exact hh.trans_eq he
  have hnoise : codegreeNoiseRadius n ≤ prefixEdgeRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hinv : 1/(n : ℝ) ≤ prefixEdgeRadius n := by
    simpa only [Real.rpow_neg_one,one_div,prefixEdgeRadius] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -1/40000))
  have hDinv : 1/prefixD n ≤ prefixEdgeRadius n := by
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  refine ⟨hη,hrad,Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num),?_⟩
  have hinit := mul_le_mul_of_nonneg_left hinv (show 0 ≤ (2 : ℝ)^(H^2)*(2*(H : ℝ)^2) by positivity)
  have hdisc := mul_le_mul_of_nonneg_left hDinv (show 0 ≤ 4*((H : ℝ)^2)^2 by positivity)
  have hgrid := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 24*((H : ℝ)^2)^2*Real.log n by positivity)
  have hηL : prefixEdgeRadius n ≤ (1+Real.log (n : ℝ))*prefixEdgeRadius n := by nlinarith only [mul_nonneg hl hη]
  have hmain := mul_le_mul_of_nonneg_left hηL
    (show 0 ≤ (2 : ℝ)^(H^2)*(2*(H : ℝ)^2)+1+4*((H : ℝ)^2)^2 by positivity)
  dsimp only [C] at hηlog
  simp only [div_eq_mul_inv,one_mul] at hinit hdisc hgrid ⊢
  nlinarith only [hinit,hdisc,hgrid,hnoise,hmain,hηlog,
    mul_nonneg (show 0 ≤ 16*(H : ℝ)^2+24*((H : ℝ)^2)^2 by positivity) hη]

theorem prefix_balanced_tracking (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper H n ω → PrefixBalancedNoise H n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ k ≤ H, ∀ T : RootedTemplate k, RootedTwoBalanced T →
    ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      |rootedCount T ψ (ω (historyIndex (prefixTime n) j))/rootedScaling T n (earlyDensity n j)-1| ≤
        prefixWheelRadius n/2 := by
  filter_upwards [balanced_closure_budget H,earlyTemplateScale_uniform_regular H,
    prefixDensity_eventually_inverse_lower,prefixD_eventual_envelope,
    eventually_ge_atTop H,eventually_ge_atTop (2 : ℕ)] with n hbud hreg hp hD hnH hn
  intro ω hω hupper hnoise j hj hsafe k hk T hT ψ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hb : T.edges.card ≤ H^2 := (rootedTemplate_edges_card_le_sq T).trans (Nat.pow_le_pow_left hk 2)
  have hbR : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by exact_mod_cast hb
  have hs := hreg (k-T.roots.card) ((Nat.sub_le _ _).trans hk) T.edges.card hb
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa only [PMF.mem_support_pure_iff] using hi
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hcap : ∀ i < j, rootedCount T ψ (ω (historyIndex (prefixTime n) i)) ≤
        2*earlyTemplateScale (k-T.roots.card) T.edges.card n i := by
      intro i hij
      have htracking := ih i hij (by omega) (fun l hl => hsafe l (hl.trans hij))
      have hbnd : rootedCount T ψ (ω (historyIndex (prefixTime n) i))/
          rootedScaling T n (earlyDensity n i) ≤ 2 := by
        have hh := (abs_le.mp htracking).2
        linarith only [hh,hbud.2.2.1]
      exact (div_le_iff₀ (hs.1 i (by omega))).mp hbnd
    have hloads : pastRelativeCopyLoadsSafe (fun φ : RootedInjection T ψ => imageEdges T φ.val)
        (balancedLoad H T n) (prefixTime n) j ω := by
      intro i hi
      have hij : i < j := lt_of_lt_of_le hi (Nat.min_le_left _ _)
      have hiT : i ≤ prefixTime n := by omega
      have hDi : 1 ≤ (n : ℝ)*earlyDensity n i^2 := by
        have hd := earlyCodegreeScale_ge_prefixD n i hiT (le_trans (by positivity) hp)
        have hh := Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/1000)
        exact hh.trans (hD.1.trans (by simpa only [earlyTemplateScale,pow_one] using hd))
      exact balanced_rooted_load_bound T hk hT ψ _ (hsafe i hij).1
        (early_density_positive (by omega) hp hiT) (earlyDensity_le_one n i) (by positivity) hDi
        (fun a ha U ξ => (hupper i hiT (fun l hl => hsafe l (hl.trans hij)) a ha U ξ).le)
    have hnse : |historyNoise (fun _ => step)
        (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω| < codegreeNoiseRadius n := by
      exact lt_of_not_ge (fun hcross => hnoise k hk T ψ ⟨j,hj,hloads,hcap,hcross⟩)
    have hd := early_relative_drift_bound (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (k-T.roots.card) T.edges.card (fun φ => imageEdges_card T φ.val)
      (prefixEdgeRadius n) (by omega) hp hbud.1 hbud.2.1 hs.2.2.1 j hj ω hsafe hcap
    have hinit := rootedCount_initial_uniform_error H hk hnH hn T ψ
    have he : earlyDensity n 0 = 1-1/(n : ℝ) := by simp [earlyDensity]
    rw [← he,← hi'] at hinit
    have htri := fun x y z : ℝ => (abs_add_le (x+y) z).trans
      (add_le_add (abs_add_le x y) le_rfl)
    have htri := htri
      (rootedCount T ψ (ω (historyIndex (prefixTime n) j))/rootedScaling T n (earlyDensity n j)-
        rootedCount T ψ (ω (historyIndex (prefixTime n) 0))/rootedScaling T n (earlyDensity n 0)-
        historyNoise (fun _ => step) (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω)
      (historyNoise (fun _ => step) (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω)
      (rootedCount T ψ (ω (historyIndex (prefixTime n) 0))/rootedScaling T n (earlyDensity n 0)-1)
    have hlarge : 16*(T.edges.card : ℝ)*prefixEdgeRadius n*Real.log n+4*(T.edges.card : ℝ)^2/prefixD n+
        24*(T.edges.card : ℝ)^2*Real.log n/(n : ℝ) ≤
        16*(H : ℝ)^2*prefixEdgeRadius n*Real.log n+4*((H : ℝ)^2)^2/prefixD n+
        24*((H : ℝ)^2)^2*Real.log n/(n : ℝ) := by
      have hdpos : 0 ≤ prefixD n := (Real.rpow_nonneg hn0.le _).trans hD.1
      gcongr
      exact hbud.1
    change |rootedCount T ψ (ω (historyIndex (prefixTime n) j))/rootedScaling T n (earlyDensity n j)-
      rootedCount T ψ (ω (historyIndex (prefixTime n) 0))/rootedScaling T n (earlyDensity n 0)-
        historyNoise (fun _ => step) (fun i G => rootedCount T ψ G/earlyTemplateScale (k-T.roots.card) T.edges.card n i)
          (prefixTime n) j ω| ≤ _ at hd
    have heq : ∀ x y z : ℝ, x-y-z+z+(y-1) = x-1 := by intros; ring
    rw [heq] at htri
    linarith only [htri,hd,hnse,hinit,hlarge,hbud.2.2.2]

end SharpTerminalLeave
end
end

end OAI
