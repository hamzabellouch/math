import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedTemplateEdgesCard
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixTimeSquare
import OAI.Combinatorics.TriangleRemoval.Process.OverlapVertices
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEdgeRadius

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def rootedCompletionMax {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun J : Finset (Fin k) =>
    if T.roots ⊆ J then (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (· ⊆ J)).card) else 1)

lemma rootedCompletionMax_ge_one {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) :
    1 ≤ rootedCompletionMax T n p := by
  unfold rootedCompletionMax
  apply Finset.le_sup'_of_le _ (Finset.mem_univ (Finset.univ : Finset (Fin k)))
  simp

lemma rootedCompletionMax_bound {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ)
    (J : Finset (Fin k)) (hJ : T.roots ⊆ J) :
    (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (· ⊆ J)).card) ≤
      rootedCompletionMax T n p := by
  unfold rootedCompletionMax
  apply Finset.le_sup'_of_le _ (Finset.mem_univ J)
  simp only [hJ,ite_true,le_refl]

lemma rootedCompletionMax_large {k n : ℕ} (T : RootedTemplate k) {p : ℝ}
    (hp : 0 ≤ p) (hT : largeTemplateEligible T n p) :
    rootedCompletionMax T n p ≤ rootedScaling T n p := by
  have h1 : 1 ≤ rootedScaling T n p := by
    simpa only [rootedScaling,Finset.card_univ,Fintype.card_fin] using
      hT Finset.univ (Finset.subset_univ _) T.edges (Finset.Subset.refl _)
        (fun _ _ => Finset.subset_univ _)
  apply Finset.sup'_le
  intro J _
  split_ifs with hJ
  · exact largeTemplate_completion_scale T hp hT J hJ
  · exact h1

lemma rootedCompletionMax_small {k n : ℕ} (T : RootedTemplate k) {p : ℝ}
    (hT : smallTemplateEligible T n p) : rootedCompletionMax T n p ≤ 1 := by
  apply Finset.sup'_le
  intro J _
  split_ifs with hJ
  · exact hT J hJ
  · exact le_rfl

theorem rooted_tail_from_survival {k n : ℕ} {Ω : Type*} [Fintype Ω]
    (T : RootedTemplate k) (ψ : {v // v ∈ T.roots} ↪ Fin n)
    (μ : PMF Ω) (state : Ω → Graph n) (A : Ω → Prop)
    (q : ℕ) {p B U : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 < B) (hU : 0 ≤ U)
    (hcoef : 2*(2*((((q+1)*k : ℕ) : ℝ)+1))^k ≤ B)
    (hsurvive : ∀ F : Graph n, F.card ≤ q*T.edges.card →
      pmfMean μ (fun ω => if A ω then intact F (state ω) else 0) ≤ U*p^F.card) :
    pmfMean μ (fun ω => if A ω ∧ B*rootedCompletionMax T n p ≤ rootedCount T ψ (state ω)
      then 1 else 0) ≤ U*(1/2 : ℝ)^q := by
  let M := rootedCompletionMax T n p
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (rootedCompletionMax_ge_one T n p)
  have hm := rooted_count_moment_from_survival T ψ μ state A q hp hp1 hM.le hU
    (rootedCompletionMax_bound T n p) hsurvive
  have ht := pmfMean_stopped_power_tail μ A (fun ω => rootedCount T ψ (state ω))
    (fun ω => copyCount_nonneg _ _) q (mul_pos hB hM) hm
  apply ht.trans
  have he : U*((2*((((q+1)*k : ℕ) : ℝ)+1))^k*M)^q/(B*M)^q =
      U*((2*((((q+1)*k : ℕ) : ℝ)+1))^k/B)^q := by
    rw [mul_div_assoc,← div_pow,mul_div_mul_right _ _ hM.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hU
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ hB).mpr
  linarith only [hcoef]

noncomputable def rootedMomentOrder (n : ℕ) : ℕ := ⌊(1+Real.log (n : ℝ))^2⌋₊

lemma rooted_moment_edge_cap (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ k ≤ H, ∀ T : RootedTemplate k, ((rootedMomentOrder n*T.edges.card : ℕ) : ℝ) ≤
      (n : ℝ)^(1/200000 : ℝ) := by
  have hc : (0 : ℝ) < 1/((H : ℝ)^2+1) := by positivity
  filter_upwards [prefixTemplateFactor_subpower 2 (by norm_num : (0 : ℝ) < 1/200000) hc,
    eventually_ge_atTop (1 : ℕ)] with n hb hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ 1+Real.log (n : ℝ) := by have := Real.log_nonneg hn1; linarith
  have hq : (rootedMomentOrder n : ℝ) ≤ (1+Real.log (n : ℝ))^2 := Nat.floor_le (sq_nonneg _)
  have hpow : (1+Real.log (n : ℝ))^(2 : ℝ) = (1+Real.log (n : ℝ))^2 := Real.rpow_two _
  change (1+Real.log (n : ℝ))^(2 : ℝ) ≤ _ at hb
  rw [hpow] at hb
  intro k hk T
  have he : (T.edges.card : ℝ) ≤ (H : ℝ)^2 := by
    exact_mod_cast (rootedTemplate_edges_card_le_sq T).trans (Nat.pow_le_pow_left hk 2)
  push_cast
  calc
    _ ≤ (1+Real.log (n : ℝ))^2*((H : ℝ)^2+1) :=
      mul_le_mul hq (by linarith only [he]) (Nat.cast_nonneg _) (sq_nonneg _)
    _ ≤ (1/((H : ℝ)^2+1)*(n : ℝ)^(1/200000 : ℝ))*((H : ℝ)^2+1) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by field_simp

lemma rooted_moment_coefficient (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    0 < (1+Real.log (n : ℝ))^(3*H+2) ∧
    ∀ k ≤ H, 2*(2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1))^k ≤
      (1+Real.log (n : ℝ))^(3*H+2) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually_ge_atTop (2*(2*(H : ℝ)+1))] with n hn
  change 2*(2*(H : ℝ)+1) ≤ Real.log (n : ℝ) at hn
  let L : ℝ := 1+Real.log (n : ℝ)
  have hL : 2 ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hq : (rootedMomentOrder n : ℝ) ≤ L^2 := Nat.floor_le (sq_nonneg _)
  refine ⟨pow_pos hL0 _,?_⟩
  intro k hk
  have hkR : (k : ℝ) ≤ H := by exact_mod_cast hk
  have hcoeff : 2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1) ≤ L^3 := by
    push_cast
    have hq' : (rootedMomentOrder n : ℝ)+1 ≤ 2*L^2 := by nlinarith [sq_nonneg (L-1)]
    have hmul := mul_le_mul hq' hkR (Nat.cast_nonneg k) (by positivity : (0 : ℝ) ≤ 2*L^2)
    have hc : 2*(2*(H : ℝ)+1) ≤ L := by dsimp [L]; linarith
    have hhc := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    nlinarith only [hmul,hhc,sq_nonneg (L-1),hL]
  have hcoeff0 : 0 ≤ 2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1) := by positivity
  have hpow : (2*((((rootedMomentOrder n+1)*k : ℕ) : ℝ)+1))^k ≤ L^(3*H) := by
    calc
      _ ≤ (L^3)^k := pow_le_pow_left₀ hcoeff0 hcoeff k
      _ = L^(3*k) := (pow_mul L 3 k).symm
      _ ≤ _ := pow_le_pow_right₀ hL1 (by omega)
  change 2*_ ≤ L^(3*H+2)
  rw [pow_add]
  have htail : 2 ≤ L^2 := by nlinarith
  exact mul_le_mul htail hpow (by positivity) (by positivity) |>.trans_eq (mul_comm _ _)

lemma historyAlive_past {α : Type*} (safe : ℕ → α → Prop) (T j : ℕ)
    (ω π : History α T) (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = π i) :
    historyAlive safe T j ω ↔ historyAlive safe T j π := by
  have he (i : ℕ) (hi : i < j) : ω (historyIndex T i) = π (historyIndex T i) := by
    apply h
    exact min_le_min_right T hi.le
  unfold historyAlive
  constructor
  · intro hA i hi; rw [← he i hi]; exact hA i hi
  · intro hA i hi; rw [he i hi]; exact hA i hi

lemma stopped_state_mean_past {α : Type*} [Fintype α] (initial : PMF α)
    (K : ℕ → α → PMF α) (safe : ℕ → α → Prop) (T j : ℕ) (hj : j ≤ T)
    (P : α → Prop) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if historyAlive safe T j ω ∧ P (ω (historyIndex T j)) then 1 else 0) =
    pmfMean (historyLaw initial K T j)
      (fun ω => if historyAlive safe T j ω ∧ P (ω (historyIndex T j)) then 1 else 0) := by
  apply historyLaw_past_mean initial K T j T hj
  intro ω π h
  have he := h (historyIndex T j) (le_refl _)
  rw [he,historyAlive_past safe T j ω π h]

theorem prefix_rooted_killed_tail (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ j ≤ prefixTime n, ∀ k ≤ H, ∀ T : RootedTemplate k,
      ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
        (prefixTime n) j ω ∧
        (1+Real.log (n : ℝ))^(3*H+2)*rootedCompletionMax T n (earlyDensity n j) ≤
          rootedCount T ψ (ω (historyIndex (prefixTime n) j)) then 1 else 0) ≤
      Real.exp 1*(1/2 : ℝ)^(rootedMomentOrder n) := by
  filter_upwards [prefix_killed_survival,rooted_moment_edge_cap H,
    rooted_moment_coefficient H,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n hsurv hcap hcoef hp hn
  intro j hj k hk T ψ
  rw [stopped_state_mean_past _ _ _ _ _ hj
    (fun G => (1+Real.log (n : ℝ))^(3*H+2)*rootedCompletionMax T n (earlyDensity n j) ≤
      rootedCount T ψ G)]
  apply rooted_tail_from_survival T ψ _ _ _ (rootedMomentOrder n)
    (early_density_positive (by omega) hp hj).le (earlyDensity_le_one n j)
    hcoef.1 (Real.exp_pos 1).le (hcoef.2 k hk)
  intro F hF
  apply hsurv j hj F
  exact (show (F.card : ℝ) ≤ ((rootedMomentOrder n*T.edges.card : ℕ) : ℝ) by exact_mod_cast hF).trans
    (hcap k hk T)

lemma rooted_moment_tail_logsquare : ∀ᶠ n : ℕ in atTop,
    Real.exp 1*(1/2 : ℝ)^(rootedMomentOrder n) ≤ Real.exp (-(Real.log (n : ℝ))^2/4) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 3] with n hn
  have hq : (1+Real.log (n : ℝ))^2 < (rootedMomentOrder n : ℝ)+1 := Nat.lt_floor_add_one _
  have hlog2 : (1 : ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have he : (1/2 : ℝ)^(rootedMomentOrder n) =
      Real.exp (-(rootedMomentOrder n : ℝ)*Real.log 2) := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [inv_pow,one_div]
  rw [he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (rootedMomentOrder n))
  nlinarith only [hh,hq,hn,sq_nonneg (Real.log (n : ℝ))]

theorem polynomial_logsquare_le_prefix_margin (A K : ℝ) : ∀ᶠ n : ℕ in atTop,
    A*(n : ℝ)^K*Real.exp (-(Real.log (n : ℝ))^2/4) ≤
      Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/3)).comp hlog
  filter_upwards [hlog.eventually_ge_atTop (8*(K+1)),hlog.eventually_ge_atTop 1,
    hpow.eventually_ge_atTop 16,tendsto_natCast_atTop_atTop.eventually_ge_atTop A,
    eventually_ge_atTop (1 : ℕ)] with n hlinear hl hpow hA hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl0 : 0 < Real.log (n : ℝ) := by linarith
  have hlin := mul_le_mul_of_nonneg_right hlinear hl0.le
  have hpow' : 16*(Real.log (n : ℝ))^(4/3 : ℝ) ≤ (Real.log (n : ℝ))^2 := by
    have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hl0.le (4/3 : ℝ))
    have he : (Real.log (n : ℝ))^(2/3 : ℝ)*(Real.log (n : ℝ))^(4/3 : ℝ) =
        (Real.log (n : ℝ))^2 := by
      rw [← Real.rpow_add hl0]; norm_num [Real.rpow_two]
    exact hm.trans_eq he
  calc
    _ ≤ (n : ℝ)*(n : ℝ)^K*Real.exp (-(Real.log (n : ℝ))^2/4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hn0.le _))
        (Real.exp_pos _).le
    _ = Real.exp ((K+1)*Real.log n-(Real.log (n : ℝ))^2/4) := by
      rw [show (n : ℝ)*(n : ℝ)^K = (n : ℝ)^(K+1) by
        rw [Real.rpow_add hn0,Real.rpow_one]; ring]
      rw [Real.rpow_def_of_pos hn0,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hlin,hpow'])

def PrefixRootedUpper (H n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
      (prefixTime n) j ω →
    ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      rootedCount T ψ (ω (historyIndex (prefixTime n) j)) <
        (1+Real.log (n : ℝ))^(3*H+2)*rootedCompletionMax T n (earlyDensity n j)

theorem prefix_rooted_upper_failure (H : ℕ) : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if PrefixRootedUpper H n ω then 0 else 1) ≤
        Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_rooted_killed_tail H,rooted_moment_tail_logsquare,
    polynomial_logsquare_le_prefix_margin
      ((rootedFamilySize H : ℝ)*2^(H+2)) (H+2),
    eventually_ge_atTop (1 : ℕ)] with n htail hnum hbudget hn
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  let P (i : Fin (prefixTime n+1) × RootedCountIndex H n)
      (ω : History (Graph n) (prefixTime n)) :=
    historyAlive (fun j => densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n))
      (prefixTime n) i.1.val ω ∧
    (1+Real.log (n : ℝ))^(3*H+2)*
      rootedCompletionMax i.2.2.1 n (earlyDensity n i.1.val) ≤
        rootedCount i.2.2.1 i.2.2.2 (ω (historyIndex (prefixTime n) i.1.val))
  have he (ω : History (Graph n) (prefixTime n)) :
      ¬ PrefixRootedUpper H n ω ↔ ∃ i ∈ Finset.univ, P i ω := by
    simp only [PrefixRootedUpper,not_forall,not_lt]
    constructor
    · rintro ⟨j,hj,ha,k,hk,T,ψ,hbad⟩
      exact ⟨(⟨j,by omega⟩,⟨⟨k,by omega⟩,T,ψ⟩),Finset.mem_univ _,ha,hbad⟩
    · rintro ⟨i,_,ha,hbad⟩
      exact ⟨i.1.val,by omega,ha,i.2.1.val,by omega,i.2.2.1,i.2.2.2,hbad⟩
  have hu := pmfMean_event_union μ Finset.univ P
  have hs : (∑ i, pmfMean μ (fun ω => if P i ω then 1 else 0)) ≤
      (Fintype.card (Fin (prefixTime n+1) × RootedCountIndex H n) : ℝ)*
        Real.exp (-(Real.log (n : ℝ))^2/4) := by
    calc
      _ ≤ ∑ _i : Fin (prefixTime n+1) × RootedCountIndex H n,
          Real.exp (-(Real.log (n : ℝ))^2/4) := by
        apply Finset.sum_le_sum
        intro i _
        exact (htail i.1.val (by omega) i.2.1.val (by omega) i.2.2.1 i.2.2.2).trans hnum
      _ = _ := by simp
  have hc : (Fintype.card (Fin (prefixTime n+1) × RootedCountIndex H n) : ℝ) ≤
      (rootedFamilySize H : ℝ)*2^(H+2)*(n : ℝ)^(H+2 : ℕ) := by
    have hh := rooted_noise_chances_le H n hn
    have hh' : Fintype.card (Fin (prefixTime n+1) × RootedCountIndex H n) ≤
        rootedFamilySize H*2^(H+2)*n^(H+2) := by
      simp only [Fintype.card_prod,Fintype.card_fin]
      nlinarith only [hh]
    exact_mod_cast hh'
  have hev : (n : ℝ)^((H : ℝ)+2) = (n : ℝ)^(H+2 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_cast
  rw [hev] at hbudget
  have hsumfinal := hs.trans ((mul_le_mul_of_nonneg_right hc
    (Real.exp_pos _).le).trans hbudget)
  have hfinal := hu.trans (by
    convert hsumfinal using 1; try rfl
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (pmfMean μ)
    funext ω
    by_cases h : P i ω <;> simp only [h,ite_true,ite_false])
  convert hfinal using 1; try rfl
  apply congrArg (pmfMean μ)
  funext ω
  simp only [← he]
  split_ifs <;> rfl

end SharpTerminalLeave
end
end

end OAI
