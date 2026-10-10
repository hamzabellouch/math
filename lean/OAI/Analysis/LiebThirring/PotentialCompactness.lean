import OAI.Analysis.LiebThirring.LocalWeight

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma small_bounded_plus_L1 {γ : ℝ} {W : ℝ → ℝ} (hγ : 1/2 < γ)
    (hW : Admissible γ W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : ℝ → ℝ, (∀ x, 0 ≤ V x) ∧ Integrable V ∧ ∀ x, ‖W x‖ ≤ δ+V x := by
  let p := γ+1/2
  let V := fun x ↦ ‖W x‖^p / δ^(p-1)
  have hc : 0 < δ^(p-1) := Real.rpow_pos_of_pos hδ _
  have hi : Integrable (fun x ↦ ‖W x‖^p) := by
    have hh := hW.2.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr (show 0 < γ+1/2 by linarith)).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ γ+1/2 by linarith)] using hh
  refine ⟨V,fun x ↦ div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hc.le,hi.div_const _,?_⟩
  intro x
  by_cases hx : ‖W x‖ ≤ δ
  · exact hx.trans (le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hc.le))
  · have hxδ : δ ≤ ‖W x‖ := (not_le.mp hx).le
    have hm : δ^(p-1) ≤ ‖W x‖^(p-1) := Real.rpow_le_rpow hδ.le hxδ (by dsimp [p]; linarith)
    have ht : ‖W x‖*δ^(p-1) ≤ ‖W x‖^p := by
      calc
        _ ≤ ‖W x‖*‖W x‖^(p-1) := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
        _ = ‖W x‖^p := by
          conv_lhs => lhs; rw [← Real.rpow_one ‖W x‖]
          rw [← Real.rpow_add (lt_of_lt_of_le hδ hxδ)]
          congr 1
          ring
    have hv : ‖W x‖ ≤ V x := (le_div_iff₀ hc).mpr ht
    exact hv.trans (le_add_of_nonneg_left hδ.le)

lemma integrable_tail_small {V : ℝ → ℝ} (hV : Integrable V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ (∫ x, ((Interval R)ᶜ).indicator V x) ≤ δ := by
  let F := fun (n : ℕ) ↦ ((Interval (n:ℝ))ᶜ).indicator V
  have hm (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    hV.aestronglyMeasurable.indicator measurableSet_Icc.compl
  have hd (n : ℕ) : ∀ᵐ x, ‖F n x‖ ≤ ‖V x‖ :=
    Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _
  have ht (x : ℝ) : Tendsto (fun n ↦ F n x) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N,hN⟩ := exists_nat_gt |x|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlarge : |x| ≤ (n:ℝ) := hN.le.trans (Nat.cast_le.mpr hn)
    have hx : x ∈ Interval (n:ℝ) := ⟨by linarith [(neg_abs_le x)],(le_abs_self x).trans hlarge⟩
    simp only [F,indicator_of_notMem (show x ∉ (Interval (n:ℝ))ᶜ from not_not_intro hx)]
  have hlim : Tendsto (fun n ↦ ∫ x, F n x) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖V x‖) hm hV.norm hd (Eventually.of_forall ht)
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  exact ⟨n,Nat.cast_nonneg _,hn.le⟩

lemma h1Graph_ae_sq_bound (u : H1C) : ∀ᵐ x, ‖valL u x‖^2 ≤ 8*‖u‖^2 := by
  have h := h1_ae_sq_bound (toH1 u)
  simp only [toLp_toH1,grad_toLp_toH1,← h1_norm_sq] at h
  exact h

lemma tail_weighted_norm_sq {W : ℝ → ℝ} (d : PotentialData W) {δ : ℝ}
    (hδ : 0 ≤ δ) {V : ℝ → ℝ} (hV : Integrable V) (hV₀ : ∀ x, 0 ≤ V x)
    (hWV : ∀ x, ‖W x‖ ≤ δ+V x) (R : ℝ) (u : H1C) :
    ‖weightedL d u-localWeightedL d R u‖^2 ≤
      (δ+8*(∫ x, ((Interval R)ᶜ).indicator V x))*‖u‖^2 := by
  let G := fun x ↦ δ*‖valL u x‖^2 + ((Interval R)ᶜ).indicator V x * (8*‖u‖^2)
  have hVG : Integrable (((Interval R)ᶜ).indicator V) := hV.indicator measurableSet_Icc.compl
  have hG : Integrable G :=
    ((Lp.memLp (valL u)).integrable_norm_pow (by norm_num)).const_mul δ |>.add
      (hVG.mul_const _)
  have hdom : ∀ᵐ x, ‖(weightedL d u-localWeightedL d R u) x‖^2 ≤ G x := by
    filter_upwards [Lp.coeFn_sub (weightedL d u) (localWeightedL d R u),
      (weightedVal_memLp d u).coeFn_toLp,localWeightedL_ae d R u,h1Graph_ae_sq_bound u]
      with x hx hy hz hu
    simp only [Pi.sub_apply] at hx
    change weightedL d u x = weightedVal d u x at hy
    rw [hx,hy,hz]
    by_cases hs : x ∈ Interval R
    · simp only [localSqrt,indicator_of_mem hs,weightedVal,sub_self,norm_zero,
        zero_pow (by decide : 2 ≠ 0),G,indicator_of_notMem (show x ∉ (Interval R)ᶜ from not_not_intro hs),
        zero_mul,add_zero]
      exact mul_nonneg hδ (sq_nonneg _)
    · simp only [localSqrt,indicator_of_notMem hs,zero_mul,sub_zero,weightedVal_norm_sq,
        G,indicator_of_mem (show x ∈ (Interval R)ᶜ from hs)]
      have hm := mul_le_mul_of_nonneg_right (hWV x) (sq_nonneg ‖valL u x‖)
      have hv := mul_le_mul_of_nonneg_left hu (hV₀ x)
      nlinarith
  rw [L2_norm_sq_eq_integral]
  calc
    _ ≤ ∫ x, G x := integral_mono_ae
      ((Lp.memLp (weightedL d u-localWeightedL d R u)).integrable_norm_pow (by norm_num)) hG hdom
    _ = δ*‖valL u‖^2 + (∫ x, ((Interval R)ᶜ).indicator V x)*(8*‖u‖^2) := by
      rw [integral_add (((Lp.memLp (valL u)).integrable_norm_pow (by norm_num)).const_mul δ)
        (hVG.mul_const _),integral_const_mul,integral_mul_const,← L2_norm_sq_eq_integral]
    _ ≤ _ := by
      have hn := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (valL_norm_le u)) hδ
      nlinarith

lemma weightedL_compact {γ : ℝ} {W : ℝ → ℝ} (hγ : 1/2 < γ)
    (hW : Admissible γ W) (d : PotentialData W) : IsCompactOperator (weightedL d) := by
  change weightedL d ∈ {f : H1C →L[ℂ] L2C | IsCompactOperator f}
  have hc : IsClosed {f : H1C →L[ℂ] L2C | IsCompactOperator f} :=
    isClosed_setOfPred_isCompactOperator
  rw [← hc.closure_eq]
  apply (Metric.mem_closure_iff (α := H1C →L[ℂ] L2C)).mpr
  intro ε hε
  let δ := ε^2/36
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) (by norm_num)
  obtain ⟨V,hV₀,hV,hWV⟩ := small_bounded_plus_L1 hγ hW hδ
  obtain ⟨R,hR,hVR⟩ := integrable_tail_small hV hδ
  refine ⟨localWeightedL d R,localWeightedL_compact d (hW.locallyIntegrable hγ) hR,?_⟩
  have hb : ‖weightedL d-localWeightedL d R‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
    have hi := tail_weighted_norm_sq d hδ.le hV hV₀ hWV R u
    change ‖weightedL d u-localWeightedL d R u‖^2 ≤ _
    rw [mul_pow]
    calc
      _ ≤ (δ+8*(∫ x, ((Interval R)ᶜ).indicator V x))*‖u‖^2 := hi
      _ ≤ (δ+8*δ)*‖u‖^2 := mul_le_mul_of_nonneg_right
        (by linarith [hVR]) (sq_nonneg _)
      _ = (ε/2)^2*‖u‖^2 := by dsimp only [δ]; ring
  rw [dist_eq_norm (weightedL d) (localWeightedL d R)]
  exact hb.trans_lt (by linarith)

end SharpLiebThirring.OperatorProof

end

end OAI
