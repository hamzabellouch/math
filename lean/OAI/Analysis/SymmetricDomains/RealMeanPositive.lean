import Mathlib
import OAI.Analysis.SymmetricDomains.CosineBumpWeightedSummable

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

theorem exists_bishop_cutoffs :
    ∃ lam η : realAlgebra,
      (∀ θ, 0 ≤ realEvaluation θ lam ∧ 0 ≤ realEvaluation θ η) ∧
      (∀ᶠ θ in 𝓝 (0 : Circle), realEvaluation θ lam = 0 ∧ realEvaluation θ η = 0) ∧
      realEvaluation ((1/2 : ℝ) : Circle) η = 1 ∧
      (∀ θ, realEvaluation θ η ≠ 0 → realEvaluation θ lam = 1) := by
  let L : ContDiffBump (-1 : ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let H : ContDiffBump (-1 : ℝ) := ⟨1/16,1/8,by norm_num,by norm_num⟩
  let lc := cosineBump (1/4) (1/2) (by norm_num) (by norm_num)
  let hc := cosineBump (1/16) (1/8) (by norm_num) (by norm_num)
  obtain ⟨lam,hlam⟩ := exists_real_boundary_of_weighted_summable lc
    (cosineBump_weighted_summable _ _ _ _ (by norm_num))
  obtain ⟨η,hη⟩ := exists_real_boundary_of_weighted_summable hc
    (cosineBump_weighted_summable _ _ _ _ (by norm_num))
  have hle (θ : Circle) : realEvaluation θ lam = L (circleCos θ) := hlam θ
  have hhe (θ : Circle) : realEvaluation θ η = H (circleCos θ) := hη θ
  refine ⟨lam,η,?_,?_,?_,?_⟩
  · intro θ
    rw [hle,hhe]
    exact ⟨L.nonneg,H.nonneg⟩
  · have hd : ContinuousAt (fun θ => dist (circleCos θ) (-1 : ℝ)) 0 := by fun_prop
    have hh : (1/2 : ℝ) < dist (circleCos 0) (-1 : ℝ) := by norm_num [circleCos_zero,Real.dist_eq]
    filter_upwards [hd.eventually (Ioi_mem_nhds hh)] with θ hθ
    rw [hle,hhe]
    exact ⟨L.zero_of_le_dist hθ.le,H.zero_of_le_dist (by change (1/8 : ℝ) ≤ _; linarith)⟩
  · rw [hhe,circleCos_half]
    exact H.one_of_mem_closedBall (by simp [H,Metric.mem_closedBall])
  · intro θ hθ
    rw [hle]
    rw [hhe] at hθ
    apply L.one_of_mem_closedBall
    have hs : dist (circleCos θ) (-1 : ℝ) < (1/8 : ℝ) := by
      by_contra hn
      exact hθ (H.zero_of_le_dist (le_of_not_gt hn))
    change dist (circleCos θ) (-1 : ℝ) ≤ 1/4
    linarith

lemma smooth_cosine_lift {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hh0 : h =ᶠ[𝓝 1] 0) :
    ∃ F : realAlgebra, ∀ θ, realEvaluation θ F = h (circleCos θ) := by
  let f : ℝ → ℂ := fun t => h (Real.cos (2*Real.pi*t))
  have hfc : ContDiff ℝ ∞ f := by
    apply Complex.ofRealCLM.contDiff.comp
    exact hh.comp (by fun_prop)
  have hevent (a : ℝ) (ha : Real.cos (2*Real.pi*a) = 1) : f =ᶠ[𝓝 a] 0 := by
    have ht : Tendsto (fun t : ℝ => Real.cos (2*Real.pi*t)) (𝓝 a) (𝓝 1) := by
      rw [← ha]
      exact (by fun_prop : ContinuousAt (fun t : ℝ => Real.cos (2*Real.pi*t)) a)
    filter_upwards [ht.eventually hh0] with t ht
    simp [f,ht]
  have hs := Release061.smooth_flat_weighted_fourier hfc (hevent 0 (by simp))
    (hevent 1 (by simp [Real.cos_two_pi]))
  let g : C(Circle,ℝ) := ⟨fun θ => h (circleCos θ),hh.continuous.comp circleCos.continuous⟩
  apply exists_real_boundary_of_weighted_summable g
  have heq : (fun θ => (g θ : ℂ)) = AddCircle.liftIoc 1 0 f := by
    funext θ
    let t := (AddCircle.equivIoc 1 0 θ).val
    have ht := (AddCircle.equivIoc 1 0 θ).property
    have htθ : (t : Circle) = θ := AddCircle.coe_equivIoc (p := 1) (a := 0) (y := θ)
    rw [← htθ,AddCircle.liftIoc_coe_apply ht]
    change (h (circleCos (t : Circle)) : ℂ) = (h (Real.cos (2*Real.pi*t)) : ℂ)
    rw [circleCos_coe]
  simpa only [weight,heq,fourierCoeff_liftIoc_eq,zero_add] using hs

theorem exists_localized_reciprocal :
    ∃ κ : realAlgebra, ∀ θ,
      dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
        (2-2*circleCos θ)*realEvaluation θ κ = 1 := by
  let B : ContDiffBump (-1 : ℝ) := ⟨3/4,1,by norm_num,by norm_num⟩
  let h : ℝ → ℝ := fun r => B r/(2-2*r)
  have he : h =ᶠ[𝓝 1] 0 := by
    have hc : ContinuousAt (fun r : ℝ => dist r (-1 : ℝ)) 1 := by fun_prop
    filter_upwards [hc.eventually (Ioi_mem_nhds (by norm_num [Real.dist_eq] : (1 : ℝ) < dist 1 (-1 : ℝ)))] with r hr
    simp [h,B.zero_of_le_dist hr.le]
  have hh : ContDiff ℝ ∞ h := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 1
    · subst r
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact B.contDiff.contDiffAt.div (by fun_prop) (by dsimp; intro hz; apply hr; linarith)
  obtain ⟨κ,hκ⟩ := smooth_cosine_lift hh he
  refine ⟨κ,?_⟩
  intro θ hθ
  rw [hκ]
  change (2-2*circleCos θ)*(B (circleCos θ)/(2-2*circleCos θ)) = 1
  have hB : B (circleCos θ) = 1 := B.one_of_mem_closedBall (by
    change dist (circleCos θ) (-1 : ℝ) ≤ 3/4
    linarith)
  rw [hB]
  have hr : circleCos θ ≤ -1/2 := by
    rw [Real.dist_eq] at hθ
    have hp := (le_abs_self (circleCos θ-(-1))).trans hθ
    linarith
  have hd : 2-2*circleCos θ ≠ 0 := by linarith
  rw [← mul_div_assoc,mul_one,div_self hd]

lemma real_mean_positive (g : realAlgebra) (hg : ∀ θ, 0 ≤ realEvaluation θ g)
    {θ₀ : Circle} (hθ : realEvaluation θ₀ g ≠ 0) : 0 < (coeff 0 (g : Space)).re := by
  have hcont : Continuous (fun θ => realEvaluation θ g) :=
    Complex.continuous_re.comp (boundary (g : Space)).continuous
  have hint : Integrable (fun θ => boundary (g : Space) θ) AddCircle.haarAddCircle :=
    (boundary (g : Space)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (coeff 0 (g : Space)).re = ∫ θ, realEvaluation θ g ∂AddCircle.haarAddCircle := by
    change (fourierCoeff (boundary (g : Space)) 0).re = _
    simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
    exact (integral_re hint).symm
  rw [he]
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) hg hθ

end Release061.Wiener

end

end OAI
