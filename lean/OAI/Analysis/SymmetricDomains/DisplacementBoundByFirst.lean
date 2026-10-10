import Mathlib
import OAI.Analysis.SymmetricDomains.SmallAutomorphismsHaveNonzero

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
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem normalized_displacement_firstJet_not_vanishing
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (h : ℕ → ℝ) (hp : ∀ i, 0<h i)
    (hh : Tendsto h atTop (𝓝 0)) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hbound : ∀ i, ∀ x∈closedBall p.val R, ‖(q i).ambientAut x-x‖≤h i)
    (hmax : ∀ i, ∃ x∈closedBall p.val R, h i≤‖(q i).ambientAut x-x‖)
    (hval : Tendsto (fun i => (h i)⁻¹ • ((q i).ambientAut p.val-p.val)) atTop (𝓝 0))
    (hder : Tendsto (fun i => (h i)⁻¹ • ((q i).derivativeAt p-1)) atTop (𝓝 0)) : False := by
  obtain ⟨X,hX,hXne,φ,hφ,hconv⟩ := normalized_automorphisms_have_nonzero_complete_limit hU hc hbd Γ hhol q h hp hh p hR hRU hbound hmax
  have hv : X p.val=0 := tendsto_nhds_unique (hconv.tendsto_at (mem_ball_self hR)) (hval.comp hφ.tendsto_atTop)
  let f : ℕ → Affine n → Affine n := fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)
  have hsmall : closedBall p.val (R/2)⊆ball p.val R := closedBall_subset_ball (half_lt_self hR)
  have hu : TendstoUniformlyOn f X atTop (ball p.val (R/2)) :=
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val (R/2))).mp
      (hconv.mono hsmall)).mono ball_subset_closedBall
  have hsmallU : ball p.val (R/2)⊆U := ball_subset_closedBall.trans (hsmall.trans (ball_subset_closedBall.trans hRU))
  have hfd : ∀ᶠ i in atTop, DifferentiableOn ℂ (f i) (ball p.val (R/2)) := by
    filter_upwards [] with i x hx
    exact ((((q (φ i)).ambientAut_analytic hU x (hsmallU hx)).differentiableAt.sub
      differentiableAt_id).const_smul (h (φ i))⁻¹).differentiableWithinAt
  have hXd := hX.analyticOnNhd hU hbd
  have hd := (tendstoUniformlyOn_fderiv_half_ball_filter (half_pos hR) hfd (hXd.differentiableOn.mono hsmallU) hu).tendsto_at
    (mem_ball_self (show 0<(R/2)/2 by positivity))
  have hde (i : ℕ) : fderiv ℂ (f i) p.val=(h (φ i))⁻¹ • ((q (φ i)).derivativeAt p-1) := by
    change fderiv ℂ ((h (φ i))⁻¹ • ((q (φ i)).ambientAut-id)) p.val=_
    rw [fderiv_const_smul (((q (φ i)).ambientAut_analytic hU p.val p.property).differentiableAt.sub differentiableAt_id),
      fderiv_sub ((q (φ i)).ambientAut_analytic hU p.val p.property).differentiableAt differentiableAt_id,fderiv_id]
    rfl
  simp_rw [hde] at hd
  have hdz : fderiv ℂ X p.val=0 := tendsto_nhds_unique hd (hder.comp hφ.tendsto_atTop)
  obtain ⟨a,ha,ha0,ham,heq⟩ := hX
  have haone : a=(fun _ => 1) := funext fun t => oneParameter_eq_one_of_generator_zero_jet hU a ha hc hbd ha0 ham p
    (by rwa [heq]) (by rwa [heq]) t
  apply hXne
  rw [←heq,haone,infinitesimalGenerator_one]

theorem exists_displacement_bound_by_firstJet
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U) :
    ∃ C : ℝ, 0<C ∧ ∃ W : Set (Biholomorph U U), W∈𝓝 1 ∧
      ∀ a∈W, ∀ x∈closedBall p.val R,
        ‖a.ambientAut x-x‖≤C*(‖a.ambientAut p.val-p.val‖+‖a.derivativeAt p-1‖) := by
  classical
  by_contra hn
  push Not at hn
  let A : Biholomorph U U → ℝ := fun a => ‖a.ambientAut p.val-p.val‖+‖a.derivativeAt p-1‖
  have hAn (a : Biholomorph U U) : 0≤A a := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hex (i : ℕ) : ∃ a : Biholomorph U U,
      dist (firstJet p a) (firstJet p 1)<1/((i:ℝ)+1) ∧
      ∃ x∈closedBall p.val R, ((i:ℝ)+1)*A a<‖a.ambientAut x-x‖ := by
    let W : Set (Biholomorph U U) := firstJet p ⁻¹' ball (firstJet p 1) (1/((i:ℝ)+1))
    have hW : W∈𝓝 1 := (firstJet_continuous hU p).continuousAt.preimage_mem_nhds
      (ball_mem_nhds _ (by positivity))
    obtain ⟨a,ha,x,hx,hl⟩ := hn ((i:ℝ)+1) (by positivity) W hW
    exact ⟨a,ha,x,hx,hl⟩
  choose q hqC x hx hxlarge using hex
  have hq : Tendsto q atTop (𝓝 1) := by
    apply (firstJet_isClosedEmbedding hU hc hbd Γ hhol p).isEmbedding.isInducing.tendsto_nhds_iff.mpr
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun i => dist_nonneg) (fun i => (hqC i).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hne (i : ℕ) : q i≠1 := by
    intro he
    have hs := hxlarge i
    rw [he,ambientAut_apply 1 ⟨x i,hRU (hx i)⟩,one_apply,sub_self,norm_zero] at hs
    exact (not_lt_of_ge (mul_nonneg (by positivity) (hAn 1))) hs
  obtain ⟨h,hp,hh,hbound,hmax⟩ := exists_displacement_maximum_normalization hU hc q hq hne p hR hRU
  have hA (i : ℕ) : (h i)⁻¹*A (q i)≤1/((i:ℝ)+1) := by
    rw [inv_mul_eq_div]
    apply (div_le_div_iff₀ (hp i) (by positivity : (0:ℝ)<(i:ℝ)+1)).mpr
    have hl := (hxlarge i).trans_le (hbound i (x i) (hx i))
    linarith
  have hval : Tendsto (fun i => (h i)⁻¹ • ((q i).ambientAut p.val-p.val)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp i)]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (inv_nonneg.mpr (hp i).le)).trans (hA i)
  have hder : Tendsto (fun i => (h i)⁻¹ • ((q i).derivativeAt p-1)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp i)]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (inv_nonneg.mpr (hp i).le)).trans (hA i)
  exact normalized_displacement_firstJet_not_vanishing hU hc hbd Γ hhol q h hp hh p hR hRU hbound hmax hval hder
end Biholomorph
end Release061

end

end OAI
