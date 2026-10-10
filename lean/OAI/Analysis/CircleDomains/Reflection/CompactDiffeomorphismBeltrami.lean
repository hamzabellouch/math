import OAI.Analysis.CircleDomains.Reflection.SmoothBeltramiDistortion
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! A smooth plane diffeomorphism fixed near infinity has an actual smooth,
compactly supported complex dilatation, uniformly bounded strictly below one. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_homeomorph_fderiv_injective (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (z : ℂ) : Injective (fderiv ℝ (P : ℂ → ℂ) z) := by
  have he := ((hi.differentiable (by simp) (P z)).hasFDerivAt.comp z
    (hs.differentiable (by simp) z).hasFDerivAt).fderiv
  have hid : (P.symm : ℂ → ℂ) ∘ P=id := funext P.symm_apply_apply
  rw [hid,fderiv_id] at he
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  simpa only [ContinuousLinearMap.comp_apply,hv,map_zero,ContinuousLinearMap.id_apply] using hh

lemma smooth_homeomorph_wirtinger_gap_ne_zero (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    (z : ℂ) : ‖partialZ P z‖^2-‖partialBar P z‖^2≠0 := by
  have hinj := smooth_homeomorph_fderiv_injective P hs hi z
  let E : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective (fderiv ℝ (P : ℂ → ℂ) z).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩
  have hn : (fderiv ℝ (P : ℂ → ℂ) z).det≠0 := E.isUnit_det'.ne_zero
  rwa [realCLM_det_wirtinger _ _ _ (fderiv_wirtinger P z)] at hn

lemma homeomorph_partials_eq_id_off (P : ℂ ≃ₜ ℂ) {R : ℝ}
    (hfix : ∀z,R≤‖z‖ → P z=z) {z : ℂ} (hz : R<‖z‖) :
    partialZ P z=1 ∧ partialBar P z=0 := by
  have he : (P : ℂ → ℂ)=ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact hfix w hw.le
  have hid : id=(fun w : ℂ => w) := rfl
  simpa only [partialZ,partialBar,he.fderiv_eq,hid] using partials_id z

lemma compact_diffeomorphism_wirtinger_gap_pos (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {R : ℝ} (hfix : ∀z,R≤‖z‖ → P z=z) (z : ℂ) :
    0<‖partialZ P z‖^2-‖partialBar P z‖^2 := by
  let q := fun w => ‖partialZ P w‖^2-‖partialBar P w‖^2
  have hq : Continuous q := (contDiff_partials hs).1.continuous.norm.pow 2 |>.sub
    ((contDiff_partials hs).2.continuous.norm.pow 2)
  let a : ℂ := ((max R 0+1 : ℝ) : ℂ)
  have ha : R<‖a‖ := by
    dsimp [a]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
    linarith [le_max_left R 0]
  have hqa : q a=1 := by
    obtain ⟨hZ,hB⟩ := homeomorph_partials_eq_id_off P hfix ha
    simp only [q,hZ,hB,norm_one,norm_zero,one_pow,zero_pow (by decide : 2≠0),sub_zero]
  by_contra hn
  have hz : q z≤0 := le_of_not_gt hn
  obtain ⟨w,hw⟩ := intermediate_value_univ z a hq ⟨hz,by rw [hqa];norm_num⟩
  exact smooth_homeomorph_wirtinger_gap_ne_zero P hs hi w hw

lemma compact_diffeomorphism_beltrami (P : ℂ ≃ₜ ℂ)
    (hs : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {R : ℝ} (hfix : ∀z,R≤‖z‖ → P z=z) :
    ∃ (μ : ℂ → ℂ) (k S : ℝ),ContDiff ℝ ∞ μ ∧ 0≤k ∧ k<1 ∧ 0<S ∧
      (∀z,‖μ z‖≤k) ∧ (∀z,S≤‖z‖ → μ z=0) ∧
      ∀z,partialBar P z=μ z*partialZ P z := by
  have hgap := compact_diffeomorphism_wirtinger_gap_pos P hs hi hfix
  have hZ (z : ℂ) : partialZ P z≠0 := by
    intro hz
    have hh := hgap z
    rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_sub] at hh
    nlinarith [sq_nonneg ‖partialBar P z‖]
  let μ := fun z => partialBar P z/partialZ P z
  have hμs : ContDiff ℝ ∞ μ := by
    convert (contDiff_partials hs).2.mul ((contDiff_partials hs).1.inv hZ) using 1
    rfl
  have hμlt (z : ℂ) : ‖μ z‖<1 := by
    change ‖partialBar P z/partialZ P z‖<1
    rw [norm_div,div_lt_one (norm_pos_iff.mpr (hZ z))]
    nlinarith [hgap z,norm_nonneg (partialZ P z),norm_nonneg (partialBar P z)]
  let S := max R 0+1
  have hS : 0<S := by dsimp [S];linarith [le_max_right R 0]
  have hzero (z : ℂ) (hz : S≤‖z‖) : μ z=0 := by
    have hz' : R<‖z‖ := by dsimp [S] at hz;linarith [le_max_left R 0]
    change partialBar P z/partialZ P z=0
    rw [(homeomorph_partials_eq_id_off P hfix hz').2,zero_div]
  obtain ⟨a,ha,hm⟩ := (isCompact_closedBall (0:ℂ) S).exists_isMaxOn
    ⟨0,mem_closedBall_self hS.le⟩ hμs.continuous.norm.continuousOn
  let k := (‖μ a‖+1)/2
  have hk : 0≤k := by dsimp [k];positivity
  have hk1 : k<1 := by dsimp [k];linarith [hμlt a]
  refine ⟨μ,k,S,hμs,hk,hk1,hS,?_,hzero,?_⟩
  · intro z
    by_cases hz : z∈closedBall (0:ℂ) S
    · have hb : ‖μ z‖≤‖μ a‖ := hm hz
      dsimp [k]
      linarith [hμlt a]
    · rw [hzero z (le_of_lt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)),norm_zero]
      exact hk
  · intro z
    exact (div_mul_cancel₀ (partialBar P z) (hZ z)).symm

end CircleDomainRigidity

end

end OAI
