import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteDimensionalCompleteGenerator

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
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem tendstoUniformlyOn_fderiv_half_ball_filter
    {ι : Type*} {l : Filter ι} {f : ι → E → F} {g : E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ j in l, DifferentiableOn ℂ (f j) (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R))
    (hfg : TendstoUniformlyOn f g l (ball c R)) :
    TendstoUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) l (ball c (R/2)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hf,Metric.tendstoUniformlyOn_iff.mp hfg (ε*R/8) (by positivity)] with j hj he
  intro x hx
  have hb : ∀ z ∈ ball c R, ‖f j z-g z‖ ≤ ε*R/8 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm,norm_sub_rev] using he z hz)
  have hest := bounded_fderiv_on_half_ball hR (hj.sub hg) hb hx
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  rw [fderiv_sub (hj.differentiableAt (isOpen_ball.mem_nhds hxR))
    (hg.differentiableAt (isOpen_ball.mem_nhds hxR))] at hest
  rw [dist_eq_norm,norm_sub_rev]
  apply hest.trans_lt
  field_simp
  nlinarith

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hU hbd ha ha0 ham

theorem infinitesimalGenerator_uniform_slope (K : Set (Affine n))
    (hK : IsCompact K) (hKU : K⊆U) :
    TendstoUniformlyOn (fun t : ℝ => fun x => t⁻¹ • ((a t).ambientAut x-x))
      (infinitesimalGenerator a) (𝓝[≠] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := productCurve_uniform_consistency hU hbd a (fun _ => 1) ha continuous_const
    ha0 ham rfl (by intro s t; simp) K hK hKU (half_pos hε)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
  have ht0' : t≠0 := ht0
  intro x hx
  have hh := ht x hx
  simp only [mul_one,infinitesimalGenerator_one,Pi.zero_apply,add_zero] at hh
  have heq : t⁻¹ • ((a t).ambientAut x-x)-infinitesimalGenerator a x=
      t⁻¹ • ((a t).ambientAut x-x-t • infinitesimalGenerator a x) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ ht0',one_smul]
  rw [dist_eq_norm,norm_sub_rev,heq,norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |t|⁻¹ *((ε/2)*|t|) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg t))
    _ = ε/2 := by field_simp
    _ < ε := by linarith

theorem oneParameter_fderiv_hasDerivAt_zero (x : Affine n) (hx : x∈U) :
    HasDerivAt (fun t : ℝ => fderiv ℂ (a t).ambientAut x)
      (fderiv ℂ (infinitesimalGenerator a) x) 0 := by
  obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp hU x hx
  let f : ℝ → Affine n → Affine n := fun t z => t⁻¹ • ((a t).ambientAut z-z)
  have hconv : TendstoUniformlyOn f (infinitesimalGenerator a) (𝓝[≠] 0) (ball x (R/2)) := by
    exact (infinitesimalGenerator_uniform_slope hU hbd a ha ha0 ham
      (closedBall x (R/2)) (isCompact_closedBall _ _)
      (fun y hy => hRU (closedBall_subset_ball (by linarith) hy))).mono ball_subset_closedBall
  have hf : ∀ᶠ t : ℝ in 𝓝[≠] 0, DifferentiableOn ℂ (f t) (ball x (R/2)) := by
    filter_upwards [] with t z hz
    exact ((((a t).ambientAut_analytic hU z (hRU (ball_subset_ball (by linarith) hz))).differentiableAt.sub
      differentiableAt_id).const_smul t⁻¹).differentiableWithinAt
  have hg : DifferentiableOn ℂ (infinitesimalGenerator a) (ball x (R/2)) := by
    intro z hz
    exact (infinitesimalGenerator_analytic hU a ha hbd ha0 ham z
      (hRU (ball_subset_ball (by linarith) hz))).differentiableAt.differentiableWithinAt
  have hd := (tendstoUniformlyOn_fderiv_half_ball_filter (half_pos hR) hf hg hconv).tendsto_at
    (show x∈ball x ((R/2)/2) by simp [hR])
  rw [hasDerivAt_iff_tendsto_slope]
  apply hd.congr'
  filter_upwards [] with t
  change fderiv ℂ ((t⁻¹:ℝ) • ((a t).ambientAut-id)) x = _
  rw [fderiv_const_smul (((a t).ambientAut_analytic hU x hx).differentiableAt.sub differentiableAt_id),
    fderiv_sub ((a t).ambientAut_analytic hU x hx).differentiableAt differentiableAt_id,fderiv_id]
  simp only [slope_def_module,sub_zero,ha0]
  change t⁻¹ • (fderiv ℂ (a t).ambientAut x-1)=t⁻¹ • (fderiv ℂ (a t).ambientAut x-(1 : Biholomorph U U).derivativeAt ⟨x,hx⟩)
  rw [derivativeAt_one hU]
end Biholomorph
end Release061

end

end OAI
