import Mathlib
import OAI.Analysis.SymmetricDomains.OneParameterFderivDeriv

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
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem ambientAut_second_derivative_joint_continuousAt {q : Biholomorph U U × Affine n} (hq : q.2∈U) :
    ContinuousAt (fun z : Biholomorph U U × Affine n => fderiv ℂ (fderiv ℂ z.1.ambientAut) z.2) q := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro z hz
  have ha := continuous_fst.tendsto q |>.comp hz
  have hx := continuous_snd.tendsto q |>.comp hz
  have hxu : Tendsto (fun j => (z j).2) atTop (𝓝[U] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,hx (hU.mem_nhds hq)⟩
  have hf := tendstoLocallyUniformlyOn_fderiv hU (ambientAut_tendstoLocallyUniformly ha)
    (fun x hx => ⟨U,hU.mem_nhds hx,Eventually.of_forall
      (fun j => ((z j).1.ambientAut_analytic hU).differentiableOn)⟩)
  have hf2 := tendstoLocallyUniformlyOn_fderiv hU hf
    (fun x hx => ⟨U,hU.mem_nhds hx,Eventually.of_forall
      (fun j y hy => ((z j).1.ambientAut_analytic hU y hy).fderiv.differentiableAt.differentiableWithinAt)⟩)
  exact hf2.tendsto_comp (q.1.ambientAut_analytic hU q.2 hq).fderiv.fderiv.continuousAt.continuousWithinAt hq hxu

variable (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hbd ha ha0 ham

theorem oneParameter_derivativeAt_hasDerivAt (s : ℝ) (p : U) :
    HasDerivAt (fun t => (a t).derivativeAt p)
      ((fderiv ℂ (infinitesimalGenerator a) ((a s).toHomeomorph p).val).comp ((a s).derivativeAt p)) s := by
  let y : U := (a s).toHomeomorph p
  have hd0 := oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham y.val y.property
  have hd0' : HasDerivAt (fun t => (a t).derivativeAt y)
      (fderiv ℂ (infinitesimalGenerator a) y.val) (s-s) := by simpa only [sub_self,derivativeAt] using hd0
  have his : HasDerivAt (fun t : ℝ => t-s) 1 s := by simpa only [id_eq] using (hasDerivAt_id s).sub_const s
  have hdt := hd0'.scomp s (h := fun t : ℝ => t-s) his
  simp only [one_smul] at hdt
  let L := ((ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).flip
    ((a s).derivativeAt p)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt s hdt
  have he (t : ℝ) : (a t).derivativeAt p=((a (t-s)).derivativeAt y).comp ((a s).derivativeAt p) := by
    have hat : a t=a (t-s)*a s := by rw [← ham,sub_add_cancel]
    rw [hat,derivativeAt_mul hU]
  have heq : (fun t => (a t).derivativeAt p)=(fun t => ((a (t-s)).derivativeAt y).comp ((a s).derivativeAt p)) := funext he
  rw [heq]
  exact hd

theorem oneParameter_derivative_joint_hasStrictFDerivAt (s : ℝ) (p : U) :
    HasStrictFDerivAt (fun z : ℝ × Affine n => fderiv ℂ (a z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        ((fderiv ℂ (infinitesimalGenerator a) ((a s).toHomeomorph p).val).comp ((a s).derivativeAt p))).coprod
        ((fderiv ℂ (fderiv ℂ (a s).ambientAut) p.val).restrictScalars ℝ)) (s,p.val) := by
  have hn : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,p.val), z.2∈U :=
    continuous_snd.continuousAt (hU.mem_nhds p.property)
  have hj : ContinuousAt (fun z : ℝ × Affine n => (a z.1).ambientAut z.2) (s,p.val) :=
    (ambientAut_joint_continuousAt hU p.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hdj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (a z.1).ambientAut z.2) (s,p.val) :=
    (ambientAut_derivative_joint_continuousAt hU p.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hddj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (fderiv ℂ (a z.1).ambientAut) z.2) (s,p.val) :=
    (ambientAut_second_derivative_joint_continuousAt hU p.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hXj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (infinitesimalGenerator a) ((a z.1).ambientAut z.2)) (s,p.val) := by
    have hX := (infinitesimalGenerator_analytic hU a ha hbd ha0 ham
      ((a s).toHomeomorph p).val ((a s).toHomeomorph p).property).fderiv.continuousAt
    have hX' : ContinuousAt (fderiv ℂ (infinitesimalGenerator a)) ((a s).ambientAut p.val) := by simpa only [ambientAut_apply] using hX
    exact hX'.comp (x := (s,p.val)) hj
  have ht := hXj.clm_comp hdj
  have h1 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,p.val), HasFDerivAt
      (fun t => fderiv ℂ (a t).ambientAut z.2)
      (ContinuousLinearMap.toSpanSingleton ℝ ((fderiv ℂ (infinitesimalGenerator a) ((a z.1).ambientAut z.2)).comp (fderiv ℂ (a z.1).ambientAut z.2))) z.1 := by
    filter_upwards [hn] with z hz
    simpa only [ambientAut_apply (a _) ⟨z.2,hz⟩,derivativeAt] using
      (oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham z.1 ⟨z.2,hz⟩).hasFDerivAt
  have h2 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,p.val), HasFDerivAt
      (fun y => fderiv ℂ (a z.1).ambientAut y)
      ((fderiv ℂ (fderiv ℂ (a z.1).ambientAut) z.2).restrictScalars ℝ) z.2 := by
    filter_upwards [hn] with z hz
    exact ((a z.1).ambientAut_analytic hU z.2 hz).fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (u := (s,p.val)) (f := fun t y => fderiv ℂ (a t).ambientAut y)
    (f₁ := fun t y => ContinuousLinearMap.toSpanSingleton ℝ
      ((fderiv ℂ (infinitesimalGenerator a) ((a t).ambientAut y)).comp (fderiv ℂ (a t).ambientAut y)))
    (f₂ := fun t y => (fderiv ℂ (fderiv ℂ (a t).ambientAut) y).restrictScalars ℝ) h1 h2
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Affine n →L[ℂ] Affine n)).continuous.continuousAt.comp ht)
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).continuousAt.comp hddj)
  dsimp only [Function.HasUncurry.uncurry,Function.hasUncurryInduction,Function.hasUncurryBase,id_eq] at hd
  simpa only [ambientAut_apply,derivativeAt] using hd
end Biholomorph
end Release061

end

end OAI
