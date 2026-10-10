import Mathlib
import OAI.Analysis.SymmetricDomains.InfinitesimalGeneratorEquivariant

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
namespace Release061
open Set Filter Topology Metric MeasureTheory
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem ambientAut_joint_continuousAt {q : Biholomorph U U × Affine n} (hq : q.2 ∈ U) :
    ContinuousAt (fun z : Biholomorph U U × Affine n => z.1.ambientAut z.2) q := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro z hz
  have ha := continuous_fst.tendsto q |>.comp hz
  have hx := continuous_snd.tendsto q |>.comp hz
  have hxu : Tendsto (fun j => (z j).2) atTop (𝓝[U] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,hx (hU.mem_nhds hq)⟩
  exact (ambientAut_tendstoLocallyUniformly ha).tendsto_comp
    ((q.1.ambientAut_analytic hU q.2 hq).continuousAt.continuousWithinAt) hq hxu

theorem ambientAut_derivative_joint_continuousAt {q : Biholomorph U U × Affine n} (hq : q.2 ∈ U) :
    ContinuousAt (fun z : Biholomorph U U × Affine n => fderiv ℂ z.1.ambientAut z.2) q := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro z hz
  have ha := continuous_fst.tendsto q |>.comp hz
  have hx := continuous_snd.tendsto q |>.comp hz
  have hxu : Tendsto (fun j => (z j).2) atTop (𝓝[U] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,hx (hU.mem_nhds hq)⟩
  have hf := tendstoLocallyUniformlyOn_fderiv hU (ambientAut_tendstoLocallyUniformly ha)
    (fun x hx => ⟨U,hU.mem_nhds hx,Eventually.of_forall
      (fun j => ((z j).1.ambientAut_analytic hU).differentiableOn)⟩)
  exact hf.tendsto_comp (q.1.ambientAut_analytic hU q.2 hq).fderiv.continuousAt.continuousWithinAt hq hxu

variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include ha

theorem oneParameter_joint_hasStrictFDerivAt (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (s : ℝ) (x : U) :
    HasStrictFDerivAt (fun z : ℝ × Affine n => (a z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator a ((a s).toHomeomorph x).val)).coprod
        (((a s).derivativeAt x).restrictScalars ℝ)) (s,x.val) := by
  have hn : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,x.val), z.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds x.property)
  have hj : ContinuousAt (fun z : ℝ × Affine n => (a z.1).ambientAut z.2) (s,x.val) :=
    (ambientAut_joint_continuousAt hU x.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hdj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (a z.1).ambientAut z.2) (s,x.val) :=
    (ambientAut_derivative_joint_continuousAt hU x.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have ht : ContinuousAt (fun z : ℝ × Affine n => infinitesimalGenerator a ((a z.1).ambientAut z.2)) (s,x.val) := by
    have hg : ContinuousAt (infinitesimalGenerator a) ((a s).ambientAut x.val) := by
      simpa only [ambientAut_apply] using
        (infinitesimalGenerator_analytic hU a ha hb hzero hmul
          ((a s).toHomeomorph x).val ((a s).toHomeomorph x).property).continuousAt
    exact hg.comp (x := (s,x.val)) hj
  have h1 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,x.val), HasFDerivAt
      (fun t => (a t).ambientAut z.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator a ((a z.1).ambientAut z.2))) z.1 := by
    filter_upwards [hn] with z hz
    simpa only [ambientAut_apply (a _) ⟨z.2,hz⟩] using
      (oneParameter_orbit_ODE hU a ha hb hzero hmul ⟨z.2,hz⟩ z.1).hasFDerivAt
  have h2 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,x.val), HasFDerivAt
      (fun y => (a z.1).ambientAut y)
      ((fderiv ℂ (a z.1).ambientAut z.2).restrictScalars ℝ) z.2 := by
    filter_upwards [hn] with z hz
    exact ((a z.1).ambientAut_analytic hU z.2 hz).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (u := (s,x.val)) (f := fun t y => (a t).ambientAut y)
    (f₁ := fun t y => ContinuousLinearMap.toSpanSingleton ℝ
      (infinitesimalGenerator a ((a t).ambientAut y)))
    (f₂ := fun t y => (fderiv ℂ (a t).ambientAut y).restrictScalars ℝ) h1 h2
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Affine n)).continuous.continuousAt.comp ht)
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).continuousAt.comp hdj)
  dsimp only [Function.HasUncurry.uncurry, Function.hasUncurryInduction,
    Function.hasUncurryBase, id_eq] at h
  simpa only [ambientAut_apply,derivativeAt] using h

end Biholomorph
end Release061

end

end OAI
