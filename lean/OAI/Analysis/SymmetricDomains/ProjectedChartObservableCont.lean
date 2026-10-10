import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteNashCoverVertical

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

section
open Set Filter Topology Metric
open scoped NNReal

theorem continuous_differential_of_everywhere_strict
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F)
    (hD : ∀ x, HasStrictFDerivAt f (D x) x) : Continuous D := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c : ℝ≥0 := ⟨ε/2, (half_pos hε).le⟩
  obtain ⟨S,hS,happrox⟩ := (hD x).approximates_deriv_on_nhds (c := c) (Or.inr (half_pos hε))
  obtain ⟨W,hWS,hWo,hxW⟩ := _root_.mem_nhds_iff.mp hS
  filter_upwards [hWo.mem_nhds hxW] with y hy
  have hyD : HasFDerivAt (fun z => f z-D x z) (D y-D x) y :=
    (hD y).hasFDerivAt.sub (D x).hasFDerivAt
  have hb := hyD.le_of_lipschitzOn (hWo.mem_nhds hy) (happrox.lipschitzOnWith.mono hWS)
  rw [dist_eq_norm]
  exact hb.trans_lt (half_lt_self hε)

theorem contDiff_one_of_everywhere_strict
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (h : ∀ x, ∃ D : E →L[ℝ] F, HasStrictFDerivAt f D x) :
    ContDiff ℝ 1 f := by
  choose D hD using h
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨D,continuous_differential_of_everywhere_strict f D hD,fun x => (hD x).hasFDerivAt⟩
end

open Set Filter Topology

theorem projected_chart_observable_contDiffAt
    {A : Type*} [TopologicalSpace A] {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : OpenPartialHomeomorph A E) (a : A) (ha : a∈e.source)
    (F : E → A) (hF : Continuous F) (hF0 : F 0=a)
    (hd : HasStrictFDerivAt (fun x => e (F x)) (ContinuousLinearMap.id ℝ E) 0)
    (hD : ContDiffAt ℝ 1 (fun x => e (F x)) 0)
    (G : A → H) (hG : ContDiffAt ℝ 1 (fun x => G (F x)) 0) :
    ContDiffAt ℝ 1 (fun y => G (e.symm y)) (e a) := by
  have hd' : HasStrictFDerivAt (fun x => e (F x))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := hd
  let I := hd'.localInverse (fun x => e (F x)) (ContinuousLinearEquiv.refl ℝ E) 0
  have hI : HasStrictFDerivAt I (ContinuousLinearMap.id ℝ E) (e a) := by
    simpa [I,hF0] using hd'.to_localInverse
  have hIC1 : ContDiffAt ℝ 1 I (e a) := by
    simpa only [ContDiffAt.localInverse,hF0] using hD.to_localInverse hd'.hasFDerivAt (by decide : (1 : WithTop ℕ∞)≠0)
  have hI0 : I (e a)=0 := by
    simpa only [hF0] using hd'.localInverse_apply_image
  have hcomp : ContDiffAt ℝ 1 (fun y => G (F (I y))) (e a) := by
    have hg := hG
    rw [←hI0] at hg
    exact hg.comp (e a) hIC1
  apply hcomp.congr_of_eventuallyEq
  have hFI : Tendsto (fun y => F (I y)) (𝓝 (e a)) (𝓝 a) := by
    have ht := hF.continuousAt.tendsto.comp hI.continuousAt.tendsto
    simpa only [Function.comp_def,hI0,hF0] using ht
  have hmem : ∀ᶠ y in 𝓝 (e a), F (I y)∈e.source :=
    hFI (e.open_source.mem_nhds ha)
  have hright : ∀ᶠ y in 𝓝 (e a), e (F (I y))=y := by
    simpa only [hF0] using hd'.eventually_right_inverse
  filter_upwards [hmem,hright] with y hym hyr
  have he : e.symm y=F (I y) := by
    calc
      e.symm y=e.symm (e (F (I y))) := congrArg e.symm hyr.symm
      _=F (I y) := e.left_inv hym
  simp only [he]
end Release061

end

end OAI
