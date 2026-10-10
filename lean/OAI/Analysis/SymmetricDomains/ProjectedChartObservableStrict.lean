import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicBoundaryFiniteNash

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

theorem openChart_of_projected_parametrization
    {A : Type*} [TopologicalSpace A] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (q : A → E) (hq : Continuous q) (a : A)
    (W : Set A) (hW : W∈𝓝 a) (hinj : Set.InjOn q W)
    (F : E → A) (hF : Continuous F) (hF0 : F 0=a)
    (hd : HasStrictFDerivAt (fun x => q (F x)) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ e : OpenPartialHomeomorph A E, (e : A → E)=q ∧ a∈e.source := by
  obtain ⟨V,hVW,hVo,haV⟩ := mem_nhds_iff.mp hW
  have hi : Set.InjOn q V := hinj.mono hVW
  have hd' : HasStrictFDerivAt (fun x => q (F x))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := hd
  let e0 := hd'.toOpenPartialHomeomorph (fun x => q (F x))
  let e := e0.restrOpen (F ⁻¹' V) (hVo.preimage hF)
  have he0 : 0∈e.source := ⟨hd'.mem_toOpenPartialHomeomorph_source,by simpa only [mem_preimage,hF0] using haV⟩
  have hev (x : E) : e x=q (F x) := rfl
  have hFe {x : E} (hx : x∈e.target) : F (e.symm x)∈V := (e.map_target hx).2
  have hqFe {x : E} (hx : x∈e.target) : q (F (e.symm x))=x := e.right_inv hx
  let c : OpenPartialHomeomorph A E :=
    { toFun := q
      invFun := fun x => F (e.symm x)
      source := V∩q ⁻¹' e.target
      target := e.target
      map_source' := fun _ hx => hx.2
      map_target' := fun _ hx => ⟨hFe hx,by simpa only [mem_preimage,hqFe hx] using hx⟩
      left_inv' := fun _ hx => hi (hFe hx.2) hx.1 (hqFe hx.2)
      right_inv' := fun _ hx => hqFe hx
      open_source := hVo.inter (e.open_target.preimage hq)
      open_target := e.open_target
      continuousOn_toFun := hq.continuousOn
      continuousOn_invFun := hF.comp_continuousOn e.continuousOn_symm }
  refine ⟨c,rfl,haV,?_⟩
  have hem := e.map_source he0
  simpa only [mem_preimage,hev,hF0] using hem
end

open Set Filter Topology

theorem projected_chart_observable_hasStrictFDerivAt
    {A : Type*} [TopologicalSpace A] {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : OpenPartialHomeomorph A E) (a : A) (ha : a∈e.source)
    (F : E → A) (hF : Continuous F) (hF0 : F 0=a)
    (hd : HasStrictFDerivAt (fun x => e (F x)) (ContinuousLinearMap.id ℝ E) 0)
    (G : A → H) (L : E →L[ℝ] H)
    (hG : HasStrictFDerivAt (fun x => G (F x)) L 0) :
    HasStrictFDerivAt (fun y => G (e.symm y)) L (e a) := by
  have hd' : HasStrictFDerivAt (fun x => e (F x))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := hd
  let I := hd'.localInverse (fun x => e (F x)) (ContinuousLinearEquiv.refl ℝ E) 0
  have hI : HasStrictFDerivAt I (ContinuousLinearMap.id ℝ E) (e a) := by
    simpa [I,hF0] using hd'.to_localInverse
  have hI0 : I (e a)=0 := by
    simpa only [hF0] using hd'.localInverse_apply_image
  have hcomp : HasStrictFDerivAt (fun y => G (F (I y))) L (e a) := by
    have hg := hG
    rw [←hI0] at hg
    simpa only [ContinuousLinearMap.comp_id] using hg.comp (e a) hI
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
