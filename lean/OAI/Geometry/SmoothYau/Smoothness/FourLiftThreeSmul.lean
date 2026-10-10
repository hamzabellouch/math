import Mathlib
import OAI.Geometry.SmoothYau.SphereMetric.FourThree

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
def metricPullbackInner (g : SmoothMetric F N) (f : M → N) (x : M) :
    TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).precomp ℝ).comp
    ((g.inner (f x)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x))
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma metricPullbackInner_smooth (g : SmoothMetric F N) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (metricPullbackInner (E:=E) g f x)) := by
  intro x₀
  rw [contMDiffAt_section x₀]
  have hd := (hf x₀).mfderiv_const (m:=∞) (by simp)
  have hg := g.contMDiff (f x₀)
  rw [contMDiffAt_section (f x₀)] at hg
  have hgf := hg.comp x₀ (hf x₀)
  have hh := hd.clm_precomp (F₃:=ℝ) |>.clm_comp (hgf.clm_comp hd)
  apply hh.congr_of_eventuallyEq
  have hn := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E _ x₀)
  have hnf := (hf x₀).continuousAt.eventually ((trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x₀)).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F _ (f x₀)))
  filter_upwards [hn,hnf] with x hx hy
  ext v w
  simp only [hom_trivializationAt_apply,ContinuousLinearMap.comp_apply,inTangentCoordinates,Function.comp_apply,id_eq]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  rw [ContinuousLinearMap.inCoordinates_eq hx hy]
  simp only [ContinuousLinearMap.precomp_apply,ContinuousLinearMap.comp_apply]
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [metricPullbackInner,
    Trivialization.continuousLinearEquivAt_apply,
    Trivialization.continuousLinearEquivAt_symm_apply,
    Trivialization.symm_apply_apply_mk (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (f x₀)) hy]
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff
local instance fourLiftThreeSmul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance fourLiftRealSmul : ContinuousSMul ℝ ℝ := IsBoundedSMul.continuousSMul
def fourProductInner (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold) :
    TangentSpace 𝓘(ℝ,FourModel) x →L[ℝ] TangentSpace 𝓘(ℝ,FourModel) x →L[ℝ] ℝ :=
  metricPullbackInner (E:=FourModel) g fourToThree x+
    metricPullbackInner (E:=FourModel) circleRoundMetric fourToCircle x
lemma fourProductInner_apply (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold) (v w : FourModel) :
    fourProductInner g x v w=g.inner (fourToThree x) (threeModelEquiv (v.1,v.2.1))
      (threeModelEquiv (w.1,w.2.1))+circleRoundMetric.inner (fourToCircle x) v.2.2 w.2.2 := by
  change g.inner (fourToThree x) (mfderiv _ _ fourToThree x v) (mfderiv _ _ fourToThree x w) +
    circleRoundMetric.inner (fourToCircle x) (mfderiv _ _ fourToCircle x v) (mfderiv _ _ fourToCircle x w) = _
  rw [mfderiv_fourToThree,mfderiv_fourToThree,mfderiv_fourToCircle,mfderiv_fourToCircle]

lemma fourProductInner_pos (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold)
    (v : FourModel) (hv : v≠0) : 0<fourProductInner g x v v := by
  rw [fourProductInner_apply]
  by_cases h : threeModelEquiv (v.1,v.2.1)=0
  · have hvc : v.2.2≠0 := by
      intro hc
      apply hv
      have hs := (map_eq_zero_iff threeModelEquiv threeModelEquiv.injective).mp h
      exact Prod.ext (congrArg (Prod.fst : ThreeProductModel → Euclidean 2) hs) (Prod.ext (congrArg (Prod.snd : ThreeProductModel → Euclidean 1) hs) hc)
    exact add_pos_of_nonneg_of_pos (metric_inner_nonneg g _ _) (circleRoundMetric.pos _ _ hvc)
  · exact add_pos_of_pos_of_nonneg (g.pos _ _ h) (metric_inner_nonneg circleRoundMetric _ _)
lemma fourProductInner_bounded (g : SmoothMetric ThreeModel ThreeManifold) (x : FourManifold) :
    Bornology.IsVonNBounded ℝ {v : FourModel | fourProductInner g x v v<1} := by
  let L : FourModel ≃L[ℝ] ThreeModel × Euclidean 1 :=
    (ContinuousLinearEquiv.prodAssoc ℝ (Euclidean 2) (Euclidean 1) (Euclidean 1)).symm.trans
      (threeModelEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Euclidean 1)))
  rw [NormedSpace.isVonNBounded_iff ℝ]
  have hgb := (NormedSpace.isVonNBounded_iff ℝ).mp (show Bornology.IsVonNBounded ℝ
    {v : ThreeModel | g.inner (fourToThree x) v v < 1} from g.isVonNBounded (fourToThree x))
  have hcb := (NormedSpace.isVonNBounded_iff ℝ).mp (show Bornology.IsVonNBounded ℝ
    {v : Euclidean 1 | circleRoundMetric.inner (fourToCircle x) v v < 1} from circleRoundMetric.isVonNBounded (fourToCircle x))
  apply (L.antilipschitz.isBounded_preimage (hgb.prod hcb)).subset
  intro v hv
  change fourProductInner g x v v < 1 at hv
  rw [fourProductInner_apply] at hv
  change g.inner (fourToThree x) (threeModelEquiv (v.1,v.2.1)) (threeModelEquiv (v.1,v.2.1)) < 1 ∧
    circleRoundMetric.inner (fourToCircle x) v.2.2 v.2.2 < 1
  constructor
  · linarith [metric_inner_nonneg circleRoundMetric (fourToCircle x) v.2.2]
  · linarith [metric_inner_nonneg g (fourToThree x) (threeModelEquiv (v.1,v.2.1))]
lemma fourProductInner_smooth (g : SmoothMetric ThreeModel ThreeManifold) :
    ContMDiff 𝓘(ℝ,FourModel) ((𝓘(ℝ,FourModel)).prod 𝓘(ℝ,FourModel →L[ℝ] FourModel →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (FourModel →L[ℝ] FourModel →L[ℝ] ℝ) x (fourProductInner g x)) := by
  intro x₀
  have h1 := metricPullbackInner_smooth g fourToThree fourToThree_smooth x₀
  have h2 := metricPullbackInner_smooth circleRoundMetric fourToCircle fourToCircle_smooth x₀
  rw [contMDiffAt_section x₀] at h1 h2 ⊢
  apply (h1.add h2).congr_of_eventuallyEq
  have hn := (trivializationAt FourModel (TangentSpace 𝓘(ℝ,FourModel)) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt FourModel _ x₀)
  filter_upwards [hn] with x hx
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [hom_trivializationAt_apply,add_apply,Pi.add_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp),inCoordinates_apply_eq₂ hx hx (by simp),inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [fourProductInner, add_apply, map_add]

def fourProductMetric (g : SmoothMetric ThreeModel ThreeManifold) : SmoothMetric FourModel FourManifold where
  inner := fourProductInner g
  symm x v w := by
    change fourProductInner g x (v:FourModel) (w:FourModel)=fourProductInner g x (w:FourModel) (v:FourModel)
    erw [fourProductInner_apply,fourProductInner_apply,g.symm,circleRoundMetric.symm]
  pos := fourProductInner_pos g
  isVonNBounded := fourProductInner_bounded g
  contMDiff := fourProductInner_smooth g

end YauCounterexamples
end

end OAI
