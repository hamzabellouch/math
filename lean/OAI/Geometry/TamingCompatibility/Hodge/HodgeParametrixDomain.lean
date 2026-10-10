import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCompactExtension
import OAI.Geometry.TamingCompatibility.Hodge.HodgeNormalInverse

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixDomainMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixDomainMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)

def parametrixDomain (O : Set Space) : Set (Space × Space) :=
  (geometricNormalChart g B hg hB q₀ Bq hBq).source ∩
  (geometricNormalChart g B hg hB q₀ Bq hBq) ⁻¹'
    inverseRegularDomain (geometricNormalChart g B hg hB q₀ Bq hBq) ∩
  gaugedDomain J α ht p D g B ∩
  (fun x : Space × Space => normalMap g B x.1 x.2) ⁻¹' O

lemma parametrixDomain_open (O : Set Space) (hO : IsOpen O) :
    IsOpen (parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O) :=
  (((geometricNormalChart g B hg hB q₀ Bq hBq).open_source.inter
    ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).preimage
      (geometricNormalChart_smooth g B hg hB q₀ Bq hBq).continuous)).inter
        (gaugedDomain_open J α ht p D g B hg hB)).inter
    (hO.preimage (normalMap_joint g B hg hB).continuous)

lemma parametrixDomain_center (O : Set Space) (hqO : q₀ ∈ O)
    (hactual : ActualData J α ht p D q₀ g B) :
    (q₀,0) ∈ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O := by
  refine ⟨⟨⟨?_,?_⟩,hactual.center J α ht p D g B⟩,?_⟩
  · exact centeredChart_mem_source B (metricJet g B) hB (metricJet_contDiff g B hg hB) q₀ Bq hBq
  · simpa only [Set.mem_preimage,geometricNormalChart_apply,normalMap_zero]
      using geometricNormalChart_center g B hg hB q₀ Bq hBq
  · simpa only [Set.mem_preimage,normalMap_zero] using hqO

lemma exists_parametrix_tube (O : Set Space) (hO : IsOpen O) (hqO : q₀ ∈ O)
    (hactual : ActualData J α ht p D q₀ g B) :
    ∃ a : ℝ, 0 < a ∧ Metric.closedBall q₀ a ×ˢ Metric.closedBall (0 : Space) a ⊆
      parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O := by
  obtain ⟨a,ha,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((parametrixDomain_open J α ht p D g B hg hB q₀ Bq hBq O hO).mem_nhds
      (parametrixDomain_center J α ht p D g B hg hB q₀ Bq hBq O hqO hactual))
  refine ⟨a,ha,?_⟩
  rintro ⟨q,z⟩ ⟨hq,hz⟩
  apply hsub
  rw [Metric.mem_closedBall,Prod.dist_eq]
  exact max_le hq hz

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {E F W : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup W]
attribute [local instance] Classical.propDecidable

def push (C : OpenPartialHomeomorph E F) (f : E → W) (y : F) : W :=
  if y ∈ C.target then f (C.symm y) else 0

lemma push_apply (C : OpenPartialHomeomorph E F) (f : E → W) {x : E} (hx : x ∈ C.source) :
    push C f (C x) = f x := by
  simp [push,C.map_source hx,C.left_inv hx]

lemma support_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hf : Function.support f ⊆ K) : Function.support (push C f) ⊆ C '' K := by
  intro y hy
  have ht : y ∈ C.target := by
    by_contra h
    exact hy (by simp [push,h])
  refine ⟨C.symm y,hf ?_,C.right_inv ht⟩
  simpa [Function.mem_support,push,ht] using hy

lemma tsupport_push_subset (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hf : Function.support f ⊆ K) :
    tsupport (push C f) ⊆ C '' K :=
  closure_minimal (support_push_subset C f K hf)
    (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed

lemma push_hasCompactSupport (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hf : Function.support f ⊆ K) :
    HasCompactSupport (push C f) :=
  (hK.image_of_continuousOn (C.continuousOn.mono hKC)).of_isClosed_subset
    isClosed_closure (tsupport_push_subset C f K hK hKC hf)

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ W]

lemma push_contDiff (C : OpenPartialHomeomorph E F) (f : E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hfK : Function.support f ⊆ K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ (C.symm : F → E) (C x)) :
    ContDiff ℝ ∞ (push C f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ C '' K
  · obtain ⟨x,hx,rfl⟩ := hy
    have ht := C.map_source (hKC hx)
    have he : push C f =ᶠ[𝓝 (C x)] (fun y => f (C.symm y)) := by
      filter_upwards [C.open_target.mem_nhds ht] with y hy
      simp [push,hy]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hfx : ContDiffAt ℝ ∞ f (C.symm (C x)) := by simpa [C.left_inv (hKC hx)] using hf x hx
    exact hfx.comp (C x) (hC x hx)
  · have hc : _root_.IsClosed (C '' K) := (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds hy] with z hz
    apply Function.notMem_support.mp
    exact fun h => hz (support_push_subset C f K hfK h)

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelExtension
open Set Filter
open scoped Topology ContDiff
variable {P E F W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] Classical.propDecidable

lemma push_family_contDiffAt (C : OpenPartialHomeomorph E F) (f : P → E → W) (K : Set E)
    (hK : IsCompact K) (hKC : K ⊆ C.source) (hfK : ∀ p, Function.support (f p) ⊆ K)
    {p : P} (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ (fun v : P × E => f v.1 v.2) (p,x))
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ (C.symm : F → E) (C x)) (y : F) :
    ContDiffAt ℝ ∞ (fun v : P × F => push C (f v.1) v.2) (p,y) := by
  by_cases hy : y ∈ C '' K
  · obtain ⟨x,hx,rfl⟩ := hy
    have ht := C.map_source (hKC hx)
    have he : (fun v : P × F => push C (f v.1) v.2) =ᶠ[𝓝 (p,C x)]
        (fun v : P × F => f v.1 (C.symm v.2)) := by
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds ht)] with v hv
      have hv' : v.2 ∈ C.target := hv
      simp [push,hv']
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hfx : ContDiffAt ℝ ∞ (fun v : P × E => f v.1 v.2) (p,C.symm (C x)) := by
      simpa [C.left_inv (hKC hx)] using hf x hx
    exact hfx.comp (p,C x) (contDiffAt_fst.prodMk ((hC x hx).comp (p,C x) contDiffAt_snd))
  · have hc : _root_.IsClosed (C '' K) := (hK.image_of_continuousOn (C.continuousOn.mono hKC)).isClosed
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hy)] with v hv
    apply Function.notMem_support.mp
    exact fun h => hv (support_push_subset C (f v.1) K (hfK v.1) h)

end TamingCompatibility.GeometricHilbert.KernelExtension

end
end

end

end OAI
