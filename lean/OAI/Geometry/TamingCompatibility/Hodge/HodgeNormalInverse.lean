import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Dpos2

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalJets
open Set Filter
open scoped ContDiff Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def inverseRegularDomain (C : OpenPartialHomeomorph V V) : Set V :=
  C.target ∩ (fun y => fderiv ℝ (C : V → V) (C.symm y)) ⁻¹'
    {L : V →L[ℝ] V | L.IsInvertible}

lemma inverseRegularDomain_open (C : OpenPartialHomeomorph V V)
    (hC : ContDiff ℝ ∞ (C : V → V)) : IsOpen (inverseRegularDomain C) := by
  have ho : IsOpen {x : V | (fderiv ℝ (C : V → V) x).IsInvertible} :=
    (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := V) (F := V)).preimage
      (hC.continuous_fderiv (by simp))
  exact C.symm.continuousOn.isOpen_inter_preimage C.open_target ho

lemma inverseRegularDomain_smooth (C : OpenPartialHomeomorph V V)
    (hC : ContDiff ℝ ∞ (C : V → V)) :
    ContDiffOn ℝ ∞ (C.symm : V → V) (inverseRegularDomain C) := by
  intro y hy
  obtain ⟨L,hL⟩ := hy.2
  apply ContDiffAt.contDiffWithinAt
  apply C.contDiffAt_symm (f₀' := L) hy.1
  · rw [hL]
    exact (hC.differentiable (by simp) (C.symm y)).hasFDerivAt
  · exact hC.contDiffAt

end TamingCompatibility.GeometricHilbert.NormalJets

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance normalInverseMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance normalInverseMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q = Bq)

def geometricNormalChart : OpenPartialHomeomorph (Space × Space) (Space × Space) :=
  centeredChart B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq

lemma geometricNormalChart_apply (x : Space × Space) :
    geometricNormalChart g B hg hB q Bq hBq x = (x.1,normalMap g B x.1 x.2) := rfl

lemma geometricNormalChart_smooth :
    ContDiff ℝ ∞ (geometricNormalChart g B hg hB q Bq hBq : Space × Space → Space × Space) :=
  centeredMap_contDiff B (metricJet g B) hB (metricJet_contDiff g B hg hB)

lemma geometricNormalChart_center :
    (q,q) ∈ inverseRegularDomain (geometricNormalChart g B hg hB q Bq hBq) := by
  refine ⟨centeredChart_mem_target B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq,?_⟩
  change (fderiv ℝ (centeredMap B (metricJet g B))
    ((centeredChart B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq).symm (q,q))).IsInvertible
  rw [centeredChart_symm_center]
  have hd := centeredMap_hasStrictFDerivAt B (metricJet g B) hB (metricJet_contDiff g B hg hB) q Bq hBq
  rw [hd.hasFDerivAt.fderiv]
  exact ⟨centeredDerivative Bq,rfl⟩

lemma geometricNormalChart_symm_fst {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).1 = x.1 := by
  have he := (geometricNormalChart g B hg hB q Bq hBq).right_inv hx
  change ((geometricNormalChart g B hg hB q Bq hBq).symm x).1 = x.1
  simpa only [geometricNormalChart_apply] using congrArg Prod.fst he

lemma geometricNormalChart_symm_right {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).target) :
    normalMap g B x.1 ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 := by
  have he := congrArg Prod.snd ((geometricNormalChart g B hg hB q Bq hBq).right_inv hx)
  change normalMap g B ((geometricNormalChart g B hg hB q Bq hBq).symm x).1
    ((geometricNormalChart g B hg hB q Bq hBq).symm x).2 = x.2 at he
  rw [geometricNormalChart_symm_fst g B hg hB q Bq hBq hx] at he
  exact he

lemma geometricNormalChart_symm_left {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q Bq hBq).source) :
    (geometricNormalChart g B hg hB q Bq hBq).symm (x.1,normalMap g B x.1 x.2) = x :=
  (geometricNormalChart g B hg hB q Bq hBq).left_inv hx

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance inverseTubeMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance inverseTubeMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)

def inverseDisplacement (x : Space × Space) : Space :=
  ((geometricNormalChart g B hg hB q₀ Bq hBq).symm (x.1,x.1+x.2)).2

def inverseTubeDomain : Set (Space × Space) :=
  (fun x : Space × Space => (x.1,0)) ⁻¹' (geometricNormalChart g B hg hB q₀ Bq hBq).source ∩
  (fun x : Space × Space => (x.1,x.1+x.2)) ⁻¹'
    inverseRegularDomain (geometricNormalChart g B hg hB q₀ Bq hBq)

lemma inverseTubeDomain_open : IsOpen (inverseTubeDomain g B hg hB q₀ Bq hBq) :=
  ((geometricNormalChart g B hg hB q₀ Bq hBq).open_source.preimage
    (continuous_fst.prodMk continuous_const)).inter
    ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).preimage
      (continuous_fst.prodMk (continuous_fst.add continuous_snd)))

lemma inverseTubeDomain_center : (q₀,0) ∈ inverseTubeDomain g B hg hB q₀ Bq hBq := by
  constructor
  · exact centeredChart_mem_source B (metricJet g B) hB (metricJet_contDiff g B hg hB) q₀ Bq hBq
  · simpa using geometricNormalChart_center g B hg hB q₀ Bq hBq

lemma inverseDisplacement_smooth {x : Space × Space}
    (hx : x ∈ inverseTubeDomain g B hg hB q₀ Bq hBq) :
    ContDiffAt ℝ ∞ (inverseDisplacement g B hg hB q₀ Bq hBq) x := by
  have hc := (inverseRegularDomain_smooth _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq))
    (x.1,x.1+x.2) hx.2
  have hd := hc.contDiffAt ((inverseRegularDomain_open _
    (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).mem_nhds hx.2)
  exact (hd.comp x (contDiffAt_fst.prodMk (contDiffAt_fst.add contDiffAt_snd))).snd

lemma inverseDisplacement_zero {q : Space}
    (hq : (q,0) ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    inverseDisplacement g B hg hB q₀ Bq hBq (q,0) = 0 := by
  have he := geometricNormalChart_symm_left g B hg hB q₀ Bq hBq hq
  simpa [inverseDisplacement] using congrArg Prod.snd he

lemma inverseDisplacement_right {x : Space × Space}
    (hx : x ∈ inverseTubeDomain g B hg hB q₀ Bq hBq) :
    normalMap g B x.1 (inverseDisplacement g B hg hB q₀ Bq hBq x) = x.1+x.2 :=
  geometricNormalChart_symm_right g B hg hB q₀ Bq hBq hx.2.1

lemma exists_inverse_center_ball :
    ∃ a : ℝ, 0 < a ∧ ∃ r : ℝ, 0 < r ∧
      Metric.closedBall q₀ a ×ˢ Metric.closedBall (0 : Space) r ⊆
        inverseTubeDomain g B hg hB q₀ Bq hBq := by
  let O := inverseTubeDomain g B hg hB q₀ Bq hBq
  have hO := inverseTubeDomain_open g B hg hB q₀ Bq hBq
  obtain ⟨s,hs,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hO.mem_nhds (inverseTubeDomain_center g B hg hB q₀ Bq hBq))
  refine ⟨s,hs,s,hs,?_⟩
  rintro ⟨q,z⟩ ⟨hq,hz⟩
  apply hball
  rw [Metric.mem_closedBall,Prod.dist_eq]
  exact max_le hq hz

lemma inverseDisplacement_bound (K : Set Space) (hK : IsCompact K)
    (hKO : K ×ˢ {(0 : Space)} ⊆ inverseTubeDomain g B hg hB q₀ Bq hBq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧
      K ×ˢ Metric.closedBall (0 : Space) r ⊆ inverseTubeDomain g B hg hB q₀ Bq hBq ∧
      ∀ q ∈ K, ∀ w : Space, ‖w‖ ≤ r →
        ‖inverseDisplacement g B hg hB q₀ Bq hBq (q,w)‖ ≤ C*‖w‖ := by
  obtain ⟨C,hC,r,hr,hsub,hbound⟩ := local_linear_bound
    (inverseDisplacement g B hg hB q₀ Bq hBq) K hK
    (inverseTubeDomain g B hg hB q₀ Bq hBq)
    (inverseTubeDomain_open g B hg hB q₀ Bq hBq) hKO
    (fun _ hx => inverseDisplacement_smooth g B hg hB q₀ Bq hBq hx)
  refine ⟨C,hC,r,hr,hsub,fun q hq w hw => ?_⟩
  simpa only [inverseDisplacement_zero g B hg hB q₀ Bq hBq (hKO (show (q,0) ∈ K ×ˢ {(0 : Space)} from ⟨hq,rfl⟩)).1,sub_zero]
    using hbound q hq w hw

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
