import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatJointSmooth
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixDomain

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixPatchMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixPatchMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

def leadingCoordinate (ψ χ : Space → ℝ) (t : ℝ) (x : Space × Space) : W →L[ℝ] W :=
  (ψ x.1 * χ x.2 * FlatHeat.heat t x.2) • normalGauge J α ht p D g B x

def leadingPatch (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  KernelExtension.push (geometricNormalChart g B hg hB q₀ Bq hBq)
    (leadingCoordinate J α ht p D g B ψ χ t)

lemma leadingCoordinate_support (ψ χ : Space → ℝ) (t : ℝ) :
    Function.support (leadingCoordinate J α ht p D g B ψ χ t) ⊆
      Function.support ψ ×ˢ Function.support χ := by
  intro x hx
  constructor
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp
  · intro h
    apply hx
    apply ContinuousLinearMap.ext
    intro u
    simp only [leadingCoordinate,smul_apply,h,zero_apply]
    simp

lemma leadingCoordinate_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    {t : ℝ} (htpos : 0 < t) {x : Space × Space}
    (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      leadingCoordinate J α ht p D g B ψ χ v.1 v.2) (t,x) := by
  have hψ' : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => ψ v.2.1) (t,x) :=
    hψ.contDiffAt.comp (t,x) contDiffAt_snd.fst
  have hχ' : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => χ v.2.2) (t,x) :=
    hχ.contDiffAt.comp (t,x) contDiffAt_snd.snd
  have hh : ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) => FlatHeat.heat v.1 v.2.2) (t,x) :=
    (FlatHeat.heat_joint_contDiffAt (x := (t,x.2)) (ne_of_gt htpos)).comp (t,x)
      (contDiffAt_fst.prodMk contDiffAt_snd.snd)
  exact ((hψ'.mul hχ').mul hh).smul
    ((normalGauge_smooth J α ht p D g B hs hg hB hx).comp (t,x) contDiffAt_snd)

lemma leadingPatch_apply (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (x.1,normalMap g B x.1 x.2) =
      leadingCoordinate J α ht p D g B ψ χ t x :=
  KernelExtension.push_apply _ _ hx

lemma leadingPatch_joint_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ Function.support χ ⊆ K)
    (O : Set Space) (hKO : K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O)
    {t : ℝ} (htpos : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ v.1 v.2) (t,y) := by
  apply KernelExtension.push_family_contDiffAt _ _ K hK (fun x hx => (hKO hx).1.1.1)
    (fun s => (leadingCoordinate_support J α ht p D g B ψ χ s).trans hFK)
  · intro x hx
    exact leadingCoordinate_smooth J α ht p D g B hs hg hB ψ χ hψ hχ htpos (hKO hx).1.2.2
  · intro x hx
    have hi := (hKO hx).1.1.2
    exact (inverseRegularDomain_smooth _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq) _ hi).contDiffAt
      ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).mem_nhds hi)

lemma leadingPatch_compact_support (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ Function.support χ ⊆ K)
    (hKC : K ⊆ (geometricNormalChart g B hg hB q₀ Bq hBq).source) (t : ℝ) :
    HasCompactSupport (leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t) :=
  KernelExtension.push_hasCompactSupport _ _ K hK hKC
    ((leadingCoordinate_support J α ht p D g B ψ χ t).trans hFK)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance leadingPatchMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance leadingPatchMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma exists_leading_patch (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (O : Set Space) (hO : IsOpen O) (hqO : q₀ ∈ O)
    (hactual : ActualData J α ht p D q₀ g B) :
    ∃ ψ χ : Space → ℝ,
      ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ χ ∧
      ψ =ᶠ[𝓝 q₀] 1 ∧ χ =ᶠ[𝓝 (0 : Space)] 1 ∧
      (∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1) ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∃ K : Set (Space × Space), IsCompact K ∧
        Function.support ψ ×ˢ Function.support χ ⊆ K ∧
        K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O) ∧
      (∀ t : ℝ, 0 < t → ∀ y : Space × Space,
        ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
          leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ v.1 v.2) (t,y)) ∧
      (∀ t : ℝ, HasCompactSupport (leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t)) := by
  obtain ⟨a,ha,hsub⟩ := exists_parametrix_tube J α ht p D g B hg hB q₀ Bq hBq O hO hqO hactual
  let ψ : ContDiffBump q₀ := ⟨a/4,a/2,by positivity,by linarith⟩
  let χ : ContDiffBump (0 : Space) := ⟨a/4,a/2,by positivity,by linarith⟩
  let K := Metric.closedBall q₀ (a/2) ×ˢ Metric.closedBall (0 : Space) (a/2)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hFK : Function.support (ψ : Space → ℝ) ×ˢ Function.support (χ : Space → ℝ) ⊆ K := by
    rw [ψ.support_eq,χ.support_eq]
    exact Set.prod_mono Metric.ball_subset_closedBall Metric.ball_subset_closedBall
  have hKO : K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O :=
    (Set.prod_mono (Metric.closedBall_subset_closedBall (by linarith : a/2 ≤ a))
      (Metric.closedBall_subset_closedBall (by linarith : a/2 ≤ a))).trans hsub
  refine ⟨ψ,χ,ψ.contDiff,χ.contDiff,ψ.eventuallyEq_one,χ.eventuallyEq_one,
    fun q => ⟨ψ.nonneg,ψ.le_one⟩,fun z => ⟨χ.nonneg,χ.le_one⟩,
    ⟨K,hK,hFK,hKO⟩,?_,?_⟩
  · exact fun t htpos y => leadingPatch_joint_smooth J α ht p D g B hs hg hB q₀ Bq hBq
      ψ χ ψ.contDiff χ.contDiff K hK hFK O hKO htpos y
  · exact fun t => leadingPatch_compact_support J α ht p D g B hg hB q₀ Bq hBq
      ψ χ K hK hFK (fun x hx => (hKO hx).1.1.1) t

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
