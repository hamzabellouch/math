import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeStarNormalGauge
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixPatch

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeParametrixInitialMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeParametrixInitialMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] normalGauge normalFirst

lemma normalDensity_continuous (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    Continuous (normalDensity g B) := by
  exact (detGram_contDiff.continuous.comp (normalMetric_contDiff g B hg hB).continuous).sqrt

lemma normalDensity_zero {q : Space} (hactual : ActualData J α ht p D q g B) :
    normalDensity g B (q,0) = 1 := by
  rw [normalDensity,hactual.metric_zero J α ht p D g B,volumeDensity_euclidean]

lemma leadingCoordinate_initial (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B)
    (ψ χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (f : Space → W) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ z : Space,
      (ψ q * χ z * FlatHeat.heat t z * normalDensity g B (q,z)) •
        (normalGauge J α ht p D g B (q,z)).adjoint (f (normalMap g B q z)))
      (𝓝[>] 0) (𝓝 (ψ q • f q)) := by
  let F : Space → W := fun z => (ψ q * χ z * normalDensity g B (q,z)) •
    (normalGauge J α ht p D g B (q,z)).adjoint (f (normalMap g B q z))
  have hU : Continuous (fun z : Space => normalGauge J α ht p D g B (q,z)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      ((normalGauge_smooth J α ht p D g B hs hg hB (hactual.center J α ht p D g B).1).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).continuousAt)
  have hUa : Continuous (fun z : Space => (normalGauge J α ht p D g B (q,z)).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp hU
  have hmap : Continuous (normalMap g B q) :=
    (normalMap_contDiff g B q).continuous
  have hF : Continuous F := ((continuous_const.mul hχ).mul
    ((normalDensity_continuous g B hg hB).comp
      (continuous_const.prodMk continuous_id))).smul (hUa.clm_apply (hf.comp hmap))
  have hFc : HasCompactSupport F := by
    apply hχc.mono
    intro z hz
    contrapose! hz
    simp only [Function.mem_support] at hz ⊢
    simp [F,hz]
  have hF0 : F 0 = ψ q • f q := by
    simp only [F,hχ0,normalDensity_zero J α ht p D g B hactual,normalGauge_zero,mul_one,
      ContinuousLinearMap.adjoint_one,one_apply_eq_self,normalMap_zero]
  have hh := FlatHeat.heat_approximate_identity F (hF.integrable_of_hasCompactSupport hFc) hF.continuousAt
  rw [hF0] at hh
  convert hh using 1
  funext t
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [F,smul_smul]
  congr 1
  ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set MeasureTheory
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance hodgeParametrixInitialSliceMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeParametrixInitialSliceMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)

lemma normalMap_slice_injective (q : Space) :
    InjOn (normalMap g B q) {z | (q,z) ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source} := by
  intro z hz w hw he
  have hc : geometricNormalChart g B hg hB q₀ Bq hBq (q,z) =
      geometricNormalChart g B hg hB q₀ Bq hBq (q,w) := by
    simpa only [geometricNormalChart_apply,Prod.mk.injEq,true_and] using he
  exact congrArg Prod.snd ((geometricNormalChart g B hg hB q₀ Bq hBq).injOn hz hw hc)

lemma normalMap_slice_image (q : Space) :
    normalMap g B q '' {z | (q,z) ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source} =
      {y | (q,y) ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).target} := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (geometricNormalChart g B hg hB q₀ Bq hBq).map_source hz
  · intro hy
    refine ⟨((geometricNormalChart g B hg hB q₀ Bq hBq).symm (q,y)).2,?_,
      geometricNormalChart_symm_right g B hg hB q₀ Bq hBq hy⟩
    have hh := (geometricNormalChart g B hg hB q₀ Bq hBq).map_target hy
    have hf := geometricNormalChart_symm_fst g B hg hB q₀ Bq hBq hy
    change (q, ((geometricNormalChart g B hg hB q₀ Bq hBq).symm (q,y)).2) ∈
      (geometricNormalChart g B hg hB q₀ Bq hBq).source
    have he : (q, ((geometricNormalChart g B hg hB q₀ Bq hBq).symm (q,y)).2) =
        (geometricNormalChart g B hg hB q₀ Bq hBq).symm (q,y) :=
      Prod.ext hf.symm rfl
    rw [he]
    exact hh

lemma leadingPatch_change (hsym : ∀ x v w, g x v w = g x w v)
    (ψ χ : Space → ℝ)
    (hsub : Function.support ψ ×ˢ Function.support χ ⊆
      (geometricNormalChart g B hg hB q₀ Bq hBq).source)
    (t : ℝ) (q : Space) (f : Space → W) :
    (∫ y : Space, volumeDensity (g y) •
      (leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y)).adjoint (f y)) =
    ∫ z : Space, (ψ q * χ z * FlatHeat.heat t z * normalDensity g B (q,z)) •
      (normalGauge J α ht p D g B (q,z)).adjoint (f (normalMap g B q z)) := by
  let C := geometricNormalChart g B hg hB q₀ Bq hBq
  let U : Set Space := {z | (q,z) ∈ C.source}
  let V : Set Space := {y | (q,y) ∈ C.target}
  let F : Space → W := fun y => volumeDensity (g y) •
    (leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y)).adjoint (f y)
  have hU : IsOpen U := C.open_source.preimage (continuous_const.prodMk continuous_id)
  have hF : ∀ y, y ∉ V → F y = 0 := by
    intro y hy
    simp [F,leadingPatch,KernelExtension.push,show (q,y) ∉ C.target from hy,C]
  have hc := integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
    (fun z (_ : z ∈ U) => ((normalMap_contDiff g B q).differentiable (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (normalMap_slice_injective g B hg hB q₀ Bq hBq q) F
  rw [normalMap_slice_image] at hc
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF]
  change (∫ y in V, F y) = _
  rw [hc]
  have hi : ∀ z ∈ U,
      |(fderiv ℝ (normalMap g B q) z).toLinearMap.det| • F (normalMap g B q z) =
      (ψ q * χ z * FlatHeat.heat t z * normalDensity g B (q,z)) •
        (normalGauge J α ht p D g B (q,z)).adjoint (f (normalMap g B q z)) := by
    intro z hz
    dsimp only [F]
    rw [leadingPatch_apply J α ht p D g B hg hB q₀ Bq hBq ψ χ t hz]
    rw [leadingCoordinate]
    simp only [map_smulₛₗ,starRingEnd_apply,star_trivial,smul_apply,smul_smul]
    rw [normalDensity,normal_density_jacobian g B hg hB hsym]
    congr 1
    have he : (fun u : Space => q+B q (coordinateJet (metricJet g B q) u)) = normalMap g B q := rfl
    rw [he]
    change |(fderiv ℝ (normalMap g B q) z).toLinearMap.det| *
      (volumeDensity (g (normalMap g B q z)) * (ψ q * χ z * FlatHeat.heat t z)) =
      (ψ q * χ z * FlatHeat.heat t z) * (|(fderiv ℝ (normalMap g B q) z).toLinearMap.det| *
        volumeDensity (g (normalMap g B q z)))
    ring
  rw [setIntegral_congr_fun hU.measurableSet hi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hh : ψ q = 0 ∨ χ z = 0 := by
    by_contra hn
    push Not at hn
    exact hz (hsub ⟨hn.1,hn.2⟩)
  rcases hh with hh | hh <;> simp [hh]

lemma leadingPatch_initial (hs : IsSmooth α) (hsym : ∀ x v w, g x v w = g x w v)
    {q : Space} (hactual : ActualData J α ht p D q g B)
    (ψ χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (hsub : Function.support ψ ×ˢ Function.support χ ⊆
      (geometricNormalChart g B hg hB q₀ Bq hBq).source)
    (f : Space → W) (hf : Continuous f) :
    Tendsto (fun t : ℝ => ∫ y : Space, volumeDensity (g y) •
      (leadingPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y)).adjoint (f y))
      (𝓝[>] 0) (𝓝 (ψ q • f q)) := by
  simp_rw [leadingPatch_change J α ht p D g B hg hB q₀ Bq hBq hsym ψ χ hsub]
  exact leadingCoordinate_initial J α ht p D g B hs hg hB hactual ψ χ hχ hχc hχ0 f hf

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
