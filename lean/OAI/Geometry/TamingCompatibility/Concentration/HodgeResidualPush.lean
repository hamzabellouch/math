import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.HodgeResidualFamily

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance residualPushMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualPushMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

lemma residualPatch_joint_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ tsupport χ ⊆ K)
    (O : Set Space) (hKO : K ⊆ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O)
    {t : ℝ} (htpos : 0 < t) (y : Space × Space) :
    ContDiffAt ℝ ∞ (fun v : ℝ × (Space × Space) =>
      residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ v.1 v.2) (t,y) := by
  apply KernelExtension.push_family_contDiffAt _ _ K hK (fun x hx => (hKO hx).1.1.1)
    (fun s => (residualCoordinate_support J α ht p D g B ψ χ s).trans hFK)
  · intro x hx
    exact residualCoordinate_smooth J α ht p D g B hs hg hB ψ χ hψ hχ htpos (hKO hx).1.2
  · intro x hx
    have hi := (hKO hx).1.1.2
    exact (inverseRegularDomain_smooth _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq) _ hi).contDiffAt
      ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).mem_nhds hi)

lemma residualPatch_compact_support (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (K : Set (Space × Space)) (hK : IsCompact K)
    (hFK : Function.support ψ ×ˢ tsupport χ ⊆ K)
    (hKC : K ⊆ (geometricNormalChart g B hg hB q₀ Bq hBq).source) (t : ℝ) :
    HasCompactSupport (residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t) :=
  KernelExtension.push_hasCompactSupport _ _ K hK hKC
    ((residualCoordinate_support J α ht p D g B ψ χ t).trans hFK)

lemma residualPatch_apply (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (t : ℝ) {x : Space × Space}
    (hx : x ∈ (geometricNormalChart g B hg hB q₀ Bq hBq).source) :
    residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (x.1,normalMap g B x.1 x.2) =
      residualCoordinate J α ht p D g B ψ χ t x :=
  KernelExtension.push_apply _ _ hx

lemma residualPatch_gaussian (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)
    (ψ χ : Space → ℝ) (hψ : ∀ q, 0 ≤ ψ q ∧ ψ q ≤ 1)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Space)] 1)
    (K : Set Space) (hK : IsCompact K) (hψK : Function.support ψ ⊆ K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B)
    {r : ℝ} (hr : 0 ≤ r) (hχr : tsupport χ ⊆ Metric.closedBall (0 : Space) r)
    (hsub : K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B) :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 < L ∧ ∀ t : ℝ, 0 < t → ∀ q y : Space,
      ‖residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y)‖ ≤
        A*FlatHeat.heat (L*t) (y-q) := by
  classical
  obtain ⟨A,hA,hb⟩ := residualCoordinate_gaussian J α ht p D g B hs hg hB ψ χ hψ hχ hχ0
    K hK hψK hactual hr hχr hsub
  obtain ⟨L,hL,hmap⟩ := normalMap_compact_bound g B hg hB K hK hr
  refine ⟨A*L^4,2*L^2,mul_nonneg hA (by positivity),by positivity,fun t htpos q y => ?_⟩
  let N := geometricNormalChart g B hg hB q₀ Bq hBq
  have hright : 0 ≤ (A*L^4)*FlatHeat.heat (2*L^2*t) (y-q) :=
    mul_nonneg (mul_nonneg hA (by positivity)) (FlatHeat.heat_nonneg _ _)
  by_cases hy : (q,y) ∈ N.target
  · let x := N.symm (q,y)
    have hfst : x.1 = q := geometricNormalChart_symm_fst g B hg hB q₀ Bq hBq hy
    have hsnd : normalMap g B q x.2 = y := geometricNormalChart_symm_right g B hg hB q₀ Bq hBq hy
    have he : residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y) =
        residualCoordinate J α ht p D g B ψ χ t (q,x.2) := by
      change (if (q,y) ∈ N.target then residualCoordinate J α ht p D g B ψ χ t x else 0) = _
      rw [ite_eq_left hy]
      rw [show x = (q,x.2) from Prod.ext hfst rfl]
    rw [he]
    by_cases hz : residualCoordinate J α ht p D g B ψ χ t (q,x.2) = 0
    · simpa only [hz,norm_zero] using hright
    have hsupp := residualCoordinate_support J α ht p D g B ψ χ t hz
    have hzr : ‖x.2‖ ≤ r := by simpa using hχr hsupp.2
    have hheat := FlatHeat.heat_compare (mul_pos (by norm_num : (0:ℝ)<2) htpos) hL
      (show ‖y-q‖ ≤ L*‖x.2‖ by rw [← hsnd]; exact hmap q (hψK hsupp.1) x.2 hzr)
    calc
      _ ≤ A*FlatHeat.heat (2*t) x.2 := hb t htpos q x.2
      _ ≤ A*(L^4*FlatHeat.heat (L^2*(2*t)) (y-q)) := mul_le_mul_of_nonneg_left hheat hA
      _ = _ := by rw [show L^2*(2*t) = 2*L^2*t by ring]; ring
  · have he : residualPatch J α ht p D g B hg hB q₀ Bq hBq ψ χ t (q,y) = 0 := ite_eq_right hy
    simpa only [he,norm_zero] using hright

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
