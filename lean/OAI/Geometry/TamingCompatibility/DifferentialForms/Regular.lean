import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalMap
import OAI.Geometry.TamingCompatibility.DifferentialForms.WeightedLower
import OAI.Geometry.TamingCompatibility.Elliptic.OperatorCalculus

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma ActualData.regular (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
    (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) (hactual : ActualData J α ht p D q g B) :
    let ρ := fun z => volumeDensity (normalMetric g B (q,z))
    let a := pulledA J α ht p D g B q
    let b := pulledB J α ht p D g B q
    ∀ᶠ z in 𝓝 (0 : Space),
      (∀ i, DifferentiableAt ℝ (a i) z) ∧ DifferentiableAt ℝ b z ∧
      DifferentiableAt ℝ ρ z ∧ ρ z ≠ 0 ∧
      (∀ i j, (a i z).adjoint ∘L a j z + (a j z).adjoint ∘L a i z =
        (2*principal (normalMetric g B (q,z)) i j) • ContinuousLinearMap.id ℝ W) := by
  dsimp only
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  have hq := hOD hqO
  have hBq : (B q).IsInvertible := by
    rw [hBact q hqO]
    exact ⟨frameEquiv _ _ (D.frame_gram q hq),rfl⟩
  have hzero : affineMetric g B (q,0) = innerSL ℝ (E := Space) := by
    simp only [affineMetric,map_zero,add_zero,hgact q hqO,hBact q hqO]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact frameMap_metric _ _ (D.frame_gram q hq) v w
  obtain ⟨hρ,hρone,-,-⟩ := normal_density_principal_jets g B hg hB hsym q hzero
  have ha := pulledA_contDiffAt J α ht p D g B q hq hBq
  have hb := pulledB_contDiffAt J α hs ht p D g B q hq
  have heA : ∀ᶠ z in 𝓝 (0 : Space), ∀ i, DifferentiableAt ℝ (pulledA J α ht p D g B q i) z :=
    eventually_all.mpr fun i =>
      (((ha i).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by norm_num)).mono
        fun z hz => hz.differentiableAt (by norm_num)
  have heB := ((hb.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by norm_num)).mono
    (fun z hz => hz.differentiableAt (by norm_num))
  have heρ := ((hρ.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by norm_num)).mono
    (fun z hz => hz.differentiableAt (by norm_num))
  have hρne : volumeDensity (normalMetric g B (q,0)) ≠ 0 := by rw [hρone]; norm_num
  have heρne := hρ.continuousAt.eventually_ne hρne
  have heP : ∀ᶠ z in 𝓝 (0 : Space), ∀ i j,
      weightedPrincipal (pulledA J α ht p D g B q)
          (fun z => volumeDensity (normalMetric g B (q,z))) i j z +
        weightedPrincipal (pulledA J α ht p D g B q)
          (fun z => volumeDensity (normalMetric g B (q,z))) j i z =
        (2*(volumeDensity (normalMetric g B (q,z))*principal (normalMetric g B (q,z)) i j)) •
          ContinuousLinearMap.id ℝ W :=
    eventually_all.mpr fun i => eventually_all.mpr fun j =>
      pulledA_weighted_principal J α ht p D g B hg hB hsym O hO hOD hgact q hqO hBq i j
  filter_upwards [heA,heB,heρ,heρne,heP] with z hzA hzB hzρ hzρne hzP
  refine ⟨hzA,hzB,hzρ,hzρne,fun i j => ?_⟩
  apply smul_right_injective (W →L[ℝ] W) hzρne
  simpa only [weightedPrincipal,map_smul,ContinuousLinearMap.smul_comp,←smul_add,
    ←mul_smul,show volumeDensity (normalMetric g B (q,z)) *
      (2*principal (normalMetric g B (q,z)) i j) =
      2*(volumeDensity (normalMetric g B (q,z))*principal (normalMetric g B (q,z)) i j) by ring]
    using hzP i j

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open FirstJetGauge
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
lemma firstMatrix_eq (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) : firstMatrix e a b ρ = actualSquareFirst e a b ρ := by
  funext j x
  unfold firstMatrix actualSquareFirst squareFirst principalMatrix weightedPrincipal
  rfl
lemma zeroMatrix_eq (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) : zeroMatrix e a b ρ = actualSquareZero e a b ρ := by
  funext x
  unfold zeroMatrix actualSquareZero lowerMatrix weightedLower
  rfl
lemma gaugeFirst_eq (e : ι → V) (a : ι → ι → V → ℝ) (b : ι → V → W →L[ℝ] W)
    (U : V → W →L[ℝ] W) : gaugeFirst e a b U = fun j => transformedFirst a b U e j := rfl
lemma gaugeZero_eq (e : ι → V) (a : ι → ι → V → ℝ) (b : ι → V → W →L[ℝ] W)
    (c U : V → W →L[ℝ] W) : gaugeZero e a b c U = transformedZero a b c U e := rfl
end TamingCompatibility.GeometricHilbert.OperatorCalculus

end

end OAI
