import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalMap
import OAI.Geometry.TamingCompatibility.DifferentialForms.WeightedLower

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma exists_gauged_normal_jets (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (hq : q ∈ D.domain) :
    ∃ (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
      (U : Space → W →L[ℝ] W),
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ B ∧ ActualData J α ht p D q g B ∧ ContDiff ℝ ∞ U ∧
      U 0 = 1 ∧ (∀ z u v, ⟪U z u,U z v⟫ = ⟪u,v⟫) ∧
      (∀ z, U z ∈ unitary (W →L[ℝ] W)) ∧
      (let ρ := fun z => volumeDensity (normalMetric g B (q,z))
       let a := fun i j z => principal (normalMetric g B (q,z)) i j
       let b := actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
         (pulledB J α ht p D g B q) ρ
       let c := actualSquareZero EuclideanEnergy.e (pulledA J α ht p D g B q)
         (pulledB J α ht p D g B q) ρ
       (∀ i j, ContDiffAt ℝ ∞ (a i j) 0 ∧ a i j 0 = (if i=j then 1 else 0) ∧
         fderiv ℝ (a i j) 0 = 0) ∧
       (∀ j, ContDiffAt ℝ ∞ (transformedFirst a b U EuclideanEnergy.e j) 0 ∧
         transformedFirst a b U EuclideanEnergy.e j 0 = 0) ∧
       ContDiffAt ℝ ∞ (transformedZero a b c U EuclideanEnergy.e) 0) := by
  obtain ⟨g,B,hg,hB,hactual,ha,hb,hρ,hρone,hρzero,hpr,hskew⟩ :=
    exists_actual_normal_jets J α hs ht p D q hq
  let ρ := fun z => volumeDensity (normalMetric g B (q,z))
  let a := fun i j z => principal (normalMetric g B (q,z)) i j
  let b := actualSquareFirst EuclideanEnergy.e (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) ρ
  let c := actualSquareZero EuclideanEnergy.e (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) ρ
  let U := gauge (halfJet EuclideanSpace.proj (fun j => b j 0))
  have hU : ContDiff ℝ ∞ U := gauge_contDiff _
  have hab : ∀ j, ContDiffAt ℝ ∞ (b j) 0 :=
    actualSquareFirst_contDiffAt _ _ _ _ ha hb hρ (by change volumeDensity (normalMetric g B (q,0)) ≠ 0; exact ne_of_eq_of_ne hρone one_ne_zero)
  have hac : ContDiffAt ℝ ∞ c 0 :=
    actualSquareZero_contDiffAt _ _ _ _ ha hb hρ (by change volumeDensity (normalMetric g B (q,0)) ≠ 0; exact ne_of_eq_of_ne hρone one_ne_zero)
  refine ⟨g,B,U,hg,hB,hactual,hU,gauge_zero _,?_,?_,hpr,?_,?_⟩
  · exact gauge_inner _ (halfJet_skew _ _ hskew)
  · exact gauge_unitary _ (halfJet_skew _ _ hskew)
  · intro j
    refine ⟨transformedFirst_contDiffAt a b U EuclideanEnergy.e j
      (fun i j => (hpr i j).1) hab hU.contDiffAt,?_⟩
    apply transformedFirst_zero EuclideanSpace.proj EuclideanEnergy.e
    · intro i k
      simp [EuclideanEnergy.e]
    · exact fun i j => (hpr i j).2.1
  · exact transformedZero_contDiffAt a b c U EuclideanEnergy.e
      (fun i j => (hpr i j).1) hab hac hU.contDiffAt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
