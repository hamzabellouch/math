import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.GaugedNormalJets
import OAI.Geometry.TamingCompatibility.DifferentialForms.End

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma exists_geometric_heat_residual (J : AlmostComplexStructure X) (α : TwoForm X)
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
       ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t →
         ∀ z : Space, ‖z‖ ≤ r →
           ‖NormalHeatResidual.residual (fun z i j => a i j z)
             (fun z j => transformedFirst a b U EuclideanEnergy.e j z)
             (transformedZero a b c U EuclideanEnergy.e) t z‖ ≤ C*FlatHeat.heat (2*t) z) := by
  obtain ⟨g,B,U,hg,hB,hactual,hU,hUzero,hUinner,hUunitary,hjets⟩ := exists_gauged_normal_jets J α hs ht p D q hq
  refine ⟨g,B,U,hg,hB,hactual,hU,hUzero,hUinner,hUunitary,?_⟩
  dsimp only at hjets ⊢
  obtain ⟨ha,hb,hc⟩ := hjets
  apply NormalHeatResidual.exists_residual_bound
  · exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => (ha i j).1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  · funext i j
    exact (ha i j).2.1
  · rw [fderiv_pi (fun i => (contDiffAt_pi.mpr fun j => (ha i j).1).differentiableAt (by simp))]
    ext v i j
    simp only [ContinuousLinearMap.pi_apply]
    rw [fderiv_pi (fun j => (ha i j).1.differentiableAt (by simp))]
    simp [(ha i j).2.2]
  · exact contDiffAt_pi.mpr fun j => (hb j).1.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  · funext j
    exact (hb j).2
  · exact hc.continuousAt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

section

noncomputable section

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
