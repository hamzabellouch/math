import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.GeometricHeatResidual
import OAI.Geometry.TamingCompatibility.Functional.GaugeOrthogonal
import OAI.Geometry.TamingCompatibility.DifferentialForms.Regular

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
section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma exists_actual_heat_residual (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)
    (q : Space) (hq : q ∈ D.domain) :
    ∃ (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
      (U : Space → W →L[ℝ] W),
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ B ∧ ActualData J α ht p D q g B ∧
      ContDiff ℝ ∞ U ∧ U 0 = 1 ∧ (∀ z, U z ∈ unitary (W →L[ℝ] W)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t →
        ∀ z : Space, ‖z‖ ≤ r → ∀ u : W,
          ‖deriv (fun s => U z (NormalHeatResidual.modelSection s u z)) t +
            weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
              (pulledB J α ht p D g B q) (fun y => volumeDensity (normalMetric g B (q,y)))
              (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
                (pulledB J α ht p D g B q)
                (fun y => U y (NormalHeatResidual.modelSection t u y))) z‖ ≤
            (C*FlatHeat.heat (2*t) z)*‖u‖ := by
  obtain ⟨g,B,U,hg,hB,hactual,hU,hUzero,hUinner,hUunitary,C,hC,r,hr,hbound⟩ :=
    exists_geometric_heat_residual J α hs ht p D q hq
  obtain ⟨s,hspos,hsball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hactual.regular J α hs ht p D q g B hg hB)
  refine ⟨g,B,U,hg,hB,hactual,hU,hUzero,hUunitary,C,hC,min r s,lt_min hr hspos,?_⟩
  intro t htpos z hz u
  have hzr := hz.trans (min_le_left _ _)
  have hzs : z ∈ Metric.closedBall (0 : Space) s := by
    simpa using hz.trans (min_le_right r s)
  obtain ⟨ha,hb,hρ,hρz,hpr⟩ := hsball hzs
  have he := NormalHeatResidual.actual_residual (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) (fun y => volumeDensity (normalMetric g B (q,y)))
    (fun i j y => principal (normalMetric g B (q,y)) i j) U hU
    (fun y => NormalHeatResidual.gauge_orthogonal (U y) (hUinner y)) ha hb hρ hρz hpr htpos u
  have hn := ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (hUunitary z))
    (deriv (fun s => U z (NormalHeatResidual.modelSection s u z)) t +
      weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => volumeDensity (normalMetric g B (q,y)))
        (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q)
          (fun y => U y (NormalHeatResidual.modelSection t u y))) z)
  have hee : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → Space) = EuclideanEnergy.e := by
    funext i
    simp [EuclideanEnergy.e]
  rw [hee,firstMatrix_eq,zeroMatrix_eq,gaugeFirst_eq,gaugeZero_eq] at he
  rw [ContinuousLinearMap.star_eq_adjoint] at hn
  rw [← hn]
  have he' := congrArg norm he
  rw [he']
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hbound t htpos z hzr) (norm_nonneg u))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
