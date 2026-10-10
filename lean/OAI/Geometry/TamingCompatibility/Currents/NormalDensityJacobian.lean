import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Dpos
import OAI.Geometry.TamingCompatibility.Charts.MetricCalculus

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace

lemma normal_density_jacobian (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p z : Space) :
    volumeDensity (normalMetric g B (p,z)) =
      |LinearMap.det (fderiv ℝ (fun u => p+B p (coordinateJet (metricJet g B p) u)) z).toLinearMap| *
      volumeDensity (g (p+B p (coordinateJet (metricJet g B p) z))) := by
  rw [normalMetric_eq_pullback g B hg hB hsym]
  exact MetricDensity.density_pullMetric (stdOrthonormalBasis ℝ Space).toBasis _ _

lemma normal_density_principal_jets (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, g x v w = g x w v) (p : Space)
    (hzero : affineMetric g B (p,0) = innerSL ℝ (E := Space)) :
    ContDiffAt ℝ ∞ (fun z => volumeDensity (normalMetric g B (p,z))) 0 ∧
    volumeDensity (normalMetric g B (p,0)) = 1 ∧
    fderiv ℝ (fun z => volumeDensity (normalMetric g B (p,z))) 0 = 0 ∧
    (∀ i j, ContDiffAt ℝ ∞ (fun z => principal (normalMetric g B (p,z)) i j) 0 ∧
      principal (normalMetric g B (p,0)) i j = (if i=j then 1 else 0) ∧
      fderiv ℝ (fun z => principal (normalMetric g B (p,z)) i j) 0 = 0) := by
  apply NormalMetricCalculus.jets
  · exact ((normalMetric_contDiff g B hg hB).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt
  · change pullbackMetric (fun z => affineMetric g B (p,z)) (metricJet g B p) 0 = _
    rw [pullbackMetric_zero]
    exact hzero
  · rw [← UniformJets.dpos_eq _ ((normalMetric_contDiff g B hg hB).differentiable (by simp))]
    exact normalMetric_dpos_zero g B hg hB hsym p hzero
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

noncomputable section

end
end
end
end
end
end
end
end

end OAI
