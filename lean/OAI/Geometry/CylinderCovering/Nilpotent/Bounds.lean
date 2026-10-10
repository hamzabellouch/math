import OAI.Geometry.CylinderCovering.Nilpotent.ConstructionDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.Construction
import OAI.Geometry.CylinderCovering.Nilpotent.Field
import OAI.Geometry.CylinderCovering.Nilpotent.Cost
import OAI.Geometry.CylinderCovering.Nilpotent.ApexPhysical
import OAI.Geometry.CylinderCovering.Nilpotent.Similarity
import OAI.Geometry.CylinderCovering.Nilpotent.ShadowSimilarity
import OAI.Geometry.CylinderCovering.Nilpotent.ShadowConsequences
import OAI.Geometry.CylinderCovering.Nilpotent.ShadowMeasure
import OAI.Geometry.CylinderCovering.Nilpotent.Volume
import OAI.Geometry.CylinderCovering.Convexity.TetrahedronIdentification

namespace OAI

noncomputable section
open Set MeasureTheory Filter RuledApproximation
open scoped Topology ContDiff
namespace CylinderCovering.Nilpotent

theorem sweepCoverage : SweepCoverageStatement := by
  intro k x y z hk hk1 hp
  exact sweep_cover hk hk1 hp

theorem angularField_proof : AngularFieldStatement := by
  refine ⟨signedField_contDiffOn, ?_, angularDerivative_square_zero,
    angularDerivative_on_ray, ?_⟩
  · intro σ k b hb
    exact signedField_hasFDerivAt σ k hb
  · intro σ k hκ
    exact no_continuous_extension hκ

theorem integralCost : IntegralCostStatement := by
  refine ⟨integral_a, integral_speedSq, ?_, integral_expansion, ?_⟩
  · intro k hk hk1
    exact integral_remainder hk hk1
  · intro k hk hk1
    exact integral_lt_quarter hk hk1

theorem auxiliaryApex : AuxiliaryApexStatement := by
  intro h k ρ σ hk hρ hρ1 hσ
  exact NilpotentApexNet.apexNet h hk hρ hρ1 hσ

theorem physicalSimilarity : PhysicalSimilarityStatement :=
  ⟨centerMap_normalized, centerMap_dist, centerMap_tetrahedron, centerMap_area,
    centerMap_volume, shadowSimilarity⟩

theorem fullConstruction_of_finite (hfinite : FiniteCounterexampleStatement) :
    FullConstructionStatement :=
  ⟨tetrahedron_volume, ruled_tetrahedron_minimum_shadow, sweepCoverage,
    angularField_proof, integralCost,
    auxiliaryApex, NilpotentApexNet.physicalApexNet, physicalSimilarity, hfinite⟩

end CylinderCovering.Nilpotent

end

end OAI
