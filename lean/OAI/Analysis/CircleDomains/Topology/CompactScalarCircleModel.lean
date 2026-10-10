import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModelData
import OAI.Analysis.CircleDomains.Transfer.PointDustModels

namespace OAI

/-! A circle model of the original compact scalar list, with its actual
continuous collapse map and global Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RetainedRealCircleModel

 def compactScalarCircleModel
    (harea : ExteriorCoefficientAreaTheorem) (hsch : PlanarSchoenflies)
    {d : PathCodeData Sphere Sphere} (hG : IsOpen d.physicalDomain)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → p = q)
    {m : ℕ} {u : Fin m → EuclideanPlane → ℝ} (T : ∀ i, ExactTraceTest d (u i))
    (R : RetainedRealCircleModel d id (fun i => (T i).coordinate))
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i)) :
    CompactScalarCircleModel d.physicalDomain u := by
  classical
  choose H hH using fun i => R.exactTraceTest_original_witness harea hsch hG hc T hu hs i
  refine {
    function := R.limit.function
    normalized := R.limit.normalized
    conformal := R.limit.conformal
    circle := R.circle
    projection := R.limit.sourceProjection hG id
    projection_continuous := R.limit.sourceProjection_continuous hG id continuous_id hc
    projection_inverse := fun p hp => R.limit.sourceProjection_on_image hG id hp
    projection_outside := ?_
    projection_component := ?_
    witness := H
    gradient_zero := hH }
  · intro p hp
    rw [R.limit.sourceProjection_off_image hG id hp]
    exact (R.limit.chosenSourceEnd hG p hp).outside
  · intro p hp q hq
    let A := R.limit.chosenSourceEnd hG p hp
    have hq' : q ∈ connectedComponentIn
        (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ A.matching.point := by
      rwa [A.point_eq]
    calc
      R.limit.sourceProjection hG id q = A.source :=
        A.matching.sourceProjection_eq hG id hc hq'
      _ = R.limit.sourceProjection hG id p := (R.limit.sourceProjection_off_image hG id hp).symm

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
