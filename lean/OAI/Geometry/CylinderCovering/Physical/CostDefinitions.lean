import OAI.Geometry.CylinderCovering.Physical.UnitEdgeFootprintsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints

def SourceCostStatement : Prop :=
  (∀ η : ℝ, |η| ≤ 1 →
    |2 * limitingArea η (sourceCap η) - height * (1 / 4 - η ^ 2 / 960)| ≤
      height * η ^ 4) ∧
  (∀ η : ℝ, 0 < η → η ≤ 1 / 40 →
    2 * limitingArea η (sourceCap η) < height / 4)

end CylinderCovering.UnitEdgeFootprints

end

end OAI
