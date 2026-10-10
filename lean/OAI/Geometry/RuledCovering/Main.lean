import OAI.Geometry.RuledCovering.Singular
import OAI.Geometry.RuledCovering.ConvexBases

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

theorem fullMain : FullMain :=
  ⟨hyperbolic, physicalHyperbolic, logarithmic, productCell,
    orthogonalGrid, nilpotent, singular⟩

end RuledApproximation

end

end OAI
