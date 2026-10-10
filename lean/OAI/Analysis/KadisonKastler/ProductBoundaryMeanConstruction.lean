import OAI.Analysis.KadisonKastler.SwappedBoundaryMean
import OAI.Analysis.KadisonKastler.NestedMeanEquivariance

namespace OAI

/-! # The scalar mean for the separate product boundary action -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]

def randomWalkProductScalarMean : ScalarBoundaryMean ((randomWalkBoundaryAction G).prod) :=
  nestedScalarBoundaryMean
    ((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G))
    ((randomWalkBoundaryAction G).rightOnProduct)
    ((randomWalkBoundaryAction G).prod) (fun _ _ => rfl)
    (randomWalkParameterizedScalarMean G (randomWalkBoundaryMeasure G))
    (randomWalkSecondScalarMean G)
    (fun g F => randomWalkParameterizedScalarMean_natural G (randomWalkBoundaryMeasure G)
      ((randomWalkBoundaryAction G).toPerm g) ((randomWalkBoundaryAction G).quasi g) F)
    (randomWalkSecondScalarMean_natural G)

end

end KadisonKastler

end OAI
