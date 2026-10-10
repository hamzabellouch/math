import OAI.Analysis.IrrationalRotation.Model.CircleSamplingGraph
import OAI.Analysis.IrrationalRotation.Model.RationalGraphTrimming

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.CircleParameterData

def trimmedSamplingGraphAverage (p : CircleParameterData) (θ : ℝ)
    (A j r : ℕ) : Measure (Circle × Circle) :=
  (p.samplingGraphAverage θ j r).restrict (Prod.fst ⁻¹' p.rationalGraphGood A j)

end Invariant233.CircleParameterData

end

end OAI
