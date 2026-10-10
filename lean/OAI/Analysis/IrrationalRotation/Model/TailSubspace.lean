import OAI.Analysis.IrrationalRotation.Model.FieldWeightedShift

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def fieldTailSubspace (m : ℤ) : Submodule ℂ (Lp Hilbert 2 μ) :=
  (fieldTailProjection (μ := μ) m).range

end Invariant233.WeightedShift

end

end OAI
