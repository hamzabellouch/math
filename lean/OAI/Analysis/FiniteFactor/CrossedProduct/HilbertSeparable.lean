import OAI.Analysis.FiniteFactor.CrossedProduct.GeneratedAlgebra
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The actual regular-representation Hilbert space is separable. This uses
the countably generated Borel structure of the countable real product times
Z and the finite exponent 2. It does not assert a predual for the algebra. -/
instance sourceHilbert_separable : TopologicalSpace.SeparableSpace (SourceHilbert SourceCoordinate) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

end
end FiniteFactor

end OAI
