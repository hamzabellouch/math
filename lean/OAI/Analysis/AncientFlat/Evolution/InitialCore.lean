import OAI.Analysis.AncientFlat.Geometry.InteriorCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicInitial
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def slab (R h : ℝ) : Set (V × ℝ) := {p | ‖p.1‖<R ∧ p.2∈Icc 0 h}
end ParabolicInitial

end

end OAI
