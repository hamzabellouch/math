import OAI.Analysis.AncientFlat.Geometry.InteriorL2

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace ParabolicAnnular
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def outer : Set (V × ℝ) := {p | (1:ℝ)/2<‖p.1‖ ∧ ‖p.1‖<2 ∧ -4<p.2 ∧ p.2<0}

def inner : Set (V × ℝ) := {p | (3:ℝ)/4<‖p.1‖ ∧ ‖p.1‖<5/4 ∧ -2<p.2 ∧ p.2<0}
end ParabolicAnnular

end

end OAI
