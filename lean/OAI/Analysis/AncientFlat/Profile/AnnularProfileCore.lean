import OAI.Analysis.AncientFlat.Geometry.AnnularCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def profilePrincipal (G : ℝ → ℝ) (p : V × ℝ) : ℝ :=
  G (‖p.1‖^2/Real.sqrt (-p.2))^2/16

def profilePotential (G : ℝ → ℝ) (p : V × ℝ) : ℝ :=
  -(-p.2)⁻¹*((‖p.1‖^2/Real.sqrt (-p.2))*deriv G (‖p.1‖^2/Real.sqrt (-p.2))/G (‖p.1‖^2/Real.sqrt (-p.2)))
end ParabolicAnnular

end

end OAI
