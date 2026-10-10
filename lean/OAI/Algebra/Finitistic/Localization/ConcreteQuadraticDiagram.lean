import OAI.Algebra.Finitistic.Encoding.RelationBasisCoefficients
import OAI.Algebra.Finitistic.Rectification.InducedDiagram

namespace OAI
noncomputable section
namespace LittleFinitistic.ConcreteQuadraticDiagram
open QuadraticEncoding RelationBasisCoefficients ThreeVertexAlgebra
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The exact three-vertex algebra and its actual independent relation basis,
packaged for the induced-column construction. -/
def quadratic : ExternalTensor.Section4.Quadratic k (B P)
    (A := Fin (d+1)) (J := Fin (d+1)) (R := RelationIndex P) where
  e₀ := vertex (composition P) 0
  e₁ := vertex (composition P) 1
  e₂ := vertex (composition P) 2
  a := arrow01 P
  b := arrow12 P
  ha i := by
    change mul (composition P) (0,0,0,basis i,0,0) (vertex (composition P) 0) = _
    simp [vertex,mul,arrow01]
  hb j := by
    change mul (composition P) (0,0,0,0,basis j,0) (vertex (composition P) 1) = _
    simp [vertex,mul,arrow12]
  coeff := basisCoefficient P
  relation := basis_relation P
end LittleFinitistic.ConcreteQuadraticDiagram

end

end OAI
