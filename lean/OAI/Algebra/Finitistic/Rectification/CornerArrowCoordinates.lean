import OAI.Algebra.Finitistic.Rectification.CornerColumnPaths
import OAI.Algebra.Finitistic.Localization.ConcreteQuadraticDiagram

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.CornerArrowCoordinates
open QuadraticEncoding CornerColumnPaths
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- On the adjacent 1,0 corner, the original a-arrow inserts its actual basis vector. -/
theorem arrow01_coordinate (a : Fin (d+1)) (c : k) :
    CornerSpaces.corner10Equiv (composition P)
      (cornerMap (composition P) 1 0 1 (arrow01 P a)
        ((ConcreteQuadraticDiagram.quadratic P).ha a)
        ((CornerSpaces.diagonalEquiv (composition P) 1).symm c)) = c • basis a := by
  simp [CornerSpaces.corner10Equiv,cornerMap,CornerSpaces.diagonalEquiv,
    arrow01,ThreeVertexAlgebra.mul,ThreeVertexAlgebra.vertex]

/-- On the adjacent 2,1 corner, the original b-arrow inserts its actual basis vector. -/
theorem arrow12_coordinate (b : Fin (d+1)) (c : k) :
    CornerSpaces.corner21Equiv (composition P)
      (cornerMap (composition P) 2 1 2 (arrow12 P b)
        ((ConcreteQuadraticDiagram.quadratic P).hb b)
        ((CornerSpaces.diagonalEquiv (composition P) 2).symm c)) = c • basis b := by
  simp [CornerSpaces.corner21Equiv,cornerMap,CornerSpaces.diagonalEquiv,
    arrow12,ThreeVertexAlgebra.mul,ThreeVertexAlgebra.vertex]

/-- Length-two multiplication is exactly the quotient of the original tensor path. -/
theorem lengthTwo_coordinate (a : Fin (d+1)) (w : Arrows k d) :
    CornerSpaces.corner20Equiv (composition P)
      (cornerMap (composition P) 2 0 1 (arrow01 P a)
        ((ConcreteQuadraticDiagram.quadratic P).ha a)
        ((CornerSpaces.corner21Equiv (composition P)).symm w)) =
      (relationSpace P).mkQ (w ⊗ₜ[k] basis a) := by
  change (0 : k) • (0 : Paths k d ⧸ relationSpace P) +
    (relationSpace P).mkQ (w ⊗ₜ[k] basis a) + (0 : k) • 0 = _
  simp only [zero_smul, zero_add, add_zero]

end LittleFinitistic.CornerArrowCoordinates

end

end OAI
