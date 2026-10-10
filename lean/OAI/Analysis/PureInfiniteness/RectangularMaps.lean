import OAI.Analysis.PureInfiniteness.RectangularAlgebra
import OAI.Analysis.WeakInfiniteness.MatrixMaps
import OAI.Analysis.JiangSu.Nonunital.MatrixDiagonal

namespace OAI

/-! Applying the unitization embedding to finite rows and columns is
contractive. This lets the scalar sample matrices be used without unitalizing
the strong pure infiniteness hypothesis. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A B I J K : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
local instance rectangularMapsOrderA : PartialOrder A := CStarAlgebra.spectralOrder A
local instance rectangularMapsStarOrderA : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance rectangularMapsOrderB : PartialOrder B := CStarAlgebra.spectralOrder B
local instance rectangularMapsStarOrderB : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

lemma rectangularMap_conjTranspose (φ : A →⋆ₙₐ[ℂ] B) (M : CStarMatrix I J A) :
    rectangularMap φ M.conjTranspose = (rectangularMap φ M).conjTranspose :=
  rectangularMap_star φ M

lemma rectangularMap_diagonal (φ : A →⋆ₙₐ[ℂ] B) [Fintype I] [DecidableEq I]
    (a : I → A) :
    rectangularMap φ (NonunitalGamma.diagonalHom a) =
      NonunitalGamma.diagonalHom (fun i => φ (a i)) := by
  ext i j
  change φ (if i = j then a i else 0) = if i = j then φ (a i) else 0
  split_ifs <;> simp

lemma rectangularMap_oneByOne (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    rectangularMap φ (CStarMatrix.toOneByOne (Fin 1) ℂ A a) =
      CStarMatrix.toOneByOne (Fin 1) ℂ B (φ a) := by
  ext i j
  rfl

end WeakPureInfiniteness

end

end OAI
