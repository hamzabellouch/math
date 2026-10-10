import OAI.Algebra.AuslanderReiten.Resolutions.BinaryKoszulDual

namespace OAI

noncomputable section
namespace ArExplicit.BinaryKoszul
universe u
variable (k : Type u) [Field k]

def zeroPieceScalarEquiv : Piece k 0 ≃ₗ[k] k :=
  LinearEquiv.funUnique (Fin 1) k k

def zeroDualPieceScalarEquiv : DualPiece k 0 ≃ₗ[k] k :=
  (zeroPieceScalarEquiv k).symm.dualMap.trans (LinearMap.ringLmapEquivSelf k k k)

end ArExplicit.BinaryKoszul

end

end OAI
