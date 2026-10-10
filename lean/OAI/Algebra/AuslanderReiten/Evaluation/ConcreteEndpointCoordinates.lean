import OAI.Algebra.AuslanderReiten.Coordinates.TensorNormalizedTop
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorZeroEquiv

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P" => AbsoluteBar.complex k R
local notation "D" => bimoduleTwoConeData q

def endpointCoordinates : (D).term 0 ≃ₗ[k] ((R ⊗[k] R) ⊗[k] (R ⊗[k] R)) :=
  (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).trans
    (((ExternalTensor.zeroEquiv k Te Te P P).restrictScalars k).trans
      ((ExternalTensor.moduleScalarCoordinates k Te Te ((P).X 0) ((P).X 0)).trans
        (barPairCoordinates q)))

theorem endpointEvaluation_eq (s t : Resolution.Simple q) (z : (D).term 0) :
    endpointEvaluation q s t z = A.barZeroCoordinate q (squareEvaluation q s t (endpointCoordinates q z)) := rfl

theorem endpointCoordinates_symm (z : (R ⊗[k] R) ⊗[k] (R ⊗[k] R)) :
    (endpointCoordinates q).symm z =
    (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).symm
      (ExternalTensor.inclusion k Te Te P P 0 0 0 rfl
        ((ExternalTensor.moduleScalarCoordinates k Te Te ((P).X 0) ((P).X 0)).symm
          ((barPairCoordinates q).symm z))) := by
  exact congrArg (ExternalTensor.envelopingScalarEquiv k R R ((productTwoConeData q).term 0)).symm
    (ExternalTensor.zeroEquiv_symm k Te Te P P _)

end ArExplicit.T

end

end OAI
