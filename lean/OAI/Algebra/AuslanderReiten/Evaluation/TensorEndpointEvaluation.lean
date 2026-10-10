import OAI.Algebra.AuslanderReiten.Coordinates.TensorTopComparison
import OAI.Algebra.AuslanderReiten.Bar.BarScalarCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def tensorBarUnit : (productTwistedTotal q H).X 0 :=
  ExternalTensor.cubicInsert k Te Te Q₀ Q₀ 0 ⟨(0,0),rfl⟩
    (twistedBarUnit q H ⊗ₜ[k] twistedBarUnit q H)

def barPairCoordinates := TensorProduct.congr
  (AbsoluteBar.scalarCoordinates k R 1) (AbsoluteBar.scalarCoordinates k R 1)

theorem tensorEndpoint_unit :
    barPairCoordinates q
      (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0 (tensorEndpoint q H (tensorBarUnit q H))) =
      twistedCasimir q H ⊗ₜ[k] twistedCasimir q H := by
  unfold tensorBarUnit tensorEndpoint
  rw [ExternalTensor.bottomMap_bottom k Te Te P₀ P₀ Q₀ Q₀ 0 0 (barDb q H) (barDb q H)
    (twistedBarUnit q H ⊗ₜ[k] twistedBarUnit q H), ExternalTensor.bottomProjection_bottom]
  rw [ExternalTensor.map_tmul, barDb_unit]
  rfl

theorem tensorEndpoint_evaluated (hq1 : 1+q ≠ 0) (s t : Resolution.Simple q) :
    A.barZeroCoordinate q (squareEvaluation q s t
      (barPairCoordinates q (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0
        (tensorEndpoint q H (tensorBarUnit q H))))) =
      (H : k)^2 • A.socleMap q (s ⊗ₜ[k] t) := by
  rw [tensorEndpoint_unit]
  exact A.squareEvaluation_eq_beta q H hq1 s t

theorem tensorEndpoint_evaluated_ne_zero (hq1 : 1+q ≠ 0) :
    A.barZeroCoordinate q (squareEvaluation q (CocycleData.simpleGenerator q)
      (CocycleData.simpleGenerator q)
      (barPairCoordinates q (ExternalTensor.bottomProjection k Te Te P₀ P₀ 0
        (tensorEndpoint q H (tensorBarUnit q H))))) ≠ 0 := by
  rw [tensorEndpoint_unit]
  exact A.squareEvaluation_coordinate_ne_zero q H hq1

end ArExplicit.T

end

end OAI
