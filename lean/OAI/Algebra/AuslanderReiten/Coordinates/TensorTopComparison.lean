import OAI.Algebra.AuslanderReiten.Coordinates.TensorHighLift
import OAI.Algebra.AuslanderReiten.Evaluation.TensorBetaEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def tensorTopComparison (n : ℕ) :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ n (n+1) (barB q H n) (barDb q H)

def tensorEndpoint :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ 0 0 (barDb q H) (barDb q H)

@[simp] theorem tensorHighB_eq (n : ℕ) :
    tensorHighB q H n = tensorTopComparison q H (n+3) := rfl

theorem tensorTopComparison_chain (n : ℕ) :
    ((ExternalTensor.complex k Te Te P₀ P₀).d (n+2) (n+1)).hom.comp
      (tensorTopComparison q H (n+1)) =
    (tensorTopComparison q H n).comp ((productTwistedTotal q H).d (n+1) n).hom := by
  unfold tensorTopComparison
  rw [ExternalTensor.bottomMap_d_target,
    ExternalTensor.bottomMap_d_source k Te Te (hg := barDb_cycle q H), barB_chain]

theorem tensorTopComparison_zero :
    ((ExternalTensor.complex k Te Te P₀ P₀).d 1 0).hom.comp (tensorTopComparison q H 0) =
      tensorEndpoint q H := by
  unfold tensorTopComparison tensorEndpoint
  rw [ExternalTensor.bottomMap_d_target, barB_bottom]

def twistedBarUnit : (Q₀).X 0 := (1 : R) ⊗ₜ[k] (1 : R)

theorem barDb_unit : barDb q H (twistedBarUnit q H) = twistedCasimir q H := by
  change AbsoluteBar.casimirMap k R (twistedCasimir q H) (1*1) = _
  rw [one_mul, AbsoluteBar.casimirMap_apply, map_one]
  rfl

end ArExplicit.T

end

end OAI
