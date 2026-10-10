import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorBottomCubic
import OAI.Algebra.AuslanderReiten.Bar.TBarHomotopies
import OAI.Algebra.AuslanderReiten.Cones.TwoConeTail

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
local notation "D" => productTwoConeData q

abbrev productTwistedTotal := ExternalTensor.complex k Te Te Q₀ Q₀

def tensorHighB (n : ℕ) :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+4) (barB q H (n+3)) (barDb q H)

def tensorHighG (n : ℕ) :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+2) (barG q H (n+2)) (barDb q H)

theorem tensorHighB_chain (n : ℕ) :
    ((D).d (n+4)).comp (tensorHighB q H (n+1)) =
      (tensorHighB q H n).comp ((productTwistedTotal q H).d (n+4) (n+3)).hom := by
  change ((ExternalTensor.complex k Te Te P₀ P₀).d (n+5) (n+4)).hom.comp
      (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+4) (n+5)
        (barB q H (n+4)) (barDb q H)) =
    (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+4)
      (barB q H (n+3)) (barDb q H)).comp
      ((productTwistedTotal q H).d (n+4) (n+3)).hom
  rw [ExternalTensor.bottomMap_d_target,
    ExternalTensor.bottomMap_d_source k Te Te (hg := barDb_cycle q H), barB_chain]

theorem tensorHighG_homotopy (n : ℕ) :
    ((D).first (n+2)).comp (tensorHighB q H (n+1)) =
      ((D).d (n+2)).comp (tensorHighG q H (n+1)) +
        (tensorHighG q H n).comp ((productTwistedTotal q H).d (n+4) (n+3)).hom := by
  change (ExternalTensor.firstCubic k Te Te P₀ P₀ (barComparison q) (n+2)).comp
      (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+4) (n+5)
        (barB q H (n+4)) (barDb q H)) =
    ((ExternalTensor.complex k Te Te P₀ P₀).d (n+3) (n+2)).hom.comp
      (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+4) (n+3)
        (barG q H (n+3)) (barDb q H)) +
    (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+2)
      (barG q H (n+2)) (barDb q H)).comp
      ((productTwistedTotal q H).d (n+4) (n+3)).hom
  rw [ExternalTensor.firstCubic_bottomMap, ExternalTensor.bottomMap_d_target,
    ExternalTensor.bottomMap_d_source k Te Te (hg := barDb_cycle q H),
    ← ExternalTensor.bottomMap_add, ← barG_equation]

theorem tensorHighG_second (n : ℕ) :
    ((D).second n).comp (tensorHighG q H (n+1)) = 0 :=
  ExternalTensor.secondCubic_bottomMap k Te Te P₀ Q₀ P₀ Q₀ (barComparison q)
    (n+4) n (barG q H (n+3)) (barDb q H)

theorem tensorHighB_second (n : ℕ) :
    ((D).second (n+2)).comp (tensorHighB q H (n+1)) = 0 :=
  ExternalTensor.secondCubic_bottomMap k Te Te P₀ Q₀ P₀ Q₀ (barComparison q)
    (n+4) (n+2) (barB q H (n+4)) (barDb q H)

end ArExplicit.T

end

end OAI
