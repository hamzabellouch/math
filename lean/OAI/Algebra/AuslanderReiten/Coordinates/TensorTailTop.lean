import OAI.Algebra.AuslanderReiten.Coordinates.TensorTailMap
import OAI.Algebra.AuslanderReiten.Coordinates.TensorTopComparison
import OAI.Algebra.AuslanderReiten.Cones.TwoConeTopCokernel

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "D" => productTwoConeData q
local notation "Q₀" => productTwistedTotal q H

theorem productHighLift_top (n : ℕ) :
    (TwoCone.topProjection D n).comp (productHighLift q H n) = tensorTopComparison q H (n+3) := rfl

theorem bimoduleHighLift_top (n : ℕ) :
    (TwoCone.topProjection (bimoduleTwoConeData q) n).comp (bimoduleHighLift q H n) =
      ((ExternalTensor.envelopingFunctor k R R).map
        (ModuleCat.ofHom (tensorTopComparison q H (n+3)))).hom := rfl

def topSyzygyMap :=
  (LinearMap.range (bimoduleTwistedDifferential q H 4)).liftQ
    (((LinearMap.range ((bimoduleTwoConeData q).d 5)).mkQ).comp
      (((ExternalTensor.envelopingFunctor k R R).map
        (ModuleCat.ofHom (tensorTopComparison q H 4))).hom)) (by
          rintro x ⟨y,rfl⟩
          change (LinearMap.range ((bimoduleTwoConeData q).d 5)).mkQ
            (tensorTopComparison q H 4 ((Q₀).d 5 4 y)) = 0
          rw [← show (productTwoConeData q).d 5 (tensorTopComparison q H 5 y) =
            tensorTopComparison q H 4 ((Q₀).d 5 4 y) from
              LinearMap.congr_fun (tensorTopComparison_chain q H 4) y]
          exact LinearMap.congr_fun (LinearMap.range_mkQ_comp ((bimoduleTwoConeData q).d 5)) _)

theorem tailMap_top :
    (TwoCone.topCokernelMap (bimoduleTwoConeData q) 1).comp (tailMap q H) = topSyzygyMap q H := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

end ArExplicit.T

end

end OAI
