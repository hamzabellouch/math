import OAI.Algebra.AuslanderReiten.Coordinates.TensorHighLift
import OAI.Algebra.AuslanderReiten.Cones.TwoConeTailRestriction

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
local notation "D" => productTwoConeData q
local notation "Q₀" => productTwistedTotal q H

private theorem tensorHighG_signed (n : ℕ) :
    -((D).d (n+2)).comp (tensorHighG q H (n+1)) -
      ((D).first (n+2)).comp (tensorHighB q H (n+1)) =
      (tensorHighG q H n).comp ((Q₀).d (n+4) (n+3)).hom := by
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (tensorHighG_homotopy q H n) x
  change (D).first (n+2) (tensorHighB q H (n+1) x) =
    (D).d (n+2) (tensorHighG q H (n+1) x) +
      tensorHighG q H n ((Q₀).d (n+4) (n+3) x) at hh
  have hn (y : (D).term (n+2)) : -y=y :=
    neg_eq_iff_add_eq_zero.mpr (SparseParity.module_add_self_eq_zero (k := k) y)
  change -((D).d (n+2) (tensorHighG q H (n+1) x)) -
    (D).first (n+2) (tensorHighB q H (n+1) x) = _
  rw [hh, sub_eq_add_neg, hn, hn, ← add_assoc,
    SparseParity.module_add_self_eq_zero (k := k), zero_add]
  rfl

def productHighLift (n : ℕ) :=
  TwoCone.highLift D (Q₀).X (tensorHighG q H) (tensorHighB q H) n

theorem productHighLift_comm (n : ℕ) :
    (TwoCone.d D n).comp (productHighLift q H (n+1)) =
      (productHighLift q H n).comp ((Q₀).d (n+4) (n+3)).hom :=
  TwoCone.highLift_comm D (Q₀).X (fun n => ((Q₀).d (n+1) n).hom)
    (tensorHighG q H) (tensorHighB q H) (tensorHighB_chain q H)
    (tensorHighG_signed q H) (tensorHighG_second q H) (tensorHighB_second q H) n

abbrev productFourthSyzygy :=
  TwoCone.FourthCokernel (Q₀).X (fun n => ((Q₀).d (n+1) n).hom)

def productTailMap :=
  TwoCone.tailMap D (Q₀).X (fun n => ((Q₀).d (n+1) n).hom)
    (productHighLift q H 1) (productHighLift q H 2) (productHighLift_comm q H 1)

local notation "F" => ExternalTensor.envelopingFunctor k R R

abbrev bimoduleTwistedTerm (n : ℕ) := (F).obj ((Q₀).X n)

def bimoduleTwistedDifferential (n : ℕ) := ((F).map ((Q₀).d (n+1) n)).hom

def bimoduleHighLift (n : ℕ) :=
  TwoCone.restrictedHighLift (ExternalTensor.envelopingEquiv k R R).symm.toRingHom
    D (Q₀).X (productHighLift q H) n

theorem bimoduleHighLift_comm (n : ℕ) :
    (TwoCone.d (bimoduleTwoConeData q) n).comp (bimoduleHighLift q H (n+1)) =
      (bimoduleHighLift q H n).comp (bimoduleTwistedDifferential q H (n+3)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (productHighLift_comm q H n) x

abbrev fourthSyzygy := TwoCone.FourthCokernel (bimoduleTwistedTerm q H) (bimoduleTwistedDifferential q H)

def tailMap : fourthSyzygy q H →ₗ[ExternalTensor.EnvelopingProduct k R R] firstTail q :=
  TwoCone.tailMap (bimoduleTwoConeData q) (bimoduleTwistedTerm q H) (bimoduleTwistedDifferential q H)
    (bimoduleHighLift q H 1) (bimoduleHighLift q H 2) (bimoduleHighLift_comm q H 1)

@[simp] theorem tailMap_mk (x : bimoduleTwistedTerm q H 4) :
    tailMap q H (Submodule.Quotient.mk x) = Submodule.Quotient.mk (bimoduleHighLift q H 1 x) := rfl

end ArExplicit.T

end

end OAI
