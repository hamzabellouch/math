import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylInvolution

namespace OAI

/-! The conjugated inversion is an involutive linear action on the
actual root-cover sections. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootWeylSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeRootWeylElement hp • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    change F.val (cubicThetaPrimeRootWeylElement hp • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeRootWeylElement hp • y)
    rw [cubicThetaPrimeRootWeylPoint_intertwines,F.property,cubicThetaPrimeRootWeyl_kubota]⟩

lemma cubicThetaPrimeRootWeylSection_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeRootWeylSection hp) := by
  intro F
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y))=F.val y
  rw [cubicThetaPrimeRootWeylPoint_involutive]

def cubicThetaPrimeRootWeylOperator {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootSections p ≃ₗ[ℂ] cubicThetaPrimeRootSections p where
  toFun := cubicThetaPrimeRootWeylSection hp
  invFun := cubicThetaPrimeRootWeylSection hp
  left_inv := cubicThetaPrimeRootWeylSection_involutive hp
  right_inv := cubicThetaPrimeRootWeylSection_involutive hp
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

end CubicFirstMoment

end

end OAI
