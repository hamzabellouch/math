import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalOrientationCoefficient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTensorNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCharacterCancellation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyQuotient

namespace OAI

/-! # Rational scalar twists of an ambient coefficient representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def rationalScalarTwist (A : Rep ℤ G) (η : G →* ℚ) : Rep ℤ G :=
  rationalCharacterRep η ⊗ A

def rationalScalarTwistRestrictionIso (N : Subgroup G) (A : Rep ℤ G)
    (η : G →* ℚ) (hη : ∀ a : N, η (a : G) = 1) :
    trivialTensorCoefficient (ModuleCat.of ℤ ℚ) (Rep.res N.subtype A) ≅
      Rep.res N.subtype (rationalScalarTwist A η) :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) (by
    intro a
    apply TensorProduct.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro v
    change q ⊗ₜ[ℤ] (A.ρ (a : G) v) = (η (a : G) * q) ⊗ₜ[ℤ] (A.ρ (a : G) v)
    rw [hη, one_mul]))

variable (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

def normalHomologyAddAction (d : ℕ) : G →* AddMonoid.End
    (groupHomology (Rep.res N.subtype A) d) where
  toFun g := (normalHomologyMap ℤ N A d g).hom.toAddMonoidHom
  map_one' := by rw [normalHomologyMap_one]; rfl
  map_mul' g h := by rw [normalHomologyMap_mul]; rfl

theorem scalarTwist_conjugation_naturality (η : G →* ℚ)
    (hη : ∀ a : N, η (a : G) = 1) (d : ℕ) (g : G) :
    groupHomology.map (MonoidHom.id N) (rationalScalarTwistRestrictionIso N A η hη).hom d ≫
        normalHomologyMap ℤ N (rationalScalarTwist A η) d g =
      groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
          (trivialTensorCoefficientMap (rationalScalarMap (η g)) _
            (normalHomologyCoefficient ℤ N A g)) d ≫
        groupHomology.map (MonoidHom.id N) (rationalScalarTwistRestrictionIso N A η hη).hom d := by
  rw [normalHomologyMap, ← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr rfl
  apply TensorProduct.ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro v
  rfl

theorem scalarTwistHomology_trivial (η : G →* ℚ)
    (hη : ∀ a : N, η (a : G) = 1) (d : ℕ)
    (e : (ℚ ⊗[ℤ] (groupHomology (Rep.res N.subtype A) d)) ≃ₗ[ℚ] ℚ)
    (hc : ∀ g, η g * rationalActionCharacter (normalHomologyAddAction N A d) e g = 1)
    (g : G) : normalHomologyMap ℤ N (rationalScalarTwist A η) d g = 𝟙 _ := by
  classical
  let R := Rep.res N.subtype A
  let f := (MulAut.conjNormal (H := N) g).toMonoidHom
  let φ := normalHomologyCoefficient ℤ N A g
  let ψ := trivialTensorCoefficientMap (rationalScalarMap (η g)) f φ
  let I := rationalTensorHomologyIso R d
  have ht : (tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
      (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (η g))).app
        (groupHomology R d)) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have he : ((tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
        (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (η g))).app
          (groupHomology R d))).hom z =
        TensorProduct.map (rationalScalarMap (η g)).hom
          (integralLinear ((normalHomologyAddAction N A d) g)) z := by
      induction z using TensorProduct.inductionOn with
      | tmul q x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    exact he.trans (rationalTensorAction_cancel _ e g _ (hc g) z)
  have hm : groupHomology.map f ψ d = 𝟙 _ := by
    apply (cancel_mono I.hom).mp
    rw [rationalTensorHomologyIso_naturality R R (rationalScalarMap (η g)) f φ d,
      ht, Category.comp_id, Category.id_comp]
  let J := (groupHomology.functor ℤ N d).mapIso (rationalScalarTwistRestrictionIso N A η hη)
  apply (cancel_epi J.hom).mp
  change groupHomology.map (MonoidHom.id N) (rationalScalarTwistRestrictionIso N A η hη).hom d ≫
      normalHomologyMap ℤ N (rationalScalarTwist A η) d g = J.hom ≫ 𝟙 _
  rw [scalarTwist_conjugation_naturality N A η hη d g, hm]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end PolycyclicRecognition

end

end OAI
