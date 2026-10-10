import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFinsuppHom

namespace OAI

/-! # The contravariant regular dual of a group-ring representation

The regular dual is Hom over the group ring into the regular module, with
left action induced by inverse right translation on the target. This is the
representation used in the top-degree duality pairing.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def regularRightTranslation (g : G) : Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G :=
  Rep.leftRegularHom _ (MonoidAlgebra.single g⁻¹ 1)

@[simp] theorem regularRightTranslation_single (g h : G) (r : ℤ) :
    (regularRightTranslation g).hom (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (h * g⁻¹) r := by
  rw [regularRightTranslation, Rep.leftRegularHom_hom_single]
  rw [Representation.ofMulAction_single]
  simp

@[simp] theorem regularRightTranslation_one :
    regularRightTranslation (1 : G) = 𝟙 (Rep.leftRegular ℤ G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro h
  apply LinearMap.ext_ring
  change (regularRightTranslation (1 : G)).hom (MonoidAlgebra.single h 1) =
    MonoidAlgebra.single h 1
  simpa only [inv_one, mul_one] using regularRightTranslation_single (1 : G) h 1

theorem regularRightTranslation_mul (g h : G) :
    regularRightTranslation h ≫ regularRightTranslation g =
      regularRightTranslation (g * h) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change (regularRightTranslation g).hom
    ((regularRightTranslation h).hom (MonoidAlgebra.single x 1)) =
      (regularRightTranslation (g * h)).hom (MonoidAlgebra.single x 1)
  rw [regularRightTranslation_single, regularRightTranslation_single,
    regularRightTranslation_single]
  simp only [mul_inv_rev, mul_assoc]

def regularDualRepresentation (P : Rep ℤ G) :
    Representation ℤ G (P ⟶ Rep.leftRegular ℤ G) where
  toFun g := Linear.rightComp ℤ P (regularRightTranslation g)
  map_one' := by
    apply LinearMap.ext
    intro f
    change f ≫ regularRightTranslation (1 : G) = f
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    change (f ≫ regularRightTranslation (g * h)) =
      (f ≫ regularRightTranslation h) ≫ regularRightTranslation g
    rw [Category.assoc, regularRightTranslation_mul]

def regularDual (P : Rep ℤ G) : Rep ℤ G := Rep.of (regularDualRepresentation P)

def regularDualMap {P Q : Rep ℤ G} (f : P ⟶ Q) : regularDual Q ⟶ regularDual P :=
  Rep.ofHom ⟨Linear.leftComp ℤ (Rep.leftRegular ℤ G) f, by
    intro g
    apply LinearMap.ext
    intro q
    exact (Category.assoc f q (regularRightTranslation g)).symm⟩

@[simp] theorem regularDualMap_apply {P Q : Rep ℤ G} (f : P ⟶ Q)
    (q : Q ⟶ Rep.leftRegular ℤ G) : (regularDualMap f).hom q = f ≫ q := rfl

end PolycyclicRecognition

end

end OAI
