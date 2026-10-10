import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRepresentationQuotients

namespace OAI

/-! # The group-ring linear map of an integral representation morphism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] {A B C : Rep.{0} ℤ G}

def integralRepresentationMap (f : A ⟶ B) : A.ρ.asModule →ₗ[ℤ[G]] B.ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom

@[simp] theorem integralRepresentationMap_apply (f : A ⟶ B) (a : A) :
    integralRepresentationMap f (A.ρ.asModuleEquiv.symm a) =
      B.ρ.asModuleEquiv.symm (f.hom a) := rfl

@[simp] theorem integralRepresentationMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    integralRepresentationMap (f ≫ g) =
      (integralRepresentationMap g).comp (integralRepresentationMap f) := rfl

@[simp] theorem integralRepresentationMap_zero :
    integralRepresentationMap (0 : A ⟶ B) = 0 := rfl

end PolycyclicRecognition

end

end OAI
