import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalExteriorHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalModuleFunctor
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupInductionDimension

namespace OAI

/-! # Rationalization and restriction of scalars for group representations

The tensor extension is exact and left adjoint to scalar restriction. Thus it
preserves the projectives used in the finite rational-coefficient resolution.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

def rationalizeRepresentation (A : Rep.{0} ℤ G) : Rep ℚ G :=
  Rep.of {
    toFun g := (A.ρ g).baseChange ℚ
    map_one' := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro q a
      change q ⊗ₜ[ℤ] A.ρ 1 a = q ⊗ₜ[ℤ] a
      rw [map_one]
      rfl
    map_mul' g h := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro q a
      change q ⊗ₜ[ℤ] A.ρ (g * h) a = q ⊗ₜ[ℤ] A.ρ g (A.ρ h a)
      rw [map_mul]
      rfl }

def rationalizeRepresentationMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    rationalizeRepresentation A ⟶ rationalizeRepresentation B :=
  Rep.ofHom ⟨f.hom.toLinearMap.baseChange ℚ, fun g => by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change q ⊗ₜ[ℤ] f.hom (A.ρ g a) = q ⊗ₜ[ℤ] B.ρ g (f.hom a)
    rw [Rep.hom_comm_apply]⟩

def rationalizeRepresentationFunctor : Rep.{0} ℤ G ⥤ Rep.{0} ℚ G where
  obj := rationalizeRepresentation
  map := rationalizeRepresentationMap
  map_id A := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_comp f.hom.toLinearMap g.hom.toLinearMap

instance : (rationalizeRepresentationFunctor (G := G)).Additive where
  map_add := by
    intro A B f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact LinearMap.baseChange_add f.hom.toLinearMap g.hom.toLinearMap

def integralRestrictionRepresentation (A : Rep.{0} ℚ G) : Rep ℤ G :=
  Rep.of {
    toFun g := (A.ρ g).restrictScalars ℤ
    map_one' := by ext x; change A.ρ 1 x = x; rw [map_one]; rfl
    map_mul' g h := by ext x; change A.ρ (g * h) x = A.ρ g (A.ρ h x); rw [map_mul]; rfl }

def integralRestrictionMap {A B : Rep.{0} ℚ G} (f : A ⟶ B) :
    integralRestrictionRepresentation A ⟶ integralRestrictionRepresentation B :=
  Rep.ofHom ⟨f.hom.toLinearMap.restrictScalars ℤ, fun g => by
    apply LinearMap.ext
    exact Rep.hom_comm_apply f g⟩

def integralRestrictionFunctor : Rep.{0} ℚ G ⥤ Rep.{0} ℤ G where
  obj := integralRestrictionRepresentation
  map := integralRestrictionMap
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (integralRestrictionFunctor (G := G)).PreservesEpimorphisms where
  preserves f hf := (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective f).mp hf)

local instance (B : Rep.{0} ℚ G) : Module ℚ (integralRestrictionRepresentation B) := B.hV2

def rationalRepresentationHomEquiv (A : Rep.{0} ℤ G) (B : Rep.{0} ℚ G) :
    (rationalizeRepresentation A ⟶ B) ≃ (A ⟶ integralRestrictionRepresentation B) where
  toFun f := Rep.ofHom ⟨(f.hom.toLinearMap.restrictScalars ℤ).comp
      (TensorProduct.mk ℤ ℚ A 1), fun g => by
    apply LinearMap.ext
    intro a
    exact Rep.hom_comm_apply f g ((1 : ℚ) ⊗ₜ[ℤ] a)⟩
  invFun f := Rep.ofHom ⟨rationalLinearExtension (show A →ₗ[ℤ] B from f.hom.toLinearMap), fun g => by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change q • (f.hom (A.ρ g a) : B) = B.ρ g (q • (f.hom a : B))
    erw [map_smul]
    exact congrArg (fun b : B => q • b) (Rep.hom_comm_apply f g a)⟩
  left_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro q a
    change q • f.hom ((1 : ℚ) ⊗ₜ[ℤ] a) = f.hom (q ⊗ₜ[ℤ] a)
    have ht : q • ((1 : ℚ) ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] a := by
      rw [TensorProduct.smul_tmul']
      change (q * 1) ⊗ₜ[ℤ] a = q ⊗ₜ[ℤ] a
      rw [mul_one]
    erw [← ht, map_smul]
  right_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    change (1 : ℚ) • (f.hom a : B) = (f.hom a : B)
    exact one_smul _ _

def rationalRepresentationAdjunction :
    rationalizeRepresentationFunctor (G := G) ⊣ integralRestrictionFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := rationalRepresentationHomEquiv
    homEquiv_naturality_left_symm f g := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro q a
      rfl
    homEquiv_naturality_right := by intros; rfl }

instance : (rationalizeRepresentationFunctor (G := G)).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    rationalRepresentationAdjunction

theorem rationalizeRepresentationFunctor_map_exact
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.Exact) :
    (S.map rationalizeRepresentationFunctor).Exact := by
  have hs := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (S.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))).mp
      (hS.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))
  apply (forget₂ (Rep ℚ G) (ModuleCat ℚ)).reflects_exact_of_faithful
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact Module.Flat.lTensor_exact ℚ (f := S.f.hom.toLinearMap) (g := S.g.hom.toLinearMap) hs

instance : (rationalizeRepresentationFunctor (G := G)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ rationalizeRepresentationFunctor_map_exact

instance : (rationalizeRepresentationFunctor (G := G)).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_map_exact _ rationalizeRepresentationFunctor_map_exact

instance : (rationalizeRepresentationFunctor (G := G)).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_map_exact _ rationalizeRepresentationFunctor_map_exact

end PolycyclicRecognition

end

end OAI
