import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinsuppRepresentationModule

namespace OAI

/-! # Hom out of a finite group-ring module commutes with direct sums -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] (G : Type) [Group G]
  (α : Type) (A B : Rep k G)

def representationModuleHomEquiv :
    (A ⟶ B) ≃ₗ[k] (A.ρ.asModule →ₗ[k[G]] B.ρ.asModule) :=
  (Rep.homLinearEquiv A B).trans (IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ)

def finsuppHomPostcompEquiv :
    (A.ρ.asModule →ₗ[k[G]] (α →₀ B.ρ.asModule)) ≃ₗ[k]
      (A.ρ.asModule →ₗ[k[G]] (Rep.finsupp α B).ρ.asModule) where
  __ := LinearEquiv.arrowCongrAddEquiv (LinearEquiv.refl k[G] A.ρ.asModule)
    (finsuppRepresentationModuleEquiv k G α B)
  map_smul' c f := by
    ext a
    change finsuppRepresentationModuleEquiv k G α B (c • f a) =
      c • finsuppRepresentationModuleEquiv k G α B (f a)
    exact ((finsuppRepresentationModuleEquiv k G α B).restrictScalars k).map_smul c (f a)

def finiteFinsuppHomEquiv [Module.Finite k[G] A.ρ.asModule] :
    (α →₀ (A ⟶ B)) ≃ₗ[k] (A ⟶ Rep.finsupp α B) :=
  (Finsupp.mapRange.linearEquiv (representationModuleHomEquiv k G A B)).trans
    ((LinearEquiv.ofBijective (LinearMap.finsuppLinearMap k)
      (LinearMap.finsuppLinearMap_bijective_of_moduleFinite (R := k[G])
        (M := A.ρ.asModule) (N := B.ρ.asModule) (ι := α) (S := k))).trans
      ((finsuppHomPostcompEquiv k G α A B).trans
        (representationModuleHomEquiv k G A (Rep.finsupp α B)).symm))

@[simp] theorem finiteFinsuppHomEquiv_apply [Module.Finite k[G] A.ρ.asModule]
    (x : α →₀ (A ⟶ B)) (a : A) (i : α) :
    ((finiteFinsuppHomEquiv k G α A B x).hom a) i = (x i).hom a := by
  change (((LinearMap.finsuppLinearMap k)
    (Finsupp.mapRange.linearEquiv (representationModuleHomEquiv k G A B) x))
      (A.ρ.asModuleEquiv.symm a)) i = (x i).hom a
  rw [LinearMap.finsuppLinearMap_apply_apply_apply]
  rfl

@[simp] theorem finiteFinsuppHomEquiv_single [Module.Finite k[G] A.ρ.asModule]
    (i : α) (f : A ⟶ B) (a : A) :
    (finiteFinsuppHomEquiv k G α A B (Finsupp.single i f)).hom a =
      Finsupp.single i (f.hom a) := by
  ext j
  rw [finiteFinsuppHomEquiv_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

end PolycyclicRecognition

end

end OAI
