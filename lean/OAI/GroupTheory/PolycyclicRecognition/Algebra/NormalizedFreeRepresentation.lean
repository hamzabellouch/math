import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RepCochainMaps

namespace OAI

/-! # The normalized free cover of an integral representation

The basis omits zero, and a coefficient morphism sends a basis element to zero
whenever its image is zero. Thus the free-cover functor preserves zero maps.
The augmentation is a natural epimorphism with projective source.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedFreeRepresentation (A : Rep.{0} ℤ G) : Rep.{0} ℤ G :=
  Rep.free ℤ G {a : A // a ≠ 0}

def normalizedFreeGenerator (A : Rep.{0} ℤ G) (a : A) :
    normalizedFreeRepresentation A := by
  classical
  exact if h : a = 0 then 0 else Finsupp.single ⟨a, h⟩ (MonoidAlgebra.single 1 1)

@[simp]
theorem normalizedFreeGenerator_zero (A : Rep.{0} ℤ G) :
    normalizedFreeGenerator A 0 = 0 := by
  simp [normalizedFreeGenerator]

theorem normalizedFreeGenerator_of_ne_zero (A : Rep.{0} ℤ G) (a : A) (ha : a ≠ 0) :
    normalizedFreeGenerator A a = Finsupp.single ⟨a, ha⟩ (MonoidAlgebra.single 1 1) := by
  simp [normalizedFreeGenerator, ha]
  rfl

def normalizedFreeMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedFreeRepresentation A ⟶ normalizedFreeRepresentation B :=
  Rep.freeLift ℤ G (normalizedFreeRepresentation B)
    (fun a : {a : A // a ≠ 0} => normalizedFreeGenerator B (f.hom a.1))

@[simp]
theorem normalizedFreeMap_generator {A B : Rep.{0} ℤ G} (f : A ⟶ B) (a : A) :
    (normalizedFreeMap f).hom (normalizedFreeGenerator A a) =
      normalizedFreeGenerator B (f.hom a) := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  · rw [normalizedFreeGenerator_of_ne_zero A a ha]
    change (Representation.freeLift (normalizedFreeRepresentation B).ρ
      (fun b : {b : A // b ≠ 0} => normalizedFreeGenerator B (f.hom b.1)))
      (Finsupp.single ⟨a, ha⟩ (MonoidAlgebra.single 1 1)) = _
    rw [Representation.freeLift_single_single]
    simp
    exact one_smul ℤ _

def normalizedFreeAugmentation (A : Rep.{0} ℤ G) : normalizedFreeRepresentation A ⟶ A :=
  Rep.freeLift ℤ G A (fun a : {a : A // a ≠ 0} => a.1)

@[simp]
theorem normalizedFreeAugmentation_generator (A : Rep.{0} ℤ G) (a : A) :
    (normalizedFreeAugmentation A).hom (normalizedFreeGenerator A a) = a := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  · rw [normalizedFreeGenerator_of_ne_zero A a ha]
    change (Representation.freeLift A.ρ (fun b : {b : A // b ≠ 0} => b.1))
      (Finsupp.single ⟨a, ha⟩ (MonoidAlgebra.single 1 1)) = _
    rw [Representation.freeLift_single_single]
    simp
    exact @one_smul ℤ A _ A.hV2.toMulAction a

instance normalizedFreeAugmentation_epi (A : Rep.{0} ℤ G) :
    Epi (normalizedFreeAugmentation A) := by
  apply (Rep.epi_iff_surjective _).mpr
  intro a
  exact ⟨normalizedFreeGenerator A a, normalizedFreeAugmentation_generator A a⟩

theorem normalizedFreeMap_id (A : Rep.{0} ℤ G) :
    normalizedFreeMap (𝟙 A) = 𝟙 (normalizedFreeRepresentation A) := by
  apply Rep.free_ext
  intro a
  change (normalizedFreeMap (𝟙 A)).hom
    (Finsupp.single a (MonoidAlgebra.single 1 1)) = Finsupp.single a (MonoidAlgebra.single 1 1)
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2, normalizedFreeMap_generator]
  rfl

theorem normalizedFreeMap_comp {A B C : Rep.{0} ℤ G} (f : A ⟶ B) (g : B ⟶ C) :
    normalizedFreeMap (f ≫ g) = normalizedFreeMap f ≫ normalizedFreeMap g := by
  apply Rep.free_ext
  intro a
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2]
  change (normalizedFreeMap (f ≫ g)).hom (normalizedFreeGenerator A a.1) =
    (normalizedFreeMap g).hom ((normalizedFreeMap f).hom (normalizedFreeGenerator A a.1))
  rw [normalizedFreeMap_generator, normalizedFreeMap_generator, normalizedFreeMap_generator]
  rfl

@[simp]
theorem normalizedFreeMap_zero (A B : Rep.{0} ℤ G) :
    normalizedFreeMap (0 : A ⟶ B) = 0 := by
  apply Rep.free_ext
  intro a
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2]
  change (normalizedFreeMap (0 : A ⟶ B)).hom (normalizedFreeGenerator A a.1) = 0
  exact (normalizedFreeMap_generator (0 : A ⟶ B) a.1).trans
    (normalizedFreeGenerator_zero B)

def normalizedFreeFunctor : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G where
  obj := normalizedFreeRepresentation
  map := normalizedFreeMap
  map_id := normalizedFreeMap_id
  map_comp := normalizedFreeMap_comp

theorem normalizedFreeAugmentation_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedFreeMap f ≫ normalizedFreeAugmentation B =
      normalizedFreeAugmentation A ≫ f := by
  apply Rep.free_ext
  intro a
  rw [← normalizedFreeGenerator_of_ne_zero A a.1 a.2]
  change (normalizedFreeAugmentation B).hom
    ((normalizedFreeMap f).hom (normalizedFreeGenerator A a.1)) =
      f.hom ((normalizedFreeAugmentation A).hom (normalizedFreeGenerator A a.1))
  rw [normalizedFreeMap_generator, normalizedFreeAugmentation_generator,
    normalizedFreeAugmentation_generator]

instance normalizedFreeRepresentation_projective (A : Rep.{0} ℤ G) :
    Projective (normalizedFreeRepresentation A) := by
  change Projective (Rep.free ℤ G {a : A // a ≠ 0})
  infer_instance

end PolycyclicRecognition

end

end OAI
