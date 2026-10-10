import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupInductionCoordinates
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

namespace OAI

/-! # Exact induction from arbitrary subgroups -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G] (N : Subgroup G)

@[simp] theorem subgroupInductionMap_mk {A B : Rep k N} (f : A ⟶ B) (g : G) (a : A) :
    (Rep.indMap N.subtype f).hom (IndV.mk N.subtype A.ρ g a) =
      IndV.mk N.subtype B.ρ g (f.hom a) := by
  simp [Rep.indMap, IndV.mk]

theorem subgroupInductionCoordinates_naturality {A B : Rep k N} (f : A ⟶ B) :
    (subgroupInductionCoordinates N k B).comp (Rep.indMap N.subtype f).hom.toLinearMap =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap).comp (subgroupInductionCoordinates N k A) := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change subgroupInductionCoordinates N k B ((Rep.indMap N.subtype f).hom
      (IndV.mk N.subtype A.ρ g a)) = _
  rw [subgroupInductionMap_mk k N f g a, subgroupInductionCoordinates_mk N k B g (f.hom a)]
  change _ = Finsupp.mapRange.linearMap f.hom.toLinearMap
    (subgroupInductionCoordinates N k A (IndV.mk N.subtype A.ρ g a))
  rw [subgroupInductionCoordinates_mk N k A g a]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  congr 1
  exact (Rep.hom_comm_apply f (subgroupRightPart N g)⁻¹ a).symm

theorem subgroupInductionMap_injective {A B : Rep k N} (f : A ⟶ B)
    (hf : Function.Injective f.hom) : Function.Injective (Rep.indMap N.subtype f).hom := by
  intro x y hxy
  apply (subgroupInductionEquiv N k A).injective
  have h := congrArg (subgroupInductionCoordinates N k B) hxy
  have hx := LinearMap.congr_fun (subgroupInductionCoordinates_naturality k N f) x
  have hy := LinearMap.congr_fun (subgroupInductionCoordinates_naturality k N f) y
  simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at hx hy
  change subgroupInductionCoordinates N k B ((Rep.indMap N.subtype f).hom x) =
    subgroupInductionCoordinates N k B ((Rep.indMap N.subtype f).hom y) at h
  rw [hx, hy] at h
  exact Finsupp.mapRange_injective _ (map_zero f.hom) hf h

instance subgroupInduction_preservesMonomorphisms :
    (Rep.indFunctor k N.subtype).PreservesMonomorphisms where
  preserves f hf := by
    rw [Rep.mono_iff_injective]
    exact subgroupInductionMap_injective k N f ((Rep.mono_iff_injective f).mp hf)

instance subgroupInduction_preservesHomology :
    (Rep.indFunctor k N.subtype).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance subgroupInduction_preservesProjectives :
    (Rep.indFunctor k N.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.indResAdjunction k N.subtype)

instance subgroupInduction_additive : (Rep.indFunctor k N.subtype).Additive where
  map_add {A B} f h := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    simp [Rep.indMap, IndV.mk, Rep.add_hom]

def subgroupInducedResolution {A : Rep k N} (P : ProjectiveResolution A) :
    ProjectiveResolution (Rep.ind N.subtype A) :=
  (Rep.indFunctor k N.subtype).mapProjectiveResolution P


end PolycyclicRecognition

end

end OAI
