import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionCoordinates
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

namespace OAI

/-! # Exact induction along the normal subgroup in a cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal]

omit [N.Normal] in
@[simp] theorem normalInductionMap_mk {A B : Rep k N} (f : A ⟶ B) (g : G) (a : A) :
    (Rep.indMap N.subtype f).hom (IndV.mk N.subtype A.ρ g a) =
      IndV.mk N.subtype B.ρ g (f.hom a) := by
  simp [Rep.indMap, IndV.mk]

theorem inductionCoordinates_naturality {A B : Rep k N} (f : A ⟶ B) :
    (inductionCoordinates k N B).comp (Rep.indMap N.subtype f).hom.toLinearMap =
      (Finsupp.mapRange.linearMap f.hom.toLinearMap).comp (inductionCoordinates k N A) := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inductionCoordinates k N B ((Rep.indMap N.subtype f).hom
      (IndV.mk N.subtype A.ρ g a)) = _
  rw [normalInductionMap_mk k N f g a, inductionCoordinates_mk k N B g (f.hom a)]
  change _ = Finsupp.mapRange.linearMap f.hom.toLinearMap
    (inductionCoordinates k N A (IndV.mk N.subtype A.ρ g a))
  rw [inductionCoordinates_mk k N A g a]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  congr 1
  exact (Rep.hom_comm_apply f (normalQuotientPart N g)⁻¹ a).symm

theorem normalInductionMap_injective {A B : Rep k N} (f : A ⟶ B)
    (hf : Function.Injective f.hom) : Function.Injective (Rep.indMap N.subtype f).hom := by
  intro x y hxy
  apply (normalInductionEquiv k N A).injective
  have h := congrArg (inductionCoordinates k N B) hxy
  have hx := LinearMap.congr_fun (inductionCoordinates_naturality k N f) x
  have hy := LinearMap.congr_fun (inductionCoordinates_naturality k N f) y
  simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at hx hy
  change inductionCoordinates k N B ((Rep.indMap N.subtype f).hom x) =
    inductionCoordinates k N B ((Rep.indMap N.subtype f).hom y) at h
  rw [hx, hy] at h
  exact Finsupp.mapRange_injective _ (map_zero f.hom) hf h

instance normalInduction_preservesMonomorphisms :
    (Rep.indFunctor k N.subtype).PreservesMonomorphisms where
  preserves f hf := by
    rw [Rep.mono_iff_injective]
    exact normalInductionMap_injective k N f ((Rep.mono_iff_injective f).mp hf)

instance normalInduction_preservesHomology :
    (Rep.indFunctor k N.subtype).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance normalInduction_preservesProjectives :
    (Rep.indFunctor k N.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (Rep.indResAdjunction k N.subtype)

instance normalInduction_additive : (Rep.indFunctor k N.subtype).Additive where
  map_add {A B} f h := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext
    intro a
    simp [Rep.indMap, IndV.mk, Rep.add_hom]

def normalInducedResolution {A : Rep k N} (P : ProjectiveResolution A) :
    ProjectiveResolution (Rep.ind N.subtype A) :=
  (Rep.indFunctor k N.subtype).mapProjectiveResolution P

end PolycyclicRecognition

end

end OAI
