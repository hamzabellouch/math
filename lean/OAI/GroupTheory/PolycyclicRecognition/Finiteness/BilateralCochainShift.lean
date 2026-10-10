import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralFinsuppFunctor
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TwistedBilateralDifference
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

namespace OAI

/-! # Translation on direct sums of cochain complexes and their cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory

variable (k : Type) [CommRing k]

def bilateralFunctorTranslation (z : Multiplicative ℤ) :
    moduleFinsuppFunctor k ℤ ⟶ moduleFinsuppFunctor k ℤ where
  app M := ModuleCat.ofHom (bilateralTranslation k M z)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    rfl

variable (C : CochainComplex (ModuleCat k) ℕ)

def bilateralCochainTranslation (z : Multiplicative ℤ) :=
  ((bilateralFunctorTranslation k z).mapHomologicalComplex (ComplexShape.up ℕ)).app C

def bilateralCochainTwist (f : C ⟶ C) :=
  bilateralCochainTranslation k C (Multiplicative.ofAdd 1) ≫
    ((moduleFinsuppFunctor k ℤ).mapHomologicalComplex _).map f

def bilateralCohomologyIso (i : ℕ) :
    (((moduleFinsuppFunctor k ℤ).mapHomologicalComplex _).obj C).homology i ≅
      (moduleFinsuppFunctor k ℤ).obj (C.homology i) :=
  (C.sc i).mapHomologyIso (moduleFinsuppFunctor k ℤ)

theorem bilateralCohomologyIso_translation (z : Multiplicative ℤ) (i : ℕ) :
    HomologicalComplex.homologyMap (bilateralCochainTranslation k C z) i ≫
        (bilateralCohomologyIso k C i).hom =
      (bilateralCohomologyIso k C i).hom ≫
        (bilateralFunctorTranslation k z).app (C.homology i) := by
  have h := (C.sc i).homologyMap_mapNatTrans (bilateralFunctorTranslation k z)
  change HomologicalComplex.homologyMap (bilateralCochainTranslation k C z) i =
    (bilateralCohomologyIso k C i).hom ≫
      (bilateralFunctorTranslation k z).app (C.homology i) ≫
        (bilateralCohomologyIso k C i).inv at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem bilateralCohomologyIso_map (f : C ⟶ C) (i : ℕ) :
    HomologicalComplex.homologyMap
        (((moduleFinsuppFunctor k ℤ).mapHomologicalComplex _).map f) i ≫
        (bilateralCohomologyIso k C i).hom =
      (bilateralCohomologyIso k C i).hom ≫
        (moduleFinsuppFunctor k ℤ).map (HomologicalComplex.homologyMap f i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map f) (moduleFinsuppFunctor k ℤ)

theorem bilateralCohomologyIso_twist (f : C ⟶ C) (i : ℕ) :
    HomologicalComplex.homologyMap (bilateralCochainTwist k C f) i ≫
        (bilateralCohomologyIso k C i).hom =
      (bilateralCohomologyIso k C i).hom ≫
        (bilateralFunctorTranslation k (Multiplicative.ofAdd 1)).app (C.homology i) ≫
          (moduleFinsuppFunctor k ℤ).map (HomologicalComplex.homologyMap f i) := by
  rw [bilateralCochainTwist, HomologicalComplex.homologyMap_comp, Category.assoc,
    bilateralCohomologyIso_map, ← Category.assoc, bilateralCohomologyIso_translation]
  exact Category.assoc _ _ _

end PolycyclicRecognition

end

end OAI
