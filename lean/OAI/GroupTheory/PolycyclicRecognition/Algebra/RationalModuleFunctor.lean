import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalTensorHomology
import Mathlib.LinearAlgebra.TensorProduct.Tower

namespace OAI

/-! # Rationalization as a functor to rational modules

The codomain remembers the rational scalar action. Flatness proves exactness;
it does not assert a finite-dimensionality conclusion.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule

def rationalModuleFunctor : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ where
  obj M := ModuleCat.of ℚ (ℚ ⊗[ℤ] M)
  map f := ModuleCat.ofHom (f.hom.baseChange ℚ)
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp f.hom g.hom

instance : rationalModuleFunctor.Additive where
  map_add := by
    intro A B f g
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add f.hom g.hom

theorem rationalModuleFunctor_map_exact (S : ShortComplex (ModuleCat.{0} ℤ))
    (hS : S.Exact) : (S.map rationalModuleFunctor).Exact := by
  have hs := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  have he := Module.Flat.lTensor_exact ℚ (f := S.f.hom) (g := S.g.hom) hs
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (S.f.hom.baseChange ℚ) (S.g.hom.baseChange ℚ)
  exact he

instance : rationalModuleFunctor.PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ rationalModuleFunctor_map_exact

def rationalModuleHomologyIso (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n) ≅
      ModuleCat.of ℚ (ℚ ⊗[ℤ] C.homology n) :=
  (C.sc n).mapHomologyIso rationalModuleFunctor

theorem rationalModuleHomologyIso_naturality {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
        (rationalModuleHomologyIso D n).hom =
      (rationalModuleHomologyIso C n).hom ≫
        rationalModuleFunctor.map (HomologicalComplex.homologyMap f n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map f)
    rationalModuleFunctor

end PolycyclicRecognition

end

end OAI
