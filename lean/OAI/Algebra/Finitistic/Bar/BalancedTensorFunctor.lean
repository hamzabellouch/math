import OAI.Algebra.Finitistic.Bar.TensorModel
import OAI.Algebra.Finitistic.Bimodule.BimoduleComparison

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Balanced
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
  (f : A →ₐ[k] D)

local instance (V : ModuleCat.{u} A) : Module k V := BimoduleTensor.scalarModule k A V
local instance (V : ModuleCat.{u} A) : IsScalarTower k A V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def tensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} D where
  obj V := ModuleCat.of D (tensor f V)
  map h := ModuleCat.ofHom (map f _ _ h.hom)
  map_id V := ModuleCat.hom_ext (map_id f V)
  map_comp h g := ModuleCat.hom_ext (map_comp f _ _ _ h.hom g.hom)

instance tensorFunctor_additive : (tensorFunctor f).Additive where
  map_add := by
    intro V W h g
    apply ModuleCat.hom_ext
    apply (relations f V).linearMap_qext
    apply AlgebraTensorModule.ext
    intro d v
    change quotient f W (d ⊗ₜ[k] (h.hom v + g.hom v)) =
      quotient f W (d ⊗ₜ[k] h.hom v) + quotient f W (d ⊗ₜ[k] g.hom v)
    rw [TensorProduct.tmul_add, map_add]

def tensorFunctorObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] :
    (tensorFunctor f).obj (ModuleCat.of A V) ≅ ModuleCat.of D (tensor f V) := by
  have h := BimoduleTensor.scalarModule_eq k A V
  cases h
  exact Iso.refl _

theorem tensorFunctorObjIso_natural (V W : Type u)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    (h : V →ₗ[A] W) :
    (tensorFunctor f).map (ModuleCat.ofHom h) ≫ (tensorFunctorObjIso f W).hom =
      (tensorFunctorObjIso f V).hom ≫ ModuleCat.ofHom (map f V W h) := by
  have hV := BimoduleTensor.scalarModule_eq k A V
  have hW := BimoduleTensor.scalarModule_eq k A W
  cases hV
  cases hW
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def resolvedTensorIso :
    ((tensorFunctor f).mapHomologicalComplex (.down ℕ)).obj
      (DerivedBar.projectiveResolution k A N).complex ≅ tensorBarComplex k A D N f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorFunctorObjIso f (DerivedBar.term k A N (n+1)))
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      simpa only [tensorBarComplex, DerivedBar.projectiveResolution,
        DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
        using (tensorFunctorObjIso_natural f (DerivedBar.term k A N (j+1+1))
          (DerivedBar.term k A N (j+1)) (DerivedBar.differential k A N (j+1))).symm)

/-- The left-derived balanced tensor functor is computed by exactly the
original tensorBarComplex, via the proved free bar projective resolution. -/
def tensorBarComputesLeftDerived :
    (tensorFunctor f).leftDerivedToHomotopyCategory.obj (ModuleCat.of A N) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} D) (.down ℕ)).obj (tensorBarComplex k A D N f) :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedToHomotopyCategoryObj (tensorFunctor f) ≪≫
    (HomotopyCategory.quotient (ModuleCat.{u} D) (.down ℕ)).mapIso (resolvedTensorIso f N)

def tensorBarHomologyIso (i : ℕ) :
    ((tensorFunctor f).leftDerived i).obj (ModuleCat.of A N) ≅
      (tensorBarComplex k A D N f).homology i :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj (tensorFunctor f) i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.down ℕ) i).mapIso (resolvedTensorIso f N)
end DerivedBar.Balanced

end

end OAI
