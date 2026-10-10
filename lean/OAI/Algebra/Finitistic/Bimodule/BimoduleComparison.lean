import OAI.Algebra.Finitistic.Bimodule.BimoduleBar
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerived

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Canonical scalar restriction agrees with every supplied compatible field action. -/
theorem scalarModule_eq (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] :
    scalarModule k D (ModuleCat.of D V) = (inferInstance : Module k V) := by
  apply Module.ext
  funext c v
  exact IsScalarTower.algebraMap_smul D c v

/-- Coherence between the categorical tensor functor and the literal balancing quotient. -/
def tensorFunctorObjIso (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] :
    (tensorFunctor k D X).obj (ModuleCat.of D V) ≅ ModuleCat.of D (tensor k D X V) := by
  have h := scalarModule_eq k D V
  cases h
  exact Iso.refl _

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
/-- The scalar-action coherence is natural for every D-linear map. -/
theorem tensorFunctorObjIso_natural (V W : Type u)
    [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
    [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]
    (h : V →ₗ[D] W) :
    (tensorFunctor k D X).map (ModuleCat.ofHom h) ≫ (tensorFunctorObjIso k D X W).hom =
      (tensorFunctorObjIso k D X V).hom ≫ ModuleCat.ofHom (map k D X V W h) := by
  have hV := scalarModule_eq k D V
  have hW := scalarModule_eq k D W
  cases hV
  cases hW
  rfl

local instance (V : ModuleCat.{u} D) : Module k V := scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The categorical derived-resolution model and the explicit balanced bar complex agree. -/
def resolvedTensorIso (N : ModuleCat.{u} D) :
    resolvedTensor k D X N ≅ tensorResolution k D X N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => tensorFunctorObjIso k D X (DerivedBar.term k D N (n+1)))
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      simpa only [tensorResolution, resolvedTensor, DerivedBar.projectiveResolution,
        DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using (tensorFunctorObjIso_natural k D X (DerivedBar.term k D N (j+1+1))
        (DerivedBar.term k D N (j+1)) (DerivedBar.differential k D N (j+1))).symm)

/-- The literal arbitrary-bimodule two-sided bar computes genuine derived tensor of a module.
There is no flatness assumption or ordinary tensor-power replacement. -/
def explicitBarComputesDerivedTensor (N : ModuleCat.{u} D) :
    (tensorFunctor k D X).leftDerivedToHomotopyCategory.obj N ≅
      (HomotopyCategory.quotient (ModuleCat.{u} D) (ComplexShape.down ℕ)).obj
        (barComplex k D X N) :=
  barComputesDerivedTensor k D X N ≪≫
    (HomotopyCategory.quotient (ModuleCat.{u} D) (ComplexShape.down ℕ)).mapIso
      (resolvedTensorIso k D X N ≪≫ tensorResolutionIso k D X N)

/-- Actual left-derived tensor homology (Tor), computed by the explicit two-sided bar. -/
def barHomologyIso (N : ModuleCat.{u} D) (i : ℕ) :
    ((tensorFunctor k D X).leftDerived i).obj N ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (ComplexShape.down ℕ) i).obj
        (barComplex k D X N) :=
  (DerivedBar.projectiveResolution k D N).isoLeftDerivedObj (tensorFunctor k D X) i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (ComplexShape.down ℕ) i).mapIso
      (resolvedTensorIso k D X N ≪≫ tensorResolutionIso k D X N)
end DerivedBar.BimoduleTensor

end

end OAI
