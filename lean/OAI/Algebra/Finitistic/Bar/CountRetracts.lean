import OAI.Algebra.Finitistic.Bar.DerivedTensorBarSplitting

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
open scoped DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

/-- Projection from the original chain direct sum to its r-th complex. -/
def directSumComplexProjection (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    directSumComplex S ⟶ S r where
  f n := ModuleCat.ofHom (DirectSum.component D ℕ (fun s => (S s).X n) r)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [directSumComplex, ChainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    rfl

@[simp] theorem directSumComplex_inclusion_projection
    (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    directSumComplexInclusion D S r ≫ directSumComplexProjection D S r = 𝟙 (S r) := by
  ext degree value
  change DirectSum.component D ℕ (fun summand => (S summand).X degree) r
    (DirectSum.lof D ℕ (fun summand => (S summand).X degree) r value) = value
  exact DirectSum.component.lof_self D (M := fun summand => (S summand).X degree) r value

end DerivedBar
namespace DerivedBar.ParityBridge

private theorem mapped_retract {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E) {V W : C} {U T : E} (e : U ≅ F.obj V) (f : T ≅ F.obj W)
    (i : V ⟶ W) (p : W ⟶ V) (h : i ≫ p = 𝟙 V) :
    (e.hom ≫ F.map i ≫ f.inv) ≫ (f.hom ≫ F.map p ≫ e.inv) = 𝟙 U := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, h, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id]

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance countRetractsScalarModule (V : ModuleCat D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance countRetractsScalarTower (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance countRetractsInflatedModule : Module A N := inflatedModule D X N
local instance countRetractsInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
local instance countRetractsHasDerivedCategory : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)
local notation "T" => tensorBarComplex k A D N (fstHom k D X)

/-- The original count subcomplex included into the actual balanced tensor bar. -/
def countTensorBarInclusion (r : ℕ) : S r ⟶ T :=
  directSumComplexInclusion D S r ≫
    (SquareZero.tensorCountSplitting k D X N (inflated_ideal_zero D X N)).inv

def countTensorBarProjection (r : ℕ) : T ⟶ S r :=
  (SquareZero.tensorCountSplitting k D X N (inflated_ideal_zero D X N)).hom ≫
    directSumComplexProjection D S r

@[simp] theorem countTensorBar_retract (r : ℕ) :
    countTensorBarInclusion k D X N r ≫ countTensorBarProjection k D X N r = 𝟙 (S r) := by
  simp only [countTensorBarInclusion, countTensorBarProjection, Category.assoc,
    Iso.inv_hom_id_assoc, directSumComplex_inclusion_projection]

/-- The genuine shifted iterate included into actual left-derived base change. -/
def shiftedIterateInclusion (r : ℕ) :
    (shiftedIterateDiagram k D X N).obj ⟨r⟩ ⟶
      (derivedBaseChange D (fstHom k D X)).obj (ModuleCat.of A N) :=
  (derivedIterateWeightShiftIso k D X N r).hom ≫
    (integerQ D).map (countTensorBarInclusion k D X N r) ≫
      (derivedBaseChangeBarIso D (fstHom k D X) N).inv

def shiftedIterateProjection (r : ℕ) :
    (derivedBaseChange D (fstHom k D X)).obj (ModuleCat.of A N) ⟶
      (shiftedIterateDiagram k D X N).obj ⟨r⟩ :=
  (derivedBaseChangeBarIso D (fstHom k D X) N).hom ≫
    (integerQ D).map (countTensorBarProjection k D X N r) ≫
      (derivedIterateWeightShiftIso k D X N r).inv

@[simp] theorem shiftedIterate_retract (r : ℕ) :
    shiftedIterateInclusion k D X N r ≫ shiftedIterateProjection k D X N r =
      𝟙 ((shiftedIterateDiagram k D X N).obj ⟨r⟩) := by
  exact mapped_retract (integerQ D) (derivedIterateWeightShiftIso k D X N r)
    (derivedBaseChangeBarIso D (fstHom k D X) N) _ _ (countTensorBar_retract k D X N r)
end DerivedBar.ParityBridge

end

end OAI
