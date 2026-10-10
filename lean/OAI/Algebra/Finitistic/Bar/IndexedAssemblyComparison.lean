import OAI.Algebra.Finitistic.Bar.FlatSupportedAssembly
import OAI.Algebra.Finitistic.Bar.BlockCoordinateGenerators

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal

private theorem assembly_eq {C : Type*} [Category C] {A B V W U T : C}
    {l : A ⟶ B} {e : B ⟶ V} {f : V ⟶ W} {i : A ⟶ U}
    {s : U ⟶ V} {a : U ⟶ T} {b : T ⟶ W} {t : A ⟶ W} {u : B ⟶ W}
    (h₁ : l ≫ e = i ≫ s) (h₂ : s ≫ f = a ≫ b)
    (h₃ : i ≫ a ≫ b = t) (h₄ : l ≫ u = t) : l ≫ e ≫ f = l ≫ u := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, h₃, h₄]

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance indexedAssemblyComparisonIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

local instance indexedAssemblyComparisonShapeDecidableEq (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _

def shapeAssembly (r n : ℕ) : indexedModule k D X N r n ⟶
    ModuleCat.of D (D ⊗[k] term k A N (r+n)) :=
  ModuleCat.ofHom ((SquareZero.twoSidedWeight k D X N (r+n) r).subtype.comp
    (Multibar.Indexed.decomposition k D X N (r+n) r).toLinearMap)

theorem shapeAssembly_injective (r n : ℕ) : Function.Injective (shapeAssembly k D X N r n).hom := by
  intro v w h
  exact (Multibar.Indexed.decomposition k D X N (r+n) r).injective (Subtype.ext h)

@[reassoc] theorem shapeAssembly_lof (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    ModuleCat.ofHom (DirectSum.lof D _ (Multibar.Indexed.outerTensor k D X N) p) ≫
      shapeAssembly k D X N r n = ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N p) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (Multibar.Indexed.assemble k D X N (r+n) r
    (DirectSum.lof D _ _ p v)).val = _
  simp only [Multibar.Indexed.assemble, DirectSum.toModule_lof, LinearMap.codRestrict_apply]
  rfl

theorem outerInclusion_eqToHom {n r : ℕ} (p q : Multibar.Indexed.Shape n r) (h : p=q) :
    eqToHom (congrArg (fun t => ModuleCat.of D (Multibar.Indexed.outerTensor k D X N t)) h) ≫
      ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N q) =
    ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N p) := by
  subst q
  simp

theorem reindexedModuleSummand_assembly (r n : ℕ) (p : Multibar.Indexed.Shape (r+n) r) :
    (reindexedModuleSummandIso k D X N r n p).inv ≫
      (moduleSummandIso k D X N r n ((moduleShapeEquiv r n).symm p)).hom ≫
        ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N
          (moduleShapeEquiv r n ((moduleShapeEquiv r n).symm p))) =
    ModuleCat.ofHom (Multibar.Indexed.outerInclusion k D X N p) := by
  simp only [reindexedModuleSummandIso, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  exact outerInclusion_eqToHom k D X N _ _ ((moduleShapeEquiv r n).apply_symm_apply p).symm

/-- The new embedding is exactly the old Shape assembly after the old inverse
coordinates. No new differential or replacement coordinate system is used. -/
theorem moduleFlatCoordinates_inv_flatEmbedding (r n : ℕ) :
    (moduleFlatCoordinates k D X N r n).inv ≫ flatEmbedding k D X N r n =
      shapeAssembly k D X N r n := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro p
  change (ModuleCat.ofHom (DirectSum.lof D _ (Multibar.Indexed.outerTensor k D X N) p) ≫
    (moduleFlatCoordinates k D X N r n).inv ≫ flatEmbedding k D X N r n).hom =
    (ModuleCat.ofHom (DirectSum.lof D _ (Multibar.Indexed.outerTensor k D X N) p) ≫
      shapeAssembly k D X N r n).hom
  apply congrArg ModuleCat.Hom.hom
  exact assembly_eq (moduleFlatCoordinates_inv_lof k D X N r n p)
    (flatEmbedding_supported k D X N r n ((moduleShapeEquiv r n).symm p))
    (reindexedModuleSummand_assembly k D X N r n p) (shapeAssembly_lof k D X N r n p)

theorem flatEmbedding_coordinates (r n : ℕ) : flatEmbedding k D X N r n =
    (moduleFlatCoordinates k D X N r n).hom ≫ shapeAssembly k D X N r n := by
  apply (cancel_epi (moduleFlatCoordinates k D X N r n).inv).mp
  rw [moduleFlatCoordinates_inv_flatEmbedding, Iso.inv_hom_id_assoc]
end DerivedBar.ParityBridge

end

end OAI
