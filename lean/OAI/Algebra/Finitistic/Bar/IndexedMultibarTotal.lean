import OAI.Algebra.Finitistic.Bar.ModuleMultibarCoordinates

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
open DerivedBar.Multibar
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)
local notation "B" => leadingBarSequence k D X
local notation "F" => flatLeadingMultibar k D X Z

abbrev indexedModule (r n : ℕ) : ModuleCat.{u} D :=
  ModuleCat.of D (⨁ p : Multibar.Indexed.Shape (r+n) r,
    Multibar.Indexed.outerTensor k D X N p)

/-- The independently recursive multibar faces in the exact Shape coordinates.
This uses the horizontal/vertical differential of RecursiveTotal, not the count
complex differential. -/
def indexedDifferential (r n : ℕ) : indexedModule k D X N r (n+1) ⟶ indexedModule k D X N r n :=
  (moduleFlatCoordinates k D X N r (n+1)).inv ≫
    (F r).d (n+1) n ≫ (moduleFlatCoordinates k D X N r n).hom

theorem indexedDifferential_sq (r n : ℕ) :
    indexedDifferential k D X N r (n+1) ≫ indexedDifferential k D X N r n = 0 := by
  simp only [indexedDifferential, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((F r).d (n+2) (n+1)), HomologicalComplex.d_comp_d,
    zero_comp, comp_zero]

/-- Exact tensor-block coordinates, with the unshifted multibar total degree n. -/
def indexedMultibar (r : ℕ) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ChainComplex.of (indexedModule k D X N r) (indexedDifferential k D X N r)
    (indexedDifferential_sq k D X N r)

/-- Chain isomorphism from the exact tensor-block direct sum to the recursive flat model. -/
def indexedFlatIso (r : ℕ) : indexedMultibar k D X N r ≅ F r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleFlatCoordinates k D X N r n).symm)
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      change (moduleFlatCoordinates k D X N r (j+1)).inv ≫ (F r).d (j+1) j =
        (indexedMultibar k D X N r).d (j+1) j ≫ (moduleFlatCoordinates k D X N r j).inv
      simp only [indexedMultibar, ChainComplex.of_d, indexedDifferential,
        Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Actual chain isomorphism flattening the recursive leading total into the
same Shape-indexed block tensors as the square-zero count decomposition. -/
def indexedLeadingIso (r : ℕ) : indexedMultibar k D X N r ≅
    barTotal k D (explicitMultibar k D X r Z) :=
  indexedFlatIso k D X N r ≪≫ flatLeadingMultibarIso k D X Z r

/-- Exact signed differential formula on a recursive generator, now in the
literal Shape-indexed block coordinates. The vertical face includes (-1)^i. -/
theorem indexedDifferential_on_generator (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    lof (B r) Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩ ≫
      (moduleFlatCoordinates k D X N r (n+1)).hom ≫ indexedDifferential k D X N r n =
    (horizontal (B r) Z r n i q h t +
      vertical (B r) Z r n i q h t (differential (B r) Z r)) ≫
        (moduleFlatCoordinates k D X N r n).hom := by
  dsimp only [indexedDifferential]
  erw [Iso.hom_inv_id_assoc]
  simp only [flatLeadingMultibar, flatComplex, ChainComplex.of_d]
  change lof (B r) Z (r+1) (n+1) _ ≫ differential (B r) Z (r+1) n ≫ _ = _
  rw [lof_differential_succ_assoc]
  rfl

/-- Genuine derived tensor iteration represented by the exact indexed block
complex. No count splitting or projective-dimension statement is assumed. -/
def derivedIterateIndexedIso (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (indexedMultibar k D X N r) :=
  derivedIterateFlatIso k D X Z r ≪≫ (chainQ D).mapIso (indexedFlatIso k D X N r).symm
end DerivedBar.RecursiveTotal

end

end OAI
