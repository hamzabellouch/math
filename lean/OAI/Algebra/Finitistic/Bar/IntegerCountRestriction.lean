import OAI.Algebra.Finitistic.Bar.GlobalIndexedComparison
import OAI.Algebra.Finitistic.Bar.IntegerDerivedMultibar
import OAI.Algebra.Finitistic.Bar.StrictSupportExtension

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt HomologicalComplex
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance integerCountRestrictionScalarModule (V : ModuleCat D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance integerCountRestrictionScalarTower (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance integerCountRestrictionIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance integerCountRestrictionShapeDecidableEq (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance integerCountRestrictionInflatedModule : Module A N := inflatedModule D X N
local instance integerCountRestrictionInflatedScalarTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

local notation "C" => ModuleCat D
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

/-- The actual integer cochain count complex shifted by -r. -/
def deshiftedCount (r : ℕ) : CochainComplex C ℤ :=
  ((integerExtension D).obj (K r))⟦-(r:ℤ)⟧

def deshiftedCountRestriction (r : ℕ) : ChainComplex C ℕ :=
  (deshiftedCount k D X N r).restriction E

def deshiftedCountXIso (r n : ℕ) : (deshiftedCountRestriction k D X N r).X n ≅
    indexedModule k D X N r n :=
  (K r).extendXIso E
    (show (E).f (r+n) = (E).f n + -(r:ℤ) by change -((r+n:ℕ):ℤ) = -(n:ℤ) + -(r:ℤ); push_cast; omega)

theorem units_hom_apply (V W : ModuleCat.{u} D) (s : ℤˣ) (f : V ⟶ W) (v : V) :
    (s • f).hom v = s • f.hom v := by
  change ((s:ℤ) • f).hom v = (s:ℤ) • f.hom v
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]

/-- The standard unit-valued cochain shift sign is the proved count sign. -/
theorem deshiftedCount_sign (r n : ℕ) :
    (-(r:ℤ)).negOnePow • (K r).d (r+(n+1)) (r+n) = indexedDifferential k D X N r n := by
  have hd : (K r).d (r+(n+1)) (r+n) =
      ModuleCat.ofHom (Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r) := by
    change ChainComplex.of.d
      (fun m => ModuleCat.of D (⨁ p : Multibar.Indexed.Shape m r, Multibar.Indexed.outerTensor k D X N p))
      (fun m => ModuleCat.ofHom (Multibar.Indexed.blockDifferential k D X N
        (inflated_ideal_zero D X N) m r)) ((r+n)+1) (r+n) = _
    exact ChainComplex.of_d _ _ (r+n)
  rw [hd]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  erw [units_hom_apply]
  erw [globalIndexedComparison]
  change (-(r:ℤ)).negOnePow •
      Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r v =
    (-1:k)^r •
      Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r v
  have hu : (r:ℤ).negOnePow = (-1:ℤˣ)^r := by
    apply Units.ext
    simpa using Int.coe_negOnePow_natCast r
  rw [Int.negOnePow_neg, hu]
  exact totalSign_smul k (⨁ p : Multibar.Indexed.Shape (r+n) r, Multibar.Indexed.outerTensor k D X N p) r
    (Multibar.Indexed.blockDifferential k D X N (inflated_ideal_zero D X N) (r+n) r v)

theorem deshiftedCount_d (r n : ℕ) :
    (deshiftedCountRestriction k D X N r).d (n+1) n =
      (deshiftedCountXIso k D X N r (n+1)).hom ≫ indexedDifferential k D X N r n ≫
        (deshiftedCountXIso k D X N r n).inv := by
  change (-(r:ℤ)).negOnePow • ((K r).extend E).d ((E).f (n+1) + -(r:ℤ)) ((E).f n + -(r:ℤ)) = _
  rw [extend_d_eq (K r) E
    (show (E).f (r+(n+1))=(E).f (n+1) + -(r:ℤ) by change -((r+(n+1):ℕ):ℤ) = -((n+1:ℕ):ℤ) + -(r:ℤ); push_cast; omega)
    (show (E).f (r+n)=(E).f n + -(r:ℤ) by change -((r+n:ℕ):ℤ) = -(n:ℤ) + -(r:ℤ); push_cast; omega)]
  rw [← deshiftedCount_sign]
  erw [CategoryTheory.Linear.units_smul_comp, CategoryTheory.Linear.comp_units_smul]
  rfl

/-- A genuine chain isomorphism using the standard integer shift differential,
not a newly stipulated shift or transported count differential. -/
def indexedDeshiftedCountIso (r : ℕ) : indexedMultibar k D X N r ≅
    deshiftedCountRestriction k D X N r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (deshiftedCountXIso k D X N r n).symm) (by
      intro i j hij
      change j+1=i at hij
      subst i
      rw [deshiftedCount_d]
      simp only [Iso.symm_hom]
      erw [Iso.inv_hom_id_assoc]
      simp only [indexedMultibar, ChainComplex.of_d])
end DerivedBar.ParityBridge

end

end OAI
