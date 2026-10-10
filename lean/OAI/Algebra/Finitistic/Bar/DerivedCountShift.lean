import OAI.Algebra.Finitistic.Bar.IntegerCountShift

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance derivedCountShiftIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
local instance derivedCountShiftShapeDecidableEq (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

local notation "C" => ModuleCat D
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

/-- Identification with the original count subcomplex, using the actual integer
cochain shift and the already verified component sign involution. -/
def integerIndexedWeightShiftIso (r : ℕ) :
    ((integerExtension D).obj (indexedMultibar k D X N r))⟦(r:ℤ)⟧ ≅
      (integerExtension D).obj (SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N) r) :=
  integerIndexedCountShiftIso k D X N r ≪≫
    (integerExtension D).mapIso (Multibar.Indexed.signedBlockIso k D X N (inflated_ideal_zero D X N) r)

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- Each original count summand is the genuine [r] shift of the constructed
finite derived tensor iterate. -/
def derivedIterateWeightShiftIso (r : ℕ) :
    ((chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)))⟦(r:ℤ)⟧ ≅
    (integerQ D).obj (SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N) r) :=
  (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} D)) (r:ℤ)).mapIso
    (integerDerivedIterateIndexedIso D k X N r) ≪≫
      ((DerivedCategory.Q.commShiftIso (r:ℤ)).symm.app
        ((integerExtension D).obj (indexedMultibar k D X N r))) ≪≫
      DerivedCategory.Q.mapIso (integerIndexedWeightShiftIso k D X N r)
end DerivedBar.ParityBridge

end

end OAI
