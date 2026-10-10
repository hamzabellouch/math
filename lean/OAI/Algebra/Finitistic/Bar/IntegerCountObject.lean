import OAI.Algebra.Finitistic.Bar.DerivedCountShift

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
local instance integerCountScalarModule (V : ModuleCat D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance integerCountScalarTower (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance integerCountIndexDecidableEq (r n : ℕ) : DecidableEq (Index r n) :=
  Classical.decEq _
local instance integerCountShapeDecidableEq (n r : ℕ) :
    DecidableEq (Multibar.Indexed.Shape n r) := Classical.decEq _
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance integerCountInflatedModule : Module A N := inflatedModule D X N
local instance integerCountInflatedScalarTower : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

local notation "C" => ModuleCat D
local notation "E" => ComplexShape.embeddingDownNat
local notation "K" => Multibar.Indexed.signedBlockComplex k D X N (inflated_ideal_zero D X N)

/-- The original r-count object, with exactly the original scalar and inflated actions. -/
abbrev countObject (r : ℕ) :=
  (integerQ D).obj (SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N) r)

local instance integerCountHasDerivedCategory : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- The proved genuine shift comparison, with its target named for downstream use. -/
def countObjectComparison (r : ℕ) :
    ((chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)))⟦(r:ℤ)⟧ ≅ countObject k D X N r :=
  derivedIterateWeightShiftIso k D X N r
end DerivedBar.ParityBridge

end

end OAI
