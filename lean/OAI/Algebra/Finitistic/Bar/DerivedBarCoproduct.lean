import OAI.Algebra.Finitistic.Bar.DerivedCountCoproduct
import OAI.Algebra.Finitistic.Bar.TensorModel

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)

/-- The actual discrete diagram of genuine shifted finite derived tensor iterates. -/
def shiftedIterateDiagram : Discrete ℕ ⥤ DerivedCategory (ModuleCat.{u} D) :=
  Discrete.functor (fun r : ℕ =>
    ((chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)))⟦(r:ℤ)⟧)

def shiftedIterateCountIso : shiftedIterateDiagram k D X N ≅
    Discrete.functor S ⋙ integerQ D :=
  Discrete.natIso (fun r => derivedIterateWeightShiftIso k D X N r.as)

def shiftedIterateCocone : Cocone (shiftedIterateDiagram k D X N) :=
  (Cocone.precompose (shiftedIterateCountIso k D X N).hom).obj
    ((integerQ D).mapCocone (directSumComplexCocone D S))

/-- Both existence and uniqueness in the derived coproduct universal property
hold for the shifted iterates, without assuming a central splitting theorem. -/
def shiftedIterateIsColimit : IsColimit (shiftedIterateCocone k D X N) :=
  (IsColimit.precomposeHomEquiv (shiftedIterateCountIso k D X N) _).symm
    (derivedCountCoproductIsColimit k D X N (inflated_ideal_zero D X N))

instance hasColimitShiftedIterates : HasColimit (shiftedIterateDiagram k D X N) :=
  ⟨⟨_, shiftedIterateIsColimit k D X N⟩⟩

/-- Manuscript prop:bar-splitting, eq:bar-splitting: the balanced tensor of
D with the verified free A-bar resolution is isomorphic, in the genuine
integer derived category, to the actual coproduct of (F^r N)[r]. -/
def derivedBarSplitting :
    (integerQ D).obj (tensorBarComplex k A D N (fstHom k D X)) ≅
      colimit (shiftedIterateDiagram k D X N) :=
  (integerQ D).mapIso (SquareZero.tensorCountSplitting k D X N
    (inflated_ideal_zero D X N)) ≪≫
  (shiftedIterateIsColimit k D X N).coconePointUniqueUpToIso
    (colimit.isColimit (shiftedIterateDiagram k D X N))
end DerivedBar.ParityBridge

end

end OAI
