import OAI.Algebra.Finitistic.Bar.DerivedBarCoproduct
import OAI.Algebra.Finitistic.Bar.BalancedTensorFunctor
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

namespace OAI
open CategoryTheory CategoryTheory.Limits TrivSqZeroExt
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]
local instance derivedTensorBarSplittingHasDerivedCategory :
    HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- Extension of the nonnegative homotopy category followed by the genuine
integer derived localization. -/
abbrev homotopyToIntegerDerived : HomotopyCategory (ModuleCat.{u} D) (.down ℕ) ⥤
    DerivedCategory (ModuleCat.{u} D) :=
  ComplexShape.embeddingDownNat.extendHomotopyFunctor (ModuleCat.{u} D) ⋙ DerivedCategory.Qh

def homotopyToIntegerDerivedIso (K : ChainComplex (ModuleCat.{u} D) ℕ) :
    (homotopyToIntegerDerived D).obj ((HomotopyCategory.quotient _ _).obj K) ≅
      (integerQ D).obj K :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{u} D)).app ((integerExtension D).obj K)

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [Algebra k D]
  (f : A →ₐ[k] D)

/-- The actual left-derived balanced base-change functor on modules, viewed
in the integer derived category. -/
abbrev derivedBaseChange : ModuleCat.{u} A ⥤ DerivedCategory (ModuleCat.{u} D) :=
  (Balanced.tensorFunctor f).leftDerivedToHomotopyCategory ⋙ homotopyToIntegerDerived D

def derivedBaseChangeBarIso (N : Type u) [AddCommGroup N] [Module k N]
    [Module A N] [IsScalarTower k A N] :
    (derivedBaseChange D f).obj (ModuleCat.of A N) ≅
      (integerQ D).obj (tensorBarComplex k A D N f) :=
  (homotopyToIntegerDerived D).mapIso (Balanced.tensorBarComputesLeftDerived f N) ≪≫
    homotopyToIntegerDerivedIso D _
end DerivedBar
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
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- The actual left-derived D tensor over A is the actual categorical
coproduct of genuine shifted derived iterates. This proves the manuscript's
bar-splitting proposition; projective-dimension detection is a separate result. -/
def derivedTensorBarSplitting :
    (derivedBaseChange D (fstHom k D X)).obj (ModuleCat.of A N) ≅
      colimit (shiftedIterateDiagram k D X N) :=
  derivedBaseChangeBarIso D (fstHom k D X) N ≪≫ derivedBarSplitting k D X N
end DerivedBar.ParityBridge

end

end OAI
