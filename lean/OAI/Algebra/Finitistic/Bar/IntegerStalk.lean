import OAI.Algebra.Finitistic.Bar.IntegerDerivedMultibar

namespace OAI
noncomputable section
open CategoryTheory
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- The original nonnegative stalk maps to the actual integer derived stalk. -/
def integerStalkIso (N : ModuleCat.{u} D) :
    (integerQ D).obj ((ChainComplex.single₀ (ModuleCat D)).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat D) 0).obj N :=
  DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso
    ComplexShape.embeddingDownNat N 0 0 rfl) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat D) 0).app N).symm
end DerivedBar

end

end OAI
