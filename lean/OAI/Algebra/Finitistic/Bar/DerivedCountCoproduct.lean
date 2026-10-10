import OAI.Algebra.Finitistic.Bar.CountProjective
import OAI.Algebra.Finitistic.Bar.KProjectiveCoproduct
import OAI.Algebra.Finitistic.Bar.ExtensionColimits

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
noncomputable section
namespace DerivedBar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
  (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)
local instance derivedCountCoproductHasDerivedCategory :
    HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
local notation "S" => SquareZero.twoSidedWeightComplex k D X N hN

/-- The original count direct sum, with its original inclusions, is an actual
coproduct after passing to the genuine integer derived category. -/
def derivedCountCoproductIsColimit :
    IsColimit ((integerQ D).mapCocone (directSumComplexCocone D S)) := by
  letI : PreservesColimit (Discrete.functor S) (integerExtension D) :=
    extensionPreservesColimit ComplexShape.embeddingDownNat (Discrete.functor S)
  let s := (integerExtension D).mapCocone (directSumComplexCocone D S)
  let hs := isColimitOfPreserves (integerExtension D) (directSumComplexIsColimit D S)
  letI : s.pt.IsKProjective := integerCountSum_isKProjective k D X N hN
  letI (r : Discrete ℕ) : (((Discrete.functor S) ⋙ integerExtension D).obj r).IsKProjective :=
    integerCount_isKProjective k D X N hN r.as
  exact kProjectiveCoproductIsColimit ((Discrete.functor S) ⋙ integerExtension D) s hs
end DerivedBar

end

end OAI
