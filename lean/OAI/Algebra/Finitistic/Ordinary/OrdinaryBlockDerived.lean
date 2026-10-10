import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockComplexes
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRestrictionHomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

abbrev firstComplexFunctor := (ProductModules.firstInflation L R).mapHomologicalComplex (.up ℤ)

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} L)] in
theorem first_inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} L) (.up ℤ)).IsInvertedBy
    (firstComplexFunctor L R ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  have : QuasiIso ((firstComplexFunctor L R).map f) :=
    (RestrictionHomology.quasiIso_iff (RingHom.fst L R) f).mpr inferInstance
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((firstComplexFunctor L R).map f)))

/-- Native derived inflation on the first block of the product algebra. -/
def derivedFirst : DerivedCategory (ModuleCat.{u} L) ⥤ DerivedCategory (ModuleCat.{u} (L × R)) :=
  Localization.lift (firstComplexFunctor L R ⋙ DerivedCategory.Q) (first_inverts L R) DerivedCategory.Q

def derivedFirstComparison : DerivedCategory.Q ⋙ derivedFirst L R ≅ firstComplexFunctor L R ⋙ DerivedCategory.Q :=
  Localization.fac (firstComplexFunctor L R ⋙ DerivedCategory.Q) (first_inverts L R) DerivedCategory.Q
end LittleFinitistic.BlockModule

end

end OAI
