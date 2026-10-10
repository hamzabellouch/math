import OAI.Algebra.Finitistic.Bimodule.BimoduleBarComparisonIso

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
variable {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)
variable (i₀ : Fin ((res.data.upper-res.data.lower).toNat+1)) (hi₀ : res.data.degrees i₀=0)

/-- Iteration of the native full-left-action integer derived endofunctor. -/
def nativeIterate : ℕ → (DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B))
  | 0 => 𝟭 _
  | r+1 => nativeIterate r ⋙ res.data.derived

/-- The augmentation comparison iterates naturally on the genuine localized
chain category. This identifies actual derived functors, not only vector spaces. -/
def nativeBarIterateIso : (r : ℕ) →
    DerivedBar.chainToIntegerDerived B ⋙ nativeIterate res r ≅
      DerivedBar.derivedTensorIterate k B (barModule (X := X)) r ⋙ DerivedBar.chainToIntegerDerived B
  | 0 => (Functor.rightUnitor _) ≪≫ (Functor.leftUnitor _).symm
  | r+1 =>
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (nativeBarIterateIso r) res.data.derived ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (DerivedBar.derivedTensorIterate k B (barModule (X := X)) r)
        (nativeBarIso res i₀ hi₀) ≪≫
      (Functor.associator _ _ _).symm

/-- The native iterate on an extended chain input is the manuscript's actual
recursive bar total, with the endpoint-minus-tail and signed vertical differentials. -/
def nativeIterateMultibarIso (Z : ChainComplex (ModuleCat.{u} B) ℕ) (r : ℕ) :
    (nativeIterate res r).obj ((DerivedBar.integerQ B).obj Z) ≅
      (DerivedBar.integerQ B).obj (DerivedBar.explicitMultibar k B (barModule (X := X)) r Z) :=
  (nativeIterate res r).mapIso ((DerivedBar.chainToIntegerDerivedIso B).app Z).symm ≪≫
    (nativeBarIterateIso res i₀ hi₀ r).app ((DerivedBar.chainQ B).obj Z) ≪≫
    (DerivedBar.chainToIntegerDerived B).mapIso
      (DerivedBar.derivedIterateMultibarIso k B (barModule (X := X)) Z r) ≪≫
    (DerivedBar.chainToIntegerDerivedIso B).app _

/-- On degree-zero modules, the same native derived iteration is represented
by the actual Section 6 indexed multibar with all module actions retained. -/
def nativeIterateIndexedIso (N : ModuleCat.{u} B) (r : ℕ) :
    (nativeIterate res r).obj ((DerivedBar.integerQ B).obj ((ChainComplex.single₀ _).obj N)) ≅
      DerivedCategory.Q.obj ((DerivedBar.integerExtension B).obj
        (DerivedBar.RecursiveTotal.indexedMultibar k B (barModule (X := X)) N r)) :=
  (nativeIterate res r).mapIso
      ((DerivedBar.chainToIntegerDerivedIso B).app ((ChainComplex.single₀ _).obj N)).symm ≪≫
    (nativeBarIterateIso res i₀ hi₀ r).app ((DerivedBar.chainQ B).obj ((ChainComplex.single₀ _).obj N)) ≪≫
    DerivedBar.integerDerivedIterateIndexedIso B k (barModule (X := X)) N r
end LittleFinitistic.BimoduleTotal

end

end OAI
