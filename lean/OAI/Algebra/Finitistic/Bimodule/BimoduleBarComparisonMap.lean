import OAI.Algebra.Finitistic.Bimodule.BimoduleStalkTotal
import OAI.Algebra.Finitistic.Bimodule.BimoduleBarTensorComparison
import OAI.Algebra.Finitistic.Localization.IntegerExtensionFunctor

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

abbrev barModule := BimoduleBarComparison.Actions k B X
abbrev actualBarFunctor := DerivedBar.BimoduleTensor.tensorFunctor k B (barModule (X := X))

/-- The stalk total on extended chains agrees with the exact tensor functor used by DerivedBar. -/
def stalkChainIso : DerivedBar.integerExtension B ⋙
    functor k B (bimoduleStalk k B X) res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) ≅
    (actualBarFunctor (X := X)).mapHomologicalComplex (.down ℕ) ⋙ DerivedBar.integerExtension B :=
  isoWhiskerLeft (DerivedBar.integerExtension B)
    (stalkTotalIso k B X res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) i₀ hi₀) ≪≫
  isoWhiskerLeft (DerivedBar.integerExtension B)
    (NatIso.mapHomologicalComplex (BimoduleBarComparison.tensorFunctorIso k B X) (.up ℤ)) ≪≫
  IntegerExtensionFunctor.naturalIso (actualBarFunctor (X := X))

def resolvedStalkIso :
    DerivedBar.barTotalFunctor k B ⋙ DerivedBar.integerExtension B ⋙
      functor k B (bimoduleStalk k B X) res.data.degrees
        (intervalDegrees_strictMono res.data.lower res.data.upper) ⋙ DerivedCategory.Q ≅
    DerivedBar.tensorTotalFunctor k B (barModule (X := X)) ⋙ DerivedBar.integerQ B :=
  isoWhiskerLeft (DerivedBar.barTotalFunctor k B)
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (stalkChainIso res i₀ hi₀) DerivedCategory.Q ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The native bar functor's defining localization comparisons, with integer extension. -/
def actualBarResolutionIso :
    DerivedBar.chainQ B ⋙
      (DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B) ≅
    DerivedBar.tensorTotalFunctor k B (barModule (X := X)) ⋙ DerivedBar.integerQ B :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedBar.derivedTensorResolutionIso k B (barModule (X := X)))
      (DerivedBar.chainToIntegerDerived B) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (DerivedBar.tensorTotalFunctor k B (barModule (X := X)))
      (DerivedBar.chainToIntegerDerivedIso B)

/-- Actual comparison induced by the actual bimodule augmentation, before
localization descent. Invertibility is a separate finite-total proof obligation. -/
def augmentationComparisonOnChains :
    DerivedBar.chainQ B ⋙ (DerivedBar.chainToIntegerDerived B ⋙ res.data.derived) ⟶
    DerivedBar.chainQ B ⋙
      (DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B) :=
  (nativeChainBarResolutionIso res.data).hom ≫
    whiskerLeft (DerivedBar.barTotalFunctor k B)
      (whiskerLeft (DerivedBar.integerExtension B)
        (whiskerRight res.tensorAugmentation DerivedCategory.Q)) ≫
    (resolvedStalkIso res i₀ hi₀).hom ≫
    (actualBarResolutionIso (X := X)).inv

/-- The concrete augmentation comparison descends to the genuine chain localization.
This constructs a map; it does not assert the still-unproved isomorphism property. -/
def augmentationComparison :
    DerivedBar.chainToIntegerDerived B ⋙ res.data.derived ⟶
      DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedBar.chainQ B)
    (DerivedBar.chainQuasiIso B) (DerivedCategory (ModuleCat.{u} B))).preimage
      (augmentationComparisonOnChains res i₀ hi₀)

/-- Descent preserves the original comparison, rather than choosing an unrelated map. -/
theorem augmentationComparison_fac :
    whiskerLeft (DerivedBar.chainQ B) (augmentationComparison res i₀ hi₀) =
      augmentationComparisonOnChains res i₀ hi₀ :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedBar.chainQ B)
    (DerivedBar.chainQuasiIso B) (DerivedCategory (ModuleCat.{u} B))).map_preimage _
end LittleFinitistic.BimoduleTotal

end

end OAI
