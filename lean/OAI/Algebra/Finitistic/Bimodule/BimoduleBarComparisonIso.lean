import OAI.Algebra.Finitistic.Bimodule.BimoduleBarComparisonMap
import OAI.Algebra.Finitistic.Bimodule.BimoduleAugmentationQuasiIso

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

/-- The original augmentation, evaluated on the actual free bar resolution,
becomes an isomorphism in the integer derived category. -/
instance resolvedTensorAugmentation_isIso : IsIso
    (whiskerLeft (DerivedBar.barTotalFunctor k B)
      (whiskerLeft (DerivedBar.integerExtension B)
        (whiskerRight res.tensorAugmentation DerivedCategory.Q))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  let : ∀ n, Projective ((DerivedBar.barTotal k B Z).X n) :=
    DerivedBar.barTotal_projective k B Z
  let Z' := (DerivedBar.integerExtension B).obj (DerivedBar.barTotal k B Z)
  have : ∀ n, Projective (Z'.X n) := by
    intro n
    exact inferInstanceAs (Projective
      (((DerivedBar.barTotal k B Z).extend ComplexShape.embeddingDownNat).X n))
  have := augmentation_total_quasiIso res Z'
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (leftTotalMap res.augmentation Z' res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper))))

instance augmentationComparisonOnChains_isIso :
    IsIso (augmentationComparisonOnChains res i₀ hi₀) := by
  unfold augmentationComparisonOnChains
  infer_instance

/-- Natural identification of the native D(B-Mod) tensor by the actual bounded
right-projective bimodule resolution and DerivedBar's genuine localized tensor,
after chainToIntegerDerived. Both outside module actions are retained. -/
def nativeBarIso :
    DerivedBar.chainToIntegerDerived B ⋙ res.data.derived ≅
      DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B :=
  (Localization.fullyFaithfulWhiskeringLeft (DerivedBar.chainQ B)
    (DerivedBar.chainQuasiIso B) (DerivedCategory (ModuleCat.{u} B))).preimageIso
      (asIso (augmentationComparisonOnChains res i₀ hi₀))

/-- This isomorphism uses precisely the original augmentation-induced map. -/
theorem nativeBarIso_hom : (nativeBarIso res i₀ hi₀).hom = augmentationComparison res i₀ hi₀ := rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
