import OAI.Algebra.Finitistic.Bimodule.BoundedBimoduleDerived
import OAI.Algebra.Finitistic.Bimodule.BimoduleLeftNaturality
import OAI.Algebra.Finitistic.Bar.IntegerDerivedMultibar

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
variable {P : BiComplex k B} (data : BoundedProjective k B P)

abbrev integerTotalFunctor := DerivedBar.integerExtension B ⋙
  functor k B P data.degrees (intervalDegrees_strictMono data.lower data.upper) ⋙ DerivedCategory.Q

/-- The original bar augmentation, followed by the fixed finite bimodule total. -/
def barInputAugmentation : DerivedBar.barTotalFunctor k B ⋙ integerTotalFunctor data ⟶
    integerTotalFunctor data :=
  Functor.whiskerRight (DerivedBar.barTotalAugmentationNat k B) (integerTotalFunctor data)

/-- The left leg of the actual comparison zigzag is invertible for every chain input. -/
instance barInputAugmentation_isIso : IsIso (barInputAugmentation data) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  let : ∀ i, Module.Projective Bᵐᵒᵖ
      (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  let ε := (DerivedBar.integerExtension B).map (DerivedBar.barTotalAugmentation k B Z)
  have : QuasiIso ε := inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (DerivedBar.barTotalAugmentation k B Z)
      ComplexShape.embeddingDownNat))
  have := totalMap_quasiIso k B P data.degrees
    (intervalDegrees_strictMono data.lower data.upper) ε
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (totalMap k B P data.degrees (intervalDegrees_strictMono data.lower data.upper) ε)))

/-- The native derived tensor of the integer extension is computed on its genuine
projective bar resolution, with no hypothesis on the input's terms. -/
def nativeBarResolutionIso : DerivedBar.integerQ B ⋙ data.derived ≅
    DerivedBar.barTotalFunctor k B ⋙ integerTotalFunctor data :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedBar.integerExtension B) data.comparison ≪≫
    (asIso (barInputAugmentation data)).symm

/-- The same comparison written using the native chain-localization inclusion. -/
def nativeChainBarResolutionIso :
    DerivedBar.chainQ B ⋙ (DerivedBar.chainToIntegerDerived B ⋙ data.derived) ≅
      DerivedBar.barTotalFunctor k B ⋙ integerTotalFunctor data :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedBar.chainToIntegerDerivedIso B) data.derived ≪≫
    nativeBarResolutionIso data
end LittleFinitistic.BimoduleTotal

end

end OAI
