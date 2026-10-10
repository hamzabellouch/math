import OAI.Algebra.Finitistic.Bar.ResolutionDerived
import OAI.Algebra.Finitistic.Bar.TotalBarComparison

namespace OAI
open CategoryTheory CategoryTheory.Functor HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
local notation "c" => ComplexShape.down ℕ

abbrev chainQuasiIso := HomologicalComplex.quasiIso (ModuleCat.{u} D) c
abbrev chainDerived := (chainQuasiIso D).Localization
abbrev chainQ : ChainComplex (ModuleCat.{u} D) ℕ ⥤ chainDerived D := (chainQuasiIso D).Q

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Ordinary balanced tensor on chains followed by the quasi-isomorphism localization. -/
def ordinaryTensorToDerived : ChainComplex (ModuleCat.{u} D) ℕ ⥤ chainDerived D :=
  (BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex c ⋙ chainQ D

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
theorem tensorTotal_inverts : (chainQuasiIso D).IsInvertedBy
    (tensorTotalFunctor k D X ⋙ chainQ D) := by
  intro Z U f hf
  have : QuasiIso f := hf
  exact Localization.inverts (chainQ D) (chainQuasiIso D) _
    (show QuasiIso ((tensorTotalFunctor k D X).map f) from inferInstance)

/-- Left derived balanced tensor on the localization of nonnegative chain complexes. -/
def derivedTensor : chainDerived D ⥤ chainDerived D :=
  Localization.lift (tensorTotalFunctor k D X ⋙ chainQ D)
    (tensorTotal_inverts k D X) (chainQ D)

def derivedTensorResolutionIso : chainQ D ⋙ derivedTensor k D X ≅
    barTotalFunctor k D ⋙ ordinaryTensorToDerived k D X :=
  Localization.fac (tensorTotalFunctor k D X ⋙ chainQ D)
    (tensorTotal_inverts k D X) (chainQ D)

def derivedTensorCounit : chainQ D ⋙ derivedTensor k D X ⟶ ordinaryTensorToDerived k D X :=
  (derivedTensorResolutionIso k D X).hom ≫
    whiskerRight (barTotalAugmentationNat k D) (ordinaryTensorToDerived k D X)

/-- The constructed tensor functor satisfies mathlib's genuine left-derived
universal property, proved using the projective total bar and its augmentation. -/
instance derivedTensor_isLeftDerivedFunctor :
    (derivedTensor k D X).IsLeftDerivedFunctor (derivedTensorCounit k D X) (chainQuasiIso D) := by
  apply isLeftDerivedFunctor_of_resolution (chainQuasiIso D) (chainQ D)
    (barTotalFunctor k D) (barTotalAugmentationNat k D)
    (fun Z => (show QuasiIso (barTotalAugmentation k D Z) from inferInstance))
    (ordinaryTensorToDerived k D X) (derivedTensor k D X)
    (derivedTensorResolutionIso k D X) (derivedTensorCounit k D X) rfl
  intro Z
  let : ∀ n, Projective (((barTotalFunctor k D).obj Z).X n) := barTotal_projective k D Z
  have ht : QuasiIso
      (((BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex c).map
        (barTotalAugmentation k D ((barTotalFunctor k D).obj Z))) := inferInstance
  have hi := Localization.inverts (chainQ D) (chainQuasiIso D) _ ht
  exact IsIso.comp_isIso' inferInstance hi


/-- The explicit two-sided total represents the genuine derived tensor of the input. -/
def derivedTensorExplicitIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    (derivedTensor k D X).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (BimoduleTensor.explicitBarTotal k D X Z) :=
  (derivedTensorResolutionIso k D X).app Z ≪≫
    (chainQ D).mapIso (BimoduleTensor.tensorTotalExplicitIso k D X Z)

/-- Genuine derived functor iteration, with the manuscript's right-to-left order. -/
def derivedTensorIterate : ℕ → (chainDerived D ⥤ chainDerived D)
  | 0 => 𝟭 _
  | r+1 => derivedTensorIterate r ⋙ derivedTensor k D X

/-- Successive resolve-and-tensor complexes represent iteration of the genuine
left derived functor. No derived comparison is included as a hypothesis. -/
def derivedTensorIterateIso : (r : ℕ) →
    chainQ D ⋙ derivedTensorIterate k D X r ≅ tensorTotalIterate k D X r ⋙ chainQ D
  | 0 => (Functor.rightUnitor _ ) ≪≫ (Functor.leftUnitor _).symm
  | r+1 =>
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (derivedTensorIterateIso r) (derivedTensor k D X) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (tensorTotalIterate k D X r) (derivedTensorResolutionIso k D X) ≪≫
      (Functor.associator _ _ _).symm

/-- The independent recursive multibar. Every new block uses the explicit
endpoint-minus-tail horizontal differential and the standard vertical total sign. -/
def explicitMultibar : ℕ → ChainComplex (ModuleCat.{u} D) ℕ → ChainComplex (ModuleCat.{u} D) ℕ
  | 0, Z => Z
  | r+1, Z => BimoduleTensor.explicitBarTotal k D X (explicitMultibar r Z)

def iterateExplicitMultibarIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) : (r : ℕ) →
    (tensorTotalIterate k D X r).obj Z ≅ explicitMultibar k D X r Z
  | 0 => Iso.refl _
  | r+1 => (tensorTotalFunctor k D X).mapIso (iterateExplicitMultibarIso Z r) ≪≫
      BimoduleTensor.tensorTotalExplicitIso k D X (explicitMultibar k D X r Z)

/-- The independent recursive multibar represents genuine finite derived iteration. -/
def derivedIterateMultibarIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (explicitMultibar k D X r Z) :=
  (derivedTensorIterateIso k D X r).app Z ≪≫
    (chainQ D).mapIso (iterateExplicitMultibarIso k D X Z r)

/-- The final leading D-bar resolution leaves the represented derived iterate unchanged. -/
def derivedIterateLeadingBarIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    (derivedTensorIterate k D X r).obj ((chainQ D).obj Z) ≅
      (chainQ D).obj (barTotal k D (explicitMultibar k D X r Z)) := by
  have := Localization.inverts (chainQ D) (chainQuasiIso D)
    (barTotalAugmentation k D (explicitMultibar k D X r Z))
    (show QuasiIso (barTotalAugmentation k D (explicitMultibar k D X r Z)) from inferInstance)
  exact derivedIterateMultibarIso k D X Z r ≪≫
    (asIso ((chainQ D).map (barTotalAugmentation k D (explicitMultibar k D X r Z)))).symm
end DerivedBar

end

end OAI
