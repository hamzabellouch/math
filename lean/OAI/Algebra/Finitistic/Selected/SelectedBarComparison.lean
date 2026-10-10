import OAI.Algebra.Finitistic.Selected.SelectedBarBimodule
import OAI.Algebra.Finitistic.Bar.BarBimoduleCongruence
import OAI.Algebra.Finitistic.Bimodule.BimoduleResolutionBarAPI
import OAI.Algebra.Finitistic.Selected.SelectedBarStart

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace LittleFinitistic.SelectedBarComparison
open SelectedOrdinaryAlgebra SelectedBarBimodule
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The actual fixed resolution supplies every generic native/bar premise. -/
def resolution := BimoduleTotal.ofNonpositiveResolution
  SelectedOrdinaryResolution.complex SelectedOrdinaryResolution.target length
  SelectedOrdinaryResolution.augmentation SelectedOrdinaryResolution.augmentation_quasiIso
  (fun n => SelectedOrdinaryResolution.right_projective n) SelectedOrdinaryResolution.bounded

/-- The native finite-interval presentation of tensor by the actual Q_X. Its
comparison to the ordinary total presentation is proved separately. -/
abbrev native := resolution.data.derived

/-- The native tensor of the actual Q_X agrees naturally with bar-derived
 tensor by the ORIGINAL X, with no remaining augmentation or action premise. -/
def naturalIso : DerivedBar.chainToIntegerDerived D ⋙ native ≅
    DerivedBar.derivedTensor ℂ D X ⋙ DerivedBar.chainToIntegerDerived D :=
  BimoduleTotal.nonpositiveResolutionBarIso
    SelectedOrdinaryResolution.complex SelectedOrdinaryResolution.target length
    SelectedOrdinaryResolution.augmentation SelectedOrdinaryResolution.augmentation_quasiIso
    (fun n => SelectedOrdinaryResolution.right_projective n) SelectedOrdinaryResolution.bounded ≪≫
  isoWhiskerRight (DerivedBar.BimoduleTensor.derivedTensorCongr ℂ D leftEquiv right_action)
    (DerivedBar.chainToIntegerDerived D)

/-- Every actual native iterate on a stalk is the original-X bar-derived iterate. -/
def powerIso (N : ModuleCat.{0} D) (r : ℕ) :
    (native.obj^[r]) (DerivedCategory.Q.obj (BimoduleTotal.singleInput D N)) ≅
      DerivedBar.IterateSupport.object ℂ D X N r :=
  BimoduleTotal.nonpositiveResolutionPowerIso
    SelectedOrdinaryResolution.complex SelectedOrdinaryResolution.target length
    SelectedOrdinaryResolution.augmentation SelectedOrdinaryResolution.augmentation_quasiIso
    (fun n => SelectedOrdinaryResolution.right_projective n) SelectedOrdinaryResolution.bounded N r ≪≫
  (DerivedBar.integerDerivedIterateIndexedIso D ℂ comparisonX N r).symm ≪≫
  (DerivedBar.chainToIntegerDerived D).mapIso
    ((DerivedBar.BimoduleTensor.derivedIterateCongr ℂ D leftEquiv right_action r).app
      ((DerivedBar.chainQ D).obj ((ChainComplex.single₀ (ModuleCat D)).obj N)))
end LittleFinitistic.SelectedBarComparison

end

end OAI
