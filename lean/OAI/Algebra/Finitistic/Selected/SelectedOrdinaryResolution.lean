import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryAlgebra
import OAI.Algebra.Finitistic.Ordinary.OrdinaryXDerivedTensor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryResolution
open SelectedOrdinaryAlgebra

/-- The one fixed genuine D-bimodule resolution Q_X used by the source. -/
abbrev complex := OrdinarySimulation.XResolution.complex SelectedRectification.bimodule a length
abbrev target := OrdinarySimulation.XResolution.ordinaryXObject SelectedRectification.bimodule a length
abbrev augmentation := OrdinarySimulation.XResolution.augmentationToX
  SelectedRectification.bimodule a length

theorem augmentation_quasiIso : QuasiIso augmentation :=
  OrdinarySimulation.XResolution.augmentationToX_quasiIso SelectedRectification.bimodule a length

theorem right_projective (n : ℤ) : Module.Projective Dᵐᵒᵖ
    (BimoduleCoefficients ℂ D D (complex.X n)) :=
  OrdinarySimulation.XResolution.right_projective SelectedRectification.bimodule a length n

theorem bounded (n : ℤ) (hn : n < -(length : ℤ) ∨ 0 < n) : IsZero (complex.X n) :=
  OrdinarySimulation.XResolution.vanishes SelectedRectification.bimodule a length n hn

local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Tensor via the actual bounded right-projective Q_X, with the left D-action retained. -/
abbrev derived := OrdinarySimulation.XResolution.derivedTensor SelectedRectification.bimodule a length
abbrev comparison := OrdinarySimulation.XResolution.derivedTensorComparison
  SelectedRectification.bimodule a length
end LittleFinitistic.SelectedOrdinaryResolution

end

end OAI
