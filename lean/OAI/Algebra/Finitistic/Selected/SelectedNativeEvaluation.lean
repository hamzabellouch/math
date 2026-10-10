import OAI.Algebra.Finitistic.Selected.SelectedDiagramEvaluation
import OAI.Algebra.Finitistic.Selected.SelectedImageComparison

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedNativeEvaluation
open QuadraticEncoding SourceImageEvaluation FiniteProjectiveHomotopy SelectedFixedDiagram
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]

abbrev H := complexObject (selectionStep (ModuleCat.of SelectionRing Y))
instance : FiniteDimensional ℂ (H (Y := Y)) :=
  Module.Finite.of_surjective (SelectedImageComparison.equiv (Y := Y)).toLinearMap
    (SelectedImageComparison.equiv (Y := Y)).surjective

def HK : K.{0,v} ℂ := ⟨(vectorStalk (k := ℂ)).obj (H (Y := Y)), single_property _ 0⟩
def HDerived : FiniteVectorDerived.{0,v} (k := ℂ) :=
  (derivedEmbedding ℂ).toEssImage.obj (HK (Y := Y))
def imageIsoK : imageK (k := ℂ) (Y := Y) e ≅ HK (Y := Y) :=
  (inclusion ℂ).preimageIso ((vectorStalk (k := ℂ)).mapIso
    (SelectedImageComparison.equiv (Y := Y)).toModuleIso)
def imageIso : imageDerived (k := ℂ) (Y := Y) e ≅ HDerived (Y := Y) :=
  (derivedEmbedding ℂ).toEssImage.mapIso (imageIsoK (Y := Y))

/-- The actual primary H(Y), concentrated in degree zero, and its shift by three. -/
abbrev target := HDerived (Y := Y) ⊞ (HDerived (Y := Y))⟦(3 : ℤ)⟧
def targetIso : SelectedDiagramEvaluation.target (Y := Y) ≅ target (Y := Y) :=
  biprod.mapIso (imageIso (Y := Y))
    ((shiftFunctor (FiniteVectorDerived.{0,v} (k := ℂ)) (3 : ℤ)).mapIso (imageIso (Y := Y)))

def V0Iso : (SelectedDiagramEvaluation.F (Y := Y)).obj fixed.V0 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.V0Iso ≪≫ targetIso

def D0Iso : (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).obj fixed.D0 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.D0Iso ≪≫ targetIso
def D1Iso : (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).obj fixed.D1 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.D1Iso ≪≫ targetIso
def D2Iso : (SelectedDiagramEvaluation.sourceEvaluation (Y := Y)).obj fixed.D2 ≅ target (Y := Y) :=
  SelectedDiagramEvaluation.D2Iso ≪≫ targetIso
end LittleFinitistic.SelectedNativeEvaluation

end

end OAI
