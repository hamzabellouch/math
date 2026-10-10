import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftedPresentation
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFirstDerivedRetraction
import OAI.Algebra.Finitistic.Ordinary.OrdinaryDerivedIterates
import OAI.Algebra.Finitistic.Selected.SelectedShiftedRealization
import OAI.Algebra.Finitistic.Selected.SelectedBarPowers
import OAI.Algebra.Finitistic.Iteration.FunctorObjectIteration

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.SelectedOrdinaryOrbit
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
local instance : HasDerivedCategory.{1} (ModuleCat.{0} (B P)) :=
  HasDerivedCategory.standard (ModuleCat.{0} (B P))

abbrev first := BlockModule.derivedFirst (B P) ((B P) ⊗[ℂ] OrdinarySimulation.ChainAlgebra ℂ length)
abbrev ordinary := SelectedOrdinaryResolution.derived

/-- The source's first-block localization is the actual selected exact inflation. -/
def firstIso : first ≅ SelectedFirstBlockFamily.derivedInflation :=
  BlockModule.derivedFirstIso (B P) ((B P) ⊗[ℂ] OrdinarySimulation.ChainAlgebra ℂ length)

def firstStalk (Y : FiniteSelectionFamily.S.{0}) :
    first.obj (FiniteSelectionFamily.derived Y) ≅ SelectedFirstBlockFamily.derived Y :=
  firstIso.app _ ≪≫ SelectedFirstBlockFamily.stalkIso Y

local instance resolution_projective : ∀ n, Module.Projective Dᵐᵒᵖ
    (ComplexTensor.rightTerm ℂ D (BimoduleTotal.right ℂ D SelectedOrdinaryResolution.complex) n) :=
  fun n => SelectedOrdinaryResolution.right_projective n

/-- Both tensor presentations use the identical Q_X and signed finite total. -/
def nativeIso : ordinary ≅ SelectedBarComparison.native :=
  BimoduleTotalPresentation.boundedNonpositiveDerivedIso ℂ D SelectedOrdinaryResolution.complex
    SelectedBarComparison.resolution.data length rfl rfl

/-- The source's shifted P[b] tensor is the concrete selecting shifted model. -/
def shiftedIso : OrdinarySimulation.shiftedDerivedTensor SelectedRectification.bimodule b length ≅
    SelectedShiftedRealization.G :=
  BimoduleTotalPresentation.shiftedDerivedIso SelectedRectification.bimodule b length
    SelectedShiftedRealization.model rfl rfl

/-- Every ordinary iterate on the selected first-block stalk is the original bar iterate. -/
def barPower (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (ordinary.obj^[r]) (SelectedFirstBlockFamily.derived Y) ≅ SelectedBaseIterates.object Y r :=
  functorObjectIteration nativeIso r _ ≪≫ SelectedBarPowers.comparison Y r

/-- Exact Section 5 even-iteration formula, with both presentation distinctions discharged. -/
def evenIteration (Y : FiniteSelectionFamily.S.{0}) (j : ℕ) :
    SelectedBaseIterates.object Y (2*j) ≅
      first.obj ((SelectedShiftedRealization.G.obj^[j]) (FiniteSelectionFamily.derived Y)) :=
  (barPower Y (2*j)).symm ≪≫ mapObjectIteration ordinary (firstStalk Y).symm (2*j) ≪≫
    OrdinarySimulation.XResolution.derivedEvenIterate SelectedRectification.bimodule a length b
      endpoints support j (FiniteSelectionFamily.derived Y) ≪≫
    first.mapIso (functorObjectIteration shiftedIso j _)

/-- Every even original-X iterate is zero exactly at the original selection stopping time. -/
theorem isZero_iff (Y : FiniteSelectionFamily.S.{0}) (j : ℕ) :
    IsZero (SelectedBaseIterates.object Y (2*j)) ↔ Subsingleton (selectionIterate Y.val j) :=
  (evenIteration Y j).isZero_iff.trans
    ((BlockModule.derivedFirst_isZero_iff (B P)
      ((B P) ⊗[ℂ] OrdinarySimulation.ChainAlgebra ℂ length) _).trans
        (SelectedShiftedRealization.isZero_iff j Y))

/-- Actual extinction/survival pair required by the main theorem, on one fixed A. -/
theorem extinction (m : ℕ) [NeZero m] :
    IsZero (SelectedBaseIterates.object (FiniteSelectionFamily.test m) (2*m)) ∧
      ¬ IsZero (SelectedBaseIterates.object (FiniteSelectionFamily.test m) (2*m-2)) := by
  constructor
  · exact (isZero_iff (FiniteSelectionFamily.test m) m).mpr (selectionIterate_test_subsingleton m)
  · have hm := NeZero.pos m
    have he : 2*m-2 = 2*(m-1) := by omega
    rw [he]
    intro hz
    exact @not_subsingleton _ (selectionIterate_test_nontrivial m (m-1) (by omega))
      ((isZero_iff (FiniteSelectionFamily.test m) (m-1)).mp hz)
end LittleFinitistic.SelectedOrdinaryOrbit

end

end OAI
