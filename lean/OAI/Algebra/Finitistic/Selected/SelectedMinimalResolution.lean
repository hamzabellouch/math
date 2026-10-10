import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryModules
import OAI.Algebra.Finitistic.Dimension.PDDimension

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedMinimalResolution
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

abbrev finiteModule (Y : FiniteSelectionFamily.S.{0}) : PDMinimal.FiniteModule ℂ A :=
  PDMinimal.FiniteModule.of (Inflated Y)

/-- A genuine minimal projective resolution of each actual constructed A-module. -/
def resolution (Y : FiniteSelectionFamily.S.{0}) : ProjectiveResolution (SelectedOrdinaryModules.module Y) :=
  PDMinimal.resolution (finiteModule Y)

/-- The constructed A-module has projective dimension at most n precisely when
its actual minimal projective resolution has zero term n+1. -/
theorem dimension_iff (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    HasProjectiveDimensionLE (SelectedOrdinaryModules.module Y) n ↔
      Subsingleton (PDMinimal.term (finiteModule Y) (n+1)) :=
  PDMinimal.pdLE_iff_term_zero (finiteModule Y) n

/-- The actual minimal-resolution terms are projective. -/
theorem projective (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    Projective ((resolution Y).complex.X n) := inferInstance
end LittleFinitistic.SelectedMinimalResolution

end

end OAI
