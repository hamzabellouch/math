import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryModules
import OAI.Algebra.Finitistic.Bar.FiniteBarResolution

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedBarResolution
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- The genuine absolute bar projective resolution of each actual inflated
module. It can have infinitely many nonzero degrees. -/
def resolution (Y : FiniteSelectionFamily.S.{0}) : ProjectiveResolution (module Y) :=
  DerivedBar.projectiveResolution ℂ A (Inflated Y)

theorem finite_free (Y : FiniteSelectionFamily.S.{0}) (n : ℕ) :
    Module.Finite A ((resolution Y).complex.X n) ∧
      Module.Free A ((resolution Y).complex.X n) :=
  ⟨DerivedBar.projectiveResolution_finite ℂ A (Inflated Y) n,
    DerivedBar.projectiveResolution_free ℂ A (Inflated Y) n⟩
end LittleFinitistic.SelectedBarResolution

end

end OAI
