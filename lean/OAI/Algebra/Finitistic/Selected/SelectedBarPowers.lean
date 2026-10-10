import OAI.Algebra.Finitistic.Selected.SelectedBarComparison

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedBarPowers
open SelectedOrdinaryAlgebra SelectedBarComparison
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- All powers on the exact selected first-block derived family are the original
bar-derived powers; every resolution, scalar, action and stalk bridge is discharged. -/
def comparison (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (native.obj^[r]) (SelectedFirstBlockFamily.derived Y) ≅ SelectedBaseIterates.object Y r :=
  (eqToIso (BimoduleTotal.nativeIterate_obj resolution r (SelectedFirstBlockFamily.derived Y))).symm ≪≫
  (BimoduleTotal.nativeIterate resolution r).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat D) 0).app (SelectedBaseIterates.input Y)) ≪≫
  eqToIso (BimoduleTotal.nativeIterate_obj resolution r
    (DerivedCategory.Q.obj (BimoduleTotal.singleInput D (SelectedBaseIterates.input Y)))) ≪≫
  powerIso (SelectedBaseIterates.input Y) r

theorem isZero_iff (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    IsZero ((native.obj^[r]) (SelectedFirstBlockFamily.derived Y)) ↔
      IsZero (SelectedBaseIterates.object Y r) := (comparison Y r).isZero_iff
end LittleFinitistic.SelectedBarPowers

end

end OAI
