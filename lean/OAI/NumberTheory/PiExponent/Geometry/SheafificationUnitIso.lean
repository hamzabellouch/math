import OAI.NumberTheory.PiExponent.Approximation.TensorPure

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme}

theorem sheafification_unit_isIso (M : X.Modules) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app M.val) := by
  exact (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso (Iso.refl M.val)

theorem sheafification_unit_isIso_of_iso (P : PresheafOfModules X.ringCatSheaf.obj)
    (M : X.Modules) (e : P ≅ M.val) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app P) :=
  (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.Geometry

end OAI
