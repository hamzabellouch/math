import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PowerExtension
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision

namespace OAI


                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def moduleTensorComm (M N : X.Modules) : moduleTensor X M N ≅ moduleTensor X N M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

def lineTensorInterchange (A B C D : LineBundle X) :
    ((A.tensor B).tensor (C.tensor D)).sheaf ≅ ((A.tensor C).tensor (B.tensor D)).sheaf :=
  lineTensorAssoc A B (C.tensor D) ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (lineTensorAssoc B C D).symm ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (moduleTensorIso (moduleTensorComm B.sheaf C.sheaf) (Iso.refl D.sheaf)) ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (lineTensorAssoc C B D) ≪≫
  (lineTensorAssoc A C (B.tensor D)).symm

def lineTensorPower (L M : LineBundle X) : ∀ n : ℕ,
    ((L.tensor M).pow n).sheaf ≅ ((L.pow n).tensor (M.pow n)).sheaf
  | 0 => (moduleTensorUnit (O X)).symm
  | n+1 => moduleTensorIso (Iso.refl _) (lineTensorPower L M n) ≪≫
    lineTensorInterchange L M (L.pow n) (M.pow n)

def lineTwistPower (L M : LineBundle X) (d n : ℕ) :
    (((L.pow d).tensor M).pow n).sheaf ≅ ((L.pow (d*n)).tensor (M.pow n)).sheaf :=
  lineTensorPower (L.pow d) M n ≪≫ moduleTensorIso (linePowerMul L d n) (Iso.refl _)

end
end MaximalSeshadri.Geometry

end

end OAI
