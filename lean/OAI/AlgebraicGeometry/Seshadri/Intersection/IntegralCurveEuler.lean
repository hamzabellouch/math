import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.AllCurveDegree

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.tensor_euler_add (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L M : LineBundle C.scheme) :
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (L.tensor M).sheaf -
        eulerCharacteristic (C.embedding ≫ S.structureMap) 1 M.sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 L.sheaf -
        eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) := by
  obtain ⟨σ,hσ,B,a,ha,hc⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hc
  exact projective_curve_tensor_euler_add (C.embedding ≫ S.structureMap)
    C.dimension a ha L M

theorem IntegralCurve.power_euler (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) (n : ℕ) :
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (L.pow n).sheaf -
        eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) =
      (n : ℤ) * (eulerCharacteristic (C.embedding ≫ S.structureMap) 1 L.sheaf -
        eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) := by
  obtain ⟨σ,hσ,B,a,ha,hc⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hc
  exact projective_curve_power_euler (C.embedding ≫ S.structureMap)
    C.dimension a ha L n

theorem IntegralCurve.pullback_power_euler (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle S.scheme) (n : ℕ) :
    eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((L.pullback C.embedding).pow n).sheaf -
        eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme) =
      (n : ℤ) * curveDegree S L C :=
  C.power_euler S A hA (L.pullback C.embedding) n

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
