import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.IntegralCurveEuler
import OAI.AlgebraicGeometry.Seshadri.Sheaves.LinePullbackTensor

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

theorem curveDegree_tensor (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L M : LineBundle S.scheme) (C : IntegralCurve S) :
    curveDegree S (L.tensor M) C = curveDegree S L C + curveDegree S M C := by
  have he := C.tensor_euler_add S A hA (L.pullback C.embedding) (M.pullback C.embedding)
  have hi := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    (PullbackTensor.iso C.embedding L M) 1
  unfold curveDegree
  rw [hi]
  change _ - _ = (_ - _) + (_ - _)
  dsimp only [LineBundle.pullback, LineBundle.tensor, O, structureSheaf] at he ⊢
  omega

theorem curveDegree_pow (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (C : IntegralCurve S) (n : ℕ) :
    curveDegree S (L.pow n) C = (n : ℤ) * curveDegree S L C := by
  have hi := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    (PullbackTensor.powIso C.embedding L n) 1
  unfold curveDegree
  rw [hi]
  exact C.pullback_power_euler S A hA L n

end
end MaximalSeshadri.Geometry

end



end OAI
