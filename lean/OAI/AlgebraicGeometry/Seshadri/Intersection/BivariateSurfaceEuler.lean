import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurveIdealDegree
import OAI.AlgebraicGeometry.Seshadri.Intersection.GeneralSurfaceEuler

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

lemma mixedEuler_self (S : Surface) (L : LineBundle S.scheme) :
    mixedEuler S L L = selfIntersection S L := by
  have h := eulerCharacteristic_iso S.structureMap
    (moduleTensorIso (Iso.refl L.sheaf) (moduleTensorRightUnit L.sheaf)) 2
  change eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf =
    eulerCharacteristic S.structureMap 2 (L.tensor L).sheaf at h
  unfold mixedEuler selfIntersection
  change _ = eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf -
    2*eulerCharacteristic S.structureMap 2 L.sheaf +
      eulerCharacteristic S.structureMap 2 (O S.scheme)
  rw [h]
  ring

theorem Surface.selfIntersection_twist (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme) (a : ℕ) :
    selfIntersection S ((L.pow a).tensor M) =
      (a : ℤ)^2*selfIntersection S L + 2*(a : ℤ)*mixedEuler S L M + selfIntersection S M := by
  let B := (L.pow a).tensor M
  have hb := S.euler_power_second_difference B
  rw [S.euler_power_one] at hb
  have hB2 := eulerCharacteristic_iso S.structureMap (lineTwistPower L M a 2) 2
  have hB1 := S.twist_euler L hL M a
  have h2 := S.twist_euler L hL (M.pow 2) (a*2)
  rw [mixedEuler_pow_right S L hL] at h2
  have hL1 := S.power_euler_quadratic L hL a
  have hL2 := S.power_euler_quadratic L hL (a*2)
  have hM := S.euler_power_second_difference M
  rw [S.euler_power_one] at hM
  change eulerCharacteristic S.structureMap 2 (B.pow 2).sheaf = _ at hB2
  rw [hB2] at hb
  change eulerCharacteristic S.structureMap 2 ((L.pow (a*2)).tensor (M.pow 2)).sheaf -
      2*eulerCharacteristic S.structureMap 2 ((L.pow a).tensor M).sheaf +
      eulerCharacteristic S.structureMap 2 (O S.scheme) = selfIntersection S B at hb
  change eulerCharacteristic S.structureMap 2 (M.pow 2).sheaf -
      2*eulerCharacteristic S.structureMap 2 M.sheaf +
      eulerCharacteristic S.structureMap 2 (O S.scheme) = selfIntersection S M at hM
  push_cast at h2 hL1 hL2
  rw [h2,hB1] at hb
  nlinarith only [hb,hL2,hL1,hM]

theorem Surface.selfIntersection_pow (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme) (b : ℕ) :
    selfIntersection S (M.pow b) = (b : ℤ)^2*selfIntersection S M := by
  have h := S.euler_power_second_difference (M.pow b)
  rw [S.euler_power_one] at h
  have he := eulerCharacteristic_iso S.structureMap (linePowerMul M b 2) 2
  change eulerCharacteristic S.structureMap 2 ((M.pow b).pow 2).sheaf =
    eulerCharacteristic S.structureMap 2 (M.pow (b*2)).sheaf at he
  rw [he] at h
  have h₁ := S.arbitrary_power_euler_quadratic L hL M b
  have h₂ := S.arbitrary_power_euler_quadratic L hL M (b*2)
  change eulerCharacteristic S.structureMap 2 (M.pow (b*2)).sheaf -
      2*eulerCharacteristic S.structureMap 2 (M.pow b).sheaf +
      eulerCharacteristic S.structureMap 2 (O S.scheme) = selfIntersection S (M.pow b) at h
  push_cast at h₂
  nlinarith only [h,h₂,h₁]

theorem Surface.selfIntersection_twist_pow (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (J : LineBundle S.scheme) (a b : ℕ) :
    selfIntersection S ((L.pow a).tensor (J.pow b)) =
      (a : ℤ)^2*selfIntersection S L + 2*(a : ℤ)*(b : ℤ)*mixedEuler S L J +
        (b : ℤ)^2*selfIntersection S J := by
  rw [S.selfIntersection_twist L hL,mixedEuler_pow_right S L hL,
    S.selfIntersection_pow L hL]
  ring

lemma mixedEuler_twist_pow (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (J : LineBundle S.scheme) (a b : ℕ) :
    mixedEuler S L ((L.pow a).tensor (J.pow b)) =
      (a : ℤ)*selfIntersection S L + (b : ℤ)*mixedEuler S L J := by
  rw [mixedEuler_tensor_right S L hL,mixedEuler_pow_right S L hL,
    mixedEuler_pow_right S L hL,mixedEuler_self]

end
end MaximalSeshadri.Geometry

end



end OAI
