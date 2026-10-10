import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.BivariateSurfaceEuler

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

lemma mixedEuler_ample_twist_left (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (d : ℕ) :
    mixedEuler S ((A.pow d).tensor M) N =
      (d : ℤ)*mixedEuler S A N + mixedEuler S M N := by
  have h₁ := S.twist_euler A hA (M.tensor N) d
  have h₂ := S.twist_euler A hA M d
  rw [mixedEuler_tensor_right S A hA] at h₁
  have he := eulerCharacteristic_iso S.structureMap
    (lineTensorAssoc (A.pow d) M N) 2
  change eulerCharacteristic S.structureMap 2 (((A.pow d).tensor M).tensor N).sheaf =
    eulerCharacteristic S.structureMap 2 ((A.pow d).tensor (M.tensor N)).sheaf at he
  unfold mixedEuler
  rw [he,h₁,h₂]
  unfold mixedEuler
  ring

lemma mixedEuler_tensor_right_general (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N P : LineBundle S.scheme) :
    mixedEuler S M (N.tensor P) = mixedEuler S M N + mixedEuler S M P := by
  obtain ⟨d,hd,hB⟩ := A.exists_ample_twist M hA
  have H := mixedEuler_tensor_right S ((A.pow d).tensor M) hB N P
  rw [mixedEuler_ample_twist_left S A hA,mixedEuler_ample_twist_left S A hA,
    mixedEuler_ample_twist_left S A hA,mixedEuler_tensor_right S A hA] at H
  linarith

lemma mixedEuler_pow_right_general (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (n : ℕ) :
    mixedEuler S M (N.pow n) = (n : ℤ)*mixedEuler S M N := by
  obtain ⟨d,hd,hB⟩ := A.exists_ample_twist M hA
  have H := mixedEuler_pow_right S ((A.pow d).tensor M) hB N n
  rw [mixedEuler_ample_twist_left S A hA,mixedEuler_ample_twist_left S A hA,
    mixedEuler_pow_right S A hA] at H
  nlinarith only [H]

lemma mixedEuler_tensor_left_general (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N P : LineBundle S.scheme) :
    mixedEuler S (M.tensor N) P = mixedEuler S M P + mixedEuler S N P := by
  rw [mixedEuler_comm,mixedEuler_tensor_right_general S A hA,
    mixedEuler_comm S P M,mixedEuler_comm S P N]

lemma mixedEuler_pow_left_general (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (n : ℕ) :
    mixedEuler S (M.pow n) N = (n : ℤ)*mixedEuler S M N := by
  rw [mixedEuler_comm,mixedEuler_pow_right_general S A hA,mixedEuler_comm S N M]

lemma Surface.selfIntersection_tensor_general (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) (M N : LineBundle S.scheme) :
    selfIntersection S (M.tensor N) = selfIntersection S M +
      2*mixedEuler S M N+selfIntersection S N := by
  rw [← mixedEuler_self,mixedEuler_tensor_left_general S A hA,
    mixedEuler_tensor_right_general S A hA,mixedEuler_tensor_right_general S A hA,
    mixedEuler_self,mixedEuler_self,mixedEuler_comm S N M]
  ring

lemma Surface.selfIntersection_twist_general (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) (M N : LineBundle S.scheme) (a b : ℕ) :
    selfIntersection S ((M.pow a).tensor (N.pow b)) =
      (a : ℤ)^2*selfIntersection S M + 2*(a : ℤ)*(b : ℤ)*mixedEuler S M N +
        (b : ℤ)^2*selfIntersection S N := by
  rw [S.selfIntersection_tensor_general A hA,S.selfIntersection_pow A hA,
    S.selfIntersection_pow A hA,mixedEuler_pow_left_general S A hA,
    mixedEuler_pow_right_general S A hA]
  ring

end
end MaximalSeshadri.Geometry

end



end OAI
