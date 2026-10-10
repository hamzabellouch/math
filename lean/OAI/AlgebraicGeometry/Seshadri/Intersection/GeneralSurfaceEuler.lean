import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorPowerDistribution
import OAI.AlgebraicGeometry.Seshadri.Intersection.MixedIntersection
import OAI.AlgebraicGeometry.Seshadri.Geometry.AmpleFromCover
import OAI.AlgebraicGeometry.Seshadri.Geometry.GeneralQuadraticNumerics

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.arbitrary_power_euler_quadratic (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (M.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S M +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 M.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  obtain ⟨d,_,hB⟩ := L.exists_ample_twist M hL
  let B := (L.pow d).tensor M
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (M.pow n).sheaf
  let g (n : ℕ) := eulerCharacteristic S.structureMap 2 (B.pow n).sheaf
  let h (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  have hQ (A : LineBundle S.scheme) (hA : A.IsAmple) :
      EulerNumerics.Quadratic (fun n => eulerCharacteristic S.structureMap 2 (A.pow n).sheaf) := by
    intro j
    dsimp only
    rw [S.euler_power_second_difference A,S.euler_power_one A]
    exact S.power_euler_quadratic A hA j
  have he (j : ℕ) : f j = g j - h (d*j) +
      eulerCharacteristic S.structureMap 2 (O S.scheme) -
      (d : ℤ)*(j : ℤ)^2*mixedEuler S L M := by
    have H := S.twist_euler L hL (M.pow j) (d*j)
    have E := eulerCharacteristic_iso S.structureMap (lineTwistPower L M d j) 2
    change g j = eulerCharacteristic S.structureMap 2 ((L.pow (d*j)).tensor (M.pow j)).sheaf at E
    rw [← E,mixedEuler_pow_right S L hL] at H
    dsimp only [f,h]
    push_cast at H
    linear_combination -H
  have H := EulerNumerics.quadratic_of_twisted f g h d
    (eulerCharacteristic S.structureMap 2 (O S.scheme)) (mixedEuler S L M)
    (hQ B hB) (hQ L hL) he n
  dsimp only [f] at H
  rw [S.euler_power_second_difference M,S.euler_power_one M] at H
  exact H

end
end MaximalSeshadri.Geometry

end


end OAI
