import OAI.Geometry.IsometricImmersion.Caps.PulseReflection
import OAI.Geometry.IsometricImmersion.Taylor.TaylorCauchyData
import OAI.Geometry.IsometricImmersion.Caps.UpperCapWords

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection SmoothLocal.Pulse

theorem reflectPoint_initialPoint (x a : ℝ) :
    reflectPoint (![x,a] : Coord) = ![x,-a] := by
  ext i
  fin_cases i <;> simp

theorem coordPartial_one_reflectedScalar (f : Coord → ℝ) (p : Coord) :
    coordPartial 1 (reflectedScalar f) p = -coordPartial 1 f (reflectPoint p) := by
  have he : fderiv ℝ (f ∘ reflectPoint) p =
      (fderiv ℝ f (reflectPoint p)).comp
        (reflectionIsometry.toContinuousLinearEquiv : Coord →L[ℝ] Coord) :=
    reflectionIsometry.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := p)
  change fderiv ℝ (f ∘ reflectPoint) p (Pi.single 1 (1 : ℝ)) =
    -fderiv ℝ f (reflectPoint p) (Pi.single 1 (1 : ℝ))
  rw [he, ContinuousLinearMap.comp_apply]
  have hb : reflectionIsometry.toContinuousLinearEquiv (Pi.single 1 (1 : ℝ)) =
      -(Pi.single 1 (1 : ℝ) : Coord) := by
    ext i
    fin_cases i <;> simp [reflectionIsometry,reflectPoint]
  change (fderiv ℝ f (reflectPoint p)) (reflectionIsometry (Pi.single 1 1)) =
    -(fderiv ℝ f (reflectPoint p)) (Pi.single 1 1)
  change reflectionIsometry (Pi.single 1 (1 : ℝ)) = -(Pi.single 1 (1 : ℝ) : Coord) at hb
  rw [hb,map_neg]

theorem heightCauchyValue_reflected (z : Coord → ℝ) (a : ℝ) :
    heightCauchyValue (reflectedScalar z) a = heightCauchyValue z (-a) := by
  funext x
  change z (reflectPoint ![x,a]) = z ![x,-a]
  rw [reflectPoint_initialPoint]

theorem heightCauchyVelocity_reflected (z : Coord → ℝ) (a : ℝ) :
    heightCauchyVelocity (reflectedScalar z) a = -heightCauchyVelocity z (-a) := by
  funext x
  change coordPartial 1 (reflectedScalar z) ![x,a] = -coordPartial 1 z ![x,-a]
  rw [coordPartial_one_reflectedScalar,reflectPoint_initialPoint]

theorem reflected_Cauchy_jet_norms (z : Coord → ℝ) (a x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (heightCauchyValue (reflectedScalar z) a) x‖ =
      ‖iteratedFDeriv ℝ n (heightCauchyValue z (-a)) x‖ ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity (reflectedScalar z) a) x‖ =
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity z (-a)) x‖ := by
  simp [heightCauchyValue_reflected,heightCauchyVelocity_reflected,
    iteratedFDeriv_neg_apply]

theorem sheared_reflected_Cauchy_jet_norms (z : Coord → ℝ) (q0 a x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (heightCauchyValue
      (heightInShearCoordinates (reflectedScalar z) (-q0)) a) x‖ =
        ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0) (-a)) x‖ ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity
      (heightInShearCoordinates (reflectedScalar z) (-q0)) a) x‖ =
        ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0) (-a)) x‖ := by
  rw [height_shear_reflection]
  exact reflected_Cauchy_jet_norms _ a x n

end SmoothLocal.Taylor

end

end OAI
