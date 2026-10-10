import OAI.GroupTheory.PolycyclicRecognition.Geometry.ActualRotationLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothRotationalTwistLift
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothLieDifferential

namespace OAI

/-! # The original nilpotent factors inside the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

private theorem rotation_inv_apply_of_eq_one {K U : Type*} [Group K] [Group U]
    (α : K →* MulAut U) {k : K} (hk : k = 1) (g : U) : α k⁻¹ g = g := by
  rw [hk, inv_one, map_one]
  rfl

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology
local instance : Fact (Continuous F.rotationCharacter) := ⟨F.continuous_rotationCharacter⟩
local instance : ChartedSpace E (F.SmoothRotationalModification hExp) :=
  F.smoothRotationalModificationChartedSpace hExp

theorem rotationCharacter_inclusionN (n : F.N.carrier) :
    F.rotationCharacter (F.inclusionN n) = 1 := by
  obtain ⟨x,rfl⟩ := F.expN_surjective n
  exact F.rotationCharacter_nilradical x

theorem inverse_rotation_fixes_nilpotent_factor (n m : F.N.carrier) :
    F.factorCompactRotationAction hExp ((F.rotationCharacter (F.inclusionN n))⁻¹)
      (F.inclusionN m) = F.inclusionN m := by
  exact rotation_inv_apply_of_eq_one (F.factorCompactRotationAction hExp)
    (F.rotationCharacter_inclusionN n) (F.inclusionN m)

theorem inverse_rotation_fixes_cartan_factor (d e : F.D.carrier) :
    F.factorCompactRotationAction hExp ((F.rotationCharacter (F.inclusionD d))⁻¹)
      (F.inclusionD e) = F.inclusionD e :=
  F.rotation_fixes_cartan_factor (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp) _ e

/-- The actual nilpotent kernel embeds with its original multiplication. -/
def nilpotentFactorToRotation : F.N.carrier →* F.SmoothRotationalModification hExp :=
  rotationalTwistLift (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.inclusionN
    (F.inverse_rotation_fixes_nilpotent_factor hExp)

/-- The Cartan factor also retains its original multiplication. -/
def cartanFactorToRotation : F.D.carrier →* F.SmoothRotationalModification hExp :=
  rotationalTwistLift (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.inclusionD
    (F.inverse_rotation_fixes_cartan_factor hExp)

theorem contMDiff_nilpotentFactorToRotation :
    ContMDiff (𝓘(ℝ,F.N.modelSpace)) (𝓘(ℝ,E)) ∞ (F.nilpotentFactorToRotation hExp) :=
  contMDiff_rotationalTwistLift _ _ _ _ _
    (F.contMDiff_inclusionN hExp)

theorem contMDiff_cartanFactorToRotation :
    ContMDiff (𝓘(ℝ,F.D.modelSpace)) (𝓘(ℝ,E)) ∞ (F.cartanFactorToRotation hExp) :=
  contMDiff_rotationalTwistLift _ _ _ _ _
    (F.contMDiff_inclusionD hExp)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
