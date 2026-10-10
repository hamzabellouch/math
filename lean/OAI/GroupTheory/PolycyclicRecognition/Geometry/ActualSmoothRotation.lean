import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothFactorRotations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothRotationalTwist

namespace OAI

/-! # The smooth rotational modification from the actual Cartan factors

The chosen compact action retains its factor formula. This constructs a
smooth graph group; its Lie algebra identification and triangular matrix
realization are separate steps.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)

def factorCompactRotationAction :
    realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G :=
  (F.exists_compact_rotation_action hExp).choose

theorem factorCompactRotationAction_formula :
    ∀ z (x : T.kernelIdeal) d,
      F.factorCompactRotationAction hExp z
        (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d :=
  (F.exists_compact_rotation_action hExp).choose_spec.2

theorem continuous_factorCompactRotationAction :
    Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H × G =>
      F.factorCompactRotationAction hExp p.1 p.2) :=
  (F.exists_compact_rotation_action hExp).choose_spec.1

theorem factorCompactRotationAction_invariant :
    ∀ z g, F.rotationCharacter (F.factorCompactRotationAction hExp z g) = F.rotationCharacter g :=
  F.rotationCharacter_invariant (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp)

theorem contMDiff_inverse_factorCompactRotationAction :
    ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun p : G × G => F.factorCompactRotationAction hExp ((F.rotationCharacter p.1)⁻¹) p.2) :=
  F.contMDiff_inverse_factorRotation hExp (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp)

attribute [local instance] semidirectProductTopology

abbrev SmoothRotationalModification :=
  ↥(rotationalTwist (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp))

@[instance_reducible]
def smoothRotationalModificationChartedSpace : ChartedSpace E (F.SmoothRotationalModification hExp) := by
  let : Fact (Continuous F.rotationCharacter) := ⟨F.continuous_rotationCharacter⟩
  exact rotationalTwistChartedSpace (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp)

attribute [local instance] smoothRotationalModificationChartedSpace

/-- Both operations of the actual graph group are infinitely differentiable. -/
theorem smoothRotationalModificationLieGroup : LieGroup (𝓘(ℝ,E)) ∞ (F.SmoothRotationalModification hExp) := by
  let : Fact (Continuous F.rotationCharacter) := ⟨F.continuous_rotationCharacter⟩
  exact rotationalTwistLieGroup (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp)
    (F.contMDiff_inverse_factorCompactRotationAction hExp)

def smoothRotationalModificationHomeomorph : F.SmoothRotationalModification hExp ≃ₜ G :=
  rotationalTwistHomeomorph (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.continuous_rotationCharacter

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
