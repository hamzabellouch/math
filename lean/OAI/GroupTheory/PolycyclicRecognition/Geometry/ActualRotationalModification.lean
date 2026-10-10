import OAI.GroupTheory.PolycyclicRecognition.Geometry.FactorRotationCharacter

namespace OAI

/-! # The actual compact rotational modification of the original group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)

/-- The compact action on the original group, now with its invariant character. -/
def compactRotationAction : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G :=
  (F.exists_invariant_compact_rotations hExp).choose

theorem continuous_compactRotationAction :
    Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H × G =>
      F.compactRotationAction hExp p.1 p.2) :=
  (F.exists_invariant_compact_rotations hExp).choose_spec.1

theorem compactRotationAction_invariant :
    ∀ k g, F.rotationCharacter (F.compactRotationAction hExp k g) = F.rotationCharacter g :=
  (F.exists_invariant_compact_rotations hExp).choose_spec.2

attribute [local instance] semidirectProductTopology

/-- The concrete graph subgroup that removes the compact rotations. -/
abbrev RotationalModification :=
  ↥(rotationalTwist (F.compactRotationAction hExp) F.rotationCharacter
    (F.compactRotationAction_invariant hExp))

/-- The modification preserves the original underlying topology. -/
def rotationalModificationHomeomorph : F.RotationalModification hExp ≃ₜ G :=
  rotationalTwistHomeomorph (F.compactRotationAction hExp) F.rotationCharacter
    (F.compactRotationAction_invariant hExp) F.continuous_rotationCharacter

instance rotationalExtensionTopologicalGroup :
    IsTopologicalGroup (G ⋊[F.compactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact semidirectProductTopologicalGroup _ (F.continuous_compactRotationAction hExp)

instance rotationalModificationTopologicalGroup :
    IsTopologicalGroup (F.RotationalModification hExp) := inferInstance

/-- The original group is properly and cocompactly included in the compact extension. -/
def originalToRotationalExtension :
    ProperCocompactHom G (G ⋊[F.compactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact semidirect_inl_properCocompact (F.compactRotationAction hExp)

/-- The actual modification has the other proper cocompact inclusion. -/
def modificationToRotationalExtension :
    ProperCocompactHom (F.RotationalModification hExp)
      (G ⋊[F.compactRotationAction hExp] realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact rotationalTwist_properCocompact (F.compactRotationAction hExp) F.rotationCharacter
    (F.compactRotationAction_invariant hExp) F.continuous_rotationCharacter

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
