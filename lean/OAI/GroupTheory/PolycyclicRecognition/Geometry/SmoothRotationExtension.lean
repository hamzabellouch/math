import OAI.GroupTheory.PolycyclicRecognition.Geometry.ActualSmoothRotation

namespace OAI

/-! # The actual smooth graph and its compact extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

instance smoothRotationExtensionTopologicalGroup :
    IsTopologicalGroup (G ⋊[F.factorCompactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact semidirectProductTopologicalGroup _ (F.continuous_factorCompactRotationAction hExp)

instance smoothRotationalModificationTopologicalGroup :
    IsTopologicalGroup (F.SmoothRotationalModification hExp) := inferInstance

/-- The metric has exactly the existing graph topology. -/
@[instance_reducible]
def smoothRotationalModificationMetric : MetricSpace (F.SmoothRotationalModification hExp) :=
  (F.smoothRotationalModificationHomeomorph hExp).isEmbedding.comapMetricSpace
    (F.smoothRotationalModificationHomeomorph hExp)

instance smoothRotationalModificationSimplyConnected [SimplyConnectedSpace G] :
    SimplyConnectedSpace (F.SmoothRotationalModification hExp) :=
  (F.smoothRotationalModificationHomeomorph hExp).toHomotopyEquiv.simplyConnectedSpace_iff.mpr
    inferInstance

def originalToSmoothRotationExtension :
    ProperCocompactHom G (G ⋊[F.factorCompactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact semidirect_inl_properCocompact (F.factorCompactRotationAction hExp)

def smoothModificationToRotationExtension :
    ProperCocompactHom (F.SmoothRotationalModification hExp)
      (G ⋊[F.factorCompactRotationAction hExp] realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  exact rotationalTwist_properCocompact (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.continuous_rotationCharacter

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
