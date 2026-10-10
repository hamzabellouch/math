import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationTriangularRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationRepresentedChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedSolvableLieModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTriangularImage
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactSemidirectModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentedMatrixChoice

namespace OAI

/-! # The analytic real-triangulable model of the actual rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  [SimplyConnectedSpace G] [SecondCountableTopology G] [Group.IsSolvable G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

omit [SimplyConnectedSpace G] [SecondCountableTopology G] in
theorem smoothRotationalModification_solvable : Group.IsSolvable (F.SmoothRotationalModification hExp) := by
  let solv : Group.IsSolvable (G ⋊[F.factorCompactRotationAction hExp]
      realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) :=
    semidirect_solvable (F.factorCompactRotationAction hExp)
  infer_instance

theorem exists_triangulable_rotation_model :
    ∃ S : SimplyConnectedSolvableLieModel, IsRealTriangulable S ∧
      Nonempty (ProperCocompactHom S.carrier
        (G ⋊[F.factorCompactRotationAction hExp]
          realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H)) := by
  let metric : MetricSpace (F.SmoothRotationalModification hExp) :=
    F.smoothRotationalModificationMetric hExp
  let countable : SecondCountableTopology (F.SmoothRotationalModification hExp) :=
    (F.smoothRotationalModificationHomeomorph hExp).secondCountableTopology
  let solv : Group.IsSolvable (F.SmoothRotationalModification hExp) :=
    F.smoothRotationalModification_solvable hExp
  apply exists_triangulable_model_of_representations (E := E)
    (F.smoothModificationToRotationExtension hExp)
  exact exists_represented_matrix_group
    (fun _ j => Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
      (∀ x ∈ realShadowKernel T H, IsNilpotent (j x)))
    (fun x : T.kernelIdeal => cartanRealShadowEquiv T H x)
    (fun h : H => cartanRealShadowEquiv T H h)
    (F.rotationExponentialProduct hExp) (F.rotationExponentialProduct_surjective hExp)
    (F.exists_faithful_rotation_triangular_representation hExp)
    (fun _ _ hj => hj.2.1)
    (fun _ j hj ρ he => F.exists_rotation_representedLocalChart hExp j hj.1 ρ he)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
