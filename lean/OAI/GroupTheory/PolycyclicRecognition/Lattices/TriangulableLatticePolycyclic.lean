import OAI.GroupTheory.PolycyclicRecognition.Geometry.DiscreteHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeFiniteGeneration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConstructChainMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MatrixDifferentialFromSmoothness

namespace OAI

/-! # Polycyclicity of lattices in the actual triangulable model

Finite generation comes from compactness and metric chains. The real triangular
adjoint representation then identifies a polycyclic kernel and abelian height
quotient. No lattice structure theorem is assumed for this specialization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

/-- The uniform-lattice polycyclicity theorem for a real-triangulable,
connected simply connected solvable Lie model. -/
theorem isPolycyclic_uniformLattice_of_realTriangulable
    (S : SimplyConnectedSolvableLieModel) (hS : IsRealTriangulable S)
    (Λ : Subgroup S.carrier) (hΛ : IsUniformLattice Λ) : IsPolycyclic Λ := by
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let := d.compatibleMetric
  let := d.proper_compatibleMetric
  let := d.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : DiscreteTopology Λ := hΛ.1
  let : Group.FG Λ := hΛ.finitelyGenerated d.chains_compatibleMetric
  obtain ⟨a, ⟨T⟩⟩ := hS.exists_triangularAdjoint matrixLieDifferentialInput S
  exact isPolycyclic_finitelyGenerated_discrete_of_triangularAdjoint T
    (groupExponential (E := S.modelSpace) (G := S.carrier))
    groupExponential_isGroupExponential Λ

end PolycyclicRecognition

end

end OAI
