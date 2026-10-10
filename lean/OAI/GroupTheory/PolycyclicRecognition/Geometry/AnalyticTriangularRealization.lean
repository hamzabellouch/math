import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MatrixDifferentialFromSmoothness
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConstructChainMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LocallyCompactGroupEmbedding

namespace OAI

/-! # Closed triangular realizations of analytic solvable Lie models -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator

theorem realTriangulable_of_triangularAdjoint (S : SimplyConnectedSolvableLieModel)
    (hT : ∃ a, Nonempty (TriangularAdjoint
      (GroupLieAlgebra (𝓘(ℝ,S.modelSpace)) S.carrier) a)) : IsRealTriangulable S := by
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let metric : MetricSpace S.carrier := d.compatibleMetric
  let tg : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ,S.modelSpace)) ⊤
  let lc : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ,S.modelSpace))
  obtain ⟨a,⟨T⟩⟩ := hT
  obtain ⟨m,hm,σ,hσ,_⟩ := onshuusPostRealizationInput_intrinsic T
    (groupExponential (E := S.modelSpace) (G := S.carrier)) groupExponential_isGroupExponential
  let ρ : S.carrier →* (Matrix (Fin m) (Fin m) ℝ)ˣ := (positiveTriangular m).subtype.comp σ
  have hind : Topology.IsInducing ρ :=
    Units.isOpenEmbedding_val.isInducing.of_comp_iff.mp hσ
  have hinj : Function.Injective ρ := by
    intro x y h
    apply hσ.injective
    change ((ρ x : (Matrix (Fin m) (Fin m) ℝ)ˣ) : Matrix (Fin m) (Fin m) ℝ) =
      ((ρ y : (Matrix (Fin m) (Fin m) ℝ)ˣ) : Matrix (Fin m) (Fin m) ℝ)
    exact congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ => (u : Matrix (Fin m) (Fin m) ℝ)) h
  exact ⟨m,ρ,closedEmbedding_of_locallyCompact_group ρ ⟨hind,hinj⟩,
    fun g => (σ g).property.1⟩

theorem realTriangulable_of_faithful_triangular_hom (S : SimplyConnectedSolvableLieModel)
    {m : ℕ} (ρ : S.carrier →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (hc : Continuous ρ) (hi : Function.Injective ρ)
    (ht : ∀ g, (ρ g : Matrix (Fin m) (Fin m) ℝ).IsUpperTriangular) : IsRealTriangulable S := by
  obtain ⟨j,hj⟩ := matrixLieDifferentialInput S m ρ hc hi
  apply realTriangulable_of_triangularAdjoint S
  apply nonempty_triangularAdjoint_of_triangular_representation j
    (matrixLieDifferential_injective S m ρ hi j hj)
  exact fun v => hasMFDerivAt_upperTriangular hj ht v

end PolycyclicRecognition

end

end OAI
