import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticRepresentationGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticTriangularRealization

namespace OAI

/-! # The solvable Lie model carried by analytic representation charts -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold Matrix.Norms.Operator

variable {G E : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [SimplyConnectedSpace G] [Group.IsSolvable G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} {ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ}

def RepresentedLocalChart.solvableLieModel (C : RepresentedLocalChart (E := E) ρ) :
    SimplyConnectedSolvableLieModel where
  modelSpace := E
  carrier := G
  chartedSpace := C.chartedSpace
  lieGroup := C.lieGroup

theorem RepresentedLocalChart.isRealTriangulable
    (C : RepresentedLocalChart (E := E) ρ) (hc : Continuous ρ) (hi : Function.Injective ρ)
    (ht : ∀ g, (ρ g : Matrix (Fin m) (Fin m) ℝ).IsUpperTriangular) :
    IsRealTriangulable C.solvableLieModel :=
  realTriangulable_of_faithful_triangular_hom C.solvableLieModel ρ hc hi ht

theorem exists_triangulable_model_of_representations
    {X : Type} [Group X] [TopologicalSpace X] (f : ProperCocompactHom G X)
    (hrep : ∃ n, ∃ τ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ,
      Continuous τ ∧ Function.Injective τ ∧
      (∀ g, (τ g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular) ∧
      Nonempty (RepresentedLocalChart (E := E) τ)) :
    ∃ S : SimplyConnectedSolvableLieModel, IsRealTriangulable S ∧
      Nonempty (ProperCocompactHom S.carrier X) := by
  obtain ⟨n,τ,hc,hi,ht,⟨C⟩⟩ := hrep
  exact ⟨C.solvableLieModel,C.isRealTriangulable hc hi ht,⟨f⟩⟩

end PolycyclicRecognition

end

end OAI
