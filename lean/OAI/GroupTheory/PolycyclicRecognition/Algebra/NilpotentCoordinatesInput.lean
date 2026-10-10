import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConstructExponential

namespace OAI

/-! # Removing exponential existence from the nilpotent coordinate input

The global intrinsic exponential identifies a simply connected nilpotent
Lie group with its Lie algebra and transports coordinate volume to Haar measure.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- Only the global topological chart, with no measure compatibility. -/
def NilpotentGlobalExponentialChartInput [T2Space G] [SimplyConnectedSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    ∃ c : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, c x = Exp x

def NilpotentExponentialCoordinatesInput [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G) →
    (∃ c : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G, ∀ x, c x = Exp x) ∧
    ∀ (n : ℕ) (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)),
      (Measure.map (Exp ∘ b.equivFun.symm) volume).IsHaarMeasure

variable {E G} [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

theorem NilpotentExponentialCoordinatesInput.toGlobalCharts
    (h : NilpotentExponentialCoordinatesInput E G) :
    NilpotentGlobalExponentialChartInput E G := fun Exp hExp hnil => (h Exp hExp hnil).1

theorem NilpotentExponentialCoordinatesInput.toHaar
    (h : NilpotentExponentialCoordinatesInput E G) : NilpotentExponentialHaarInput E G :=
  ⟨fun _ => exists_groupExponential, h⟩

theorem nilpotentExponentialHaarInput_iff_coordinates :
    NilpotentExponentialHaarInput E G ↔ NilpotentExponentialCoordinatesInput E G :=
  ⟨fun h => h.2, fun h => h.toHaar⟩

end PolycyclicRecognition

end

end OAI
