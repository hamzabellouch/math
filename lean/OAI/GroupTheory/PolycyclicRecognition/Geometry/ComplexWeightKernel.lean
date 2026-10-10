import OAI.GroupTheory.PolycyclicRecognition.Algebra.ClosedNilpotentLinearKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightRange

namespace OAI

/-! # The actual closed kernel of the complex adjoint weights -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  {n : ℕ} (T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
/-- The nilpotent infinitesimal weight kernel integrates onto the full
kernel of a continuous character on the original group. -/
theorem exists_closed_complex_weight_kernel :
    ∃ π : G →* Multiplicative T.weightMap.range, Continuous π ∧
      (∀ x, (π (Exp x)).toAdd = T.weightMap.rangeRestrict x) ∧
      ∃ (N : NilpotentLieModel T.kernelIdeal)
        (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier),
        IsGroupExponential ExpN ∧
        ∃ ι : N.carrier →* G, Topology.IsClosedEmbedding ι ∧
          ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, E)) ∞ ι ∧
          (∀ x : T.kernelIdeal, ι (ExpN (N.equiv x)) = Exp x) ∧
          Set.range ι = (π.ker : Set G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace E G
  obtain ⟨π₀, hπ₀, hπ₀Exp⟩ := exists_additive_complex_adjoint_weights (Module.finBasis ℝ E) T hExp
  obtain ⟨π, hπ, he⟩ := exists_range_restricted_complex_weights hExp T.weightMap π₀ hπ₀ hπ₀Exp
  have hπc : Continuous π := continuous_ofAdd.comp hπ
  refine ⟨π, hπc, he, ?_⟩
  apply exists_closed_nilpotent_linear_kernel T.kernelIdeal T.kernelIdeal_nilpotent
    T.weightMap.rangeRestrict T.weightMap.surjective_rangeRestrict _ Exp hExp π hπc he
  intro x
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

end PolycyclicRecognition

end

end OAI
