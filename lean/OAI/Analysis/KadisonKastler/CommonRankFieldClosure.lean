import OAI.Analysis.KadisonKastler.CommonRankSourceModel
import OAI.Analysis.KadisonKastler.HilbertSumConjugateClosure

namespace OAI

/-! # Actual rank fields of a represented bicommutant member

Kaplansky approximation on the original representation, transported through
the constructed unitary, places the rank fields in the corresponding fiber
bicommutants. The common source may be larger than the algebra being closed.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankClosureCoordinateSeparable (n : ℕ) :
    TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  separable_scalarHilbertCoordinates

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRank_field_mem_of_closure
    {C : Type*} [CStarAlgebra C] (ι : C →⋆ₐ[ℂ] B)
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra)
    (hT : T.val ∈ representationVonNeumannAlgebra (σ.comp ι)) (n : ℕ) :
    ∀ᵐ x ∂commonRankSourceMeasure M n,
      commonRankOperatorField M T n x ∈ commonRankFiberAlgebra M ι n x := by
  let : TopologicalSpace.SeparableSpace (CommonRankSpace M) := commonRankSpace_separable M
  exact ae_hilbertSum_representation_field_mem
    (K := fun i => ℓ²(projectionDimensionIndex i, ℂ)) (commonRankSourceMeasure M)
    (commonRankCoordinates M) (σ.comp ι)
    (fun n x => (fixedFiberRepresentation M.field (commonRankBasis π D)
      (commonRankBasis_total π D) n x).comp ι)
    (fun a v n => commonRankCoordinates_action M (ι a) v n)
    T.val hT (commonRankOperatorField M T) (commonRankOperatorField_action M T) n

end

end KadisonKastler

end OAI
