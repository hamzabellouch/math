import OAI.Analysis.KadisonSimilarity.Derivation.CyclicSummandColumns
import OAI.Analysis.KadisonSimilarity.Representation.ScalarKaplansky
import OAI.Analysis.KadisonSimilarity.Representation.SpectralSteps

namespace OAI

/-! Derivation implementation and quantitative hyperreflexivity follow
from the uniform commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open Filter

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite cyclic column implementers, uniform commutator control and
Paulsen similarity give an implementer for the whole derivation. -/
theorem derivation_inner_of_finite_columns {l : Filter I} [l.NeBot]
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (δ : A →L[ℂ] (H →L[ℂ] H))
    (hδ : ∀ a b, δ (a * b) = (σ a).comp (δ b) + (δ a).comp (σ b))
    (P : VonNeumannAlgebra H) (hP : ∀ a, σ a ∈ P)
    (kaplansky : TwoVectorKaplanskyInput σ P)
    (columns : FiniteColumnImplementers σ δ l)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation σ σ δ hδ)) :
    ∃ V : H →L[ℂ] H, ∀ a, δ a = V.comp (σ a) - (σ a).comp V := by
  have hcb := derivation_completeBound_of_finite_columns σ δ P hP
    (scalarKaplanskyClosure_of_twoVector σ P kaplansky) columns hC estimate
  have hrect : RectangularCompleteBound δ (C * ‖δ‖) := hcb
  obtain ⟨V, hV, _⟩ := rectangular_inner_of_completeBound σ σ δ hδ
    (mul_nonneg hC (norm_nonneg δ)) hrect paulsen
  exact ⟨V, hV⟩

universe u

/-- The uniform commutator theorem implies quantitative hyperreflexivity
using spectral step approximation and Arveson's distance formula. -/
theorem universalHyperreflexivity_of_uniformCommutator
    {C : ℝ} (hC : 0 ≤ C) (estimate : UniformCommutatorEstimate.{u} C)
    (spectral : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (M : VonNeumannAlgebra K), SpectralStepApproximation M.commutant)
    (arveson : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (M : VonNeumannAlgebra K) (T : K →L[ℂ] K), ArvesonDistanceFormula M T) :
    UniversalHyperreflexivity.{u} C := by
  intro K _ _ _ M T
  exact hyperreflexivity_of_spectralSteps_and_arveson M (spectral K M) T hC
    (arveson K M T) (estimate K M.commutant)

end KadisonSimilarity

end

end OAI
