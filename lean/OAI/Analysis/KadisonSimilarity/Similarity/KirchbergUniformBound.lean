import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergCompleteBound
import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergScalarDerivation
import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyDischarge

namespace OAI

/-! The quantitative conclusion of Kirchberg's Proposition 1: a uniform
complete bound for those homomorphisms already known to be similar. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kirchberg_uniform_completeBound {C : ℝ} (hC : 0 ≤ C)
    (estimate : UniformCommutatorEstimate.{v} C) (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 < M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    (hcb : IsCompletelyBounded π.1) :
    CompleteBound π.1 (Real.exp (C * (M + 1))) := by
  obtain ⟨t, σ, ht, he, hK⟩ := exists_exponential_similarity π hcb
  let P := representationVonNeumannAlgebra σ
  have hscalar : scalarCommutatorNorm P t ≤ M + 1 := by
    apply scalarKaplanskyClosure_of_twoVector σ P (twoVectorKaplanskyInput σ)
      t (M + 1) (by positivity)
    intro a
    apply kirchberg_commutator_bound σ t ht hM
    intro b
    simpa only [kirchbergPath, one_smul] using (he b ▸ hπ b)
  have hd : CompleteBound (fun a => commutator t (σ a)) (C * (M + 1)) := by
    intro n X
    exact (completeBound_commutator_of_estimate P hC (estimate H P) σ
      (mem_representationVonNeumannAlgebra σ) t n X).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar hC) (norm_nonneg _))
  have hk := kirchberg_completeNorm_le_exp π t σ ht he hK (by positivity) hd
  intro n X
  exact (completeBound_completeNorm hcb n X).trans
    (mul_le_mul_of_nonneg_right hk (norm_nonneg _))

end KadisonSimilarity

end

end OAI
