import OAI.Analysis.KadisonKastler.CommonMatrixPreparation
import OAI.Analysis.KadisonKastler.PublishedProperInfiniteProjection

namespace OAI

/-! # Matrix preparation for a properly infinite identity -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Countable copies of the identity yield the infinite matrix corner
needed by the common-matrix preparation. -/
theorem exists_properInfinite_matrix_preparation
    (hCopies : PublishedProperInfiniteProjectionCopies.{u})
    (hAFD : PublishedIncreasingMatrixInjectivity (H := H))
    (hEmbed : PublishedAmenableEmbedding (H := H))
    (M N : VonNeumannAlgebra H) (hM : ProperlyInfiniteIdentity M)
    {γ : ℝ} (hsmall : γ < 1 / 100) (hgap : kkDistance M N < γ) :
    ∃ a : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      kkDistance M (unitaryConjugateAlgebra (star a) N) < 301 * γ ∧
      MatrixNearInclusion M (unitaryConjugateAlgebra (star a) N) (301 * γ) ∧
      MatrixNearInclusion (unitaryConjugateAlgebra (star a) N) M (301 * γ) := by
  let p : AlgebraProjection M := ⟨1, IsStarProjection.one (Algebra M)⟩
  have hfull : (centralSupport p).val = 1 := by
    have hp := le_centralSupport p
    change (centralSupport p).val * 1 = 1 at hp
    simpa only [mul_one] using hp
  obtain ⟨D⟩ := hCopies H M hM p hfull
  obtain ⟨a, ha, _hFN, hd, hMN, hNM⟩ :=
    exists_common_matrix_preparation hAFD hEmbed M N _ D.fullMatrixCorner
      D.fullMatrixCorner_mem hsmall hgap
  exact ⟨a, ha, hd, hMN, hNM⟩

end

end KadisonKastler

end OAI
