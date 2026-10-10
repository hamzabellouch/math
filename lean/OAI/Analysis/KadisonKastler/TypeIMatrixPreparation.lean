import OAI.Analysis.KadisonKastler.FullCornerPreparation
import OAI.Analysis.KadisonKastler.FullMatrixInjectivity
import OAI.Analysis.KadisonKastler.CommonMatrixPreparation
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.ProperInfiniteProjectionCopies

namespace OAI

/-! # Matrix preparation through the constructed type I algebra

Full countable matrix units generate an injective type I algebra directly.
The finite signed groups in its actual matrix corners construct the small
embedding directly. Neither the general amenable embedding nor the
increasing-matrix injectivity input is needed for this step.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [TopologicalSpace.SeparableSpace H] in
/-- The constructed embedding of the concrete matrix algebra makes its entries common. -/
theorem exists_common_typeI_matrix_preparation
    (M N : VonNeumannAlgebra H) (E : Submodule ℂ H) [CompleteSpace E]
    (F : FullMatrixCorner E) (hF : ∀ i j, F.entry i j ∈ M)
    {γ : ℝ} (hsmall : γ ≤ 1 / 1152) (hgap : kkDistance M N < γ) :
    ∃ a : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      (∀ i j, F.entry i j ∈ unitaryConjugateAlgebra (star a) N) ∧
      kkDistance M (unitaryConjugateAlgebra (star a) N) < 301 * γ ∧
      MatrixNearInclusion M (unitaryConjugateAlgebra (star a) N) (301 * γ) ∧
      MatrixNearInclusion (unitaryConjugateAlgebra (star a) N) M (301 * γ) := by
  obtain ⟨a, ha, hFN, hdist⟩ := F.exists_common_neighbor M N hF hsmall hgap
  have hd : kkDistance M (unitaryConjugateAlgebra (star a) N) < 301 * γ := by
    linarith
  refine ⟨a,ha,hFN,hd,?_,?_⟩
  · exact MatrixNearInclusion.of_common_matrix_units M _ E F hF hFN hd
  · exact MatrixNearInclusion.of_common_matrix_units _ M E F hFN hF
      (by simpa only [kkDistance_comm] using hd)

/-- Type III matrix preparation uses the constructed small embedding. -/
theorem exists_typeIII_matrix_preparation_of_embedding
    (M N : VonNeumannAlgebra H) (hM : TypeIIIFactor M)
    {γ : ℝ} (hsmall : γ ≤ 1 / 1152) (hgap : kkDistance M N < γ) :
    ∃ a : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      kkDistance M (unitaryConjugateAlgebra (star a) N) < 301 * γ ∧
      MatrixNearInclusion M (unitaryConjugateAlgebra (star a) N) (301 * γ) ∧
      MatrixNearInclusion (unitaryConjugateAlgebra (star a) N) M (301 * γ) := by
  obtain ⟨p,_hp,F,hF⟩ := hM.exists_fullMatrixCorner publishedTypeIIIProjectionComparison
  obtain ⟨a,ha,_hFN,hd,hMN,hNM⟩ :=
    exists_common_typeI_matrix_preparation M N (typeIIIInitialSpace p) F hF hsmall hgap
  exact ⟨a,ha,hd,hMN,hNM⟩

/-- Every properly infinite identity has the same constructed matrix preparation. -/
theorem exists_properInfinite_matrix_preparation_of_embedding
    (M N : VonNeumannAlgebra H) (hM : ProperlyInfiniteIdentity M)
    {γ : ℝ} (hsmall : γ ≤ 1 / 1152) (hgap : kkDistance M N < γ) :
    ∃ a : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      kkDistance M (unitaryConjugateAlgebra (star a) N) < 301 * γ ∧
      MatrixNearInclusion M (unitaryConjugateAlgebra (star a) N) (301 * γ) ∧
      MatrixNearInclusion (unitaryConjugateAlgebra (star a) N) M (301 * γ) := by
  let p : Generator.Tracial.AlgebraProjection M := ⟨1, IsStarProjection.one (Algebra M)⟩
  have hfull : (Generator.Tracial.centralSupport p).val = 1 := by
    have hp := Generator.Tracial.le_centralSupport p
    change (Generator.Tracial.centralSupport p).val * 1 = 1 at hp
    simpa only [mul_one] using hp
  obtain ⟨D⟩ := publishedProperInfiniteProjectionCopies H M hM p hfull
  obtain ⟨a,ha,_hFN,hd,hMN,hNM⟩ :=
    exists_common_typeI_matrix_preparation M N _ D.fullMatrixCorner
      D.fullMatrixCorner_mem hsmall hgap
  exact ⟨a,ha,hd,hMN,hNM⟩

end

end KadisonKastler

end OAI
