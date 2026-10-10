import OAI.Analysis.KadisonKastler.StateCentralizerVonNeumann
import OAI.Analysis.KadisonKastler.PointedSiteBalance
import OAI.Analysis.KadisonKastler.TwoRatioPointedConstruction
import OAI.Analysis.FactorGeneration.ProjectionLimits

namespace OAI

/-! # Small projections in the fixed product-state centralizer

The all-zero diagonal in a finite block of lambda sites is in the exact
state centralizer. Its trace is `(1 + lambda)⁻ⁿ`, hence tends to zero.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

theorem twoRatio_site_diagonal_mem_centralizer (i : TwoRatioSite) (a : Fin 2) :
    (S.site i).entry a a ∈ stateCentralizerVonNeumann (M := M) Ω := by
  refine ⟨?_,?_⟩
  · have hm := subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem a a))
    exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H =>
      (S.site i).entry a a ∈ N) S.generates) hm
  · intro b hb
    apply mul_left_cancel₀ (a := (twoSiteWeight (twoRatioSiteParameter i) a : ℂ))
    · have hp : 0 < twoRatioSiteParameter i := by
        rcases i with n | n
        · exact fixedProductLambda_pos
        · exact fixedProductMu_pos
      have hw : 0 < twoSiteWeight (twoRatioSiteParameter i) a := by
        unfold twoSiteWeight
        split_ifs <;> positivity
      exact_mod_cast ne_of_gt hw
    · exact S.twoRatio_site_balance i a a b hb

theorem twoRatio_block_zero_mem_centralizer (l : List TwoRatioSite) :
    S.blockEntry l (matrixSiteBlockZero l) (matrixSiteBlockZero l) ∈
      stateCentralizerVonNeumann (M := M) Ω := by
  induction l with
  | nil => exact (stateCentralizerVonNeumann (M := M) Ω).one_mem
  | cons i l ih =>
    exact (stateCentralizerVonNeumann (M := M) Ω).mul_mem
      (S.twoRatio_site_diagonal_mem_centralizer i 0) ih

def centralizerBlockZero (l : List TwoRatioSite) (hl : l.Nodup) :
    AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω) := by
  let E := S.finiteBlock l hl
  let z := matrixSiteBlockZero l
  refine ⟨⟨E.entry z z,S.twoRatio_block_zero_mem_centralizer l⟩,?_,?_⟩
  · exact Subtype.ext (E.diagonal_projection z).isIdempotentElem.eq
  · exact Subtype.ext (E.diagonal_projection z).isSelfAdjoint.star_eq

theorem centralizerBlockZero_trace (l : List TwoRatioSite) (hl : l.Nodup) :
    (stateCentralizerTrace Ω S.unit_vector S.separating).trace
      (S.centralizerBlockZero l hl).val =
      matrixSiteBlockWeight twoRatioSiteParameter l (matrixSiteBlockZero l)
        (matrixSiteBlockZero l) := S.blockEntry_moment l hl _ _

theorem lambda_block_zero_weight (l : List ℕ) :
    matrixSiteBlockWeight twoRatioSiteParameter (l.map Sum.inl)
      (matrixSiteBlockZero _) (matrixSiteBlockZero _) =
      ((((1+fixedProductLambda)⁻¹ : ℝ)^l.length : ℝ) : ℂ) := by
  induction l with
  | nil => change (1 : ℂ) = ((1 : ℝ) : ℂ); exact_mod_cast rfl
  | cons i l ih =>
    change (((1+fixedProductLambda)⁻¹ : ℝ) : ℂ) *
      matrixSiteBlockWeight twoRatioSiteParameter (l.map Sum.inl)
        (matrixSiteBlockZero _) (matrixSiteBlockZero _) =
      ((((1+fixedProductLambda)⁻¹ : ℝ)^(l.length+1) : ℝ) : ℂ)
    rw [ih,pow_succ,Complex.ofReal_mul]
    exact mul_comm _ _

/-- Nonzero exact centralizer projections with arbitrarily small faithful trace. -/
theorem exists_small_centralizer_projection (ε : ℝ) (hε : 0 < ε) :
    ∃ p : AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω),
      p.val ≠ 0 ∧
      ((stateCentralizerTrace Ω S.unit_vector S.separating).trace p.val).re < ε := by
  classical
  have hr : 0 < (1+fixedProductLambda)⁻¹ :=
    inv_pos.mpr (by linarith [fixedProductLambda_pos])
  have hr1 : (1+fixedProductLambda)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by linarith [fixedProductLambda_pos])]
    linarith [fixedProductLambda_pos]
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1
  have he : ∀ᶠ n : ℕ in atTop, ((1+fixedProductLambda)⁻¹ : ℝ)^n < ε :=
    ht (Iio_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  let l : List TwoRatioSite := (List.range n).map Sum.inl
  have hl : l.Nodup := List.nodup_range.map Sum.inl_injective
  let p := S.centralizerBlockZero l hl
  have hp : (stateCentralizerTrace Ω S.unit_vector S.separating).trace p.val =
      ((((1+fixedProductLambda)⁻¹ : ℝ)^n : ℝ) : ℂ) := by
    rw [S.centralizerBlockZero_trace]
    simpa only [l,List.length_range] using lambda_block_zero_weight (List.range n)
  refine ⟨p,?_,?_⟩
  · intro hz
    have hh := hp
    rw [hz] at hh
    change inner ℂ Ω ((0 : H →L[ℂ] H) Ω) = _ at hh
    simp only [zero_apply,inner_zero_right] at hh
    have hnz : ((((1+fixedProductLambda)⁻¹ : ℝ)^n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (pow_pos hr n)
    exact hnz hh.symm
  · rw [hp,Complex.ofReal_re]
    exact hn

end PointedMatrixSites

end

end KadisonKastler

end OAI
