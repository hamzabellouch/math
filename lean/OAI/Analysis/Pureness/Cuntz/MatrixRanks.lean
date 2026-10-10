import OAI.Analysis.Pureness.Cuntz.MatrixDiagonal

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma matrixRank_ne_top (τ : TracialState A) (M : CStarMatrix ι ι A) (hM : 0 ≤ M) :
    matrixRank τ M ≠ ∞ := by
  apply ENNReal.mul_ne_top (by simp)
  exact ne_of_lt ((normalizedRootRank_le_one (matrixTracialState τ) M hM).trans_lt
    ENNReal.one_lt_top)

lemma matrixRank_toReal (τ : TracialState A) (M : CStarMatrix ι ι A) :
    (matrixRank τ M).toReal =
      (Fintype.card ι : ℝ) * (normalizedRootRank (matrixTracialState τ) M).toReal := by
  simp [matrixRank, ENNReal.toReal_mul]

lemma matrixTracialState_scale (τ : TracialState A) (M : CStarMatrix ι ι A) :
    (Fintype.card ι : ℝ) * ((matrixTracialState τ).functional M).re =
      (matrixTrace τ M).re := by
  have heq : (Fintype.card ι : ℂ) * (matrixTracialState τ).functional M = matrixTrace τ M := by
    change (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ)⁻¹ * matrixTrace τ M) = _
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
  have hr := congrArg Complex.re heq
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using hr

lemma matrixPower_trace_tendsto_realRank (τ : TracialState A)
    (M : CStarMatrix ι ι A) (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ => (matrixTrace τ (positivePower M (((n : ℝ≥0) + 1)⁻¹))).re)
      atTop (𝓝 (matrixRank τ M).toReal) := by
  rw [matrixRank_toReal]
  have ht := (positivePower_trace_tendsto (matrixTracialState τ) M hM).const_mul (Fintype.card ι : ℝ)
  simpa only [matrixTracialState_scale] using ht

theorem matrixPower_trace_tendsto_rank (τ : TracialState A)
    (M : CStarMatrix ι ι A) (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (matrixTrace τ (positivePower M (((n : ℝ≥0) + 1)⁻¹))).re)
      atTop (𝓝 (matrixRank τ M)) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (matrixPower_trace_tendsto_realRank τ M hM)
  rw [ENNReal.ofReal_toReal (matrixRank_ne_top τ M hM)] at ht
  exact ht

theorem matrixRank_diagonal_toReal (τ : TracialState A) (a : ι → A)
    (ha : ∀ i, 0 ≤ a i) :
    (matrixRank τ (diagonalMatrixHom a)).toReal = ∑ i, (normalizedRootRank τ (a i)).toReal := by
  have hmatrix := matrixPower_trace_tendsto_realRank τ (diagonalMatrixHom a)
    (diagonalMatrix_nonneg a ha)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => positivePower_trace_tendsto τ (a i) (ha i))
  apply tendsto_nhds_unique hmatrix
  convert hsum using 1
  funext n
  rw [matrixTrace_positivePower_diagonal τ a ha _ (by positivity), Complex.re_sum]
end CuntzPureness

end OAI
