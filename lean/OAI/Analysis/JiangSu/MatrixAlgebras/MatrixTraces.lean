import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.SourceRankLimit

namespace OAI

namespace Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [StarOrderedRing A] [DecidableEq ι] in
@[simp] lemma matrixTraceLinear_apply (τ : TracialState A) (M : CStarMatrix ι ι A) :
    matrixTraceLinear τ M = ∑ i, τ.functional (M i i) := rfl

lemma matrixTrace_one (τ : TracialState A) :
    matrixTrace τ (1 : CStarMatrix ι ι A) = (Fintype.card ι : ℂ) := by
  simp [matrixTrace_apply, CStarMatrix.one_apply_eq, τ.normalized]

noncomputable def matrixTracialState [Nonempty ι] (τ : TracialState A) :
    TracialState (CStarMatrix ι ι A) where
  functional :=
    { ((Fintype.card ι : ℂ)⁻¹ • (matrixTrace τ).toLinearMap) with
      monotone' := by
        intro M N hMN
        change (Fintype.card ι : ℂ)⁻¹ * matrixTrace τ M ≤
          (Fintype.card ι : ℂ)⁻¹ * matrixTrace τ N
        exact mul_le_mul_of_nonneg_left ((matrixTrace τ).monotone hMN) (by positivity) }
  normalized := by
    change (Fintype.card ι : ℂ)⁻¹ * matrixTrace τ 1 = 1
    rw [matrixTrace_one, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]
  tracial M N := by
    change (Fintype.card ι : ℂ)⁻¹ * matrixTrace τ (M * N) =
      (Fintype.card ι : ℂ)⁻¹ * matrixTrace τ (N * M)
    rw [matrixTrace_tracial]

noncomputable def matrixRank [Nonempty ι] (τ : TracialState A) (M : CStarMatrix ι ι A) : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞) * normalizedRootRank (matrixTracialState τ) M

end Pureness

namespace Pureness
open Filter Topology
open scoped NNReal ENNReal ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

noncomputable def positivePower (a : A) (r : ℝ≥0) : A := CFC.nnrpow a r

lemma positivePower_map (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a)
    (r : ℝ≥0) (hr : 0 < r) : positivePower (φ a) r = φ (positivePower a r) := by
  have hb := starAlgHom_positive φ a ha
  simp only [positivePower, CFC.nnrpow_eq_pow,
    CFC.nnrpow_eq_cfcₙ_real a r ha, CFC.nnrpow_eq_cfcₙ_real (φ a) r hb]
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  rw [cfcₙ_eq_cfc (hf0 := hf0), cfcₙ_eq_cfc (hf0 := hf0)]
  exact (φ.map_cfc _ a (Real.continuous_rpow_const (by positivity)).continuousOn
    (map_continuous φ) ha.isSelfAdjoint hb.isSelfAdjoint).symm

lemma positivePower_trace_tendsto (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (τ.functional (positivePower a (((n : ℝ≥0) + 1)⁻¹))).re)
      atTop (𝓝 (normalizedRootRank τ a).toReal) := by
  have hfinite : normalizedRootRank τ a ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ a ha).trans_lt ENNReal.one_lt_top)
  have ht := (ENNReal.tendsto_toReal hfinite).comp (source_root_trace_tendsto_rank τ a ha)
  exact ht.congr' (Eventually.of_forall fun n => ENNReal.toReal_ofReal
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg CFC.nnrpow_nonneg)).1)

end Pureness

namespace Pureness
open scoped ComplexOrder ENNReal NNReal
open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonalMatrix_nonneg (a : ι → A) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ diagonalMatrixHom a := by
  exact starAlgHom_positive diagonalMatrixHom a ha

lemma positivePower_diagonal (a : ι → A) (ha : ∀ i, 0 ≤ a i)
    (r : ℝ≥0) (hr : 0 < r) :
    positivePower (diagonalMatrixHom a) r =
      diagonalMatrixHom (fun i => positivePower (a i) r) := by
  rw [positivePower_map diagonalMatrixHom a ha r hr]
  congr 1
  exact CFC.nnrpow_map_pi ha

lemma matrixTrace_positivePower_diagonal (τ : TracialState A) (a : ι → A)
    (ha : ∀ i, 0 ≤ a i) (r : ℝ≥0) (hr : 0 < r) :
    matrixTrace τ (positivePower (diagonalMatrixHom a) r) =
      ∑ i, τ.functional (positivePower (a i) r) := by
  rw [positivePower_diagonal a ha r hr]
  simp only [matrixTrace_apply, diagonalMatrixHom_apply, ite_true]

end Pureness

end OAI
