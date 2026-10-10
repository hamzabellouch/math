import OAI.Analysis.Pureness.Divisibility.SourceRankLimit
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma positive_square_factor (a : A) (ha : 0 ≤ a) : ∃ x : A, star x * x = a := by
  refine ⟨CFC.sqrt a, ?_⟩
  rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]

noncomputable def matrixTraceLinear (τ : TracialState A) : CStarMatrix ι ι A →ₗ[ℂ] ℂ where
  toFun M := ∑ i, τ.functional (M i i)
  map_add' M N := by simp [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' z M := by simp [CStarMatrix.smul_apply, Finset.mul_sum]

omit [StarOrderedRing A] [DecidableEq ι] in
@[simp] lemma matrixTraceLinear_apply (τ : TracialState A) (M : CStarMatrix ι ι A) :
    matrixTraceLinear τ M = ∑ i, τ.functional (M i i) := rfl

lemma matrix_entry_nonneg (M : CStarMatrix ι ι A) (hM : 0 ≤ M) (i : ι) : 0 ≤ M i i := by
  obtain ⟨x, hs⟩ := positive_square_factor M hM
  rw [← hs, CStarMatrix.mul_apply]
  exact Finset.sum_nonneg fun j _ => by
    rw [CStarMatrix.star_apply]
    exact star_mul_self_nonneg _

noncomputable def matrixTrace (τ : TracialState A) : CStarMatrix ι ι A →ₚ[ℂ] ℂ :=
  { matrixTraceLinear τ with
    monotone' := by
      intro M N hMN
      apply sub_nonneg.mp
      change 0 ≤ matrixTraceLinear τ N - matrixTraceLinear τ M
      rw [← map_sub]
      exact Finset.sum_nonneg fun i _ => τ.functional.map_nonneg
        (matrix_entry_nonneg (N - M) (sub_nonneg.mpr hMN) i) }

@[simp] lemma matrixTrace_apply (τ : TracialState A) (M : CStarMatrix ι ι A) :
    matrixTrace τ M = ∑ i, τ.functional (M i i) := rfl

lemma matrixTrace_one (τ : TracialState A) :
    matrixTrace τ (1 : CStarMatrix ι ι A) = (Fintype.card ι : ℂ) := by
  simp [matrixTrace_apply, CStarMatrix.one_apply_eq, τ.normalized]

lemma matrixTrace_tracial (τ : TracialState A) (M N : CStarMatrix ι ι A) :
    matrixTrace τ (M * N) = matrixTrace τ (N * M) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  exact τ.tracial _ _

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
end CuntzPureness

end OAI
