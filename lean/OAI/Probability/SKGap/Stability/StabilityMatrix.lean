import Mathlib
import OAI.Probability.SKGap.Localization.DiagonalSum
import OAI.Probability.SKGap.Matrix.MatrixQuad

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
section GOEPath
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stabilityMatrix (a : ι → ℝ) (z q : ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k => (if i = k then 1 + z^2*q*a i else 0) - z*sqrt (a i)*M i k*sqrt (a k)

lemma stabilityMatrix_quad (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (z q : ℝ)
    (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad (stabilityMatrix a z q M) p =
      ‖p‖^2 + z^2*q*‖diagonalSqrt a p‖^2 - z*matrixQuad M (diagonalSqrt a p) := by
  rw [diagonalSqrt_norm_sq a ha, ← sum_coord_sq p]
  simp only [matrixQuad, stabilityMatrix, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  · simp only [Finset.mul_sum, diagonalSqrt]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

omit [Fintype ι] in
lemma stabilityMatrix_symm {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (a : ι → ℝ) (z q : ℝ) : (stabilityMatrix a z q M).IsHermitian := by
  ext i k
  have hmk : M k i = M i k := by simpa using congrFun (congrFun hM i) k
  simp only [Matrix.conjTranspose_apply, star_trivial, stabilityMatrix, hmk]
  by_cases h : i = k
  · subst k; rfl
  · simp only [h, Ne.symm h, ↓reduceIte]
    ring

lemma diagonalProcess_coercive {r z q c : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) {g : MatrixCoordinates ι → ℝ}
    (hg : diagonalProcess r a z q g ≤ 1-c) (p : EuclideanSpace ℝ ι) :
    c*‖p‖^2 ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p := by
  by_cases hp : p = 0
  · simp [hp, matrixQuad]
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  let v : EuclideanSpace ℝ ι := ‖p‖⁻¹ • p
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp0, inv_mul_cancel₀ hp0.ne']
  let v' : UnitBall ι := ⟨v, by simp [Metric.mem_closedBall, hv]⟩
  have h := (gaussianAffine_le_gaussianSup (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z) g v').trans hg
  rw [diagonal_affine_matrix] at h
  have hs := stabilityMatrix_quad a ha z q (goeMatrix r g) v
  change z*matrixQuad (goeMatrix r g) (diagonalSqrt a v) -
    z^2*q*‖diagonalSqrt a v‖^2 ≤ 1-c at h
  rw [hv, one_pow] at hs
  have hc : c ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) v := by linarith
  rw [show v = ‖p‖⁻¹ • p from rfl, matrixQuad_smul] at hc
  have hc' : c ≤ matrixQuad (stabilityMatrix a z q (goeMatrix r g)) p / ‖p‖^2 := by
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using hc
  exact (le_div_iff₀ (sq_pos_of_pos hp0)).mp hc'

variable [Nonempty ι]

theorem goe_diagonal_matrix_path_tail {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hsub : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤
      (1-sqrt j*A)^2/4) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ z ∈ Icc (0:ℝ) 1, ∃ p : EuclideanSpace ℝ ι,
        matrixQuad (stabilityMatrix a z ((j/(Fintype.card ι:ℝ))*∑ i, a i)
          (goeMatrix (j/(Fintype.card ι:ℝ)) g)) p < (1-sqrt j*A)^2/2 * ‖p‖^2} ≤
      Real.exp (-((1-sqrt j*A)^2)^2 * (Fintype.card ι:ℝ) / (16*π^2*j*A^2)) := by
  apply (measureReal_mono ?_).trans (scaled_diagonal_path_tail hj hA0 ha hA hsub herr)
  rintro g ⟨z, hz, p, hp⟩
  refine ⟨z, hz, ?_⟩
  by_contra hh
  have hc := diagonalProcess_coercive ha (le_of_not_gt hh) p
  exact (not_lt_of_ge hc) hp

end GOEPath
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
