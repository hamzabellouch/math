import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianCoordinates
import OAI.Probability.SKGap.Localization.QuadraticCoeff

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
namespace SKGap
section QuadraticComparison
variable {I ι : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype ι] [Nonempty ι]

theorem gaussian_quadraticSup_comparison {m : I → ℝ}
    {w : I → EuclideanSpace ℝ ι} (hm : Continuous m) (hw : Continuous w)
    {r : ℝ} (hr : 0 ≤ r) (z : ℝ) :
    (∫ g, gaussianSup m (fun i k => z * quadraticCoeff r (w i) k) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
    ∫ g, gaussianSup m (fun i k => z * linearCoeff r (w i) k) g
      ∂gaussianCoordinates (MatrixCoordinates ι) := by
  have hc {q : EuclideanSpace ℝ ι → MatrixCoordinates ι → ℝ} (hq : Continuous q) :
      Continuous (fun i k => z * q (w i) k) := by
    apply continuous_pi
    intro k
    exact continuous_const.mul ((continuous_apply k).comp (hq.comp hw))
  apply gaussianSup_comparison hm (hc (continuous_linearCoeff r))
    (hc (continuous_quadraticCoeff r))
  · intro i j
    simp_rw [← mul_sub]
    simp_rw [show ∀ k, (z * (linearCoeff r (w i) k - linearCoeff r (w j) k)) *
        (z * (quadraticCoeff r (w i) k - quadraticCoeff r (w j) k)) =
        z^2 * ((linearCoeff r (w i) k - linearCoeff r (w j) k) *
        (quadraticCoeff r (w i) k - quadraticCoeff r (w j) k)) by intros; ring]
    rw [← Finset.mul_sum, quadratic_linear_orthogonal, mul_zero]
  · intro i j
    simp_rw [← mul_sub, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (quadratic_linear_increment_le r hr (w i) (w j))
      (sq_nonneg z)
end QuadraticComparison
end SKGap

namespace SKGap
section SupLipschitz
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I] [Fintype κ]

lemma gaussianAffine_le_gaussianSup {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) (x : κ → ℝ) (i : I) :
    gaussianAffine m a x i ≤ gaussianSup m a x := by
  obtain ⟨j, hj, hmax⟩ := gaussianSup_attained hm ha x
  rw [hj]
  exact hmax i

lemma gaussianSup_sub_le {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) {L : ℝ}
    (hL : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) (x y : EuclideanSpace ℝ κ) :
    gaussianSup m a x.ofLp - gaussianSup m a y.ofLp ≤ L * ‖x-y‖ := by
  obtain ⟨i, hi, _⟩ := gaussianSup_attained hm ha x.ofLp
  calc
    _ ≤ gaussianAffine m a x.ofLp i - gaussianAffine m a y.ofLp i := by
      rw [hi]
      exact sub_le_sub_left (gaussianAffine_le_gaussianSup hm ha y.ofLp i) _
    _ = inner ℝ (WithLp.toLp 2 (a i)) (x-y) := by
      simp only [gaussianAffine, PiLp.inner_apply, WithLp.ofLp_sub,
        Pi.sub_apply, RCLike.inner_apply, conj_trivial]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ‖WithLp.toLp 2 (a i)‖ * ‖x-y‖ := real_inner_le_norm _ _
    _ ≤ L * ‖x-y‖ := mul_le_mul_of_nonneg_right (hL i) (norm_nonneg _)

theorem gaussianSup_lipschitz {m : I → ℝ} {a : I → κ → ℝ}
    (hm : Continuous m) (ha : Continuous a) {L : ℝ≥0}
    (hL : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ (L : ℝ)) :
    LipschitzWith L (fun x : EuclideanSpace ℝ κ => gaussianSup m a x.ofLp) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := gaussianSup_sub_le hm ha hL y x
    rw [norm_sub_rev] at h
    linarith
  · exact gaussianSup_sub_le hm ha hL x y

end SupLipschitz
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

end OAI
