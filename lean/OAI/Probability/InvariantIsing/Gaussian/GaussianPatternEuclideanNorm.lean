import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternEigenvalueMeasurability

namespace OAI

/-! The Euclidean operator norm of the physical Gaussian array is 1-Lipschitz. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianPatternEuclideanOperator {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (gaussianPatternArray z).toEuclideanLin.toContinuousLinearMap

open scoped Matrix.Norms.Frobenius in
lemma gaussianPattern_frobenius {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ‖gaussianPatternArray z‖ = ‖z‖ := by
  rw [Matrix.frobenius_norm_def,PiLp.norm_eq_of_L2,Real.sqrt_eq_rpow]
  congr 1
  simp only [gaussianPatternArray,Fintype.sum_prod_type,Real.norm_eq_abs,Real.rpow_two, sq_abs]

open scoped Matrix.Norms.Frobenius in
lemma gaussianPatternEuclideanOperator_bound {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (x : EuclideanSpace ℝ (Fin m)) :
    ‖gaussianPatternEuclideanOperator z x‖ ≤ ‖z‖ * ‖x‖ := by
  have h := Matrix.frobenius_norm_mul (gaussianPatternArray z)
    (Matrix.replicateCol Unit (fun j => x j))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol,gaussianPattern_frobenius] at h
  exact h

lemma gaussianPatternEuclideanOperator_norm_le {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ‖gaussianPatternEuclideanOperator z‖ ≤ ‖z‖ :=
  (gaussianPatternEuclideanOperator z).opNorm_le_bound (norm_nonneg _)
    (gaussianPatternEuclideanOperator_bound z)

lemma gaussianPatternEuclideanOperator_sub {N m : ℕ}
    (z w : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternEuclideanOperator (z-w) =
      gaussianPatternEuclideanOperator z-gaussianPatternEuclideanOperator w := by
  unfold gaussianPatternEuclideanOperator
  rw [show gaussianPatternArray (z-w) = gaussianPatternArray z-gaussianPatternArray w from rfl,
    map_sub,map_sub]

def gaussianPatternSingularMax {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  ‖gaussianPatternEuclideanOperator z‖

theorem gaussianPatternSingularMax_lipschitz (N m : ℕ) :
    LipschitzWith 1 (gaussianPatternSingularMax (N := N) (m := m)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,gaussianPatternSingularMax]
  calc
    _ ≤ ‖gaussianPatternEuclideanOperator z-gaussianPatternEuclideanOperator w‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖gaussianPatternEuclideanOperator (z-w)‖ := by rw [gaussianPatternEuclideanOperator_sub]
    _ ≤ ‖z-w‖ := gaussianPatternEuclideanOperator_norm_le _

end InvariantIsing

end

end OAI
