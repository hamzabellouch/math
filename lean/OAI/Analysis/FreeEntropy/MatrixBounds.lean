import OAI.Analysis.FreeEntropy.MatrixPolynomial

namespace OAI

noncomputable section
open scoped ENNReal
open Finset MeasureTheory Set
namespace FiniteEntropySeparation
 theorem matrixOpNorm_continuous {d : ℕ} : Continuous (matrixOpNorm (d := d)) := by
  exact ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin d) (n := Fin d)).trans
    LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional.norm
 theorem matrix_column_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    (∑ j, Complex.normSq (A j k)) ≤ matrixOpNorm A ^ 2 := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have he : T (EuclideanSpace.single k 1) = WithLp.toLp 2 (fun j => A j k) := by
    change Matrix.toEuclideanLin A (EuclideanSpace.single k 1) = _
    rw [Matrix.toLpLin_apply]
    congr 1
    simp [EuclideanSpace.single, Matrix.mulVec_single, Matrix.col, Matrix.transpose]
    rfl
  have hb := T.le_opNorm (EuclideanSpace.single k 1)
  rw [he, PiLp.norm_single, norm_one, mul_one] at hb
  have hn : ‖WithLp.toLp 2 (fun j => A j k)‖^2 = ∑ j, Complex.normSq (A j k) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Complex.normSq_eq_norm_sq]
  rw [← hn]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2
 theorem matrix_frobenius_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Complex.normSq (A j k)) ≤ (d : ℝ) * matrixOpNorm A ^ 2 := by
  rw [sum_comm]
  simpa using sum_le_sum (s := (univ : Finset (Fin d))) (fun k _ => matrix_column_bound A k)
 theorem coordinates_sq_bound {n d : ℕ} (a : MatrixCoordinates n d) (R : ℝ)
    (hR : 0 ≤ R) (ha : ∀ i, matrixOpNorm (hermitianMatrix a i) ≤ R) :
    ‖a‖^2 ≤ (n : ℝ)*d*R^2 := by
  rw [← hermitianChart_normSq]
  calc
    _ ≤ ∑ i : Fin n, (d : ℝ) * matrixOpNorm (hermitianMatrix a i)^2 :=
      sum_le_sum (fun i _ => matrix_frobenius_bound _)
    _ ≤ ∑ _i : Fin n, (d : ℝ)*R^2 := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hR).mpr (ha i)) (Nat.cast_nonneg d))
    _ = _ := by simp; ring
 theorem microstates_measurable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (m d : ℕ) (ε : ℝ) : MeasurableSet (microstates τ X R m d ε) := by
  simp only [microstates, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (matrixOpNorm_continuous.comp (hermitianMatrix_continuous i)) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro w
    apply MeasurableSet.iInter
    intro hw
    exact (isOpen_lt (((matrixMoment_continuous w).sub continuous_const).norm) continuous_const).measurableSet
 theorem microstates_subset_closedBall {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (hR : 0 ≤ R) (m d : ℕ) (ε : ℝ) :
    microstates τ X R m d ε ⊆ Metric.closedBall 0 (Real.sqrt ((n : ℝ)*d) * R) := by
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  have hb := coordinates_sq_bound a R hR ha.1
  have he : (Real.sqrt ((n : ℝ)*d) * R)^2 = (n : ℝ)*d*R^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hn : 0 ≤ Real.sqrt ((n : ℝ)*d) * R := by positivity
  nlinarith [norm_nonneg a]
 theorem microstates_volume_lt_top {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (hR : 0 ≤ R) (m d : ℕ) (ε : ℝ) : volume (microstates τ X R m d ε) < ⊤ :=
  (measure_mono (microstates_subset_closedBall τ X R hR m d ε)).trans_lt
    (isCompact_closedBall (0 : MatrixCoordinates n d) _).measure_lt_top
end FiniteEntropySeparation

end

end OAI
