import OAI.Probability.InvariantIsing.Spectral.PositiveResolventSpectrum

namespace OAI

/-! Uniform trace and quadratic bounds for positive resolvents. -/
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace InvariantIsing

lemma positiveResolvent_trace_le {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    (positiveResolvent t B).trace ≤ (N : ℝ)/t := by
  have he := (positiveResolvent_posDef ht hB).isHermitian.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id,id_eq] at he
  rw [he]
  calc
    _ ≤ ∑ _ : Fin N, 1/t := Finset.sum_le_sum (fun i _ => (positiveResolvent_eigenvalues ht hB i).2)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma positiveResolvent_quadratic_le {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : EuclideanSpace ℝ (Fin N)) :
    gaussianQuadraticForm (positiveResolvent t B) x ≤ ‖x‖^2/t := by
  let hR := (positiveResolvent_posDef ht hB).isHermitian
  rw [gaussianQuadraticForm,hermitian_quadratic_coordinates _ hR]
  calc
    _ ≤ ∑ i, (1/t)*(hR.eigenvectorBasis.repr x i)^2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (positiveResolvent_eigenvalues ht hB i).2 (sq_nonneg _))
    _ = (1/t)*‖hR.eigenvectorBasis.repr x‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

lemma positiveResolvent_quadratic_nonneg {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : EuclideanSpace ℝ (Fin N)) :
    0 ≤ gaussianQuadraticForm (positiveResolvent t B) x := by
  rw [gaussianQuadraticForm,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  exact (positiveResolvent_posDef ht hB).posSemidef.dotProduct_mulVec_nonneg x.ofLp

lemma positiveResolvent_normalized_abs_bound {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : EuclideanSpace ℝ (Fin N)) :
    |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x-
      (positiveResolvent t B).trace/N| ≤ (1/((N : ℝ)*t))*‖x‖^2+1/t := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := positiveResolvent_quadratic_nonneg ht hB x
  have htr := (positiveResolvent_posDef ht hB).posSemidef.trace_nonneg
  calc
    _ ≤ |(1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x|+
        |(positiveResolvent t B).trace/N| := abs_sub _ _
    _ = (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x+
        (positiveResolvent t B).trace/N := by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    _ ≤ (1/(N : ℝ))*(‖x‖^2/t)+((N : ℝ)/t)/N := add_le_add
      (mul_le_mul_of_nonneg_left (positiveResolvent_quadratic_le ht hB x) (by positivity))
      (div_le_div_of_nonneg_right (positiveResolvent_trace_le ht hB) hn.le)
    _ = _ := by field_simp

end InvariantIsing

end

end OAI
