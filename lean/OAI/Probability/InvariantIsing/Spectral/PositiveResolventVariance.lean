import OAI.Probability.InvariantIsing.Spectral.PositiveResolventSpectrum

namespace OAI

/-! The dimension-explicit Gaussian quadratic variance bound for a positive resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace InvariantIsing

lemma positiveResolvent_quadratic_variance {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    variance (gaussianQuadraticForm (positiveResolvent t B)) (stdGaussian _) ≤ 2*N/t^2 := by
  rw [hermitianGaussianQuadratic_variance _ (positiveResolvent_posDef ht hB).isHermitian]
  have hs : (∑ i, ((positiveResolvent_posDef ht hB).isHermitian.eigenvalues i)^2) ≤
      (N : ℝ)*(1/t)^2 := by
    calc
      _ ≤ ∑ _ : Fin N, (1/t)^2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (positiveResolvent_eigenvalues ht hB i).1 (by positivity)).2
          (positiveResolvent_eigenvalues ht hB i).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  calc
    _ ≤ 2*((N : ℝ)*(1/t)^2) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

lemma positiveResolvent_normalized_variance {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) :
    variance (fun x => (1/(N : ℝ))*gaussianQuadraticForm (positiveResolvent t B) x) (stdGaussian _) ≤
      2/((N : ℝ)*t^2) := by
  rw [variance_const_mul]
  have h := mul_le_mul_of_nonneg_left (positiveResolvent_quadratic_variance ht hB) (sq_nonneg (1/(N : ℝ)))
  apply h.trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp [hn]

end InvariantIsing

end

end OAI
