import OAI.Probability.SLE.Angle.AngleEigenBasis

namespace OAI

/-! Explicit coefficient and supremum bounds for the monic cosine
eigenfunctions. Quadratic spectral decay will dominate this growth. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

lemma anglePolynomialEigenvalue_sub (κ : ℝ) (N k : ℕ) :
    anglePolynomialEigenvalue κ N-anglePolynomialEigenvalue κ k =
      ((N:ℝ)-(k:ℝ))*(1+(κ/8)*((N:ℝ)+(k:ℝ))) := by
  unfold anglePolynomialEigenvalue
  ring

lemma angleEigenCoefficient_ratio_bound {κ : ℝ} (hκ : 0<κ) {N k : ℕ} (hk : k<N) :
    |(κ/8)*((k:ℝ)+2)*((k:ℝ)+1)/
      (anglePolynomialEigenvalue κ k-anglePolynomialEigenvalue κ N)| ≤ (N:ℝ)+1 := by
  have hden := anglePolynomialEigenvalue_strictMono hκ hk
  have hdenp : 0<anglePolynomialEigenvalue κ N-anglePolynomialEigenvalue κ k :=
    sub_pos.mpr hden
  have hkN : (k:ℝ)+1≤(N:ℝ) := by exact_mod_cast hk
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg N
  have hnum : (κ/8)*((k:ℝ)+2)*((k:ℝ)+1) ≤ (κ/8)*((N:ℝ)+1)*(N:ℝ) := by
    apply mul_le_mul _ hkN (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hd : (κ/8)*(N:ℝ) ≤ anglePolynomialEigenvalue κ N-anglePolynomialEigenvalue κ k := by
    rw [anglePolynomialEigenvalue_sub]
    calc
      _ ≤ 1+(κ/8)*((N:ℝ)+(k:ℝ)) := by nlinarith
      _ ≤ ((N:ℝ)-(k:ℝ))*(1+(κ/8)*((N:ℝ)+(k:ℝ))) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
  rw [abs_div,abs_of_nonneg (by positivity),abs_of_neg (sub_neg.mpr hden),neg_sub]
  apply (div_le_iff₀ hdenp).mpr
  calc
    _ ≤ (κ/8)*((N:ℝ)+1)*(N:ℝ) := hnum
    _ = ((N:ℝ)+1)*((κ/8)*(N:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

lemma angleEigenCoefficient_abs_le {κ : ℝ} (hκ : 0<κ) (N k : ℕ) :
    |angleEigenCoefficient κ N k| ≤ ((N:ℝ)+1)^(N-k) := by
  have hN1 : 1≤(N:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
  by_cases he : k=N
  · subst k
    rw [angleEigenCoefficient_top]
    simp
  by_cases hk : k<N
  · by_cases hk2 : k+2≤N
    · have hi := angleEigenCoefficient_abs_le hκ N (k+2)
      conv_lhs => rw [angleEigenCoefficient]
      rw [ite_eq_right he,dite_eq_left hk,abs_mul]
      calc
        _ ≤ ((N:ℝ)+1)*((N:ℝ)+1)^(N-(k+2)) :=
          mul_le_mul (angleEigenCoefficient_ratio_bound hκ hk) hi (abs_nonneg _) (by positivity)
        _ = ((N:ℝ)+1)^(N-(k+2)+1) := by rw [pow_succ]; ring
        _ ≤ ((N:ℝ)+1)^(N-k) :=
          pow_le_pow_right₀ hN1 (by omega)
    · have hz : angleEigenCoefficient κ N (k+2)=0 := angleEigenCoefficient_above κ (by omega)
      conv_lhs => rw [angleEigenCoefficient]
      rw [ite_eq_right he,dite_eq_left hk,hz,mul_zero,abs_zero]
      positivity
  · rw [angleEigenCoefficient_above κ (by omega),abs_zero]
    positivity
termination_by N-k
  decreasing_by omega

lemma angleEigenPolynomial_eval_abs_le {κ : ℝ} (hκ : 0<κ) (N : ℕ) {x : ℝ} (hx : |x|≤1) :
    |(angleEigenPolynomial κ N).eval x| ≤ ((N:ℝ)+1)^(N+1) := by
  have hN1 : 1≤(N:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
  unfold angleEigenPolynomial
  rw [eval_finsetSum]
  calc
    _ ≤ ∑ k ∈ Finset.range (N+1), |(monomial k (angleEigenCoefficient κ N k)).eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (N+1), ((N:ℝ)+1)^N := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [eval_monomial,abs_mul,abs_pow]
      have hc := (angleEigenCoefficient_abs_le hκ N k).trans
        (pow_le_pow_right₀ hN1 (Nat.sub_le _ _))
      have hpow : |x|^k≤1 := pow_le_one₀ (abs_nonneg _) hx
      exact (mul_le_mul hc hpow (by positivity) (by positivity)).trans_eq (mul_one _)
    _ = ((N:ℝ)+1)^(N+1) := by simp [pow_succ,mul_comm]

end SLEExactGauge

end

end OAI
