import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare

namespace OAI

/-! Weighted Schur estimates for the prime-supported polynomials in Halász's
mean-value argument.  The weight occurs only once in the squared coefficient
sum, so a bound for the weighted frequency rows saves the extra logarithm
that an unrestricted integer mean-value theorem would lose. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset
open scoped BigOperators Classical

lemma halasz_weighted_symmetric_row_bound {ι : Type*} (S : Finset ι)
    (K : ι → ι → ℝ) (w v : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, w j * K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, (v i * w i) * (v j * w j) * K i j) ≤
      C * ∑ i ∈ S, (v i) ^ 2 * w i := by
  have he : (∑ i ∈ S, ∑ j ∈ S,
      ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j)) =
      ∑ i ∈ S, (v i) ^ 2 * w i * ∑ j ∈ S, w j * K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S)
      (f := fun i j => (v j) ^ 2 / 2 * (w i * w j * K i j))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hsymm j hj i hi]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hv : v i * v j ≤ ((v i) ^ 2 + (v j) ^ 2) / 2 := by
        nlinarith [sq_nonneg (v i - v j)]
      convert mul_le_mul_of_nonneg_right hv
        (mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hK i hi j hj)) using 1; ring
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * w i * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (mul_nonneg (sq_nonneg _) (hw i hi))
    _ = _ := by rw [← sum_mul, mul_comm]

/-- The weighted frequency-row version of the finite mean-value theorem.
The coefficients are `a i * w i`, and only one copy of `w` remains on the
right.  Zero weights are allowed. -/
theorem halasz_weighted_mean_square_of_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (w freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hrow : ∀ i ∈ S,
      ∑ j ∈ S, w j * (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t : ℝ, Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S (fun i => a i * (w i : ℂ)) freq t‖ ^ 2) ≤
      C * ∑ i ∈ S, ‖a i‖ ^ 2 * w i := by
  apply (mrt_weighted_mean_square_le S _ freq hT).trans
  have hn (i : ι) (hi : i ∈ S) : ‖a i * (w i : ℂ)‖ = ‖a i‖ * w i := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  have he : (∑ i ∈ S, ∑ j ∈ S, ‖a i * (w i : ℂ)‖ * ‖a j * (w j : ℂ)‖ *
      (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2))) =
      ∑ i ∈ S, ∑ j ∈ S, (‖a i‖ * w i) * (‖a j‖ * w j) *
      (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hn i hi, hn j hj]
  rw [he]
  apply halasz_weighted_symmetric_row_bound S _ w (fun i => ‖a i‖) C hw
    (fun _ _ _ _ => by positivity) _ hrow
  intro i _ j _
  rw [show (freq i - freq j) ^ 2 = (freq j - freq i) ^ 2 by ring]

/-- Unweighted time integration costs just the fixed factor `exp 1`. -/
theorem halasz_mean_square_of_weighted_rows {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (w freq : ι → ℝ) {T C : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hrow : ∀ i ∈ S,
      ∑ j ∈ S, w j * (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) ≤ C) :
    (∫ t in -T..T,
      ‖mrtExponentialPolynomial S (fun i => a i * (w i : ℂ)) freq t‖ ^ 2) ≤
      Real.exp 1 * C * ∑ i ∈ S, ‖a i‖ ^ 2 * w i := by
  apply (mrt_unweighted_mean_square_le S _ freq hT).trans
  calc
    _ ≤ Real.exp 1 * (C * ∑ i ∈ S, ‖a i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left
        (halasz_weighted_mean_square_of_rows S a w freq hT hw hrow) (Real.exp_pos _).le
    _ = _ := by ring

end TwoPointCorrelations

end OAI
