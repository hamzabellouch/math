import OAI.NumberTheory.CubicMoment.Estimates.MeanValueGaussianRows

namespace OAI

/-! Gaussian mean square of the actual integer-frequency polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def meanValueGaussianWeight (L t : ℝ) : ℝ := Real.exp (-(t/L)^2)

lemma meanValueGaussian_phase_product (L t x y : ℝ) :
    (meanValueGaussianWeight L t:ℂ)*mellinPhase t x*star (mellinPhase t y) =
      meanValueGaussianPhase L (Real.log x-Real.log y) t := by
  simp only [← starRingEnd_apply]
  simp only [meanValueGaussianWeight,meanValueGaussianPhase,mellinPhase,
    Complex.ofReal_exp,← Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma meanValueGaussian_expansion (Z : ℕ) (v : ℕ → ℂ) (L t : ℝ) :
    ((meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2:ℝ):ℂ) =
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t := by
  rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
  unfold integerNormPolynomial
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [← meanValueGaussian_phase_product]
  simp only [starRingEnd_apply]
  ring

lemma meanValueGaussian_integrable {L : ℝ} (hL : 0 < L) (Z : ℕ) (v : ℕ → ℂ) :
    Integrable (fun t : ℝ => meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) := by
  have hi : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t) := by
    apply integrable_finsetSum
    intro n hn
    apply integrable_finsetSum
    intro m hm
    exact (meanValueGaussianPhase_integrable hL _).const_mul _
  have he : (fun t : ℝ => meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) =
      fun t => (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        (v n*star (v m))*meanValueGaussianPhase L
          (Real.log (n:ℝ)-Real.log (m:ℝ)) t).re := by
    funext t
    rw [← meanValueGaussian_expansion]
    rfl
  rw [he]
  exact hi.re

lemma meanValueGaussian_integral_bound {L : ℝ} (hL : 0 < L)
    (Z : ℕ) (v : ℕ → ℂ) :
    (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) ≤
      L*Real.sqrt Real.pi * ∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
        ‖v n‖*‖v m‖*Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4) := by
  let S := Finset.Icc 1 Z
  have he : Complex.ofReal (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) =
      ∑ n ∈ S, ∑ m ∈ S, (v n*star (v m))*
        ∫ t : ℝ, meanValueGaussianPhase L (Real.log (n:ℝ)-Real.log (m:ℝ)) t := by
    rw [← integral_complex_ofReal]
    simp_rw [meanValueGaussian_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro m hm
        exact integral_const_mul _ _
      · intro m hm
        exact (meanValueGaussianPhase_integrable hL _).const_mul _
    · intro n hn
      apply integrable_finsetSum
      intro m hm
      exact (meanValueGaussianPhase_integrable hL _).const_mul _
  have h0 : 0 ≤ ∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2 :=
    integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  calc
    _ = ‖Complex.ofReal (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
    _ ≤ ∑ n ∈ S, ∑ m ∈ S,
        ‖(v n*star (v m))*∫ t : ℝ,
          meanValueGaussianPhase L (Real.log (n:ℝ)-Real.log (m:ℝ)) t‖ := by
      rw [he]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => norm_sum_le _ _))
    _ = _ := by
      simp only [norm_mul,norm_star,meanValueGaussianPhase_integral_norm hL]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

lemma gaussian_schur_bound {Z : ℕ} {L : ℝ} (hL : (Z:ℝ) ≤ L) (v : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 Z, ∑ m ∈ Finset.Icc 1 Z,
      ‖v n‖*‖v m‖*Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)) ≤
      (2/(1-Real.exp (-(1/4:ℝ))))*∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
  let S := Finset.Icc 1 Z
  let K := fun n m : ℕ => Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)
  have hsym : ∀ n m, K n m = K m n := by
    intro n m
    dsimp [K]
    congr 1
    ring
  have hrow : ∀ n ∈ S, ∑ m ∈ S, K n m ≤ 2/(1-Real.exp (-(1/4:ℝ))) :=
    fun n hn => gaussian_log_frequency_row_bound hn hL
  have hcol : (∑ n ∈ S, ∑ m ∈ S, ‖v m‖^2*K n m) =
      ∑ n ∈ S, ∑ m ∈ S, ‖v n‖^2*K n m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [hsym]
  have he : (∑ n ∈ S, ∑ m ∈ S, (‖v n‖^2+‖v m‖^2)*K n m) =
      2*∑ n ∈ S, ‖v n‖^2*(∑ m ∈ S, K n m) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have hpair : 2*(∑ n ∈ S, ∑ m ∈ S, ‖v n‖*‖v m‖*K n m) ≤
      ∑ n ∈ S, ∑ m ∈ S, (‖v n‖^2+‖v m‖^2)*K n m := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro m hm
    have hp : 2*‖v n‖*‖v m‖ ≤ ‖v n‖^2+‖v m‖^2 := by nlinarith [sq_nonneg (‖v n‖-‖v m‖)]
    exact (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
  have htotal : (∑ n ∈ S, ‖v n‖^2*(∑ m ∈ S, K n m)) ≤
      (2/(1-Real.exp (-(1/4:ℝ))))*∑ n ∈ S, ‖v n‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg ‖v n‖)
  change (∑ n ∈ S, ∑ m ∈ S, ‖v n‖*‖v m‖*K n m) ≤ _
  rw [he] at hpair
  linarith

 theorem integerNormPolynomial_gaussian_meanSquare {Z : ℕ} {L : ℝ}
    (hL : 0 < L) (hZL : (Z:ℝ) ≤ L) (v : ℕ → ℂ) :
    (∫ t : ℝ, meanValueGaussianWeight L t*‖integerNormPolynomial Z v t‖^2) ≤
      (L*Real.sqrt Real.pi*(2/(1-Real.exp (-(1/4:ℝ)))))*
        ∑ n ∈ Finset.Icc 1 Z, ‖v n‖^2 := by
  exact (meanValueGaussian_integral_bound hL Z v).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_schur_bound hZL v)
      (mul_nonneg hL.le (Real.sqrt_nonneg _)))

end CubicFirstMoment

end

end OAI
