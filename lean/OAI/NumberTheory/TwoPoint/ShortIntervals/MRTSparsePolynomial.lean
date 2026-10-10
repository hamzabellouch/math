import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseGram

namespace OAI

/-! The sparse Gram bound for the actual finite exponential polynomial.
The optional nonnegative weight permits a smooth integer majorant. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical ComplexConjugate

theorem mrt_sparse_polynomial_energy {ι : Type*} (K : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (S : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ t ∈ S, ∑ s ∈ S,
      ‖mrtExponentialPolynomial K (fun _ => 1) freq (t-s)‖ ≤ B) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K a freq t‖^2) ≤
      B * ∑ n ∈ K, ‖a n‖^2 := by
  let A := fun t n => Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I)
  have hp (t s : ℝ) : (∑ n ∈ K, A t n * conj (A s n)) =
      mrtExponentialPolynomial K (fun _ => 1) freq (t-s) := by
    apply sum_congr rfl
    intro n _
    dsimp only [A, mrtExponentialPolynomial]
    rw [mrt_phase_pair, one_mul]
    rw [show freq n*t-freq n*s = freq n*(t-s) by ring]
  have he (t : ℝ) : (∑ n ∈ K, A t n*a n) =
      mrtExponentialPolynomial K a freq t := by
    apply sum_congr rfl
    intro n _
    exact mul_comm _ _
  have hr : ∀ t ∈ S, ∑ s ∈ S, ‖∑ n ∈ K, A t n*conj (A s n)‖ ≤ B := by
    simpa only [hp] using hrow
  simpa only [he] using mrt_finite_matrix_gram S K A a hB hr

theorem mrt_sparse_weighted_polynomial_energy {ι : Type*} (K : Finset ι)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (S : Finset ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ t ∈ S, ∑ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤ B) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t‖^2) ≤
      B * ∑ n ∈ K, w n*‖a n‖^2 := by
  let A := fun t n => (Real.sqrt (w n):ℂ)*Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I)
  let b := fun n => (Real.sqrt (w n):ℂ)*a n
  have hs (n : ι) (hn : n ∈ K) : (Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ) = w n := by
    exact_mod_cast Real.mul_self_sqrt (hw n hn)
  have hp (t s : ℝ) : (∑ n ∈ K, A t n * conj (A s n)) =
      mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s) := by
    apply sum_congr rfl
    intro n hn
    dsimp only [A, mrtExponentialPolynomial]
    rw [map_mul, conj_ofReal]
    calc
      _ = ((Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ)) *
          (Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I) *
            conj (Complex.exp (((freq n*s:ℝ):ℂ)*Complex.I))) := by ring
      _ = _ := by
        rw [hs n hn, mrt_phase_pair]
        rw [show freq n*t-freq n*s = freq n*(t-s) by ring]
  have he (t : ℝ) : (∑ n ∈ K, A t n*b n) =
      mrtExponentialPolynomial K (fun n => (w n:ℂ)*a n) freq t := by
    apply sum_congr rfl
    intro n hn
    dsimp only [A, b, mrtExponentialPolynomial]
    calc
      _ = ((Real.sqrt (w n):ℂ)*(Real.sqrt (w n):ℂ))*a n*
          Complex.exp (((freq n*t:ℝ):ℂ)*Complex.I) := by ring
      _ = _ := by rw [hs n hn]
  have hm : (∑ n ∈ K, ‖b n‖^2) = ∑ n ∈ K, w n*‖a n‖^2 := by
    apply sum_congr rfl
    intro n hn
    simp only [b, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw n hn)]
  have hr : ∀ t ∈ S, ∑ s ∈ S, ‖∑ n ∈ K, A t n*conj (A s n)‖ ≤ B := by
    simpa only [hp] using hrow
  simpa only [he, hm] using mrt_finite_matrix_gram S K A b hB hr

end TwoPointCorrelations

end OAI
