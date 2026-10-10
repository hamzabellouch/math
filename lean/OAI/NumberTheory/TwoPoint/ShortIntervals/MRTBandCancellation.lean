import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! The elementary band cancellation in corrected MRT, Appendix A,
Lemma A.8 and equation (A.12). -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

lemma mrt_exp_sub_square_monotone : Monotone (fun x : ℝ => Real.exp x - x ^ 2) := by
  apply monotone_of_hasDerivAt_nonneg
    (f' := fun x => Real.exp x - 2 * x)
  · intro x
    convert (Real.hasDerivAt_exp x).sub ((hasDerivAt_id x).pow 2) using 1 <;>
      first | rfl | norm_num
  · intro x
    exact sub_nonneg.mpr Real.two_mul_le_exp

/-- Corrected MRT Lemma A.8, proved using the monotonicity of
`exp x - x²` rather than a second derivative at a square root. -/
theorem mrt_exp_cos_inequality (a θ : ℝ) :
    Real.exp a + Real.exp (-a) - 2 * Real.cos θ ≤
      Real.exp (Real.sqrt (a ^ 2 + θ ^ 2)) := by
  have hs : 0 ≤ a ^ 2 + θ ^ 2 := by positivity
  have ha : |a| ≤ Real.sqrt (a ^ 2 + θ ^ 2) :=
    Real.le_sqrt_of_sq_le (by rw [sq_abs]; nlinarith [sq_nonneg θ])
  have hm := mrt_exp_sub_square_monotone ha
  change Real.exp |a| - |a| ^ 2 ≤
    Real.exp (Real.sqrt (a ^ 2 + θ ^ 2)) - Real.sqrt (a ^ 2 + θ ^ 2) ^ 2 at hm
  rw [sq_abs, Real.sq_sqrt hs] at hm
  have he : Real.exp a + Real.exp (-a) ≤ Real.exp |a| + 1 := by
    by_cases ha0 : 0 ≤ a
    · rw [abs_of_nonneg ha0]
      have hh : Real.exp (-a) ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -a ≤ 0)
      linarith
    · rw [abs_of_neg (lt_of_not_ge ha0)]
      have hh : Real.exp a ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (le_of_not_ge ha0)
      linarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

lemma mrt_exp_difference_square (z : ℂ) :
    ‖Complex.exp (z / 2) - Complex.exp (-z / 2)‖ ^ 2 =
      Real.exp z.re + Real.exp (-z.re) - 2 * Real.cos z.im := by
  have hp : z / 2 + conj (-z / 2) = (z.im : ℂ) * Complex.I := by
    simp only [map_div₀, map_neg, map_ofNat]
    apply Complex.ext
    · simp
      ring
    · simp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.norm_exp, Complex.norm_exp, ← Complex.exp_conj, ← Complex.exp_add, hp]
  have h1 : Real.exp (z / 2).re ^ 2 = Real.exp z.re := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
    ring
  have h2 : Real.exp (-z / 2).re ^ 2 = Real.exp (-z.re) := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
    ring
  rw [h1, h2]
  simp [Complex.exp_re]

theorem mrt_exp_difference_bound (z : ℂ) :
    ‖Complex.exp (z / 2) - Complex.exp (-z / 2)‖ ≤ Real.exp (‖z‖ / 2) := by
  have hsq := mrt_exp_cos_inequality z.re z.im
  rw [← Complex.norm_eq_sqrt_sq_add_sq, ← mrt_exp_difference_square] at hsq
  have he : Real.exp (‖z‖ / 2) ^ 2 = Real.exp ‖z‖ := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← he] at hsq
  nlinarith [norm_nonneg (Complex.exp (z / 2) - Complex.exp (-z / 2)),
    Real.exp_pos (‖z‖ / 2)]

theorem mrt_normalized_band_bound (z : ℂ) (M : ℝ) (hM : ‖z‖ ≤ M) :
    ‖Complex.exp (z / 2) - Complex.exp (-z / 2)‖ * Real.exp (-M / 2) ≤ 1 := by
  calc
    _ ≤ Real.exp (M / 2) * Real.exp (-M / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mrt_exp_difference_bound z).trans (Real.exp_le_exp.mpr (by linarith))
    _ = 1 := by rw [← Real.exp_add, show M / 2 + -M / 2 = 0 by ring, Real.exp_zero]

/-- Every band contributes at most one after normalization.  In particular
this product incurs no loss depending on the number of bands. -/
theorem mrt_normalized_bands_bound {ι : Type*} (J : Finset ι)
    (z : ι → ℂ) (M : ι → ℝ) (hM : ∀ j ∈ J, ‖z j‖ ≤ M j) :
    (∏ j ∈ J, ‖Complex.exp (z j / 2) - Complex.exp (-z j / 2)‖ *
      Real.exp (-M j / 2)) ≤ 1 := by
  exact prod_le_one₀ (fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun j hj => mrt_normalized_band_bound (z j) (M j) (hM j hj))

end TwoPointCorrelations

end OAI
