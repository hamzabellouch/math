import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace InternalCatalan

noncomputable def blaschkeFactor (x : ℝ) (z : ℂ) : ℂ :=
  (z - (x : ℂ)) / (1 - (x : ℂ) * z)

noncomputable def finiteBlaschke {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, blaschkeFactor (x i) z

theorem blaschkeFactor_imaginary_norm_sq (u x : ℝ) :
    ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ ^ 2 =
      (u ^ 2 + x ^ 2) / (1 + x ^ 2 * u ^ 2) := by
  unfold blaschkeFactor
  rw [Complex.sq_norm, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, sub_zero,
    zero_sub]
  congr 1 <;> ring

theorem blaschkeFactor_outer_one_le_norm {u x : ℝ}
    (hu : 1 ≤ u) (hx : x ^ 2 ≤ 1) :
    1 ≤ ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ := by
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hden : 0 < 1 + x ^ 2 * u ^ 2 := by positivity
  have hnum : 1 + x ^ 2 * u ^ 2 ≤ u ^ 2 + x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sub_nonneg.mpr hx)]
  have hs : 1 ≤ ‖blaschkeFactor x (Complex.I * (u : ℂ))‖ ^ 2 := by
    rw [blaschkeFactor_imaginary_norm_sq]
    exact (one_le_div hden).2 hnum
  nlinarith [norm_nonneg (blaschkeFactor x (Complex.I * (u : ℂ)))]

theorem blaschkeFactor_imaginary_ne_zero {u : ℝ} (x : ℝ) (hu : u ≠ 0) :
    blaschkeFactor x (Complex.I * (u : ℂ)) ≠ 0 := by
  unfold blaschkeFactor
  apply div_ne_zero
  · intro h
    have him := congrArg Complex.im h
    apply hu
    simpa [Complex.mul_re, Complex.mul_im] using him
  · intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.mul_im] at hre

theorem finiteBlaschke_norm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (z : ℂ) :
    ‖finiteBlaschke s x z‖ = ∏ i ∈ s, ‖blaschkeFactor (x i) z‖ := by
  exact Complex.norm_prod s _

theorem finiteBlaschke_outer_one_le_norm {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) {u : ℝ} (hu : 1 ≤ u) (hx : ∀ i ∈ s, x i ^ 2 ≤ 1) :
    1 ≤ ‖finiteBlaschke s x (Complex.I * (u : ℂ))‖ := by
  rw [finiteBlaschke_norm]
  exact Finset.one_le_prod₀ (fun i hi => blaschkeFactor_outer_one_le_norm hu (hx i hi))

theorem outer_diameter_power_le_exp_two {D n : ℕ} {u : ℝ}
    (hDn : D ≤ n) (hu : 1 ≤ u) (hun : u ≤ 1 + 2 / (n : ℝ)) :
    u ^ D ≤ Real.exp 2 := by
  calc
    u ^ D ≤ u ^ n := pow_le_pow_right₀ hu hDn
    _ ≤ (1 + 2 / (n : ℝ)) ^ n := pow_le_pow_left₀ (by linarith) hun n
    _ ≤ Real.exp 2 := by
      simpa only [neg_div, sub_neg_eq_add, neg_neg] using
        (Real.one_sub_div_pow_le_exp_neg (n := n) (t := -2)
          (le_trans (by norm_num) (Nat.cast_nonneg n)))

end InternalCatalan

end OAI
