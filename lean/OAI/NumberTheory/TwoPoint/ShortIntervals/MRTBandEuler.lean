import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandCancellation

namespace OAI

/-! Exact finite Euler-product bounds for inclusion-exclusion over prime
bands.  Each nonempty-band factor pays a square root of its Euler product,
with only the summable prime-square error remaining. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped ComplexConjugate

lemma mrt_local_euler_log_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 - z)⁻¹‖ ≤ ‖z‖ + ‖z‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hr : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  calc
    _ = ‖(Complex.log (1 - z)⁻¹ - z) + z‖ := by congr 1; ring
    _ ≤ ‖Complex.log (1 - z)⁻¹ - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ _ := by linarith

lemma mrt_exp_sub_one_bound (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤
      Real.sqrt ‖Complex.exp z‖ * Real.exp (‖z‖ / 2) := by
  have hf : Complex.exp z - 1 = Complex.exp (z / 2) *
      (Complex.exp (z / 2) - Complex.exp (-z / 2)) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add,
      show z / 2 + z / 2 = z by ring,
      show z / 2 + -z / 2 = 0 by ring, Complex.exp_zero]
  rw [hf, norm_mul]
  have he : ‖Complex.exp (z / 2)‖ = Real.sqrt ‖Complex.exp z‖ := by
    rw [Complex.norm_exp, Complex.norm_exp, Complex.div_ofNat_re, Real.exp_half]
  rw [he]
  exact mul_le_mul_of_nonneg_left (mrt_exp_difference_bound z) (Real.sqrt_nonneg _)

lemma mrt_euler_block_exp {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    Complex.exp (∑ i ∈ S, Complex.log (1 - z i)⁻¹) =
      ∏ i ∈ S, (1 - z i)⁻¹ := by
  rw [Complex.exp_sum]
  apply prod_congr rfl
  intro i hi
  apply Complex.exp_log
  apply inv_ne_zero
  intro he
  have hez : z i = 1 := (sub_eq_zero.mp he).symm
  have := hz i hi
  simp only [hez, norm_one] at this
  norm_num at this

theorem mrt_euler_block_difference_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ S, (1 - z i)⁻¹) - 1‖ ≤
      Real.sqrt ‖∏ i ∈ S, (1 - z i)⁻¹‖ *
        Real.exp ((∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  have he := mrt_euler_block_exp S z hz
  have hb := mrt_exp_sub_one_bound (∑ i ∈ S, Complex.log (1 - z i)⁻¹)
  rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  exact (norm_sum_le _ _).trans (sum_le_sum fun i hi => mrt_local_euler_log_bound (hz i hi))

end TwoPointCorrelations

end OAI
