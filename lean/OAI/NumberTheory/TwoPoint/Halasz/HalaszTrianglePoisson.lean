import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleFourier

namespace OAI

/-! Poisson summation for the compact triangular logarithmic weight. -/
namespace TwoPointCorrelations

open MeasureTheory Filter Asymptotics
open scoped FourierTransform

lemma halasz_triangle_decay (N u : ℝ) (hN : 0 < N) :
    (halaszTriangleFunction N u 0) =O[cocompact ℝ] (fun x : ℝ => |x|^(-2:ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [(isCompact_Icc : IsCompact (Set.Icc (N/2) (5*N/2))).compl_mem_cocompact] with x hx
  rw [halasz_triangle_function_zero N u 0 x hN hx, norm_zero]
  positivity

lemma halasz_triangle_fourier_decay (N u : ℝ) (hN : 0 < N) :
    (𝓕 (halaszTriangleFunction N u 0)) =O[cocompact ℝ] (fun x : ℝ => |x|^(-2:ℝ)) := by
  let R := max 1 (2*|u|/(Real.pi*N))
  apply IsBigO.of_bound (512/(N*(2*Real.pi)^2))
  filter_upwards [(isCompact_Icc : IsCompact (Set.Icc (-R) R)).compl_mem_cocompact] with ξ hx
  have hξ : R < |ξ| := by
    by_contra hn
    apply hx
    exact abs_le.mp (le_of_not_gt hn)
  have hξ0 : ξ ≠ 0 := by
    have h1 : 1 < |ξ| := (le_max_left _ _).trans_lt hξ
    exact abs_pos.mp (lt_trans zero_lt_one h1)
  have hpos : 0 < Real.pi*N := mul_pos Real.pi_pos hN
  have hlow : 2*|u| ≤ |ξ| *(Real.pi*N) :=
    (div_le_iff₀ hpos).mp ((le_max_right _ _).trans hξ.le)
  have hfar : 4*|u| ≤ N*|2*Real.pi*ξ| := by
    rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith
  have hfreq : 2*Real.pi*ξ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ0
  rw [halasz_triangle_fourier N u ξ hN]
  apply (halasz_triangle_far N u (2*Real.pi*ξ) hN hfreq hfar).trans_eq
  have hg : ‖|ξ|^(-2:ℝ)‖ = 1/ξ^2 := by
    rw [Real.rpow_neg (abs_nonneg ξ) 2, Real.rpow_two, norm_inv, Real.norm_eq_abs,
      abs_pow, abs_abs, sq_abs]
    rw [one_div]
  rw [hg]
  ring

theorem halasz_triangle_poisson (N u : ℝ) (hN : 0 < N) :
    (∑' n : ℤ, halaszTriangleFunction N u 0 n) =
      ∑' k : ℤ, halaszTriangleIntegral N u (2*Real.pi*k) := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay
    (halasz_triangle_function_continuous N u 0 hN) (by norm_num : (1:ℝ)<2)
    (halasz_triangle_decay N u hN) (halasz_triangle_fourier_decay N u hN) 0
  simpa only [zero_add, fourier_coe_apply, mul_zero, neg_zero, Complex.ofReal_zero,
    zero_mul, zero_div, Complex.exp_zero, mul_one, halasz_triangle_fourier N u _ hN] using h

end TwoPointCorrelations

end OAI
