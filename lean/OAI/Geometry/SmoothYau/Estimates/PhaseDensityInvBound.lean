import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YauCounterexamples

lemma phase_density_inv_bound (η c n δ : ℝ) (hη : 0 < η) (hc : 0 < c)
    (hn : 1 ≤ n) (hδ : 0 < δ) (hδsq : δ^2 = 1/n) :
    (Real.sqrt η/2*δ*(c/2*(n^6)⁻¹)^4)⁻¹ ≤
      (Real.sqrt η/2*(c/2)^4)⁻¹*n^28 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have heq : δ^2*n = 1 := (eq_div_iff hn0.ne').mp hδsq
  have hδ1 : δ ≤ 1 := by
    have hh : δ^2 ≤ 1 := by rw [hδsq]; exact (div_le_one hn0).mpr hn
    nlinarith
  have hinv : δ⁻¹ ≤ n := by
    rw [← one_div]
    apply (div_le_iff₀ hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hn0.le hδ.le)]
  have hid : (Real.sqrt η/2*δ*(c/2*(n^6)⁻¹)^4)⁻¹ =
      (Real.sqrt η/2*(c/2)^4)⁻¹*δ⁻¹*n^24 := by
    field_simp
  rw [hid]
  calc
    _ ≤ (Real.sqrt η/2*(c/2)^4)⁻¹*n*n^24 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by positivity)) (by positivity)
    _ = (Real.sqrt η/2*(c/2)^4)⁻¹*n^25 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn (by omega)) (by positivity)

lemma phase_density_power_bound (η c n δ r : ℝ) (hη : 0 < η) (hc : 0 < c)
    (hn : 1 ≤ n) (hδ : 0 < δ) (hδsq : δ^2 = 1/n) (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.sqrt η/2*δ*(c/2*(n^6)⁻¹)^4)⁻¹*(ENNReal.ofReal (2*r))^4 ≤
      ENNReal.ofReal (16*(Real.sqrt η/2*(c/2)^4)⁻¹*n^28*r^4) := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r),← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((Real.sqrt η/2*(c/2)^4)⁻¹*n^28)*(2*r)^4 :=
      mul_le_mul_of_nonneg_right (phase_density_inv_bound η c n δ hη hc hn hδ hδsq) (by positivity)
    _ = _ := by ring

end YauCounterexamples

end

end OAI
