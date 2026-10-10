import OAI.Probability.InvariantIsing.Haar.HaarReflectionConnectivity
import OAI.Probability.InvariantIsing.Haar.HaarHeatVanishingGradient

namespace OAI

/-! Pointwise decay of spatial oscillations under the actual polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial Filter
open scoped Topology
namespace InvariantIsing

theorem haarPolynomialHeat_difference_tendsto {N d : ℕ} (hN : 3 ≤ N)
    (p : haarPolynomialSpace N d) (U V : SpecialOrthogonal N) :
    Tendsto (fun t : ℝ =>
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U-
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) V)
      atTop (𝓝 0) := by
  obtain ⟨M,hM,hgrad⟩ := haarPolynomialHeat_gradient_envelope p
  have hpoint (W : SpecialOrthogonal N) : Tendsto (fun t : ℝ =>
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) W-
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) 1)
      atTop (𝓝 0) := by
    obtain ⟨K,_,hK⟩ := haarPolynomial_global_oscillation_bound W
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using
      (tendsto_haar_gradient_envelope hN M).const_mul K)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [Real.norm_eq_abs]
    exact hK _ _ (mul_nonneg hM (Real.exp_pos _).le) (hgrad t ht)
  have hh := (hpoint U).sub (hpoint V)
  convert hh using 1
  · funext t
    ring
  · norm_num

end InvariantIsing

end

end OAI
