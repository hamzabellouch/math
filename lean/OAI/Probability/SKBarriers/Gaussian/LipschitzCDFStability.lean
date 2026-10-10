import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFTiltedStability
import OAI.Probability.SKBarriers.Gaussian.LipschitzChainRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_cdf_stability_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z∈Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((L:ℝ)+2*(B:ℝ)^2)*h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hd : 0<d := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*d ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = ε/2 := by dsimp [d]; field_simp
  have hga (z) : |g z-scalarWindow g d z| ≤ (L:ℝ)*d := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hd z
  have Hα := scalarCDFAverage_observable_distance β hα hαm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hγ := scalarCDFAverage_observable_distance β hγ hγm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hc := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm hf
    (scalarWindow_hasDerivAt hgL.continuous d) (scalarWindowDerivative_continuous hgL.continuous d)
    hfK (scalarWindow_bound hgL.continuous hB hd) (scalarWindowDerivative_lipschitz_bound hgL hd)
    s t ht x h hh
  have H₁ := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarCDFAverage β α s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  have H₂ := abs_sub_le (scalarCDFAverage β α s t f (scalarWindow g d) x)
    (scalarCDFAverage β γ s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  rw [abs_sub_comm (scalarCDFAverage β γ s t f (scalarWindow g d) x)] at H₂
  linarith

end SK.Analytic

end
end

end OAI
