import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedPrimitive
import OAI.Probability.SKBarriers.Scalar.GeneralCDFStability

namespace OAI

section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFTerminalDerivative_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    LipschitzWith (C+2*B^2) (scalarCDFTerminalDerivative β α s t f G x) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have H := dyadicScalar_terminal_derivative_uniform β hα hmono hf hG hg hdg hfK hGB hB hC s t ht x
  exact le_of_tendsto ((H.tendsto_at a).dist (H.tendsto_at b)) (Eventually.of_forall
    (fun n => (dyadicScalar_primitive_derivative_lipschitz β hα hmono n s t hf hG hg hdg hB hC x).dist_le_mul a b))

theorem scalarCDFAverage_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((C:ℝ)+2*(B:ℝ)^2)*h := by
  rw [scalarCDFAverage_eq_terminalDerivative β α s t hf hG hg,
    scalarCDFAverage_eq_terminalDerivative β γ s t hf hG hg]
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _
    ((C+2*B^2)+(C+2*B^2))
    (scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))
    (fun a => (scalarCDFOperator_terminal_hasDerivAt β hα hαm hf hG hg hdg hfK hGB hB hC s t ht x a).sub
      (scalarCDFOperator_terminal_hasDerivAt β hγ hγm hf hG hg hdg hfK hGB hB hC s t ht x a))
    ((scalarCDFTerminalDerivative_lipschitz β hα hαm hf hG hg hdg hfK hGB hB hC s t ht x).sub
      (scalarCDFTerminalDerivative_lipschitz β hγ hγm hf hG hg hdg hfK hGB hB hC s t ht x))
    (fun a => scalarCDFOperator_cdf_lipschitz (primitivePerturbation_regular hf hG a)
      (primitivePerturbation_lipschitz hfK hGB a) β hα hαm hγ hγm s t ht x) 0 h hh
  simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow,two_mul] using H

theorem scalarCDFAverage_cdf_stability_C1 (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hdg : Continuous dg)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((C:ℝ)+2*(B:ℝ)^2)*h := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hg y).continuousAt)
  exact scalarCDFAverage_cdf_stability β hα hαm hγ hγm hf
    (boundedPrimitive_regular hg hdg hB hC) (boundedPrimitive_hasDerivAt hc) hg hfK
    (boundedPrimitive_lipschitz hc hB) hB hC s t ht x h hh

end SK.Analytic

end
end

end OAI
