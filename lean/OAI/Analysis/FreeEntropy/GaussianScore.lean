import OAI.Analysis.FreeEntropy.PolynomialGrowth

namespace OAI

universe u1

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem smoothed_polynomial_ibp (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s)
    {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    (∫x,f (WithLp.ofLp x)*smoothedGradient μ s x i) =
      -(∫x,coordinateDerivative f i (WithLp.ofLp x)*smoothedDensity μ s x) := by
  have hm : ∀ᵐy ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  exact integral_coordinate_ibp i (fun x => f (WithLp.ofLp x))
    (fun x => coordinateDerivative f i (WithLp.ofLp x))
    (smoothedDensity μ s) (fun x => smoothedGradient μ s x i)
    (fun x r => hf.hasDerivAt_line x i r)
    (fun x r => smoothedDensity_hasDeriv_coordinate μ (isCompact_closedBall _ _) hm s x i r)
    (hf.smoothedGradient_integrable μ hs hK hμ i)
    ((hf.derivative i).smoothed_integrable μ hs hK hμ)
    (hf.smoothed_integrable μ hs hK hμ)
 theorem smoothed_score_lower (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s)
    {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    (∫x,(2*coordinateDerivative f i (WithLp.ofLp x)-f (WithLp.ofLp x)^2)*smoothedDensity μ s x) ≤
      ∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x := by
  have hd := (hf.derivative i).smoothed_integrable μ hs hK hμ
  have hsq := (hf.pow 2).smoothed_integrable μ hs hK hμ
  have hg := hf.smoothedGradient_integrable μ hs hK hμ i
  have hi := smoothedScore_integrable μ hs hK hμ i
  have hle : 0 ≤ ∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x +
      2*(f (WithLp.ofLp x)*smoothedGradient μ s x i)+f (WithLp.ofLp x)^2*smoothedDensity μ s x := by
    apply integral_nonneg
    intro x
    have hp := smoothedDensity_pos μ hs x
    have hsq' := sq_nonneg (smoothedGradient μ s x i+f (WithLp.ofLp x)*smoothedDensity μ s x)
    have he : (smoothedGradient μ s x i)^2/smoothedDensity μ s x + 2*(f (WithLp.ofLp x)*smoothedGradient μ s x i)+f (WithLp.ofLp x)^2*smoothedDensity μ s x =
        (smoothedGradient μ s x i+f (WithLp.ofLp x)*smoothedDensity μ s x)^2/smoothedDensity μ s x := by field_simp; ring
    change 0 ≤ (smoothedGradient μ s x i)^2/smoothedDensity μ s x + 2*(f (WithLp.ofLp x)*smoothedGradient μ s x i)+f (WithLp.ofLp x)^2*smoothedDensity μ s x
    rw [he]
    exact div_nonneg hsq' hp.le
  have hsum := integral_add (hi.add (hg.const_mul 2)) hsq
  have hsum' := integral_add hi (hg.const_mul 2)
  simp only [Pi.add_apply] at hsum hsum'
  rw [hsum,hsum',integral_const_mul,smoothed_polynomial_ibp μ hK hμ hs hf i] at hle
  have he : (fun x => (2*coordinateDerivative f i (WithLp.ofLp x)-f (WithLp.ofLp x)^2)*smoothedDensity μ s x) =
      fun x => 2*(coordinateDerivative f i (WithLp.ofLp x)*smoothedDensity μ s x)-f (WithLp.ofLp x)^2*smoothedDensity μ s x := by
    funext x; ring
  rw [he,integral_sub (hd.const_mul 2) hsq,integral_const_mul]
  linarith
 theorem classicalFisher_polynomial_lower (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s)
    (f : ι → (ι → ℝ) → ℝ) (hf : ∀i,IsRealPolynomial (f i)) :
    (∑i,∫x,(2*coordinateDerivative (f i) i (WithLp.ofLp x)-(f i (WithLp.ofLp x))^2)*smoothedDensity μ s x) ≤
      classicalFisher μ s :=
  sum_le_sum (fun i _ => smoothed_score_lower μ hK hμ hs (hf i) i)
end FiniteEntropySeparation

end

end OAI
