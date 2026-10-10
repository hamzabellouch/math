import OAI.Probability.ClassicalON.ProductMoments

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem doubled_covariance_identity {w f g : X → ℝ}
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g) :
    (∫ p : X×X,w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2) ∂μ.prod μ) =
      2*((∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ)-
        (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ)) := by
  have he : (fun p : X×X => w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2)) =
      (fun p : X×X => (w p.1*(f p.1*g p.1)*w p.2+w p.1*(w p.2*(f p.2*g p.2)))-
        (w p.1*f p.1*(w p.2*g p.2)+w p.1*g p.1*(w p.2*f p.2))) := by
    funext p; ring
  rw [he,integral_sub (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))]
  rw [integral_prod_mul (fun x => w x*(f x*g x)) w,
    integral_prod_mul w (fun x => w x*(f x*g x)),
    integral_prod_mul (fun x => w x*f x) (fun x => w x*g x),
    integral_prod_mul (fun x => w x*g x) (fun x => w x*f x)]
  ring

theorem covariance_nonneg_of_doubled {w f g : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) (hf : Continuous f) (hg : Continuous g)
    (h : 0≤∫ p : X×X,w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2) ∂μ.prod μ) :
    weightedMean μ w f*weightedMean μ w g≤weightedMean μ w (fun x => f x*g x) := by
  rw [doubled_covariance_identity μ hw hf hg] at h
  apply (weightedMean_inequality_iff hw hp).2
  linarith

end
end ClassicalON

end

end OAI
