import OAI.Probability.ClassicalON.AssociationCore

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def exponentialMean (H f : X → ℝ) : ℝ := weightedMean μ (fun x => Real.exp (H x)) f

theorem exponentialMean_continuous {H : ℝ×X → ℝ} (hH : Continuous H)
    {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun t => exponentialMean μ (fun x => H (t,x)) f) := by
  apply (compact_parametric_integral (fun t x => Real.exp (H (t,x))*f x) (by fun_prop)).div
    (compact_parametric_integral (fun t x => Real.exp (H (t,x))) (by fun_prop))
  exact fun t => (compact_integral_pos (by fun_prop) (fun x => Real.exp_pos (H (t,x)))).ne'

theorem hasDerivAt_exponentialIntegral {H A f : X → ℝ}
    (hH : Continuous H) (hA : Continuous A) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => ∫ x,Real.exp (H x+u*A x)*f x ∂μ)
      (∫ x,Real.exp (H x+t*A x)*(f x*A x) ∂μ) t := by
  apply hasDerivAt_integral_compact μ
    (fun u x => Real.exp (H x+u*A x)*f x)
    (fun u x => Real.exp (H x+u*A x)*(f x*A x)) (by fun_prop) (by fun_prop)
  intro u x
  exact ((((hasDerivAt_id u).mul_const (A x)).const_add (H x)).exp.mul_const (f x)).congr_deriv (by simp only [id_eq]; ring)

theorem hasDerivAt_exponentialMean {H A f : X → ℝ}
    (hH : Continuous H) (hA : Continuous A) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => exponentialMean μ (fun x => H x+u*A x) f)
      (exponentialMean μ (fun x => H x+t*A x) (fun x => f x*A x)-
        exponentialMean μ (fun x => H x+t*A x) f*
        exponentialMean μ (fun x => H x+t*A x) A) t := by
  have hN := hasDerivAt_exponentialIntegral μ hH hA hf t
  have hD := hasDerivAt_exponentialIntegral μ hH hA continuous_const t (f := fun _ => 1)
  simp only [mul_one,one_mul] at hD
  have hz : (∫ x,Real.exp (H x+t*A x) ∂μ)≠0 :=
    (compact_integral_pos (by fun_prop) (fun x => Real.exp_pos _)).ne'
  exact (hN.div hD hz).congr_deriv (by unfold exponentialMean weightedMean; field_simp)

end
end ClassicalON

end

end OAI
