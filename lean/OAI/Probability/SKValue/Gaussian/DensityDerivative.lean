import Mathlib
import OAI.Probability.SKValue.Equations.ForwardDensity
import OAI.Probability.SKValue.Gaussian.DensityJump

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
lemma gaussianPDFReal_derivative {a:ℝ} (ha:0<a) (x:ℝ) :
    HasDerivAt (gaussianPDFReal 0 a.toNNReal)
      (-(x/a)*gaussianPDFReal 0 a.toNNReal x) x := by
  have hd := (((((hasDerivAt_id x).pow 2).neg).div_const (2*a)).exp).const_mul
    (Real.sqrt (2*Real.pi*a))⁻¹
  convert! hd using 1
  · funext y
    simp only [gaussianPDFReal,Real.coe_toNNReal _ ha.le,sub_zero,
      Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [gaussianPDFReal,Real.coe_toNNReal _ ha.le,sub_zero,
      Pi.neg_apply,Pi.pow_apply,id_eq]
    field_simp
    ring

namespace ForwardDensityData
variable (D:ForwardDensityData)
lemma weight_derivative (x:ℝ) : HasDerivAt D.weight (-D.jet 0 x*D.weight x) x := by
  have hψ := D.smooth.smooth.differentiable (by simp)
  have hd := (gaussianPDFReal_derivative D.variance_pos x).mul
    ((((hψ x).hasDerivAt).const_mul D.size).exp)
  convert! hd using 1
  simp only [jet,ite_true,iteratedDeriv_zero,weight]
  ring
lemma weight_exp_integrable {f:ℝ → ℝ} (hf:ExpGrowth f) (hm:Measurable f) :
    Integrable (fun x ↦ D.weight x*f x) := by
  have he := (ExpGrowth.exp_lipschitz D.smooth.lipschitz D.size_pos.le).mul hf
  have hm' : Measurable (fun x ↦ Real.exp (D.size*D.potential x)*f x) :=
    ((measurable_const.mul D.smooth.smooth.continuous.measurable).exp).mul hm
  simpa only [weight,mul_assoc] using he.pdf_integrable hm' D.variance_pos 0
lemma density_derivative {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A) (x:ℝ) :
    HasDerivAt (fun y ↦ Real.exp (c*A y)*D.weight y)
      ((c*deriv A x-D.jet 0 x)*(Real.exp (c*A x)*D.weight x)) x := by
  have hd := ((((hA.smooth.differentiable (by simp)) x).hasDerivAt.const_mul c).exp).mul
    (D.weight_derivative x)
  convert! hd using 1
  ring
end ForwardDensityData
end SKValue

end

end OAI
