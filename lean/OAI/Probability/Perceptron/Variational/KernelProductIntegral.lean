import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace SphericalPerceptronFreeEnergy
lemma measurable_kernel_product_integral {X A B Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (κ : Kernel A B) [IsSFiniteKernel κ] (ν : Measure Y) [SFinite ν]
    (a : X→A) (ha : Measurable a) (F : X×(B×Y)→ℝ) (hF : Measurable F) :
    Measurable (fun x=>∫ u,F (x,u) ∂(κ (a x)).prod ν) := by
  let κ' : Kernel X (B×Y):=(κ.comap a ha).prod (Kernel.const X ν)
  have h := hF.stronglyMeasurable.integral_kernel_prod_right (κ:=κ') (f:=fun x u=>F (x,u))
  have he (x : X) : κ' x=(κ (a x)).prod ν := by
    change ((κ.comap a ha).prod (Kernel.const X ν)) x=_
    rw [Kernel.prod_apply]
    rfl
  simpa only [he] using h.measurable
end SphericalPerceptronFreeEnergy

end

end OAI
