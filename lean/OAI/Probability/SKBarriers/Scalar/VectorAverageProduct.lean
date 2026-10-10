import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorAverageAlgebra

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementAverage_product_plus_le (l : List (ℝ × E)) {f R C D T : E → ℝ}
    (hf : BoundedDerivs f) (hR : Continuous R) (hC : Continuous C) (hD : Continuous D) (hT : Continuous T)
    (hRE : HasExpGrowth R) (hCE : HasExpGrowth C) (hDE : HasExpGrowth D) (hTE : HasExpGrowth T)
    {V : ℝ} (hV : ∀ x,R x ≤ V) (hC0 : ∀ x,0 ≤ C x) (Λ : ℝ) (x : E) :
    vectorIncrementAverage l f (fun x => R x*C x+Λ*D x+T x) x ≤
      V*vectorIncrementAverage l f C x+Λ*vectorIncrementAverage l f D x+vectorIncrementAverage l f T x := by
  have H := vectorIncrementAverage_mono l (g:=fun x => R x*C x+Λ*D x+T x)
    (h:=fun x => V*C x+Λ*D x+T x) hf
    (((hR.mul hC).add (continuous_const.mul hD)).add hT)
    (((continuous_const.mul hC).add (continuous_const.mul hD)).add hT)
    (((hRE.mul hCE).add ((HasExpGrowth.const Λ).mul hDE)).add hTE)
    ((((HasExpGrowth.const V).mul hCE).add ((HasExpGrowth.const Λ).mul hDE)).add hTE)
    (fun x => by nlinarith [mul_le_mul_of_nonneg_right (hV x) (hC0 x)]) x
  rw [vectorIncrementAverage_add l (g:=fun x => V*C x+Λ*D x) (h:=T) hf
    ((continuous_const.mul hC).add (continuous_const.mul hD)) hT
    (((HasExpGrowth.const V).mul hCE).add ((HasExpGrowth.const Λ).mul hDE)) hTE] at H
  simp only at H
  rw [vectorIncrementAverage_add l (g:=fun x => V*C x) (h:=fun x => Λ*D x) hf (continuous_const.mul hC) (continuous_const.mul hD)
    ((HasExpGrowth.const V).mul hCE) ((HasExpGrowth.const Λ).mul hDE)] at H
  simpa only [vectorIncrementAverage_const_mul] using H
end

end SK.Analytic

end
end

end OAI
