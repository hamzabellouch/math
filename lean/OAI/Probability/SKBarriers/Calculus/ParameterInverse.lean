import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterLinear

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterInverse
variable {P E : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]

theorem ParamLinearGrowth.inv_gaussian_exp {f : P × (E × ℝ) → ℝ}
    (hf : ParamLinearGrowth f) (hc : Continuous f) :
    ParamExpGrowth (fun z : P × E => (∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1)⁻¹) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  let B := ∫ y : ℝ, Real.exp (-C*|y|) ∂gaussianReal 0 1
  have hB : 0 < B := integral_exp_pos (integrable_exp_mul_abs_gaussian (-C))
  refine ⟨Real.exp C/B,C,by positivity,hC,?_⟩
  intro p e he
  let A := C*(1+‖e‖)
  have hb y : |f (p,(e,y))| ≤ A+C*|y| := by
    apply (hf p (e,y) he).trans
    rw [Prod.norm_def,Real.norm_eq_abs]
    have hh := max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
    dsimp [A]
    nlinarith
  have H := gaussian_exp_integral_bounds (fun y => f (p,(e,y)))
    (hc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) hC hb
  let Z := ∫ y, Real.exp (f (p,(e,y))) ∂gaussianReal 0 1
  have hlo : 0 < Real.exp (-A)*B := mul_pos (Real.exp_pos _) hB
  have hz : 0 < Z := hlo.trans_le H.1
  change ‖Z⁻¹‖ ≤ Real.exp C/B*Real.exp (C*‖e‖)
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.2 hz)]
  calc
    Z⁻¹ ≤ (Real.exp (-A)*B)⁻¹ := (inv_le_inv₀ hz hlo).2 H.1
    _ = Real.exp C/B*Real.exp (C*‖e‖) := by
      rw [mul_inv_rev,Real.exp_neg,inv_inv]
      dsimp [A]
      rw [mul_add,mul_one,Real.exp_add]
      ring
end ParameterInverse
end SK.Analytic

end
end

end

end OAI
