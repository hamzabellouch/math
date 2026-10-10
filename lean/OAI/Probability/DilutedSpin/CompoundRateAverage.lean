import OAI.Probability.DilutedSpin.CavityAllocatedMean
import OAI.Probability.DilutedSpin.CompoundRate

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [CompleteSpace V]

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma integral_add_lipschitz [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {F : E → ℝ} (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (fun x => ∫ y,F (x+y) ∂μ) := by
  have hi x : Integrable (fun y => F (x+y)) μ :=
    integrable_lipschitz_of_id μ hμ (by simpa only [mul_one, Function.comp_def] using hF.comp (isometry_add_left x).lipschitzWith)
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  rw [← integral_sub (hi x) (hi z)]
  apply abs_integral_le_bound
  intro y
  simpa only [Real.norm_eq_abs,add_sub_add_right_eq_sub,NNReal.coe_one,one_mul] using hF.norm_sub_le (x+y) (z+y)

omit [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V] in
lemma integrated_compound_rate_bound [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (ρ : Measure V) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    {e : V → E} (he : LipschitzWith 1 e) {F : E → ℝ} (hF : LipschitzWith 1 F)
    (r s : ℝ≥0) :
    |(∫ x,∫ y,F (e x+y) ∂compoundPoisson r μ ∂ρ)-
      (∫ x,∫ y,F (e x+y) ∂compoundPoisson s μ ∂ρ)|≤
        |(r:ℝ)-s| * (∫ y,‖y‖ ∂μ) := by
  have hl t : LipschitzWith 1 (fun x => ∫ y,F (e x+y) ∂compoundPoisson t μ) := by
    simpa only [one_mul,Function.comp_def] using
      (integral_add_lipschitz (compoundPoisson t μ) (compoundPoisson_integrable_id t μ hμ) hF).comp he
  rw [← integral_sub (integrable_lipschitz_of_id ρ hρ (hl r)) (integrable_lipschitz_of_id ρ hρ (hl s))]
  apply abs_integral_le_bound
  intro x
  have hx : LipschitzWith 1 (fun y => F (e x+y)) := by
    simpa only [mul_one, Function.comp_def] using hF.comp (isometry_add_left (e x)).lipschitzWith
  simpa only [NNReal.coe_one,one_mul] using compoundPoisson_rate_bound r s μ hμ hx

end DilutedSpinGlass

end

end OAI
