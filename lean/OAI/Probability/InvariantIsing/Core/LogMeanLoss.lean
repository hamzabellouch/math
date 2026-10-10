import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldOrder
import Mathlib.Analysis.Convex.Integral

namespace OAI

/-! One Gaussian backward step propagates a terminal loss by expectation
under its canonical tilted transition. No lower bound on its positive
exponent is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integral_le_log_integral_exp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F : X → ℝ)
    (hF : Integrable F μ) (he : Integrable (fun x => Real.exp (F x)) μ) :
    (∫ x, F x ∂μ) ≤ Real.log (∫ x, Real.exp (F x) ∂μ) := by
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all μ (fun _ => Set.mem_univ _)) hF he
  have hl := Real.log_le_log (Real.exp_pos (∫ x, F x ∂μ)) hj
  rwa [Real.log_exp] at hl

theorem logMean_loss_le_tilted_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (F G : X → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hF : Integrable (fun x => Real.exp (b * F x)) μ)
    (hG : Integrable (fun x => Real.exp (b * G x)) μ)
    (hD : Integrable (fun x => F x - G x) (μ.tilted (fun x => b * F x))) :
    logMean b μ F - logMean b μ G ≤
      ∫ x, F x - G x ∂μ.tilted (fun x => b * F x) := by
  let ν := μ.tilted (fun x => b * F x)
  let : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hF
  have hE : Integrable (fun x => Real.exp (-b * (F x - G x))) ν := by
    apply (integrable_tilted_iff hF _).mpr
    convert hG using 1
    funext x
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  have hi := integral_le_log_integral_exp ν (fun x => -b * (F x - G x))
    (hD.const_mul (-b)) hE
  have he : (∫ x, Real.exp (-b * (F x - G x)) ∂ν) =
      (∫ x, Real.exp (b * G x) ∂μ) / ∫ x, Real.exp (b * F x) ∂μ := by
    rw [integral_exp_tilted]
    congr 2
    funext x
    congr 1
    change b * F x + -b * (F x - G x) = b * G x
    ring
  rw [integral_const_mul, he, Real.log_div (integral_exp_pos μ G hG).ne'
    (integral_exp_pos μ F hF).ne'] at hi
  change Real.log (∫ x, Real.exp (b * F x) ∂μ) / b -
    Real.log (∫ x, Real.exp (b * G x) ∂μ) / b ≤ _
  rw [← sub_div]
  apply (div_le_iff₀ hb).mpr
  dsimp only [ν] at hi
  linarith

end InvariantIsing

end

end OAI
