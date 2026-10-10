import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Likelihood for changing a Gamma rate from `rate` to `rate / alpha`. -/
noncomputable def gammaScaleLikelihood (shape rate alpha x : ℝ) : ℝ :=
  alpha ^ (-shape) * exp (-(rate * (alpha⁻¹ - 1)) * x)

lemma gammaScaleLikelihood_pos (shape rate : ℝ) {alpha : ℝ}
    (halpha : 0 < alpha) (x : ℝ) : 0 < gammaScaleLikelihood shape rate alpha x := by
  exact mul_pos (Real.rpow_pos_of_pos halpha (-shape)) (exp_pos _)

/-- The likelihood identity includes the real-power convention at `x = 0`. -/
lemma gamma_scale_likelihood_density {shape rate alpha : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (halpha : 0 < alpha) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (gammaScaleLikelihood shape rate alpha x) =
      gammaPDF shape (rate / alpha) x := by
  have hcoeff : rate ^ shape * alpha ^ (-shape) = (rate / alpha) ^ shape := by
    rw [Real.div_rpow hrate.le halpha.le, Real.rpow_neg halpha.le, div_eq_mul_inv]
  have hexp : exp (-(rate * x)) * exp (-(rate * (alpha⁻¹ - 1)) * x) =
      exp (-((rate / alpha) * x)) := by
    rw [← exp_add]
    congr 1
    field_simp [halpha.ne']; ring
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold gammaScaleLikelihood
    calc
      (rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x))) *
          (alpha ^ (-shape) * exp (-(rate * (alpha⁻¹ - 1)) * x)) =
          (rate ^ shape * alpha ^ (-shape)) / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (-(rate * (alpha⁻¹ - 1)) * x)) := by ring
      _ = (rate / alpha) ^ shape / Gamma shape * x ^ (shape - 1) *
          exp (-((rate / alpha) * x)) := by rw [hcoeff, hexp]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- Weighting the Gamma measure by the scaling likelihood changes its rate. -/
theorem gammaMeasure_withDensity_scaleLikelihood {shape rate alpha : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (halpha : 0 < alpha) :
    (gammaMeasure shape rate).withDensity
        (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate alpha x)) =
      gammaMeasure shape (rate / alpha) := by
  change (volume.withDensity (gammaPDF shape rate)).withDensity _ =
    volume.withDensity (gammaPDF shape (rate / alpha))
  rw [← withDensity_mul volume (by unfold gammaPDF; fun_prop)
    (by unfold gammaScaleLikelihood; fun_prop)]
  congr 1
  funext x
  exact gamma_scale_likelihood_density hshape hrate halpha x

/-- The likelihood with the parametrization `alpha = 1 - delta`. -/
noncomputable def gammaShrinkLikelihood (shape rate delta x : ℝ) : ℝ :=
  gammaScaleLikelihood shape rate (1 - delta) x

theorem gammaMeasure_withDensity_shrinkLikelihood {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hdelta : delta < 1) :
    (gammaMeasure shape rate).withDensity
        (fun x => ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) =
      gammaMeasure shape (rate / (1 - delta)) := by
  exact gammaMeasure_withDensity_scaleLikelihood hshape hrate (sub_pos.mpr hdelta)

end GammaFPP

end OAI
