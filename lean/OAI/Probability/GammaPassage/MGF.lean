import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Exponential weighting changes the Gamma rate from `rate` to `rate - theta`. -/
lemma gamma_weighted_density {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (exp (theta * x)) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) *
        gammaPDF shape (rate - theta) x := by
  have hs : 0 < rate - theta := sub_pos.mpr htheta
  have hc : 0 ≤ (rate / (rate - theta)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hrate hs) shape).le
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    have hexp : exp (-(rate * x)) * exp (theta * x) =
        exp (-((rate - theta) * x)) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) *
          exp (theta * x) =
          rate ^ shape / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (theta * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x)) := by rw [hexp]
      _ = (rate / (rate - theta)) ^ shape *
          ((rate - theta) ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x))) := by
        rw [Real.div_rpow hrate.le hs.le]
        have hpow : (rate - theta) ^ shape ≠ 0 :=
          (Real.rpow_pos_of_pos hs shape).ne'
        have hgamma : Gamma shape ≠ 0 := (Real.Gamma_pos_of_pos hshape).ne'
        field_simp [hpow, hgamma]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- The nonnegative exponential moment from the normalized density with shifted rate. -/
theorem gamma_lintegral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x)) ∂gammaMeasure shape rate) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x))
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_weighted_density hshape hrate htheta]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one hshape (sub_pos.mpr htheta), mul_one]

/-- Exponential functions are integrable under the Gamma law for `theta < rate`. -/
theorem gamma_integrable_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    Integrable (fun x : ℝ => exp (theta * x)) (gammaMeasure shape rate) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall fun x => (exp_pos (theta * x)).le)).mp
  rw [gamma_lintegral_exp hshape hrate htheta]
  exact ENNReal.ofReal_ne_top

/-- Gamma exponential moments, as in paper 210, Lemma `df:ga:moment`. -/
theorem gamma_integral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫ x : ℝ, exp (theta * x) ∂gammaMeasure shape rate) =
      (rate / (rate - theta)) ^ shape := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (exp_pos (theta * x)).le) (by fun_prop),
    gamma_lintegral_exp hshape hrate htheta]
  exact ENNReal.toReal_ofReal
    (Real.rpow_pos_of_pos (div_pos hrate (sub_pos.mpr htheta)) shape).le

end GammaFPP

end OAI
