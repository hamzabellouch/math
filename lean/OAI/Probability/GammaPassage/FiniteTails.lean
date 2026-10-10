import OAI.Probability.GammaPassage.FiniteMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate theta : ℝ}

/-- Exponential Markov bound for a real parameter `theta` and an arbitrary real threshold. -/
theorem GammaEnvironment.exponential_markov_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S)))
  calc
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
        P {ω | ENNReal.ofReal (Real.exp (theta * a)) ≤
          ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) /
        ENNReal.ofReal (Real.exp (theta * a)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ = _ := by rw [h.lintegral_exp_edgeSum hshape hrate htheta S]

/-- Gamma Chernoff upper-tail estimate for `0 < theta < rate`. -/
theorem GammaEnvironment.upper_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_pos : 0 < theta) (htheta : theta < rate)
    (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | a ≤ edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate htheta S a)
  intro ω hω
  exact mul_le_mul_of_nonneg_left hω htheta_pos.le

/-- Gamma Chernoff lower-tail estimate for `theta < 0`. -/
theorem GammaEnvironment.lower_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | edgeSum S τ ω ≤ a} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate (htheta_neg.trans hrate) S a)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω htheta_neg.le

theorem GammaEnvironment.upper_tail_edgeSum_linear
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_pos : 0 < theta) (htheta : theta < rate)
    (S : Finset PlanarFPP.Edge) (c : ℝ) :
    P {ω | (S.card : ℝ) * c ≤ edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape) /
        ENNReal.ofReal (Real.exp (theta * c))) ^ S.card := by
  have hb := h.upper_tail_edgeSum hshape hrate htheta_pos htheta S ((S.card : ℝ) * c)
  have he : theta * ((S.card : ℝ) * c) = (S.card : ℝ) * (theta * c) := by ring
  simpa only [he, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le,
    div_eq_mul_inv, mul_pow, ENNReal.inv_pow] using hb

/-- A lower-tail estimate at a threshold proportional to the number of edges. -/
theorem GammaEnvironment.lower_tail_edgeSum_linear
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (c : ℝ) :
    P {ω | edgeSum S τ ω ≤ (S.card : ℝ) * c} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape) /
        ENNReal.ofReal (Real.exp (theta * c))) ^ S.card := by
  have hb := h.lower_tail_edgeSum hshape hrate htheta_neg S ((S.card : ℝ) * c)
  have he : theta * ((S.card : ℝ) * c) = (S.card : ℝ) * (theta * c) := by ring
  simpa only [he, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le,
    div_eq_mul_inv, mul_pow, ENNReal.inv_pow] using hb

end GammaFPP

end OAI
