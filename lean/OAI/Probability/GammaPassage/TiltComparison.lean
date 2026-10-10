import OAI.Probability.GammaPassage.FiniteTilt
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

namespace GammaFPP
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Cauchy–Schwarz for an extended nonnegative density and a measurable event. -/
theorem withDensity_sq_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L : Ω → ℝ≥0∞) (hL : Measurable L)
    (A : Set Ω) (hA : MeasurableSet A) :
    ((P.withDensity L) A)^2 ≤ (∫⁻ x, (L x)^2 ∂P)*P A := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hL.aemeasurable (measurable_const.aemeasurable :
      AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) (P.restrict A))
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two, one_pow, lintegral_one,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hh
  have hsqrt (x : ℝ≥0∞) : (x^(1/(2 : ℝ)))^2 = x := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hh2 := pow_le_pow_left' hh 2
  rw [mul_pow, hsqrt, hsqrt] at hh2
  rw [withDensity_apply L hA]
  exact hh2.trans (mul_le_mul'
    (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl)

/-- A second-moment bound for scaled finite Gamma event probabilities when `-1 < delta < 1`. -/
theorem finite_gamma_scaled_probability_sq_bound
    {ι : Type*} [Fintype ι] {shape rate delta : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    ((finiteGammaMeasure (ι := ι) shape rate).map
      (fun x i => (1-delta)*x i)).real A ^ 2 ≤
    (1-delta^2)^(-shape * (Fintype.card ι : ℝ)) *
      (finiteGammaMeasure (ι := ι) shape rate).real A := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  have hmeasure : (finiteGammaMeasure (ι := ι) shape rate) A ≠ ∞ := by
    unfold finiteGammaMeasure
    exact measure_ne_top _ _
  have hb : 0 < 1-delta^2 := by
    have hp : 0 < (1-delta)*(1+delta) :=
      mul_pos (sub_pos.mpr hhi) (by linarith)
    nlinarith
  have hc : 0 ≤ (1-delta^2)^(-shape * (Fintype.card ι : ℝ)) :=
    Real.rpow_nonneg hb.le _
  have hh := withDensity_sq_le_second_moment
    (finiteGammaMeasure (ι := ι) shape rate)
    (finiteGammaScaleLikelihood shape rate (1-delta))
    (measurable_finiteGammaScaleLikelihood shape rate (1-delta)) A hA
  rw [← finite_gamma_map_scale_eq_withDensity hs hr (sub_pos.mpr hhi),
    finite_gamma_shrink_second_moment hs hr hlo hhi] at hh
  have hfin : ENNReal.ofReal ((1-delta^2)^(-shape * (Fintype.card ι : ℝ))) *
      (finiteGammaMeasure (ι := ι) shape rate) A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmeasure
  have hhReal := ENNReal.toReal_mono hfin hh
  simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc] using hhReal

end GammaFPP

end OAI
