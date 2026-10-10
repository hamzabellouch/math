import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {shape rate : ℝ}

lemma gamma_nullSingleton : NullSingletonClass (gammaMeasure shape rate) := by
  unfold gammaMeasure
  infer_instance

lemma gamma_cdf_continuous (hs : 0 < shape) (hr : 0 < rate) :
    Continuous (cdf (gammaMeasure shape rate)) := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  let := gamma_nullSingleton (shape := shape) (rate := rate)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf (gammaMeasure shape rate)).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [StieltjesFunction.rightLim_eq]
  have hzero : ENNReal.ofReal (cdf (gammaMeasure shape rate) x -
      Function.leftLim (cdf (gammaMeasure shape rate)) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, measure_singleton]
  have hle := ENNReal.ofReal_eq_zero.mp hzero
  have hother := (monotone_cdf (gammaMeasure shape rate)).leftLim_le (le_refl x)
  linarith

lemma gamma_Ioc_pos (hs : 0 < shape) (hr : 0 < rate)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    0 < gammaMeasure shape rate (Ioc x y) := by
  have hmeas : Measurable (gammaPDF shape rate) :=
    (measurable_gammaPDFReal shape rate).ennreal_ofReal
  have hsupport : {z | gammaPDF shape rate z ≠ 0} ∩ Ioc x y = Ioc x y := by
    ext z
    constructor
    · exact fun h => h.2
    · intro hz
      refine ⟨?_, hz⟩
      exact ne_of_gt (ENNReal.ofReal_pos.mpr
        (gammaPDFReal_pos hs hr (lt_of_le_of_lt hx hz.1)))
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := (withDensity_apply_eq_zero hmeas).mp hz
  rw [hsupport, Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hv
  linarith

lemma gamma_cdf_strictMonoOn (hs : 0 < shape) (hr : 0 < rate) :
    StrictMonoOn (cdf (gammaMeasure shape rate)) (Ici 0) := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  intro x hx y _ hxy
  have hp := gamma_Ioc_pos hs hr hx hxy
  rw [← measure_cdf (gammaMeasure shape rate), StieltjesFunction.measure_Ioc,
    ENNReal.ofReal_pos] at hp
  exact sub_pos.mp hp

lemma gamma_cdf_zero (hs : 0 < shape) (hr : 0 < rate) :
    cdf (gammaMeasure shape rate) 0 = 0 := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  let := gamma_nullSingleton (shape := shape) (rate := rate)
  have he : gammaMeasure shape rate (Iic 0) = gammaMeasure shape rate (Iio 0) :=
    (measure_congr Iio_ae_eq_Iic).symm
  have hz : gammaMeasure shape rate (Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos (le_refl 0)
  rw [cdf_eq_real, measureReal_def, he, hz, ENNReal.toReal_zero]

lemma gamma_cdf_lt_one (hs : 0 < shape) (hr : 0 < rate)
    {x : ℝ} (hx : 0 ≤ x) : cdf (gammaMeasure shape rate) x < 1 := by
  have hlt := gamma_cdf_strictMonoOn hs hr hx
    (show 0 ≤ x + 1 by linarith) (show x < x + 1 by linarith)
  exact hlt.trans_le (cdf_le_one (gammaMeasure shape rate) (x + 1))

/-- Every `u ∈ [0, 1)` has a unique nonnegative Gamma quantile. -/
lemma gamma_cdf_existsUnique (hs : 0 < shape) (hr : 0 < rate)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    ∃! x : ℝ, 0 ≤ x ∧ cdf (gammaMeasure shape rate) x = u := by
  have hev : ∀ᶠ b : ℝ in atTop, 0 ≤ b ∧ u < cdf (gammaMeasure shape rate) b := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      (tendsto_cdf_atTop (gammaMeasure shape rate)).eventually (Ioi_mem_nhds hu1)]
      with b hb hbu
    exact ⟨hb, hbu⟩
  obtain ⟨b, hb, hbu⟩ := hev.exists
  have hu0 : cdf (gammaMeasure shape rate) 0 ≤ u := by
    rw [gamma_cdf_zero hs hr]
    exact hu
  obtain ⟨x, hx, hxu⟩ := intermediate_value_Icc hb
    (gamma_cdf_continuous hs hr).continuousOn ⟨hu0, hbu.le⟩
  refine ⟨x, ⟨hx.1, hxu⟩, ?_⟩
  intro y hy
  exact (gamma_cdf_strictMonoOn hs hr).injOn hy.1 hx.1 (hy.2.trans hxu.symm)

end GammaFPP

end OAI
