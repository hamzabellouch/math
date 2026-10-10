import OAI.Analysis.FiniteFactor.Sampling.Transport
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingTransportDensity_bounds (h v s : ℝ) (hh : 0 ≤ h) (hh1 : h < 1)
    (hv : 0 ≤ v) (hvh : v ≤ h) :
    0 ≤ samplingTransportDensity v s ∧ samplingTransportDensity v s ≤ 1/(1-h) ∧
      |samplingTransportDensity v s-1| ≤ h/(1-h) := by
  have hmh : 0 < 1-h := by linarith
  have hph : 0 < 1+h := by linarith
  have hmv : 0 < 1-v := by linarith
  have hpv : 0 < 1+v := by linarith
  have hlo : 1/(1+h) ≤ samplingTransportDensity v s := by
    unfold samplingTransportDensity
    split_ifs
    · exact one_div_le_one_div_of_le hpv (by linarith)
    · exact one_div_le_one_div_of_le hmv (by linarith)
  have hhi : samplingTransportDensity v s ≤ 1/(1-h) := by
    unfold samplingTransportDensity
    split_ifs <;> exact one_div_le_one_div_of_le hmh (by linarith)
  have hl : 1-h/(1-h) ≤ 1/(1+h) := by
    field_simp
    nlinarith
  have hr : 1/(1-h)-1 = h/(1-h) := by field_simp; ring
  exact ⟨(by positivity : 0 ≤ 1/(1+h)).trans hlo,hhi,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem samplingTransportDensity_integral (v : ℝ) (hv : 0 ≤ v) (hv1 : v < 1) :
    (∫ s, samplingTransportDensity v s ∂unitIntervalMeasure) = 1 := by
  have hm : Measurable (samplingTransportDensity v) :=
    samplingTransportDensity_measurable.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (samplingTransportDensity v) unitIntervalMeasure :=
    (integrable_const (1/(1-v))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1]
        exact (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).2.1))
  have hmap := congrArg (fun μ : Measure ℝ => μ Set.univ) (samplingTransport_density v hv hv1)
  have htm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
  rw [Measure.map_apply htm MeasurableSet.univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hmap
  simp only [Set.preimage_univ,measure_univ] at hmap
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun s => (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1))
  rw [← hmap] at he
  have hn : 0 ≤ ∫ s, samplingTransportDensity v s ∂unitIntervalMeasure := integral_nonneg (fun s => (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1)
  have hh := congrArg ENNReal.toReal he
  simpa [ENNReal.toReal_ofReal hn] using hh

def samplingVelocityMeasure (h : ℝ) : Measure ℝ := cond volume (Set.Ioc (0 : ℝ) h)

theorem samplingVelocity_probability (h : ℝ) (hh : 0 < h) : IsProbabilityMeasure (samplingVelocityMeasure h) := by
  apply cond_isProbabilityMeasure_of_finite
  · simp [Real.volume_Ioc,hh]
  · simp [Real.volume_Ioc]

/-- Actual averaged density of the uncut diagonal transport. -/
def samplingIdealSecond (h s : ℝ) : ℝ :=
  ∫ v, samplingTransportDensity v s ∂samplingVelocityMeasure h

theorem samplingIdealSecond_bounds (h s : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    0 ≤ samplingIdealSecond h s ∧ samplingIdealSecond h s ≤ 1/(1-h) ∧
      |samplingIdealSecond h s-1| ≤ h/(1-h) := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hm : Measurable (fun v => samplingTransportDensity v s) :=
    samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun v => samplingTransportDensity v s) (samplingVelocityMeasure h) :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (by
      filter_upwards [hv] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1]
      exact (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1)
  have hnon : 0 ≤ samplingIdealSecond h s := integral_nonneg_of_ae (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1))
  have hu := integral_mono_ae hqi (integrable_const (1/(1-h))) (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1))
  refine ⟨hnon,by simpa [samplingIdealSecond] using hu,?_⟩
  have he : samplingIdealSecond h s-1 = ∫ v, samplingTransportDensity v s-1 ∂samplingVelocityMeasure h := by
    rw [integral_sub hqi (integrable_const 1)]
    simp [samplingIdealSecond]
  rw [he]
  calc
    _ ≤ ∫ v, |samplingTransportDensity v s-1| ∂samplingVelocityMeasure h := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v => samplingTransportDensity v s-1)
    _ ≤ ∫ _v, h/(1-h) ∂samplingVelocityMeasure h := by
      apply integral_mono_ae
      · simpa [Real.norm_eq_abs] using (hqi.sub (integrable_const 1)).norm
      · exact integrable_const _
      · exact hv.mono (fun v hv => (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.2)
    _ = _ := by simp

theorem samplingIdealSecond_measurable (h : ℝ) (hh : 0 < h) : Measurable (samplingIdealSecond h) := by
  have := samplingVelocity_probability h hh
  exact samplingTransportDensity_measurable.stronglyMeasurable.integral_prod_left.measurable

/-- Fubini gives the exact mass identity for the averaged transport density. -/
theorem samplingIdealSecond_integral (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ s, samplingIdealSecond h s ∂unitIntervalMeasure) = 1 := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hvp : ∀ᵐ p : ℝ × ℝ ∂(samplingVelocityMeasure h).prod unitIntervalMeasure,
      p.1 ∈ Set.Ioc (0 : ℝ) h := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    exact hv.mono (fun v hv => Eventually.of_forall (fun _ => hv))
  have hqi : Integrable (fun p : ℝ × ℝ => samplingTransportDensity p.1 p.2)
      ((samplingVelocityMeasure h).prod unitIntervalMeasure) :=
    (integrable_const (1/(1-h))).mono' samplingTransportDensity_measurable.aestronglyMeasurable (by
      filter_upwards [hvp] with p hp
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h p.1 p.2 hh.le hh1 hp.1.le hp.2).1]
      exact (samplingTransportDensity_bounds h p.1 p.2 hh.le hh1 hp.1.le hp.2).2.1)
  have hswap := integral_integral_swap (f := fun v s => samplingTransportDensity v s) hqi
  calc
    _ = ∫ v, (∫ s, samplingTransportDensity v s ∂unitIntervalMeasure) ∂samplingVelocityMeasure h := hswap.symm
    _ = ∫ _v, (1 : ℝ) ∂samplingVelocityMeasure h := integral_congr_ae
      (hv.mono (fun v hv => samplingTransportDensity_integral v hv.1.le (hv.2.trans_lt hh1)))
    _ = 1 := by simp

/-- The source's quadratic cancellation for the actual averaged uncut
transport density. The exact mass-one identity eliminates the linear term. -/
theorem samplingIdealSecond_square (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ s, samplingIdealSecond h s^2 ∂unitIntervalMeasure) =
      1+(∫ s, (samplingIdealSecond h s-1)^2 ∂unitIntervalMeasure) ∧
    (∫ s, samplingIdealSecond h s^2 ∂unitIntervalMeasure) ≤ 1+h^2/(1-h)^2 := by
  let q := samplingIdealSecond h
  let C := h/(1-h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm := samplingIdealSecond_measurable h hh
  have hqi : Integrable q unitIntervalMeasure :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingIdealSecond_bounds h s hh hh1).1]
      exact (samplingIdealSecond_bounds h s hh hh1).2.1))
  have hdev (s : ℝ) : (q s-1)^2 ≤ C^2 := by
    have hb := abs_le.mp (samplingIdealSecond_bounds h s hh hh1).2.2
    dsimp [C,q]
    nlinarith
  have hdi : Integrable (fun s => (q s-1)^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (by fun_prop) (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hdev s))
  have heq : (fun s => q s^2) = (fun s => ((q s-1)^2+2*q s)-1) := by funext s; ring
  have hmass : (∫ s, q s ∂unitIntervalMeasure) = 1 := samplingIdealSecond_integral h hh hh1
  have he : (∫ s, q s^2 ∂unitIntervalMeasure) = 1+∫ s, (q s-1)^2 ∂unitIntervalMeasure := by
    rw [heq]
    have hsum : Integrable (fun s => (q s-1)^2+2*q s) unitIntervalMeasure := hdi.add (hqi.const_mul 2)
    rw [integral_sub hsum (integrable_const 1),integral_add hdi (hqi.const_mul 2),integral_const_mul,hmass]
    simp
    ring
  refine ⟨he,?_⟩
  have hu := integral_mono_ae hdi (integrable_const (C^2)) (Eventually.of_forall hdev)
  simp at hu
  have hCeq : C^2 = h^2/(1-h)^2 := by dsimp [C]; rw [div_pow]
  rw [he]
  linarith

end
end FiniteFactor

end OAI
