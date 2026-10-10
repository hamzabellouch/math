import OAI.Probability.SLE.Stochastic.WienerRealSupport

namespace OAI

/-! Finite-window planar Wiener support from finite Gaussian increments,
independent interpolation residuals, and uniform continuity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def wienerUnitClamp (s : ℝ≥0) : unitInterval :=
  ⟨min (s:ℝ) 1,le_min s.2 zero_le_one,min_le_right _ _⟩

lemma continuous_wienerUnitClamp : Continuous wienerUnitClamp := by
  unfold wienerUnitClamp
  fun_prop

@[simp] lemma wienerUnitClamp_unit (t : unitInterval) :
    wienerUnitClamp ⟨t,t.2.1⟩ = t := by
  apply Subtype.ext
  exact min_eq_left t.2.2

@[simp] lemma wienerUnitClamp_zero : wienerUnitClamp 0=0 := by
  apply Subtype.ext
  simp [wienerUnitClamp]

/-- The planar Wiener law gives positive probability to each uniform tube
about a continuous based path, as in Millet--Sanz-Sole (1994), Theorem 3.5. -/
theorem actual_planarWienerUnitSupport : PublishedPlanarWienerUnitSupport := by
  intro W hW f hf r hr
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let fR : ℝ≥0 → ℝ := fun s => (f (wienerUnitClamp s)).re
  let fI : ℝ≥0 → ℝ := fun s => (f (wienerUnitClamp s)).im
  have hR : Continuous fR := Complex.continuous_re.comp (f.continuous.comp continuous_wienerUnitClamp)
  have hI : Continuous fI := Complex.continuous_im.comp (f.continuous.comp continuous_wienerUnitClamp)
  have hR0 : fR 0=0 := by simp [fR,hf]
  have hI0 : fI 0=0 := by simp [fI,hf]
  let A : Set Target.Driver := {b | ∀ t : unitInterval, |b ⟨t,t.2.1⟩-fR ⟨t,t.2.1⟩| < r/4}
  let B : Set Target.Driver := {b | ∀ t : unitInterval, |b ⟨t,t.2.1⟩-fI ⟨t,t.2.1⟩| < r/4}
  have hA : 0 < W A := wienerReal_uniform_tube_pos W hW fR hR hR0 (r/4) (by positivity)
  have hB : 0 < W B := wienerReal_uniform_tube_pos W hW fI hI hI0 (r/4) (by positivity)
  have hp : 0 < (W.prod W) (A ×ˢ B) := by
    rw [Measure.prod_prod]
    exact bot_lt_iff_ne_bot.mpr (mul_ne_zero hA.ne' hB.ne')
  refine hp.trans_le (measure_mono ?_)
  intro b hb
  apply (BoundedContinuousFunction.dist_lt_iff_of_compact hr).mpr
  intro t
  rw [dist_eq_norm]
  have hre : |(planarUnitPath b t-f t).re| < r/4 := by
    simpa [planarUnitPath,fR] using hb.1 t
  have him : |(planarUnitPath b t-f t).im| < r/4 := by
    simpa [planarUnitPath,fI] using hb.2 t
  exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (by linarith)

end SLEExactGauge

end

end OAI
