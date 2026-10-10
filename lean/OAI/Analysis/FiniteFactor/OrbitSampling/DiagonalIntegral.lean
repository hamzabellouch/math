import OAI.Analysis.FiniteFactor.OrbitSampling.DiagonalLimit

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- The actual one-coordinate diagonal model converges to uniform diagonal
mass on every measurable first test and closed-interval second test. -/
theorem sourceSampling_diagonal_integral_tendsto (E : Set ℝ) (hE : MeasurableSet E) (a c : ℝ) :
    Tendsto (fun stage => ∫ s,
      samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s ∂unitIntervalMeasure)
      atTop (𝓝 ((unitIntervalMeasure (E ∩ Set.Icc a c)).toReal)) := by
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  let f : ℝ → ℝ := (E ∩ Set.Icc a c).indicator (fun _ => 1)
  have hlim : ∀ᵐ s ∂unitIntervalMeasure,
      Tendsto (fun stage => samplingTestedFirstDensity false
        (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E (Set.Icc a c) s)
        atTop (𝓝 (f s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico,unitIntervalMeasure.ae_ne 0,
      unitIntervalMeasure.ae_ne a,unitIntervalMeasure.ae_ne c] with s hs hs0 hsa hsc
    have hh := sourceSampling_diagonal_eventually s a c E ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),hs.2⟩ hsa hsc
    have he : (fun stage => samplingTestedFirstDensity false (sourceSamplingWidth stage)
        (sourceSamplingCutoff stage) E (Set.Icc a c) s) =ᶠ[atTop] (fun _ => f s) := by
      filter_upwards [hh] with stage hstage
      simpa only [f,Set.indicator_apply,Set.mem_inter_iff] using hstage
    exact tendsto_const_nhds.congr' he.symm
  have hm (stage : ℕ) : AEStronglyMeasurable
      (samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c)) unitIntervalMeasure := (samplingTestedFirstDensity_measurable false
    (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E (Set.Icc a c) hE measurableSet_Icc).aestronglyMeasurable
  have hb (stage : ℕ) : ∀ᵐ s ∂unitIntervalMeasure,
      ‖samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    have hp := sourceSampling_parameters stage
    have h := samplingTestedFirstDensity_bounds false _ _ E (Set.Icc a c)
      hp.1 hp.2.1 hp.2.2 hE measurableSet_Icc s hs
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2
  have ht := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ)) hm (integrable_const 1) hb hlim
  have hf : (∫ s, f s ∂unitIntervalMeasure) = (unitIntervalMeasure (E ∩ Set.Icc a c)).toReal := by
    rw [integral_indicator (hE.inter measurableSet_Icc)]
    simp [measureReal_def]
  rwa [hf] at ht

/-- Triangular tested factors are independent of the sampling width and cutoff. -/
theorem samplingTestedFirstDensity_triangular_parameters (h α h' α' s : ℝ) (E G : Set ℝ) :
    samplingTestedFirstDensity true h α E G s = samplingTestedFirstDensity true h' α' E G s := by
  unfold samplingTestedFirstDensity samplingTestedFirstWeight samplingWeight
  simp only [ite_true]

end
end FiniteFactor

end OAI
