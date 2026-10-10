import OAI.Analysis.FiniteFactor.OrbitSampling.RectangleError

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Actual rational rectangle masses approach their ideal product integrals
on a single conull event. This is the stochastic approximation step; the
identification of the ideal limiting law is a separate obligation. -/
theorem sourceSampling_rectangle_approximation_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest),
      Tendsto (fun stage =>
        ((sourceSamplingUntrimmed I stage θ)
          (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal -
        ∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I))
          (sourceSamplingRationalX T) (sourceSamplingRationalY T) x ∂sourceSamplingHaar)
      atTop (𝓝 0) := by
  filter_upwards [sourceSampling_rational_event] with θ hθ
  intro I T
  have he := (hθ I false T).1
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  simp only [Real.sqrt_zero] at hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall (fun stage => abs_nonneg _)) _ hs
  filter_upwards [sourceSamplingPrefix_eventually_covers T.1] with stage hstage
  exact Real.abs_le_sqrt (sourceSamplingUntrimmed_rectangle_error I stage
    (sourceSamplingRationalX T) (sourceSamplingRationalY T)
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
    (sourceSamplingRationalTests_outside T stage hstage) θ)

end
end FiniteFactor

end OAI
