import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionEvent
import OAI.Analysis.FiniteFactor.L2UniformAbsoluteContinuity

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Positive measurable functions have vanishing mass below the actual
source threshold 1/(j+1), without any quantitative lower bound. -/
theorem positive_small_sets_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (r : X → ℝ) (hr : Measurable r)
    (hpos : ∀ᵐ x ∂μ, 0 < r x) :
    Tendsto (fun j : ℕ => μ.real {x | r x < 1/((j : ℝ)+1)}) atTop (𝓝 0) := by
  let f := fun j : ℕ => {x | r x < 1/((j : ℝ)+1)}.indicator (fun _ => (1 : ℝ))
  have hA (j : ℕ) : MeasurableSet {x | r x < 1/((j : ℝ)+1)} := measurableSet_lt hr measurable_const
  have hm (j : ℕ) : AEStronglyMeasurable (f j) μ := (measurable_const.indicator (hA j)).aestronglyMeasurable
  have hb (j : ℕ) : ∀ᵐ x ∂μ, ‖f j x‖ ≤ (1 : ℝ) := by
    exact Eventually.of_forall fun x => by
      by_cases h : x ∈ {x | r x < 1/((j : ℝ)+1)}
      · simp only [f,Set.indicator_of_mem h,norm_one,le_refl]
      · simp only [f,Set.indicator_of_notMem h,norm_zero,zero_le_one]
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpos] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hx)] with j hj
    have hnot : x ∉ {x | r x < 1/((j : ℝ)+1)} := not_lt.mpr hj.le
    simp only [f,Set.indicator_of_notMem hnot]
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ)) hm (integrable_const 1) hb hl
  have hi (j) : (∫ x, f j x ∂μ) = μ.real {x | r x < 1/((j : ℝ)+1)} := by
    rw [integral_indicator (hA j)]
    simp [measureReal_def]
  simpa only [hi,integral_zero] using ht

/-- The actual uniformly L2-bounded biased marginals inherit that vanishing
loss even though their full infinite-dimensional densities vary with j. -/
theorem sourceBiased_positive_endpoint_loss (r : (SourceCoordinate → ℝ) → ℝ)
    (hr : Measurable r) (hpos : ∀ᵐ x ∂sourceBaseMeasure, 0 < r x) (b : Bool) :
    Tendsto (fun j : ℕ => (sourceBiasedLaw j).real
      {ω | r (sourceBiasedEndpoint (fun _ => b) ω) < 1/((j : ℝ)+1)}) atTop (𝓝 0) := by
  let C := Real.exp (20*(2*(∑' s,sourceKappa s^2)+1))
  have hbound (j : ℕ) : (sourceBiasedLaw j).real
      {ω | r (sourceBiasedEndpoint (fun _ => b) ω) < 1/((j : ℝ)+1)} ≤
        Real.sqrt C * Real.sqrt (sourceBaseMeasure.real {x | r x < 1/((j : ℝ)+1)}) := by
    obtain ⟨g,hg,hg0,hglp,he,hgC⟩ := sourceBiasedEndpoint_density j (fun _ => b)
    have hA : MeasurableSet {x | r x < 1/((j : ℝ)+1)} := measurableSet_lt hr measurable_const
    have hh := withDensity_L2_set_le sourceSamplingHaar g hglp hg0 _ hA C hgC
    rw [← he,Measure.map_apply (sourceBiasedEndpoint_measurable _) hA] at hh
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hh
  have ht := ((positive_small_sets_tendsto sourceBaseMeasure r hr hpos).sqrt).const_mul (Real.sqrt C)
  apply squeeze_zero (fun j => ENNReal.toReal_nonneg) hbound
  simpa only [Real.sqrt_zero,mul_zero] using ht

end
end FiniteFactor

end OAI
