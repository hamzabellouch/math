import OAI.NumberTheory.Jacobsthal.Renewal.UniformCycleMoments

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InitialOddDraw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open KernelDensityBridge CycleCostMoments PairedDrift CompactExponentialMoments

noncomputable def firstOddUpdate (t : OddState) : OddCost := (t, cost t.1)

theorem firstOddUpdate_measurable : Measurable firstOddUpdate :=
  measurable_id.prodMk (cost_measurable.comp measurable_subtype_coe)

noncomputable def firstOdd : Kernel EvenState OddCost := evenToOdd.map firstOddUpdate

instance firstOdd_isMarkovKernel : IsMarkovKernel firstOdd :=
  Kernel.IsMarkovKernel.map _ firstOddUpdate_measurable

theorem firstOdd_full_draw (s : EvenState) :
    (firstOdd s).map embedOdd = costKernel (.inl s, 0) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH embedOdd_measurable, firstOdd, Kernel.map_apply _ firstOddUpdate_measurable,
    lintegral_map (f := fun z : OddCost => H (embedOdd z)) (hH.comp embedOdd_measurable) firstOddUpdate_measurable]
  simpa only [embedOdd, firstOddUpdate, zero_add] using (costKernel_even_lintegral s 0 hH).symm

theorem firstOdd_cost_bounds (s : EvenState) : ∀ᵐ z ∂firstOdd s,
    0 ≤ z.2 ∧ z.2 ≤ Real.log 3 := by
  rw [firstOdd, Kernel.map_apply _ firstOddUpdate_measurable]
  apply (ae_map_iff firstOddUpdate_measurable.aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  exact Eventually.of_forall fun t =>
    ⟨(cost_pos (by linarith [t.2])).le, draw_cost_le_log_three (by linarith [t.2])⟩

theorem firstOdd_drift_lintegral (s : EvenState) {D : ℝ} (hD : 0 ≤ D) :
    (∫⁻ z, ENNReal.ofReal (V z.1 + D) ∂firstOdd s) =
      (∫⁻ t, ENNReal.ofReal (Real.exp t) ∂evenKernel s) + ENNReal.ofReal D := by
  rw [firstOdd, Kernel.map_apply _ firstOddUpdate_measurable,
    lintegral_map (f := fun z : OddCost => ENNReal.ofReal (V z.1 + D))
      (ENNReal.measurable_ofReal.comp ((V_measurable.comp measurable_fst).add measurable_const)) firstOddUpdate_measurable]
  change (∫⁻ t : OddState, ENNReal.ofReal (Real.exp t.1 + D) ∂evenToOdd s) = _
  rw [evenToOdd_lintegral_ratio s (H := fun t : ℝ => ENNReal.ofReal (Real.exp t + D))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.add measurable_const))]
  simp_rw [ENNReal.ofReal_add (Real.exp_pos _).le hD]
  rw [lintegral_add_left (f := fun t : ℝ => ENNReal.ofReal (Real.exp t))
    (ENNReal.measurable_ofReal.comp Real.measurable_exp), lintegral_const, measure_univ, mul_one]

theorem firstOdd_weighted_exponential (S η D : ℝ) (hη : 0 ≤ η) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + D)) ∂firstOdd s) ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb, _⟩ := kernel_compact_exponential_moments S
  let C := Real.exp (η * Real.log 3) * (B + D)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (add_nonneg hB.le hD)
  refine ⟨C, hC, ?_⟩
  intro s hs
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (η * Real.log 3)) * ENNReal.ofReal (V z.1 + D) ∂firstOdd s := by
      apply lintegral_mono_ae
      filter_upwards [firstOdd_cost_bounds s] with z hz
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz.2 hη)) (add_nonneg (V_pos z.1).le hD))
    _ = ENNReal.ofReal (Real.exp (η * Real.log 3)) *
        ((∫⁻ t, ENNReal.ofReal (Real.exp t) ∂evenKernel s) + ENNReal.ofReal D) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, firstOdd_drift_lintegral s hD]
    _ ≤ ENNReal.ofReal (Real.exp (η * Real.log 3)) * (ENNReal.ofReal B + ENNReal.ofReal D) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply add_le_add _ le_rfl
      rw [← ofReal_integral_eq_lintegral_ofReal (hb s hs).1 (Eventually.of_forall fun t => (Real.exp_pos t).le)]
      exact ENNReal.ofReal_le_ofReal (hb s hs).2
    _ = _ := by rw [← ENNReal.ofReal_add hB.le hD, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end NumberTheoryLean.InitialOddDraw

end

end Erdos970

end OAI
