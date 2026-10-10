import OAI.Analysis.CoulombTransport.ProductPlan

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356

theorem integrableOn_inv_norm_ball (r : ℝ) :
    IntegrableOn (fun x : E3 => ‖x‖⁻¹) (Metric.ball 0 r) volume := by
  refine integrableOn_ball_of_norm_le_rpow (by simp [E3]) (C := 1) (α := 1)
    (by norm_num [E3]) ?_ ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp [Real.rpow_neg_one])
  · fun_prop

/-- The Coulomb singularity is integrable on every bounded ball in dimension three. -/
theorem lintegral_invDistance_zero_ball_lt_top (r : ℝ) :
    (∫⁻ x in Metric.ball (0 : E3) r, invDistance 0 x ∂volume) < ⊤ := by
  have heq : (fun x : E3 => invDistance 0 x) =ᵐ[
      (volume : Measure E3).restrict (Metric.ball 0 r)]
      (fun x => ENNReal.ofReal (‖x‖⁻¹)) := by
    filter_upwards [ae_restrict_of_ae ((volume : Measure E3).ae_ne 0)] with x hx
    simp [invDistance, ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hx)]
  rw [lintegral_congr_ae heq]
  exact (integrableOn_inv_norm_ball r).lintegral_lt_top

/-- Local part of the singular kernel; the omitted tail is bounded by one. -/
def localCoulombKernel (x : E3) : ℝ≥0∞ :=
  (Metric.ball (0 : E3) 1).indicator (fun x => invDistance 0 x) x

theorem measurable_localCoulombKernel : Measurable localCoulombKernel := by
  unfold localCoulombKernel
  apply Measurable.indicator _ measurableSet_ball
  unfold invDistance
  fun_prop

theorem lintegral_localCoulombKernel_lt_top :
    (∫⁻ x : E3, localCoulombKernel x ∂volume) < ⊤ := by
  simp only [localCoulombKernel, lintegral_indicator measurableSet_ball]
  exact lintegral_invDistance_zero_ball_lt_top 1

theorem densityMeasure_le_smul_volume_of_le {rho : E3 → ℝ} {M : ℝ}
    (h : ∀ x, rho x ≤ M) :
    densityMeasure rho ≤ ENNReal.ofReal M • (volume : Measure E3) := by
  have hb := withDensity_mono (μ := (volume : Measure E3))
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (h x))
  simpa [densityMeasure, withDensity_const] using hb

theorem invDistance_le_localCoulombKernel_add_one (x y : E3) :
    invDistance x y ≤ localCoulombKernel (x - y) + 1 := by
  by_cases h : x - y ∈ Metric.ball (0 : E3) 1
  · simp only [localCoulombKernel, indicator_of_mem h, invDistance, zero_sub, norm_neg]
    exact le_add_of_nonneg_right zero_le_one
  · simp only [localCoulombKernel, indicator_of_notMem h, zero_add]
    apply ENNReal.inv_le_one.mpr
    have hn : 1 ≤ ‖x - y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using h
    exact_mod_cast (ENNReal.ofReal_le_ofReal hn)

/-- Uniform control of the Coulomb potential for a probability with bounded density. -/
theorem lintegral_invDistance_le_of_measure_le (mu : Measure E3)
    [IsProbabilityMeasure mu] {C : ℝ≥0∞}
    (hmu : mu ≤ C • (volume : Measure E3)) (x : E3) :
    (∫⁻ y, invDistance x y ∂mu) ≤
      C * (∫⁻ y : E3, localCoulombKernel y ∂volume) + 1 := by
  calc
    (∫⁻ y, invDistance x y ∂mu) ≤
        ∫⁻ y, localCoulombKernel (x - y) + 1 ∂mu :=
      lintegral_mono (invDistance_le_localCoulombKernel_add_one x)
    _ = (∫⁻ y, localCoulombKernel (x - y) ∂mu) + 1 := by
      rw [lintegral_add_left (f := fun y : E3 => localCoulombKernel (x - y))
        (measurable_localCoulombKernel.comp (by fun_prop))]
      simp
    _ ≤ (∫⁻ y, localCoulombKernel (x - y) ∂(C • (volume : Measure E3))) + 1 := by
      exact add_le_add (lintegral_mono' hmu le_rfl) le_rfl
    _ = C * (∫⁻ y : E3, localCoulombKernel y ∂volume) + 1 := by
      rw [lintegral_smul_measure, lintegral_sub_left_eq_self]
      rfl

theorem coulombPairEnergy_lt_top_of_measure_le (mu : Measure E3)
    [IsProbabilityMeasure mu] {C : ℝ≥0∞} (hC : C < ⊤)
    (hmu : mu ≤ C • (volume : Measure E3)) :
    coulombPairEnergy mu < ⊤ := by
  have hm : Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
    unfold invDistance
    fun_prop
  unfold coulombPairEnergy
  rw [lintegral_prod _ hm.aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono (lintegral_invDistance_le_of_measure_le mu hmu))
  simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hC lintegral_localCoulombKernel_lt_top,
    ENNReal.one_lt_top⟩

theorem coulombPairEnergy_densityMeasure_lt_top_of_bounded {rho : E3 → ℝ}
    [IsProbabilityMeasure (densityMeasure rho)] {M : ℝ} (h : ∀ x, rho x ≤ M) :
    coulombPairEnergy (densityMeasure rho) < ⊤ := by
  exact coulombPairEnergy_lt_top_of_measure_le _ ENNReal.ofReal_lt_top
    (densityMeasure_le_smul_volume_of_le h)

theorem coulombPairEnergy_densityMeasure_lt_top {rho : E3 → ℝ}
    [IsProbabilityMeasure (densityMeasure rho)]
    (h : IsSmoothCompactProbabilityDensity rho) :
    coulombPairEnergy (densityMeasure rho) < ⊤ := by
  obtain ⟨M, hM⟩ := h.2.1.continuous.bounded_above_of_compact_support h.2.2.1
  apply coulombPairEnergy_densityMeasure_lt_top_of_bounded (M := M)
  intro x
  exact (le_abs_self (rho x)).trans (hM x)

theorem kantorovichValue_densityMeasure_lt_top {rho : E3 → ℝ}
    [IsProbabilityMeasure (densityMeasure rho)]
    (h : IsSmoothCompactProbabilityDensity rho) :
    kantorovichValue (densityMeasure rho) < ⊤ := by
  exact kantorovichValue_lt_top_of_pairEnergy_lt_top _
    (coulombPairEnergy_densityMeasure_lt_top h)

end Problem356

end

end OAI
