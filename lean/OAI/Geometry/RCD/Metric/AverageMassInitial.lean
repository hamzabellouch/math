import OAI.Geometry.RCD.Heat.HeatMassTimeContinuity

namespace OAI

/-! # Integrability of the averaged positive source at the initial time -/

open Set MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Averaging makes the full finite positive source integrable down to
zero time. The bound uses unit heat mass and retains singular source mass. -/
theorem cutoffAverageHeatMassAt_intervalIntegrable_zero
    (M : PositiveBilinearMeasure X E) (hχbounds : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (A : Set X) (hA : MeasurableSet A) (hbounded : Bornology.IsBounded A)
    (v : E) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => ⟪v, cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded t v⟫_ℝ)
      volume 0 T := by
  let F := fun t => ⟪v, cutoffAverageHeatMassAt μ hQ hk hχ hc M A hA hbounded t v⟫_ℝ
  have hcont : ContinuousOn F (Ioc 0 T) :=
    (cutoffAverageHeatMassAt_continuousOn μ hQ hk hχ hc M A hA hbounded v).mono
      (fun _ ht => ht.1)
  have hm : AEStronglyMeasurable F (volume.restrict (Ioc 0 T)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  let B := (μ.real A)⁻¹ * (M.measure v).real univ
  have hb : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ‖F t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoffAverageHeatMassAt_nonneg μ hQ hk hχ hc M
      (fun z => (hχbounds z).1) A hA hbounded t v)]
    rw [cutoffAverageHeatMassAt_of_pos μ hQ hk hχ hc M A hA hbounded ht.1]
    rw [cutoffAverageHeatMass_integral]
    have hi : Integrable (fun z => χ z * kernelAverage μ ker t A z) (M.measure v) :=
      (hχ.mul (kernelAverage_continuous μ hQ hk ht.1 hA hbounded)).integrable_of_hasCompactSupport
        hc.mul_right
    calc
      _ ≤ ∫ _z, (μ.real A)⁻¹ ∂(M.measure v) := by
        apply integral_mono hi (integrable_const _)
        intro z
        exact (mul_le_of_le_one_left (kernelAverage_bounds μ hQ hk ht.1 A z).1
          (hχbounds z).2).trans (kernelAverage_bounds μ hQ hk ht.1 A z).2
      _ = B := by simp only [integral_const, smul_eq_mul, B]; ring
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact IntegrableOn.of_bound measure_Ioc_lt_top hm B hb

end RegularPointCoordinates

end

end OAI
