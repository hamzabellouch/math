import OAI.MeasureTheory.Falconer.Geometry.EuclideanRieszEnergy

namespace OAI

/-! # A Riesz potential bound from small balls at one fixed center -/
namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

noncomputable def rieszSmallBallBound (s C u : ℝ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal ((1/2:ℝ)^(-u)*C*2^s) *
    ∑' n : ℕ, (ENNReal.ofReal ((1/2:ℝ)^(s-u)))^n

theorem rieszSmallBallBound_lt_top {s C u : ℝ} (hus : u < s) :
    rieszSmallBallBound s C u < ∞ := by
  have ha : ENNReal.ofReal ((1/2:ℝ)^(s-u)) < 1 :=
    ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  exact ENNReal.add_lt_top.mpr ⟨by simp,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tsum_geometric_lt_top.mpr ha)⟩

theorem singleton_eq_zero_of_point_frostman (μ : Measure (Space d)) (x : Space d)
    {s C : ℝ} (hs : 0 < s)
    (hb : ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) : μ {x} = 0 := by
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb r hr)

theorem point_energy_term_integral_le (μ : Measure (Space d)) {s C : ℝ}
    (x : Space d) (hb : ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) (u : ℝ) (n : ℕ) :
    (∫⁻ y, euclideanEnergyMajorant x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [euclideanEnergyMajorant, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem point_riesz_potential_bound (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (x : Space d) {s C u : ℝ} (hu : 0 < u) (hus : u < s)
    (hb : ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    euclideanRieszPotential μ u x ≤ rieszSmallBallBound s C u := by
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have hm (n : ℕ) : Measurable (euclideanEnergyMajorant x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simpa using singleton_eq_zero_of_point_frostman μ x (hu.trans hus) hb
  calc
    euclideanRieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact euclidean_riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, euclideanEnergyMajorant x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => point_energy_term_integral_le μ x hb u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left, measure_univ]; rfl

end Falconer

end OAI
