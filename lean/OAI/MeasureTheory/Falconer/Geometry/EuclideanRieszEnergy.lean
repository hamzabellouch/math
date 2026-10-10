import OAI.MeasureTheory.Falconer.Measures.StartingMeasures
import OAI.MeasureTheory.Falconer.Fourier.FourierEnergy

namespace OAI

/-! # Finite Riesz energies from the original all-dimensional Frostman bounds

The dyadic potential argument and its scalar scale identity are dimension
independent.
-/

namespace Falconer
open Set Metric MeasureTheory Filter PlanarFalconer
open scoped ENNReal Topology
variable {d : ℕ}

noncomputable def euclideanRieszPotential (μ : Measure (Space d)) (u : ℝ)
    (x : Space d) : ℝ≥0∞ := ∫⁻ y, (edist x y)^(-u) ∂μ

noncomputable def euclideanEnergyMajorant (x : Space d) (u : ℝ) (n : ℕ) : Space d → ℝ≥0∞ :=
  (ball x (2*energyScale n)).indicator
    (fun _ => ENNReal.ofReal ((energyScale n/2)^(-u)))

theorem euclidean_riesz_kernel_majorant (x y : Space d) {u : ℝ} (hu : 0 < u) (hxy : x ≠ y) :
    (edist x y)^(-u) ≤ 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have heq : (edist x y)^(-u) = ENNReal.ofReal ((dist x y)^(-u)) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_pos hd]
  rw [heq]
  by_cases hlarge : 1 ≤ dist x y
  · have hle : (dist x y)^(-u) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hlarge (neg_nonpos.mpr hu.le)
    exact (show ENNReal.ofReal ((dist x y)^(-u)) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal hle).trans (le_add_right le_rfl)
  · obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hd (le_of_not_ge hlarge)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have hlo' : energyScale n/2 < dist x y := by
      simpa [energyScale,pow_succ,div_eq_mul_inv] using hlo
    have hball : y ∈ ball x (2*energyScale n) := by
      rw [mem_ball, dist_comm]
      have hpos := energyScale_pos n
      change dist x y ≤ energyScale n at hhi
      linarith
    have hpoint : (edist x y)^(-u) ≤ euclideanEnergyMajorant x u n y := by
      rw [heq, euclideanEnergyMajorant, indicator_of_mem hball]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (div_pos (energyScale_pos n) (by norm_num)) hlo'.le (by linarith))
    rw [heq] at hpoint
    exact hpoint.trans ((ENNReal.le_tsum (f := fun index : ℕ =>
      euclideanEnergyMajorant x u index y) n).trans (le_add_left le_rfl))

theorem euclidean_energy_term_integral_le (μ : Measure (Space d)) {s C : ℝ}
    (hb : FrostmanBallBound μ s C) (x : Space d) (u : ℝ) (n : ℕ) :
    (∫⁻ y, euclideanEnergyMajorant x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [euclideanEnergyMajorant, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb x _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem euclidean_riesz_potential_uniform_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, euclideanRieszPotential μ u x ≤ B := by
  let := noAtoms_of_frostman μ (hu.trans hus) hb
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have ha : a < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  have hsum : (∑' n : ℕ, a^n) < ∞ := tsum_geometric_lt_top.mpr ha
  refine ⟨μ univ + D * ∑' n : ℕ, a^n,
    ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum⟩,?_⟩
  intro x
  have hm (n : ℕ) : Measurable (euclideanEnergyMajorant x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simp
  calc
    euclideanRieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, euclideanEnergyMajorant x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact euclidean_riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, euclideanEnergyMajorant x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => euclidean_energy_term_integral_le μ hb x u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]

theorem rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : FrostmanBallBound μ s C) :
    PlanarFalconer.rieszEnergyOn μ u < ∞ := by
  obtain ⟨B,hB,hpot⟩ := euclidean_riesz_potential_uniform_bound μ hu hus hb
  rw [PlanarFalconer.rieszEnergyOn,lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : Space d, B ∂μ := lintegral_mono hpot
    _ = B*μ univ := lintegral_const B
    _ < ∞ := ENNReal.mul_lt_top hB (measure_lt_top μ univ)

end Falconer

end OAI
