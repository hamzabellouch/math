import OAI.MeasureTheory.Falconer.Frostman.Frostman
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

def BallBound (μ : Measure Plane) (s C : ℝ) : Prop :=
  ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)

theorem noAtoms_of_ball_bound (μ : Measure Plane) {s C : ℝ}
    (hs : 0 < s) (hb : BallBound μ s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C*r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (C*r^s)) := ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa [Real.zero_rpow hs.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

noncomputable def rieszPotential (μ : Measure Plane) (u : ℝ) (x : Plane) : ℝ≥0∞ :=
  ∫⁻ y, (edist x y)^(-u) ∂μ

noncomputable def rieszEnergy (μ : Measure Plane) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, rieszPotential μ u x ∂μ

noncomputable def energyScale (n : ℕ) : ℝ := (1/2 : ℝ)^n

noncomputable def energyMajorantTerm (x : Plane) (u : ℝ) (n : ℕ) : Plane → ℝ≥0∞ :=
  (ball x (2*energyScale n)).indicator
    (fun _ => ENNReal.ofReal ((energyScale n/2)^(-u)))

theorem energyScale_pos (n : ℕ) : 0 < energyScale n := by
  unfold energyScale
  positivity

theorem riesz_kernel_majorant (x y : Plane) {u : ℝ} (hu : 0 < u) (hxy : x ≠ y) :
    (edist x y)^(-u) ≤ 1 + ∑' n : ℕ, energyMajorantTerm x u n y := by
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
    have hpoint : (edist x y)^(-u) ≤ energyMajorantTerm x u n y := by
      rw [heq, energyMajorantTerm, indicator_of_mem hball]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (div_pos (energyScale_pos n) (by norm_num)) hlo'.le (by linarith))
    rw [heq] at hpoint
    exact hpoint.trans ((ENNReal.le_tsum (f := fun index : ℕ =>
      energyMajorantTerm x u index y) n).trans (le_add_left le_rfl))

theorem energy_scale_identity (n : ℕ) (u s C : ℝ) :
    (energyScale n/2)^(-u) * (C*(2*energyScale n)^s) =
      ((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n := by
  have ha : (0 : ℝ) < 1/2 := by norm_num
  have hn := energyScale_pos n
  have hadd : (energyScale n)^(-u)*(energyScale n)^s = (energyScale n)^(s-u) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hpow : (energyScale n)^(s-u) = ((1/2 : ℝ)^(s-u))^n := by
    rw [energyScale, ← Real.rpow_natCast_mul ha.le, mul_comm,
      Real.rpow_mul_natCast ha.le]
  rw [show energyScale n/2 = energyScale n*(1/2) by ring,
    Real.mul_rpow hn.le ha.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
  calc
    _ = ((1/2 : ℝ)^(-u)*C*2^s) * ((energyScale n)^(-u)*(energyScale n)^s) := by ring
    _ = _ := by rw [hadd,hpow]

theorem energy_term_integral_le (μ : Measure Plane) {s C : ℝ}
    (hb : BallBound μ s C) (x : Plane) (u : ℝ) (n : ℕ) :
    (∫⁻ y, energyMajorantTerm x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [energyMajorantTerm, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb x _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem riesz_potential_uniform_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : BallBound μ s C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, rieszPotential μ u x ≤ B := by
  let := noAtoms_of_ball_bound μ (hu.trans hus) hb
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have ha : a < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  have hsum : (∑' n : ℕ, a^n) < ∞ := tsum_geometric_lt_top.mpr ha
  refine ⟨μ univ + D * ∑' n : ℕ, a^n,
    ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum⟩,?_⟩
  intro x
  have hm (n : ℕ) : Measurable (energyMajorantTerm x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simp
  calc
    rieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, energyMajorantTerm x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, energyMajorantTerm x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => energy_term_integral_le μ hb x u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]

theorem rieszEnergy_lt_top_of_ball_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : BallBound μ s C) :
    rieszEnergy μ u < ∞ := by
  obtain ⟨B,hB,hpot⟩ := riesz_potential_uniform_bound μ hu hus hb
  calc
    rieszEnergy μ u ≤ ∫⁻ _ : Plane, B ∂μ := lintegral_mono hpot
    _ = B * μ univ := lintegral_const B
    _ < ∞ := ENNReal.mul_lt_top hB (measure_lt_top μ univ)

end PlanarFalconer

end OAI
