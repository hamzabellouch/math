import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.WeakSommerfeldBoundsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombPDE

theorem weak_sommerfeld_asymptotic {F : Space → ℝ} {d c C R : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R)
    (hreg : ContinuousOn F {0}ᶜ)
    (hpde : PuncturedPoisson F (fun x => reaction d (F x)))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x)
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space)) (𝓝 (sommerfeldCoefficient d)) := by
  have hA : 0 < sommerfeldCoefficient d := sommerfeldCoefficient_pos hd
  have hn : Tendsto (fun x : Space => ‖x‖) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt.tendsto (x := (0 : Space))).mono_left nhdsWithin_le_nhds
  have hfour : Tendsto (fun x : Space => ‖x‖ ^ 4) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa using hn.pow 4
  have hball : ∀ᶠ x : Space in 𝓝[≠] (0 : Space), x ≠ 0 ∧ ‖x‖ ≤ R := by
    have hsmall : ∀ᶠ x : Space in 𝓝 (0 : Space), ‖x‖ < R := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hR] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with x hx hr
    exact ⟨hx, hr.le⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨B, hB₁, hB₂⟩ := exists_between (max_lt hA ha)
    have hB : 0 < B := (le_max_left _ _).trans_lt hB₁
    have haB : a < B := (le_max_right _ _).trans_lt hB₁
    have hq : d * B ^ (1 / 2 : ℝ) < 12 := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hB.le hB₂ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := B * (R ^ 2) ^ (-2 : ℝ)
    have ht : Tendsto (fun x : Space => B - ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.sub (hfour.mul_const D)
    have he := ht.eventually (eventually_gt_nhds haB)
    filter_upwards [hball, he] with x hx he
    have hl := weak_singular_lower_bound hd hc hR hB hq hreg hpde hlower x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith
  · intro b hb
    obtain ⟨B, hB₁, hB₂⟩ := exists_between hb
    have hB : 0 < B := hA.trans hB₁
    have hq : 12 < d * B ^ (1 / 2 : ℝ) := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hA.le hB₁ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := C * (R ^ 2) ^ (-2 : ℝ) + 1
    have ht : Tendsto (fun x : Space => B + ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.add (hfour.mul_const D)
    have he := ht.eventually (eventually_lt_nhds hB₂)
    filter_upwards [hball, he] with x hx he
    have hl := weak_singular_upper_bound hd hC hR hB hq hreg hpde hupper x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith

end CoulombAnalysis

end

end OAI
