import Mathlib.Analysis.SpecificLimits.Basic
import OAI.Combinatorics.BalancedRyser.Probability.ExposureSchedule

namespace OAI

namespace Balanced.ExposureInterleaving

open Filter
open scoped Topology

theorem uniform_remainingD_fraction_error {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (n m : ℕ), N ≤ n →
      ∀ (γ : ℝ), 0 < γ → ∀ s : Step n m,
        |((remainingD γ s).card : ℝ) / n - parameter γ s| < ε := by
  have hlim := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨max N 1, by omega, ?_⟩
  intro n m hn γ hγ s
  exact (remainingD_fraction_error (by omega) hγ s).trans_lt (hN n (by omega))

theorem uniform_remainingC_fraction_error {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (n m : ℕ), N ≤ m →
      ∀ (γ : ℝ), 0 < γ → ∀ s : Step n m,
        |((remainingC γ s).card : ℝ) / m - parameter γ s ^ γ| < ε := by
  have hlim := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨max N 1, by omega, ?_⟩
  intro n m hm γ hγ s
  exact (remainingC_fraction_error (by omega) hγ s).trans_lt (hN m (by omega))

theorem remainingD_fraction_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    (n m : ι → ℕ) (γ : ι → ℝ) (s : ∀ t, Step (n t) (m t))
    (hn : Tendsto n l atTop) (hγ : ∀ᶠ t in l, 0 < γ t) :
    Tendsto (fun t => ((remainingD (γ t) (s t)).card : ℝ) / n t -
      parameter (γ t) (s t)) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    _ (tendsto_one_div_atTop_nhds_zero_nat.comp hn)
  filter_upwards [hn.eventually (eventually_gt_atTop 0), hγ] with t hnt hγt
  exact remainingD_fraction_error hnt hγt (s t)

theorem remainingC_fraction_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    (n m : ι → ℕ) (γ : ι → ℝ) (s : ∀ t, Step (n t) (m t))
    (hm : Tendsto m l atTop) (hγ : ∀ᶠ t in l, 0 < γ t) :
    Tendsto (fun t => ((remainingC (γ t) (s t)).card : ℝ) / m t -
      parameter (γ t) (s t) ^ γ t) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    _ (tendsto_one_div_atTop_nhds_zero_nat.comp hm)
  filter_upwards [hm.eventually (eventually_gt_atTop 0), hγ] with t hmt hγt
  exact remainingC_fraction_error hmt hγt (s t)

theorem remainingD_fraction_tendsto {ι : Type*} {l : Filter ι}
    (n m : ι → ℕ) (γ : ι → ℝ) (s : ∀ t, Step (n t) (m t))
    (hn : Tendsto n l atTop) (hγ : ∀ᶠ t in l, 0 < γ t)
    {z : ℝ} (hz : Tendsto (fun t => parameter (γ t) (s t)) l (𝓝 z)) :
    Tendsto (fun t => ((remainingD (γ t) (s t)).card : ℝ) / n t) l (𝓝 z) := by
  simpa only [sub_add_cancel, zero_add] using
    (remainingD_fraction_sub_tendsto_zero n m γ s hn hγ).add hz

theorem remainingC_fraction_tendsto {ι : Type*} {l : Filter ι}
    (n m : ι → ℕ) (γ : ι → ℝ) (s : ∀ t, Step (n t) (m t))
    (hm : Tendsto m l atTop) (hγ : ∀ᶠ t in l, 0 < γ t)
    {y : ℝ} (hy : Tendsto (fun t => parameter (γ t) (s t) ^ γ t) l (𝓝 y)) :
    Tendsto (fun t => ((remainingC (γ t) (s t)).card : ℝ) / m t) l (𝓝 y) := by
  simpa only [sub_add_cancel, zero_add] using
    (remainingC_fraction_sub_tendsto_zero n m γ s hm hγ).add hy

end Balanced.ExposureInterleaving

end OAI
