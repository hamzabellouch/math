import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedLowerTangents
import OAI.Analysis.RieszRectifiability.Limits.CappedFlatBallLimits
import OAI.Analysis.RieszRectifiability.Limits.UniformNonflatLimits

namespace OAI

/-!
Bounded rescaled centers eventually remain in any open neighborhood of the blowup center.
This transfers local capped nonflatness to a global bilateral lower bound for tangent limits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem scaled_bounded_centers_eventually_mem_open {d : ℕ}
    (U : Set (Ambient d)) (hU : IsOpen U) (a : Ambient d) (ha : a ∈ U)
    (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (hs0 : Tendsto s atTop (𝓝 0)) (M : ℝ) :
    ∀ᶠ j in atTop, ∀ x : Ambient d, ‖x‖ ≤ M → a + s j • x ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have ht : Tendsto (fun j => s j * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hs0.mul_const M
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with j hj
  intro x hx
  apply hball
  change dist (a + s j • x) a < δ
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hs j)]
  exact (mul_le_mul_of_nonneg_left hx (hs j)).trans_lt hj

theorem global_bilateral_lower_of_capped_tangent {n d : ℕ} (hnd : n ≤ d)
    (C G H cap ε : ℝ) (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hg : GlobalUpperGrowth n G μ) (hlower : CappedLowerGrowth n C H μ)
    (U : Set (Ambient d)) (hU : IsOpen U) (a : Ambient d) (haU : a ∈ U)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hsH : ∀ j, s j ≤ H) (hs0 : Tendsto s atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (hcap : 0 < cap) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : ∀ x ∈ μ.support, x ∈ U → ∀ r : ℝ, 0 < r → r < cap → ε ≤ bilateralBeta n μ x r) :
    GlobalBilateralLower n ν (ε / 64) := by
  let μj := fun j => blowupMeasure n μ a (s j)
  let : ∀ j, IsFiniteMeasureOnCompacts (μj j) := fun j =>
    globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ a (s j) G (hs j) hg)
  have hl (j : ℕ) : CappedLowerGrowth n C 1 (μj j) :=
    capped_blowup_lower_unit_cap n C H μ hlower a (s j) (hs j) (hsH j)
  intro b hb R hR
  have hscale : Tendsto (fun j => s j * (R / 2)) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hs0.mul_const (R / 2)
  have hbadj : ∀ᶠ j in atTop, ∀ x ∈ (μj j).support, x ∈ ball b 1 →
      ε ≤ bilateralBeta n (μj j) x (R / 2) := by
    filter_upwards [scaled_bounded_centers_eventually_mem_open U hU a haU s
      (fun j => (hs j).le) hs0 (‖b‖ + 1), hscale.eventually (gt_mem_nhds hcap)] with j hjU hjR
    intro x hx hxb
    have hxM : ‖x‖ ≤ ‖b‖ + 1 := by
      have ht := dist_triangle x b (0 : Ambient d)
      have hxb' : dist x b < 1 := hxb
      simp only [dist_zero_right] at ht
      linarith
    change ε ≤ bilateralBeta n (blowupMeasure n μ a (s j)) x (R / 2)
    rw [bilateralBeta_blowup_at n μ a x (s j) (R / 2) (hs j)]
    exact hbad _ ((blowupMeasure_support_iff n μ a x (s j) (hs j)).mp hx)
      (hjU x hxM) _ (mul_pos (hs j) (by positivity)) hjR
  have ht := compactTestConvergence_capped_beta_lower hnd C 1 μj ν hlocal hC zero_lt_one hl
    (ball b 1) isOpen_ball ε hε hε1 (R / 2) (by positivity) hbadj b hb (mem_ball_self zero_lt_one)
  simpa only [mul_div_cancel₀ R (by norm_num : (2 : ℝ) ≠ 0)] using! ht

end

end RieszRectifiability

end OAI
